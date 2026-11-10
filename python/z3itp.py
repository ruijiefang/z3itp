"""

z3itp.py

A Python re-implementation of 
    K. L. McMillan, "Interpolants from Z3 proofs" (FMCAD 2011), 

using only Z3's public API and a constellation of secondary-provers
that are user-configurable.

Terminologies:
    Local: A collection of formulas that are only in A's or B's vocabulary.
    Strict: A collection of formulas, where each formula is local, but 
        the entire collection may mix formulas from both A's and B's vocabularies.


Pipeline for an unsat pair (A, B):

  1. solve A /\\ B with proofs on and import the proof DAG;
  2. colour leaves: Each leaf in the proof dag is colored either A, 
    B, or mixed. Asserted A / B formulas, and "definition-like" leaves
     (skolemize, def-intro) whose fresh symbol is made local to one side;
  3. axiom elimination (paper IV.C): every quant-inst node 
     whose instance is not local is rewritten to a local instance phi[s] 
     plus definitions s = t|pi, which are added as extra leaves on the side of t|pi.
     localisation constants s are treated as interpreted (shared);
  4. translate the proof into the interpolation calculus S_I (paper Fig. 1):
     LOCAL_{A|B}, RES_{A|B} for unit-resolution, CONTRA for lemma;
  5. lemma extraction (paper IV.B): any other strict node becomes a LEMMA whose
     premises are the nearest strict descendants; the lemma is interpolated by
     a *secondary* pass (ItpPipeline), which tries the SecondaryInterpolator
     subclasses in order, by default farkas -> mbp -> shared-atoms -> qe -> z3-binary;
  6. ELIM (IV.C): close the interpolant over the localisation constants,
     ForAll for B-side definitions, Exists for A-side ones, in reverse order.

Our proof calculus assumes one-sided sequents: a node proves a goal of form
    (A, B) |- Delta  
where Delta is the literals of its conclusion plus the negations of its 
open hypotheses.  An interpolation phi for this goal satisfies
     (i) A /\\ ~Delta_A |= phi,   
     (ii) B /\\ ~Delta_B |= ~phi,   
     (iii) L(phi) <= L(A) & L(B)
with Delta_B = Delta & L(B) and Delta_A the rest (paper, section III).
"""
import itertools
import math
import subprocess
import sys
import threading
import time
from collections import Counter

import z3
from z3 import (And, BoolVal, Exists, ForAll, Not, Or, Solver, is_and, is_app,
                is_const, is_false, is_not, is_or, is_quantifier, is_true,
                substitute_vars, unsat, sat)

TIMEOUT_MS = 10000
Z3_BINARY = "z3"          # used only by the last-resort secondary prover

# --------------------------------------------------------------------------
# Expression utilities

def neg(e):
    return e.arg(0) if is_not(e) else Not(e)

def lits(e):
    if is_false(e):
        return []
    if is_or(e):
        return list(e.children())
    return [e]

def is_complement(x, y):
    """Z3's notion (ast_manager::is_complement): x = not y, y = not x, or
    {true, false}."""
    return (is_not(x) and x.arg(0).eq(y)) or (is_not(y) and y.arg(0).eq(x)) or \
        (is_true(x) and is_false(y)) or (is_false(x) and is_true(y))


def oeq_to_iff(e):
    """Replace Z3's equisatisfiability connective  ~(p, q)  (from sk, nnf-*,
    apply-def) by  p == q.  For a Skolem leaf this holds once the Skolem
    symbol is interpreted as a witness, which is all a side needs."""
    cache = {}

    def go(x):
        k = x.get_id()
        if k in cache:
            return cache[k][1]
        if is_app(x) and x.decl().kind() == z3.Z3_OP_OEQ:
            r = go(x.arg(0)) == go(x.arg(1))
        elif is_app(x) and x.num_args() > 0 and z3.is_bool(x):
            r = x.decl()(*[go(c) for c in x.children()])
        else:
            r = x
        cache[k] = (x, r)
        return r
    return go(e)


def mk_or(xs):
    xs = [x for x in xs if not is_false(x)]
    if any(is_true(x) for x in xs):
        return BoolVal(True)
    return BoolVal(False) if not xs else xs[0] if len(xs) == 1 else Or(xs)

def mk_and(xs):
    xs = [x for x in xs if not is_true(x)]
    if any(is_false(x) for x in xs):
        return BoolVal(False)
    return BoolVal(True) if not xs else xs[0] if len(xs) == 1 else And(xs)

_sym_cache = {}

def symbols(e):
    """Uninterpreted function/constant symbols of e (quantifier bodies included)."""
    k = e.get_id()
    r = _sym_cache.get(k)
    if r is not None and r[0].eq(e):
        return r[1]
    out, seen, stack = set(), set(), [e]
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if is_quantifier(x):
            stack.append(x.body())
        elif is_app(x):
            d = x.decl()
            if d.kind() == z3.Z3_OP_UNINTERPRETED:
                out.add(d)
            stack.extend(x.children())
    r = frozenset(out)
    _sym_cache[k] = (e, r)      # keep e alive: Z3 recycles ids of freed ASTs
    return r

def fresh_consts(e, shared):
    return [z3.Const(d.name(), d.range()) for d in symbols(e)
            if d.arity() == 0 and d not in shared]

def check(fmls, timeout=TIMEOUT_MS):
    s = Solver()
    s.set("timeout", timeout)
    s.add(fmls)
    return s.check()

# --------------------------------------------------------------------------
# Proof nodes (our own mutable copy of Z3's immutable proof DAG)

class Node:
    __slots__ = ("uid", "rule", "prem", "concl", "side", "params",
                 "_hyps", "_sides", "_delta")

    def __init__(self, uid, rule, prem, concl, side=None, params=None):
        self.uid, self.rule, self.prem, self.concl = uid, rule, prem, concl
        self.side, self.params = side, params
        self._hyps = self._sides = self._delta = None

    def __repr__(self):
        return f"<{self.rule} #{self.uid}: {self.concl}>"


class DeadlineReached(Exception):
    """The caller's time ran out during an interpolation."""

# secondary interpolation pass
class ItpPipeline(object):
    """One secondary pass: interpolate a lemma's sides A and B (formulas) over `shared` by trying the
    secondary interpolators `itps` in order. The first answer that `verify` accepts wins.

    `shared` is the main Interpolator's shared vocabulary, which can be wider than the symbols A
    and B have in common. A narrower set would still be sound, but mbp and qe would then project away
    symbols the interpolant may keep.

    The pass does what every engine needs, so the engines don't have to:
      - if A or B alone is unsat, return false or true without calling an engine;
      - replace quantified subformulas by Boolean atoms (abstract_quantifiers), then remove A-local
        function applications (ackermannize), once for all engines;
      - give each engine the abstracted pair, and undo the abstraction in its answer;
      - check the answer against the original A and B, and move on if the check fails or the
        engine returns None or raises.
    run() returns the interpolant, or None if no engine succeeds. `winner` names the stage that
    produced it ("A-unsat", "B-unsat", an engine's `name`, or "FAILED")."""

    def __init__(self, A, B, itps, shared, verbose=False):
        self.itps = itps
        self.A = A
        self.B = B
        self.shared = shared
        self.verbose = verbose
        self.winner = None

    def run(self):
        a, b = self.A, self.B
        if check([a], 2000) == unsat:
            self.winner = "A-unsat"
            return BoolVal(False)
        if check([b], 2000) == unsat:
            self.winner = "B-unsat"
            return BoolVal(True)
        shared = set(self.shared)       # abstract_quantifiers adds the shared atoms it creates
        a2, b2, back = abstract_quantifiers(a, b, shared)
        a2 = ackermannize(a2, shared)
        for itp in self.itps:
            try:
                I = itp(a2, b2, shared, verbose=self.verbose).run()
            except Exception as ex:          # noqa: BLE001 - try the next one
                if self.verbose:
                    print(f"  secondary {itp.name} failed: {ex}", file=sys.stderr)
                I = None
            if I is not None:
                I = z3.substitute(I, *back) if back else I
                if verify(a, b, I, shared) is True:
                    self.winner = itp.name
                    return I
        self.winner = "FAILED"
        return None


class Interpolator:
    """The main, proof-based interpolator for an unsat pair of lists (A, B); run() returns the
    interpolant. Lemmas it cannot read off the proof go to a secondary pass, an ItpPipeline over
    `pipeline`: a sequence of SecondaryInterpolator subclasses, or their names, tried in order.
    The default is DEFAULT_PIPELINE, farkas -> mbp -> shared-atoms -> qe -> z3-binary."""

    def __init__(self, A, B, verbose=False, deadline=None, pipeline=None):
        # book-keeping
        self.deadline = deadline
        self.pipeline = resolve_pipeline(pipeline)
        self.verbose = verbose
        self.debug = False
        self.stats = Counter()
        self.lemma_sizes = []
        self.memo = {}
        self._uid = itertools.count()

        # shared definitions
        self.A = list(A) # A-formulas
        self.B = list(B) # B-formulas
        self.LA = set().union(*(symbols(a) for a in self.A)) if self.A else set() # symbols appearing on the A side
        self.LB = set().union(*(symbols(b) for b in self.B)) if self.B else set() # symbols appearing on the B side
        self.X = []            # localization constants, in introduction order
        self.arbitrary = []    # constants Z3 picked with no definition; see colour_fresh_symbols
        self.local_quantifiers = set()   # ids of quantifiers held by localised instances
        self.fresh_defs = []   # (side, closed formula) for each definitional step of Z3's
        self.defs = {}         # s decl -> (s, t, side)
        self.def_cache = {}    # t id -> s

    # ---------------- coloring of a formula
    def col(self, e):
        s = symbols(e)
        if s <= self.LB:
            return "B"
        if s <= self.LA:
            return "A"
        return None

    def local_to(self, e, side):
        return symbols(e) <= (self.LA if side == "A" else self.LB)

    def shared(self):
        return self.LA & self.LB

    # ---------------- importing a proof dag from Z3
    def solve(self):
        s = Solver()
        s.set("proof", True)
        if self.deadline is not None:
            s.set("timeout", max(1, int(1000 * (self.deadline - time.time()))))
        for a in self.A:
            s.add(a)
        for b in self.B:
            s.add(b)
        r = s.check()
        if r != unsat:
            raise ValueError(f"A /\\ B is {r}")
        return s.proof()

    def import_proof(self, p):
        # we first get the IDs of formulas in Z3
        ida = {a.get_id() for a in self.A}
        idb = {b.get_id() for b in self.B}
        memo = {}

        # next we visit the proof dag in post-order, 
        # the graph traversal done iteratively to avoid stack blowup
        order, stack = [], [(p, False)]
        while stack:
            n, done = stack.pop()
            if n.get_id() in memo: # we have already visited
                continue
            k = n.num_args() - 1
            if not done:
                stack.append((n, True))
                stack.extend((n.arg(i), False) for i in range(k)
                             if n.arg(i).get_id() not in memo)
                continue
            d = n.decl()
            node = Node(next(self._uid), d.name(),
                        [memo[n.arg(i).get_id()] for i in range(k)],
                        n.arg(k), params=d.params())
            if node.rule == "asserted":
                cid = node.concl.get_id()
                node.side = "A" if cid in ida else "B" if cid in idb else None
                if node.side is None:
                    raise ValueError(f"unrecognised assertion {node.concl}")
            memo[n.get_id()] = node
            order.append(node)
        self.nodes = order
        self.stats["proof_nodes"] = len(order)
        self.stats.update("rule:" + x.rule for x in order)
        return memo[p.get_id()]

    # ---------------- step 2: fresh symbols introduced by Z3 itself
    def colour_fresh_symbols(self):
        """Z3's proofs can mention symbols that are in neither A nor B does. Each gets a status by how it arises.

        Definitional: a leaf step `F ~ G` or `F = G` where G has new symbols. These are Skolem functions
        (`sk`, inside a proof-bind binder when under a universal), names (`intro-def`), and the inverse
        functions and Boolean names of `rewrite`. Every model of F extends to the new symbols. So they
        are local to the side that owns F, and the step counts as an assertion of that side: the
        symbols are fresh for the other side and never reach the interpolant, so an interpolant of the
        extended side is one of the original.

        Arbitrary: a constant with no definition, at which Z3 instantiates a quantifier when a sort has
        no other element (`elem!`, from its model finder). Nothing constrains it, so it is shared, and
        run() closes the interpolant over it.

        Anything else stays in self.stray. It is local to neither side, so literals using it can only
        be handled inside a lemma."""
        fresh = set()
        for n in self.nodes:
            fresh |= symbols(n.concl) - self.LA - self.LB
        for f in self.A + self.B:      # asserted formulas are local whatever the proof does
            fresh -= symbols(f)
        la, lb = set(self.LA), set(self.LB)
        for n, new, src, closed in self.definitional_steps(fresh):
            side = self.owning_side(src, n, fresh, la, lb)
            if side is None:
                self.stats["uncoloured_fresh_defs"] += 1
                continue
            (self.LA if side == "A" else self.LB).update(new)
            n.side = side
            self.fresh_defs.append((side, closed))
        for n in self.nodes:
            if n.rule == "quant-inst":
                for t in n.params or []:
                    for d in symbols(t):
                        if d.arity() == 0 and d not in self.LA and d not in self.LB and d in fresh:
                            self.LA.add(d)
                            self.LB.add(d)
                            self.arbitrary.append(d())
                            self.stats["arbitrary_constants"] += 1
        self.stray = {d for d in fresh if d not in self.LA and d not in self.LB}
        self.stats["stray_symbols"] = len(self.stray)

    def definitional_steps(self, fresh):
        """(node, new symbols, source formula, closed definition) for each leaf step introducing symbols.
        import_proof reads a proof-bind as a leaf, so the proof terms inside its binders are read here."""
        for n in self.nodes:
            if n.prem:
                continue
            if n.rule == "proof-bind":
                steps = steps_under_binders(n.concl)
            else:
                steps = [(n.rule, n.concl, ())]
            for rule, c, sorts in steps:
                if rule == "intro-def":
                    src = c
                    new = symbols(c) & fresh
                elif rule in ("sk", "rewrite") and c.num_args() == 2:
                    src = c.arg(0)
                    new = (symbols(c.arg(1)) - symbols(src)) & fresh
                else:
                    continue
                if new:
                    yield n, new, src, close_over(oeq_to_iff(c), sorts)

    def owning_side(self, src, node, fresh, la, lb):
        """The side a definition belongs to. The vocabulary of its source formula settles this unless
        that is all shared, and then the proof says which assertions the step was applied to."""
        old = symbols(src) - fresh
        in_a, in_b = old <= la, old <= lb
        if not in_a and not in_b:
            return None                # mixes the vocabularies: not a definition of either side
        if in_a != in_b:
            return "A" if in_a else "B"
        found = self.asserted_by(node)
        if found == {"A", "B"}:
            self.stats["fresh_on_both_sides"] += 1
        return "B" if found == {"B"} else "A"

    def asserted_by(self, node):
        """The sides of the first steps below `node` that also depend on an assertion."""
        if not hasattr(self, "_consumers"):
            self._consumers, self._asserted = {}, {}
            for n in self.nodes:       # premises come first
                s = {n.side} if n.rule == "asserted" and n.side else set()
                for p in n.prem:
                    s |= self._asserted[p.uid]
                    self._consumers.setdefault(p.uid, []).append(n)
                self._asserted[n.uid] = s
        found, seen, queue = set(), {node.uid}, [node]
        while queue:
            for c in self._consumers.get(queue.pop().uid, []):
                if c.uid in seen:
                    continue
                seen.add(c.uid)
                if self._asserted[c.uid]:
                    found |= self._asserted[c.uid]
                else:
                    queue.append(c)
        return found

    # ---------------- step 3: axiom elimination (localise quant-inst)
    def new_def(self, t):
        k = t.get_id()
        if k in self.def_cache:
            return self.def_cache[k]
        s = z3.FreshConst(t.sort(), "loc")
        side = self.col(t)
        self.LA.add(s.decl())
        self.LB.add(s.decl())
        self.X.append(s)
        self.defs[s.decl()] = (s, t, side)
        self.def_cache[k] = s
        return s

    def localise_term(self, t, side):
        """Paper IV.C: replace highest local positions by fresh symbols until
        the term is local to `side`."""
        for _ in range(64):
            if self.local_to(t, side):
                return t
            if self.col(t) is not None:
                return self.new_def(t)
            t2 = self._replace_maximal_local(t)
            if t2.eq(t):
                return None                    # stray symbol: cannot localise
            t = t2
        return None

    def _replace_maximal_local(self, t):
        if self.col(t) is not None:
            return t if is_const(t) and t.decl() in self.defs else self.new_def(t)
        if not is_app(t) or t.num_args() == 0:
            return t
        return t.decl()(*[self._replace_maximal_local(c) for c in t.children()])

    def eliminate_axioms(self):
        """Localise the quantifier instances that mix the vocabularies.

        The quantifier of an instance can itself be mixed. Instantiating the outer variable of
        forall x. ... forall z. phi(x, y(x), z) at a B-local b gives an inner quantifier holding both b
        and A's y. The outer instance, once localised, holds that inner quantifier with b replaced by
        the localisation constant, so the inner instance is localised to the same quantifier."""
        pending = []
        for n in self.nodes:
            if n.rule != "quant-inst" or self.strict_formula(n.concl):
                continue
            terms = self.instance_terms(n)
            if terms is None:
                continue
            q = n.concl.arg(0).arg(0)
            side = self.col(q)
            if side is None:
                pending.append((n, q, terms))
                continue
            if side == "B" and self.local_to(q, "A"):
                side = "A"               # shared quantifier: prefer A (arbitrary)
            self.localise_instance(n, q, terms, side)
        while pending:
            # Prefer a quantifier that a localised instance already holds. Otherwise take the first
            # that can be localised, whose own instances may be the ones others are waiting for.
            for need_known in (True, False):
                chosen = next(((k, r) for k, (_, q, _) in enumerate(pending)
                               for r in [self.localise_quantifier(q, need_known)] if r), None)
                if chosen:
                    break
            if not chosen:
                self.stats["qinst_mixed_unlocalisable"] += len(pending)
                return
            k, (q_local, side) = chosen
            n, _, terms = pending.pop(k)
            self.localise_instance(n, q_local, terms, side)
            self.stats["qinst_mixed_localised"] += 1

    def instance_terms(self, n):
        """The terms of a quant-inst whose conclusion is the instance those terms give, or None."""
        c = n.concl
        if not (is_or(c) and c.num_args() == 2 and is_not(c.arg(0))
                and is_quantifier(c.arg(0).arg(0))):
            return None
        q, inst = c.arg(0).arg(0), c.arg(1)
        terms = list(n.params or [])
        if len(terms) != q.num_vars():
            return None
        if not substitute_vars(q.body(), *reversed(terms)).eq(inst):
            self.stats["qinst_not_syntactic"] += 1
            return None
        return terms

    def localise_quantifier(self, q, need_known):
        """A mixed quantifier with the ground terms foreign to one side replaced by localisation
        constants, and that side; None if neither side can hold it. With need_known, only a result
        made from existing constants that a localised instance already holds."""
        for side in ("A", "B"):
            targets = self.foreign_terms(q, side)
            if targets is None:
                continue
            if need_known:
                if not all(t.get_id() in self.def_cache for t in targets):
                    continue
                r = z3.substitute(q, *[(t, self.def_cache[t.get_id()]) for t in targets])
                if r.get_id() in self.local_quantifiers:
                    return r, side
            else:
                return z3.substitute(q, *[(t, self.new_def(t)) for t in targets]), side
        return None

    def foreign_terms(self, q, side):
        """The maximal ground subterms of q local to the other side, or None if replacing them would
        not make q local to `side`: a foreign symbol applied to a bound variable has to stay."""
        vocabulary, out, seen, stack = (self.LA if side == "A" else self.LB), [], set(), [q.body()]
        while stack:
            e = stack.pop()
            if e.get_id() in seen:
                continue
            seen.add(e.get_id())
            if is_quantifier(e):
                stack.append(e.body())
            elif is_app(e) and not self.local_to(e, side):
                if self.col(e) is not None and is_ground(e):
                    out.append(e)
                elif e.decl().kind() == z3.Z3_OP_UNINTERPRETED and e.decl() not in vocabulary:
                    return None
                else:
                    stack.extend(e.children())
        return out

    def localise_instance(self, n, q, terms, side):
        """Replace a quant-inst by a local instance of q and the definitions it uses."""
        ndefs = len(self.X)
        loc = [self.localise_term(t, side) for t in terms]
        if any(x is None for x in loc):
            self.stats["qinst_unlocalisable"] += 1
            return
        leaf = Node(next(self._uid), "quant-inst-local", [],
                    Or(Not(q), substitute_vars(q.body(), *reversed(loc))))
        self.remember_quantifiers(leaf.concl)
        defs = [Node(next(self._uid), "definition", [], s == self.defs[s.decl()][1],
                     side=self.defs[s.decl()][2])
                for s in self.X[ndefs:]]
        # definitions reused from the cache, or held by q, must also be premises
        used = symbols(q).union(*[symbols(x) for x in loc])
        known = {d.concl.arg(0).decl() for d in defs}
        for s in self.X:
            if s.decl() in used and s.decl() not in known:
                defs.append(Node(next(self._uid), "definition", [],
                                 s == self.defs[s.decl()][1],
                                 side=self.defs[s.decl()][2]))
        # nested definitions: loc_2 = f(loc_1) needs loc_1's definition too
        seen = {d.concl.arg(0).decl() for d in defs}
        frontier = list(defs)
        while frontier:
            d = frontier.pop()
            for sd in symbols(d.concl.arg(1)):
                if sd in self.defs and sd not in seen:
                    seen.add(sd)
                    s, t, sside = self.defs[sd]
                    nd = Node(next(self._uid), "definition", [], s == t, side=sside)
                    defs.append(nd)
                    frontier.append(nd)
        n.rule, n.prem = "elim-subst", [leaf] + defs
        self.stats["qinst_localised"] += 1

    def remember_quantifiers(self, e):
        seen, stack = set(), [e]
        while stack:
            x = stack.pop()
            if x.get_id() in seen:
                continue
            seen.add(x.get_id())
            if is_quantifier(x):
                self.local_quantifiers.add(x.get_id())
                stack.append(x.body())
            elif is_app(x):
                stack.extend(x.children())

    # ---------------- sequents
    def hyps(self, n):
        if n._hyps is None:
            if n.rule == "hypothesis":
                n._hyps = {n.concl.get_id(): n.concl}
            elif n.rule == "lemma":
                n._hyps = {}
            else:
                h = {}
                for p in n.prem:
                    h.update(self.hyps(p))
                n._hyps = h
        return n._hyps

    def sides(self, n):
        if n._sides is None:
            s = {n.side} if n.side else set()
            for p in n.prem:
                s |= self.sides(p)
            n._sides = frozenset(s)
        return n._sides

    def clause_lits(self, n):
        """The literals of n's conclusion *as the rule that produced it means
        them*.  An Or-shaped conclusion is usually a clause, but it is a single
        literal when (a) unit-resolution left exactly one literal, (b) a lemma
        discharged exactly one hypothesis h and concludes not(h), or (c) it is
        a hypothesis.  (Same conventions as Z3's proof_checker.cpp.)"""
        c = n.concl
        if n.rule == "hypothesis":
            return [c]
        if n.rule == "unit-resolution" and n.prem:
            if self.resolves_whole_formula(n):
                return []
            rest = list(self.as_clause_lits(n.prem[0]))
            for u in n.prem[1:]:
                for i, l in enumerate(rest):
                    if is_complement(l, u.concl):
                        del rest[i]
                        break
            return rest
        if n.rule == "lemma" and n.prem:
            hs = list(self.hyps(n.prem[0]).values())
            if len(hs) == 1 and neg(hs[0]).eq(c):
                return [c]
        return lits(c)

    @staticmethod
    def resolves_whole_formula(n):
        """F, not F |- false: F is one literal here, even if it happens to be an Or."""
        return len(n.prem) == 2 and is_complement(n.prem[0].concl, n.prem[1].concl)

    @staticmethod
    def as_clause_lits(n):
        """How a consumer that uses n as a clause (first premise of
        unit-resolution) reads it: the top-level disjuncts."""
        return lits(n.concl)

    def delta(self, n):
        if n._delta is None:
            d = {}
            for e in self.hyps(n).values():
                v = neg(e)
                d[v.get_id()] = v
            for l in self.clause_lits(n):
                d[l.get_id()] = l
            n._delta = d
        return n._delta

    def strict_formula(self, e):
        return self.col(e) is not None

    def strict(self, n):
        return all(self.col(l) is not None for l in self.delta(n).values())

    # ---------------- step 4/5: translation into S_I
    def interp(self, n):
        """Interpolation phi for node n, for its natural Delta (see delta)."""
        r = self.memo.get(n.uid)
        if r is None:
            r = self._interp(n)
            self.memo[n.uid] = r
            if self.debug:
                self.check_node(n, r)
        return r

    def side_axioms(self):
        """Formulas each side may use besides its assertions: localisation
        definitions and Z3's own definitional leaves (sk, intro-def)."""
        ax = {"A": [], "B": []}
        for s_, t, side in self.defs.values():
            ax[side].append(s_ == t)
        for side, closed in self.fresh_defs:
            ax[side].append(closed)
        return ax

    def check_node(self, n, phi):
        """Debug: the S_I validity condition for (A, B) |- Delta [phi]."""
        D = list(self.delta(n).values())
        da = [oeq_to_iff(neg(l)) for l in D if self.col(l) == "A"]
        db = [oeq_to_iff(neg(l)) for l in D if self.col(l) == "B"]
        ax = self.side_axioms()
        if check(self.A + ax["A"] + da + [Not(phi)]) == sat:
            raise AssertionError(f"A-condition fails at {n} (rule {n.rule}) phi={phi}")
        if check(self.B + ax["B"] + db + [phi]) == sat:
            raise AssertionError(f"B-condition fails at {n} (rule {n.rule}) phi={phi}")

    def _interp(self, n):
        D = list(self.delta(n).values())
        sd = self.sides(n)
        # LOCAL (A / B)
        if sd <= {"B"} and all(self.local_to(l, "B") for l in D):
            self.stats["S_I:LocalB"] += 1
            return BoolVal(True)
        if sd <= {"A"} and all(self.local_to(l, "A") for l in D):
            self.stats["S_I:LocalA"] += 1
            return mk_or([l for l in D if self.col(l) == "B"])
        if n.rule == "lemma" and n.prem and self.strict(n.prem[0]):
            p = n.prem[0]
            if set(self.delta(p)) == set(self.delta(n)):
                self.stats["S_I:Contra"] += 1
                return self.interp(p)
        if n.rule == "unit-resolution" and self.native_unit_resolution(n):
            return self._unit_resolution(n)
        return self._lemma(n)

    # -- views: the same node read as a clause or as one formula
    def split_view_strict(self, p):
        return all(self.col(l) is not None for l in self.as_clause_lits(p)) and \
            all(self.col(neg(h)) is not None for h in self.hyps(p).values())

    def as_clause(self, p):
        """Interpolation for p with its conclusion split into top-level
        disjuncts.  Converting from a single literal F with col(F) = A: the
        shared disjuncts S move from Delta_A to Delta_B, phi' = phi or S."""
        phi = self.interp(p)
        nat = self.clause_lits(p)
        if len(nat) != 1 or not is_or(nat[0]) or self.col(nat[0]) == "B":
            return phi
        S = self._moved(p, lits(nat[0]))
        return mk_or([phi] + S)

    def as_unit(self, p):
        """Interpolation for p with its conclusion read as ONE formula F.
        From split literals with col(F) = A: the shared disjuncts S move from
        Delta_B to Delta_A, phi' = phi and not S."""
        phi = self.interp(p)
        nat = self.clause_lits(p)
        if len(nat) == 1 and nat[0].eq(p.concl) or self.col(p.concl) == "B":
            return phi
        S = self._moved(p, nat)
        return mk_and([phi] + [neg(l) for l in S])

    def _moved(self, p, ls):
        hyp_lits = {neg(h).get_id() for h in self.hyps(p).values()}
        return [l for l in ls if self.col(l) == "B" and l.get_id() not in hyp_lits]

    def native_unit_resolution(self, n):
        c = n.prem[0]
        return self.split_view_strict(c) and all(
            self.strict_formula(u.concl) and
            all(self.col(neg(h)) is not None for h in self.hyps(u).values())
            for u in n.prem[1:])

    def _unit_resolution(self, n):
        clause = n.prem[0]
        cl = list(self.as_clause_lits(clause))
        if self.resolves_whole_formula(n):
            cl = [clause.concl]
            phi = self.as_unit(clause)
        else:
            phi = self.as_clause(clause)
        for u in n.prem[1:]:
            piv = next((l for l in cl if is_complement(l, u.concl)), None)
            if piv is None:           # 2-premise form  p, not p |- false
                piv = clause.concl
            psi = self.as_unit(u)
            phi = And(phi, psi) if self.col(piv) == "B" else Or(phi, psi)
            self.stats["S_I:ResB" if self.col(piv) == "B" else "S_I:ResA"] += 1
        return phi

    def _lemma(self, n):
        """Lemma extraction (paper IV.B) rooted at strict node n."""
        if self.deadline is not None and time.time() > self.deadline:
            raise DeadlineReached()
        hn = set(self.hyps(n))
        frontier, fids, seen, stack = [], set(), set(), list(n.prem)
        inner = 0
        while stack:
            p = stack.pop()
            if p.uid in seen:
                continue
            seen.add(p.uid)
            if (p.rule != "hypothesis" and set(self.hyps(p)) <= hn
                    and self.strict(p) and self.strict_formula(p.concl)):
                if p.concl.get_id() not in fids:
                    fids.add(p.concl.get_id())
                    frontier.append(p)
            else:
                inner += 1
                stack.extend(p.prem)
        D = list(self.delta(n).values())
        Ap = [p.concl for p in frontier if self.col(p.concl) == "A"] + \
             [neg(l) for l in D if self.col(l) == "A"]
        Bp = [p.concl for p in frontier if self.col(p.concl) == "B"] + \
             [neg(l) for l in D if self.col(l) == "B"]
        self.stats["S_I:Lemma"] += 1
        self.lemma_sizes.append(inner + 1)
        phi = self.secondary_interpolant(oeq_to_iff(mk_and(Ap)), oeq_to_iff(mk_and(Bp)))
        for p in frontier:
            psi = self.as_unit(p)
            phi = And(phi, psi) if self.col(p.concl) == "B" else Or(phi, psi)
        return phi

    # ---------------- secondary interpolating prover
    def secondary_interpolant(self, a, b):
        """Interpolate a lemma with the secondary pass; stats["2nd:<stage>"] counts who answered."""
        p = ItpPipeline(a, b, self.pipeline, self.shared(), self.verbose)
        i = p.run()
        self.stats["2nd:" + p.winner] += 1
        if i is None:
            raise RuntimeError(f"secondary prover failed on lemma\n A'={a}\n B'={b}")
        return i

    # ---------------- step 6: ELIM + driver
    def run(self):
        root = self.import_proof(self.solve())
        self.colour_fresh_symbols()
        self.eliminate_axioms()
        if not self.strict(root):
            raise RuntimeError("root sequent not strict")
        itp = self.interp(root)
        for s in reversed(self.X):
            _, t, side = self.defs[s.decl()]
            if s.decl() in symbols(itp):
                itp = ForAll([s], itp) if side == "B" else Exists([s], itp)
        # A |= I(e) and I(e) /\\ B unsat for an e fresh in both, so forall e. I(e) is an interpolant.
        for e in self.arbitrary:
            if e.decl() in symbols(itp):
                itp = ForAll([e], itp)
        self.stats["localisation_constants"] = len(self.X)
        itp = simplify_itp(itp)
        return itp


# --------------------------------------------------------------------------
# Secondary interpolators, scheduled by ItpPipeline

class SecondaryInterpolator(Interpolator):
    """A secondary prover for one lemma: formulas A and B, unsat together, and the vocabulary
    `shared` an interpolant may use. The pipeline makes one per lemma, as cls(A, B, shared,
    verbose=...), and calls run(), which returns an interpolant or None. It need not check its
    answer, since the pipeline verifies it, and it may raise, which counts as None.

    To add an engine, subclass this, set `name` and implement run(). Options such as `max_iter`
    are class attributes, so a subclass that overrides one is a configured engine. This class does
    not call Interpolator.__init__, so the proof machinery it inherits is not set up and must not
    be used; only shared(), overridden below, is."""
    name = None

    def __init__(self, A, B, shared, verbose=False):
        self.A = A
        self.B = B
        self.vocab = shared
        self.verbose = verbose

    def shared(self):
        return self.vocab

    def run(self):
        raise NotImplementedError


class FarkasInterpolator(SecondaryInterpolator):
    """Linear arithmetic, by a Farkas combination of A's and B's inequalities (farkas_interpolant)."""
    name = "farkas"

    def run(self):
        return farkas_interpolant(self.A, self.B, self.vocab)


class MBPInterpolator(SecondaryInterpolator):
    """Model-based interpolation with Z3's model-based projection (mbp_interpolant)."""
    name = "mbp"
    max_iter = 200

    def run(self):
        return mbp_interpolant(self.A, self.B, self.vocab, self.max_iter)


class SharedAtomInterpolator(SecondaryInterpolator):
    """Model-based interpolation over the shared ground atoms, for local constants of uninterpreted
    sorts that projection cannot remove (shared_atom_interpolant)."""
    name = "shared-atoms"
    max_iter = 200

    def run(self):
        return shared_atom_interpolant(self.A, self.B, self.vocab, self.max_iter)


class QEInterpolator(SecondaryInterpolator):
    """The strongest interpolant, Exists(local). A, by Z3's qe tactic (qe_interpolant)."""
    name = "qe"

    def run(self):
        return qe_interpolant(self.A, self.B, self.vocab)


class Z3BinaryInterpolator(SecondaryInterpolator):
    """The z3 executable's (get-interpolant A B) command (binary_interpolant)."""
    name = "z3-binary"

    def run(self):
        return binary_interpolant(self.A, self.B, self.vocab)


SECONDARY_INTERPOLATORS = {cls.name: cls for cls in (
    FarkasInterpolator, MBPInterpolator, SharedAtomInterpolator, QEInterpolator,
    Z3BinaryInterpolator)}

# The default secondary pass, cheapest first; the z3 binary is the last resort.
DEFAULT_PIPELINE = (FarkasInterpolator, MBPInterpolator, SharedAtomInterpolator, QEInterpolator,
                    Z3BinaryInterpolator)


def resolve_pipeline(pipeline):
    """A tuple of SecondaryInterpolator subclasses from None (the default), or from a sequence of
    subclasses and names in SECONDARY_INTERPOLATORS."""
    if pipeline is None:
        return DEFAULT_PIPELINE
    if isinstance(pipeline, str):
        raise TypeError("pipeline must be a sequence of names or classes, not a string")
    out = []
    for p in pipeline:
        if isinstance(p, str):
            if p not in SECONDARY_INTERPOLATORS:
                raise ValueError(f"unknown secondary interpolator {p!r}; "
                                 f"known: {', '.join(SECONDARY_INTERPOLATORS)}")
            p = SECONDARY_INTERPOLATORS[p]
        if not (isinstance(p, type) and issubclass(p, SecondaryInterpolator)):
            raise TypeError(f"{p!r} is not a SecondaryInterpolator subclass")
        out.append(p)
    return tuple(out)


def is_ground(e):
    """Whether e has no bound variables and no binders."""
    seen, stack = set(), [e]
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        if z3.is_var(x) or is_quantifier(x):
            return False
        stack.extend(x.children())
    return True


def steps_under_binders(term):
    """The leaf proof steps inside a proof-bind's binders, as (rule, conclusion, sorts bound around it,
    outermost first)."""
    seen, stack = set(), [(term, ())]
    while stack:
        e, sorts = stack.pop()
        if (e.get_id(), sorts) in seen:
            continue
        seen.add((e.get_id(), sorts))
        if is_quantifier(e):
            stack.append((e.body(), sorts + tuple(e.var_sort(i) for i in range(e.num_vars()))))
        elif is_app(e) and e.sort().name() == "Proof":
            if e.decl().name() == "proof-bind":      # a binder nested inside another
                stack.append((e.arg(0), sorts))
            elif e.num_args() == 1:
                yield e.decl().name(), e.arg(0), sorts
            else:
                stack.extend((e.arg(i), sorts) for i in range(e.num_args() - 1))


def close_over(f, sorts):
    """f with its free de Bruijn variables, bound around it by `sorts`, closed universally."""
    if not sorts:
        return f
    vs = [z3.FreshConst(s, "v") for s in sorts]
    return ForAll(vs, z3.substitute_vars(f, *reversed(vs)))


def abstract_quantifiers(a, b, shared):
    """Replace quantified sub-formulas by Boolean atoms (named consistently
    across a and b); returns substitution pairs to undo it."""
    qs = {}

    def collect(e, seen):
        if e.get_id() in seen:
            return
        seen.add(e.get_id())
        if is_quantifier(e):
            qs[e.get_id()] = e
            return
        if is_app(e):
            for c in e.children():
                collect(c, seen)
    seen = set()
    collect(a, seen)
    collect(b, seen)
    if not qs:
        return a, b, []
    fwd, back = [], []
    for q in qs.values():
        v = z3.FreshBool("qatom")
        fwd.append((q, v))
        back.append((v, q))
        if symbols(q) <= shared:
            shared.add(v.decl())     # caller passes a fresh set
    a2, b2 = z3.substitute(a, *fwd), z3.substitute(b, *fwd)
    if check([a2, b2]) != unsat:
        return a, b, []
    return a2, b2, back


def linearize(e, coef=1, poly=None):
    """e as {atom-id: [atom, coef]} plus constant (key None); non-arithmetic
    subterms become atoms.  Returns None for non-linear terms."""
    poly = {} if poly is None else poly
    if z3.is_rational_value(e) or z3.is_int_value(e):
        poly.setdefault(None, [None, 0])[1] += coef * z3_fraction(e)
    elif z3.is_add(e):
        for c in e.children():
            if linearize(c, coef, poly) is None:
                return None
    elif z3.is_sub(e):
        linearize(e.arg(0), coef, poly)
        for c in e.children()[1:]:
            if linearize(c, -coef, poly) is None:
                return None
    elif z3.is_app_of(e, z3.Z3_OP_UMINUS):
        return linearize(e.arg(0), -coef, poly)
    elif z3.is_mul(e):
        nums = [c for c in e.children() if z3.is_rational_value(c) or z3.is_int_value(c)]
        rest = [c for c in e.children() if not (z3.is_rational_value(c) or z3.is_int_value(c))]
        if len(rest) > 1:
            return None
        k = coef
        for c in nums:
            k *= z3_fraction(c)
        return linearize(rest[0], k, poly) if rest else \
            linearize(z3.RealVal(1), k, poly)
    elif z3.is_to_real(e):
        return linearize(e.arg(0), coef, poly)
    else:
        poly.setdefault(e.get_id(), [e, 0])[1] += coef
    return poly


def z3_fraction(v):
    from fractions import Fraction
    return Fraction(v.as_fraction()) if z3.is_rational_value(v) else Fraction(v.as_long())


def ineq(e):
    """Normalise a literal to (poly, op) meaning  poly op 0, op in <=, <, ="""
    neg_ = is_not(e)
    x = e.arg(0) if neg_ else e
    if not is_app(x) or x.num_args() != 2 or not z3.is_arith(x.arg(0)):
        return None
    k = x.decl().kind()
    l, r = x.arg(0), x.arg(1)
    table = {z3.Z3_OP_LE: (l, r, "<="), z3.Z3_OP_GE: (r, l, "<="),
             z3.Z3_OP_LT: (l, r, "<"), z3.Z3_OP_GT: (r, l, "<"),
             z3.Z3_OP_EQ: (l, r, "=")}
    if k not in table:
        return None
    lhs, rhs, op = table[k]
    if neg_:
        if op == "=":
            return None
        lhs, rhs, op = rhs, lhs, "<" if op == "<=" else "<="
    poly = linearize(lhs)
    if poly is None or linearize(rhs, -1, poly) is None:
        return None
    return poly, op


def farkas_interpolant(a, b, shared):
    """Linear-arithmetic interpolation by a Farkas combination (computed with
    an LP, since Z3 often omits the coefficients): the A-part of the
    contradictory combination is the interpolant.  Sound over Int as well."""
    from fractions import Fraction
    rows = []
    for side, f in (("A", a), ("B", b)):
        for c in flatten_and(f):
            r = ineq(c)
            if r is None:
                return None
            rows.append((side, r[0], r[1]))
    lam = [z3.Real(f"lam{i}") for i in range(len(rows))]
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    atoms = {k for _, p, _ in rows for k in p if k is not None}
    for l, (_, _, op) in zip(lam, rows):
        if op != "=":
            s.add(l >= 0)
    for k in atoms:
        s.add(z3.Sum([l * float_free(p[k][1]) for l, (_, p, _) in zip(lam, rows) if k in p]) == 0)
    const = z3.Sum([l * float_free(p[None][1]) for l, (_, p, _) in zip(lam, rows)
                    if None in p] + [z3.RealVal(0)])
    strict = z3.Sum([l for l, (_, _, op) in zip(lam, rows) if op == "<"] + [z3.RealVal(0)])
    s.add(Or(const > 0, And(const >= 0, strict > 0)))
    if s.check() != sat:
        return None
    m = s.model()
    val = [Fraction(m.eval(l, model_completion=True).as_fraction()) for l in lam]
    total, is_strict = {}, False
    for v, (side, p, op) in zip(val, rows):
        if side != "A" or v == 0:
            continue
        is_strict |= op == "<"
        for k, (t, c) in p.items():
            total.setdefault(k, [t, 0])[1] += v * c
    items = [(t, c) for k, (t, c) in total.items() if k is not None and c != 0]
    k0 = total.get(None, [None, 0])[1]
    scale = math.lcm(*[c.denominator for _, c in items], k0.denominator)
    if all(t.is_int() for t, _ in items):       # stay in Int when possible
        num = lambda c: z3.IntVal(int(c * scale))
        cast = lambda t: t
    else:
        num = lambda c: z3.RealVal(str(c * scale))
        cast = lambda t: z3.ToReal(t) if t.is_int() else t
    lhs = z3.Sum([num(c) * cast(t) for t, c in items] + [num(k0)]) \
        if items else num(k0)
    return z3.simplify(lhs < 0 if is_strict else lhs <= 0)


def float_free(c):
    return z3.RealVal(str(c))


def ackermannize(a, shared):
    """Replace applications of A-local function symbols by fresh constants
    plus functional-consistency constraints.  Any model of a extends to one of
    the result, and the fresh constants never reach the interpolant, so an
    interpolant for (ackermannize(a), b) is one for (a, b)."""
    apps = {}                                   # decl -> [(app, const)]
    cache = {}

    def go(e):
        k = e.get_id()
        if k in cache:
            return cache[k][1]
        if is_quantifier(e) or not is_app(e) or e.num_args() == 0:
            r = e
        else:
            args = [go(c) for c in e.children()]
            d = e.decl()
            if d.kind() == z3.Z3_OP_UNINTERPRETED and d not in shared:
                for old_args, v in apps.get(d, []):
                    if all(x.eq(y) for x, y in zip(old_args, args)):
                        r = v
                        break
                else:
                    r = z3.FreshConst(d.range(), "ack")
                    apps.setdefault(d, []).append((args, r))
            else:
                r = d(*args) if args else e
        cache[k] = (e, r)
        return r
    body = go(a)
    if not apps:
        return a
    cons = [z3.Implies(mk_and([x == y for x, y in zip(ai, aj)]), vi == vj)
            for insts in apps.values()
            for (ai, vi), (aj, vj) in itertools.combinations(insts, 2)]
    return mk_and([body] + cons)


def mbp_interpolant(a, b, shared, max_iter=200):
    """Model-based interpolation (the 'pogo' loop of Z3's qe_mbi.cpp) in
    Python: enumerate models of a, project away non-shared constants with
    Z3's public model-based projection, generalise with an unsat core of b."""
    if any(d.arity() > 0 and d not in shared for d in symbols(a)):
        return None                        # MBP cannot project functions
    loc = fresh_consts(a, shared)
    sa = Solver()
    sa.set("timeout", TIMEOUT_MS)
    sa.add(a)
    sb = Solver()
    sb.set("timeout", TIMEOUT_MS)
    sb.add(b)
    itps = []
    for _ in range(max_iter):
        r = sa.check()
        if r == unsat:
            return mk_or(itps)
        if r != sat:
            return None
        m = sa.model()
        proj = m.project(loc, a) if loc else a
        if not symbols(proj) <= shared:
            return None
        cube = flatten_and(proj)
        tags = [z3.FreshBool("t") for _ in cube]
        sb.push()
        for t, c in zip(tags, cube):
            sb.add(z3.Implies(t, c))
        r = sb.check(*tags)
        core = {t.get_id() for t in sb.unsat_core()} if r == unsat else None
        sb.pop()
        if core is None:
            return None
        gen = mk_and([c for t, c in zip(tags, cube) if t.get_id() in core])
        itps.append(gen)
        sa.add(Not(gen))
    return None


def shared_atoms(a, b, shared):
    """The ground atoms of a and b over the shared vocabulary, and equalities between shared terms."""
    atoms, terms, seen, stack = {}, {}, set(), [a, b]
    connectives = (z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT, z3.Z3_OP_IMPLIES, z3.Z3_OP_XOR, z3.Z3_OP_ITE)
    while stack:
        e = stack.pop()
        if e.get_id() in seen or not is_app(e):
            continue
        seen.add(e.get_id())
        stack.extend(e.children())
        if not symbols(e) <= shared:
            continue
        kind = e.decl().kind()
        if not z3.is_bool(e):
            terms.setdefault(e.sort(), {})[e.get_id()] = e
        elif not (kind in connectives or (z3.is_eq(e) and z3.is_bool(e.arg(0))) or z3.is_true(e) or z3.is_false(e)):
            atoms[e.get_id()] = e
    for group in terms.values():
        for x, y in itertools.combinations(sorted(group.values(), key=lambda t: t.get_id()), 2):
            if x.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
                eq = x == y
                atoms[eq.get_id()] = eq
    return list(atoms.values())


def shared_atom_interpolant(a, b, shared, max_iter=200):
    """Model-based interpolation for ground problems that projection cannot handle. MBP has no way to
    eliminate a local constant of an uninterpreted sort from a literal like q(c). Instead of projecting
    it away, read each model of a through the shared atoms alone, and generalise with an unsat core of
    b. The result is quantifier-free by construction. None if those atoms cannot separate a and b."""
    if any(is_quantifier(x) for f in (a, b) for x in _subterms(f)):
        return None
    atoms = shared_atoms(a, b, shared)
    sa = Solver()
    sa.set("timeout", TIMEOUT_MS)
    sa.add(a)
    sb = Solver()
    sb.set("timeout", TIMEOUT_MS)
    sb.add(b)
    itps = []
    for _ in range(max_iter):
        r = sa.check()
        if r == unsat:
            return mk_or(itps)
        if r != sat:
            return None
        m = sa.model()
        cube = [x if z3.is_true(m.eval(x, model_completion=True)) else Not(x) for x in atoms]
        tags = [z3.FreshBool("t") for _ in cube]
        sb.push()
        for t, c in zip(tags, cube):
            sb.add(z3.Implies(t, c))
        r = sb.check(*tags)
        core = {t.get_id() for t in sb.unsat_core()} if r == unsat else None
        sb.pop()
        if core is None:
            return None
        gen = mk_and([c for t, c in zip(tags, cube) if t.get_id() in core])
        itps.append(gen)
        sa.add(Not(gen))
    return None


def _subterms(e):
    seen, stack = set(), [e]
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        yield x
        if is_quantifier(x):
            stack.append(x.body())
        elif is_app(x):
            stack.extend(x.children())


def flatten_and(e):
    if is_and(e):
        return [x for c in e.children() for x in flatten_and(c)]
    return [e]


def qe_interpolant(a, b, shared):
    """Strongest interpolant  Exists(local). a  via Z3's QE tactic."""
    if any(d.arity() > 0 and d not in shared for d in symbols(a)):
        return None
    loc = fresh_consts(a, shared)
    if not loc:
        return a
    g = z3.Tactic("qe")(Exists(loc, a))
    r = mk_or([mk_and(list(sub)) for sub in g])
    return None if not symbols(r) <= shared else r


def binary_interpolant(a, b, shared):
    """Last resort: the z3 executable's (get-interpolant A B) command
    (qe::interpolator::pogo), which is not reachable from the API."""
    s = Solver()
    s.add(a, b)
    decls = [l for l in s.sexpr().splitlines() if l.startswith("(declare")]
    script = "\n".join(decls) + f"\n(get-interpolant {a.sexpr()} {b.sexpr()})\n"
    out = subprocess.run([Z3_BINARY, "-in"], input=script, capture_output=True,
                         text=True, timeout=TIMEOUT_MS / 1000).stdout.strip()
    if not out or out in ("sat", "unknown") or out.startswith("(error"):
        return None
    env = {d.name(): d for d in symbols(a) | symbols(b)}
    return z3.parse_smt2_string(f"(assert {out})", decls=env)[0]


def simplify_itp(i):
    try:
        g = z3.Then("simplify", "qe-light")(i)
        r = mk_or([mk_and(list(sub)) for sub in g])
        if check([Not(i == r)]) == unsat:
            return r
    except z3.Z3Exception:
        pass
    return z3.simplify(i)


def verify(a, b, i, shared=None):
    """True iff a |= i, b /\\ i unsat, and (if given) L(i) <= shared.
    Returns the failing reason otherwise."""
    if shared is not None and not symbols(i) <= set(shared):
        return f"vocabulary: {symbols(i) - set(shared)}"
    r = check([a, Not(i)])
    if r != unsat:
        return "A does not imply I" if r == sat else "A -> I: z3 says unknown"
    r = check([b, i])
    if r != unsat:
        return "B /\\ I satisfiable" if r == sat else "B /\\ I: z3 says unknown"
    return True


def interpolate(A, B, verbose=False, deadline=None, pipeline=None):
    """Return (interpolant, Interpolator) for the unsat conjunction A /\\ B,
    where A and B are lists of Z3 Boolean formulas. A deadline, in time.time() terms, raises
    DeadlineReached when it passes, checked before each lemma. `pipeline` orders the secondary
    interpolators (see Interpolator); None means DEFAULT_PIPELINE."""
    if deadline is not None and time.time() > deadline:
        raise DeadlineReached()
    it = Interpolator(A, B, verbose, deadline, pipeline)
    return it.run(), it


def run_big_stack(fn, *args):
    """Proof DAGs can be deep; run fn with a large recursion budget."""
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}

    def target():
        try:
            box["r"] = fn(*args)
        except BaseException as ex:      # noqa: BLE001 - re-raised below
            box["e"] = ex
    t = threading.Thread(target=target)
    t.start()
    t.join()
    if "e" in box:
        raise box["e"]
    return box["r"]


def annotated_listing(it, width=70):
    """After it.run(): the imported proof, one line per node, with the
    partial interpolant computed for it (or '.' if none was needed)."""
    num = {n.uid: i + 1 for i, n in enumerate(it.nodes)}
    out = []
    for n in it.nodes:
        prem = ",".join(f"{num.get(p.uid, '*')}" for p in n.prem)
        c = " ".join(str(n.concl).split())
        c = c if len(c) <= width else c[:width - 3] + "..."
        side = f" {n.side}" if n.side else ""
        phi = it.memo.get(n.uid)
        phi = "." if phi is None else " ".join(str(z3.simplify(phi)).split())
        out.append(f"[{num[n.uid]:>2}] {n.rule}{side}({prem})  |- {c}\n"
                   f"      itp: {phi}")
    return "\n".join(out)

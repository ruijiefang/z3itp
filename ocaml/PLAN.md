# Plan: an OCaml port of `z3itp.py`

> **Status (implemented).** Milestones M0–M5 are done; M6 (the follow-on
> improvements) is open. See `README.md` for the result:
> - **Tests:** hand-written 16/16, BMC 8/8, random sweeps 100/100; debug mode
>   (invariant at every node) passes on the hand-written, BMC and random
>   cases.
> - **Parity:** on the shared 119-case corpus, both implementations verify
>   all 119, with the Python side pinned to z3-solver 4.16.0.0.
>
> The decisions of §8 were all taken as recommended. Decision 3 was later
> reversed: the `z3`-binary stage has been removed, and the secondary
> prover's stages are `[farkas; mbp; qe]`. The rest of this plan is kept as
> written.

This plan covers porting the Python interpolator (`z3itp.py`, 911 lines), its
test driver (`test_z3itp.py`) and the proof dumper (`dump_proof.py`) to OCaml,
using Z3's OCaml bindings. It is based on a full read of the Python sources and
on two probe programs that check the parts of the OCaml API the port depends on
(§2.2).

## 1. Scope

**In scope: a faithful port.** Same pipeline, same decisions, same statistics,
same failure behaviour as the Python version as it stands today:

1. proof import;
2. colouring of fresh symbols;
3. axiom elimination (localising `quant-inst`);
4. translation into the interpolation calculus (LOCAL / RES / CONTRA);
5. lemma extraction;
6. the secondary prover, with stages trivial → Farkas → MBP loop → QE →
   `z3` binary;
7. ELIM, the final simplification, `verify`, the debug `check_node`, and the
   annotated listing.

**Out of scope for the port, planned as a follow-on (§6, M6).** The changes
discussed after the Python version was written:

- an explicit `∃x̄. Ack(A')` fallback;
- a purified-MBP attempt;
- a strength setting (strong / weak / balanced);
- dropping or flag-gating the binary stage;
- making QE an optional post-pass.

The secondary prover will be a *list of stage functions*, so these can be added
without restructuring.

**Not ported:** the documents under `docs/` and the one-off experiment scripts.

## 2. Toolchain and verified facts

### 2.1 Environment (opam switch `default`)

| Component | Version |
|---|---|
| OCaml | 5.4.1 |
| dune | 3.23.1 |
| Z3 OCaml bindings (opam `z3`) | 4.16.0 |
| zarith | 1.14 |
| ounit2 | 2.2.7 |
| cmdliner | 2.1.1 |
| `z3` executable (for the binary stage) | 4.16.0 |

**Version skew.** The Python results so far came from pip `z3-solver` 5.1.0.0.
The OCaml bindings are 4.16.0, and proofs differ between the two in detail.
In the 4.16 probe, `quant-inst`'s instance clause is already flattened and
the quantifier carries a `:pattern`.

**Decision:** for parity runs, pin the Python side to `z3-solver==4.16.0.0`
in a fresh venv. The scratchpad venv used so far has been removed, and whether
4.16.0.0 is on PyPI is still to be checked. If it isn't, the fallback is to
compare outcomes only (§5) and to document the skew.

### 2.2 API facts verified with probe programs

| Need | OCaml API | Verified |
|---|---|---|
| proof-enabled context | `Z3.mk_context [("proof","true"); ("model","true")]` | ✔ proofs returned |
| proof DAG | `Solver.get_proof : solver -> Expr.expr option` | ✔ |
| rule of a node | `FuncDecl.get_decl_kind (Expr.get_func_decl n)` gives `Z3enums.OP_PR_*`; `FuncDecl.get_name` gives the printed name | ✔ |
| premises / conclusion | `Expr.get_args n`; the last element is the conclusion | ✔ |
| parameters | `FuncDecl.get_parameters`: `P_Sym` (theory name), `P_Int`/`P_Rat` (coefficients), `P_Ast` (`quant-inst` terms, converted with `Expr.expr_of_ast`) | ✔ `quant-inst {ast:c}` |
| model-based projection | **not** in `z3.mli`; only `Z3native.qe_model_project` | ✔ via a re-declared stub (below) |
| rationals | `Arithmetic.Real.get_ratio : expr -> Q.t`; `Real.mk_numeral_s ctx (Q.to_string q)` accepts `"-3/4"` | ✔ round-trips |
| re-parsing SMT-LIB | prepend the `(declare-…)` lines from `Solver.to_string`, call `SMT.parse_smtlib2_string ctx text [] [] [] []` | ✔ yields the *same* decls (`FuncDecl.equal`) |

How the projection stub works:

- In `z3.ml` every handle type is an alias of the same native pointer type
  (`type context = Z3native.context`, `type expr = AST.ast = Z3native.ast`,
  `type model = Z3native.model`); they are only abstract in `z3.mli`.
- So the port binds projection by re-declaring the existing C stub with
  high-level types, with no `Obj.magic`:

```ocaml
external qe_model_project :
  Z3.context -> Z3.Model.model -> int -> Z3.Expr.expr list -> Z3.Expr.expr -> Z3.Expr.expr
  = "n_qe_model_project"
```

- Probe result: projecting `x` from `y ≤ x ∧ x ≤ 3` gave `y ≤ 3`.

## 3. Layout

```
ocaml/
  dune-project
  lib/                      library z3itp
    util.ml                 expression helpers, symbol sets, solver checks, verify
    native.ml               the re-declared qe_model_project stub
    proof.ml                node type + proof import
    interp.ml               interpolator state, colouring, axiom elimination,
                            sequents, S_I translation, lemma extraction, ELIM, run
    secondary.ml            abstract_quantifiers, ackermannize, linearize/ineq,
                            farkas, mbp, qe, binary, simplify_itp; stage list
    listing.ml              dump_proof listing + annotated listing
  bin/
    dump_proof.ml           port of dump_proof.py (built-in examples)
  test/
    cases.ml                the 16 hand-written cases + BMC generator
    corpus.ml               reads the shared SMT-LIB corpus (§5)
    test_z3itp.ml           runner: verify every interpolant, print stats
  corpus/                   generated by scripts/dump_corpus.py (§5)
scripts/
  dump_corpus.py            Python: writes the corpus from test_z3itp.py
```

Library dependencies: `z3`, `zarith`, `unix` (binary stage only). Tests use
plain executables with exit codes; ounit2 is optional. No CLI yet; a cmdliner
CLI that reads an A/B pair from SMT-LIB can come later.

## 4. Python → OCaml mapping

### 4.1 Cross-cutting decisions

**One context, threaded explicitly.**
- The Python code relies on the global `set_param(proof=True)`.
- In OCaml, every formula (test cases, parsed corpus, everything the
  interpolator builds) must live in a single context created with
  `[("proof","true"); ("model","true")]`.
- The interpolator record carries `ctx`. Solvers created for checks in that
  context also run in proof mode, as in Python.

**Identity and hashing: never key on bare ids.**
- Python's worst bug was `get_id()`-keyed caches returning stale results after
  Z3 recycled ids.
- In OCaml, every table and set is keyed on the *object*:

```ocaml
module EH = Hashtbl.Make (struct
  type t = Z3.Expr.expr
  let equal = Z3.Expr.equal
  let hash e = Z3.AST.hash (Z3.Expr.ast_of_expr e)
end)
module ES = Set.Make (struct type t = Z3.Expr.expr let compare = Z3.Expr.compare end)
module FS = Set.Make (struct
  type t = Z3.FuncDecl.func_decl
  let compare a b = compare (Z3.FuncDecl.get_id a) (Z3.FuncDecl.get_id b)
end)
```

- Keys and elements keep their Z3 objects alive, so ids cannot be recycled
  under them.
- Rule for the code base: no `Hashtbl` keyed on `int` ids.
- `FS.compare` uses ids, but only to compare elements that the set itself keeps
  alive.

**Rules as a variant.**
- Dispatch on `Z3enums.decl_kind` rather than on printed names.
- `eliminate_axioms` rewrites nodes, so the variant also carries the three
  synthetic rules.

```ocaml
type rule =
  | Asserted | Hypothesis | Lemma | Unit_resolution | Quant_inst
  | Sk | Intro_def | Th_lemma
  | Other of string                 (* mp, rewrite, trans*, ... : name kept for listings/stats *)
  | Quant_inst_local | Definition | Elim_subst      (* synthetic *)

type side = A | B

type node = {
  uid : int;
  mutable rule : rule;
  mutable prem : node list;
  concl : Z3.Expr.expr;
  mutable side : side option;
  params : Z3.FuncDecl.Parameter.parameter list;
  mutable hyps : ES.t option;                  (* lazily computed caches *)
  mutable sides : side list option;
  mutable delta : Z3.Expr.expr list option;    (* ordered; see 4.3 *)
}
```

**Deep proofs.**
- In OCaml 5 the OCaml stack is heap-allocated and growable up to the
  `OCAMLRUNPARAM=l=…` limit, so `run_big_stack` has no counterpart.
- `import_proof` stays iterative, as in Python. The `interp` recursion stays
  recursive. The README will document `l=` as the escape hatch.

**Errors.**
- Python's `except Exception` around each secondary stage becomes
  `try … with Z3.Error _ | Failure _ | Not_found -> None`.
- `RuntimeError`/`ValueError` become exceptions declared in `Interp`.

**Timeouts.**
- `Params.mk_params ctx`, then `Params.add_int p (Symbol.mk_string ctx "timeout") ms`,
  then `Solver.set_parameters`.

### 4.2 Function-by-function

| Python (`z3itp.py`) | OCaml | Notes |
|---|---|---|
| `neg`, `lits`, `is_complement`, `mk_or`, `mk_and`, `flatten_and` | `Util` | `Boolean.is_not/is_or/is_and/is_true/is_false`; `mk_or`/`mk_and` keep Python's simplifications (drop `false`/`true`, short-circuit, singleton) |
| `oeq_to_iff` | `Util.oeq_to_iff` | memoised with `EH`; detect `OP_OEQ` via `get_decl_kind`; rebuild Boolean apps with `FuncDecl.apply` |
| `symbols` + `_sym_cache` | `Util.symbols` | per-interpolator `EH` cache (the Python cache was global and unbounded); traverse quantifier bodies via `Quantifier.get_body`; collect decls with `OP_UNINTERPRETED` |
| `fresh_consts` | `Util.fresh_consts` | `Expr.mk_const ctx (FuncDecl.get_name d) (FuncDecl.get_range d)` for arity-0 non-shared decls |
| `check` | `Util.check ?timeout` | new solver per call, as in Python |
| `verify` | `Util.verify` | returns a variant: `` `Ok | `Vocabulary of FS.t | `A_not_implies | `B_sat | `Unknown_A | `Unknown_B ``, not `True`/string |
| `Node`, `import_proof` | `Proof.import` | iterative post-order with an `EH` memo; `asserted` side by membership in the A/B lists via `Expr.equal`; collect stats per rule |
| `Interpolator.__init__`, `col`, `local_to`, `shared` | `Interp.t` record + functions | `la`, `lb : FS.t ref`; `col` prefers B, exactly as Python |
| `solve` | `Interp.solve` | solver in the proof context; error if not unsat |
| `colour_fresh_symbols` | `Interp.colour_fresh_symbols` | rules `Sk`/`Intro_def` with no premises; `src = arg 0` for `sk` with two args; same stats (`uncoloured_fresh_defs`, `stray_symbols`) |
| `new_def`, `localise_term`, `_replace_maximal_local` | `Interp` | `def_cache : expr EH.t` keyed on the term object (not id); `Expr.mk_fresh_const ctx "loc" sort`; 64-iteration bound kept |
| `eliminate_axioms` | `Interp.eliminate_axioms` | shape check `or(not(∀…), inst)`; terms from `P_Ast` params; `Expr.substitute_vars body (List.rev terms)` must equal `inst`; B→A side preference; the definition-collection logic (new, reused, nested) ported line by line; mutate `rule`/`prem` |
| `hyps`, `sides`, `clause_lits`, `as_clause_lits`, `delta`, `strict_formula`, `strict` | `Interp` | see §4.3 for ordering and set semantics |
| `interp` (memo), `_interp` | `Interp.interp` | memo `(int, expr) Hashtbl` keyed on node `uid` (our own counter, safe) |
| `side_axioms`, `check_node` | `Interp` | debug mode flag; same checks and messages |
| `split_view_strict`, `as_clause`, `as_unit`, `_moved`, `native_unit_resolution`, `_unit_resolution` | `Interp` | preserve the operator precedence in `as_unit` (§4.3) |
| `_lemma` | `Interp.lemma` | frontier walk with seen-set on `uid`, dedup by conclusion via `ES`; `inner` count for `lemma_sizes` |
| `secondary_interpolant` | `Secondary.run` | trivial checks (2 s), then `abstract_quantifiers`, `ackermannize`, then a **stage list** `[farkas; mbp; qe; binary]` of type `ctx -> expr -> expr -> FS.t -> expr option`; each result un-abstracted with `Expr.substitute` and accepted only if `verify` returns `` `Ok`` |
| `abstract_quantifiers` | `Secondary` | returns the extended shared set (Python mutated a copy through the walrus) |
| `linearize`, `z3_fraction`, `ineq`, `farkas_interpolant`, `float_free` | `Secondary` | polynomials as `(expr option, Q.t) EH`-like maps; numerals via `Arithmetic.Integer.get_big_int`/`Real.get_ratio`; LP over `lam_i` Real consts; model values via `Model.eval m e true` then `get_ratio`; scaling with `Z.lcm`; Int output when all atoms are Int |
| `ackermannize` | `Secondary` | `EH` memo; per-decl list of `(args, const)`; pairwise constraints |
| `mbp_interpolant` | `Secondary` | uses `Native.qe_model_project ctx m (List.length loc) loc a`; tracking literals via `Expr.mk_fresh_const ctx "t" bool`; `Solver.push/pop`, `check s tags`, `get_unsat_core`; cap of 200 |
| `qe_interpolant` | `Secondary` | `Tactic.mk_tactic ctx "qe"` on a goal holding `∃loc. a`; disjunction of subgoal conjunctions |
| `binary_interpolant` | `Secondary` (behind a flag, default on for parity) | `Unix.open_process_args "z3" [|"z3";"-in"|]`; script = declarations + `(get-interpolant …)` using `Expr.to_string`; parse the answer with prepended declarations (§2.2) |
| `simplify_itp` | `Secondary.simplify_itp` | `Tactic.and_then ctx (mk "simplify") (mk "qe-light") []`; keep only if `¬(i = r)` is unsat; else `Expr.simplify i None` |
| `run` | `Interp.run` | ELIM: for `s` in reverse introduction order, if `s`'s decl occurs in the interpolant, wrap with `Quantifier.mk_forall_const` (B-side) / `mk_exists_const` (A-side) and `expr_of_quantifier` |
| `interpolate` | `Z3itp.interpolate : ctx -> expr list -> expr list -> expr * Interp.t` | |
| `run_big_stack` | none | see deep proofs above |
| `annotated_listing` | `Listing.annotated` | same format |
| `dump_proof.listing`/`examples` | `Listing.proof`, `bin/dump_proof.ml` | same `[k] rule{params} (premises) |- conclusion` format |

### 4.3 Behaviours that are easy to get subtly wrong

1. **`col` prefers B.** A formula in both vocabularies is colored B.
2. **`delta` contents.** Negated hypotheses first, then `clause_lits`, with
   duplicates merged. Python used an id-keyed dict, preserving insertion order.
   Use an `ES` for membership and a list for order. Order only changes the
   printed shape of interpolants, never their correctness.
3. **`clause_lits` for `unit-resolution`:**
   - the 2-premise complement case returns `[]`;
   - otherwise remove *one* complementary literal per unit;
   - a single remaining `or` is one literal.

   **For `lemma`:** a single hypothesis whose negation equals the conclusion
   gives `[concl]`.
4. **CONTRA test** compares the *key sets* of `delta(p)` and `delta(n)`, not
   the lists.
5. **`as_unit` precedence.** Python's condition
   `len(nat) == 1 and nat[0].eq(p.concl) or col(concl) == "B"` parses as
   `(… and …) or …`. Port it with explicit parentheses.
6. **`_moved`** excludes literals that coincide with negated hypotheses.
7. **`_unit_resolution` pivot fallback.** If no complementary literal is
   found, the pivot is the clause's conclusion (the 2-premise `p, ¬p` form).
8. **`_lemma` frontier condition:** not a hypothesis, `hyps ⊆ hyps(N)`, strict
   node, and colored conclusion. Dedupe frontier facts by conclusion.
9. **Secondary inputs** go through `oeq_to_iff` *before* the trivial checks
   (Python applies it in `_lemma`).
10. **`abstract_quantifiers`:**
    - collects only *outermost* quantifiers;
    - an atom is shared iff the quantified formula's symbols are shared;
    - if the abstraction makes the pair satisfiable, return the originals and
      an empty undo list.
11. **`ackermannize`** is applied to `a2` only, never to `b2`.
12. **`qe_interpolant`** returns `a` unchanged when there are no local
    constants.
13. **`eliminate_axioms`** mutates `rule` and `prem` of the `quant-inst` node.
    The synthetic leaves get fresh `uid`s from the same counter.
14. **`run`** wraps ELIM quantifiers only for localisation constants that
    actually occur in the interpolant.
15. **The `quant-inst` shape depends on the Z3 version. This one matters.**
    - Under z3-solver 5.1 (Python), the conclusion is nested:
      `or(not ∀x.φ, inst)`, with exactly two arguments.
    - Under 4.16 (the OCaml probe), it is *flattened*:
      `(or (not ∀x.φ) (P c) (>= (+ a (* -1 c)) 0))`.
    - Python's `eliminate_axioms` (lines 288–295) only accepts the 2-argument
      shape. Ported literally, it would silently never localise anything under
      4.16.
    - The port must accept both shapes. Let `inst' = substitute_vars body
      (List.rev terms)`. The node qualifies if the disjuncts after `not ∀x.φ`
      are exactly `[inst']`, or exactly the disjuncts of `inst'` when `inst'` is
      an `or`.
    - The localised leaf must be rebuilt in the *same* shape, so the
      `elim-subst` lemma stays a pure congruence step.
    - Check this first in M4, on `quant-2var`.

## 5. Parity harness

**The problem.** Python's `random.Random(1)` stream can't be reproduced in
OCaml, so the two implementations must read the *same inputs*.

**The corpus.**
- `scripts/dump_corpus.py` (Python) writes every test input:
  - the 16 hand-written cases;
  - the random cases (seeded generator, three sizes);
  - the BMC cases.
- Each case gets a directory with `A.smt2` and `B.smt2`. Each file holds the
  full declarations plus `(assert …)` lines, one per conjunct. No `:named`
  annotations.
- `test/corpus.ml` parses both files into the shared context.
  Same-named declarations resolve to the same symbols (§2.2).

**What is compared per case:**
- verified yes/no;
- number of lemmas;
- the winning secondary stage per lemma;
- whether any secondary stage failed.

Not compared: interpolant text (set iteration order and Z3 version differ),
per-rule counts if the Z3 versions differ.

**Reports.**
- `test_z3itp.exe` prints the same one-line-per-case report as
  `test_z3itp.py`.
- A small diff script compares the two reports.

**Debug parity.** Running with `check_node` on (per-node invariant) must pass
on the hand-written cases and the BMC cases, as in Python.

## 6. Milestones

| | Content | Done when |
|---|---|---|
| M0 | dune scaffold, `Util`, `Native`; smoke test of projection + parsing | builds; smoke test passes |
| M1 | `Proof.import` + `bin/dump_proof` | listings match Python's `dump_proof.py` (same Z3 version) on its built-in examples |
| M2 | colouring, sequents, LOCAL / RES / CONTRA | zero-lemma cases verify: propositional, `quant-A`, `quant-foreign-witness`, `arrays`, enum and `dt-exhaust` from the datatype probe |
| M3 | lemma extraction + all secondary stages | all hand-written cases verify |
| M4 | axiom elimination, ELIM, debug `check_node`, `simplify_itp`, annotated listing | `quant-2var` produces the ∀-closed interpolant; debug mode passes |
| M5 | corpus + parity harness + BMC + random sweeps | per-case parity report clean, or every difference explained |
| M6 (follow-on) | improvements from §1 as new stages / options | each with tests from the purification/fallback experiments |

## 7. Deliberate deviations (to keep parity diffs explainable)

1. **`linearize`'s `is_sub` branch.** Python ignores a `None` (non-linear)
   result from the first operand. The port checks it and fails the whole
   linearisation. This is a bug fix; it can only turn a Farkas success into
   a fall-through, never change a verified answer.
2. **The symbol cache is per interpolator,** not process-global.
3. **`verify` returns a variant;** the reports print the same strings.
4. **Rule dispatch uses `decl_kind`,** not printed names. Same behaviour; only
   the printed names in listings come from `FuncDecl.get_name`.
5. **Interpolant shape** may differ by conjunct/disjunct order, because of
   set iteration order.
6. **`eliminate_axioms` accepts the flattened `quant-inst` shape** (§4.3,
   item 15). This is a fix for a version dependency the Python code never
   hit.

## 8. Decisions for you (with my recommendation)

1. **Pin Python to `z3-solver==4.16.0.0` for parity runs.** Recommended. Without
   it, OCaml-vs-Python differences can't be attributed.
2. **Faithful port first, improvements later (M6).** Recommended.
3. **Keep the `z3`-binary stage, behind a flag that defaults to on** for
   parity. Recommended; it is the only stage needing `unix` and an external
   executable.
4. **Deliverables: library + test executable + `dump_proof`, no CLI yet.**
   Recommended; a cmdliner CLI reading an A/B pair from SMT-LIB is a small
   later addition.
5. **Location: `ocaml/` inside this repository**, with the corpus generator
   in `scripts/`. Recommended.

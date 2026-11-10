(** The secondary interpolating prover.

    Lemma extraction ({!Interp}) cuts the Z3 proof into small valid clauses
    ("lemmas"). For each lemma it calls {!interpolate} on a pair [(a, b)] with
    [a /\ b] unsatisfiable, where [a] uses only A's vocabulary and [b] only
    B's. The result must be an interpolant for the pair: [a |= i],
    [b /\ i] unsatisfiable, and [L(i)] contained in the shared symbols.

    McMillan's paper used a separate interpolating QF_UFLIA solver here. Z3's
    API has no interpolation, so this module assembles one from public API
    calls. The pipeline is that of [secondary_interpolant] in [z3itp.py]:

    + {b trivial cases}: [a] alone unsatisfiable gives [false]; [b] alone
      unsatisfiable gives [true] (2-second checks);
    + {b preparation}: quantified sub-formulas become Boolean atoms
      ({!abstract_quantifiers}); A-local function symbols are removed by
      Ackermann's reduction ({!ackermannize});
    + {b stages}, tried in order, the first {e verified} result winning:
      {!farkas} (linear arithmetic, Farkas certificate from an LP), {!mbp}
      (model-based interpolation loop), and {!qe} (quantifier elimination).

    [z3itp.py] has one more, last-resort stage, which runs the [z3]
    executable on [(get-interpolant a b)]. It is not ported: everything here
    goes through the library API, with no external process.

    Every stage result has the quantifier abstraction undone and is accepted
    only if {!Util.verify} returns [Ok]; a stage that fails, returns
    nothing, or raises a Z3 error simply passes control to the next stage. *)

open Z3

(** {1 Stages} *)

type stage = {
  name : string;  (** used in statistics as ["2nd:" ^ name] *)
  run : context -> Expr.expr -> Expr.expr -> Util.FS.t -> Expr.expr option;
      (** [run ctx a b shared] proposes an interpolant, or [None] *)
}

val farkas : stage
(** Linear-arithmetic interpolation. Every conjunct of [a] and [b] must be a
    linear (in)equality, with non-arithmetic subterms treated as opaque
    variables. Multipliers [lam_i] (non-negative except for equalities) are
    found by a Z3 check such that the combination [sum lam_i * p_i] is a
    positive constant, or a non-negative one with a strict row. The
    interpolant is the A-part of the combination, [sum_{i in A} lam_i * p_i]
    compared with [0], scaled to integer coefficients. Sound over the
    integers too, but incomplete there. Z3's own [farkas] hints are not used
    because they are often missing. *)

val mbp : stage
(** Model-based interpolation: the "pogo" loop of Z3's [qe_mbi.cpp]
    re-implemented with the public projection {!Native.project}. Repeatedly:
    take a model of [a] (minus the cubes found so far), project away the
    non-shared constants, shrink the projection to an unsat core of [b], and
    block it. Returns the disjunction of the cubes once [a] is exhausted. Gives
    up (returns [None]) if [a] still contains non-shared function symbols, if
    a projection keeps a non-shared symbol, if a cube is not refuted by [b],
    on a solver [unknown], or after 200 iterations. *)

val qe : stage
(** Strongest interpolant [exists loc. a] through Z3's [qe] tactic, where
    [loc] are the non-shared constants of [a]. May leave an existential
    quantifier when Z3 cannot eliminate a constant. *)

val default_stages : stage list
(** [[farkas; mbp; qe]]. *)

(** {1 Preparation} *)

val abstract_quantifiers :
  context -> Expr.expr -> Expr.expr -> Util.FS.t -> Expr.expr * Expr.expr * (Expr.expr * Expr.expr) list * Util.FS.t
(** [abstract_quantifiers ctx a b shared] replaces every outermost quantified
    sub-formula of [a] and [b] by a fresh Boolean constant (the same constant
    for the same formula on both sides). Returns [(a', b', undo, shared')],
    where [undo] lists [(atom, formula)] pairs and [shared'] adds the atoms
    whose formula uses only shared symbols. If [a' /\ b'] is not
    unsatisfiable (the lemma depended on reasoning inside a quantifier), the
    abstraction is abandoned and [(a, b, [], shared)] is returned.

    Sound because an interpolant of the abstracted pair, with the formulas
    substituted back for the atoms, is an interpolant of the original pair:
    substituting a formula for a propositional atom preserves validity. *)

val ackermannize : context -> Expr.expr -> Util.FS.t -> Expr.expr
(** [ackermannize ctx a shared] replaces every application [g(t)] of a
    function symbol [g] that is not in [shared] (outside quantifiers) by a
    fresh constant [v], and conjoins [t1 = t2 -> v1 = v2] for every pair of
    applications of the same symbol. Exact for interpolation: every model of
    [a] extends to a model of the result and conversely (by redefining [g],
    which the other side does not mention), and the fresh constants never
    reach an interpolant. *)

(** {1 Driver} *)

exception Failed of Expr.expr * Expr.expr
(** No stage produced a verified interpolant for the pair [(a, b)]. *)

val interpolate :
  ?stages:stage list -> count:(string -> unit) -> context -> Util.FS.t -> Expr.expr -> Expr.expr -> Expr.expr
(** [interpolate ~count ctx shared a b] runs the pipeline described above and
    returns a verified interpolant. [count] is called with the name of each
    event (["2nd:A-unsat"], ["2nd:farkas"], ["2nd:FAILED"], ...), for the
    statistics. [a] and [b] must not contain the [~] connective (see
    {!Util.oeq_to_iff}).
    @raise Failed when every stage fails. *)

(** {1 Post-processing} *)

val simplify_itp : context -> Expr.expr -> Expr.expr
(** Simplify a final interpolant with the tactics [simplify] then
    [qe-light], keeping the result only if Z3 confirms it is equivalent;
    otherwise fall back to [Expr.simplify]. *)

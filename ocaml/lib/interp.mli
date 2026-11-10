(** Interpolants from Z3 proofs: the main algorithm.

    An OCaml port of the [Interpolator] class of [z3itp.py], which implements
    K. L. McMillan, {e Interpolants from Z3 proofs} (FMCAD 2011). Given lists
    of formulas [A] and [B] whose conjunction is unsatisfiable, {!interpolate}
    returns a formula [I] with [A |= I], [B /\ I] unsatisfiable, and every
    uninterpreted symbol of [I] occurring in both [A] and [B].

    {1 Pipeline}

    {!run} performs, in order (paper section IV.F):

    + {b solve} [A /\ B] with proofs and {b import} the proof DAG
      ({!Proof_dag.import});
    + {b colour fresh symbols} ({!colour_fresh_symbols}): Skolem constants and
      Tseitin names introduced by Z3 become local to the side of the formula
      they name, and their defining leaf counts as an assertion of that side;
    + {b axiom elimination} ({!eliminate_axioms}, paper IV.C): every
      [quant-inst] leaf whose instance mixes A-only and B-only symbols is
      rewritten into a local instance [phi[s]] plus definitions [s = t],
      where the fresh {e localisation constants} [s] count as shared;
    + {b translation} into the interpolation calculus S_I (paper Fig. 1),
      node by node ({!interp}): LOCAL for one-sided sub-proofs, RES for
      [unit-resolution], CONTRA for [lemma];
    + {b lemma extraction} (paper IV.B): any other node is replaced by a
      LEMMA whose premises are its nearest "strict" descendants, and the
      lemma is interpolated by {!Secondary.interpolate};
    + {b ELIM} (paper IV.C): the localisation constants are quantified out of
      the interpolant, [forall] for B-side definitions and [exists] for A-side
      ones, in reverse order of introduction; then the result is simplified.

    {1 Sequents and partial interpolants}

    Every proof node proves a one-sided sequent [(A, B) |- Delta], where
    [Delta] ({!delta}) holds the literals of its conclusion and the negations
    of its open hypotheses. A formula is coloured ({!col}) [B] if its symbols
    occur in [B], else [A] if they occur in [A], else it is uncoloured; a node
    is {e strict} if every member of its [Delta] is coloured. Writing
    [Delta_B] for the [B]-coloured members and [Delta_A] for the rest, a
    {e partial interpolant} [phi] of a node satisfies

    - [A /\ not Delta_A |= phi],
    - [B /\ not Delta_B /\ phi] is unsatisfiable,
    - [L(phi)] contained in the shared symbols.

    At the root [Delta] is empty, so the root's partial interpolant is an
    interpolant. [docs/INTERPOLATION-GUIDE.md] explains every rule, with
    proofs and worked examples. *)

open Z3

(** {1 State} *)

type t
(** An interpolation problem and everything computed for it. *)

val create : ?debug:bool -> ?stages:Secondary.stage list -> context -> Expr.expr list -> Expr.expr list -> t
(** [create ctx a b] sets up the problem. [ctx] must have been created with
    proof generation on (see {!make_context}), and every formula of [a] and
    [b] must belong to it.
    @param debug check the S_I invariant at every node ({!check_node})
    @param stages secondary-prover stages (default
      [Secondary.default_stages]) *)

val make_context : unit -> context
(** A context with [proof=true] and [model=true]. *)

(** {1 Running} *)

exception Not_unsat of string
(** [A /\ B] is satisfiable or unknown (the status is given). *)

exception Root_not_strict
(** The root sequent mentions an uncoloured formula (cannot happen when every
    symbol of the proof is coloured). *)

exception Check_failed of string
(** Debug mode found a node whose partial interpolant violates the S_I
    invariant; the message names the node and the failing condition. *)

val run : t -> Expr.expr
(** Run the whole pipeline and return the interpolant.
    @raise Not_unsat
    @raise Root_not_strict
    @raise Check_failed in debug mode
    @raise Secondary.Failed when a lemma cannot be interpolated *)

val interpolate :
  ?debug:bool -> ?stages:Secondary.stage list -> context -> Expr.expr list -> Expr.expr list -> Expr.expr * t
(** [interpolate ctx a b] is [let t = create ctx a b in (run t, t)]. *)

(** {1 Results and statistics} *)

val stats : t -> (string * int) list
(** Event counts, sorted by name, with the same keys as the Python version:
    ["proof_nodes"], ["rule:<name>"], ["S_I:LocalA"], ["S_I:LocalB"],
    ["S_I:ResA"], ["S_I:ResB"], ["S_I:Contra"], ["S_I:Lemma"],
    ["2nd:<stage>"], ["qinst_localised"], ["qinst_not_syntactic"],
    ["qinst_unlocalisable"], ["uncoloured_fresh_defs"], ["stray_symbols"],
    ["localisation_constants"]. *)

val stat : t -> string -> int
(** One count (0 if absent). *)

val lemma_sizes : t -> int list
(** For each extracted lemma, the number of proof nodes it replaced
    (including its root), in extraction order. *)

val nodes : t -> Proof_dag.node list
(** The imported proof, premises before conclusions (after {!run}). *)

val partial_interpolant : t -> Proof_dag.node -> Expr.expr option
(** The partial interpolant computed for a node, if one was needed. *)

val shared : t -> Util.FS.t
(** Shared symbols: [L(A) ∩ L(B)], including localisation constants. *)

val localisation_constants : t -> (Expr.expr * Expr.expr * Proof_dag.side) list
(** [(s, t, side)] for every definition [s = t], in introduction order. *)

(** {1 Individual steps}

    Exposed for testing and for the annotated listing; {!run} calls them in
    order. *)

val solve : t -> Expr.expr
(** Solve [A /\ B] with proofs and return the proof term. *)

val colour_fresh_symbols : t -> unit
val eliminate_axioms : t -> unit

val col : t -> Expr.expr -> Proof_dag.side option
(** Colour of a formula: [B] if its symbols are in [L(B)], else [A] if they
    are in [L(A)], else [None]. A shared formula is coloured [B]. *)

val delta : t -> Proof_dag.node -> Expr.expr list
(** The node's one-sided sequent: negated open hypotheses, then the literals
    of its conclusion as the producing rule means them (see
    [docs/Z3-PROOF-FORMAT.md] §7.2), without duplicates. *)

val strict : t -> Proof_dag.node -> bool
val interp : t -> Proof_dag.node -> Expr.expr
(** Partial interpolant of a strict node (memoised). *)

val check_node : t -> Proof_dag.node -> Expr.expr -> unit
(** Debug check of the S_I invariant for [(A, B) |- delta n [phi]], using the
    localisation definitions and Z3's definitional leaves as side axioms.
    @raise Check_failed if a condition is satisfiable *)

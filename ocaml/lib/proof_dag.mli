(** Proof nodes: a mutable copy of Z3's immutable proof DAG.

    A Z3 proof is a term whose head symbol is the {e rule} and whose
    arguments are the {e premises} followed by the {e conclusion} (see
    [docs/Z3-PROOF-FORMAT.md]). {!import} copies that DAG into {!node}
    records. Sharing is preserved: a sub-proof used twice becomes one node.
    The copy is mutable because axiom elimination
    ({!Interp.eliminate_axioms}) rewrites [quant-inst] leaves in place.

    Each node also carries three lazily computed caches used by {!Interp}:
    its open hypotheses, the input sides it depends on, and its one-sided
    sequent [Delta]. *)

open Z3

(** Proof rules. The rules the interpolator dispatches on have their own
    constructors (recognised by [Z3enums.decl_kind], not by printed name);
    every other Z3 rule is [Other name]. The last three constructors are
    {e synthetic}: they never occur in Z3 proofs and are created by axiom
    elimination. *)
type rule =
  | Asserted          (** an input formula; its [side] says A or B *)
  | Hypothesis        (** temporary assumption, discharged by [Lemma] *)
  | Lemma             (** discharges all hypotheses of its premise *)
  | Unit_resolution   (** resolution of a clause against unit facts *)
  | Quant_inst        (** [not (forall x. phi) \/ phi[t]]; parameters: [t] *)
  | Sk                (** Skolemisation, [(exists x. p) ~ p[sk]] *)
  | Intro_def         (** definition of a fresh (Tseitin) name *)
  | Th_lemma          (** theory lemma *)
  | Other of string   (** any other Z3 rule, by printed name *)
  | Quant_inst_local  (** synthetic: localised quantifier instance *)
  | Definition        (** synthetic: localisation definition [s = t] *)
  | Elim_subst        (** synthetic: the original instance, re-derived from
                          the localised one and its definitions *)

val rule_name : rule -> string
(** Printed name, as Z3 prints it (["unit-resolution"], ["sk"], ...);
    synthetic rules print as ["quant-inst-local"], ["definition"],
    ["elim-subst"]. *)

(** Which input side a leaf belongs to. *)
type side = A | B

val side_to_string : side -> string

(** Input sides a sub-proof depends on. *)
type sides = { has_a : bool; has_b : bool }

type node = {
  uid : int;  (** unique per process; also identifies synthetic nodes *)
  mutable rule : rule;
  mutable prem : node list;  (** premises, in Z3's order *)
  concl : Expr.expr;  (** the conclusion *)
  mutable side : side option;
      (** set for [Asserted] leaves, for Skolem/Tseitin leaves coloured by
          {!Interp.colour_fresh_symbols}, and for [Definition] leaves *)
  params : FuncDecl.Parameter.parameter list;  (** rule parameters *)
  mutable hyps : Util.ES.t option;  (** cache: open hypotheses *)
  mutable sides : sides option;  (** cache: input sides used *)
  mutable delta : Expr.expr list option;  (** cache: one-sided sequent *)
}

val fresh_uid : unit -> int
(** Next node id. *)

val mk_node : ?side:side -> ?params:FuncDecl.Parameter.parameter list -> rule -> node list -> Expr.expr -> node
(** Make a node with a fresh [uid] and empty caches. *)

(** Result of {!import}. *)
type imported = {
  root : node;
  nodes : node list;  (** every node, premises before conclusions *)
  rule_counts : (string * int) list;  (** occurrences per printed rule name *)
}

exception Unrecognised_assertion of Expr.expr
(** Raised when an [asserted] leaf is neither in A nor in B (it would mean
    Z3 asserted something we did not give it). *)

val import : a:Expr.expr list -> b:Expr.expr list -> Expr.expr -> imported
(** [import ~a ~b proof] copies the proof DAG rooted at [proof]. The traversal
    is iterative (proofs can be deep) and memoised on the proof term, so
    shared sub-proofs are imported once. [Asserted] leaves get side [A] or
    [B] by comparing their conclusion with the members of [a] and [b] (Z3
    hash-conses terms, so this is object identity). A formula given on both
    sides is classified as [A]. *)

val premises : Expr.expr -> Expr.expr list
(** Premises of a raw Z3 proof term (all arguments but the last). *)

val conclusion : Expr.expr -> Expr.expr
(** Conclusion of a raw Z3 proof term (the last argument). *)

val param_to_string : FuncDecl.Parameter.parameter -> string

(** Expression utilities shared by every other module.

    This module is the OCaml counterpart of the "Expression utilities" section
    of [z3itp.py]: literal and clause helpers, simplifying [and]/[or]
    constructors, the vocabulary function [symbols], solver checks with a
    timeout, and the interpolant checker [verify].

    {1 Identity of Z3 objects}

    Z3 hash-conses ASTs, so two structurally equal expressions are the same
    object, and [Z3.Expr.equal] is pointer equality on the underlying AST.
    Z3 also {e recycles} the integer ids of ASTs that have been freed. The
    Python implementation was bitten by this: a cache keyed on
    [get_id()] returned stale entries after an id was reused.

    The OCaml port therefore never keys a table on a bare integer id. All
    tables and sets below are keyed on the Z3 object itself ({!EH}, {!ES},
    {!FS}, {!FH}); a key held in a table keeps its object alive, so its id
    cannot be recycled while the entry exists. *)

open Z3

(** {1 Tables and sets keyed on Z3 objects} *)

(** Hash tables keyed on expressions ([Expr.equal] / [AST.hash]). *)
module EH : Stdlib.Hashtbl.S with type key = Expr.expr

(** Sets of expressions, ordered by [Expr.compare]. *)
module ES : Stdlib.Set.S with type elt = Expr.expr

(** Sets of function declarations (uninterpreted symbols), ordered by id.
    Ordering by id is safe here because a set keeps its elements alive. *)
module FS : Stdlib.Set.S with type elt = FuncDecl.func_decl

(** Hash tables keyed on function declarations. *)
module FH : Stdlib.Hashtbl.S with type key = FuncDecl.func_decl

(** {1 Expression tests and accessors} *)

val is_app : Expr.expr -> bool
(** [true] for applications (including constants); [false] for quantifiers
    and bound variables. *)

val is_quantifier : Expr.expr -> bool

val kind : Expr.expr -> Z3enums.decl_kind
(** Declaration kind of an application (e.g. [OP_OR], [OP_PR_LEMMA],
    [OP_UNINTERPRETED]). Only valid when [is_app e]. *)

val args : Expr.expr -> Expr.expr list
val arg : Expr.expr -> int -> Expr.expr
val num_args : Expr.expr -> int

val is_not : Expr.expr -> bool
val is_or : Expr.expr -> bool
val is_and : Expr.expr -> bool
val is_true : Expr.expr -> bool
val is_false : Expr.expr -> bool

val decl_name : FuncDecl.func_decl -> string
(** Printed name of a declaration. *)

val to_string : Expr.expr -> string
(** One-line SMT-LIB rendering (newlines and repeated spaces collapsed). *)

(** {1 Literals and clauses} *)

val neg : context -> Expr.expr -> Expr.expr
(** [neg ctx e] is the complement of [e]: the argument of [e] if [e] is a
    negation, [not e] otherwise. Never builds a double negation. *)

val lits : Expr.expr -> Expr.expr list
(** Top-level disjuncts: [[]] for [false], the arguments of an [or], and
    [[e]] otherwise. Never flattens nested [or]s. *)

val is_complement : Expr.expr -> Expr.expr -> bool
(** Z3's [ast_manager::is_complement]: one is the negation of the other,
    or they are [true] and [false]. *)

val flatten_and : Expr.expr -> Expr.expr list
(** Conjuncts of a (nested) conjunction. *)

val mk_or : context -> Expr.expr list -> Expr.expr
(** Disjunction that drops [false], short-circuits on [true], and returns the
    single element of a one-element list. *)

val mk_and : context -> Expr.expr list -> Expr.expr
(** Dual of {!mk_or}. *)

val oeq_to_iff : context -> Expr.expr -> Expr.expr
(** Replace Z3's equisatisfiability connective [~(p, q)] (produced by the
    [sk], [nnf-*] and [apply-def] proof rules) by [p = q], recursively through
    Boolean structure. Formulas containing [~] must not be given to a Z3
    solver, which aborts on them. For a Skolem leaf the equivalence holds
    once the Skolem symbol is interpreted as a witness. *)

(** {1 Vocabulary} *)

val symbols : Expr.expr -> FS.t
(** Uninterpreted function and constant symbols of an expression, including
    those inside quantifier bodies. Interpreted symbols ([+], [select],
    datatype constructors, ...) are never included.

    Results are memoised in a process-wide table keyed on the expression
    object; see {!clear_symbol_cache}. *)

val clear_symbol_cache : unit -> unit
(** Drop the memo table of {!symbols} (called at the start of every
    interpolation run so the table does not grow without bound). *)

val fresh_consts : Expr.expr -> FS.t -> Expr.expr list
(** [fresh_consts e shared] are the constants (arity-0 symbols) of [e] that
    are not in [shared], as expressions. *)

(** {1 Solver checks} *)

val default_timeout_ms : int
(** 10000 ms, as in the Python version. *)

val check : ?timeout:int -> context -> Expr.expr list -> Solver.status
(** Satisfiability of the conjunction, in a fresh solver with a timeout. *)

(** Outcome of {!verify}. *)
type verdict =
  | Ok
  | Vocabulary of FS.t  (** symbols of the candidate that are not shared *)
  | A_not_implies       (** [A /\ not I] is satisfiable *)
  | A_unknown           (** Z3 answered unknown on [A /\ not I] *)
  | B_sat               (** [B /\ I] is satisfiable *)
  | B_unknown           (** Z3 answered unknown on [B /\ I] *)

val verdict_to_string : verdict -> string

val verify : ?shared:FS.t -> context -> Expr.expr -> Expr.expr -> Expr.expr -> verdict
(** [verify ~shared ctx a b i] checks the three interpolant conditions:
    [a |= i], [b /\ i] unsatisfiable, and (if [shared] is given)
    [L(i) ⊆ shared]. An [unknown] answer is reported separately from a
    counterexample. *)

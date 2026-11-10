(** A small DSL for building Z3 formulas in one context, used by the tests
    and by [dump_proof]. Example:
{[
  let ctx = Z3itp.Interp.make_context () in
  let open Z3itp.Dsl.Make (struct let ctx = ctx end) in
  let x = ic "x" and f = fn "f" [ int ] int in
  let a = [ (f @@@ [ x ]) >== num 0 ] and b = [ (f @@@ [ x ]) <<< num 0 ] in
  Z3itp.Interp.interpolate ctx a b
]}
    Operators are suffixed with extra symbols so that they do not shadow
    OCaml's own. *)

open Z3

module Make (_ : sig
  val ctx : context
end) : sig
  val ctx : context
  val int : Sort.sort
  val real : Sort.sort
  val bool : Sort.sort

  (** integer constant *)
  val ic : string -> Expr.expr

  (** real constant *)
  val rc : string -> Expr.expr

  (** Boolean constant *)
  val bc : string -> Expr.expr

  (** integer numeral *)
  val num : int -> Expr.expr

  (** real numeral *)
  val rnum : int -> Expr.expr


  val fn : string -> Sort.sort list -> Sort.sort -> FuncDecl.func_decl
  (** uninterpreted function symbol *)

  (** application *)
  val ( @@@ ) : FuncDecl.func_decl -> Expr.expr list -> Expr.expr

  (** [=] *)
  val ( === ) : Expr.expr -> Expr.expr -> Expr.expr

  (** [not (=)] *)
  val ( =/= ) : Expr.expr -> Expr.expr -> Expr.expr

  val ( <== ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( >== ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( <<< ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( >>> ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( +++ ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( --- ) : Expr.expr -> Expr.expr -> Expr.expr
  val ( *** ) : Expr.expr -> Expr.expr -> Expr.expr
  val not_ : Expr.expr -> Expr.expr
  val and_ : Expr.expr list -> Expr.expr
  val or_ : Expr.expr list -> Expr.expr
  val implies : Expr.expr -> Expr.expr -> Expr.expr
  val distinct : Expr.expr list -> Expr.expr
  val ite : Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  val forall : Expr.expr list -> Expr.expr -> Expr.expr
  (** [forall [x; y] body], over constants [x], [y] *)

  val exists : Expr.expr list -> Expr.expr -> Expr.expr

  (** constant of sort [Array Int Int] *)
  val array : string -> Expr.expr

  val store : Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr
  val select : Expr.expr -> Expr.expr -> Expr.expr
end

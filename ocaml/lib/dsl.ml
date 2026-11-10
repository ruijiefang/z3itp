(* A small formula-building DSL.  See dsl.mli. *)

open Z3

module Make (C : sig
  val ctx : context
end) =
struct
  let ctx = C.ctx
  let int = Arithmetic.Integer.mk_sort ctx
  let real = Arithmetic.Real.mk_sort ctx
  let bool = Boolean.mk_sort ctx
  let ic n = Arithmetic.Integer.mk_const_s ctx n
  let rc n = Arithmetic.Real.mk_const_s ctx n
  let bc n = Boolean.mk_const_s ctx n
  let num n = Arithmetic.Integer.mk_numeral_i ctx n
  let rnum n = Arithmetic.Real.mk_numeral_i ctx n
  let fn name dom rng = FuncDecl.mk_func_decl_s ctx name dom rng
  let ( @@@ ) f xs = FuncDecl.apply f xs
  let ( === ) a b = Boolean.mk_eq ctx a b
  let ( =/= ) a b = Boolean.mk_not ctx (Boolean.mk_eq ctx a b)
  let ( <== ) a b = Arithmetic.mk_le ctx a b
  let ( >== ) a b = Arithmetic.mk_ge ctx a b
  let ( <<< ) a b = Arithmetic.mk_lt ctx a b
  let ( >>> ) a b = Arithmetic.mk_gt ctx a b
  let ( +++ ) a b = Arithmetic.mk_add ctx [ a; b ]
  let ( --- ) a b = Arithmetic.mk_sub ctx [ a; b ]
  let ( *** ) a b = Arithmetic.mk_mul ctx [ a; b ]
  let not_ a = Boolean.mk_not ctx a
  let and_ xs = Boolean.mk_and ctx xs
  let or_ xs = Boolean.mk_or ctx xs
  let implies a b = Boolean.mk_implies ctx a b
  let distinct xs = Boolean.mk_distinct ctx xs
  let forall vs body = Quantifier.expr_of_quantifier (Quantifier.mk_forall_const ctx vs body None [] [] None None)
  let exists vs body = Quantifier.expr_of_quantifier (Quantifier.mk_exists_const ctx vs body None [] [] None None)
  let array name = Z3Array.mk_const_s ctx name int int
  let store a i v = Z3Array.mk_store ctx a i v
  let select a i = Z3Array.mk_select ctx a i
  let ite c a b = Boolean.mk_ite ctx c a b
end

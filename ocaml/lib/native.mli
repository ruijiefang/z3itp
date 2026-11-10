(** Bindings to Z3 functions that the high-level OCaml API does not expose.

    The high-level module [Z3] declares its handle types abstractly in
    [z3.mli], but in [z3.ml] they are all aliases of the same native pointer
    type ([type context = Z3native.context], [type expr = AST.ast =
    Z3native.ast], [type model = Z3native.model]). We can therefore re-declare
    an existing C stub of [libz3ml] with high-level types, without casts. *)

open Z3

val qe_model_project : context -> Model.model -> int -> Expr.expr list -> Expr.expr -> Expr.expr
(** [qe_model_project ctx m n vars fml] is [Z3_qe_model_project]: a
    model-based projection of [fml] that eliminates the [n] constants [vars],
    guided by the model [m] (which must satisfy [fml]). This is the function
    Python exposes as [ModelRef.project].

    The result is true in [m] and contains none of [vars] when projection
    succeeds; for constants under uninterpreted functions the projection is
    best-effort (it may substitute model values or leave a variable in place),
    so callers must check the vocabulary of the result. *)

val project : context -> Model.model -> Expr.expr list -> Expr.expr -> Expr.expr
(** [project ctx m vars fml] is [qe_model_project ctx m (List.length vars) vars fml]. *)

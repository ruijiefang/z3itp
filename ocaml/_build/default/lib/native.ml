(* See native.mli.  "n_qe_model_project" is the C stub generated for
   Z3_qe_model_project in libz3ml (declared in z3native.mli with native
   types); we declare it again with the equivalent high-level types. *)

open Z3

external qe_model_project : context -> Model.model -> int -> Expr.expr list -> Expr.expr -> Expr.expr
  = "n_qe_model_project"

let project ctx m vars fml = qe_model_project ctx m (List.length vars) vars fml

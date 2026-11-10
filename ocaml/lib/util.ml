(* Expression utilities.  See util.mli for the documentation of each
   function; comments here explain implementation choices only. *)

open Z3

(* ------------------------------------------------------------------ *)
(* Tables keyed on Z3 objects (never on bare ids: see util.mli).       *)

module EH = Stdlib.Hashtbl.Make (struct
  type t = Expr.expr

  let equal = Expr.equal
  let hash e = AST.hash (Expr.ast_of_expr e)
end)

module ES = Stdlib.Set.Make (struct
  type t = Expr.expr

  let compare = Expr.compare
end)

module FS = Stdlib.Set.Make (struct
  type t = FuncDecl.func_decl

  let compare a b = compare (FuncDecl.get_id a) (FuncDecl.get_id b)
end)

module FH = Stdlib.Hashtbl.Make (struct
  type t = FuncDecl.func_decl

  let equal = FuncDecl.equal
  let hash = FuncDecl.get_id
end)

(* ------------------------------------------------------------------ *)
(* Tests and accessors                                                  *)

let is_app e = AST.get_ast_kind (Expr.ast_of_expr e) = Z3enums.APP_AST || AST.get_ast_kind (Expr.ast_of_expr e) = Z3enums.NUMERAL_AST
let is_quantifier e = AST.is_quantifier (Expr.ast_of_expr e)
let kind e = FuncDecl.get_decl_kind (Expr.get_func_decl e)
let args e = if is_app e then Expr.get_args e else []
let arg e i = List.nth (Expr.get_args e) i
let num_args e = if is_app e then Expr.get_num_args e else 0

(* The Boolean recognisers of the OCaml API inspect the head symbol, so they
   are guarded by [is_app] to be safe on quantifiers and bound variables. *)
let is_kind k e = is_app e && kind e = k
let is_not = is_kind Z3enums.OP_NOT
let is_or = is_kind Z3enums.OP_OR
let is_and = is_kind Z3enums.OP_AND
let is_true = is_kind Z3enums.OP_TRUE
let is_false = is_kind Z3enums.OP_FALSE
let decl_name d = Symbol.to_string (FuncDecl.get_name d)

let to_string e =
  let s = Expr.to_string e in
  let b = Buffer.create (String.length s) in
  let last_space = ref false in
  String.iter
    (fun c ->
      let c = if c = '\n' || c = '\t' then ' ' else c in
      if c = ' ' then (if not !last_space then Buffer.add_char b c; last_space := true)
      else (Buffer.add_char b c; last_space := false))
    s;
  Buffer.contents b

(* ------------------------------------------------------------------ *)
(* Literals and clauses                                                 *)

let neg ctx e = if is_not e then arg e 0 else Boolean.mk_not ctx e
let lits e = if is_false e then [] else if is_or e then args e else [ e ]

let is_complement x y =
  (is_not x && Expr.equal (arg x 0) y)
  || (is_not y && Expr.equal (arg y 0) x)
  || (is_true x && is_false y)
  || (is_false x && is_true y)

let rec flatten_and e = if is_and e then List.concat_map flatten_and (args e) else [ e ]

let mk_or ctx xs =
  let xs = List.filter (fun x -> not (is_false x)) xs in
  if List.exists is_true xs then Boolean.mk_true ctx
  else match xs with [] -> Boolean.mk_false ctx | [ x ] -> x | _ -> Boolean.mk_or ctx xs

let mk_and ctx xs =
  let xs = List.filter (fun x -> not (is_true x)) xs in
  if List.exists is_false xs then Boolean.mk_false ctx
  else match xs with [] -> Boolean.mk_true ctx | [ x ] -> x | _ -> Boolean.mk_and ctx xs

let oeq_to_iff ctx e =
  let memo = EH.create 64 in
  let rec go x =
    match EH.find_opt memo x with
    | Some r -> r
    | None ->
        let r =
          if is_app x && kind x = Z3enums.OP_OEQ then Boolean.mk_eq ctx (go (arg x 0)) (go (arg x 1))
          else if is_app x && num_args x > 0 && Boolean.is_bool x then
            FuncDecl.apply (Expr.get_func_decl x) (List.map go (args x))
          else x
        in
        EH.replace memo x r;
        r
  in
  go e

(* ------------------------------------------------------------------ *)
(* Vocabulary                                                           *)

let symbol_cache : FS.t EH.t = EH.create 1024
let clear_symbol_cache () = EH.reset symbol_cache

(* Iterative traversal: expressions (and proof conclusions) can be deep.
   Bound variables are neither applications nor quantifiers and contribute
   nothing. *)
let symbols e =
  match EH.find_opt symbol_cache e with
  | Some s -> s
  | None ->
      let seen = EH.create 64 in
      let out = ref FS.empty in
      let stack = Stack.create () in
      Stack.push e stack;
      while not (Stack.is_empty stack) do
        let x = Stack.pop stack in
        if not (EH.mem seen x) then begin
          EH.replace seen x ();
          if is_quantifier x then Stack.push (Quantifier.get_body (Quantifier.quantifier_of_expr x)) stack
          else if is_app x then begin
            let d = Expr.get_func_decl x in
            if FuncDecl.get_decl_kind d = Z3enums.OP_UNINTERPRETED then out := FS.add d !out;
            List.iter (fun c -> Stack.push c stack) (Expr.get_args x)
          end
        end
      done;
      EH.replace symbol_cache e !out;
      !out

let fresh_consts e shared =
  FS.fold
    (fun d acc -> if FuncDecl.get_arity d = 0 && not (FS.mem d shared) then FuncDecl.apply d [] :: acc else acc)
    (symbols e) []
  |> List.rev

(* ------------------------------------------------------------------ *)
(* Solver checks                                                        *)

let default_timeout_ms = 10_000

let check ?(timeout = default_timeout_ms) ctx fmls =
  let s = Solver.mk_solver ctx None in
  let p = Params.mk_params ctx in
  Params.add_int p (Symbol.mk_string ctx "timeout") timeout;
  Solver.set_parameters s p;
  Solver.add s fmls;
  Solver.check s []

type verdict =
  | Ok
  | Vocabulary of FS.t
  | A_not_implies
  | A_unknown
  | B_sat
  | B_unknown

let verdict_to_string = function
  | Ok -> "OK"
  | Vocabulary s -> "vocabulary: " ^ String.concat ", " (List.map decl_name (FS.elements s))
  | A_not_implies -> "A does not imply I"
  | A_unknown -> "A -> I: z3 says unknown"
  | B_sat -> "B /\\ I satisfiable"
  | B_unknown -> "B /\\ I: z3 says unknown"

let verify ?shared ctx a b i =
  let extra = match shared with Some sh -> FS.diff (symbols i) sh | None -> FS.empty in
  if not (FS.is_empty extra) then Vocabulary extra
  else
    match check ctx [ a; Boolean.mk_not ctx i ] with
    | Solver.SATISFIABLE -> A_not_implies
    | Solver.UNKNOWN -> A_unknown
    | Solver.UNSATISFIABLE -> (
        match check ctx [ b; i ] with
        | Solver.SATISFIABLE -> B_sat
        | Solver.UNKNOWN -> B_unknown
        | Solver.UNSATISFIABLE -> Ok)

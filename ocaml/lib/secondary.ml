(* The secondary interpolating prover.  See secondary.mli for what each
   stage computes and why it is sound; comments here cover implementation
   details and the correspondence with z3itp.py. *)

open Z3
open Util

type stage = { name : string; run : context -> Expr.expr -> Expr.expr -> FS.t -> Expr.expr option }

let bool_sort ctx = Boolean.mk_sort ctx

let with_timeout ctx s ms =
  let p = Params.mk_params ctx in
  Params.add_int p (Symbol.mk_string ctx "timeout") ms;
  Solver.set_parameters s p

let has_nonshared_function a shared =
  FS.exists (fun d -> FuncDecl.get_arity d > 0 && not (FS.mem d shared)) (symbols a)

(* ------------------------------------------------------------------ *)
(* Quantifier abstraction (abstract_quantifiers in z3itp.py)           *)

let abstract_quantifiers ctx a b shared =
  (* Outermost quantified sub-formulas, in first-occurrence order. *)
  let seen = EH.create 64 and qs = ref [] in
  let rec collect e =
    if not (EH.mem seen e) then begin
      EH.replace seen e ();
      if is_quantifier e then qs := e :: !qs else if is_app e then List.iter collect (args e)
    end
  in
  collect a;
  collect b;
  match List.rev !qs with
  | [] -> (a, b, [], shared)
  | qs ->
      let atoms = List.map (fun _ -> Expr.mk_fresh_const ctx "qatom" (bool_sort ctx)) qs in
      let shared' =
        List.fold_left2
          (fun acc q v -> if FS.subset (symbols q) shared then FS.add (Expr.get_func_decl v) acc else acc)
          shared qs atoms
      in
      let a2 = Expr.substitute a qs atoms and b2 = Expr.substitute b qs atoms in
      if check ctx [ a2; b2 ] <> Solver.UNSATISFIABLE then (a, b, [], shared)
      else (a2, b2, List.combine atoms qs, shared')

(* ------------------------------------------------------------------ *)
(* Ackermann's reduction of non-shared function symbols                *)

let ackermannize ctx a shared =
  let memo = EH.create 64 in
  let apps : (Expr.expr list * Expr.expr) list FH.t = FH.create 8 in
  let decl_order = ref [] in
  let rec go e =
    match EH.find_opt memo e with
    | Some r -> r
    | None ->
        let r =
          if is_quantifier e || (not (is_app e)) || num_args e = 0 then e
          else
            let xs = List.map go (args e) in
            let d = Expr.get_func_decl e in
            if FuncDecl.get_decl_kind d = Z3enums.OP_UNINTERPRETED && not (FS.mem d shared) then begin
              let insts = Option.value ~default:[] (FH.find_opt apps d) in
              match List.find_opt (fun (ys, _) -> List.for_all2 Expr.equal ys xs) insts with
              | Some (_, v) -> v
              | None ->
                  let v = Expr.mk_fresh_const ctx "ack" (FuncDecl.get_range d) in
                  if not (FH.mem apps d) then decl_order := d :: !decl_order;
                  FH.replace apps d (insts @ [ (xs, v) ]);
                  v
            end
            else FuncDecl.apply d xs
        in
        EH.replace memo e r;
        r
  in
  let body = go a in
  if FH.length apps = 0 then a
  else
    let rec pairs = function [] -> [] | x :: rest -> List.map (fun y -> (x, y)) rest @ pairs rest in
    let cons =
      List.concat_map
        (fun d ->
          List.map
            (fun ((ai, vi), (aj, vj)) ->
              Boolean.mk_implies ctx (mk_and ctx (List.map2 (Boolean.mk_eq ctx) ai aj)) (Boolean.mk_eq ctx vi vj))
            (pairs (FH.find apps d)))
        (List.rev !decl_order)
    in
    mk_and ctx (body :: cons)

(* ------------------------------------------------------------------ *)
(* Linear arithmetic: linearisation and the Farkas stage               *)

(* A linear polynomial: constant plus coefficients of opaque atoms.  The
   atom order is kept so that the produced interpolant is deterministic. *)
type poly = { mutable const : Q.t; coeffs : Q.t EH.t; mutable atoms : Expr.expr list (* reversed *) }

let new_poly () = { const = Q.zero; coeffs = EH.create 8; atoms = [] }

let add_atom p t c =
  match EH.find_opt p.coeffs t with
  | Some c0 -> EH.replace p.coeffs t (Q.add c0 c)
  | None ->
      EH.replace p.coeffs t c;
      p.atoms <- t :: p.atoms

let is_numeral e = Arithmetic.is_int_numeral e || Arithmetic.is_rat_numeral e

let numeral_value e =
  if Arithmetic.is_int_numeral e then Q.of_bigint (Arithmetic.Integer.get_big_int e)
  else Arithmetic.Real.get_ratio e

(* [linearize e coef p] adds [coef * e] to [p]; [false] if [e] is not linear.
   Deviation from z3itp.py (documented in PLAN.md §7): the first operand of
   a subtraction is checked for linearity too. *)
let rec linearize e coef p =
  if is_numeral e then (p.const <- Q.add p.const (Q.mul coef (numeral_value e)); true)
  else if Arithmetic.is_add e then List.for_all (fun c -> linearize c coef p) (args e)
  else if Arithmetic.is_sub e then
    match args e with
    | first :: rest -> linearize first coef p && List.for_all (fun c -> linearize c (Q.neg coef) p) rest
    | [] -> true
  else if Arithmetic.is_uminus e then linearize (arg e 0) (Q.neg coef) p
  else if Arithmetic.is_mul e then
    let nums, rest = List.partition is_numeral (args e) in
    let k = List.fold_left (fun k c -> Q.mul k (numeral_value c)) coef nums in
    match rest with
    | [] -> (p.const <- Q.add p.const k; true)
    | [ t ] -> linearize t k p
    | _ -> false
  else if Arithmetic.is_int2real e then linearize (arg e 0) coef p
  else (add_atom p e coef; true)

type op = Le | Lt | Eq

let is_arith_sort e =
  match Sort.get_sort_kind (Expr.get_sort e) with Z3enums.INT_SORT | REAL_SORT -> true | _ -> false

(* Normalise a literal to [poly op 0]. *)
let ineq e =
  let negated = is_not e in
  let x = if negated then arg e 0 else e in
  if (not (is_app x)) || num_args x <> 2 || not (is_arith_sort (arg x 0)) then None
  else
    let l = arg x 0 and r = arg x 1 in
    let shape =
      match kind x with
      | Z3enums.OP_LE -> Some (l, r, Le)
      | OP_GE -> Some (r, l, Le)
      | OP_LT -> Some (l, r, Lt)
      | OP_GT -> Some (r, l, Lt)
      | OP_EQ -> Some (l, r, Eq)
      | _ -> None
    in
    let shape =
      match shape with
      | Some (_, _, Eq) when negated -> None
      | Some (lhs, rhs, op) when negated -> Some (rhs, lhs, if op = Le then Lt else Le)
      | s -> s
    in
    match shape with
    | None -> None
    | Some (lhs, rhs, op) ->
        let p = new_poly () in
        if linearize lhs Q.one p && linearize rhs Q.minus_one p then Some (p, op) else None

let real_num ctx q = Arithmetic.Real.mk_numeral_s ctx (Q.to_string q)
let sum ctx = function [] -> Arithmetic.Real.mk_numeral_i ctx 0 | xs -> Arithmetic.mk_add ctx xs

let farkas_run ctx a b _shared =
  let rows =
    List.concat_map (fun (side, f) -> List.map (fun c -> (side, ineq c)) (flatten_and f)) [ (`A, a); (`B, b) ]
  in
  if List.exists (fun (_, r) -> r = None) rows then None
  else
    let rows = List.map (function s, Some (p, op) -> (s, p, op) | _, None -> assert false) rows in
    let real = Arithmetic.Real.mk_sort ctx in
    let lam = List.map (fun _ -> Expr.mk_fresh_const ctx "lam" real) rows in
    let s = Solver.mk_solver ctx None in
    with_timeout ctx s default_timeout_ms;
    List.iter2 (fun l (_, _, op) -> if op <> Eq then Solver.add s [ Arithmetic.mk_ge ctx l (real_num ctx Q.zero) ]) lam rows;
    (* every atom must cancel *)
    let all_atoms = EH.create 16 and atom_order = ref [] in
    List.iter
      (fun (_, p, _) ->
        List.iter
          (fun t -> if not (EH.mem all_atoms t) then (EH.replace all_atoms t (); atom_order := t :: !atom_order))
          (List.rev p.atoms))
      rows;
    List.iter
      (fun t ->
        let terms =
          List.concat
            (List.map2
               (fun l (_, p, _) ->
                 match EH.find_opt p.coeffs t with
                 | Some c -> [ Arithmetic.mk_mul ctx [ l; real_num ctx c ] ]
                 | None -> [])
               lam rows)
        in
        Solver.add s [ Boolean.mk_eq ctx (sum ctx terms) (real_num ctx Q.zero) ])
      (List.rev !atom_order);
    let const = sum ctx (List.map2 (fun l (_, p, _) -> Arithmetic.mk_mul ctx [ l; real_num ctx p.const ]) lam rows) in
    let strict = sum ctx (List.concat (List.map2 (fun l (_, _, op) -> if op = Lt then [ l ] else []) lam rows)) in
    let zero = real_num ctx Q.zero in
    Solver.add s
      [ Boolean.mk_or ctx
          [ Arithmetic.mk_gt ctx const zero; Boolean.mk_and ctx [ Arithmetic.mk_ge ctx const zero; Arithmetic.mk_gt ctx strict zero ] ] ];
    if Solver.check s [] <> Solver.SATISFIABLE then None
    else
      let m = Option.get (Solver.get_model s) in
      let value l = match Model.eval m l true with Some v -> Arithmetic.Real.get_ratio v | None -> Q.zero in
      (* sum of the A rows *)
      let total = new_poly () and strict_a = ref false in
      List.iter2
        (fun l (side, p, op) ->
          let v = value l in
          if side = `A && not (Q.equal v Q.zero) then begin
            if op = Lt then strict_a := true;
            List.iter (fun t -> add_atom total t (Q.mul v (EH.find p.coeffs t))) (List.rev p.atoms);
            total.const <- Q.add total.const (Q.mul v p.const)
          end)
        lam rows;
      let items =
        List.filter_map
          (fun t ->
            let c = EH.find total.coeffs t in
            if Q.equal c Q.zero then None else Some (t, c))
          (List.rev total.atoms)
      in
      let k0 = total.const in
      let scale = List.fold_left (fun acc (_, c) -> Z.lcm acc (Q.den c)) (Q.den k0) items |> Q.of_bigint in
      let all_int = List.for_all (fun (t, _) -> Arithmetic.is_int t) items in
      (* stay in Int when every atom is an integer term *)
      let num c =
        let c = Q.mul c scale in
        if all_int then Arithmetic.Integer.mk_numeral_s ctx (Z.to_string (Q.num c)) else real_num ctx c
      in
      let cast t = if (not all_int) && Arithmetic.is_int t then Arithmetic.Integer.mk_int2real ctx t else t in
      let lhs =
        match items with
        | [] -> num k0
        | _ -> Arithmetic.mk_add ctx (List.map (fun (t, c) -> Arithmetic.mk_mul ctx [ num c; cast t ]) items @ [ num k0 ])
      in
      let zero = num Q.zero in
      let atom = if !strict_a then Arithmetic.mk_lt ctx lhs zero else Arithmetic.mk_le ctx lhs zero in
      Some (Expr.simplify atom None)

let farkas = { name = "farkas"; run = farkas_run }

(* ------------------------------------------------------------------ *)
(* Model-based interpolation loop (mbp_interpolant in z3itp.py)        *)

let mbp_max_iter = 200

let mbp_run ctx a b shared =
  if has_nonshared_function a shared then None (* projection cannot remove functions *)
  else
    let loc = fresh_consts a shared in
    let sa = Solver.mk_solver ctx None and sb = Solver.mk_solver ctx None in
    with_timeout ctx sa default_timeout_ms;
    with_timeout ctx sb default_timeout_ms;
    Solver.add sa [ a ];
    Solver.add sb [ b ];
    let rec loop i itps =
      if i >= mbp_max_iter then None
      else
        match Solver.check sa [] with
        | Solver.UNSATISFIABLE -> Some (mk_or ctx (List.rev itps))
        | Solver.UNKNOWN -> None
        | Solver.SATISFIABLE -> (
            let m = Option.get (Solver.get_model sa) in
            let proj = if loc = [] then a else Native.project ctx m loc a in
            if not (FS.subset (symbols proj) shared) then None
            else
              (* generalise: keep the literals of the cube that B needs *)
              let cube = flatten_and proj in
              let tags = List.map (fun _ -> Expr.mk_fresh_const ctx "t" (bool_sort ctx)) cube in
              Solver.push sb;
              List.iter2 (fun t c -> Solver.add sb [ Boolean.mk_implies ctx t c ]) tags cube;
              let r = Solver.check sb tags in
              let core = if r = Solver.UNSATISFIABLE then Some (ES.of_list (Solver.get_unsat_core sb)) else None in
              Solver.pop sb 1;
              match core with
              | None -> None
              | Some core ->
                  let gen = mk_and ctx (List.concat (List.map2 (fun t c -> if ES.mem t core then [ c ] else []) tags cube)) in
                  Solver.add sa [ Boolean.mk_not ctx gen ];
                  loop (i + 1) (gen :: itps))
    in
    loop 0 []

let mbp = { name = "mbp"; run = mbp_run }

(* ------------------------------------------------------------------ *)
(* Quantifier elimination                                              *)

let exists_const ctx vars body =
  Quantifier.expr_of_quantifier (Quantifier.mk_exists_const ctx vars body None [] [] None None)

let goal_disjunction ctx (r : Tactic.ApplyResult.apply_result) =
  mk_or ctx (List.map (fun g -> mk_and ctx (Goal.get_formulas g)) (Tactic.ApplyResult.get_subgoals r))

let qe_run ctx a _b shared =
  if has_nonshared_function a shared then None
  else
    match fresh_consts a shared with
    | [] -> Some a
    | loc ->
        let g = Goal.mk_goal ctx true false false in
        Goal.add g [ exists_const ctx loc a ];
        let r = goal_disjunction ctx (Tactic.apply (Tactic.mk_tactic ctx "qe") g None) in
        if FS.subset (symbols r) shared then Some r else None

let qe = { name = "qe"; run = qe_run }

(* z3itp.py tries one more stage after qe: the z3 executable's
   (get-interpolant A B).  It is deliberately not ported; see secondary.mli. *)
let default_stages = [ farkas; mbp; qe ]

(* ------------------------------------------------------------------ *)
(* Driver                                                              *)

exception Failed of Expr.expr * Expr.expr

let interpolate ?(stages = default_stages) ~count ctx shared a b =
  if check ~timeout:2000 ctx [ a ] = Solver.UNSATISFIABLE then (count "2nd:A-unsat"; Boolean.mk_false ctx)
  else if check ~timeout:2000 ctx [ b ] = Solver.UNSATISFIABLE then (count "2nd:B-unsat"; Boolean.mk_true ctx)
  else
    let a2, b2, undo, shared' = abstract_quantifiers ctx a b shared in
    let a2 = ackermannize ctx a2 shared' in
    let atoms = List.map fst undo and formulas = List.map snd undo in
    let attempt st =
      match st.run ctx a2 b2 shared' with
      | exception (Z3.Error _ | Failure _ | Not_found | Invalid_argument _) -> None
      | None -> None
      | Some i ->
          let i = if undo = [] then i else Expr.substitute i atoms formulas in
          if verify ~shared:shared' ctx a b i = Ok then Some i else None
    in
    let rec go = function
      | [] ->
          count "2nd:FAILED";
          raise (Failed (a, b))
      | st :: rest -> (
          match attempt st with
          | Some i ->
              count ("2nd:" ^ st.name);
              i
          | None -> go rest)
    in
    go stages

(* ------------------------------------------------------------------ *)
(* Final simplification                                                *)

let simplify_itp ctx i =
  try
    let t = Tactic.and_then ctx (Tactic.mk_tactic ctx "simplify") (Tactic.mk_tactic ctx "qe-light") [] in
    let g = Goal.mk_goal ctx true false false in
    Goal.add g [ i ];
    let r = goal_disjunction ctx (Tactic.apply t g None) in
    if check ctx [ Boolean.mk_not ctx (Boolean.mk_eq ctx i r) ] = Solver.UNSATISFIABLE then r else Expr.simplify i None
  with Z3.Error _ -> Expr.simplify i None

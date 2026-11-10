(* Interpolants from Z3 proofs: the main algorithm.  See interp.mli for the
   overview.  Each function below names the method of z3itp.py it ports and
   the section of McMillan's paper it implements. *)

open Z3
open Util
open Proof_dag

type t = {
  ctx : context;
  a : Expr.expr list;
  b : Expr.expr list;
  mutable la : FS.t;  (* L(A), grows with coloured fresh symbols and localisation constants *)
  mutable lb : FS.t;  (* L(B), likewise *)
  xs : Expr.expr Dynarray.t;  (* localisation constants, in introduction order *)
  defs : (Expr.expr * Expr.expr * side) FH.t;  (* decl of s -> (s, t, side of t) *)
  def_cache : Expr.expr EH.t;  (* term t -> its localisation constant s *)
  counts : (string, int) Hashtbl.t;
  mutable sizes : int list;  (* lemma sizes, reversed *)
  memo : (int, Expr.expr) Hashtbl.t;  (* node uid -> partial interpolant *)
  mutable all_nodes : node list;
  debug : bool;
  stages : Secondary.stage list;
}

exception Not_unsat of string
exception Root_not_strict
exception Check_failed of string

let make_context () = mk_context [ ("proof", "true"); ("model", "true") ]
let union_symbols es = List.fold_left (fun acc e -> FS.union acc (symbols e)) FS.empty es

let create ?(debug = false) ?(stages = Secondary.default_stages) ctx a b =
  clear_symbol_cache ();
  {
    ctx;
    a;
    b;
    la = union_symbols a;
    lb = union_symbols b;
    xs = Dynarray.create ();
    defs = FH.create 8;
    def_cache = EH.create 8;
    counts = Hashtbl.create 32;
    sizes = [];
    memo = Hashtbl.create 256;
    all_nodes = [];
    debug;
    stages;
  }

let count t ?(by = 1) k = Hashtbl.replace t.counts k (by + Option.value ~default:0 (Hashtbl.find_opt t.counts k))
let stat t k = Option.value ~default:0 (Hashtbl.find_opt t.counts k)
let stats t = Hashtbl.fold (fun k v acc -> (k, v) :: acc) t.counts [] |> List.sort compare
let lemma_sizes t = List.rev t.sizes
let nodes t = t.all_nodes
let partial_interpolant t n = Hashtbl.find_opt t.memo n.uid
let localisation_constants t = Dynarray.to_list t.xs |> List.map (fun s -> FH.find t.defs (Expr.get_func_decl s))

(* ------------------------------------------------------------------ *)
(* Colouring (Interpolator.col / local_to / shared)                    *)

let col t e =
  let s = symbols e in
  if FS.subset s t.lb then Some B else if FS.subset s t.la then Some A else None

let local_to t e side = FS.subset (symbols e) (match side with A -> t.la | B -> t.lb)
let shared t = FS.inter t.la t.lb
let strict_formula t e = col t e <> None

(* ------------------------------------------------------------------ *)
(* Solving and importing (Interpolator.solve / import_proof)           *)

let solve t =
  let s = Solver.mk_solver t.ctx None in
  Solver.add s t.a;
  Solver.add s t.b;
  match Solver.check s [] with
  | Solver.UNSATISFIABLE -> (
      match Solver.get_proof s with
      | Some p -> p
      | None -> raise (Not_unsat "unsat, but no proof (was the context created with proof=true?)"))
  | st -> raise (Not_unsat (Solver.string_of_status st))

(* ------------------------------------------------------------------ *)
(* Step 2: fresh symbols introduced by Z3 (colour_fresh_symbols)       *)

(* Skolem constants and Tseitin names are definitional extensions: each is
   made local to the side of the formula it names, and its defining leaf is
   treated as an assertion of that side.  Sound because the symbol is fresh
   for the other side. *)
let colour_fresh_symbols t =
  List.iter
    (fun n ->
      match n.rule with
      | (Sk | Intro_def) when n.prem = [] ->
          let c = n.concl in
          let src = if n.rule = Sk && num_args c = 2 then arg c 0 else c in
          let fresh = FS.diff (FS.diff (symbols c) t.la) t.lb in
          if not (FS.is_empty fresh) then begin
            let old = FS.diff (symbols src) fresh in
            let side = if FS.subset old t.la then Some A else if FS.subset old t.lb then Some B else None in
            match side with
            | None -> count t "uncoloured_fresh_defs"
            | Some A ->
                t.la <- FS.union t.la fresh;
                n.side <- Some A
            | Some B ->
                t.lb <- FS.union t.lb fresh;
                n.side <- Some B
          end
      | _ -> ())
    t.all_nodes;
  let stray =
    List.fold_left (fun acc n -> FS.union acc (FS.diff (FS.diff (symbols n.concl) t.la) t.lb)) FS.empty t.all_nodes
  in
  count t ~by:(FS.cardinal stray) "stray_symbols"

(* ------------------------------------------------------------------ *)
(* Step 3: axiom elimination (new_def / localise_term / eliminate_axioms) *)

(* A fresh localisation constant s for the coloured term tm, with the
   definition s = tm on the side of tm.  s is added to both vocabularies,
   i.e. treated as shared.  Identical terms share one constant. *)
let new_def t tm =
  match EH.find_opt t.def_cache tm with
  | Some s -> s
  | None ->
      let s = Expr.mk_fresh_const t.ctx "loc" (Expr.get_sort tm) in
      let side = match col t tm with Some sd -> sd | None -> invalid_arg "new_def: uncoloured term" in
      let d = Expr.get_func_decl s in
      t.la <- FS.add d t.la;
      t.lb <- FS.add d t.lb;
      Dynarray.add_last t.xs s;
      FH.replace t.defs d (s, tm, side);
      EH.replace t.def_cache tm s;
      s

(* Replace the maximal coloured subterms of tm by localisation constants. *)
let rec replace_maximal_local t tm =
  if col t tm <> None then
    if is_app tm && num_args tm = 0 && FH.mem t.defs (Expr.get_func_decl tm) then tm else new_def t tm
  else if (not (is_app tm)) || num_args tm = 0 then tm
  else FuncDecl.apply (Expr.get_func_decl tm) (List.map (replace_maximal_local t) (args tm))

(* Paper IV.C: replace highest local positions by fresh symbols until the
   term is local to [side].  None if a stray symbol blocks progress. *)
let localise_term t tm side =
  let rec loop tm k =
    if k = 0 then None
    else if local_to t tm side then Some tm
    else if col t tm <> None then Some (new_def t tm)
    else
      let tm' = replace_maximal_local t tm in
      if Expr.equal tm' tm then None else loop tm' (k - 1)
  in
  loop tm 64

let def_node t s =
  let s, tm, side = FH.find t.defs (Expr.get_func_decl s) in
  mk_node ~side Definition [] (Boolean.mk_eq t.ctx s tm)

(* The instance part of a quant-inst conclusion, in one of the two shapes
   Z3 produces (PLAN.md §4.3 item 15):
     nested     (or (not q) inst)                  -- z3-solver 5.1
     flattened  (or (not q) l1 ... ln), inst = (or l1 ... ln)  -- Z3 4.16
   Returns the shape if the conclusion is literally the instance [inst]. *)
type shape = Nested | Flattened

let instance_shape rest inst =
  match rest with
  | [ x ] when Expr.equal x inst -> Some Nested
  | _ when is_or inst && List.length rest = num_args inst && List.for_all2 Expr.equal rest (args inst) -> Some Flattened
  | _ -> None

let localise_quant_inst t n =
  let c = n.concl in
  if not (is_or c && num_args c >= 2 && is_not (arg c 0) && is_quantifier (arg (arg c 0) 0)) then ()
  else
    let nq = arg c 0 in
    let q = arg nq 0 and rest = List.tl (args c) in
    let quant = Quantifier.quantifier_of_expr q in
    let body = Quantifier.get_body quant in
    let terms =
      List.filter_map (function FuncDecl.Parameter.P_Ast a -> Some (Expr.expr_of_ast a) | _ -> None) n.params
    in
    (* every parameter must be a term (stricter than z3itp.py, which took all
       parameters as terms; Z3's quant-inst parameters are the instance terms) *)
    if List.length terms <> List.length n.params || List.length terms <> Quantifier.get_num_bound quant then ()
    else
      (* Z3 numbers bound variables from the innermost: reverse the terms. *)
      match instance_shape rest (Expr.substitute_vars body (List.rev terms)) with
      | None -> count t "qinst_not_syntactic"
      | Some shape -> (
          match col t q with
          | None -> ()
          | Some side -> (
              let side = if side = B && local_to t q A then A else side (* shared quantifier: prefer A *) in
              let ndefs = Dynarray.length t.xs in
              let loc = List.map (fun tm -> localise_term t tm side) terms in
              if List.mem None loc then count t "qinst_unlocalisable"
              else
                let loc = List.map Option.get loc in
                let inst_loc = Expr.substitute_vars body (List.rev loc) in
                let leaf_concl =
                  match shape with
                  | Flattened when is_or inst_loc -> Boolean.mk_or t.ctx (nq :: args inst_loc)
                  | _ -> Boolean.mk_or t.ctx [ nq; inst_loc ]
                in
                let leaf = mk_node Quant_inst_local [] leaf_concl in
                let xs = Dynarray.to_list t.xs in
                (* definitions introduced now *)
                let fresh = List.filteri (fun i _ -> i >= ndefs) xs in
                (* definitions reused from the cache *)
                let reused =
                  List.filteri (fun i _ -> i < ndefs) xs
                  |> List.filter (fun s ->
                      List.exists (fun x -> is_app x && FS.mem (Expr.get_func_decl s) (symbols x)) loc)
                in
                let defs = ref (List.map (def_node t) (fresh @ reused)) in
                (* nested definitions: loc2 = f(loc1) needs loc1's definition *)
                let seen = ref (FS.of_list (List.map (fun d -> Expr.get_func_decl (arg d.concl 0)) !defs)) in
                let frontier = Stack.create () in
                List.iter (fun d -> Stack.push d frontier) !defs;
                while not (Stack.is_empty frontier) do
                  let d = Stack.pop frontier in
                  FS.iter
                    (fun sd ->
                      if FH.mem t.defs sd && not (FS.mem sd !seen) then begin
                        seen := FS.add sd !seen;
                        let s, _, _ = FH.find t.defs sd in
                        let nd = def_node t s in
                        defs := !defs @ [ nd ];
                        Stack.push nd frontier
                      end)
                    (symbols (arg d.concl 1))
                done;
                n.rule <- Elim_subst;
                n.prem <- leaf :: !defs;
                count t "qinst_localised"))

let eliminate_axioms t =
  List.iter
    (fun n -> if n.rule = Quant_inst && not (strict_formula t n.concl) then localise_quant_inst t n)
    t.all_nodes

(* ------------------------------------------------------------------ *)
(* Sequents (hyps / sides / clause_lits / delta / strict)              *)

let rec hyps n =
  match n.hyps with
  | Some h -> h
  | None ->
      let h =
        match n.rule with
        | Hypothesis -> ES.singleton n.concl
        | Lemma -> ES.empty
        | _ -> List.fold_left (fun acc p -> ES.union acc (hyps p)) ES.empty n.prem
      in
      n.hyps <- Some h;
      h

let rec sides n =
  match n.sides with
  | Some s -> s
  | None ->
      let s =
        List.fold_left
          (fun acc p ->
            let ps = sides p in
            { has_a = acc.has_a || ps.has_a; has_b = acc.has_b || ps.has_b })
          { has_a = n.side = Some A; has_b = n.side = Some B }
          n.prem
      in
      n.sides <- Some s;
      s

(* How a consumer that uses [n] as a clause (first premise of
   unit-resolution) reads it: the top-level disjuncts. *)
let as_clause_lits n = lits n.concl

(* The literals of n's conclusion as the rule that produced it means them.
   An or-shaped conclusion is a single literal when unit-resolution left one
   literal, when a lemma discharged a single hypothesis h and concludes
   not h, or for a hypothesis (Z3's proof_checker.cpp conventions). *)
let clause_lits t n =
  let c = n.concl in
  match n.rule with
  | Hypothesis -> [ c ]
  | Unit_resolution when n.prem <> [] -> (
      let clause = List.hd n.prem and units = List.tl n.prem in
      let rest = as_clause_lits clause in
      match (units, rest) with
      | [ u ], [ l ] when is_complement l u.concl -> []
      | _ ->
          let remove_one rest u =
            let rec go = function [] -> [] | l :: ls -> if is_complement l u.concl then ls else l :: go ls in
            go rest
          in
          List.fold_left remove_one rest units)
  | Lemma when n.prem <> [] -> (
      match ES.elements (hyps (List.hd n.prem)) with
      | [ h ] when Expr.equal (neg t.ctx h) c -> [ c ]
      | _ -> lits c)
  | _ -> lits c

let delta t n =
  match n.delta with
  | Some d -> d
  | None ->
      let seen = ref ES.empty and out = ref [] in
      let add l = if not (ES.mem l !seen) then (seen := ES.add l !seen; out := l :: !out) in
      ES.iter (fun h -> add (neg t.ctx h)) (hyps n);
      List.iter add (clause_lits t n);
      let d = List.rev !out in
      n.delta <- Some d;
      d

let delta_set t n = ES.of_list (delta t n)
let strict t n = List.for_all (fun l -> col t l <> None) (delta t n)

(* ------------------------------------------------------------------ *)
(* Debug check of the S_I invariant (side_axioms / check_node)         *)

let side_axioms t =
  let ax_a = ref [] and ax_b = ref [] in
  let add side e = match side with A -> ax_a := e :: !ax_a | B -> ax_b := e :: !ax_b in
  Dynarray.iter
    (fun s ->
      let s, tm, side = FH.find t.defs (Expr.get_func_decl s) in
      add side (Boolean.mk_eq t.ctx s tm))
    t.xs;
  List.iter
    (fun n ->
      match (n.rule, n.side) with (Sk | Intro_def), Some side -> add side (oeq_to_iff t.ctx n.concl) | _ -> ())
    t.all_nodes;
  (List.rev !ax_a, List.rev !ax_b)

let check_node t n phi =
  let d = delta t n in
  let part side = List.filter_map (fun l -> if col t l = Some side then Some (oeq_to_iff t.ctx (neg t.ctx l)) else None) d in
  let ax_a, ax_b = side_axioms t in
  let where = Printf.sprintf "node #%d (rule %s) |- %s; phi = %s" n.uid (rule_name n.rule) (to_string n.concl) (to_string phi) in
  if check t.ctx (t.a @ ax_a @ part A @ [ Boolean.mk_not t.ctx phi ]) = Solver.SATISFIABLE then
    raise (Check_failed ("A-condition fails at " ^ where));
  if check t.ctx (t.b @ ax_b @ part B @ [ phi ]) = Solver.SATISFIABLE then
    raise (Check_failed ("B-condition fails at " ^ where))

(* ------------------------------------------------------------------ *)
(* Steps 4/5: translation into S_I, with lemma extraction              *)

let rec interp t n =
  match Hashtbl.find_opt t.memo n.uid with
  | Some phi -> phi
  | None ->
      let phi = interp_node t n in
      Hashtbl.replace t.memo n.uid phi;
      if t.debug then check_node t n phi;
      phi

and interp_node t n =
  let d = delta t n in
  let sd = sides n in
  (* LOCAL: the whole sub-proof uses one side and its sequent is local to
     that side; nothing inside needs to be looked at. *)
  if (not sd.has_a) && List.for_all (fun l -> local_to t l B) d then (count t "S_I:LocalB"; Boolean.mk_true t.ctx)
  else if (not sd.has_b) && List.for_all (fun l -> local_to t l A) d then begin
    count t "S_I:LocalA";
    mk_or t.ctx (List.filter (fun l -> col t l = Some B) d)
  end
  else
    let contra =
      match (n.rule, n.prem) with
      | Lemma, p :: _ when strict t p && ES.equal (delta_set t p) (delta_set t n) -> Some p
      | _ -> None
    in
    match contra with
    | Some p ->
        (* CONTRA: hypotheses are already on the right of the one-sided
           sequent, so the premise's interpolant carries over. *)
        count t "S_I:Contra";
        interp t p
    | None -> if n.rule = Unit_resolution && native_unit_resolution t n then unit_resolution t n else lemma t n

(* -- views: the same node read as a clause or as one formula -- *)

and split_view_strict t p =
  List.for_all (fun l -> col t l <> None) (as_clause_lits p)
  && ES.for_all (fun h -> col t (neg t.ctx h) <> None) (hyps p)

(* Shared disjuncts of an A-coloured formula that move between Delta_A and
   Delta_B when the reading changes; literals that coincide with negated
   hypotheses stay where they are. *)
and moved t p ls =
  let hyp_lits = ES.map (neg t.ctx) (hyps p) in
  List.filter (fun l -> col t l = Some B && not (ES.mem l hyp_lits)) ls

(* p read as a clause.  From a single A-coloured or-literal F: the shared
   disjuncts S move from Delta_A to Delta_B, so phi' = phi \/ S. *)
and as_clause t p =
  let phi = interp t p in
  match clause_lits t p with
  | [ f ] when is_or f && col t f <> Some B -> mk_or t.ctx (phi :: moved t p (lits f))
  | _ -> phi

(* p read as one formula F.  From split literals with col F = A: the shared
   disjuncts S move from Delta_B to Delta_A, so phi' = phi /\ not S.  The
   condition is ((one literal equal to the conclusion) or (F is B)),
   with the precedence of the Python expression made explicit. *)
and as_unit t p =
  let phi = interp t p in
  let nat = clause_lits t p in
  let already_unit = match nat with [ f ] -> Expr.equal f p.concl | _ -> false in
  if already_unit || col t p.concl = Some B then phi
  else mk_and t.ctx (phi :: List.map (neg t.ctx) (moved t p nat))

and native_unit_resolution t n =
  match n.prem with
  | [] -> false
  | c :: units ->
      split_view_strict t c
      && List.for_all
           (fun u -> strict_formula t u.concl && ES.for_all (fun h -> col t (neg t.ctx h) <> None) (hyps u))
           units

(* RES chain: fold the units into the clause's interpolant, OR for an
   A-coloured pivot (RESA), AND for a B-coloured one (RESB). *)
and unit_resolution t n =
  let clause = List.hd n.prem in
  let cl = as_clause_lits clause in
  List.fold_left
    (fun phi u ->
      let piv = match List.find_opt (fun l -> is_complement l u.concl) cl with Some l -> l | None -> clause.concl in
      let psi = as_unit t u in
      if col t piv = Some B then (count t "S_I:ResB"; Boolean.mk_and t.ctx [ phi; psi ])
      else (count t "S_I:ResA"; Boolean.mk_or t.ctx [ phi; psi ]))
    (as_clause t clause) (List.tl n.prem)

(* Lemma extraction rooted at the strict node n (paper IV.B).  The frontier
   is the set of nearest descendants that are not hypotheses, whose
   hypotheses are among n's, that are strict, and whose conclusion is
   coloured as a whole.  The lemma  |- not F_1, ..., not F_m, Delta(n)  is
   valid and strict; it is interpolated by the secondary prover and the
   frontier is resolved back in. *)
and lemma t n =
  let hn = hyps n in
  let frontier = ref [] and fids = ref ES.empty and seen = Hashtbl.create 64 and inner = ref 0 in
  let stack = Stack.create () in
  List.iter (fun p -> Stack.push p stack) n.prem;
  while not (Stack.is_empty stack) do
    let p = Stack.pop stack in
    if not (Hashtbl.mem seen p.uid) then begin
      Hashtbl.replace seen p.uid ();
      if p.rule <> Hypothesis && ES.subset (hyps p) hn && strict t p && strict_formula t p.concl then begin
        if not (ES.mem p.concl !fids) then begin
          fids := ES.add p.concl !fids;
          frontier := p :: !frontier
        end
      end
      else begin
        incr inner;
        List.iter (fun q -> Stack.push q stack) p.prem
      end
    end
  done;
  let frontier = List.rev !frontier in
  let d = delta t n in
  let part side =
    List.filter_map (fun p -> if col t p.concl = Some side then Some p.concl else None) frontier
    @ List.filter_map (fun l -> if col t l = Some side then Some (neg t.ctx l) else None) d
  in
  count t "S_I:Lemma";
  t.sizes <- (!inner + 1) :: t.sizes;
  let a' = oeq_to_iff t.ctx (mk_and t.ctx (part A)) and b' = oeq_to_iff t.ctx (mk_and t.ctx (part B)) in
  let phi = Secondary.interpolate ~stages:t.stages ~count:(fun k -> count t k) t.ctx (shared t) a' b' in
  List.fold_left
    (fun phi p ->
      let psi = as_unit t p in
      if col t p.concl = Some B then Boolean.mk_and t.ctx [ phi; psi ] else Boolean.mk_or t.ctx [ phi; psi ])
    phi frontier

(* ------------------------------------------------------------------ *)
(* Step 6: ELIM and the driver (Interpolator.run)                      *)

let run t =
  let imported = Proof_dag.import ~a:t.a ~b:t.b (solve t) in
  t.all_nodes <- imported.nodes;
  count t ~by:(List.length imported.nodes) "proof_nodes";
  List.iter (fun (r, k) -> count t ~by:k ("rule:" ^ r)) imported.rule_counts;
  colour_fresh_symbols t;
  eliminate_axioms t;
  if not (strict t imported.root) then raise Root_not_strict;
  let itp = ref (interp t imported.root) in
  (* ELIM: quantify localisation constants out, innermost = latest *)
  for i = Dynarray.length t.xs - 1 downto 0 do
    let s = Dynarray.get t.xs i in
    let _, _, side = FH.find t.defs (Expr.get_func_decl s) in
    if FS.mem (Expr.get_func_decl s) (symbols !itp) then
      let q =
        match side with
        | B -> Quantifier.mk_forall_const t.ctx [ s ] !itp None [] [] None None
        | A -> Quantifier.mk_exists_const t.ctx [ s ] !itp None [] [] None None
      in
      itp := Quantifier.expr_of_quantifier q
  done;
  count t ~by:(Dynarray.length t.xs) "localisation_constants";
  Secondary.simplify_itp t.ctx !itp

let interpolate ?debug ?stages ctx a b =
  let t = create ?debug ?stages ctx a b in
  let i = run t in
  (i, t)

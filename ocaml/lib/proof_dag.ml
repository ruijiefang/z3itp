(* Proof nodes and proof import.  See proof.mli. *)

open Z3
open Util

type rule =
  | Asserted
  | Hypothesis
  | Lemma
  | Unit_resolution
  | Quant_inst
  | Sk
  | Intro_def
  | Th_lemma
  | Other of string
  | Quant_inst_local
  | Definition
  | Elim_subst

let rule_name = function
  | Asserted -> "asserted"
  | Hypothesis -> "hypothesis"
  | Lemma -> "lemma"
  | Unit_resolution -> "unit-resolution"
  | Quant_inst -> "quant-inst"
  | Sk -> "sk"
  | Intro_def -> "intro-def"
  | Th_lemma -> "th-lemma"
  | Other s -> s
  | Quant_inst_local -> "quant-inst-local"
  | Definition -> "definition"
  | Elim_subst -> "elim-subst"

(* Classification by declaration kind; the printed name is kept for every
   other rule so listings and statistics read like Z3's own output. *)
let rule_of_decl d =
  match FuncDecl.get_decl_kind d with
  | Z3enums.OP_PR_ASSERTED -> Asserted
  | OP_PR_HYPOTHESIS -> Hypothesis
  | OP_PR_LEMMA -> Lemma
  | OP_PR_UNIT_RESOLUTION -> Unit_resolution
  | OP_PR_QUANT_INST -> Quant_inst
  | OP_PR_SKOLEMIZE -> Sk
  | OP_PR_DEF_INTRO -> Intro_def
  | OP_PR_TH_LEMMA -> Th_lemma
  | _ -> Other (decl_name d)

type side = A | B

let side_to_string = function A -> "A" | B -> "B"

type sides = { has_a : bool; has_b : bool }

type node = {
  uid : int;
  mutable rule : rule;
  mutable prem : node list;
  concl : Expr.expr;
  mutable side : side option;
  params : FuncDecl.Parameter.parameter list;
  mutable hyps : ES.t option;
  mutable sides : sides option;
  mutable delta : Expr.expr list option;
}

let uid_counter = ref 0

let fresh_uid () =
  incr uid_counter;
  !uid_counter

let mk_node ?side ?(params = []) rule prem concl =
  { uid = fresh_uid (); rule; prem; concl; side; params; hyps = None; sides = None; delta = None }

type imported = { root : node; nodes : node list; rule_counts : (string * int) list }

exception Unrecognised_assertion of Expr.expr

let premises p =
  let a = Expr.get_args p in
  List.filteri (fun i _ -> i < List.length a - 1) a

let conclusion p =
  let a = Expr.get_args p in
  List.nth a (List.length a - 1)

let param_to_string = function
  | FuncDecl.Parameter.P_Int i -> string_of_int i
  | P_Dbl f -> string_of_float f
  | P_Rat r -> r
  | P_Sym s -> Symbol.to_string s
  | P_Srt s -> Sort.to_string s
  | P_Ast a -> Util.to_string (Expr.expr_of_ast a)
  | P_Fdl f -> decl_name f
  | P_Internal s | P_ZStr s -> s

(* Iterative post-order traversal, mirroring import_proof in z3itp.py: a node
   is pushed once unexpanded (to schedule its premises) and once expanded (to
   build it after its premises). *)
let import ~a ~b proof =
  let in_a = ES.of_list a and in_b = ES.of_list b in
  let memo : node EH.t = EH.create 1024 in
  let order = ref [] in
  let stack = Stack.create () in
  Stack.push (proof, false) stack;
  while not (Stack.is_empty stack) do
    let p, expanded = Stack.pop stack in
    if not (EH.mem memo p) then
      if not expanded then begin
        Stack.push (p, true) stack;
        (* Same order as z3itp.py (premises pushed left to right, so the last
           premise is expanded first): node numbering and the order in which
           localisation constants are introduced then match the Python version. *)
        List.iter (fun q -> if not (EH.mem memo q) then Stack.push (q, false) stack) (premises p)
      end
      else begin
        let d = Expr.get_func_decl p in
        let rule = rule_of_decl d in
        let prem = List.map (EH.find memo) (premises p) in
        let concl = conclusion p in
        let side =
          if rule <> Asserted then None
          else if ES.mem concl in_a then Some A
          else if ES.mem concl in_b then Some B
          else raise (Unrecognised_assertion concl)
        in
        let n = mk_node ?side ~params:(FuncDecl.get_parameters d) rule prem concl in
        EH.replace memo p n;
        order := n :: !order
      end
  done;
  let nodes = List.rev !order in
  let counts = Hashtbl.create 32 in
  List.iter
    (fun n ->
      let k = rule_name n.rule in
      Hashtbl.replace counts k (1 + Option.value ~default:0 (Hashtbl.find_opt counts k)))
    nodes;
  let rule_counts = Hashtbl.fold (fun k v acc -> (k, v) :: acc) counts [] |> List.sort compare in
  { root = EH.find memo proof; nodes; rule_counts }

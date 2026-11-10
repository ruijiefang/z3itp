(* Proof listings.  See listing.mli. *)

open Z3
open Util
open Proof_dag

let truncate width s = if String.length s <= width then s else String.sub s 0 (width - 3) ^ "..."

let proof ?(width = 110) p =
  let ids = EH.create 256 and lines = ref [] in
  let stack = Stack.create () in
  Stack.push (p, false) stack;
  while not (Stack.is_empty stack) do
    let n, expanded = Stack.pop stack in
    if not (EH.mem ids n) then
      if not expanded then begin
        Stack.push (n, true) stack;
        (* as dump_proof.py: push premises right to left, so the first
           premise is listed first *)
        List.iter (fun q -> Stack.push (q, false) stack) (List.rev (premises n))
      end
      else begin
        EH.replace ids n (EH.length ids + 1);
        let d = Expr.get_func_decl n in
        let params = FuncDecl.get_parameters d in
        let ptxt = if params = [] then "" else "{" ^ String.concat ", " (List.map param_to_string params) ^ "}" in
        let prem =
          match premises n with
          | [] -> ""
          | ps -> "  (" ^ String.concat ", " (List.map (fun q -> Printf.sprintf "[%d]" (EH.find ids q)) ps) ^ ")"
        in
        lines :=
          Printf.sprintf "[%3d] %s%s%s  |-  %s" (EH.find ids n) (decl_name d) ptxt prem
            (truncate width (to_string (conclusion n)))
          :: !lines
      end
  done;
  String.concat "\n" (List.rev !lines)

let annotated ?(width = 70) t =
  let nodes = Interp.nodes t in
  let num = Hashtbl.create 256 in
  List.iteri (fun i n -> Hashtbl.replace num n.uid (i + 1)) nodes;
  let lines =
    List.map
      (fun n ->
        let prem =
          String.concat ","
            (List.map
               (fun p -> match Hashtbl.find_opt num p.uid with Some k -> string_of_int k | None -> "*")
               n.prem)
        in
        let side = match n.side with Some s -> " " ^ side_to_string s | None -> "" in
        let phi =
          match Interp.partial_interpolant t n with
          | None -> "."
          | Some phi -> to_string (Expr.simplify phi None)
        in
        Printf.sprintf "[%2d] %s%s(%s)  |- %s\n      itp: %s" (Hashtbl.find num n.uid) (rule_name n.rule) side prem
          (truncate width (to_string n.concl)) phi)
      nodes
  in
  String.concat "\n" lines

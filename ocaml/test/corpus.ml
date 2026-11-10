(* Reading the shared test corpus written by scripts/dump_corpus.py.

   Layout: one directory per case, holding A.smt2 and B.smt2.  Each file has
   the full set of declarations followed by one (assert ...) per conjunct of
   that side.  Both files are parsed into the same context; same-named
   declarations resolve to the same symbols, so A and B share vocabulary
   exactly as in the original problem. *)

open Z3

let read_file path = In_channel.with_open_bin path In_channel.input_all

let parse ctx path =
  AST.ASTVector.to_expr_list (SMT.parse_smtlib2_string ctx (read_file path) [] [] [] [])

(* Cases in lexicographic order of their directory names. *)
let load ctx dir =
  Sys.readdir dir |> Array.to_list |> List.sort compare
  |> List.filter (fun n -> Sys.file_exists (Filename.concat (Filename.concat dir n) "A.smt2"))
  |> List.map (fun n ->
         let d = Filename.concat dir n in
         { Cases.name = n; a = parse ctx (Filename.concat d "A.smt2"); b = parse ctx (Filename.concat d "B.smt2") })

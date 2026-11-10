(* Test runner: interpolate every case, verify every interpolant
   (A |= I, B /\ I unsat, L(I) within L(A) & L(B)), print one line per case.

   Usage:
     test_z3itp.exe [options] MODE [ARGS]
   modes:
     hand                 the 16 hand-written cases
     bmc K...             BMC unrollings, cuts 1, K/2, K-1 for each K (default 3 6 10)
     random N [SIZE]      N random unsat UF+LIA pairs with SIZE atoms per side (default 40, 6)
     corpus DIR           every case of a corpus written by scripts/dump_corpus.py
   options:
     -v                   print each interpolant
     --debug              check the S_I invariant at every proof node
     --report FILE        also write a tab-separated report (for parity checks)
     --seed N             seed of the random mode (default 1) *)

open Z3
open Z3itp

let verbose = ref false
let debug = ref false
let report_file = ref None
let seed = ref 1
let mode = ref []

let speclist =
  [
    ("-v", Arg.Set verbose, " print interpolants");
    ("--debug", Arg.Set debug, " check the S_I invariant at every node");
    ("--report", Arg.String (fun f -> report_file := Some f), "FILE write a tab-separated report");
    ("--seed", Arg.Set_int seed, "N seed for the random mode");
  ]

let union_symbols es = List.fold_left (fun acc e -> Util.FS.union acc (Util.symbols e)) Util.FS.empty es

(* Stage counts as "name=k" pairs, sorted. *)
let stage_summary t =
  Interp.stats t
  |> List.filter_map (fun (k, v) ->
         if String.length k > 4 && String.sub k 0 4 = "2nd:" then Some (Printf.sprintf "%s=%d" (String.sub k 4 (String.length k - 4)) v)
         else None)
  |> String.concat ","

type outcome = { name : string; ok : bool; line : string; tsv : string }

let run_case ctx (c : Cases.case) =
  let t0 = Unix.gettimeofday () in
  match Interp.interpolate ~debug:!debug ctx c.a c.b with
  | exception e ->
      let msg =
        match e with
        | Secondary.Failed (a, b) -> Printf.sprintf "secondary prover failed on lemma A'=%s B'=%s" (Util.to_string a) (Util.to_string b)
        | Interp.Not_unsat s -> "A /\\ B is " ^ s
        | Interp.Check_failed s -> "S_I check failed: " ^ s
        | Z3.Error s -> "Z3 error: " ^ s
        | e -> Printexc.to_string e
      in
      let msg = if String.length msg > 300 then String.sub msg 0 300 ^ "..." else msg in
      { name = c.name; ok = false; line = Printf.sprintf "%-24s ERROR %s" c.name msg; tsv = Printf.sprintf "%s\tERROR\t\t\t\t\t" c.name }
  | itp, t ->
      let dt = Unix.gettimeofday () -. t0 in
      let shared = Util.FS.inter (union_symbols c.a) (union_symbols c.b) in
      let v = Util.verify ~shared ctx (Util.mk_and ctx c.a) (Util.mk_and ctx c.b) itp in
      let sizes = Interp.lemma_sizes t in
      let line =
        Printf.sprintf "%-24s %-3s %5.2fs nodes=%4d lemmas=%d max_lemma=%d loc=%d 2nd={%s}%s" c.name
          (if v = Util.Ok then "OK" else "BAD " ^ Util.verdict_to_string v)
          dt (Interp.stat t "proof_nodes") (Interp.stat t "S_I:Lemma")
          (List.fold_left max 0 sizes)
          (Interp.stat t "localisation_constants")
          (stage_summary t)
          (if !verbose then "\n   I = " ^ Util.to_string itp else "")
      in
      let tsv =
        String.concat "\t"
          [
            c.name;
            Util.verdict_to_string v;
            string_of_int (Interp.stat t "proof_nodes");
            string_of_int (Interp.stat t "S_I:Lemma");
            string_of_int (Interp.stat t "localisation_constants");
            string_of_int (Interp.stat t "qinst_localised");
            stage_summary t;
          ]
      in
      { name = c.name; ok = v = Util.Ok; line; tsv }

let random_cases ctx n size =
  let rng = Random.State.make [| !seed |] in
  let rec loop k acc =
    if k > n then List.rev acc
    else
      let a, b = Cases.random_case ctx rng size size in
      let sat fs = Util.check ctx fs <> Solver.UNSATISFIABLE in
      if Util.check ctx (a @ b) = Solver.UNSATISFIABLE && sat a && sat b then
        loop (k + 1) ({ Cases.name = Printf.sprintf "random-%d" k; a; b } :: acc)
      else loop k acc
  in
  loop 1 []

let () =
  Arg.parse (Arg.align speclist) (fun s -> mode := !mode @ [ s ]) "test_z3itp.exe [options] (hand | bmc K... | random N [SIZE] | corpus DIR)";
  let ctx = Interp.make_context () in
  let cases =
    match !mode with
    | [] | [ "hand" ] -> Cases.hand ctx
    | "bmc" :: ks ->
        let ks = if ks = [] then [ 3; 6; 10 ] else List.map int_of_string ks in
        List.concat_map
          (fun k -> List.sort_uniq compare [ 1; k / 2; k - 1 ] |> List.map (fun cut -> Cases.bmc ctx k cut))
          ks
    | [ "random"; n ] -> random_cases ctx (int_of_string n) 6
    | [ "random"; n; size ] -> random_cases ctx (int_of_string n) (int_of_string size)
    | [ "corpus"; dir ] -> Corpus.load ctx dir
    | _ ->
        prerr_endline "unknown mode; see --help";
        exit 2
  in
  let outcomes =
    List.map
      (fun c ->
        let o = run_case ctx c in
        print_endline o.line;
        o)
      cases
  in
  let good = List.length (List.filter (fun o -> o.ok) outcomes) in
  Printf.printf "\n%d/%d verified\n" good (List.length outcomes);
  (match !report_file with
  | Some f -> Out_channel.with_open_text f (fun oc -> List.iter (fun o -> output_string oc (o.tsv ^ "\n")) outcomes)
  | None -> ());
  exit (if good = List.length outcomes then 0 else 1)

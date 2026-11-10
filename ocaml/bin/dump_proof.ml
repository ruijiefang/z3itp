(* Print the Z3 proof of each built-in example as a numbered listing,
   premises first:  [k] rule{params}  (premises)  |-  conclusion.
   Port of dump_proof.py; the examples are the ones used in
   docs/Z3-PROOF-FORMAT.md. *)

open Z3
open Z3itp

let () =
  let ctx = Interp.make_context () in
  let open Dsl.Make (struct
    let ctx = ctx
  end) in
  let show title fmls =
    let s = Solver.mk_solver ctx None in
    Solver.add s fmls;
    let r = Solver.check s [] in
    Printf.printf "==== %s: %s\n" title (Solver.string_of_status r);
    List.iter (fun f -> Printf.printf "   assert %s\n" (Util.to_string f)) fmls;
    (if r = Solver.UNSATISFIABLE then match Solver.get_proof s with Some p -> print_endline (Listing.proof p) | None -> ());
    print_newline ()
  in
  let a = ic "a" and c = ic "c" and x = ic "x" and y = ic "y" and z = ic "z" in
  let f = fn "f" [ int ] int in
  show "EUF + arithmetic" [ a === x; (f @@@ [ a ]) >== num 0; y === (f @@@ [ x ]); z === y; z <<< num 0 ];
  let p = bc "p" and q = bc "q" and r = bc "r" in
  show "propositional with case splits" [ or_ [ p; q ]; or_ [ not_ p; r ]; or_ [ not_ q; r ]; not_ r ];
  show "arithmetic case split"
    [ or_ [ x >>> num 2; x <<< num (-2) ]; ((x *** num 1) +++ y) === num 0; y >== num (-1); y <== num 1 ];
  let xv = ic "X" and pp = fn "P" [ int ] bool in
  show "quantifier instantiation" [ forall [ xv ] (implies (xv >>> a) (pp @@@ [ xv ])); c >>> a; not_ (pp @@@ [ c ]) ];
  show "skolemization"
    [ exists [ xv ] (and_ [ xv >>> a; (f @@@ [ xv ]) === c ]); forall [ xv ] (implies (xv >>> a) ((f @@@ [ xv ]) =/= c)) ];
  let arr = array "arr" in
  show "arrays" [ store arr x y === arr; x === a; select arr a =/= y ];
  show "ite / Tseitin" [ ite p x y >>> num 3; x <<< num 0; y <<< num 0 ]

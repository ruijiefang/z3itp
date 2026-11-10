(* The quick-start example of README.md, kept compiled so it cannot rot. *)
let () =
  let ctx = Z3itp.Interp.make_context () in          (* proof=true, model=true *)
  let open Z3itp.Dsl.Make (struct let ctx = ctx end) in
  let a = ic "a" and x = ic "x" and y = ic "y" and z = ic "z" in
  let f = fn "f" [ int ] int in
  let alist = [ a === x; (f @@@ [ a ]) >== num 0; y === (f @@@ [ x ]) ] in
  let blist = [ z === y; z <<< num 0 ] in
  let itp, t = Z3itp.Interp.interpolate ctx alist blist in
  print_endline (Z3itp.Util.to_string itp);           (* (>= y 0) *)
  print_endline (Z3itp.Listing.annotated t)           (* proof + partial interpolants *)

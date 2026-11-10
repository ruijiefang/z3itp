(* Test inputs, rebuilt from test_z3itp.py:
   - [hand ctx]: the 16 hand-written A/B pairs;
   - [bmc ctx k cut]: bounded-model-checking unrollings;
   - [random_case]: random unsat UF+LIA pairs (OCaml's own generator; not the
     same stream as Python's -- use the corpus for parity).
   Every formula is built in the given context, which must have proofs on. *)

open Z3

type case = { name : string; a : Expr.expr list; b : Expr.expr list }

let hand ctx =
  let open Z3itp.Dsl.Make (struct
    let ctx = ctx
  end) in
  let x = ic "x" and y = ic "y" and z = ic "z" and a = ic "a" and b = ic "b" and c = ic "c" and d = ic "d" in
  let f = fn "f" [ int ] int and g = fn "g" [ int ] int and h = fn "h" [ int ] int in
  let x1 = rc "x1" and x2 = rc "x2" in
  let xv = ic "X" and yv = ic "Y" in
  let p = fn "P" [ int ] bool and q = fn "Q" [ int; int ] bool in
  let arr = array "arr" and brr = array "brr" in
  let s = Array.init 5 (fun i -> ic (Printf.sprintf "s%d" i)) in
  let step u v = or_ [ v === (u +++ num 2); v === u ] in
  (* pigeonhole 4 -> 3 *)
  let p3 = Array.init 4 (fun i -> Array.init 3 (fun j -> bc (Printf.sprintf "p%d%d" i j))) in
  let at_most =
    List.concat_map
      (fun j ->
        List.concat_map
          (fun i -> List.init (3 - i) (fun k -> or_ [ not_ p3.(i).(j); not_ p3.(i + k + 1).(j) ]))
          [ 0; 1; 2 ])
      [ 0; 1; 2 ]
  in
  let take n l = List.filteri (fun i _ -> i < n) l and drop n l = List.filteri (fun i _ -> i >= n) l in
  let row i = or_ (Array.to_list p3.(i)) in
  [
    { name = "uf-lia"; a = [ a === x; (f @@@ [ a ]) >== num 0; y === (f @@@ [ x ]) ]; b = [ z === y; z <<< num 0 ] };
    { name = "euf-chain"; a = [ a === b; (f @@@ [ b ]) === c ]; b = [ b === d; (f @@@ [ d ]) =/= c ] };
    { name = "lra"; a = [ x1 <== (rnum 2 *** x2); x2 <== rnum 0 ]; b = [ x1 >== rnum 1 ] };
    { name = "lia-parity"; a = [ x === (num 2 *** a) ]; b = [ x === ((num 2 *** b) +++ num 1) ] };
    { name = "quant-A"; a = [ forall [ xv ] (implies (xv >>> a) (p @@@ [ xv ])); c >>> a ]; b = [ not_ (p @@@ [ c ]) ] };
    (* the ACL2 S6 counterexample shape: abstracting g(c) would be unsound *)
    { name = "quant-foreign-witness"; a = [ forall [ xv ] (p @@@ [ g @@@ [ xv ] ]) ]; b = [ not_ (p @@@ [ g @@@ [ c ] ]) ] };
    {
      name = "quant-2var";
      a = [ forall [ xv; yv ] (or_ [ q @@@ [ xv; yv ]; (xv +++ yv) >>> a ]); a >>> num 10 ];
      b = [ not_ (q @@@ [ b; c ]); (b +++ c) <<< num 3 ];
    };
    { name = "arrays"; a = [ store arr x y === arr; x === a ]; b = [ select arr a =/= y ] };
    { name = "arrays-2"; a = [ brr === store arr a (num 5) ]; b = [ select brr c =/= num 5; c === a ] };
    {
      name = "bmc";
      a = [ s.(0) === num 0; step s.(0) s.(1); step s.(1) s.(2) ];
      b = [ step s.(2) s.(3); step s.(3) s.(4); s.(4) === num 5 ];
    };
    (* existentials: Skolemisation ('sk' leaves) on each side *)
    {
      name = "exists-A";
      a = [ exists [ xv ] (and_ [ xv >>> a; (f @@@ [ xv ]) === c ]) ];
      b = [ forall [ xv ] (implies (xv >>> a) ((f @@@ [ xv ]) =/= c)) ];
    };
    { name = "exists-B"; a = [ forall [ xv ] ((f @@@ [ xv ]) >== b) ]; b = [ exists [ xv ] ((f @@@ [ xv ]) <<< (b --- num 1)) ] };
    (* proofs with hypothesis / lemma (case splits in the SAT search) *)
    { name = "pigeonhole-4-3"; a = [ row 0; row 1 ] @ take 9 at_most; b = [ row 2; row 3 ] @ drop 9 at_most };
    {
      name = "uf-case-split";
      a = [ or_ [ (f @@@ [ x ]) === a; (f @@@ [ x ]) === b ]; or_ [ x === y; x === z ] ];
      b = [ (f @@@ [ y ]) =/= a; (f @@@ [ z ]) =/= a; (f @@@ [ y ]) =/= b; (f @@@ [ z ]) =/= b ];
    };
    { name = "distinct"; a = [ distinct [ x; y; z ]; x >== num 0; x <== num 1 ]; b = [ y >== num 0; y <== num 1; z >== num 0; z <== num 1 ] };
    {
      name = "uf-bmc";
      a = [ s.(0) === num 0; s.(1) === (h @@@ [ s.(0) ]); forall [ xv ] ((h @@@ [ xv ]) >== xv) ];
      b = [ s.(2) === (h @@@ [ s.(1) ]); s.(2) <<< num 0 ];
    };
  ]

(* Unrolling of  i := 0; s := 0; loop { mem[i] := h(i); s := s + mem[i]; i := i + 1 }
   with axiom  forall x. h(x) >= 0  and bad state  s < 0  at step k.
   A = init + first [cut] steps (+ axiom), B = remaining steps + bad. *)
let bmc ctx k cut =
  let open Z3itp.Dsl.Make (struct
    let ctx = ctx
  end) in
  let h = fn "h" [ int ] int and xv = ic "X" in
  let i = Array.init (k + 1) (fun t -> ic (Printf.sprintf "i%d" t)) in
  let s = Array.init (k + 1) (fun t -> ic (Printf.sprintf "s%d" t)) in
  let m = Array.init (k + 1) (fun t -> array (Printf.sprintf "mem%d" t)) in
  let steps =
    List.init k (fun t ->
        and_
          [
            m.(t + 1) === store m.(t) i.(t) (h @@@ [ i.(t) ]);
            s.(t + 1) === (s.(t) +++ select m.(t + 1) i.(t));
            i.(t + 1) === (i.(t) +++ num 1);
          ])
  in
  let a = [ i.(0) === num 0; s.(0) === num 0 ] @ List.filteri (fun j _ -> j < cut) steps @ [ forall [ xv ] ((h @@@ [ xv ]) >== num 0) ] in
  let b = List.filteri (fun j _ -> j >= cut) steps @ [ s.(k) <<< num 0 ] in
  { name = Printf.sprintf "bmc k=%d cut=%d" k cut; a; b }

(* Random UF+LIA pair with A-local, B-local and shared constants, same shape
   as test_z3itp.random_case. *)
let random_case ctx rng n_a n_b =
  let open Z3itp.Dsl.Make (struct
    let ctx = ctx
  end) in
  let sh = List.init 3 (fun i -> ic (Printf.sprintf "s%d" i)) in
  let la = List.init 3 (fun i -> ic (Printf.sprintf "a%d" i)) in
  let lb = List.init 3 (fun i -> ic (Printf.sprintf "b%d" i)) in
  let f = fn "f" [ int ] int and fa = fn "fa" [ int ] int and fb = fn "fb" [ int ] int in
  let pick l = List.nth l (Random.State.int rng (List.length l)) in
  let atom vs fn =
    let u = pick vs and v = pick vs in
    let k = Random.State.int rng 5 - 2 in
    let t = pick [ u; fn @@@ [ u ]; f @@@ [ u ] ] in
    match Random.State.int rng 4 with
    | 0 -> t === (v +++ num k)
    | 1 -> t <== (v +++ num k)
    | 2 -> t >== (v +++ num k)
    | _ -> t =/= v
  in
  let fml vs fn n =
    List.init n (fun _ -> if Random.State.float rng 1.0 < 0.4 then or_ [ atom vs fn; atom vs fn ] else atom vs fn)
  in
  (fml (sh @ la) fa n_a, fml (sh @ lb) fb n_b)

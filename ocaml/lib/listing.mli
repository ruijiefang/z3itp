(** Human-readable listings of proofs, in the formats of [dump_proof.py] and
    [z3itp.annotated_listing]. *)

open Z3

val proof : ?width:int -> Expr.expr -> string
(** [proof p] lists the raw Z3 proof term [p], one node per line, premises
    before the nodes that use them:
    {v [  k] rule{params}  ([i], [j])  |-  conclusion v}
    Shared sub-proofs appear once. Conclusions longer than [width]
    (default 110) are truncated with ["..."]. Same numbering and format as
    [dump_proof.py] (first premise explored first). *)

val annotated : ?width:int -> Interp.t -> string
(** After {!Interp.run}: the imported proof (in import order), one node per
    line, followed by the partial interpolant computed for it, or ["."] if
    none was needed (a LOCAL step above it covered it). Same format as
    [annotated_listing] in [z3itp.py]:
    {v [ k] rule side(premises)  |- conclusion
      itp: phi v} *)

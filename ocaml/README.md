# z3itp (OCaml): interpolants from Z3 proofs

An OCaml port of `../z3itp.py`. It computes Craig interpolants from Z3
proofs, following K. L. McMillan, *Interpolants from Z3 proofs*
(FMCAD 2011, `../81.pdf`), using only Z3's public OCaml API, plus one C stub
of the bindings that the high-level API does not expose (see
[Design decisions](#design-decisions)).

Given lists of formulas `A` and `B` whose conjunction is unsatisfiable, it
returns a formula `I` such that:

- `A ⊨ I`;
- `B ∧ I` is unsatisfiable;
- every uninterpreted symbol of `I` occurs in both `A` and `B`.

The port is faithful to the Python version: same pipeline, same decisions,
same statistics. On a shared corpus of 119 problems, both versions verify
every interpolant ([Parity with the Python version](#parity-with-the-python-version)).

Background reading in `../docs/`:

- `Z3-PROOF-FORMAT.md`: Z3's proof objects, rule by rule;
- `INTERPOLATION-GUIDE.md`: the algorithm, from scratch, with soundness
  arguments and worked examples;
- `z3-mbi/z3-mbi.pdf`: Z3's own model-based interpolation (`pogo`), which
  the secondary prover's MBP stage re-implements.

## Contents

- [Requirements and building](#requirements-and-building)
- [Quick start](#quick-start)
- [Layout](#layout)
- [The pipeline](#the-pipeline)
- [The secondary prover](#the-secondary-prover)
- [Design decisions](#design-decisions)
- [Tests](#tests)
- [Parity with the Python version](#parity-with-the-python-version)
- [Deviations from the Python version](#deviations-from-the-python-version)
- [Limitations and follow-ons](#limitations-and-follow-ons)

## Requirements and building

| Component | Version used |
|---|---|
| OCaml | 5.4.1 |
| dune | ≥ 3.0 (3.23.1 used) |
| `z3` opam package (OCaml bindings) | 4.16.0 |
| `zarith` | 1.14 |
| `unix` | (part of OCaml; test runner only) |

```sh
cd ocaml
dune build                 # library, test runner, dump_proof
dune test                  # hand-written cases + BMC cases
```

## Quick start

```ocaml
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
```

This is `bin/quickstart.ml`; run it with `dune exec bin/quickstart.exe`.

Constraints on the input:

- **Every formula must be built in the context passed to `interpolate`.**
- **That context must have proof generation on.** Use
  `Interp.make_context`, or `Z3.mk_context [("proof","true"); ...]`.

Options:

- **`~debug:true`** checks the calculus invariant at every proof node.
- **`~stages`** chooses the secondary-prover stages. The default is
  `Secondary.default_stages`, i.e. `[farkas; mbp; qe]`.

Exceptions (all documented in `lib/interp.mli`):

| Exception | Raised when |
|---|---|
| `Interp.Not_unsat` | `A ∧ B` is not unsatisfiable |
| `Secondary.Failed` | a lemma could not be interpolated |
| `Interp.Check_failed` | debug mode finds a violated invariant |
| `Interp.Root_not_strict` | the root sequent contains an uncoloured formula |

## Layout

```
ocaml/
  dune-project
  lib/                 library z3itp (every module has a documented .mli)
    util.ml(i)         expression helpers, tables keyed on Z3 objects, symbols, check, verify
    native.ml(i)       Z3_qe_model_project, bound by re-declaring its C stub
    proof_dag.ml(i)    proof nodes and iterative proof import
    interp.ml(i)       the interpolator: colouring, axiom elimination, sequents,
                       S_I translation, lemma extraction, ELIM, driver
    secondary.ml(i)    the secondary interpolating prover (stages)
    listing.ml(i)      proof listings and annotated listings
    dsl.ml(i)          a small formula-building DSL (tests, examples)
  bin/dump_proof.ml    prints Z3 proofs of built-in examples (port of dump_proof.py)
  bin/quickstart.ml    the quick-start example below, kept compiled
  test/                test runner, the hand-written cases, the BMC generator, corpus reader
  corpus/              119 A/B problems as SMT-LIB, written by ../scripts/dump_corpus.py
  PLAN.md              the porting plan
../scripts/
  dump_corpus.py       writes the corpus from ../test_z3itp.py (Python)
  run_corpus.py        runs ../z3itp.py on the corpus, writes a TSV report (Python)
  compare_reports.py   compares the Python and OCaml reports
```

Correspondence with the Python source:

| `z3itp.py` | OCaml |
|---|---|
| expression utilities, `symbols`, `check`, `verify` | `Util` |
| `Node`, `import_proof` | `Proof_dag` |
| `Interpolator` (all methods except the secondary prover) | `Interp` |
| `secondary_interpolant`, `abstract_quantifiers`, `ackermannize`, `linearize`, `ineq`, `farkas_interpolant`, `mbp_interpolant`, `qe_interpolant`, `simplify_itp` | `Secondary` |
| `binary_interpolant` | none (see [The secondary prover](#the-secondary-prover)) |
| `ModelRef.project` | `Native.project` |
| `annotated_listing`, `dump_proof.listing` | `Listing` |
| `interpolate` | `Interp.interpolate` |
| `run_big_stack` | none needed (see below) |

## The pipeline

`Interp.run` performs these steps. Paper sections are in brackets.

1. **Solve and import.** Solve `A ∧ B` with proofs, then copy the proof DAG
   into mutable `Proof_dag.node` records with an iterative, memoised
   traversal. Sharing is preserved. `asserted` leaves get side `A` or `B` by
   identity with the input formulas.
2. **Colour fresh symbols** (`colour_fresh_symbols`).
   - Skolem constants (`sk` leaves) and Tseitin names (`intro-def` leaves)
     belong to neither input. Each becomes local to the side of the formula
     it names, and its leaf counts as an assertion of that side.
   - Sound because these are definitional extensions.
3. **Axiom elimination** (`eliminate_axioms`) [IV-C].
   - Applies to a `quant-inst` leaf whose instance mixes A-only and B-only
     symbols.
   - The instance terms are localised: their highest coloured subterms are
     replaced by fresh *localisation constants* `s`, with definitions
     `s = t` on the side of `t`.
   - The leaf becomes `elim-subst`, with premises: the local instance, plus
     the definition leaves (including reused and nested ones).
   - Localisation constants count as shared.
4. **Translation into S_I** (`interp`) [III, Fig. 1]. Every node proves a
   one-sided sequent `(A,B) ⊢ Δ`. For each node:
   - **LOCAL:** the sub-proof uses one side and `Δ` is local to it. The
     partial interpolant is `true` (B), or the disjunction of `Δ`'s shared
     literals (A).
   - **CONTRA:** a `lemma` whose premise has the same `Δ`.
   - **RES:** `unit-resolution` with strict premises. Units are folded into
     the clause's interpolant: OR for an A-coloured pivot, AND for a
     B-coloured one.
   - **LEMMA:** anything else; see the next step.
5. **Lemma extraction** (`lemma`) [IV-B].
   - The frontier is the nearest strict descendants with coloured
     conclusions and no extra hypotheses.
   - The lemma `⊢ ¬F₁, …, ¬Fₘ, Δ` is interpolated by `Secondary.interpolate`.
   - The frontier facts are then resolved back in.
   - Nodes are read either as a clause or as one formula, and the
     interpolants converted between the two readings (`as_clause` /
     `as_unit`).
6. **ELIM** [IV-C]. Quantify the localisation constants out of the
   interpolant, in reverse order of introduction: `∀` for B-side
   definitions, `∃` for A-side ones. Then simplify (`simplify`, then
   `qe-light`, kept only if Z3 confirms equivalence).

`../docs/INTERPOLATION-GUIDE.md` §7 explains each step with proofs.
`Listing.annotated` prints the proof together with the partial interpolant
computed at every node.

## The secondary prover

`Secondary.interpolate ctx shared a b` interpolates one lemma. Its input is
`(a, b)` with `a ∧ b` unsatisfiable.

1. **Trivial cases:** `a` unsat gives `false`; `b` unsat gives `true`
   (2-second checks).
2. **Preparation:**
   - quantified sub-formulas become Boolean atoms, if the pair stays unsat
     (`abstract_quantifiers`);
   - A-local function symbols are Ackermannized (`ackermannize`).
3. **Stages,** each a `Secondary.stage` record, tried in order. The first
   result that passes `Util.verify` wins:

   | Stage | What it does |
   |---|---|
   | `farkas` | Finds Farkas multipliers with a Z3 LP over the lemma's linear literals; the interpolant is the A-part of the combination. Coefficients are exact (`zarith` `Q.t`). |
   | `mbp` | The model-based interpolation loop of Z3's `qe_mbi.cpp`: project models of `a` with `Native.project`, generalise with unsat cores of `b`, block, repeat (cap 200). |
   | `qe` | `∃ loc. a` through Z3's `qe` tactic. |

The chain stops at `qe`. `z3itp.py` has one more, last-resort stage: it runs
the `z3` executable on `(get-interpolant a b)`, Z3's own model-based
interpolator, which is reachable only from the command line. That stage is
not ported, so the library never starts an external process. It was never
the winning stage on the test suites below, while `qe` is: on the corpus it
interpolates 6 lemmas (in `exists-B`, `uf-case-split`, `random20-003`,
`random20-007`, `random20-009`) on which `mbp` fails, all with an A-local
constant under a shared function symbol.

The list is a parameter (`?stages`), so new stages (§[Limitations](#limitations-and-follow-ons))
can be added without touching the driver. Per-stage outcomes are counted in
the statistics as `2nd:<stage>`.

## Design decisions

**One context, threaded explicitly.**
- Python relies on a global `set_param(proof=True)`.
- Here the interpolator record carries the `context`. Every input formula,
  and everything built during interpolation, lives in it.

**Tables are keyed on Z3 objects, never on integer ids.**
- Z3 recycles AST ids of freed objects. A cache keyed on `get_id()` was the
  worst bug of the Python version.
- `Util.EH`, `Util.ES`, `Util.FS` and `Util.FH` are keyed on the expression
  or declaration itself, which keeps it alive. That rules the bug out by
  construction.
- Node memo tables are keyed on our own `uid`s, which are never reused.

**Rules are a variant, dispatched by `Z3enums.decl_kind`.**
- Printed names are kept only for listings.
- Three synthetic rules (`Quant_inst_local`, `Definition`, `Elim_subst`)
  record the rewriting done by axiom elimination.

**Model-based projection without casts.**
- `Z3_qe_model_project` is not in `z3.mli`. In `z3.ml`, however, all handle
  types are aliases of the same native pointer type.
- `Native` therefore re-declares the existing C stub `n_qe_model_project`
  with high-level types:

  ```ocaml
  external qe_model_project : context -> Model.model -> int -> Expr.expr list -> Expr.expr -> Expr.expr
    = "n_qe_model_project"
  ```

**Both `quant-inst` shapes are accepted.**
- Z3 4.16 (these bindings) flattens the conclusion:
  `(or (not ∀x.φ) l₁ … lₙ)`.
- z3-solver 5.1 (where the Python version was developed) nests it:
  `(or (not ∀x.φ) (or l₁ … lₙ))`.
- `Interp.instance_shape` recognises both, and the localised leaf is rebuilt
  in the same shape. A literal port of the Python check would silently never
  localise anything under 4.16.

**Same traversal order as Python.**
- Premises are pushed left to right, so the last premise is expanded first.
- Node numbering, and the order in which localisation constants are
  introduced, therefore match `z3itp.py`.

**No `run_big_stack`.**
- OCaml 5 code runs on a heap-allocated, growable stack.
- Proof import is iterative anyway. If a very deep proof exhausts the stack
  during translation, raise the limit with `OCAMLRUNPARAM=l=<words>`.

**Errors in a stage are not fatal.**
- `Z3.Error`, `Failure`, `Not_found` and `Invalid_argument` raised by a
  stage make the driver move on to the next stage, as Python's
  `except Exception` did.

## Tests

`test/test_z3itp.exe [options] MODE`:

| Mode | Cases |
|---|---|
| `hand` | the 16 hand-written cases of `test_z3itp.py`: UF+LIA, LRA, LIA parity, quantifiers (incl. localisation), arrays, BMC, Skolemisation on either side, pigeonhole (hypothesis/lemma), case splits, `distinct` |
| `bmc K...` | BMC unrollings with arrays, UF and a ∀-axiom; cuts 1, K/2, K−1 |
| `random N [SIZE]` | N random unsat UF+LIA pairs, SIZE atoms per side (OCaml's own generator) |
| `corpus DIR` | every case of a corpus directory |

| Option | Effect |
|---|---|
| `-v` | print interpolants |
| `--debug` | check the S_I invariant at every node |
| `--report FILE` | write a TSV report |
| `--seed N` | seed for the random mode |

Every interpolant is checked independently with `Util.verify`: `A ⊨ I`,
`B ∧ I` unsat, and the vocabulary is shared.

Results with Z3 4.16.0:

| Suite | Result |
|---|---|
| `hand` | 16/16 verified; with `--debug` (invariant at every node) 16/16 |
| `bmc 3 6 10` | 8/8; with `--debug` (`bmc 3 6`) 5/5 |
| `random 40` (6 atoms) | 40/40 |
| `random 30 20` (20 atoms) | 30/30 |
| `random 30 12` with `--debug` | 30/30 |
| `corpus corpus` (119 cases) | 119/119 |

`bin/dump_proof.exe` prints the Z3 proofs of the seven examples used in
`../docs/Z3-PROOF-FORMAT.md`.

## Parity with the Python version

Python's random streams can't be reproduced in OCaml, so both versions are
run on the same files. The corpus was written by the Python script from
`test_z3itp.py`:

- the 16 hand-written cases;
- 8 BMC cases;
- 95 random cases, from Python's seeded generator at three sizes.

To reproduce the comparison:

```sh
# Python side pinned to the same Z3 version as the OCaml bindings
python -m venv venv416 && venv416/bin/pip install z3-solver==4.16.0.0
venv416/bin/python scripts/dump_corpus.py ocaml/corpus            # once
venv416/bin/python scripts/run_corpus.py ocaml/corpus py.tsv
ocaml/_build/default/test/test_z3itp.exe corpus ocaml/corpus --report ml.tsv
python3 scripts/compare_reports.py py.tsv ml.tsv
```

Result (both on Z3 4.16.0):

| | Python | OCaml |
|---|---|---|
| verified | 119 / 119 | 119 / 119 |
| wall time for the corpus | 4.0 s | 1.1 s |
| cases with a different verdict | 0 | 0 |
| different proof size | 39 cases | |
| different lemma count | 13 cases | |
| different winning secondary stages | 13 cases | |

Why proofs differ even on the same Z3 version:

- **Term creation order.** Z3's search depends on the order in which terms
  are created, and the two runners create terms differently. The OCaml
  runner parses the whole corpus first; Python interleaves parsing and
  solving. Run in isolation, several cases do get identical proofs, e.g.
  `exists-B` (37 nodes) and `bmc-k06-cut1` (167 nodes).
- **Different library builds.** Some differences remain even in isolation
  (`uf-lia`: 14 vs 13 nodes), which we attribute to the two `libz3` builds
  (pip wheel vs opam).
- **Interpolant text** also differs (set iteration order), and is never
  compared.

One stage difference was traced in detail (`exists-B`). The two runs produce
the corresponding lemma in different normal forms (`f(X) + -1*b >= -1` vs.
`b - f(x) <= 1`), so the `qe` tactic received different inputs. Z3's `qe`
tactic:

- returned the formula with its top-level `∃` simply dropped in the Python
  run, so the result was rejected by the vocabulary check and Python's
  `z3`-executable stage (not ported, see
  [The secondary prover](#the-secondary-prover)) won;
- kept the quantifier in the OCaml run, and that result verified.

Both outcomes are sound: every candidate is verified before it is accepted.

## Deviations from the Python version

1. **`linearize`** checks the first operand of a subtraction for linearity.
   Python ignores a failure there. This is a bug fix; it can only turn a
   Farkas success into a fall-through.
2. **The symbol cache** is cleared at the start of every run, rather than
   kept process-wide.
3. **`verify`** returns a variant (`Util.verdict`), not `True` or a string.
   The printed strings are the same.
4. **Rule dispatch** uses `decl_kind`; behaviour is unchanged.
5. **Both `quant-inst` shapes** are accepted (see
   [Design decisions](#design-decisions)).
6. **Interpolants** may differ in conjunct and disjunct order.
7. **No `z3`-executable stage.** Python's last-resort `binary_interpolant`
   (`(get-interpolant a b)` run by the `z3` executable) is not ported; the
   secondary prover stops after `qe`.
8. **`quant-inst` parameters:** localisation requires every parameter to be
   a term (`P_Ast`); otherwise the leaf is left alone. Python used all
   parameters as terms. Stricter and harmless: Z3's `quant-inst` parameters
   are always the instance terms.

## Limitations and follow-ons

These are inherited from the Python version and documented in
`../FEASIBILITY.md` and `../docs/`:

- **Few native S_I rules.** Only `unit-resolution`, `lemma` and LOCAL are
  handled natively; everything else becomes a lemma.
- **§IV-D is not implemented.** Pushing resolutions on rewritten atoms
  toward the leaves would shrink lemmas.
- **Array and datatype axiom instances are not localised.** They arrive as
  `th-lemma{array}` / `th-lemma{datatype}` leaves, not `quant-inst`.
- **The secondary prover is incomplete,** and failure aborts the run with
  `Secondary.Failed`.

Planned follow-ons (PLAN.md milestone M6). The stage list is designed for
them:

- an explicit `∃x̄. Ack(a)` fallback, which is correct by construction;
- a purified-MBP stage;
- a strength setting (strong / weak / balanced);
- QE as an optional post-pass.

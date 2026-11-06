# Complex-weighted CSP decidability in Lean

A Lean formalization of Chenghua Liu and Boning Meng,
[*From Block Orthogonality to Decidability in Complex-Weighted Counting CSP*](https://arxiv.org/abs/2608.14845).
The development includes exact uniform recognition, the structural collapse to
Block Orthogonality, the degree-multiple extension, and concrete FP and #P-hardness
implications for fixed languages.

**Current manuscript.** The target is the [STOC 2027 source](paper/stoc2027-CSP.tex)
exported from Overleaf on **2026-11-06**, with its [compiled PDF](paper/stoc2027-CSP.pdf).
The [paper map](docs/paper.md) covers all 48 numbered items in the short paper,
full paper, and appendix. Theorem F.5.2 is the proved **all-instance** pinned
isomorphism theorem. Appendix F.B.1 refutes the historical simple-instance
premise using the exact current profiles `(1,2,6)` and `(1,3,5)`.

The updated public bridges in [ComplexCSP/Paper.lean](ComplexCSP/Paper.lean)
cover the explicit purification group properties in F.3.1 and the general
indexed-family comparison in F.5.6. The independent specification has 127
Comparator goals with stable, label-based identifiers. Historical arXiv v1
sources and receipts remain separately identified.

## Build

Install [Lean via elan](https://lean-lang.org/install/), then run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean **4.24.0**. The exact mathlib revision and verification-tool
revisions are committed in `lake-manifest.json`. All required PlanarHom sources
are included under `vendor/plgh`; no separate proof workspace is needed.
Only public dependencies are downloaded. The full source build is substantial.

## Check the statements and proofs

```sh
python3 scripts/audit.py
python3 scripts/verify.py
```

`verify.py` runs the pinned official [Lean Comparator](https://github.com/leanprover/comparator).
It compares the frozen statements, checks the allowed axioms, and replays the
exported proof dependencies through Lean's kernel. The default mode uses
[Landrun](https://github.com/zouuup/landrun) on Linux.
On macOS, use the explicit local mode
`python3 scripts/verify.py --no-sandbox`. The proof comparison and kernel replay
are the same in both modes.
For an existing checkout with pinned, shared dependency caches, use
`python3 scripts/verify.py --no-sandbox --reuse-dependencies`. This mode uses
direct Lean builds for local sources and never invokes Lake against dependencies.

Start a mathematical review in [verification/Statements.lean](verification/Statements.lean).
That file contains propositions without proofs. [Challenge.lean](verification/Challenge.lean)
exposes those fixed goals, and [Solution.lean](verification/Solution.lean) connects
them to the proved declarations. The verification command does not regenerate
the specification from the solution.

[Verification notes](docs/verification.md) describe the input representation,
checking methods, regression examples, and verification records.

## Source layout

| Directory | Contents |
| --- | --- |
| `ComplexCSP/Algebra` | Exact algebraic encodings, number fields, torsion, power sums, and purification |
| `ComplexCSP/Instances` | Finite instances, pinned values, presentations, and all-instance isomorphism |
| `ComplexCSP/Recognition` | Finite certificates, identity oracles, and uniform recognition |
| `ComplexCSP/Structure` | Generated relations, row equivalence, Mal'tsev operations, and Type Partition |
| `ComplexCSP/Complexity` | Bit-machine evaluators, counting, and charged hardness reductions |
| `verification` | Frozen specification, comparator goals and solutions, and paper correspondence |
| `tests` | Exact-input and instance-semantics regression checks |
| `paper` | Current self-contained STOC source and PDF; archived arXiv v1 source and historical correction |
| `vendor/plgh` | Required PlanarHom proof sources |

To cite the paper, use [CITATION.cff](CITATION.cff).

A software license has not been specified. Provenance of the included PlanarHom
sources is described in [vendor/plgh/README.md](vendor/plgh/README.md).

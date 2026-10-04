# Complex-weighted CSP decidability in Lean

A Lean formalization of Chenghua Liu and Boning Meng,
[*From Block Orthogonality to Decidability in Complex-Weighted Counting CSP*](https://arxiv.org/abs/2608.14845v1).
The development includes exact uniform recognition, the structural collapse to
Block Orthogonality, the degree-multiple extension, and concrete FP and #P-hardness
implications for fixed languages.

**Scope.** Theorem 5.2 of the paper's first version is false with its printed
simple-instance premise. This repository proves an explicit counterexample and
a corrected theorem whose premise quantifies over all finite instances.
The recognition proofs use that correction. The original manuscript is preserved
unchanged; [the paper map and correction](docs/paper.md) identify every numbered
item and the affected argument.

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
For an author's local macOS check without the Linux sandbox, use
`python3 scripts/verify.py --no-sandbox`. The proof comparison and kernel replay
are the same in both modes.

Start a mathematical review in [verification/Statements.lean](verification/Statements.lean).
That file contains propositions without proofs. [Challenge.lean](verification/Challenge.lean)
exposes those fixed goals, and [Solution.lean](verification/Solution.lean) connects
them to the proved declarations. The verification command does not regenerate
the specification from the solution.

[Verification notes](docs/verification.md) describe the input representation,
trust boundary, regression checks, and release verification results.

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
| `paper` | Unmodified arXiv v1 source and the separate minimal correction patch |
| `vendor/plgh` | Required PlanarHom proof sources |

To cite the paper, use [CITATION.cff](CITATION.cff).

This release does not grant an open-source license. The reused source provenance
is described in [vendor/plgh/README.md](vendor/plgh/README.md).

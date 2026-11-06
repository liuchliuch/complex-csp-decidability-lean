# Verification

## Mathematical contract

The input domain is finite and nonempty; the signature is finite and each symbol
has positive arity. Empty signatures, singleton domains, zero tables, unary
symbols, duplicate indexed tables, repeated constraints, repeated scope positions,
and isolated variables are included. Generated tables are literal finite-instance
partial sums, with complex cancellation retained. A degree restriction counts
all scope occurrences; an isolated variable has degree zero.

Each algebraic-complex entry is described by an ascending list of integer
polynomial coefficients and an open rational rectangle isolating exactly one
root. The polynomial need not be monic, irreducible, or square-free. The
recognizers are executable and total on valid descriptions. Validity is the
representation's semantic promise; proofs of validity are erased. There is no
claim that arbitrary malformed descriptions are recognized as invalid.

Recognition is uniform in the input language and positive degree modulus.
Polynomial-time partition evaluation and hardness are statements about a fixed
language, with values represented in a fixed finite rational basis. Such a
representation exists for every finite algebraic language. Instance size includes
the variable count in unary, so isolated variables and the output length are
charged. No polynomial bound for uniform recognition is asserted. FP and
#P-hardness implications do not assume that these complexity properties are
mutually exclusive.

## Frozen propositions and Comparator

`verification/Statements.lean` is the reviewable specification, with 127 goals
for the current 48-item STOC manuscript inventory. Its propositions
are written out explicitly and contain no proof holes. `Challenge.lean` turns them
into comparator goals; its intentional `sorry` terms are confined to that file.
`Solution.lean` proves exactly those goals using the production library.
Neither solution nor production code imports Challenge.

The checker uses the official Comparator revision compatible with Lean 4.24.0,
`97ef939c9fe3f8abf93e4adb654517476da7a66f`, with the corresponding pinned
lean4export and lean4checker. It compares goal types and referenced definitions,
restricts axioms to `propext`, `Classical.choice`, and `Quot.sound`, then rechecks
the exported proof dependency closure in a fresh environment using Lean's kernel.
This is a separate replay with the same kernel, not a different kernel implementation.
Rechecking this large proof closure can take much longer than a cached build;
the checker may remain quiet during that step.

The shared language, instance, encoding, and algorithm definitions are part of
the reviewed specification. Statements import them from the production library.
The release source hashes fix those files as well as the written propositions.
Comparator checks the formal claims; correspondence with the paper still requires
reading the definitions and [paper map](paper.md).

For Linux sandboxing, install Landrun from its official source and put it in PATH,
then run `python3 scripts/verify.py`. The explicit `--no-sandbox` option is for
local author checks on systems without Landrun; it must not be described as
sandboxed evaluation of adversarial source.

## Repeatable checks

```sh
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/verify.py
```

The audit checks the source inventory, import closure, absence of proof placeholders
and extra axioms, paper-source and numbered-statement hashes, specification targets,
and release-file hygiene. The verification command also checks all production
axiom dependencies and runs regression examples for exact algebraic inputs,
ordinary and degree-filtered identities and recognition, occurrence degrees, signed and zero
weights, repeated scopes, isolated variables, empty signatures, singleton domains, and the original-language row detector.
The GitHub Actions workflow repeats these checks on Linux with Landrun.
It also runs two official Comparator negative controls on the current
Appendix F.B.1 goal: replacing its type by `True`, and supplying its unchanged
type through an injected axiom. Each must fail with its specific mismatch
or illegal-axiom diagnostic; a failed build does not count as rejection.

To check that every source byte still matches the verified release receipt, run
`python3 scripts/audit.py --release`. Ordinary development checks validate the
current tree without rewriting that receipt or the frozen propositions.

Generated objects, checker exports, and logs stay under `.lake` and are excluded
from the release archive. `verification/release.json` records only the compact
results for the packaged sources.

## Read-only dependency reuse

For a local author checkout with existing pinned dependency caches, run:

```sh
python3 scripts/verify.py --no-sandbox --reuse-dependencies
```

This mode calls Lean directly and does not load a Lake workspace. Lake may
replace a dependency checkout while loading its configuration if a Git URL
has changed; it must therefore not be invoked against shared dependency
symlinks. The direct builder compares local source bytes with the existing
Lean build traces using the pinned toolchain's source hash, rebuilds changed
local modules and their dependants, and records subsequent SHA-256 signatures.
It writes only project build outputs. Official Comparator and lean4export
remain the pinned executables; a narrow build adapter handles Comparator's
local module build requests. The goal comparison, axiom policy, and fresh
kernel replay are unchanged. This is cached local verification, not a claim
of a clean dependency rebuild or Linux sandboxing.

## Current and historical records

The current manuscript is the Overleaf snapshot exported on 2026-11-06.
[paper.json](../verification/paper.json) records its source, PDF, exact statement
hashes, current numbers, and frozen goals. The source is byte-for-byte identical
to the downloaded snapshot. The PDF was compiled with pdfLaTeX in four passes;
all 68 pages were rendered for inspection, and all 48 statement numbers agree
with the emitted TeX labels. The source needed no formatting changes.

[release.json](../verification/release.json) records local prepublication checks
and the digest of this source tree. It does not assert an official Comparator
result. The GitHub Actions run for the exact published commit supplies the
complete build, axiom, regression, Comparator, kernel-replay, and negative-control
results. Local continuation output and negative-control logs remain under
`.lake/verification`; they are not source artifacts.

[original-release.json](../verification/original-release.json) preserves the
original prepared-package receipt, and
[arxiv-v1-release.json](../verification/arxiv-v1-release.json) preserves the
last v1 publication receipt. Those builds and 123-goal Comparator results
cover their historical source trees. They are not evidence for this snapshot.
The current targets use stable TeX-label identifiers and include four new
contracts for F.3.1, F.5.6, and the complete F.B.1 counterexample.

The Linux launcher preserves lean4export's `--` argument separator with the
pinned Landrun parser. It invokes the real Landrun binary with the same sandbox
permissions. Current GitHub Actions status must be read for the exact published
commit; a historical successful run does not validate later commits.

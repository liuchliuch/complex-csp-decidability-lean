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

`verification/Statements.lean` is the reviewable specification. Its propositions
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
The GitHub Actions workflow repeats these checks on Linux with Landrun; its
remote run is triggered when this repository is uploaded.

To check that every source byte still matches the verified release receipt, run
`python3 scripts/audit.py --release`. Ordinary development checks validate the
current tree without rewriting that receipt or the frozen propositions.

Generated objects, checker exports, and logs stay under `.lake` and are excluded
from the release archive. `verification/release.json` records only the compact
results for the packaged sources.

## Publication records

[original-release.json](../verification/original-release.json) preserves the
verification record from the prepared package. The current
[release.json](../verification/release.json) also identifies publication changes
and the exact current file digest. Its original build and Comparator results
refer to the unchanged mathematical inputs.

The Linux launcher preserves lean4export's `--` argument separator with the
pinned Landrun parser. It invokes the real Landrun binary with the same sandbox
permissions. This compatibility fix changes the launcher, rather than the
theorem statements or proofs.

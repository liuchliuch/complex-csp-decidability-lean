# Paper correspondence

The current target is the **STOC 2027 manuscript exported from Overleaf on
2026-11-06 at 14:23:17 UTC**, including both the short exposition and the embedded
full paper and appendices. Its [self-contained TeX](../paper/stoc2027-CSP.tex)
is preserved byte for byte; the [PDF](../paper/stoc2027-CSP.pdf) is compiled from
that source. The authors are Chenghua Liu and Boning Meng, and the paper is
[*From Block Orthogonality to Decidability in Complex-Weighted Counting CSP*](https://arxiv.org/abs/2608.14845).
The arXiv identifier is bibliographic context, not a claim that this Overleaf
snapshot is the published arXiv version.

The source SHA-256 is
`ee3205e9ae4390dab734730c0d5cbf3ae1f9dc8c69b803ac29db91c35204d62c`.
The export URL, timestamp, archive hash, PDF hash, and exact statement texts and
line hashes are in [verification/paper.json](../verification/paper.json).
There are **48 numbered items**: eight in the short paper, 39 in the full paper,
and one appendix remark. The 36 theorem, lemma, and corollary statements include
five short-paper restatements of full-paper results. Every proof statement and
the appendix counterexample have explicit frozen Comparator goals.

The short paper uses ordinary section numbers. The full paper uses the prefix
`F.`, and the counterexample is **Remark F.B.1**. These numbers were checked
against the labels emitted by pdfLaTeX. Goal identifiers use the stable TeX
labels rather than section numbers; for example,
`paper_thm_young_pinned_all_instance_pinned_iso_iff` corresponds to F.5.2.

## Current mathematical changes

**Theorem F.5.2 is the all-instance pinned isomorphism theorem.** Its premise
requires equality on every finite labelled instance, including repeated
constraints and repeated scope positions. The conclusion gives a domain
bijection preserving the indexed tables and matching each prescribed pin up to
twins. The proof includes twin-class multiplicities. The converse is proved as
well. [IsomorphismCompleteness.lean](../ComplexCSP/Instances/IsomorphismCompleteness.lean)
supplies the equivalence and the finite bijection checker used by recognition.
There is no simple-instance premise in that recognition chain.

**Remark F.B.1 uses the current explicit counterexample.** The unary profiles
are `(1, 2, 6)` and `(1, 3, 5)`, with the label pinned at the entry of weight one.
Both are positive and twin-free. Every simple instance has the same value:
a constrained hidden variable contributes nine, an isolated hidden variable
contributes three, and a constraint on the pin contributes one. No table
isomorphism exists because the value two appears only in the first profile.
The actual finite instance with two unary constraints on one hidden variable
has values **41 and 35**, respectively. The proof quantifies over actual finite
instances and identifies its simplicity predicate with the manuscript's
scope-permutation definition. The rational result and its complex-valued bridge
are both checked. The module name `Theorem52Counterexample` and a few production
theorem identifiers remain historical API names; their current paper mapping
is F.B.1, never the proved current F.5.2.

**Lemma F.3.1 now states the group extensions explicitly.** In addition to the
ambient row comparisons, [Paper.lean](../ComplexCSP/Paper.lean) exposes the
exponent, phase, and purified-value homomorphisms. It proves that the exponent
kernel is the torsion subgroup, that the phase map fixes torsion, and that the
purified map is injective and has modulus one exactly on torsion. Its separate
singleton-field bridge proves that phase values lie in the containing field
and have finite order. These are proved consequences of the legal generating
set, not additional assumptions about the conclusion.

**Lemma F.5.6 compares general indexed families.** The new
`ComplexCSP.Paper.indexed_family_comparison` bridge transfers the all-instance
checker from a retargeted language back to the original instance templates.
It applies to arbitrary finite indexed families over a common exact field.
Thus it also handles the paper's more restricted families with at most one
zero function per arity. Monomial comparison is a specialization; the
scalar-tag construction and its equality-preservation theorem remain checked
separately for the paper's presentation in terms of sets of functions.

The remaining proof changes reorganize equivalent mathematics. The degree
filter and restricted identity oracle move to F.10.1 and F.10.2. Intrinsic
purification tests move from old 4.1 to F.3.5; new numbered definitions cover
generating sets, certificates, and tensor realizations. The lower-level proofs
remain in place where their statements are unchanged.

## Representation and proof choices

Languages use a finite indexed signature with positive arities; duplicate
tables are allowed. An arity-preserving correspondence between finite sets is
represented by a common index type. Generated tables are presentation-backed
partial sums of products. The ordered `PaperGenerated` bridge aligns this
semantics with the manuscript's retained-variable family.

The constructive bounded power-sum argument chooses row detectors without
changing their mathematical specification. The full nondegenerate exponential
sum result F.8.3 is also proved using number-field and p-adic arguments;
Skolem--Mahler--Lech is not an added axiom. Explicit bridges specialize the
relational and phase results to the actual language in F.7.3, F.7.4, F.8.2, and
F.8.5. Fixed-language complexity results use actual bit-machine bounds and
charged reductions. See [the verification contract](verification.md) for exact
input promises and output representations.

[Statements.lean](../verification/Statements.lean) writes the propositions out
independently of their proofs. [Challenge.lean](../verification/Challenge.lean)
fixes those goals, and [Solution.lean](../verification/Solution.lean) proves them
from the production library. The checker does not regenerate the specification
from the solution. The source audit independently parses every numbered
statement from the current TeX and checks its label, kind, number, source span,
text, hash, and goal coverage.

## Current numbered items

Short-paper rows share the goals of their indicated full-paper statements.
Definition and procedure rows identify concrete encodings and algorithms;
they are not counted as additional theorem proofs. The machine-readable map
lists all declarations and goals, including supporting endpoints beyond the
principal source shown below.

| Item | Statement or definition | Principal correspondence |
| --- | --- | --- |
| 1.1 | Uniform decidability | [Same goals as F.1.1](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| 1.2 | Uniform decidability for degree-multiple CSP | [Same goals as F.1.2](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| 2.1 | Global Block Orthogonality | [Same definition as F.2.3](../ComplexCSP/Recognition/GlobalConditions.lean) |
| 2.2 | Type Partition and Mal'tsev polymorphism conditions | [Same definitions as F.2.4](../ComplexCSP/Structure/StructuralCollapse.lean) |
| 3.1 | Bounded external arity | [Same goals as F.3.4](../ComplexCSP/Structure/BoundedArity.lean) |
| 3.2 | Block Orthogonality certificate | [Same definition as F.4.1](../ComplexCSP/Recognition/Certificates.lean) |
| 4.1 | Universal identity test | [Same goals as F.5.8](../ComplexCSP/Recognition/UniformAlgebraicIdentity.lean) |
| 4.2 | Pinned isomorphism | [Same goals as F.5.2](../ComplexCSP/Instances/IsomorphismCompleteness.lean) |
| F.1.1 | Uniform decidability | [Proved](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| F.1.2 | Uniform decidability for degree-multiple CSP | [Proved](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| F.2.1 | Block-orthogonal function | [Definition](../ComplexCSP/Structure/BlockOrthogonality.lean) |
| F.2.2 | Generating set | [Definition](../ComplexCSP/Algebra/LegalPurificationChoices.lean) |
| F.2.3 | Global Block Orthogonality condition | [Definition](../ComplexCSP/Recognition/GlobalConditions.lean) |
| F.2.4 | Type Partition and Mal'tsev polymorphism conditions | [Definition](../ComplexCSP/Structure/StructuralCollapse.lean) |
| F.3.1 | Ambient invariance and purification group extensions | [Proved](../ComplexCSP/Paper.lean) |
| F.3.2 | Singleton purification suffices | [Proved](../ComplexCSP/Recognition/GlobalConditions.lean) |
| F.3.3 | External diagonal minors | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| F.3.4 | Bounded external arity | [Proved](../ComplexCSP/Structure/BoundedArity.lean) |
| F.3.5 | Intrinsic purification tests | [Proved](../ComplexCSP/Recognition/CertificatesPurificationBridge.lean) |
| F.4.1 | Block Orthogonality certificate | [Definition](../ComplexCSP/Recognition/Certificates.lean) |
| F.4.2 | Algebraic description of the BO locus | [Proved](../ComplexCSP/Recognition/CertificatesLegalTables.lean) |
| F.4.3 | The role of the working field | [Working-field scope](../ComplexCSP/Algebra/WorkingField.lean) |
| F.4.4 | Polynomial identities for the BO locus | [Proved](../ComplexCSP/Structure/PolynomialUnion.lean) |
| F.5.1 | Pinned realization of the generated family | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| F.5.2 | Pinned constraint-function isomorphism | [Proved](../ComplexCSP/Instances/IsomorphismCompleteness.lean) |
| F.5.3 | Tensor realization | [Definition](../ComplexCSP/Structure/TensorCharacters.lean) |
| F.5.4 | Tensor realization of monomial characters | [Proved](../ComplexCSP/Structure/TensorCharacters.lean) |
| F.5.5 | Common scalar tags | [Proved](../ComplexCSP/Algebra/ScalarTagsTyped.lean) |
| F.5.6 | Effective comparison of indexed families and characters | [Proved](../ComplexCSP/Paper.lean) |
| F.5.7 | Linear independence of monoid characters | [Proved](../ComplexCSP/Structure/CharacterIndependence.lean) |
| F.5.8 | Universal identity oracle | [Proved](../ComplexCSP/Recognition/UniformAlgebraicIdentity.lean) |
| F.6.1 | Global Block Orthogonality | [Executable procedure](../ComplexCSP/Recognition/GlobalProgram.lean) |
| F.6.2 | Exact decision of global BO | [Proved](../ComplexCSP/Recognition/GlobalProgram.lean) |
| F.7.1 | Simultaneous nonvanishing of power sums | [Proved](../ComplexCSP/Algebra/PowerSums.lean) |
| F.7.2 | Equality-free support realization | [Proved](../ComplexCSP/Structure/SupportRealization.lean) |
| F.7.3 | Singleton rectangularity | [Proved](../ComplexCSP/Recognition/GlobalConditions.lean) |
| F.7.4 | Finite-family support lemma | [Proved](../ComplexCSP/Structure/MaltsevRelations.lean) |
| F.7.5 | Common Mal'tsev polymorphism of generated supports | [Proved](../ComplexCSP/Recognition/GlobalConditions.lean) |
| F.8.1 | Generated entrywise powers | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| F.8.2 | Finite relative row phases | [Proved](../ComplexCSP/Structure/BlockRowPhases.lean) |
| F.8.3 | Nondegenerate exponential sums | [Proved](../ComplexCSP/Algebra/AlgebraicPowerSumZeros.lean) |
| F.8.4 | Row-equivalence realization | [Proved](../ComplexCSP/Structure/RowEquivalenceRealization.lean) |
| F.8.5 | Support preservation extends to all row relations | [Proved](../ComplexCSP/Structure/RowEquivalenceRealization.lean) |
| F.9.1 | Row equivalence forces Type Partition | [Proved](../ComplexCSP/Structure/RowTypes.lean) |
| F.9.2 | Structural collapse | [Proved](../ComplexCSP/Structure/StructuralCollapse.lean) |
| F.10.1 | Degree-filtered character comparison | [Proved](../ComplexCSP/Recognition/DegreeFilter.lean) |
| F.10.2 | Universal identity oracle for the degree-restricted family | [Proved](../ComplexCSP/Recognition/UniformAlgebraicIdentityDegree.lean) |
| F.B.1 | Simple-instance indistinguishability need not imply isomorphism | [Simple-instance counterexample; 41 vs 35](../ComplexCSP/Algebra/Theorem52Counterexample.lean) |

## Historical v1 material

The [original arXiv v1 TeX](../paper/source/cai-chen-complex-csp-decidability.tex)
and bibliography remain unchanged. Its old statement inventory is preserved in
[arxiv-v1-paper.json](../verification/arxiv-v1-paper.json), and
[theorem52-correction.patch](../paper/theorem52-correction.patch) records the
separate correction made against that version. That patch is historical;
the current manuscript already contains the all-instance theorem and its proof.
The old explicit profiles were `(1, 2, 5)` and `(1, 3, 4)`, with doubled values
30 and 26; they are not the counterexample stated in the current appendix.

The original package and publication receipts are preserved in
[original-release.json](../verification/original-release.json) and
[arxiv-v1-release.json](../verification/arxiv-v1-release.json). Their results
refer to those older source trees and do not establish verification of this
snapshot. The current [local prepublication receipt](../verification/release.json) and
[verification notes](verification.md) identify the new checks and explain how
to obtain the exact-commit GitHub Actions results.

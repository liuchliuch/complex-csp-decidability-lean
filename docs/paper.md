# Paper correspondence

The source is the arXiv **v1** manuscript by Chenghua Liu and Boning Meng,
[*From Block Orthogonality to Decidability in Complex-Weighted Counting CSP*](https://arxiv.org/abs/2608.14845v1).
The archived TeX and bibliography were checked against a fresh download of that
version and remain unchanged. There are 36 numbered items: 31 theorem, lemma,
and corollary statements, three definitions, one remark, and one procedure.

## Theorem 5.2 correction

With the printed definition of a simple instance, the implication in Theorem 5.2
is false. The unary profiles `(1, 2, 5)` and `(1, 3, 4)` on a three-element
domain, pinned at the entry of weight one, are positive and twin-free. Every
simple instance has the same value for the two profiles: a constrained hidden
variable contributes eight, an isolated hidden variable contributes three,
and a constrained pin contributes one. No bijection preserves the tables,
since the weight two occurs only in the first profile.

The counterexample quantifies over actual finite instances and proves that its
simplicity predicate is the printed scope-permutation condition. A companion
bridge interprets the profiles directly in the complex-valued model.
Repeating the unary constraint twice gives 30 and 26, so the premise changes
when all finite instances are allowed.

The formalized replacement assumes equality on **all finite labelled instances**
and proves the full isomorphism-and-pin-twins equivalence, including twin
multiplicities. The monomial comparison and recognition chain use this proved
replacement. The separate [manuscript correction](../paper/theorem52-correction.patch)
changes the premise, corrects the attribution, supplies the independent proof
argument, and updates the callsite in Lemma 5.5. The original Theorem 5.2 is
recorded as refuted, rather than counted as a proved printed statement.

## Representation and proof choices

Languages use a finite indexed signature with positive arities; duplicate tables
are allowed. The monomial comparator works directly with these indexed families,
while a companion theorem verifies the paper's scalar-tagged comparison.
Generated tables are presentation-backed partial sums of products. An ordered
`PaperGenerated` bridge aligns that semantics with the manuscript's family.

The structural proof uses a constructive bounded power-sum argument to choose
the row detector. The full numbered Lemma 8.3 is also proved separately using
number-field and p-adic arguments; Skolem--Mahler--Lech is not an added axiom.
Explicit bridge lemmas specialize the relational and phase results to the actual
language for 7.3, 7.4, 8.2, and 8.5. The fixed-language complexity theorems use
actual bit-machine bounds and charged reductions. See [the mathematical
contract](verification.md) for input promises and exact output conventions.

## Numbered items

Each row links to the production source of its principal endpoint.
[The machine-readable map](../verification/paper.json) preserves every exact
printed statement and its source-line hash, lists the associated declarations,
and identifies the frozen Comparator goals. All proof statements have goals;
5.2 has counterexample and corrected-theorem goals.

| Item | Printed title | Correspondence |
| --- | --- | --- |
| 1.1 | Uniform decidability | [Proved with corrected 5.2](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| 1.2 | Uniform recognition for $\#\mathrm{CSP}^{\delta}$ | [Proved with corrected 5.2](../ComplexCSP/Recognition/UniformAlgebraicEncoded.lean) |
| 2.1 | Block-orthogonal function | [Definition](../ComplexCSP/Structure/BlockOrthogonality.lean) |
| 2.2 | Global Block Orthogonality | [Definition](../ComplexCSP/Recognition/GlobalConditions.lean) |
| 2.3 | Type Partition and the common Mal'tsev condition | [Definition](../ComplexCSP/Structure/StructuralCollapse.lean) |
| 3.1 | Ambient invariance of purification | [Proved](../ComplexCSP/Algebra/AmbientInvarianceClauses.lean) |
| 3.2 | Singleton purification suffices | [Proved](../ComplexCSP/Recognition/GlobalConditions.lean) |
| 3.3 | External diagonal minors | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| 3.4 | Bounded external arity | [Proved](../ComplexCSP/Structure/BoundedArity.lean) |
| 4.1 | Intrinsic purification tests | [Proved](../ComplexCSP/Recognition/CertificatesPurificationBridge.lean) |
| 4.2 | Algebraic description of the BO locus | [Proved](../ComplexCSP/Recognition/CertificatesLegalTables.lean) |
| 4.3 | The role of the working field | [Working-field scope](../ComplexCSP/Algebra/WorkingField.lean) |
| 4.4 | Polynomial identities for the BO locus | [Proved](../ComplexCSP/Structure/PolynomialUnion.lean) |
| 5.1 | Pinned realization of the generated family | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| 5.2 | Pinned constraint-function isomorphism | [Original refuted; all-instance replacement proved](../ComplexCSP/Structure/PaperBridge.lean) |
| 5.3 | Tensor realization of monomial characters | [Proved](../ComplexCSP/Structure/TensorCharacters.lean) |
| 5.4 | Common scalar tags | [Proved](../ComplexCSP/Algebra/ScalarTagsTyped.lean) |
| 5.5 | Effective comparison of monomial characters | [Proved with corrected 5.2](../ComplexCSP/Recognition/CharacterComparison.lean) |
| 5.6 | Linear independence of monoid characters | [Proved](../ComplexCSP/Structure/CharacterIndependence.lean) |
| 5.7 | Universal identity oracle | [Proved with corrected 5.2](../ComplexCSP/Recognition/UniformAlgebraicIdentity.lean) |
| 5.8 | Degree-filtered comparison of monomial characters | [Proved with corrected 5.2](../ComplexCSP/Recognition/DegreeFilter.lean) |
| 5.9 | Degree-multiple universal identity oracle | [Proved with corrected 5.2](../ComplexCSP/Recognition/UniformAlgebraicIdentityDegree.lean) |
| 6.1 | Global Block Orthogonality | [Executable procedure](../ComplexCSP/Recognition/GlobalProgram.lean) |
| 6.2 | Exact decision of global BO | [Proved with corrected 5.2](../ComplexCSP/Recognition/GlobalProgram.lean) |
| 7.1 | Simultaneous nonvanishing of power sums | [Proved](../ComplexCSP/Algebra/PowerSums.lean) |
| 7.2 | Equality-free support realization | [Proved](../ComplexCSP/Structure/SupportRealization.lean) |
| 7.3 | Singleton rectangularity | [Proved](../ComplexCSP/Structure/PaperBridge.lean) |
| 7.4 | Finite-family support lemma | [Proved](../ComplexCSP/Structure/PaperBridge.lean) |
| 7.5 | Common Mal'tsev operation for generated supports | [Proved](../ComplexCSP/Recognition/GlobalConditions.lean) |
| 8.1 | Generated entrywise powers | [Proved](../ComplexCSP/Instances/OrderedInstances.lean) |
| 8.2 | Finite relative row phases | [Proved](../ComplexCSP/Structure/PaperBridge.lean) |
| 8.3 | Nondegenerate exponential sums | [Proved](../ComplexCSP/Algebra/AlgebraicPowerSumZeros.lean) |
| 8.4 | Row-equivalence realization | [Proved](../ComplexCSP/Structure/RowEquivalenceRealization.lean) |
| 8.5 | Support preservation extends to all row relations | [Proved](../ComplexCSP/Structure/PaperBridge.lean) |
| 9.1 | Row equivalence forces Type Partition | [Proved](../ComplexCSP/Structure/RowTypes.lean) |
| 9.2 | Structural collapse | [Proved](../ComplexCSP/Structure/StructuralCollapse.lean) |

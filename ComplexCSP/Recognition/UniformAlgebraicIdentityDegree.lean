import ComplexCSP.Recognition.UniformAlgebraicIdentity
import ComplexCSP.Algebra.UniformCyclotomicExtensionRuntime

/-!
# Exact recognition: uniform Theorem 5.9 frontend

The primitive filter root and its containing field are computed by the actual
validated cyclotomic search. Both coefficient conversion and genuine
conjugation are transported to that extension before the degree identity test.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField

variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι] [Encodable ι]
  {n k : ℕ}

/-- Full finite-data degree-multiple identity algorithm with no supplied root,
extension, shared coefficient field, or conjugation oracle. -/
def uniformAlgebraicDegreeIdentityTest (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (δ : ℕ) (hδ : 0 < δ) (coords : Fin n → PinnedCoordinate (Fin k) D) : Bool := by
  let input := identityDescriptions L P
  let hinput := identityDescriptions_valid L hL P hP
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  let b := identityPairedConjugate input hinput
  let hb := identityPairedConjugate_valid input hinput
  let E := findCyclotomicCandidate C.tail hv δ hδ
  have hE : E.test C.tail δ = true := findCyclotomicCandidate_spec C.tail hv δ hδ
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  letI : Fact (Element.Valid E.dimension E.relation) := ⟨candidate_valid C.tail δ E hE⟩
  let ψ := candidateEmbedding C.tail hv δ hδ E hE
  let eb := extensionConjugateCoordinates E.relation E.oldGenerator E.root b E.d E.m
  let heb := validatedCandidate_conjugation C.tail hv δ hδ E hE b hb
  letI := Element.starRing eb heb
  exact degreeProgramIdentityTest ((identityCandidateLanguage L P C).mapValues ψ) δ
    (⟨E.root⟩ : Element E.dimension E.relation) coords
    (PolynomialPrograms.mapCoefficients ψ (identityCandidateProgram L P C))

/-- Exact all-instance degree-multiple correctness, including repeated variable
occurrences, hidden variables of degree zero, and nonhomogeneous polynomials. -/
theorem uniformAlgebraicDegreeIdentityTest_correct (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (δ : ℕ) (hδ : 0 < δ) (coords : Fin n → PinnedCoordinate (Fin k) D)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a))
    (coefficients : Fin P.length → ℂ)
    (hc : ∀ j, (P.get j).coefficient.Represents (coefficients j)) :
    uniformAlgebraicDegreeIdentityTest L hL P hP δ hδ coords = true ↔
      ∀ h : ℕ, ∀ I : Instance (realizedAlgebraicLanguage L z) (Fin k) (Fin h), I.DegreeDivisible δ →
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) (programWithCoefficients P coefficients) = 0 := by
  let input := identityDescriptions L P
  let hinput := identityDescriptions_valid L hL P hP
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  let b := identityPairedConjugate input hinput
  let hb := identityPairedConjugate_valid input hinput
  let E := findCyclotomicCandidate C.tail hv δ hδ
  have hE : E.test C.tail δ = true := findCyclotomicCandidate_spec C.tail hv δ hδ
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  letI : Fact (Element.Valid E.dimension E.relation) := ⟨candidate_valid C.tail δ E hE⟩
  let ψ := candidateEmbedding C.tail hv δ hδ E hE
  let eb := extensionConjugateCoordinates E.relation E.oldGenerator E.root b E.d E.m
  let heb := validatedCandidate_conjugation C.tail hv δ hδ E hE b hb
  letI := Element.starRing eb heb
  let values := identityInputValues L z P coefficients
  have hvalues := identityInputValues_represents L z hz P coefficients hc
  obtain ⟨Φ, hΦ, he⟩ := C.sound (pairedDescriptions input) (pairedInputs values)
    (pairedDescriptions_represents input values hvalues) (identityPairedCandidate_accepted input hinput)
  have hΦb : interpret (Φ (Element.generator (c := EffectiveRoots.coefficientRelation C.tail))) b =
      star (Φ Element.generator) :=
    initialConjugateCoordinates_correct C.coordinates C.expression (pairedInputSwap (n := IdentityInputSize L P))
      (pairedInputs values) (pairedInputs_swap values) Φ hΦ he
  obtain ⟨Ψ, hΨ⟩ := exists_complex_embedding_extension ψ Φ
  have hΨold : Ψ (⟨E.oldGenerator⟩ : Element E.dimension E.relation) =
      Φ (Element.generator (c := EffectiveRoots.coefficientRelation C.tail)) := by
    rw [← candidateEmbedding_generator C.tail hv δ hδ E hE]
    exact RingHom.congr_fun hΨ Element.generator
  have heq := acceptedCandidate_equations C.tail δ hδ E hE
  have hroot : IsPrimitiveRoot (⟨E.root⟩ : Element E.dimension E.relation) δ := heq.2.1
  have hΨb : interpret (Ψ (Element.generator (c := E.relation))) eb = star (Ψ Element.generator) := by
    exact extensionConjugateCoordinates_correct (Element.powerBasis (c := E.relation))
      E.relation E.oldGenerator E.root Element.generator_relation b E.d E.m
      (by simpa only [Element.powerBasis_gen, Element.interpret_generator] using heq.2.2)
      δ hδ (by simpa only [Element.powerBasis_gen, Element.interpret_generator] using hroot) Ψ
      (by simpa only [Element.powerBasis_gen, Element.interpret_generator, hΨold] using hΦb)
  have hstar : ∀ x, Ψ (star x) = star (Ψ x) := map_computed_coordinate_star E.relation eb heb Ψ hΨb
  have hlang : ((identityCandidateLanguage L P C).mapValues ψ).mapValues Ψ =
      realizedAlgebraicLanguage L z := by
    have hh : (fun i a => Ψ (ψ (C.coordinateValue (identityEntryIndex L P ⟨i,a⟩)))) = z := by
      funext i a
      have hh := RingHom.congr_fun hΨ (C.coordinateValue (identityEntryIndex L P ⟨i,a⟩))
      exact hh.trans ((hΦ (identityEntryIndex L P ⟨i,a⟩)).trans
        (identityInputValues_entry L z P coefficients i a))
    exact congrArg (Language.mk L.arity L.arity_pos) hh
  have hprogram : PolynomialPrograms.mapCoefficients Ψ
      (PolynomialPrograms.mapCoefficients ψ (identityCandidateProgram L P C)) =
        programWithCoefficients P coefficients := by
    rw [identityCandidateProgram, programWithCoefficients_map, programWithCoefficients_map]
    congr 1
    funext j
    have hh := RingHom.congr_fun hΨ (C.coordinateValue (identityCoefficientIndex L P j))
    exact hh.trans ((hΦ (identityCoefficientIndex L P j)).trans
      (identityInputValues_coefficient L z P coefficients j))
  have horacle := (degreeProgramIdentityTest_correct_instances
    ((identityCandidateLanguage L P C).mapValues ψ) hδ hroot coords
    (PolynomialPrograms.mapCoefficients ψ (identityCandidateProgram L P C))).trans
      (degree_instance_identity_map_iff ((identityCandidateLanguage L P C).mapValues ψ) Ψ hstar δ coords
        (PolynomialPrograms.mapCoefficients ψ (identityCandidateProgram L P C)))
  rw [hlang, hprogram] at horacle
  exact horacle

/-- Every rejection has a genuine finite degree-certified counterexample. -/
theorem uniformAlgebraicDegreeIdentityTest_rejects_iff (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (δ : ℕ) (hδ : 0 < δ) (coords : Fin n → PinnedCoordinate (Fin k) D)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a))
    (coefficients : Fin P.length → ℂ)
    (hc : ∀ j, (P.get j).coefficient.Represents (coefficients j)) :
    uniformAlgebraicDegreeIdentityTest L hL P hP δ hδ coords = false ↔
      ∃ h : ℕ, ∃ I : Instance (realizedAlgebraicLanguage L z) (Fin k) (Fin h),
        I.DegreeDivisible δ ∧
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) (programWithCoefficients P coefficients) ≠ 0 := by
  classical
  rw [← Bool.not_eq_true,
    uniformAlgebraicDegreeIdentityTest_correct L hL P hP δ hδ coords z hz coefficients hc]
  push_neg
  rfl

end ComplexCSP.Recognition

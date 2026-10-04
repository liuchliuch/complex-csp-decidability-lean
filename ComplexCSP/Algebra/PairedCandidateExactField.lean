import ComplexCSP.Recognition.UniformAlgebraicIdentityInput
import ComplexCSP.Algebra.EffectiveRootsExactExponent
import Mathlib.Algebra.Group.Units.Equiv

/-! # The paired runtime field is exactly the source working field

The candidate's checked coordinate equations and stored primitive expression
prove both field containments. This file is proof-only: no semantic field or
embedding is supplied to the runtime search.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField IntermediateField
open scoped BigOperators NumberField

/-- Every runtime coordinate is a rational polynomial in its own generator,
so the image under any genuine embedding is exactly the simple field. -/
theorem coordinate_fieldRange_eq_adjoin {n : ℕ} (c : CoeffVector n)
    [Fact (Element.Valid n c)] (σ : Element n c →+* ℂ) :
    σ.fieldRange = (ℚ⟮σ Element.generator⟯).toSubfield := by
  have h : σ.toRatAlgHom.fieldRange = ℚ⟮σ Element.generator⟯ := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      have he : σ a = interpret (σ Element.generator) a.coeff := by
        rw [← Element.map_interpret_complex, Element.interpret_generator]
      change σ a ∈ ℚ⟮σ Element.generator⟯
      rw [he]
      apply (ℚ⟮σ Element.generator⟯).sum_mem
      intro i _
      exact mul_mem ((ℚ⟮σ Element.generator⟯).algebraMap_mem _)
        (pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) _)
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      exact ⟨Element.generator, rfl⟩
  exact congrArg IntermediateField.toSubfield h

/-- Any accepted candidate with its correct coordinate realization generates
exactly the field of the supplied input vector. -/
theorem acceptedCandidate_fieldRange {m : ℕ} (C : InitialInputCandidate m)
    (input : Fin m → AlgebraicInput) (h : C.test input = true)
    (x : Fin m → ℂ) :
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (InitialInputCandidate.test_valid h)⟩
    ∀ σ : C.FieldType →+* ℂ, (∀ i, σ (C.coordinateValue i) = x i) →
      σ.fieldRange = (initialInputField x).toSubfield := by
  let hv := InitialInputCandidate.test_valid h
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  intro σ hx
  have he := ((C.test_spec input hv).mp h).2.2
  have he' := congrArg σ he
  rw [PolynomialPrograms.map_interpret] at he'
  have hrat : σ.comp (algebraMap ℚ C.FieldType) = algebraMap ℚ ℂ := by ext; simp
  rw [hrat] at he'
  have hfun : (fun i => σ (C.coordinateValue i)) = x := funext hx
  rw [hfun] at he'
  have hc (i) : interpret (σ Element.generator) (C.coordinates i) = x i := by
    rw [← C.map_coordinateValue hv σ i]
    exact hx i
  rw [coordinate_fieldRange_eq_adjoin, exact_field_of_coordinate_and_program_witnesses
    x (σ Element.generator) C.coordinates hc C.expression he']

/-- Torsion cardinality, hence the exact displayed exponent, is invariant
under a genuine coefficient-field isomorphism. -/
theorem fieldExponent_eq_of_ringEquiv {K R : Type*} [Field K] [Field R]
    [NumberField K] [NumberField R] (e : K ≃+* R) :
    RowDetector.fieldExponent K = RowDetector.fieldExponent R := by
  let eu := Units.mapEquiv (NumberField.RingOfIntegers.mapRingEquiv e).toMulEquiv
  have hmem (u : (𝓞 K)ˣ) : u ∈ NumberField.Units.torsion K ↔
      eu u ∈ NumberField.Units.torsion R := by
    simp only [NumberField.Units.torsion, CommGroup.mem_torsion]
    exact eu.injective.isOfFinOrder_iff.symm
  let et : NumberField.Units.torsion K ≃ NumberField.Units.torsion R :=
    eu.toEquiv.subtypeEquiv hmem
  have hc := Fintype.card_congr et
  simp only [RowDetector.fieldExponent, NumberField.Units.torsionOrder, hc]

section LanguageInput
variable {D ι : Type} [Fintype D] [Encodable D] [Fintype ι] [Encodable ι]

/-- The actual complex entry vector in exactly the runtime description order. -/
def languageEntryValues (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    Fin (Fintype.card (AlgebraicEntryIndex L)) → ℂ := fun k =>
  let x := (algebraicEntryNumbering L).symm k
  z x.1 x.2

/-- Pairing the entry vector introduces exactly the source entries and their
conjugates, and no independent polynomial coefficients. -/
theorem pairedLanguageValues_range (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    Set.range (pairedInputs (languageEntryValues L z)) =
      (realizedAlgebraicLanguage L z).conjugateValues := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      refine ⟨((algebraicEntryNumbering L).symm j, false), ?_⟩
      simp only [pairedInputs_left, languageEntryValues,
        Bool.false_eq_true, if_false, realizedAlgebraicLanguage]
    | inr j =>
      refine ⟨((algebraicEntryNumbering L).symm j, true), ?_⟩
      simp only [pairedInputs_right, languageEntryValues,
        if_true, realizedAlgebraicLanguage]
  · rintro ⟨⟨⟨i,a⟩, b⟩, rfl⟩
    cases b with
    | false =>
      refine ⟨finSumFinEquiv (Sum.inl (algebraicEntryNumbering L ⟨i,a⟩)), ?_⟩
      simp only [pairedInputs_left, languageEntryValues,
        Bool.false_eq_true, if_false, realizedAlgebraicLanguage]
      exact congrArg (fun p : AlgebraicEntryIndex L => z p.1 p.2)
        ((algebraicEntryNumbering L).symm_apply_apply ⟨i,a⟩)
    | true =>
      refine ⟨finSumFinEquiv (Sum.inr (algebraicEntryNumbering L ⟨i,a⟩)), ?_⟩
      simp only [pairedInputs_right, languageEntryValues,
        if_true, realizedAlgebraicLanguage]
      exact congrArg (fun p : AlgebraicEntryIndex L => star (z p.1 p.2))
        ((algebraicEntryNumbering L).symm_apply_apply ⟨i,a⟩)

theorem pairedLanguageValues_field (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    initialInputField (pairedInputs (languageEntryValues L z)) =
      (realizedAlgebraicLanguage L z).workingField := by
  unfold initialInputField Language.workingField
  rw [pairedLanguageValues_range]

/-- Any coordinate-compatible realization of the actually searched paired
candidate has exactly the original source working-field image. -/
theorem identityPairedCandidate_fieldRange (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    let input := algebraicDescriptions L
    let hinput := algebraicDescriptions_valid L hL
    let C := identityPairedCandidate input hinput
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
    ∀ σ : C.FieldType →+* ℂ,
      (∀ i, σ (C.coordinateValue i) = pairedInputs (languageEntryValues L z) i) →
      σ.fieldRange = (realizedAlgebraicLanguage L z).workingField.toSubfield := by
  intro input hinput C
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  intro σ hσ
  rw [← pairedLanguageValues_field]
  exact acceptedCandidate_fieldRange C (pairedDescriptions input)
    (identityPairedCandidate_accepted input hinput) _ σ hσ

/-- The sound realization theorem with exact working-field equality included.
The runtime arguments remain only the raw algebraic descriptions. -/
theorem identityPairedCandidate_realization_exactField
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    let input := algebraicDescriptions L
    let hinput := algebraicDescriptions_valid L hL
    let C := identityPairedCandidate input hinput
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
    letI := Element.starRing (identityPairedConjugate input hinput)
      (identityPairedConjugate_valid input hinput)
    ∃ σ : C.FieldType →+* ℂ,
      (∀ i, σ (C.coordinateValue i) = pairedInputs (languageEntryValues L z) i) ∧
      (∀ x, σ (star x) = star (σ x)) ∧
      σ.fieldRange = (realizedAlgebraicLanguage L z).workingField.toSubfield := by
  intro input hinput C
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  letI := Element.starRing (identityPairedConjugate input hinput)
    (identityPairedConjugate_valid input hinput)
  obtain ⟨σ, hσ, hstar⟩ := identityPairedCandidate_realization input hinput
    (languageEntryValues L z) (fun k => hz _ _)
  exact ⟨σ, hσ, hstar, identityPairedCandidate_fieldRange L hL z σ hσ⟩

/-- The runtime carrier is genuinely isomorphic to the precise source working
field, with the isomorphism induced by its sound complex realization. -/
noncomputable def identityPairedCandidate_workingFieldEquiv
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    let input := algebraicDescriptions L
    let hinput := algebraicDescriptions_valid L hL
    let C := identityPairedCandidate input hinput
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
    ∀ σ : C.FieldType →+* ℂ,
      (∀ i, σ (C.coordinateValue i) = pairedInputs (languageEntryValues L z) i) →
      C.FieldType ≃+* (realizedAlgebraicLanguage L z).workingField := by
  intro input hinput C
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  intro σ hσ
  exact σ.rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr (identityPairedCandidate_fieldRange L hL z σ hσ))

/-- The exponent computed from the actual paired candidate is exactly Kμ for
the original source working field. Only raw-description validity and the
represented values appear as hypotheses; no containing-field choice remains. -/
theorem identityPairedCandidate_rootExponent_eq
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    let input := algebraicDescriptions L
    let hinput := algebraicDescriptions_valid L hL
    let C := identityPairedCandidate input hinput
    letI := (realizedAlgebraicLanguage L z).workingField_numberField
      (fun i a => (hz i a).isAlgebraic)
    EffectiveRoots.rootExponentFromCoefficients C.degree C.tail =
      RowDetector.fieldExponent (realizedAlgebraicLanguage L z).workingField := by
  intro input hinput C
  letI := (realizedAlgebraicLanguage L z).workingField_numberField
    (fun i a => (hz i a).isAlgebraic)
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  obtain ⟨σ, hσ, _⟩ := identityPairedCandidate_realization input hinput
    (languageEntryValues L z) (fun k => hz _ _)
  calc
    _ = RowDetector.fieldExponent C.FieldType :=
      EffectiveRoots.checkedRootExponent_eq_fieldExponent C.tail
        (identityPairedCandidate_valid input hinput)
    _ = _ := fieldExponent_eq_of_ringEquiv
      (identityPairedCandidate_workingFieldEquiv L hL z σ hσ)

end LanguageInput
end ComplexCSP.Recognition

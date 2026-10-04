import ComplexCSP.Algebra.InitialPrimitiveCoordinateRuntime
import ComplexCSP.Algebra.InitialInputSearch
import ComplexCSP.Algebra.AlgebraicInputConjugate
import ComplexCSP.Recognition.UniformAlgebraicGlobal

/-!
# Exact recognition: one exact field for language entries and all polynomial coefficients

Independent coefficient descriptions are included before pairing with conjugates.
The primitive expression computes the initial conjugation; no field or star
oracle is supplied.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField

 theorem pairedDescriptions_valid {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : ∀ i, (pairedDescriptions input i).Valid := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => simpa only [pairedDescriptions, Equiv.symm_apply_apply, Sum.elim_inl] using hinput j
  | inr j =>
    obtain ⟨z, hz⟩ := hinput j
    exact ⟨star z, by simpa only [pairedDescriptions, Equiv.symm_apply_apply, Sum.elim_inr]
      using hz.conjugate⟩

/-- Actual initial conversion on a finite vector and its conjugate descriptions. -/
def identityPairedCandidate {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : InitialInputCandidate (m + m) :=
  findInitialInputCandidate (pairedDescriptions input) (pairedDescriptions_valid input hinput)

 theorem identityPairedCandidate_accepted {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) :
    (identityPairedCandidate input hinput).test (pairedDescriptions input) = true :=
  findInitialInputCandidate_spec _ _

 theorem identityPairedCandidate_valid {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : validTail (identityPairedCandidate input hinput).tail = true :=
  InitialInputCandidate.test_valid (identityPairedCandidate_accepted input hinput)

/-- Executable conjugate-generator vector derived from the stored primitive expression. -/
def identityPairedConjugate {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : CoeffVector (identityPairedCandidate input hinput).degree := by
  let C := identityPairedCandidate input hinput
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  exact initialConjugateCoordinates (relation := EffectiveRoots.coefficientRelation C.tail)
    C.coordinates C.expression (pairedInputSwap (n := m))

 theorem identityPairedConjugate_valid {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) :
    Element.StarValid (identityPairedCandidate input hinput).degree
      (EffectiveRoots.coefficientRelation (identityPairedCandidate input hinput).tail)
      (identityPairedConjugate input hinput) := by
  choose z hz using (fun i => hinput i)
  let C := identityPairedCandidate input hinput
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  obtain ⟨Φ, hΦ, he⟩ := C.sound (pairedDescriptions input) (pairedInputs z)
    (pairedDescriptions_represents input z hz) (identityPairedCandidate_accepted input hinput)
  exact initialConjugateCoordinates_starValid C.coordinates C.expression (pairedInputSwap (n := m))
    (pairedInputs z) (pairedInputs_swap z) Φ hΦ he

/-- The computed star operation agrees with every compatible specified complex realization. -/
theorem map_computed_coordinate_star {n : ℕ} (c b : CoeffVector n) [Fact (Element.Valid n c)]
    (hb : Element.StarValid n c b) (Φ : Element n c →+* ℂ)
    (hΦb : interpret (Φ (Element.generator (c := c))) b = star (Φ Element.generator)) :
    letI := Element.starRing b hb
    ∀ x : Element n c, Φ (star x) = star (Φ x) := by
  letI := Element.starRing b hb
  intro x
  have h := Element.conjugation_value (coordinateFieldModel n c) Φ b hΦb x
  simpa only [coordinateFieldModel, Element.Model.value, Element.interpret_generator] using h

/-- The converted field realizes the paired entries with genuine conjugation. -/
theorem identityPairedCandidate_realization {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) (z : Fin m → ℂ)
    (hz : ∀ i, (input i).Represents (z i)) :
    let C := identityPairedCandidate input hinput
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
    letI := Element.starRing (identityPairedConjugate input hinput)
      (identityPairedConjugate_valid input hinput)
    ∃ Φ : C.FieldType →+* ℂ,
      (∀ i, Φ (C.coordinateValue i) = pairedInputs z i) ∧
      (∀ x, Φ (star x) = star (Φ x)) := by
  let C := identityPairedCandidate input hinput
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  letI := Element.starRing (identityPairedConjugate input hinput)
    (identityPairedConjugate_valid input hinput)
  obtain ⟨Φ, hΦ, he⟩ := C.sound (pairedDescriptions input) (pairedInputs z)
    (pairedDescriptions_represents input z hz) (identityPairedCandidate_accepted input hinput)
  refine ⟨Φ, hΦ, map_computed_coordinate_star _ _ _ Φ ?_⟩
  exact initialConjugateCoordinates_correct C.coordinates C.expression (pairedInputSwap (n := m))
    (pairedInputs z) (pairedInputs_swap z) Φ hΦ he

section CombinedInput
variable {D ι : Type} [Fintype D] [Encodable D] [Fintype ι] [Encodable ι]
  {n : ℕ}

/-- Every polynomial coefficient is included, even if outside the original language field. -/
def identityDescriptions (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) :
    Fin (Fintype.card (AlgebraicEntryIndex L) + P.length) → AlgebraicInput := fun i =>
  Sum.elim (algebraicDescriptions L) (fun j : Fin P.length => (P.get j).coefficient)
    (finSumFinEquiv.symm i)

 theorem identityDescriptions_valid (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid) :
    ∀ i, (identityDescriptions L P i).Valid := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => simpa only [identityDescriptions, Equiv.symm_apply_apply, Sum.elim_inl]
      using algebraicDescriptions_valid L hL j
  | inr j => simpa only [identityDescriptions, Equiv.symm_apply_apply, Sum.elim_inr] using hP j

/-- Preserve the sparse syntax while assigning each occurrence its own coefficient value. -/
def programWithCoefficients {K : Type} (P : PolynomialPrograms.Program AlgebraicInput n)
    (c : Fin P.length → K) : PolynomialPrograms.Program K n :=
  List.ofFn (fun j => ⟨c j, (P.get j).exponent⟩)

end CombinedInput
end ComplexCSP.Recognition

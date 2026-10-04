import ComplexCSP.Recognition.UniformAlgebraicIdentityInput
import ComplexCSP.Recognition.UniformAlgebraicIdentityTransport

/-!
# Exact recognition: uniform Theorem 5.7 frontend for arbitrary algebraic coefficients

Both language entries and every polynomial coefficient are separate standard
algebraic-number descriptions. Direct and conjugate variables are independent;
no homogeneity, nonzero coefficient, or shared input-field restriction is used.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField

variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι] [Encodable ι]
  {n k : ℕ}

abbrev IdentityInputSize (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) := Fintype.card (AlgebraicEntryIndex L) + P.length

abbrev IdentityInputCandidate (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) :=
  InitialInputCandidate (IdentityInputSize L P + IdentityInputSize L P)

/-- The original half of a paired input vector. -/
def identityOriginalIndex {m : ℕ} (i : Fin m) : Fin (m+m) := finSumFinEquiv (Sum.inl i)

def identityEntryIndex (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) (i : AlgebraicEntryIndex L) :
    Fin (IdentityInputSize L P + IdentityInputSize L P) :=
  identityOriginalIndex (finSumFinEquiv (Sum.inl (algebraicEntryNumbering L i)))

def identityCoefficientIndex (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) (i : Fin P.length) :
    Fin (IdentityInputSize L P + IdentityInputSize L P) :=
  identityOriginalIndex (finSumFinEquiv (Sum.inr i))

/-- The actual converted tables retain the exact input signature and scopes. -/
def identityCandidateLanguage (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) (C : IdentityInputCandidate L P) :
    Language D C.FieldType ι :=
  ⟨L.arity, L.arity_pos, fun i a => C.coordinateValue (identityEntryIndex L P ⟨i,a⟩)⟩

/-- Each coefficient occurrence is converted in the same field as the table entries. -/
def identityCandidateProgram (L : Language D AlgebraicInput ι)
    (P : PolynomialPrograms.Program AlgebraicInput n) (C : IdentityInputCandidate L P) :
    PolynomialPrograms.Program C.FieldType n :=
  programWithCoefficients P (fun j => C.coordinateValue (identityCoefficientIndex L P j))

/-- The semantic finite vector paired with the combined descriptions. -/
def identityInputValues (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) (P : PolynomialPrograms.Program AlgebraicInput n)
    (coefficients : Fin P.length → ℂ) : Fin (IdentityInputSize L P) → ℂ := fun j =>
  Sum.elim (fun j => (fun t : AlgebraicEntryIndex L => z t.1 t.2)
    ((algebraicEntryNumbering L).symm j)) coefficients (finSumFinEquiv.symm j)

omit [DecidableEq D] in
 theorem identityInputValues_represents (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a))
    (P : PolynomialPrograms.Program AlgebraicInput n) (coefficients : Fin P.length → ℂ)
    (hc : ∀ j, (P.get j).coefficient.Represents (coefficients j)) :
    ∀ j, (identityDescriptions L P j).Represents (identityInputValues L z P coefficients j) := by
  intro j
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  cases t with
  | inl j =>
    simp only [identityDescriptions, identityInputValues, Equiv.symm_apply_apply, Sum.elim_inl]
    exact hz _ _
  | inr j =>
    simpa only [identityDescriptions, identityInputValues, Equiv.symm_apply_apply, Sum.elim_inr] using hc j

omit [DecidableEq D] in
 theorem identityInputValues_entry (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) (P : PolynomialPrograms.Program AlgebraicInput n)
    (coefficients : Fin P.length → ℂ) (i : ι) (a : Fin (L.arity i) → D) :
    pairedInputs (identityInputValues L z P coefficients) (identityEntryIndex L P ⟨i,a⟩) = z i a := by
  rw [identityEntryIndex, identityOriginalIndex, pairedInputs_left]
  simp only [identityInputValues, Equiv.symm_apply_apply, Sum.elim_inl]
  change (fun t : AlgebraicEntryIndex L => z t.1 t.2)
    ((algebraicEntryNumbering L).symm (algebraicEntryNumbering L ⟨i,a⟩)) = _
  rw [Equiv.symm_apply_apply]

omit [DecidableEq D] in
 theorem identityInputValues_coefficient (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) (P : PolynomialPrograms.Program AlgebraicInput n)
    (coefficients : Fin P.length → ℂ) (j : Fin P.length) :
    pairedInputs (identityInputValues L z P coefficients) (identityCoefficientIndex L P j) = coefficients j := by
  rw [identityCoefficientIndex, identityOriginalIndex, pairedInputs_left]
  simp only [identityInputValues, Equiv.symm_apply_apply, Sum.elim_inr]

 theorem programWithCoefficients_map {K R : Type} (f : K → R)
    (P : PolynomialPrograms.Program AlgebraicInput n) (c : Fin P.length → K) :
    PolynomialPrograms.mapCoefficients f (programWithCoefficients P c) =
      programWithCoefficients P (fun j => f (c j)) := by
  simp only [programWithCoefficients, PolynomialPrograms.mapCoefficients, List.map_ofFn]
  rfl

/-- The full raw-data identity algorithm, including common-field conversion and
computed initial conjugation. -/
def uniformAlgebraicIdentityTest (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (coords : Fin n → PinnedCoordinate (Fin k) D) : Bool := by
  let input := identityDescriptions L P
  let hinput := identityDescriptions_valid L hL P hP
  let C := identityPairedCandidate input hinput
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  letI := Element.starRing (identityPairedConjugate input hinput)
    (identityPairedConjugate_valid input hinput)
  exact programIdentityTest (identityCandidateLanguage L P C) coords (identityCandidateProgram L P C)

/-- Exact universal correctness over all actual finite instances, for arbitrary
finite sparse polynomials with independently encoded algebraic coefficients. -/
theorem uniformAlgebraicIdentityTest_correct (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (coords : Fin n → PinnedCoordinate (Fin k) D)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a))
    (coefficients : Fin P.length → ℂ)
    (hc : ∀ j, (P.get j).coefficient.Represents (coefficients j)) :
    uniformAlgebraicIdentityTest L hL P hP coords = true ↔
      ∀ h : ℕ, ∀ I : Instance (realizedAlgebraicLanguage L z) (Fin k) (Fin h),
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) (programWithCoefficients P coefficients) = 0 := by
  let input := identityDescriptions L P
  let hinput := identityDescriptions_valid L hL P hP
  let C := identityPairedCandidate input hinput
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail (identityPairedCandidate_valid input hinput)⟩
  letI := Element.starRing (identityPairedConjugate input hinput)
    (identityPairedConjugate_valid input hinput)
  obtain ⟨Φ, hΦ, hstar⟩ := identityPairedCandidate_realization input hinput
    (identityInputValues L z P coefficients) (identityInputValues_represents L z hz P coefficients hc)
  have hlang : (identityCandidateLanguage L P C).mapValues Φ = realizedAlgebraicLanguage L z := by
    have hh : (fun i a => Φ (C.coordinateValue (identityEntryIndex L P ⟨i,a⟩))) = z := by
      funext i a
      exact (hΦ (identityEntryIndex L P ⟨i,a⟩)).trans (identityInputValues_entry L z P coefficients i a)
    exact congrArg (Language.mk L.arity L.arity_pos) hh
  have hprogram : PolynomialPrograms.mapCoefficients Φ (identityCandidateProgram L P C) =
      programWithCoefficients P coefficients := by
    rw [identityCandidateProgram, programWithCoefficients_map]
    congr 1
    funext j
    exact (hΦ (identityCoefficientIndex L P j)).trans (identityInputValues_coefficient L z P coefficients j)
  have horacle := (programIdentityTest_correct_instances (identityCandidateLanguage L P C)
    coords (identityCandidateProgram L P C)).trans
      (all_instance_identity_map_iff (identityCandidateLanguage L P C) Φ hstar coords
        (identityCandidateProgram L P C))
  rw [hlang, hprogram] at horacle
  exact horacle

/-- Rejection supplies a real finite counterexample; no witness-size bound is asserted. -/
theorem uniformAlgebraicIdentityTest_rejects_iff (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (P : PolynomialPrograms.Program AlgebraicInput n)
    (hP : ∀ j : Fin P.length, (P.get j).coefficient.Valid)
    (coords : Fin n → PinnedCoordinate (Fin k) D)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a))
    (coefficients : Fin P.length → ℂ)
    (hc : ∀ j, (P.get j).coefficient.Represents (coefficients j)) :
    uniformAlgebraicIdentityTest L hL P hP coords = false ↔
      ∃ h : ℕ, ∃ I : Instance (realizedAlgebraicLanguage L z) (Fin k) (Fin h),
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) (programWithCoefficients P coefficients) ≠ 0 := by
  classical
  rw [← Bool.not_eq_true, uniformAlgebraicIdentityTest_correct L hL P hP coords z hz coefficients hc]
  push_neg
  rfl

end ComplexCSP.Recognition

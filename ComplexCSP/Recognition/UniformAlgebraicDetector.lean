import ComplexCSP.Recognition.GeneratedDetectorSearch
import ComplexCSP.Instances.PresentationReweight
import ComplexCSP.Recognition.UniformAlgebraicIdentityInput
import ComplexCSP.Algebra.PairedCandidateExactField

/-! # Theorem 8.4 compiler on separate original-style algebraic input

The input presentation and returned presentation use the original signature.
Only finite coefficient descriptions, arities and scopes run. Common-field
construction, exact root enumeration, time search and independent-copy output
compilation are performed internally. BO is the theorem's proof-only hypothesis.
-/
namespace ComplexCSP
open AlgebraicEncoding EncodedNumberField EffectiveRoots
open Recognition

variable {D ι : Type} [Fintype D] [Encodable D] [Fintype ι] [Encodable ι]

/-- BO of the uniquely represented original complex language. -/
def HasAlgebraicBO (L : Language D AlgebraicInput ι) : Prop :=
  ∃ z : ∀ i, (Fin (L.arity i) → D) → ℂ,
    (∀ i a, (L.value i a).Represents (z i a)) ∧ JointBO (realizedAlgebraicLanguage L z)

abbrev DetectorInputCandidate (L : Language D AlgebraicInput ι) :=
  InitialInputCandidate (Fintype.card (AlgebraicEntryIndex L) + Fintype.card (AlgebraicEntryIndex L))

def detectorCandidateLanguage (L : Language D AlgebraicInput ι) (C : DetectorInputCandidate L) :
    Language D C.FieldType ι :=
  L.reweight (fun i a => C.coordinateValue
    (finSumFinEquiv (Sum.inl (algebraicEntryNumbering L ⟨i,a⟩))))

def detectorInputValues (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    Fin (Fintype.card (AlgebraicEntryIndex L)) → ℂ := fun k =>
  let t := (algebraicEntryNumbering L).symm k
  z t.1 t.2

 theorem detectorCandidate_values {L : Language D AlgebraicInput ι}
    (C : DetectorInputCandidate L) (hv : validTail C.tail = true)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) :
    letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
    ∀ (σ : C.FieldType →+* ℂ),
      (∀ i, σ (C.coordinateValue i) = pairedInputs (detectorInputValues L z) i) →
      (fun i a => σ ((detectorCandidateLanguage L C).value i a)) = z := by
  letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
  intro σ hσ
  funext i a
  have he := hσ (finSumFinEquiv (Sum.inl (algebraicEntryNumbering L ⟨i,a⟩)))
  rw [pairedInputs_left] at he
  change σ (C.coordinateValue _) =
    (fun t : AlgebraicEntryIndex L => z t.1 t.2)
      ((algebraicEntryNumbering L).symm (algebraicEntryNumbering L ⟨i,a⟩)) at he
  rw [Equiv.symm_apply_apply] at he
  exact he

 theorem detectorCandidate_hasComplexBO (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (hBO : HasAlgebraicBO L) :
    let input := algebraicDescriptions L
    let C := identityPairedCandidate input (algebraicDescriptions_valid L hL)
    letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (identityPairedCandidate_valid input (algebraicDescriptions_valid L hL))⟩
    Presentation.HasComplexBO (detectorCandidateLanguage L C) := by
  let input := algebraicDescriptions L
  let hinput := algebraicDescriptions_valid L hL
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
  obtain ⟨z,hz,hBO⟩ := hBO
  have hvalues (k) : (input k).Represents (detectorInputValues L z k) := hz _ _
  obtain ⟨σ,hσ,_⟩ := C.sound (pairedDescriptions input) (pairedInputs (detectorInputValues L z))
    (pairedDescriptions_represents input _ hvalues) (identityPairedCandidate_accepted input hinput)
  refine ⟨σ,?_⟩
  have he : (detectorCandidateLanguage L C).mapValues σ = realizedAlgebraicLanguage L z := by
    have hv := detectorCandidate_values C hv z σ hσ
    change Language.mk L.arity L.arity_pos _ = Language.mk L.arity L.arity_pos z
    exact congrArg (Language.mk L.arity L.arity_pos) hv
  rwa [he]

/-- Actual raw-input search and original-signature presentation output. -/
def uniformAlgebraicRowDetector (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) {n : ℕ} (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (hBO : HasAlgebraicBO L) : RowDetectorOutput L n := by
  let input := algebraicDescriptions L
  let hinput := algebraicDescriptions_valid L hL
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
  let LC := detectorCandidateLanguage L C
  let PC : Presentation LC (Fin (n+1)) := P.reweight LC.value
  let O := validatedRowDetector C.tail hv LC PC hn (detectorCandidate_hasComplexBO L hL hBO)
  exact ⟨O.time,O.exponent,O.presentation.reweight L.value⟩

/-- The returned syntax, evaluated in the original selected complex values, has
precisely the original table's nonzero proportional-row relation as support. -/
theorem uniformAlgebraicRowDetector_support (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) {n : ℕ} (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (hBO : HasAlgebraicBO L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) (a : Fin (n+n) → D) :
    ((uniformAlgebraicRowDetector L hL P hn hBO).presentation.reweight z).table a ≠ 0 ↔
      a ∈ (RowTypes.omegaRelation (P.reweight z).table).tuples := by
  let input := algebraicDescriptions L
  let hinput := algebraicDescriptions_valid L hL
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
  let LC := detectorCandidateLanguage L C
  let PC : Presentation LC (Fin (n+1)) := P.reweight LC.value
  let hBC := detectorCandidate_hasComplexBO L hL hBO
  let O := validatedRowDetector C.tail hv LC PC hn hBC
  have hvalues (k) : (input k).Represents (detectorInputValues L z k) := hz _ _
  obtain ⟨σ,hσ,_⟩ := C.sound (pairedDescriptions input) (pairedInputs (detectorInputValues L z))
    (pairedDescriptions_represents input _ hvalues) (identityPairedCandidate_accepted input hinput)
  have hvz : (fun i a => σ (LC.value i a)) = z := detectorCandidate_values C hv z σ hσ
  have hp : (fun b => σ (PC.table b)) = (P.reweight z).table := by
    funext b
    have hm := PC.table_reweight_map σ b
    rw [hvz] at hm
    simpa only [PC,Presentation.reweight_reweight] using hm.symm
  have ho : ((O.presentation.reweight L.value).reweight z).table a = σ (O.presentation.table a) := by
    rw [Presentation.reweight_reweight,← hvz]
    exact O.presentation.table_reweight_map σ a
  change ((O.presentation.reweight L.value).reweight z).table a ≠ 0 ↔ _
  rw [ho,map_ne_zero]
  have hs := validatedRowDetector_support C.tail hv LC PC hn hBC σ a
  rw [← hp]
  exact hs

/-- The searched output uses exactly the allowed arithmetic progression. -/
theorem uniformAlgebraicRowDetector_exponent (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) {n : ℕ} (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (hBO : HasAlgebraicBO L) :
    (uniformAlgebraicRowDetector L hL P hn hBO).exponent =
      1 + RowPhases.phaseExponent (Fintype.card D) *
        (uniformAlgebraicRowDetector L hL P hn hBO).time := rfl

/-- The raw-input compiler returns the literal displayed Cq, with Kμ from the
exact original working field generated by the language values and conjugates.
No larger ambient field or substituted torsion exponent occurs in this formula. -/
theorem uniformAlgebraicRowDetector_exact_formula (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) {n : ℕ} (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (hBO : HasAlgebraicBO L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    letI := (realizedAlgebraicLanguage L z).workingField_numberField
      (fun i a => (hz i a).isAlgebraic)
    let output := uniformAlgebraicRowDetector L hL P hn hBO
    (output.presentation.reweight z).table =
      rowDetector (P.reweight z).table
        ((RowDetector.fieldExponent (realizedAlgebraicLanguage L z).workingField - 1)*output.exponent)
        output.exponent := by
  letI := (realizedAlgebraicLanguage L z).workingField_numberField
    (fun i a => (hz i a).isAlgebraic)
  let input := algebraicDescriptions L
  let hinput := algebraicDescriptions_valid L hL
  let C := identityPairedCandidate input hinput
  let hv := identityPairedCandidate_valid input hinput
  letI : Fact (Element.Valid C.degree (coefficientRelation C.tail)) := ⟨validTail_sound C.tail hv⟩
  let LC := detectorCandidateLanguage L C
  let PC : Presentation LC (Fin (n+1)) := P.reweight LC.value
  let hBC := detectorCandidate_hasComplexBO L hL hBO
  let O := validatedRowDetector C.tail hv LC PC hn hBC
  have hvalues (k) : (input k).Represents (detectorInputValues L z k) := hz _ _
  obtain ⟨σ,hσ,_⟩ := C.sound (pairedDescriptions input) (pairedInputs (detectorInputValues L z))
    (pairedDescriptions_represents input _ hvalues) (identityPairedCandidate_accepted input hinput)
  have hvz : (fun i a => σ (LC.value i a)) = z := detectorCandidate_values C hv z σ hσ
  have hp : (fun b => σ (PC.table b)) = (P.reweight z).table := by
    funext b
    have hm := PC.table_reweight_map σ b
    rw [hvz] at hm
    simpa only [PC,Presentation.reweight_reweight] using hm.symm
  have ho : ((O.presentation.reweight L.value).reweight z).table =
      fun a => σ (O.presentation.table a) := by
    funext a
    rw [Presentation.reweight_reweight,← hvz]
    exact O.presentation.table_reweight_map σ a
  have hE : rootExponentFromCoefficients C.degree C.tail =
      RowDetector.fieldExponent (realizedAlgebraicLanguage L z).workingField :=
    identityPairedCandidate_rootExponent_eq L hL z hz
  have ht : O.presentation.table = rowDetector PC.table
      ((rootExponentFromCoefficients C.degree C.tail-1)*O.exponent) O.exponent :=
    PC.compileRowDetector_table hn (rootExponentFromCoefficients C.degree C.tail)
      (checkedRootExponent_ge_two C.tail hv) (checkedRootExponent_killsTorsion C.tail hv) hBC
  change ((O.presentation.reweight L.value).reweight z).table = _
  rw [ho,← hE,← hp]
  funext a
  rw [ht]
  exact (rowDetector_map σ PC.table _ _ a).symm

end ComplexCSP

import ComplexCSP.Recognition.GeneratedDetectorAlgorithms
import ComplexCSP.Structure.RowDetectorEmbeddedExistence
import ComplexCSP.Algebra.EffectiveRootsExactExponent

/-! # Terminating exact detector search returning a literal presentation

The only semantic input assumption is the theorem's global BO hypothesis.
Existence of a successful time is proved from that hypothesis, rather than supplied
as an oracle. The raw integer-tail frontend computes the exact paper exponent.
-/
namespace ComplexCSP
open RowPhases RowDetector EncodedNumberField EffectiveRoots

/-- Output data requested by Theorem 8.4. -/
structure RowDetectorOutput {D K ι : Type} (L : Language D K ι) (n : ℕ) where
  time : ℕ
  exponent : ℕ
  presentation : Presentation L (Fin (n+n))

namespace Presentation
variable {D K ι : Type} [Fintype D] [Fintype ι] [Field K] [DecidableEq K]
variable {L : Language D K ι} {n : ℕ}

/-- Exact BO on a selected complex realization is a proof-only precondition. -/
def HasComplexBO (L : Language D K ι) : Prop := ∃ σ : K →+* ℂ, JointBO (L.mapValues σ)

 theorem exists_detectorTimeTest (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E)
    (hBO : HasComplexBO L) : ∃ t, detectorTimeTest P.table E t = true := by
  obtain ⟨σ,hσ⟩ := hBO
  obtain ⟨t,ht⟩ := RowDetectorEmbeddedExistence.exists_generated_detector_time
    L σ hσ hn P.table P.table_generated E hE hkill
  refine ⟨t,(detectorTimeTest_correct P.table E t σ).mpr ?_⟩
  intro a
  simpa only [rowDetector_map,map_ne_zero] using ht a

/-- Search and compile, retaining actual independent hidden-variable copies. -/
def compileRowDetector (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E)
    (hBO : HasComplexBO L) : RowDetectorOutput L n :=
  let t := findTableDetectorTime P.table E (P.exists_detectorTimeTest hn E hE hkill hBO)
  let q := 1 + phaseExponent (Fintype.card D)*t
  ⟨t,q,P.rowDetector ((E-1)*q) q⟩

 theorem compileRowDetector_exponent (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E)
    (hBO : HasComplexBO L) :
    (P.compileRowDetector hn E hE hkill hBO).exponent =
      1 + phaseExponent (Fintype.card D)*(P.compileRowDetector hn E hE hkill hBO).time := rfl

 theorem compileRowDetector_table (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E)
    (hBO : HasComplexBO L) :
    (P.compileRowDetector hn E hE hkill hBO).presentation.table =
      ComplexCSP.rowDetector P.table ((E-1)*(P.compileRowDetector hn E hE hkill hBO).exponent)
        (P.compileRowDetector hn E hE hkill hBO).exponent :=
  P.table_rowDetector _ _

/-- The returned actual presentation has exactly Ω as support. No successful
search-time, output table, or target isomorphism is assumed. -/
theorem compileRowDetector_support (P : Presentation L (Fin (n+1)))
    (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E)
    (hBO : HasComplexBO L) (σ : K →+* ℂ) (a : Fin (n+n) → D) :
    (P.compileRowDetector hn E hE hkill hBO).presentation.table a ≠ 0 ↔
      a ∈ (RowTypes.omegaRelation (fun b => σ (P.table b))).tuples := by
  have ht := findTableDetectorTime_spec P.table E (P.exists_detectorTimeTest hn E hE hkill hBO)
  have hs := (detectorTimeTest_correct P.table E _ σ).mp ht a
  rw [rowDetector_map,map_ne_zero] at hs
  simpa only [compileRowDetector,table_rowDetector] using hs

end Presentation

namespace EncodedNumberField
variable {d : ℕ} (coefficients : Fin d → ℤ)
variable {D ι : Type} [Fintype D] [Fintype ι] {n : ℕ}

/-- Uniform raw-coordinate detector: the exponent is computed from the complete
root enumeration and proved equal to lcm(2, exp μ(K)) for this exact field. -/
def validatedRowDetector (hvalid : validTail coefficients = true)
    (L : Language D (Element d (coefficientRelation coefficients)) ι)
    (P : Presentation L (Fin (n+1))) (hn : 0 < n) :
    letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
      ⟨validTail_sound coefficients hvalid⟩
    Presentation.HasComplexBO L → RowDetectorOutput L n := by
  letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
    ⟨validTail_sound coefficients hvalid⟩
  intro hBO
  exact P.compileRowDetector hn (rootExponentFromCoefficients d coefficients)
    (checkedRootExponent_ge_two coefficients hvalid)
    (checkedRootExponent_killsTorsion coefficients hvalid) hBO

 theorem validatedRowDetector_support (hvalid : validTail coefficients = true)
    (L : Language D (Element d (coefficientRelation coefficients)) ι)
    (P : Presentation L (Fin (n+1))) (hn : 0 < n) :
    letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
      ⟨validTail_sound coefficients hvalid⟩
    ∀ (hBO : Presentation.HasComplexBO L)
      (σ : Element d (coefficientRelation coefficients) →+* ℂ) (a : Fin (n+n) → D),
      (validatedRowDetector coefficients hvalid L P hn hBO).presentation.table a ≠ 0 ↔
        a ∈ (RowTypes.omegaRelation (fun b => σ (P.table b))).tuples := by
  letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
    ⟨validTail_sound coefficients hvalid⟩
  intro hBO σ a
  exact P.compileRowDetector_support hn (rootExponentFromCoefficients d coefficients)
    (checkedRootExponent_ge_two coefficients hvalid)
    (checkedRootExponent_killsTorsion coefficients hvalid) hBO σ a

/-- The literal displayed formula uses the exact mathematical field exponent. -/
theorem validatedRowDetector_exact_formula (hvalid : validTail coefficients = true)
    (L : Language D (Element d (coefficientRelation coefficients)) ι)
    (P : Presentation L (Fin (n+1))) (hn : 0 < n) :
    letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
      ⟨validTail_sound coefficients hvalid⟩
    ∀ hBO : Presentation.HasComplexBO L,
      let output := validatedRowDetector coefficients hvalid L P hn hBO
      output.exponent = 1 + phaseExponent (Fintype.card D)*output.time ∧
      output.presentation.table = ComplexCSP.rowDetector P.table
        ((fieldExponent (Element d (coefficientRelation coefficients))-1)*output.exponent)
        output.exponent := by
  letI : Fact (Element.Valid d (coefficientRelation coefficients)) :=
    ⟨validTail_sound coefficients hvalid⟩
  intro hBO
  refine ⟨rfl,?_⟩
  have ht := P.compileRowDetector_table hn (rootExponentFromCoefficients d coefficients)
    (checkedRootExponent_ge_two coefficients hvalid)
    (checkedRootExponent_killsTorsion coefficients hvalid) hBO
  rw [← checkedRootExponent_eq_fieldExponent coefficients hvalid]
  exact ht

end EncodedNumberField
end ComplexCSP

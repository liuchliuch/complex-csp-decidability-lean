import ComplexCSP.Structure.RowEquivalenceRealization
import ComplexCSP.Algebra.WorkingField
import ComplexCSP.Instances.ValueTransport
import ComplexCSP.Algebra.Theorem52Counterexample
import ComplexCSP.Recognition.CertificatesLegalTables

/-! Explicit paper statements obtained by composing the structural theorems. -/
namespace ComplexCSP.PaperBridge
open MaltsevRelations RowTypes BlockOrthogonality

theorem lemma_7_3_pp_rectangularity {D ι : Type} [Fintype D]
    (L : Language D ℂ ι) (hBO : JointBO L) :
    EqualityFreeSingletonRectangularity (generatedSupports L) :=
  generated_supports_equalityfree_rectangularity
    (allGeneratedOriginalBO_supportRectangular (hBO.original L))

theorem lemma_7_4 {D ι : Type} [Fintype D]
    (L : Language D ℂ ι) (hBO : JointBO L)
    (Δ : Finset (Relation D)) (hΔ : (↑Δ : Set (Relation D)) ⊆ generatedSupports L) :
    ∃ m, IsMaltsev m ∧ CommonPolymorphism (↑Δ : Set (Relation D)) m :=
  finite_family_maltsev (lemma_7_3_pp_rectangularity L hBO) Δ hΔ

theorem lemma_8_2 {D ι : Type} [Fintype D]
    (L : Language D ℂ ι) (hBO : JointBO L) {n : ℕ}
    (G : (Fin (n+1) → D) → ℂ) (hG : Instance.Generated L G)
    (x y : Fin n → D) (z₀ : D)
    (hxz : tableRows G x z₀ ≠ 0) (hyz : tableRows G y z₀ ≠ 0) :
    support (tableRows G x) = support (tableRows G y) ∧
    RowPhases.anchorScalar (tableRows G x) (tableRows G y) z₀ ≠ 0 ∧
    RowPhases.anchorScalar (tableRows G x) (tableRows G y) z₀ ∈ L.workingField ∧
    RowPhases.anchoredPhase (tableRows G x) (tableRows G y) z₀ z₀ = 1 ∧
    ∀ z, tableRows G x z ≠ 0 →
      tableRows G y z = RowPhases.anchorScalar (tableRows G x) (tableRows G y) z₀ *
        RowPhases.anchoredPhase (tableRows G x) (tableRows G y) z₀ z * tableRows G x z ∧
      RowPhases.anchoredPhase (tableRows G x) (tableRows G y) z₀ z ∈ L.workingField ∧
      IsOfFinOrder (RowPhases.anchoredPhase (tableRows G x) (tableRows G y) z₀ z) ∧
      RowPhases.anchoredPhase (tableRows G x) (tableRows G y) z₀ z ^
        RowPhases.phaseExponent (Fintype.card D) = 1 := by
  have hp : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => tableRows G x z ^ h) := by
    intro h _ _
    exact hBO.original L n (fun a => G a ^ h) (Instance.generated_pow hG h)
  obtain ⟨hs,hlambda,ha,hp⟩ := finite_row_phases_of_power_BO (tableRows G) hp x y z₀ hxz hyz
  have hm (a : Fin n → D) (z : D) : tableRows G a z ∈ L.workingField :=
    Instance.generated_mem_workingField hG (Fin.snoc a z)
  refine ⟨hs,hlambda,?_,ha,?_⟩
  · exact L.workingField.div_mem (hm y z₀) (hm x z₀)
  · intro z hz
    obtain ⟨he,hfin,hpow⟩ := hp z hz
    refine ⟨he,?_,hfin,hpow⟩
    exact L.workingField.div_mem
      (L.workingField.div_mem (hm y z) (hm x z))
      (L.workingField.div_mem (hm y z₀) (hm x z₀))

theorem lemma_8_5 {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : JointBO L) (m : Operation D)
    (hm : ∀ (r : ℕ), 0 < r → ∀ (F : (Fin r → D) → ℂ),
      Instance.Generated L F → Preserves m {a | F a ≠ 0})
    {n : ℕ} (hn : 0 < n) (G : (Fin (n+1) → D) → ℂ)
    (hG : Instance.Generated L G) : Preserves m (omegaRelation G).tuples := by
  obtain ⟨F,hF,he⟩ := RowEquivalenceRealization.omega_mem_generatedSupports L hAlg hBO hn G hG
  rw [he]
  exact hm (n+n) (by omega) F hF

/-- Cancelling one table-wide nonzero normalization preserves every intrinsic
entry equation in 4.1, including arbitrary four (not only adjacent) entries. -/
theorem normalization_norm_iff (c a b : ℂ) (hc : c ≠ 0) :
    ‖c*a‖ = ‖c*b‖ ↔ ‖a‖ = ‖b‖ := by
  rw [norm_mul,norm_mul]
  constructor
  · exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hc)
  · exact congrArg (fun x => ‖c‖ * x)

theorem normalization_products_iff (c a b u v : ℂ) (hc : c ≠ 0) :
    (c*a)*(c*b) = (c*u)*(c*v) ↔ a*b = u*v := by
  rw [show (c*a)*(c*b) = (c*c)*(a*b) by ring,
    show (c*u)*(c*v) = (c*c)*(u*v) by ring]
  constructor
  · exact mul_left_cancel₀ (mul_ne_zero hc hc)
  · exact congrArg (fun x => c*c*x)

theorem normalization_norm_products_iff (c a b u v : ℂ) (hc : c ≠ 0) :
    ‖(c*a)*(c*b)‖ = ‖(c*u)*(c*v)‖ ↔ ‖a*b‖ = ‖u*v‖ := by
  rw [show (c*a)*(c*b) = (c*c)*(a*b) by ring,
    show (c*u)*(c*v) = (c*c)*(u*v) by ring]
  exact normalization_norm_iff (c*c) _ _ (mul_ne_zero hc hc)

theorem normalization_covariance_iff (c a b ρ : ℂ) (hc : c ≠ 0) :
    c*a = ρ*(c*b) ↔ a = ρ*b := by
  rw [show ρ*(c*b) = c*(ρ*b) by ring]
  constructor
  · exact mul_left_cancel₀ hc
  · exact congrArg (fun x => c*x)

/-- A finite rational basis represents exactly the original algebraic tables. -/
theorem workingField_realization {D : Type} [Fintype D] {s : ℕ}
    (L : Language D ℂ (Fin s))
    (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    ∃ n : ℕ, ∃ _basis : Module.Basis (Fin n) ℚ L.workingField,
      L.workingFieldLanguage.mapValues L.workingField.subtype = L := by
  letI := L.workingField_finiteDimensional hL
  refine ⟨Module.finrank ℚ L.workingField, Module.finBasis ℚ L.workingField, ?_⟩
  rfl

open Theorem52Counterexample
/-- The simple-instance counterexample interpreted as algebraic complex tables. -/
theorem theorem_5_2_complex_counterexample :
    (∀ (n : ℕ)
      (I : Instance (unaryLanguage (fun i => (firstProfile i : ℂ))) (Fin 1) (Fin n)),
      PaperSimple I → I.partition zeroPin =
        (I.retarget (fun _ x => (secondProfile (x 0) : ℂ))).partition zeroPin) ∧
    ¬ (∃ e : Fin 3 ≃ Fin 3,
      (unaryLanguage (fun i => (firstProfile i : ℂ))).IsTargetIso
        (fun _ x => (secondProfile (x 0) : ℂ)) e) := by
  constructor
  · intro n I hs
    apply all_simple_unary_equal (fun i => (firstProfile i : ℂ))
      (fun i => (secondProfile i : ℂ)) _ zeroPin zeroPin (fun _ => by rfl) I hs
    norm_num [Fin.sum_univ_succ, firstProfile, secondProfile,
      show (2 : Fin 3) ≠ 1 by decide]
  · rintro ⟨e, he⟩
    have hv := he () (fun _ => (1 : Fin 3))
    have htwo : (2 : ℂ) = (secondProfile (e 1) : ℂ) := by
      simpa only [unaryLanguage, firstProfile, Function.comp_apply] using hv
    exact secondProfile_ne_two (e 1) (Rat.cast_injective htwo.symm)

end ComplexCSP.PaperBridge

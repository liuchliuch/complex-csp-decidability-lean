import ComplexCSP.Complexity.CSPDegreeFieldTransport
import ComplexCSP.Complexity.CSPDomainTransport

/-! # Genuine ordinary and degree-promised FP invariance of fixed field encodings

All reductions use actual fixed-coordinate machines and charged answer bounds.
These interfaces preserve FP under representation changes; they make no
classification claim without the separately proved evaluator construction.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityCSPRepresentationFP
open PlanarHom PlanarHom.Complexity ComplexityGadgetSubstitution
variable {D K R : Type} [Fintype D] [Field K] [Field R] [Algebra ℚ K] [Algebra ℚ R]
variable {s d e : ℕ} (bK : Module.Basis (Fin d) ℚ K) (bR : Module.Basis (Fin e) ℚ R)
variable (σ : K →+* ℂ) (τ : R →+* ℂ)
variable (L : Language D K (Fin s)) (M : Language D R (Fin s))
variable (h : L.mapValues σ=M.mapValues τ)

/-- Fixed degree promises commute with the constructed two-field diagram. -/
def degreeReduction (δ : ℕ) : PromisePolyTimeTuringReduction
    (degreePartitionProblem L bK δ) (degreePartitionProblem M bR δ) := by
  let bJ := ComplexityCSPCommonField.basis bK bR σ τ
  have h₁ := ComplexityCSPDegreeFieldTransport.descentReduction L bK bJ
    (ComplexityCSPCommonField.left bK bR σ τ).toRatAlgHom δ
  have h₂ := ComplexityCSPDegreeFieldTransport.embeddingReduction M bR bJ
    (ComplexityCSPCommonField.right bK bR σ τ).toRatAlgHom δ
  change PromisePolyTimeTuringReduction (degreePartitionProblem L bK δ)
    (degreePartitionProblem (L.mapValues (ComplexityCSPCommonField.left bK bR σ τ)) bJ δ) at h₁
  change PromisePolyTimeTuringReduction
    (degreePartitionProblem (M.mapValues (ComplexityCSPCommonField.right bK bR σ τ)) bJ δ)
    (degreePartitionProblem M bR δ) at h₂
  rw [ComplexityCSPCommonField.mapped_languages bK bR σ τ L M h] at h₁
  exact h₁.trans h₂

include h in
theorem inFP_iff : (ComplexityCSPCountReduction.partitionProblem L bK).InFP ↔
    (ComplexityCSPCountReduction.partitionProblem M bR).InFP :=
  ⟨fun hL => (ComplexityCSPCommonField.reverseReduction bK bR σ τ L M h).inFP hL,
    fun hM => (ComplexityCSPCommonField.reduction bK bR σ τ L M h).inFP hM⟩

include h in
theorem degree_inFP_iff (δ : ℕ) : (degreePartitionProblem L bK δ).InFP ↔
    (degreePartitionProblem M bR δ).InFP :=
  ⟨fun hL => (degreeReduction bR bK τ σ M L h.symm δ).inFP hL,
    fun hM => (degreeReduction bK bR σ τ L M h δ).inFP hM⟩

/-- A change of basis in the same field needs no complex embedding or common
field; the compiled identity linear map and its left inverse suffice. -/
theorem basis_inFP_iff {d' : ℕ} (bK' : Module.Basis (Fin d') ℚ K) :
    (ComplexityCSPCountReduction.partitionProblem L bK).InFP ↔
      (ComplexityCSPCountReduction.partitionProblem L bK').InFP := by
  have he : L.mapValues (AlgHom.id ℚ K).toRingHom=L := by cases L; rfl
  constructor
  · intro hL
    have hr := ComplexityCSPFieldTransport.embeddingReduction L bK bK' (AlgHom.id ℚ K)
    rw [he] at hr
    exact hr.inFP hL
  · intro hL
    have hr := ComplexityCSPFieldTransport.descentReduction L bK bK' (AlgHom.id ℚ K)
    rw [he] at hr
    exact hr.inFP hL

theorem degree_basis_inFP_iff {d' : ℕ} (bK' : Module.Basis (Fin d') ℚ K) (δ : ℕ) :
    (degreePartitionProblem L bK δ).InFP ↔ (degreePartitionProblem L bK' δ).InFP := by
  have he : L.mapValues (AlgHom.id ℚ K).toRingHom=L := by cases L; rfl
  constructor
  · intro hL
    have hr := ComplexityCSPDegreeFieldTransport.embeddingReduction L bK bK' (AlgHom.id ℚ K) δ
    rw [he] at hr
    exact hr.inFP hL
  · intro hL
    have hr := ComplexityCSPDegreeFieldTransport.descentReduction L bK bK' (AlgHom.id ℚ K) δ
    rw [he] at hr
    exact hr.inFP hL

end ComplexCSP.ComplexityCSPRepresentationFP

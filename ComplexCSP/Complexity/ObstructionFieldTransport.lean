import ComplexCSP.Complexity.CSPCommonField
import ComplexCSP.Complexity.ReducedGram

/-! # Obstruction reductions in any prescribed original coefficient basis

The selected obstruction field and the supplied realization are joined inside ℂ.
Neither inclusion between the two original ambient fields is assumed. All
coordinate conversions are compiled fixed-field rational-linear machines.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityObstructionFieldTransport
open PlanarHom PlanarHom.Complexity ComplexityReducedGram
variable {D K : Type} [Fintype D] [Field K] [Algebra ℚ K] [DecidableEq K]
variable {s d : ℕ} {L : Language D ℂ (Fin s)}
variable (W : Witness L) (b : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ)
variable (M : Language D K (Fin s)) (hM : M.mapValues σ=L)

/-- The original-input realization selected with the Gram obstruction reduces
to any supplied finite-basis realization of exactly the same complex language. -/
def reduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem W.input W.basis)
    (ComplexityCSPCountReduction.partitionProblem M b) :=
  ComplexityCSPCommonField.reduction W.basis b W.field.subtype σ W.input M
    (W.input_correct.trans hM.symm)

/-- Representation independence holds in both directions, with charged answers. -/
def reverseReduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem M b)
    (ComplexityCSPCountReduction.partitionProblem W.input W.basis) :=
  ComplexityCSPCommonField.reverseReduction W.basis b W.field.subtype σ W.input M
    (W.input_correct.trans hM.symm)

/-- The actual finite Gram query reduction now targets the prescribed original
coefficient encoding, rather than the obstruction-selected ambient field. -/
def matrixReduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage W.matrix) W.basis)
    (ComplexityCSPCountReduction.partitionProblem M b) :=
  W.reduction.trans (reduction W b σ M hM)

include b σ M hM in
omit [Fintype D] [DecidableEq K] in
/-- Finite rational-basis realizations supply the algebraicity needed by the
literal structural witness construction; no additional entry oracle is needed. -/
theorem language_algebraic : ∀ i a,IsAlgebraic ℚ (L.value i a) := by
  letI : FiniteDimensional ℚ K := Module.Finite.of_basis b
  intro i a
  subst L
  exact (IsIntegral.map σ.toRatAlgHom
    (IsIntegral.of_finite (R:=ℚ) (M.value i a))).isAlgebraic

end ComplexCSP.ComplexityObstructionFieldTransport

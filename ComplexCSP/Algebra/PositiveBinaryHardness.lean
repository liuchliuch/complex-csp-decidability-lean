import ComplexCSP.Instances.MatrixCSPApexSemantics
import ComplexCSP.Instances.MatrixCSPMixedAdapter
import PlanarHom.BiasedPositiveReduction

/-! # General-graph hardness of every positive nonsingular two-spin interaction

Unequal diagonals use the independently proved signed-NAND reduction. Equal
diagonals use a shared apex and an explicit factor-two recovery. This does not
assert that the planar Ising problem is hard, and it does not assume the full
Bulatov--Grohe dichotomy or arbitrary principal-submatrix availability.
-/
namespace ComplexCSP.PositiveBinaryApex
open ComplexityCSPCode PlanarHom PlanarHom.Complexity PairProjectionMachines

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- Actual charged single-query reduction from the biased interaction to the
original equal-diagonal interaction on unrestricted raw CSP instances. -/
noncomputable def apexReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Bool → Bool → K) (hs : ∀ i j, A i j = A j i)
    (hd : A false false = A true true) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language (biased A)) basis)
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  classical
  let prepare : Code → Bits × List Code := fun g => ([],[compileApex A g])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare :=
    (fp_const encoding BitEncoding.bits []).pair
      (((fp_compileApex A).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding))
  let recover : Bits × List K → K := fun p => p.2.headD 0 / 2
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (((fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)).pair
      (fp_const _ (numberFieldEncoding basis) 2)).comp (FixedFieldArithmetic.fp_division basis)
  let target := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language (biased A)) basis
  let source := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis
  let view : ∀ raw, target.valid raw → Code := fun _ h => h.choose
  have hview : ∀ raw h, encoding.encode (view raw h) = raw := fun _ h => h.choose_spec.2
  let p := Classical.choose (exists_partition_output_bound (MatrixCSP.language A) basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound (MatrixCSP.language A) basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding basis)
    (numberFieldEncoding basis) target source prepare (partition (MatrixCSP.language A)) recover
    (Classical.choice hp) (Classical.choice hr) view hview ?_ ?_ ?_ p ?_
  · intro raw h q hq
    have he : q = compileApex A (view raw h) := List.mem_singleton.mp hq
    subst q
    exact ⟨_,compileApex_valid A (biased A) _ h.choose_spec.1,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis)
      (partition (MatrixCSP.language A)) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (partition (MatrixCSP.language A) (compileApex A (view raw h)) / 2) =
      encodedFunction encoding (numberFieldEncoding basis) (partition (MatrixCSP.language (biased A))) [] raw
    conv_rhs => rw [← hview raw h,encodedFunction_encode]
    rw [compileApex_twice_partition A hs hd _ h.choose_spec.1]
    congr 1
    have htwo : (2 : K) ≠ 0 := by
      have hh : (algebraMap ℚ K) 2 ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr (by norm_num)
      simpa using hh
    rw [mul_comm, mul_div_cancel_right₀ _ htwo]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

/-- The complete strict-positive rank-two Boolean seed, with genuine #P source
machines and both diagonal cases discharged. The graph input is unrestricted. -/
theorem positive_nonsingular_hard (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K →+* ℝ) (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 < ρ (A i j))
    (hdet : A false false * A true true ≠ A false true ^ 2) :
    PromisedSharpPHard
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  letI : Module.Finite ℚ K := Module.Finite.of_basis basis
  by_cases hd : A false false = A true true
  · have ha : A false false ≠ 0 := by
      intro he
      simpa only [he,map_zero,lt_self_iff_false] using hpos false false
    have hb : A false true ≠ 0 := by
      intro he
      simpa only [he,map_zero,lt_self_iff_false] using hpos false true
    have hh := BiasedPositiveHardness.promisedSharpPHard basis ρ (biased A)
      (biased_symmetric A hs) (biased_positive A ρ hpos)
      (biased_diagonal_ne A hs hd ha hdet) (biased_det_ne A hs ha hb hdet)
    exact (hh.trans (MatrixCSPMixedAdapter.reduction basis (biased A))).trans
      (apexReduction basis A hs hd)
  · exact (BiasedPositiveHardness.promisedSharpPHard basis ρ A hs hpos hd hdet).trans
      (MatrixCSPMixedAdapter.reduction basis A)

end ComplexCSP.PositiveBinaryApex

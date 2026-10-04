import ComplexCSP.Algebra.PadicInterpolationMatrixPowers

/-! # From integral matrix powers to the small Banach-algebra interpolation input -/

namespace ComplexCSP.PadicInterpolation

open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def matrixOperator (d : ℕ) :
    Matrix (Fin d) (Fin d) ℚ_[p] ≃ₐ[ℚ_[p]]
      ((Fin d → ℚ_[p]) →L[ℚ_[p]] (Fin d → ℚ_[p])) :=
  Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap _)

@[simp] theorem matrixOperator_apply {d : ℕ} (T : Matrix (Fin d) (Fin d) ℚ_[p])
    (v : Fin d → ℚ_[p]) : matrixOperator p d T v = T.mulVec v := rfl

/-- A deliberately coarse ordinary triangle-inequality operator bound. No
ultrametric operator-norm convention or unproved norm equivalence is needed. -/
theorem matrixOperator_norm_le {d : ℕ} (T : Matrix (Fin d) (Fin d) ℚ_[p])
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ i j, ‖T i j‖ ≤ B) :
    ‖matrixOperator p d T‖ ≤ (d:ℝ)*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, T i j * v j‖ ≤ (d:ℝ)*B*‖v‖
  calc
    _ ≤ ∑ j, ‖T i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin d, B*‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hT i j) (norm_le_pi_norm v j) (norm_nonneg _) hB
    _ = _ := by simp; ring

/-- Integral inverse matrices have a common positive power whose operator
remainder satisfies the precise analytic interpolation smallness condition. -/
theorem exists_common_small_operator_power {ι : Type*} {d : ℕ}
    (T S : ι → Matrix (Fin d) (Fin d) ℚ_[p])
    (hT : ∀ a i j, ‖T a i j‖ ≤ 1) (hS : ∀ a i j, ‖S a i j‖ ≤ 1)
    (hTS : ∀ a, T a*S a=1) (hST : ∀ a, S a*T a=1) :
    ∃ M : ℕ, 0 < M ∧ ∀ a,
      2*((p:ℝ)*‖(matrixOperator p d (T a))^M - 1‖) < 1 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  have hden : 0 < 2*(p:ℝ)*((d:ℝ)+1) := by positivity
  obtain ⟨N,hN⟩ := PadicInt.exists_pow_neg_lt p (show 0 < 1/(2*(p:ℝ)*((d:ℝ)+1)) by positivity)
  have hN' : (p:ℝ)^(-(N:ℤ)) * (2*(p:ℝ)*((d:ℝ)+1)) < 1 :=
    (lt_div_iff₀ hden).mp hN
  obtain ⟨M,hM,hbound⟩ := exists_common_matrix_power p T S hT hS hTS hST N
  refine ⟨M,hM,?_⟩
  intro a
  have hpow0 : 0 ≤ (p:ℝ)^(-(N:ℤ)) := le_of_lt (zpow_pos hp0 _)
  have hnorm := matrixOperator_norm_le p (T a^M-1) _ hpow0 (hbound a)
  rw [map_sub, map_pow, map_one] at hnorm
  have hscaled := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2*(p:ℝ) by positivity)
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

end ComplexCSP.PadicInterpolation

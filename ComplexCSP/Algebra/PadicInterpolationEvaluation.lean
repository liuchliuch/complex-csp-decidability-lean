import ComplexCSP.Algebra.PadicInterpolationSeries

/-! # Natural-number values of the constructed analytic p-adic interpolation -/

namespace ComplexCSP.PadicInterpolation

open Polynomial
open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

noncomputable def doubleTerm (C : A) (z : ℚ_[p]) (k j : ℕ) : A :=
  z^j • ((binomialPolynomial p k).coeff j • C^k)

omit [CompleteSpace A] [NormOneClass A] in
theorem doubleTerm_zero (C : A) (z : ℚ_[p]) (k j : ℕ) (h : k < j) :
    doubleTerm p C z k j = 0 := by
  simp [doubleTerm, binomialPolynomial_coeff_eq_zero p k j h]

omit [CompleteSpace A] in
theorem norm_doubleTerm_le (C : A) (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) (k j : ℕ) :
    ‖doubleTerm p C z k j‖ ≤ ((p:ℝ)*‖C‖)^k := by
  rw [doubleTerm, norm_smul, norm_pow]
  calc
    _ ≤ 1 * ‖(binomialPolynomial p k).coeff j • C^k‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact pow_le_one₀ (norm_nonneg _) hz
    _ ≤ _ := by simpa using coefficient_term_bound p C j k

omit [CompleteSpace A] in
/-- Absolute convergence of the whole double family justifies exchanging the
polynomial coefficient sum with the interpolation sum. -/
theorem summable_doubleTerm_norm (C : A) (hC : (p:ℝ)*‖C‖ < 1)
    (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    Summable (fun ij : ℕ × ℕ ↦ ‖doubleTerm p C z ij.1 ij.2‖) := by
  let q : ℝ := (p:ℝ)*‖C‖
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hC
  apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
  constructor
  · intro k
    apply summable_of_ne_finset_zero (s := Finset.range (k+1))
    intro j hj
    rw [doubleTerm_zero p C z k j (by simpa using hj), norm_zero]
  · have hg : Summable (fun k : ℕ ↦ ((k+1:ℕ):ℝ)*q^k) := by
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq1
      have h2 := summable_geometric_of_lt_one hq0 hC
      simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h1.add h2
    apply Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg (fun _ ↦ norm_nonneg _)) _ hg
    intro k
    rw [tsum_eq_sum (s := Finset.range (k+1)) (fun j hj ↦ by
      rw [doubleTerm_zero p C z k j (by simpa using hj), norm_zero])]
    calc
      _ ≤ ∑ j ∈ Finset.range (k+1), q^k := Finset.sum_le_sum fun _ _ ↦ norm_doubleTerm_le p C z hz k _
      _ = _ := by simp

omit [CompleteSpace A] [NormOneClass A] in
theorem doubleTerm_tsum_row (C : A) (z : ℚ_[p]) (k : ℕ) :
    (∑' j : ℕ, doubleTerm p C z k j) = (binomialPolynomial p k).eval z • C^k := by
  rw [tsum_eq_sum (s := Finset.range (k+1)) (fun j hj ↦
    doubleTerm_zero p C z k j (by simpa using hj))]
  have hdegree : (binomialPolynomial p k).natDegree < k+1 := by
    apply Nat.lt_succ_of_le
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [descPochhammer_natDegree])
  rw [Polynomial.eval_eq_sum_range' hdegree, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [doubleTerm, smul_smul]
  rw [mul_comm]

set_option maxHeartbeats 1500000 in
/-- On the entire p-adic unit disk, the constructed analytic power series is
the convergent binomial sum. -/
theorem analyticInterpolation_eq_binomial (C : A) (hC : (p:ℝ)*‖C‖ < 1)
    (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    analyticInterpolation p C z = ∑' k : ℕ, (binomialPolynomial p k).eval z • C^k := by
  change (∑' j : ℕ, (interpolationSeries p C j) (fun _ ↦ z)) = _
  simp only [interpolationSeries, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [interpolationCoefficient, ← (summable_coefficient_terms p C hC _).tsum_const_smul _]
  change (∑' j : ℕ, ∑' k : ℕ, doubleTerm p C z k j) = _
  have hs : Summable (Function.uncurry (fun k j : ℕ ↦ doubleTerm p C z k j)) :=
    (summable_doubleTerm_norm p C hC z hz).of_norm
  rw [hs.tsum_comm]
  apply tsum_congr
  intro k
  exact doubleTerm_tsum_row p C z k

/-- The actual analytic function has the prescribed operator-power values. -/
theorem analyticInterpolation_nat (C : A) (hC : 2*((p:ℝ)*‖C‖) < 1) (n : ℕ) :
    analyticInterpolation p C (n:ℚ_[p]) = (1+C)^n := by
  have hq0 : 0 ≤ (p:ℝ)*‖C‖ := by positivity
  have hq1 : (p:ℝ)*‖C‖ < 1 := by linarith
  rw [analyticInterpolation_eq_binomial p C hq1 _ (by
    simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (n:ℤ))]
  simp_rw [binomialPolynomial_eval_nat]
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk ↦ by
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk), Nat.cast_zero, zero_smul])]
  rw [add_comm (1:A) C, (Commute.one_right C).add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_pow, mul_one, Nat.cast_smul_eq_nsmul]
  rw [nsmul_eq_mul, Nat.cast_comm]

end ComplexCSP.PadicInterpolation

import ComplexCSP.Algebra.PadicInterpolationBinomial
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# An actual analytic binomial power series near the p-adic unit disk

The coefficients are constructed by convergent infinite sums from a small
Banach-algebra element. The radius lower bound is proved from the binomial
coefficient estimate; no analyticity premise is supplied.
-/

namespace ComplexCSP.PadicInterpolation

open Polynomial
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [hp : Fact p.Prime]
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

noncomputable def interpolationCoefficient (C : A) (j : ℕ) : A :=
  ∑' k : ℕ, (binomialPolynomial p k).coeff j • C^k

omit [CompleteSpace A] in
theorem coefficient_term_bound (C : A) (j k : ℕ) :
    ‖(binomialPolynomial p k).coeff j • C^k‖ ≤ ((p:ℝ)*‖C‖)^k := by
  rw [norm_smul, mul_pow]
  exact mul_le_mul (norm_binomialPolynomial_coeff_le p k j) (norm_pow_le C k)
    (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem summable_coefficient_terms (C : A) (hC : (p:ℝ)*‖C‖ < 1) (j : ℕ) :
    Summable (fun k : ℕ ↦ (binomialPolynomial p k).coeff j • C^k) := by
  exact (summable_geometric_of_lt_one (by positivity) hC).of_norm_bounded
    (coefficient_term_bound p C j)

theorem interpolationCoefficient_bound (C : A) (hC : (p:ℝ)*‖C‖ < 1) (j : ℕ) :
    ‖interpolationCoefficient p C j‖ ≤
      ((p:ℝ)*‖C‖)^j * (1-(p:ℝ)*‖C‖)⁻¹ := by
  let q : ℝ := (p:ℝ)*‖C‖
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := hC
  have hsum := summable_coefficient_terms p C hC j
  have hzero : ∑ k ∈ Finset.range j, (binomialPolynomial p k).coeff j • C^k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [binomialPolynomial_coeff_eq_zero p k j (Finset.mem_range.mp hk), zero_smul]
  have hsplit := hsum.sum_add_tsum_nat_add j
  rw [hzero, zero_add] at hsplit
  rw [interpolationCoefficient, ← hsplit]
  have hbound (k : ℕ) : ‖(binomialPolynomial p (k+j)).coeff j • C^(k+j)‖ ≤ q^(k+j) :=
    coefficient_term_bound p C j (k+j)
  have hgeo : Summable (fun k : ℕ ↦ q^(k+j)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^j)
  have hnorm : Summable (fun k : ℕ ↦ ‖(binomialPolynomial p (k+j)).coeff j • C^(k+j)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hgeo
  calc
    _ ≤ ∑' k : ℕ, ‖(binomialPolynomial p (k+j)).coeff j • C^(k+j)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, q^(k+j) := hnorm.tsum_le_tsum hbound hgeo
    _ = q^j * (1-q)⁻¹ := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
      ring

/-- The resulting ordinary power series viewed as a formal multilinear series. -/
noncomputable def interpolationSeries (C : A) : FormalMultilinearSeries ℚ_[p] ℚ_[p] A :=
  fun j ↦ ContinuousMultilinearMap.mkPiRing ℚ_[p] (Fin j) (interpolationCoefficient p C j)

/-- The constructed series has radius at least two, hence is analytic around
every p-adic integer, whenever 2p‖C‖<1. -/
theorem interpolationSeries_radius (C : A) (hC : 2*((p:ℝ)*‖C‖) < 1) :
    (2 : ENNReal) ≤ (interpolationSeries p C).radius := by
  have hq0 : 0 ≤ (p:ℝ)*‖C‖ := by positivity
  have hq1 : (p:ℝ)*‖C‖ < 1 := by linarith
  apply FormalMultilinearSeries.le_radius_of_bound _ ((1-(p:ℝ)*‖C‖)⁻¹) (r := 2)
  intro j
  rw [interpolationSeries, ContinuousMultilinearMap.norm_mkPiRing]
  change ‖interpolationCoefficient p C j‖ * (2:ℝ)^j ≤ _
  calc
    _ ≤ (((p:ℝ)*‖C‖)^j * (1-(p:ℝ)*‖C‖)⁻¹) * (2:ℝ)^j :=
      mul_le_mul_of_nonneg_right (interpolationCoefficient_bound p C hq1 j) (by positivity)
    _ = (2*((p:ℝ)*‖C‖))^j * (1-(p:ℝ)*‖C‖)⁻¹ := by ring
    _ ≤ 1 * (1-(p:ℝ)*‖C‖)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sub_nonneg.mpr hq1.le))
      exact pow_le_one₀ (by positivity) hC.le
    _ = _ := one_mul _

noncomputable def analyticInterpolation (C : A) : ℚ_[p] → A :=
  (interpolationSeries p C).sum

theorem analyticInterpolation_analyticAt (C : A) (hC : 2*((p:ℝ)*‖C‖) < 1)
    (z : ℚ_[p]) (hz : ‖z‖ < 2) : AnalyticAt ℚ_[p] (analyticInterpolation p C) z := by
  have hr := interpolationSeries_radius p C hC
  apply ((interpolationSeries p C).hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num) hr)).analyticAt_of_mem
  apply lt_of_lt_of_le _ hr
  rw [edist_zero_right, ← ofReal_norm]
  exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<2)).mpr hz

end ComplexCSP.PadicInterpolation

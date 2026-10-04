import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Analytic.Basic

/-!
# P-adic binomial interpolation foundations for standalone Lemma 8.3

These are genuine factorial/coefficient estimates for the planned analytic
interpolation proof. They do not assert the finite-zero theorem and do not
assume a Skolem–Mahler–Lech or interpolation oracle.
-/

namespace ComplexCSP.PadicInterpolation

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem factorial_valuation_le (n : ℕ) : padicValNat p n.factorial ≤ n := by
  have hp1 : 1 ≤ p-1 := by have := hp.out.two_le; omega
  calc
    padicValNat p n.factorial = 1 * padicValNat p n.factorial := by omega
    _ ≤ (p-1) * padicValNat p n.factorial := Nat.mul_le_mul_right _ hp1
    _ = n - (p.digits n).sum := sub_one_mul_padicValNat_factorial n
    _ ≤ n := Nat.sub_le _ _

/-- A coarse geometric bound sufficient for a binomial interpolation radius. -/
theorem norm_inv_factorial_le (n : ℕ) :
    ‖((n.factorial : ℚ_[p])⁻¹)‖ ≤ (p:ℝ)^n := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr n.factorial_ne_zero),
    Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]
  exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (factorial_valuation_le p n)

/-- The ordinary polynomial z(z−1)…(z−n+1)/n! over Q_p. -/
noncomputable def binomialPolynomial (n : ℕ) : Polynomial ℚ_[p] :=
  C ((n.factorial : ℚ_[p])⁻¹) * descPochhammer ℚ_[p] n

/-- Each coefficient is bounded geometrically in n. The integral descending
Pochhammer polynomial contributes norm at most one. -/
theorem norm_binomialPolynomial_coeff_le (n j : ℕ) :
    ‖(binomialPolynomial p n).coeff j‖ ≤ (p:ℝ)^n := by
  rw [binomialPolynomial, coeff_C_mul, norm_mul]
  have hcoeff : ‖(descPochhammer ℚ_[p] n).coeff j‖ ≤ 1 := by
    rw [← descPochhammer_map (Int.castRingHom ℚ_[p]), coeff_map]
    exact Padic.norm_int_le_one _
  exact (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _)).trans
    (by simpa using norm_inv_factorial_le p n)

/-- At natural integers the polynomial has exactly the finite binomial value. -/
theorem binomialPolynomial_eval_nat (n k : ℕ) :
    (binomialPolynomial p k).eval (n:ℚ_[p]) = (n.choose k : ℚ_[p]) := by
  rw [binomialPolynomial, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero)]

/-- Coefficients above the finite degree vanish exactly. -/
theorem binomialPolynomial_coeff_eq_zero (n j : ℕ) (h : n < j) :
    (binomialPolynomial p n).coeff j = 0 := by
  rw [binomialPolynomial, coeff_C_mul,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero]

end ComplexCSP.PadicInterpolation

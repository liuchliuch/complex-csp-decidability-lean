import ComplexCSP.Algebra.PadicInterpolationEvaluation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Compactness turns infinitely many analytic p-adic zeros into a progression

This is an actual analytic endpoint for Lemma 8.3, not the finite-zero theorem
itself. The input is a genuinely analytic function on the unit disk. Applying
it to algebraic exponential sums still requires the good-prime/matrix bridge.
-/

namespace ComplexCSP.PadicInterpolation

open Filter Set
open scoped Topology

variable (p : ℕ) [hp : Fact p.Prime]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]

/-- Every open p-adic neighborhood of an integral point contains a whole
positive-step arithmetic progression of natural integers. -/
theorem exists_nat_progression_in_neighborhood (x : ℚ_[p]) (hx : ‖x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t : ℕ, dist ((a+d*t : ℕ):ℚ_[p]) x < ε := by
  let xi : ℤ_[p] := ⟨x,hx⟩
  obtain ⟨a,ha⟩ := PadicInt.denseRange_natCast.exists_dist_lt xi (half_pos hε)
  have ha' : dist (a:ℚ_[p]) x < ε/2 := by
    have he : dist xi (a:ℤ_[p]) = dist x (a:ℚ_[p]) := rfl
    rw [he, dist_comm] at ha
    exact ha
  obtain ⟨k,hk⟩ := PadicInt.exists_pow_neg_lt p (half_pos hε)
  refine ⟨a,p^k,pow_pos hp.out.pos _,?_⟩
  intro t
  have hnear : dist ((a+p^k*t:ℕ):ℚ_[p]) (a:ℚ_[p]) < ε/2 := by
    rw [dist_eq_norm, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_sub_cancel_left, norm_mul]
    have ht : ‖(t:ℚ_[p])‖ ≤ 1 := by
      simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (t:ℤ)
    exact (mul_le_of_le_one_right (norm_nonneg _) ht).trans_lt
      (by rwa [Padic.norm_p_pow])
  exact (dist_triangle _ (a:ℚ_[p]) x).trans_lt (by linarith)

/-- An analytic function on the p-adic unit disk with infinitely many natural
zeros vanishes on an entire natural arithmetic progression. -/
theorem progression_of_infinite_nat_zeros (f : ℚ_[p] → E)
    (hf : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → AnalyticAt ℚ_[p] f x)
    (hzero : {n : ℕ | f (n:ℚ_[p]) = 0}.Infinite) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t : ℕ, f ((a+d*t:ℕ):ℚ_[p]) = 0 := by
  let S : Set ℚ_[p] := (fun n : ℕ ↦ (n:ℚ_[p])) '' {n : ℕ | f (n:ℚ_[p]) = 0}
  have hS : S.Infinite := Set.Infinite.image Nat.cast_injective.injOn hzero
  have hsub : S ⊆ Metric.closedBall (0:ℚ_[p]) 1 := by
    rintro _ ⟨n,hn,rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (n:ℤ)
  obtain ⟨x,hx,hacc⟩ := hS.exists_accPt_of_subset_isCompact
    (isCompact_closedBall (0:ℚ_[p]) 1) hsub
  have hxn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hfreq : ∃ᶠ y in 𝓝[≠] x, f y = 0 := by
    rw [nhdsWithin, Filter.frequently_inf_principal]
    apply (accPt_iff_frequently.mp hacc).mono
    rintro y ⟨hy, n, hn, rfl⟩
    exact ⟨hy,hn⟩
  have hlocal := (hf x hxn).frequently_zero_iff_eventually_zero.mp hfreq
  obtain ⟨ε,hε,hεspec⟩ := Metric.eventually_nhds_iff.mp hlocal
  obtain ⟨a,d,hd,hprog⟩ := exists_nat_progression_in_neighborhood p x hxn ε hε
  exact ⟨a,d,hd,fun t ↦ hεspec (hprog t)⟩

/-- Analytic interpolation plus a separately proved progression obstruction
implies finiteness of natural zeros. The obstruction is not an SML assumption;
it is the elementary Vandermonde endpoint for exponential sums. -/
theorem finite_nat_zeros_of_no_progression (f : ℚ_[p] → E)
    (hf : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → AnalyticAt ℚ_[p] f x)
    (hprog : ∀ a d : ℕ, 0 < d → ∃ t : ℕ, f ((a+d*t:ℕ):ℚ_[p]) ≠ 0) :
    {n : ℕ | f (n:ℚ_[p]) = 0}.Finite := by
  by_contra h
  obtain ⟨a,d,hd,hall⟩ := progression_of_infinite_nat_zeros p f hf h
  obtain ⟨t,ht⟩ := hprog a d hd
  exact ht (hall t)

end ComplexCSP.PadicInterpolation

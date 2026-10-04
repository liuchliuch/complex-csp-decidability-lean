import ComplexCSP.Algebra.PadicInterpolationZeros
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Good primes for rational data and common small powers of integral matrices -/

namespace ComplexCSP.PadicInterpolation

open scoped BigOperators

/-- Avoiding the finite denominator gives an integral p-adic rational image. -/
theorem rational_norm_le_one_of_den_lt (q : ℚ) (p : ℕ) [hp : Fact p.Prime]
    (hq : q.den < p) : ‖(q : ℚ_[p])‖ ≤ 1 := by
  rw [Rat.cast_def, norm_div]
  have hden : ‖(q.den : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr
      (hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt q.den_pos hq))
  rw [hden, div_one]
  exact Padic.norm_int_le_one _

/-- One prime works for every member of any supplied finite rational family.
The statement constructs the prime rather than assuming a good-place oracle. -/
theorem exists_good_prime {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ (p : ℕ) (hp : p.Prime), 2 < p ∧
      letI : Fact p.Prime := ⟨hp⟩
      ∀ i, ‖(q i : ℚ_[p])‖ ≤ 1 := by
  classical
  let B := 3 + ∑ i, (q i).den
  obtain ⟨p,hpB,hp⟩ := Nat.exists_infinite_primes B
  refine ⟨p,hp,by dsimp [B] at hpB; omega,?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro i
  apply rational_norm_le_one_of_den_lt
  have hsum : (q i).den ≤ ∑ j, (q j).den := Finset.single_le_sum (f := fun j ↦ (q j).den) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  dsimp [B] at hpB
  omega

end ComplexCSP.PadicInterpolation

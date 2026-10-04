import ComplexCSP.Algebra.PadicInterpolationMatrixZeros
import ComplexCSP.Algebra.PowerSums
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finitely many zeros of nondegenerate algebraic exponential sums

This proves the standalone Lemma 8.3 route through rational regular
representation, constructed p-adic interpolation, compactness, and Vandermonde.
No Skolem–Mahler–Lech theorem, finite-zero hypothesis, or analytic interpolation
oracle is assumed.
-/

namespace ComplexCSP

open scoped BigOperators

/-- The rational regular representation preserves the entire power-sum sequence. -/
theorem matrixSequence_leftMul
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {n : ℕ} (a b : Fin n → K) (k : ℕ) :
    PadicInterpolation.matrixSequence
      (fun i ↦ Algebra.leftMulMatrix (Module.finBasis ℚ K) (b i))
      (fun i ↦ (Module.finBasis ℚ K).equivFun (a i)) k =
      (Module.finBasis ℚ K).equivFun (weightedPowerSum a b k) := by
  unfold PadicInterpolation.matrixSequence weightedPowerSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow]
  simpa only [Module.Basis.equivFun_apply, mul_comm] using
    Algebra.leftMulMatrix_mulVec_repr (Module.finBasis ℚ K) (b i^k) (a i)

/-- Finiteness in every finite rational extension. Only one coefficient needs
to be nonzero; the paper's all-nonzero hypothesis is stronger. -/
theorem finite_weightedPowerSum_zeros_numberField
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {n : ℕ} (a b : Fin n → K) (ha : ∃ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ¬ IsOfFinOrder (b i / b j)) :
    {k : ℕ | weightedPowerSum a b k = 0}.Finite := by
  classical
  let B := Module.finBasis ℚ K
  let T := fun i ↦ Algebra.leftMulMatrix B (b i)
  let S := fun i ↦ Algebra.leftMulMatrix B (b i)⁻¹
  let v := fun i ↦ B.equivFun (a i)
  have hTS : ∀ i, T i*S i=1 := by
    intro i
    dsimp [T,S]
    rw [← map_mul, mul_inv_cancel₀ (hb i), map_one]
  have hST : ∀ i, S i*T i=1 := by
    intro i
    dsimp [T,S]
    rw [← map_mul, inv_mul_cancel₀ (hb i), map_one]
  have hzero (k : ℕ) : PadicInterpolation.matrixSequence T v k = 0 ↔
      weightedPowerSum a b k = 0 := by
    rw [matrixSequence_leftMul]
    exact B.equivFun.map_eq_zero_iff
  have hf := PadicInterpolation.finite_matrixSequence_zeros
    (Module.finrank_pos (R := ℚ) (M := K)) T S v hTS hST ?_
  · simpa only [hzero] using hf
  · intro r m hm
    obtain ⟨t,ht⟩ := exists_weightedPowerSum_ne_zero_on_progression a b hb ha r m 0
      (injective_pow_of_no_torsion_ratios b hb hnd m hm)
    refine ⟨t, ?_⟩
    rw [ne_eq, hzero]
    simpa only [zero_add] using ht

/-- Standalone Lemma 8.3: a nondegenerate exponential sum of algebraic complex
numbers has only finitely many zero terms. -/
theorem finite_weightedPowerSum_zeros_algebraic
    {n : ℕ} (a b : Fin n → ℂ)
    (haAlg : ∀ i, IsAlgebraic ℚ (a i)) (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (ha : ∃ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ¬ IsOfFinOrder (b i / b j)) :
    {k : ℕ | weightedPowerSum a b k = 0}.Finite := by
  classical
  let s : Set ℂ := Set.range a ∪ Set.range b
  have hs : s.Finite := Set.finite_range a |>.union (Set.finite_range b)
  letI : Fintype s := hs.fintype
  let K := IntermediateField.adjoin ℚ s
  have hIntegral : ∀ x ∈ s, IsIntegral ℚ x := by
    rintro x (⟨i,rfl⟩|⟨i,rfl⟩)
    · exact (haAlg i).isIntegral
    · exact (hbAlg i).isIntegral
  letI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hIntegral
  let a' : Fin n → K := fun i ↦ ⟨a i, IntermediateField.subset_adjoin ℚ s (Or.inl ⟨i,rfl⟩)⟩
  let b' : Fin n → K := fun i ↦ ⟨b i, IntermediateField.subset_adjoin ℚ s (Or.inr ⟨i,rfl⟩)⟩
  have ha' : ∃ i, a' i ≠ 0 := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,fun h ↦ hi (congrArg Subtype.val h)⟩
  have hb' : ∀ i, b' i ≠ 0 := fun i h ↦ hb i (congrArg Subtype.val h)
  have hnd' : ∀ i j, i ≠ j → ¬ IsOfFinOrder (b' i/b' j) := by
    intro i j hij hfin
    apply hnd i j hij
    obtain ⟨m,hm,hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    have h := congrArg K.val hpow
    simpa only [map_pow, map_div₀, map_one] using h
  have hf := finite_weightedPowerSum_zeros_numberField a' b' ha' hb' hnd'
  have hzero (k : ℕ) : weightedPowerSum a' b' k = 0 ↔ weightedPowerSum a b k = 0 := by
    rw [← K.val.injective.eq_iff]
    simp only [weightedPowerSum, map_sum, map_mul, map_pow, map_zero]
    rfl
  simpa only [hzero] using hf

/-- Literal numbered statement of the paper: a positive number of terms and
all coefficients/bases nonzero. -/
theorem lemma_8_3 {s : ℕ} (hs : 0 < s) (a b : Fin s → ℂ)
    (haAlg : ∀ i, IsAlgebraic ℚ (a i)) (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hnd : ∀ i j, i ≠ j → ¬ IsOfFinOrder (b i / b j)) :
    {t : ℕ | (∑ i, a i * b i^t) = 0}.Finite :=
  finite_weightedPowerSum_zeros_algebraic a b haAlg hbAlg ⟨⟨0,hs⟩,ha _⟩ hb hnd

end ComplexCSP

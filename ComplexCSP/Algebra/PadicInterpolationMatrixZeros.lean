import ComplexCSP.Algebra.PadicInterpolationOperators

/-!
# Finiteness of zeros for rational matrix power sums without zero progressions

This combines the constructed p-adic interpolation, actual good-prime/common
power construction, and compactness. The progression obstruction will be
supplied by Vandermonde after the regular representation of algebraic bases.
-/

namespace ComplexCSP.PadicInterpolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {d : ℕ}

noncomputable def matrixSequence {R : Type*} [CommSemiring R]
    (T : ι → Matrix (Fin d) (Fin d) R) (v : ι → Fin d → R) (n : ℕ) : Fin d → R :=
  ∑ i, (T i^n).mulVec (v i)

theorem map_matrixSequence {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (T : ι → Matrix (Fin d) (Fin d) R)
    (v : ι → Fin d → R) (n : ℕ) (j : Fin d) :
    matrixSequence (fun i ↦ f.mapMatrix (T i)) (fun i j ↦ f (v i j)) n j =
      f (matrixSequence T v n j) := by
  simp only [matrixSequence, Finset.sum_apply, map_sum, ← map_pow]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply]

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def progressionInterpolation (T : ι → Matrix (Fin d) (Fin d) ℚ_[p])
    (v : ι → Fin d → ℚ_[p]) (M r : ℕ) (z : ℚ_[p]) : Fin d → ℚ_[p] :=
  ∑ i, ((matrixOperator p d (T i))^r)
    (analyticInterpolation p ((matrixOperator p d (T i))^M-1) z (v i))

 theorem progressionInterpolation_analytic [NeZero d]
    (T : ι → Matrix (Fin d) (Fin d) ℚ_[p]) (v : ι → Fin d → ℚ_[p])
    (M r : ℕ) (hsmall : ∀ i, 2*((p:ℝ)*‖(matrixOperator p d (T i))^M-1‖) < 1)
    (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    AnalyticAt ℚ_[p] (progressionInterpolation p T v M r) z := by
  have hsum : AnalyticAt ℚ_[p] (∑ i, fun z ↦ ((matrixOperator p d (T i))^r)
      (analyticInterpolation p ((matrixOperator p d (T i))^M-1) z (v i))) z := by
    apply Finset.analyticAt_sum
    intro i _
    have hbase := analyticInterpolation_analyticAt p ((matrixOperator p d (T i))^M-1)
      (hsmall i) z (lt_of_le_of_lt hz (by norm_num))
    have happ := ((ContinuousLinearMap.apply ℚ_[p] (Fin d → ℚ_[p]) (v i)).analyticAt _).comp hbase
    exact (((matrixOperator p d (T i))^r).analyticAt _).comp happ
  convert hsum using 1
  funext x
  simp [progressionInterpolation]

 theorem progressionInterpolation_nat [NeZero d]
    (T : ι → Matrix (Fin d) (Fin d) ℚ_[p]) (v : ι → Fin d → ℚ_[p])
    (M r : ℕ) (hsmall : ∀ i, 2*((p:ℝ)*‖(matrixOperator p d (T i))^M-1‖) < 1)
    (n : ℕ) : progressionInterpolation p T v M r (n:ℚ_[p]) = matrixSequence T v (r+M*n) := by
  unfold progressionInterpolation matrixSequence
  apply Finset.sum_congr rfl
  intro i _
  rw [analyticInterpolation_nat p _ (hsmall i)]
  rw [← add_sub_assoc, add_sub_cancel_left, ← pow_mul, ← ContinuousLinearMap.mul_apply, ← pow_add,
    ← map_pow, matrixOperator_apply]

/-- Full p-adic argument for rational matrix sums; no zero-set finiteness or
analytic interpolation hypothesis is supplied. -/
theorem finite_matrixSequence_zeros (hd : 0 < d)
    (T S : ι → Matrix (Fin d) (Fin d) ℚ) (v : ι → Fin d → ℚ)
    (hTS : ∀ i, T i*S i=1) (hST : ∀ i, S i*T i=1)
    (hprog : ∀ a b : ℕ, 0 < b → ∃ t : ℕ, matrixSequence T v (a+b*t) ≠ 0) :
    {n : ℕ | matrixSequence T v n = 0}.Finite := by
  classical
  letI : NeZero d := ⟨ne_of_gt hd⟩
  let entries : (ι × Fin d × Fin d × Bool) → ℚ :=
    fun x ↦ if x.2.2.2 then T x.1 x.2.1 x.2.2.1 else S x.1 x.2.1 x.2.2.1
  obtain ⟨p,hp,_,hgood⟩ := exists_good_prime entries
  letI : Fact p.Prime := ⟨hp⟩
  let cast : ℚ →+* ℚ_[p] := Rat.castHom ℚ_[p]
  let Tp := fun i ↦ cast.mapMatrix (T i)
  let Sp := fun i ↦ cast.mapMatrix (S i)
  let vp := fun i j ↦ cast (v i j)
  have hTp : ∀ i j k, ‖Tp i j k‖ ≤ 1 := by
    intro i j k
    simpa [Tp,cast,entries] using hgood (i,j,k,true)
  have hSp : ∀ i j k, ‖Sp i j k‖ ≤ 1 := by
    intro i j k
    simpa [Sp,cast,entries] using hgood (i,j,k,false)
  have hTSp : ∀ i, Tp i*Sp i=1 := by
    intro i
    change cast.mapMatrix (T i) * cast.mapMatrix (S i) = 1
    rw [← map_mul,hTS,map_one]
  have hSTp : ∀ i, Sp i*Tp i=1 := by
    intro i
    change cast.mapMatrix (S i) * cast.mapMatrix (T i) = 1
    rw [← map_mul,hST,map_one]
  have hzero (n : ℕ) : matrixSequence Tp vp n = 0 ↔ matrixSequence T v n = 0 := by
    constructor
    · intro h
      funext j
      apply cast.injective
      have hj := congrFun h j
      change matrixSequence (fun i ↦ cast.mapMatrix (T i)) (fun i j ↦ cast (v i j)) n j = 0 at hj
      rw [map_matrixSequence] at hj
      simpa only [Pi.zero_apply, map_zero] using hj
    · intro h
      funext j
      rw [map_matrixSequence, h]
      exact map_zero cast
  obtain ⟨M,hM,hsmall⟩ := exists_common_small_operator_power p Tp Sp hTp hSp hTSp hSTp
  have hfinite (r : Fin M) : {n : ℕ | matrixSequence T v (r.val+M*n)=0}.Finite := by
    have hf := finite_nat_zeros_of_no_progression p
      (progressionInterpolation p Tp vp M r.val)
      (progressionInterpolation_analytic p Tp vp M r.val hsmall) ?_
    · simpa only [progressionInterpolation_nat p Tp vp M r.val hsmall, hzero] using hf
    · intro a b hb
      obtain ⟨t,ht⟩ := hprog (r.val+M*a) (M*b) (Nat.mul_pos hM hb)
      refine ⟨t, ?_⟩
      rw [progressionInterpolation_nat p Tp vp M r.val hsmall, ne_eq, hzero]
      have he : r.val+M*(a+b*t) = r.val+M*a+M*b*t := by ring
      simpa only [he] using ht
  have hcover : {n : ℕ | matrixSequence T v n=0} ⊆
      ⋃ r : Fin M, (fun n ↦ r.val+M*n) '' {n : ℕ | matrixSequence T v (r.val+M*n)=0} := by
    intro n hn
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n%M,Nat.mod_lt _ hM⟩, n/M, ?_, ?_⟩
    · change matrixSequence T v (n%M+M*(n/M)) = 0
      rw [Nat.mod_add_div]
      exact hn
    · exact Nat.mod_add_div _ _
  exact (Set.finite_iUnion (fun r ↦ (hfinite r).image (fun n ↦ r.val+M*n))).subset hcover

end ComplexCSP.PadicInterpolation

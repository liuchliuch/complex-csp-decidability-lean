import ComplexCSP.Algebra.PadicInterpolationGoodPrime

/-!
# Finite residue matrix groups supply powers arbitrarily close to identity

The exponent is the cardinality of the actual finite unit group over Z/p^N.
No near-identity power or p-adic interpolation is supplied as an oracle.
-/

namespace ComplexCSP.PadicInterpolation

open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

/-- All invertible integral matrices of a fixed size have one common positive
power congruent to identity modulo p^N, with the corresponding norm bound. -/
theorem exists_common_integral_matrix_power (d N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (U : (Matrix (Fin d) (Fin d) ℤ_[p])ˣ) (i j : Fin d),
      ‖(U.val^M - 1) i j‖ ≤ (p:ℝ)^(-(N:ℤ)) := by
  classical
  letI : NeZero (p^N) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let G := (Matrix (Fin d) (Fin d) (ZMod (p^N)))ˣ
  let M := Fintype.card G
  have hM : 0 < M := Fintype.card_pos
  refine ⟨M,hM,?_⟩
  intro U i j
  let reduction : Matrix (Fin d) (Fin d) ℤ_[p] →+* Matrix (Fin d) (Fin d) (ZMod (p^N)) :=
    (PadicInt.toZModPow N).mapMatrix
  let v : G := Units.map reduction.toMonoidHom U
  have hv : v^M = 1 := pow_card_eq_one
  have hmatrix : reduction (U.val^M - 1) = 0 := by
    have hpow : reduction U.val ^ M = 1 := by
      simpa only [v, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one,
        MonoidHom.coe_coe] using congrArg Units.val hv
    rw [map_sub, map_pow, map_one, hpow, sub_self]
  have hentry : PadicInt.toZModPow N ((U.val^M-1) i j) = 0 := by
    exact congrArg (fun A : Matrix (Fin d) (Fin d) (ZMod (p^N)) ↦ A i j) hmatrix
  apply (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
  exact hentry

/-- Lift a matrix whose entries lie in the p-adic integer disk. -/
noncomputable def integralMatrix {d : ℕ} (T : Matrix (Fin d) (Fin d) ℚ_[p])
    (hT : ∀ i j, ‖T i j‖ ≤ 1) : Matrix (Fin d) (Fin d) ℤ_[p] :=
  fun i j ↦ ⟨T i j,hT i j⟩

@[simp] theorem integralMatrix_coe {d : ℕ} (T : Matrix (Fin d) (Fin d) ℚ_[p])
    (hT : ∀ i j, ‖T i j‖ ≤ 1) :
    PadicInt.Coe.ringHom.mapMatrix (integralMatrix p T hT) = T := rfl

/-- An integral matrix with integral inverse is an actual unit matrix. -/
noncomputable def integralMatrixUnit {d : ℕ} (T S : Matrix (Fin d) (Fin d) ℚ_[p])
    (hT : ∀ i j, ‖T i j‖ ≤ 1) (hS : ∀ i j, ‖S i j‖ ≤ 1)
    (hTS : T*S=1) (hST : S*T=1) : (Matrix (Fin d) (Fin d) ℤ_[p])ˣ where
  val := integralMatrix p T hT
  inv := integralMatrix p S hS
  val_inv := by
    apply Matrix.map_injective (f := fun z : ℤ_[p] ↦ (z:ℚ_[p])) Subtype.coe_injective
    change PadicInt.Coe.ringHom.mapMatrix (_*_) = PadicInt.Coe.ringHom.mapMatrix 1
    rw [map_mul, map_one, integralMatrix_coe, integralMatrix_coe, hTS]
  inv_val := by
    apply Matrix.map_injective (f := fun z : ℤ_[p] ↦ (z:ℚ_[p])) Subtype.coe_injective
    change PadicInt.Coe.ringHom.mapMatrix (_*_) = PadicInt.Coe.ringHom.mapMatrix 1
    rw [map_mul, map_one, integralMatrix_coe, integralMatrix_coe, hST]

/-- Corresponding statement directly for arbitrary Q_p matrices with integral
entries and integral inverse entries, simultaneously for every family index. -/
theorem exists_common_matrix_power {ι : Type*} {d : ℕ}
    (T S : ι → Matrix (Fin d) (Fin d) ℚ_[p])
    (hT : ∀ a i j, ‖T a i j‖ ≤ 1) (hS : ∀ a i j, ‖S a i j‖ ≤ 1)
    (hTS : ∀ a, T a*S a=1) (hST : ∀ a, S a*T a=1) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ a i j, ‖(T a^M - 1) i j‖ ≤ (p:ℝ)^(-(N:ℤ)) := by
  obtain ⟨M,hM,hbound⟩ := exists_common_integral_matrix_power p d N
  refine ⟨M,hM,?_⟩
  intro a i j
  let U := integralMatrixUnit p (T a) (S a) (hT a) (hS a) (hTS a) (hST a)
  have hcoe : PadicInt.Coe.ringHom.mapMatrix (U.val^M-1) = T a^M-1 := by
    rw [map_sub, map_pow, map_one]
    rfl
  have hentry : (((U.val^M-1) i j : ℤ_[p]) : ℚ_[p]) = (T a^M-1) i j :=
    congrArg (fun A : Matrix (Fin d) (Fin d) ℚ_[p] ↦ A i j) hcoe
  rw [← hentry, ← PadicInt.norm_def]
  exact hbound U i j

end ComplexCSP.PadicInterpolation

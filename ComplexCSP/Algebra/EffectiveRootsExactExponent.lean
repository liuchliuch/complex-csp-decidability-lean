import ComplexCSP.Algebra.EffectiveRootsChecked
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The computed root exponent is exactly the paper's number-field exponent

Computed root coordinates are bijective with integral torsion units. Cyclicity
then identifies their common cardinality with the actual root-group exponent.
-/
namespace ComplexCSP.EffectiveRoots
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K]

private theorem torsionUnit_finite_order (u : NumberField.Units.torsion K) :
    IsOfFinOrder (u.val : K) := by
  have hu := (CommGroup.mem_torsion (𝓞 K)ˣ u.val).mp u.property
  exact ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).isOfFinOrder hu

/-- Lift every finite-order field scalar to an actual integral torsion unit. -/
theorem exists_torsionUnit_of_finite_order (x : K) (hx : IsOfFinOrder x) :
    ∃ u : NumberField.Units.torsion K, (u.val : K) = x := by
  let y : 𝓞 K := ⟨x, RowDetector.isIntegral_int_of_isOfFinOrder x hx⟩
  have hy : IsOfFinOrder y := by
    obtain ⟨m, hm, hp⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, Subtype.ext hp⟩
  let u : (𝓞 K)ˣ := hy.unit
  have humem : u ∈ NumberField.Units.torsion K := by
    apply (CommGroup.mem_torsion (𝓞 K)ˣ u).mpr
    exact Units.isOfFinOrder_val.mp hy
  exact ⟨⟨u, humem⟩, rfl⟩

/-- The exact coordinate map is bijective; surjectivity uses the proved finite
order of each computed root and its integral-unit lift. -/
noncomputable def torsionUnitsEquivCoordinates (pb : PowerBasis ℚ K)
    (p : Polynomial ℤ) (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : Fin pb.dim → ℤ) (hcoeff : ∀ i, p.coeff i.val = a i) :
    NumberField.Units.torsion K ≃ ↥(rootCoordinatesFromCoefficients pb.dim a) := by
  let f : NumberField.Units.torsion K → ↥(rootCoordinatesFromCoefficients pb.dim a) :=
    fun u => ⟨pb.basis.equivFun (u.val : K),
      (mem_rootCoordinatesFromCoefficients_iff pb p hp hroot hpoly a hcoeff _).mpr (by
        rw [EncodedNumberField.interpret_coordinates]
        exact torsionUnit_finite_order u)⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v huv
    apply Subtype.ext
    apply NumberField.Units.coe_injective K
    apply pb.basis.equivFun.injective
    exact congrArg Subtype.val huv
  · intro v
    have hv := (mem_rootCoordinatesFromCoefficients_iff pb p hp hroot hpoly a hcoeff v.val).mp v.property
    obtain ⟨u, hu⟩ := exists_torsionUnit_of_finite_order _ hv
    refine ⟨u, ?_⟩
    apply Subtype.ext
    dsimp [f]
    rw [hu]
    exact EncodedNumberField.coordinates_interpret pb v.val

theorem presentation_rootCount_eq_torsionOrder {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) :
    (rootCoordinatesFromCoefficients n a).card = NumberField.Units.torsionOrder K := by
  obtain ⟨b, hb, p, hp, hroot, hpoly, hcoeff⟩ := h
  let pb : PowerBasis ℚ K := ⟨α, n, b, hb⟩
  simpa only [NumberField.Units.torsionOrder, Fintype.card_coe] using
    (Fintype.card_congr (torsionUnitsEquivCoordinates pb p hp hroot hpoly a hcoeff)).symm

/-- Cyclicity identifies the mathematical root-group exponent with its order. -/
theorem torsion_exponent_eq_order :
    Monoid.exponent (NumberField.Units.torsion K) = NumberField.Units.torsionOrder K := by
  simpa only [Nat.card_eq_fintype_card, NumberField.Units.torsionOrder] using
    (IsCyclic.exponent_eq_card (α := NumberField.Units.torsion K))

theorem presentation_rootExponent_eq_fieldExponent {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) :
    rootExponentFromCoefficients n a = RowDetector.fieldExponent K := by
  simp only [rootExponentFromCoefficients, RowDetector.fieldExponent,
    presentation_rootCount_eq_torsionOrder h]

/-- Exact Kμ for the validated executable field; no larger exponent substituted. -/
theorem checkedRootExponent_eq_fieldExponent {n : ℕ} (a : Fin n → ℤ)
    [Fact (EncodedNumberField.Element.Valid n (coefficientRelation a))]
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    rootExponentFromCoefficients n a = RowDetector.fieldExponent
      (EncodedNumberField.Element n (coefficientRelation a)) :=
  presentation_rootExponent_eq_fieldExponent
    (EncodedNumberField.Element.integralPresentation_of_checkedTail a ha)

end ComplexCSP.EffectiveRoots

import ComplexCSP.Recognition.IdentityOracle
import ComplexCSP.Recognition.DegreeConditionsTransport

/-! # Exact recognition: exact transport of arbitrary star-polynomial identities -/
namespace ComplexCSP.Recognition
open scoped BigOperators

variable {D K R ι V : Type} {n : ℕ}
variable [Field K] [StarRing K] [Field R] [StarRing R]

/-- Coefficients and formally independent direct/conjugate coordinates transport
along a genuine conjugation-preserving field embedding. -/
theorem map_pinned_program_eval (φ : K →+* R) (hφ : ∀ x, φ (star x) = star (φ x))
    (G : (V → D) → K) (coords : Fin n → PinnedCoordinate V D)
    (P : PolynomialPrograms.Program K n) :
    φ (PolynomialPrograms.eval (fun j => Sum.elim G (fun a => star (G a)) (coords j)) P) =
      PolynomialPrograms.eval
        (fun j => Sum.elim (fun a => φ (G a)) (fun a => star (φ (G a))) (coords j))
        (PolynomialPrograms.mapCoefficients φ P) := by
  simp only [PolynomialPrograms.eval, PolynomialPrograms.interpret_mapCoefficients,
    RingHom.id_comp]
  rw [PolynomialPrograms.map_interpret, RingHom.comp_id]
  congr 1
  funext j
  cases coords j <;> simp only [Sum.elim_inl, Sum.elim_inr, hφ]

variable [Fintype D]

/-- All literal finite instances are preserved and reflected by coefficient
transport. No bound or syntactic identification of instances is assumed. -/
theorem all_instance_identity_map_iff (L : Language D K ι)
    (φ : K →+* R) (hφ : ∀ x, φ (star x) = star (φ x))
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    (∀ h : ℕ, ∀ I : Instance L V (Fin h),
      PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
        (coords j)) P = 0) ↔
    (∀ h : ℕ, ∀ I : Instance (L.mapValues φ) V (Fin h),
      PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
        (coords j)) (PolynomialPrograms.mapCoefficients φ P) = 0) := by
  constructor
  · intro h hcount I
    have he := congrArg φ (h hcount (I.sourceValues φ))
    rw [map_pinned_program_eval φ hφ] at he
    simpa only [Instance.partition_sourceValues, map_zero] using he
  · intro h hcount I
    apply φ.injective
    rw [map_zero, map_pinned_program_eval φ hφ]
    have hp : (I.mapValues φ).partition = fun a => φ (I.partition a) :=
      funext (I.partition_mapValues φ)
    simpa only [hp] using h hcount (I.mapValues φ)

variable [DecidableEq V]

/-- Exact occurrence-degree restrictions survive the same transport. -/
theorem degree_instance_identity_map_iff (L : Language D K ι)
    (φ : K →+* R) (hφ : ∀ x, φ (star x) = star (φ x)) (δ : ℕ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    (∀ h : ℕ, ∀ I : Instance L V (Fin h), I.DegreeDivisible δ →
      PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
        (coords j)) P = 0) ↔
    (∀ h : ℕ, ∀ I : Instance (L.mapValues φ) V (Fin h), I.DegreeDivisible δ →
      PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
        (coords j)) (PolynomialPrograms.mapCoefficients φ P) = 0) := by
  constructor
  · intro h hcount I hI
    have he := congrArg φ (h hcount (I.sourceValues φ)
      ((Instance.degreeDivisible_sourceValues_iff φ I δ).mpr hI))
    rw [map_pinned_program_eval φ hφ] at he
    simpa only [Instance.partition_sourceValues, map_zero] using he
  · intro h hcount I hI
    apply φ.injective
    rw [map_zero, map_pinned_program_eval φ hφ]
    have hp : (I.mapValues φ).partition = fun a => φ (I.partition a) :=
      funext (I.partition_mapValues φ)
    simpa only [hp] using h hcount (I.mapValues φ)
      ((Instance.degreeDivisible_mapValues_iff I φ δ).mpr hI)

end ComplexCSP.Recognition

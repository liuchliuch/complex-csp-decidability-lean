import ComplexCSP.Algebra.LegalPurificationTables

/-! # Every clause of Lemma 3.1 for actual legal ambient purifications

The global BO equivalence already follows from the structural map theorem. This
file exposes the stronger, individual positive-magnitude-block vanishing clause,
and connects all clauses to arbitrary actual legal generating sets and tables.
-/
namespace ComplexCSP.Purification.PurificationMap
open BlockOrthogonality RowTypes
open scoped BigOperators

variable {Γ : Type*} [CommGroup Γ] {original : Γ →* ℂˣ}

/-- A single positive block has the same vanishing Hermitian sum, without an
assumption about any other block. -/
theorem blockSum_zero_iff (P Q : PurificationMap Γ original)
    {D : Type*} [Fintype D] (a b : D → Option Γ)
    (hmag : MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b))
    (z : D) (hz : P.entry (a z) ≠ 0) :
    hermitianSum (P.entry ∘ a) (P.entry ∘ b) (magnitudeBlock (P.entry ∘ a) z) = 0 ↔
      hermitianSum (Q.entry ∘ a) (Q.entry ∘ b) (magnitudeBlock (Q.entry ∘ a) z) = 0 := by
  classical
  have hzQ : Q.entry (a z) ≠ 0 := by simpa only [entry_ne_zero_iff] using hz
  have hs := magnitudeProportional_support_eq hmag
  have hbz : P.entry (b z) ≠ 0 := by
    change z ∈ support (P.entry ∘ b)
    rw [← hs]
    exact hz
  have hbzQ : Q.entry (b z) ≠ 0 := by simpa only [entry_ne_zero_iff] using hbz
  let B := magnitudeBlock (P.entry ∘ a) z
  have hna : ∀ w ∈ B, ‖P.entry (a w)‖ = ‖P.entry (a z)‖ := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hnb : ∀ w ∈ B, ‖P.entry (b w)‖ = ‖P.entry (b z)‖ := by
    obtain ⟨c,hc,hmag⟩ := hmag
    intro w hw
    apply (mul_right_inj' (ne_of_gt hc)).mp
    exact (hmag w).symm.trans ((hna w hw).trans (hmag z))
  let c := Q.entry (a z) / P.entry (a z)
  let d := Q.entry (b z) / P.entry (b z)
  have hc : c ≠ 0 := div_ne_zero hzQ hz
  have hd : d ≠ 0 := div_ne_zero hbzQ hbz
  have he : hermitianSum (Q.entry ∘ a) (Q.entry ∘ b) B =
      (c * star d) * hermitianSum (P.entry ∘ a) (P.entry ∘ b) B := by
    simp only [hermitianSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    dsimp only [Function.comp_apply]
    rw [P.entry_rescale_of_norm_eq Q (a w) (a z) (hna w hw) hzQ,
      P.entry_rescale_of_norm_eq Q (b w) (b z) (hnb w hw) hbzQ, star_mul]
    dsimp only [Function.comp_apply, c, d]
    ring
  rw [← P.magnitudeBlock_entry Q a z]
  change _ = 0 ↔ hermitianSum (Q.entry ∘ a) (Q.entry ∘ b) B = 0
  rw [he, mul_eq_zero]
  simp [hc, hd, B]

/-- Positive magnitude proportionality also transfers when a row is zero. -/
theorem magnitudeProportional_entry_iff_all (P Q : PurificationMap Γ original)
    {D : Type*} (a b : D → Option Γ) :
    MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b) ↔
      MagnitudeProportional (Q.entry ∘ a) (Q.entry ∘ b) := by
  by_cases ha : P.entry ∘ a = 0
  · have haQ := (P.row_zero_iff Q a).mp ha
    rw [ha,haQ]
    have hz (u : D → ℂ) : MagnitudeProportional 0 u ↔ u = 0 := by
      constructor
      · rintro ⟨c,hc,h⟩
        funext z
        have ht := h z
        simp only [Pi.zero_apply,norm_zero] at ht
        have hu : ‖u z‖ = 0 := (mul_eq_zero.mp ht.symm).resolve_left (ne_of_gt hc)
        exact norm_eq_zero.mp hu
      · intro hu
        subst u
        exact ⟨1,by norm_num,by simp⟩
    rw [hz,hz]
    exact P.row_zero_iff Q b
  by_cases hb : P.entry ∘ b = 0
  · have hbQ := (P.row_zero_iff Q b).mp hb
    have hz (u : D → ℂ) : MagnitudeProportional u 0 ↔ u = 0 := by
      constructor
      · rintro ⟨c,hc,h⟩
        funext z
        have ht := h z
        simpa only [Pi.zero_apply,norm_zero,mul_zero,norm_eq_zero] using ht
      · intro hu
        subst u
        exact ⟨1,by norm_num,by simp⟩
    rw [hb,hbQ,hz,hz]
    exact P.row_zero_iff Q a
  exact P.magnitudeProportional_entry_iff Q a b ha hb

end ComplexCSP.Purification.PurificationMap

namespace ComplexCSP
open BlockOrthogonality RowTypes

/-- The conclusions of Lemma 3.1, packaged only as theorem output. This is not
an input interface that assumes ambient invariance. -/
structure AmbientTableAgreement {X D : Type*} [Fintype D] (P Q : X → D → ℂ) : Prop where
  supports : ∀ x, support (P x) = support (Q x)
  magnitude_proportional : ∀ x y, MagnitudeProportional (P x) (P y) ↔
    MagnitudeProportional (Q x) (Q y)
  proportional : ∀ x y, P x ≠ 0 → P y ≠ 0 →
    (Proportional (P x) (P y) ↔ Proportional (Q x) (Q y))
  blocks : ∀ x z, magnitudeBlock (P x) z = magnitudeBlock (Q x) z
  block_sum : ∀ x y, MagnitudeProportional (P x) (P y) → ∀ z, P x z ≠ 0 →
    (hermitianSum (P x) (P y) (magnitudeBlock (P x) z) = 0 ↔
      hermitianSum (Q x) (Q y) (magnitudeBlock (Q x) z) = 0)
  block_orthogonal : BlockOrthogonal P ↔ BlockOrthogonal Q

namespace GeneratingSet.LegalGeneratingSet
variable {X D : Type*} [Fintype D] {S T : Finset ℂˣ}

/-- All individual clauses for two arbitrary actual legal ambient choices. -/
theorem table_ambient_agreement (L : LegalGeneratingSet S) (M : LegalGeneratingSet T)
    (G : X → D → ℂ) (hS : ContainsTable S G) (hT : ContainsTable T G) :
    AmbientTableAgreement (L.purifyTable G hS) (M.purifyTable G hT) := by
  let P := L.tableMap G hS
  let Q := M.tableMap G hT
  let A := Purification.PurificationMap.encodeTable G
  change AmbientTableAgreement (fun x => P.entry ∘ A x) (fun x => Q.entry ∘ A x)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x
    simp only [Purification.PurificationMap.support_entry]
  · intro x y
    exact P.magnitudeProportional_entry_iff_all Q (A x) (A y)
  · intro x y hx hy
    exact P.proportional_entry_iff Q (A x) (A y) hx hy
  · intro x z
    exact P.magnitudeBlock_entry Q (A x) z
  · intro x y hmag z hz
    exact P.blockSum_zero_iff Q (A x) (A y) hmag z hz
  · exact P.blockOrthogonal_iff Q A

end GeneratingSet.LegalGeneratingSet

namespace AmbientTableAgreement
variable {X D : Type*} [Fintype D] {P Q : X → D → ℂ}

/-- Disjointness is one of the literal consequences of support agreement. -/
theorem disjoint_iff (h : AmbientTableAgreement P Q) (x y : X) :
    Disjoint (support (P x)) (support (P y)) ↔ Disjoint (support (Q x)) (support (Q y)) := by
  rw [h.supports,h.supports]

/-- Every clause persists under independent nonzero table-wide scales. -/
theorem scale (h : AmbientTableAgreement P Q) {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    AmbientTableAgreement (fun x => BlockOrthogonality.scale c (P x))
      (fun x => BlockOrthogonality.scale d (Q x)) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x
    rw [support_scale hc,support_scale hd,h.supports]
  · intro x y
    rw [magnitudeProportional_scale_iff hc,magnitudeProportional_scale_iff hd]
    exact h.magnitude_proportional x y
  · intro x y hx hy
    rw [proportional_scale_iff hc,proportional_scale_iff hd]
    exact h.proportional x y ((scale_ne_zero_iff hc _).mp hx) ((scale_ne_zero_iff hc _).mp hy)
  · intro x z
    rw [magnitudeBlock_scale hc,magnitudeBlock_scale hd,h.blocks]
  · intro x y hmag z hz
    have hm := (magnitudeProportional_scale_iff hc _ _).mp hmag
    have hz' : P x z ≠ 0 := fun he => hz (by simp [BlockOrthogonality.scale,he])
    rw [magnitudeBlock_scale hc,magnitudeBlock_scale hd,hermitianSum_scale,hermitianSum_scale]
    simpa only [mul_eq_zero, star_eq_zero, hc, hd, false_or] using h.block_sum x y hm z hz'
  · rw [blockOrthogonal_scale_iff hc,blockOrthogonal_scale_iff hd]
    exact h.block_orthogonal

end AmbientTableAgreement

namespace GeneratingSet.LegalGeneratingSet
variable {X D : Type*} [Fintype D] {S T : Finset ℂˣ}

/-- Literal Lemma 3.1 with printed purification or positive normalization. -/
theorem table_normalized_ambient_agreement
    (L : LegalGeneratingSet S) (M : LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ContainsTable S G) (hT : ContainsTable T G)
    {N K : ℝ} (hN : 0 < N) (hK : 0 < K) :
    AmbientTableAgreement (fun x z => (N : ℂ) * L.purifyTable G hS x z)
      (fun x z => (K : ℂ) * M.purifyTable G hT x z) :=
  (L.table_ambient_agreement M G hS hT).scale
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hN)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hK))

end GeneratingSet.LegalGeneratingSet
end ComplexCSP

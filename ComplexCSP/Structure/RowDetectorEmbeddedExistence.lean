import ComplexCSP.Structure.RowEquivalenceRealization
import ComplexCSP.Instances.ValueTransport

/-!
# Row detectors for an explicit embedded coefficient field

The exponent is supplied as finite arithmetic data with its algebraic torsion
property, rather than silently replaced by the exponent of a larger field.
Purification and all support assertions are derived from the actual language.
Only characteristic zero and the explicit torsion property are needed below;
in particular these results apply to every actual number field.
-/
namespace ComplexCSP.RowDetectorEmbeddedExistence

open BlockOrthogonality RowTypes RowPhases RowDetector
open Purification PurificationMap RowEquivalenceRealization
open scoped BigOperators

universe u v

/-- A supplied torsion exponent also kills finite-order complex elements in the
actual coefficient subfield. -/
theorem subfield_torsion_power (K : Subfield ℂ) (E : ℕ)
    (hkill : KillsTorsion K E) {z : ℂ} (hz : z ∈ K) (ht : IsOfFinOrder z) :
    z ^ E = 1 := by
  let x : K := ⟨z, hz⟩
  have hx : IsOfFinOrder x := K.subtype.injective.isOfFinOrder_iff.mp ht
  exact congrArg Subtype.val (hkill x hx)

/-- Independent overlapping rows contribute zero to every permitted detector
exponent. All block invariants are derived from legal purification structure. -/
theorem independent_detector_zero_of_exponent {X : Type u} {D : Type v} [Fintype D]
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (hP : BlockOrthogonal (PurificationMap.purifyTable G P))
    (hpow : ∀ h, 0 < h → h ≤ Fintype.card D → BlockOrthogonal (fun x z => G x z ^ h))
    (K : Subfield ℂ) (hK : ∀ x z, G x z ∈ K) (E : ℕ) (hE : 2 ≤ E)
    (hkill : KillsTorsion K E)
    (x y : X) (z₀ : D) (hx : G x z₀ ≠ 0) (hy : G y z₀ ≠ 0)
    (hind : ¬ Proportional (G x) (G y)) (t : ℕ) :
    detector (G x) (G y) E
      (1 + phaseExponent (Fintype.card D) * t) = 0 := by
  classical
  let U := PurificationMap.purifyTable G P
  let L := phaseExponent (Fintype.card D)
  let lam := anchorScalar (G x) (G y) z₀
  let ζ := anchoredPhase (G x) (G y) z₀
  obtain ⟨hsupport, hlam, _, hphase⟩ := finite_row_phases_of_power_BO G hpow x y z₀ hx hy
  have hxP : U x z₀ ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P x z₀)).mpr hx
  have hyP : U y z₀ ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P y z₀)).mpr hy
  have hmag := magnitudeProportional_of_overlap hP.1 x y z₀ hxP hyP
  have hxrow : U x ≠ 0 := by intro he; exact hxP (congrFun he z₀)
  have hyrow : U y ≠ 0 := by intro he; exact hyP (congrFun he z₀)
  have horth : VectorBlockOrthogonal (U x) (U y) := by
    rcases hP.2 x y hxrow hyrow hmag with hdep | ho
    · exfalso
      apply hind
      have hh := P.source_proportional_of (encodeTable G x) (encodeTable G y) hxrow hyrow hdep
      simpa only [Function.comp_def, source_encodeTable] using hh
    · exact ho
  let S : Finset D := Finset.univ.filter fun z => G x z ≠ 0
  let f : D → ℝ := fun z => ‖U x z‖
  let g : D → ℂ := fun z => G x z ^ ((E - 1) * (1 + L * t)) * G y z ^ (1 + L * t)
  have hrestrict : detector (G x) (G y) E (1 + L * t) = ∑ z ∈ S, g z := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    have hu : G x z = 0 := by simpa [S] using hz
    have hexp : (E - 1) * (1 + L * t) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    change g z = 0
    simp only [g, hu, zero_pow hexp, zero_mul]
  rw [hrestrict, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f)
    (g := f) (fun z hz => Finset.mem_image_of_mem f hz) g]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hwG : G x w ≠ 0 := (Finset.mem_filter.mp hw).2
  have hwP : U x w ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P x w)).mpr hwG
  have hfilter : S.filter (fun z => f z = f w) = BlockOrthogonality.magnitudeBlock (U x) w := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hz⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    · intro hz
      have hnorm := (Finset.mem_filter.mp hz).2
      have hzP : U x z ≠ 0 := by
        intro hzero
        have hwzero : ‖U x w‖ = 0 := by simpa [hzero] using hnorm.symm
        exact hwP (norm_eq_zero.mp hwzero)
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (not_congr (purifiedTable_eq_zero_iff G P x z)).mp hzP⟩, hnorm⟩
  rw [hfilter]
  let B := BlockOrthogonality.magnitudeBlock (U x) w
  have hBnonzero : ∀ z ∈ B, G x z ≠ 0 := by
    intro z hz
    have hmem : z ∈ S.filter (fun z => f z = f w) := hfilter.symm ▸ hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hnormP : ∀ z ∈ B, ‖U x z‖ = ‖U x w‖ := fun z hz => (Finset.mem_filter.mp hz).2
  have hnormG : ∀ z ∈ B, ‖G x z‖ = ‖G x w‖ := by
    intro z hz
    have hn := P.source_norm_eq_of (hnormP z hz)
    simpa only [source_encodeTable] using hn
  have hsum : hermitianSum (G x) (G y) B = 0 := by
    have hh := P.source_sum_on_purified_block (encodeTable G x) (encodeTable G y) hmag horth w hwP
    simpa only [Function.comp_def, source_encodeTable] using hh
  apply detector_block_eq_zero (G x) (G y) ζ B lam (G x w ^ E) E L t (by omega)
  · intro z hz
    exact (hphase z (hBnonzero z hz)).1
  · intro z hz
    exact (hphase z (hBnonzero z hz)).2.2
  · intro z hz
    have ht : IsOfFinOrder (G x z / G x w) := by
      have hh := source_ratio_finite_order P (encodeTable G x z) (encodeTable G x w)
        (by simpa only [source_encodeTable] using hwG) (hnormP z hz)
      simpa only [source_encodeTable] using hh
    have hp := subfield_torsion_power K E hkill (K.div_mem (hK x z) (hK x w)) ht
    rw [div_pow] at hp
    exact (div_eq_one_iff_eq (pow_ne_zero E hwG)).mp hp
  · exact phase_sum_zero (G x) (G y) ζ B w lam hwG hlam
      (fun z hz => (hphase z (hBnonzero z hz)).1) hnormG hsum

/-- One bounded finite simultaneous search makes the pure power sum nonzero on
every nonzero row, using the explicit coefficient subfield and its torsion exponent. -/
theorem exists_nonzero_row_sums_of_exponent {X : Type u} {D : Type v} [Fintype X] [Fintype D]
    (G : X → D → ℂ) (K : Subfield ℂ)
    (hK : ∀ x z, G x z ∈ K) (E : ℕ) (hE : 2 ≤ E)
    (hkill : KillsTorsion K E) (L : ℕ) (hL : 0 < L) :
    ∃ t : ℕ, ∀ x, G x ≠ 0 →
      powerSum (fun z => G x z ^ E) (1 + L * t) ≠ 0 := by
  classical
  let R := {x : X // G x ≠ 0}
  let Z : R → Type v := fun x => {z : D // G x.val z ≠ 0}
  letI : ∀ x : R, Nonempty (Z x) := fun x => by
    have h : ∃ z, G x.val z ≠ 0 := by
      by_contra! hz
      exact x.property (funext hz)
    obtain ⟨z, hz⟩ := h
    exact ⟨⟨z, hz⟩⟩
  let u : ∀ x : R, Z x → K := fun x z => ⟨G x.val z.val, hK _ _⟩
  have hu : ∀ x z, u x z ≠ 0 := by
    intro x z hz
    exact z.property (congrArg Subtype.val hz)
  obtain ⟨t, _, ht⟩ := exists_simultaneous_detector_time u hu E L (by omega) hL hkill
  refine ⟨t, ?_⟩
  intro x hx
  let xr : R := ⟨x, hx⟩
  have hmap : (∑ z : Z xr, (G x z.val ^ E) ^ (1 + L * t)) ≠ 0 := by
    have hnonzero : K.subtype (powerSum (fun z => u xr z ^ E) (1 + L * t)) ≠ 0 := by
      intro hz
      exact ht xr (K.subtype.injective (by simpa using hz))
    simpa only [powerSum, map_sum, map_pow, Subfield.subtype_apply, u] using hnonzero
  have heq : powerSum (fun z => G x z ^ E) (1 + L * t) =
      ∑ z : Z xr, (G x z.val ^ E) ^ (1 + L * t) := by
    let S := Finset.univ.filter fun z => G x z ≠ 0
    calc
      _ = ∑ z ∈ S, (G x z ^ E) ^ (1 + L * t) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro z _ hz
        have hzG : G x z = 0 := by simpa [S] using hz
        rw [hzG, zero_pow (by omega), zero_pow (by omega)]
      _ = _ := Finset.sum_subtype S (fun z => by simp [S, xr]) _
  exact heq ▸ hmap

/-- The detector support is exactly the nonzero proportional-row relation,
with no support classification supplied as a hypothesis. -/
theorem exists_detector_support_of_exponent {X : Type u} {D : Type v} [Fintype X] [Fintype D]
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (hP : BlockOrthogonal (PurificationMap.purifyTable G P))
    (hpow : ∀ h, 0 < h → h ≤ Fintype.card D → BlockOrthogonal (fun x z => G x z ^ h))
    (K : Subfield ℂ) (hK : ∀ x z, G x z ∈ K) (E : ℕ) (hE : 2 ≤ E)
    (hkill : KillsTorsion K E) :
    ∃ t : ℕ, ∀ x y,
      detector (G x) (G y) E (1 + phaseExponent (Fintype.card D) * t) ≠ 0 ↔
        NonzeroProportionalRows G x y := by
  obtain ⟨t, ht⟩ := exists_nonzero_row_sums_of_exponent G K hK E hE hkill _ (phaseExponent_pos _)
  refine ⟨t, ?_⟩
  intro x y
  constructor
  · intro hnonzero
    by_contra hnot
    apply hnonzero
    by_cases hmeet : ∃ z, G x z ≠ 0 ∧ G y z ≠ 0
    · obtain ⟨z, hxz, hyz⟩ := hmeet
      have hx : G x ≠ 0 := by intro he; exact hxz (congrFun he z)
      have hy : G y ≠ 0 := by intro he; exact hyz (congrFun he z)
      have hind : ¬ Proportional (G x) (G y) := fun hp => hnot ⟨hx, hy, hp⟩
      exact independent_detector_zero_of_exponent G P hP hpow K hK E hE hkill x y z hxz hyz hind t
    · apply Finset.sum_eq_zero
      intro z _
      have he : G x z = 0 ∨ G y z = 0 := by
        by_contra! hz
        exact hmeet ⟨z, hz⟩
      rcases he with he | he
      · have hexp : (E - 1) * (1 + phaseExponent (Fintype.card D) * t) ≠ 0 :=
          Nat.mul_ne_zero (by omega) (by omega)
        rw [he, zero_pow hexp, zero_mul]
      · rw [he, zero_pow (by omega), mul_zero]
  · rintro ⟨hx, hy, hprop⟩
    obtain ⟨lam, hlam, hrow⟩ := proportional_symm hprop
    exact detector_ne_zero_of_dependent (G x) (G y) lam hlam _ _
      (by omega) hrow (ht x hx)


/-- Transport the actual torsion property to the image subfield. No number-field
structure or root enumeration oracle on the image is assumed. -/
theorem killsTorsion_fieldRange {K : Type*} [Field K] (σ : K →+* ℂ)
    (E : ℕ) (hkill : KillsTorsion K E) : KillsTorsion σ.fieldRange E := by
  intro x hx
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp x.property
  have haorder : IsOfFinOrder a := σ.injective.isOfFinOrder_iff.mp (by
    change IsOfFinOrder (σ a)
    rw [ha]
    exact σ.fieldRange.subtype.isOfFinOrder hx)
  apply Subtype.ext
  change (x : ℂ) ^ E = 1
  rw [← ha, ← map_pow, hkill a haorder, map_one]

/-- Exact support for the embedded table using the supplied source-field
exponent. The detector itself is evaluated in the source field. -/
theorem exists_embedded_detector_support {K X D : Type*} [Field K]
    [Fintype X] [Fintype D] (σ : K →+* ℂ) (G : X → D → K)
    (P : PurificationMap (entryGroup (fun x z => σ (G x z)))
      (entryGroup (fun x z => σ (G x z))).subtype)
    (hP : BlockOrthogonal (PurificationMap.purifyTable (fun x z => σ (G x z)) P))
    (hpow : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => σ (G x z) ^ h))
    (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E) :
    ∃ t : ℕ, ∀ x y,
      detector (G x) (G y) E (1 + phaseExponent (Fintype.card D) * t) ≠ 0 ↔
        NonzeroProportionalRows (fun x z => σ (G x z)) x y := by
  obtain ⟨t, ht⟩ := exists_detector_support_of_exponent (fun x z => σ (G x z))
    P hP hpow σ.fieldRange (fun x z => σ.mem_fieldRange_self (G x z))
    E hE (killsTorsion_fieldRange σ E hkill)
  refine ⟨t, fun x y => ?_⟩
  have hmap : detector (fun z => σ (G x z)) (fun z => σ (G y z)) E
      (1 + phaseExponent (Fintype.card D) * t) =
      σ (detector (G x) (G y) E (1 + phaseExponent (Fintype.card D) * t)) := by
    simp only [detector, map_sum, map_mul, map_pow]
  have hxy := ht x y
  rw [hmap, ne_eq, map_eq_zero] at hxy
  exact hxy

/-- The exact time-existence bridge for generated source-field tables. Joint BO
supplies the legal purification and the BO of every required pointwise power. -/
theorem exists_generated_detector_time {D K ι : Type} [Fintype D] [Fintype ι]
    [Field K] (L : Language D K ι) (σ : K →+* ℂ)
    (hBO : JointBO (L.mapValues σ)) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → K) (hG : Instance.Generated L G)
    (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E) :
    ∃ t : ℕ, ∀ a : Fin (n + n) → D,
      rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
          (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
        a ∈ (omegaRelation (fun b => σ (G b))).tuples := by
  classical
  let Gc := fun a => σ (G a)
  have hGc : Instance.Generated (L.mapValues σ) Gc := Instance.generated_mapValues hG σ
  let T : PositiveTable D := ⟨n, Gc⟩
  let C := GeneratingSet.LegalGeneratingSet.choose T.nonzeroValues
  have hcontains : GeneratingSet.LegalGeneratingSet.ContainsTable T.nonzeroValues
      (tableRows Gc) := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x, z, rfl⟩
  let P := C.tableMap (tableRows Gc) hcontains
  have hP : BlockOrthogonal (PurificationMap.purifyTable (tableRows Gc) P) := by
    exact (jointBO_iff_singletonBO (L.mapValues σ)).mp hBO T hGc hn
  have hpow : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => tableRows Gc x z ^ h) := by
    intro h _ _
    exact hBO.original (L.mapValues σ) n (fun a => Gc a ^ h)
      (Instance.generated_pow hGc h)
  obtain ⟨t, ht⟩ := exists_embedded_detector_support σ
    (fun x z => G (Fin.snoc x z)) P hP hpow E hE hkill
  exact ⟨t, fun a => ht (fun i => a (Fin.castAdd n i))
    (fun i => a (Fin.natAdd n i))⟩

/-- The supplied exponent produces an actual generated source-field detector
whose support is exactly the embedded original nonzero-row equivalence. -/
theorem generated_row_equivalence_detector {D K ι : Type} [Fintype D] [Fintype ι]
    [Field K] (L : Language D K ι) (σ : K →+* ℂ)
    (hBO : JointBO (L.mapValues σ)) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → K) (hG : Instance.Generated L G)
    (E : ℕ) (hE : 2 ≤ E) (hkill : KillsTorsion K E) :
    ∃ t : ℕ,
      Instance.Generated L (rowDetector G
        ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
        (1 + phaseExponent (Fintype.card D) * t)) ∧
      ∀ a : Fin (n + n) → D,
        rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
            (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
          a ∈ (omegaRelation (fun b => σ (G b))).tuples := by
  obtain ⟨t, ht⟩ := exists_generated_detector_time L σ hBO hn G hG E hE hkill
  exact ⟨t, generated_rowDetector hG _ _, ht⟩

/-- Number-field specialization with the exact mathematical exponent of this
specified working field, without enlarging the field or changing the formula. -/
theorem generated_row_equivalence_detector_fieldExponent {D K ι : Type}
    [Fintype D] [Fintype ι] [Field K] [NumberField K]
    (L : Language D K ι) (σ : K →+* ℂ)
    (hBO : JointBO (L.mapValues σ)) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → K) (hG : Instance.Generated L G) :
    ∃ t : ℕ,
      Instance.Generated L (rowDetector G
        ((fieldExponent K - 1) * (1 + phaseExponent (Fintype.card D) * t))
        (1 + phaseExponent (Fintype.card D) * t)) ∧
      ∀ a : Fin (n + n) → D,
        rowDetector G ((fieldExponent K - 1) * (1 + phaseExponent (Fintype.card D) * t))
            (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
          a ∈ (omegaRelation (fun b => σ (G b))).tuples :=
  generated_row_equivalence_detector L σ hBO hn G hG (fieldExponent K)
    (fieldExponent_ge_two K) (fieldExponent_killsTorsion K)

/-- Literal original-language specialization: the displayed exponent is exactly
that of the input-generated conjugation-stable working field from Section 4. -/
theorem generated_detector_exact_workingField {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : JointBO L) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → ℂ) (hG : Instance.Generated L G) :
    letI := L.workingField_numberField hAlg
    ∃ t : ℕ,
      Instance.Generated L (rowDetector G
        ((fieldExponent L.workingField - 1) * (1 + phaseExponent (Fintype.card D) * t))
        (1 + phaseExponent (Fintype.card D) * t)) ∧
      ∀ a : Fin (n + n) → D,
        rowDetector G
          ((fieldExponent L.workingField - 1) * (1 + phaseExponent (Fintype.card D) * t))
          (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
          a ∈ (omegaRelation G).tuples := by
  letI := L.workingField_numberField hAlg
  obtain ⟨F, hF, hmap⟩ := Instance.generated_inWorkingField hG
  let σ : L.workingField →+* ℂ := L.workingField.subtype
  have hL : L.workingFieldLanguage.mapValues σ = L := by cases L; rfl
  have hBO' : JointBO (L.workingFieldLanguage.mapValues σ) := hL.symm ▸ hBO
  obtain ⟨t, _, ht⟩ := generated_row_equivalence_detector_fieldExponent
    L.workingFieldLanguage σ hBO' hn F hF
  refine ⟨t, generated_rowDetector hG _ _, ?_⟩
  intro a
  have hFG : (fun b => σ (F b)) = G := funext hmap
  have hdet : σ (rowDetector F
      ((fieldExponent L.workingField - 1) * (1 + phaseExponent (Fintype.card D) * t))
      (1 + phaseExponent (Fintype.card D) * t) a) =
      rowDetector G
      ((fieldExponent L.workingField - 1) * (1 + phaseExponent (Fintype.card D) * t))
      (1 + phaseExponent (Fintype.card D) * t) a := by
    simp only [rowDetector, map_sum, map_mul, map_pow, show ∀ b, σ (F b) = G b from hmap]
  have hta := ht a
  rw [hFG] at hta
  rw [← hdet, map_ne_zero]
  exact hta

end ComplexCSP.RowDetectorEmbeddedExistence

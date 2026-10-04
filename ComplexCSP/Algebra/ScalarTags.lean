import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Common positive scalar tags

The scalar-avoidance step of Lemma 5.4. Positive integer scalars suffice to avoid
any finite collection of equalities in each of two table families. The finite
search below has actual coefficient/table decidability parameters.
-/

namespace ComplexCSP

section ScalarAvoidance

variable {K A : Type*} [Field K] [CharZero K]

/-- Scaling a nonzero table by distinct positive integers gives distinct tables. -/
theorem positive_scaling_injective {x : A → K} (hx : x ≠ 0) :
    Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : K) • x) := by
  intro m n h
  have hc := smul_left_injective K hx h
  have hn : m + 1 = n + 1 := Nat.cast_injective hc
  exact Nat.add_right_cancel hn

/-- Only finitely many positive integers can scale a table into a fixed finite
set. A zero table is allowed if the forbidden set contains no zero table. -/
theorem finite_bad_positive_scalars (x : A → K) (U : Finset (A → K))
    (hz : x = 0 → (0 : A → K) ∉ U) :
    {n : ℕ | ((n + 1 : ℕ) : K) • x ∈ U}.Finite := by
  classical
  by_cases hx : x = 0
  · have he : {n : ℕ | ((n + 1 : ℕ) : K) • x ∈ U} = ∅ := by
      ext n
      simp [hx, hz hx]
    rw [he]
    exact Set.finite_empty
  · exact U.finite_toSet.preimage (positive_scaling_injective hx).injOn

/-- One common positive integer simultaneously avoids both finite forbidden
families. This is the exact induction step in the common-scalar-tag argument. -/
theorem exists_common_positive_scalar {B : Type*} (x : A → K) (y : B → K)
    (U : Finset (A → K)) (V : Finset (B → K))
    (hx : x = 0 → (0 : A → K) ∉ U)
    (hy : y = 0 → (0 : B → K) ∉ V) :
    ∃ n : ℕ, ((n + 1 : ℕ) : K) • x ∉ U ∧ ((n + 1 : ℕ) : K) • y ∉ V := by
  have hU := finite_bad_positive_scalars x U hx
  have hV := finite_bad_positive_scalars y V hy
  obtain ⟨n, hn⟩ := (hU.union hV).exists_notMem
  exact ⟨n, by simpa only [Set.mem_union, Set.mem_setOf_eq, not_or] using hn⟩

omit [CharZero K] in
/-- Extending a tag assignment by a new scalar outside the previous image
preserves pairwise distinctness on the enlarged finite index set. -/
theorem tag_update_injOn {ι : Type*} [DecidableEq ι] [DecidableEq (A → K)] (s : Finset ι) (a : ι)
    (ha : a ∉ s) (x : ι → A → K) (tags : ι → ℕ) (n : ℕ)
    (hinj : Set.InjOn (fun i => (tags i : K) • x i) (s : Set ι))
    (hnew : (n : K) • x a ∉ s.image (fun i => (tags i : K) • x i)) :
    Set.InjOn (fun i => (Function.update tags a n i : K) • x i)
      (↑(insert a s) : Set ι) := by
  classical
  intro i hi j hj heq
  rcases Finset.mem_insert.mp hi with hia | hi
  · subst i
    rcases Finset.mem_insert.mp hj with hja | hj
    · exact hja.symm
    · have hja : j ≠ a := fun h => ha (h ▸ hj)
      simp only [Function.update_self, Function.update_of_ne hja] at heq
      exact False.elim (hnew (Finset.mem_image.mpr ⟨j, hj, heq.symm⟩))
  · have hia : i ≠ a := fun h => ha (h ▸ hi)
    rcases Finset.mem_insert.mp hj with hja | hj
    · subst j
      simp only [Function.update_self, Function.update_of_ne hia] at heq
      exact False.elim (hnew (Finset.mem_image.mpr ⟨i, hi, heq⟩))
    · have hja : j ≠ a := fun h => ha (h ▸ hj)
      simp only [Function.update_of_ne hia, Function.update_of_ne hja] at heq
      exact hinj hi hj heq

/-- Common positive integer tags for two finite table families. Each family
may contain one zero table, but not two. Applied separately at each arity,
this is the common-scalar-tag existence assertion of Lemma 5.4. -/
theorem exists_common_positive_tags {ι B : Type*}
    (x : ι → A → K) (y : ι → B → K)
    (hx0 : ∀ i j, x i = 0 → x j = 0 → i = j)
    (hy0 : ∀ i j, y i = 0 → y j = 0 → i = j) (s : Finset ι) :
    ∃ tags : ι → ℕ, (∀ i ∈ s, 0 < tags i) ∧
      Set.InjOn (fun i => (tags i : K) • x i) (s : Set ι) ∧
      Set.InjOn (fun i => (tags i : K) • y i) (s : Set ι) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, by simp, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨tags, hpos, hx, hy⟩ := ih
    have hUx : x a = 0 → (0 : A → K) ∉ s.image (fun i => (tags i : K) • x i) := by
      intro hxa hmem
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      have hi0 : x i = 0 := (smul_eq_zero.mp he).resolve_left
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hpos i hi)))
      exact ha (hx0 i a hi0 hxa ▸ hi)
    have hVy : y a = 0 → (0 : B → K) ∉ s.image (fun i => (tags i : K) • y i) := by
      intro hya hmem
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      have hi0 : y i = 0 := (smul_eq_zero.mp he).resolve_left
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hpos i hi)))
      exact ha (hy0 i a hi0 hya ▸ hi)
    obtain ⟨n, hnX, hnY⟩ := exists_common_positive_scalar (x a) (y a)
      (s.image (fun i => (tags i : K) • x i))
      (s.image (fun i => (tags i : K) • y i)) hUx hVy
    refine ⟨Function.update tags a (n + 1), ?_,
      tag_update_injOn s a ha x tags (n + 1) hx hnX,
      tag_update_injOn s a ha y tags (n + 1) hy hnY⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp
    · have hia : i ≠ a := fun h => ha (h ▸ hi)
      simpa only [Function.update_of_ne hia] using hpos i hi

end ScalarAvoidance

section ExecutableSearch

variable {K A B : Type*} [Field K] [CharZero K] [DecidableEq K]
variable [Fintype A] [Fintype B]

/-- Search positive integers in increasing order. Decidable field equality and
finite table domains make each comparison effective; proved finite avoidance
supplies termination. No classical equality procedure is installed here. -/
def nextCommonPositiveScalar (x : A → K) (y : B → K)
    (U : Finset (A → K)) (V : Finset (B → K))
    (hx : x = 0 → (0 : A → K) ∉ U)
    (hy : y = 0 → (0 : B → K) ∉ V) : ℕ :=
  Nat.find (exists_common_positive_scalar x y U V hx hy) + 1

/-- The computed scalar is positive and avoids both finite sets. -/
theorem nextCommonPositiveScalar_spec (x : A → K) (y : B → K)
    (U : Finset (A → K)) (V : Finset (B → K))
    (hx : x = 0 → (0 : A → K) ∉ U)
    (hy : y = 0 → (0 : B → K) ∉ V) :
    0 < nextCommonPositiveScalar x y U V hx hy ∧
      (nextCommonPositiveScalar x y U V hx hy : K) • x ∉ U ∧
      (nextCommonPositiveScalar x y U V hx hy : K) • y ∉ V := by
  exact ⟨Nat.succ_pos _, Nat.find_spec (exists_common_positive_scalar x y U V hx hy)⟩

end ExecutableSearch

end ComplexCSP

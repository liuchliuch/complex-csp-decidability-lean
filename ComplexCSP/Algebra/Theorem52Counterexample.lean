import ComplexCSP.Instances.PinnedIsomorphism
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Counterexample to the literal simple-instance implication in Theorem 5.2

The manuscript's TeX lines 2268–2271 prohibit repeated occurrences of one unary
function at a variable. Under that exact convention, strictly positive unary profiles (1,2,5) and
(1,3,4) with a label pinned to the weight-one entry have identical values on every
simple instance and are not isomorphic. No claim about all-instance equality
is made; repeating a unary constraint twice distinguishes the profiles.
-/
namespace ComplexCSP.Theorem52Counterexample
open scoped BigOperators

variable {D K V H : Type}

abbrev unaryLanguage (f : D → K) : Language D K Unit where
  arity := fun _ => 1
  arity_pos := fun _ => by decide
  value := fun _ x => f (x 0)

/-- List of constrained variables, retaining every occurrence. -/
def occurrences {f : D → K} (I : Instance (unaryLanguage f) V H) : List (V ⊕ H) :=
  I.constraints.map (fun c => c.scope 0)

/-- In a one-function unary language, source simplicity means no variable
occurs twice in the constraint list. -/
def Simple {f : D → K} (I : Instance (unaryLanguage f) V H) : Prop :=
  (occurrences I).Nodup

/-- The two clauses in the paper's printed simple-instance definition. -/
def PaperSimple {f : D → K} (I : Instance (unaryLanguage f) V H) : Prop :=
  (∀ c ∈ I.constraints, Function.Injective c.scope) ∧
  I.constraints.Pairwise (fun c d =>
    ¬ ∃ e : Fin 1 ≃ Fin 1, d.scope = c.scope ∘ e)

private theorem unary_no_permuted_scope_iff {f : D → K}
    (c d : Constraint (unaryLanguage f) (V ⊕ H)) :
    (¬ ∃ e : Fin 1 ≃ Fin 1, d.scope = c.scope ∘ e) ↔ c.scope 0 ≠ d.scope 0 := by
  constructor
  · intro h he
    apply h
    refine ⟨Equiv.refl _, ?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj, Function.comp_apply, Equiv.refl_apply] using he.symm
  · intro h ⟨e, he⟩
    apply h
    have hv := congrFun he 0
    have hz : e 0 = 0 := Subsingleton.elim _ _
    simpa only [Function.comp_apply, hz] using hv.symm

theorem paperSimple_iff_simple {f : D → K} (I : Instance (unaryLanguage f) V H) :
    PaperSimple I ↔ Simple I := by
  have hinj : ∀ c ∈ I.constraints, Function.Injective c.scope := by
    intro c _ a b _
    exact Subsingleton.elim _ _
  simp only [PaperSimple, Simple, occurrences,
    List.nodup_iff_pairwise_ne, List.pairwise_map, unary_no_permuted_scope_iff]
  exact and_iff_right hinj

/-- Literal evaluation in the existing finite-instance semantics. -/
theorem eval_unary [CommMonoid K] {f : D → K}
    (I : Instance (unaryLanguage f) V H) (a : V → D) (b : H → D) :
    I.eval a b = ((occurrences I).map (fun v => f (Sum.elim a b v))).prod := by
  simp only [Instance.eval, occurrences, List.map_map]
  rfl

/-- No multiplicity is discarded: this conversion requires source simplicity. -/
theorem eval_simple [CommMonoid K] [Fintype V] [Fintype H]
    [DecidableEq V] [DecidableEq H] {f : D → K}
    (I : Instance (unaryLanguage f) V H) (hs : Simple I) (a : V → D) (b : H → D) :
    I.eval a b = ∏ v : V ⊕ H, if v ∈ (occurrences I).toFinset then f (Sum.elim a b v) else 1 := by
  rw [eval_unary, ← List.prod_toFinset _ hs]
  exact
    (Fintype.prod_ite_mem (occurrences I).toFinset (fun v => f (Sum.elim a b v))).symm

theorem partition_simple [CommSemiring K] [Fintype D] [Fintype V] [Fintype H]
    [DecidableEq V] [DecidableEq H] {f : D → K}
    (I : Instance (unaryLanguage f) V H) (hs : Simple I) (a : V → D) :
    I.partition a =
      (∏ v : V, if Sum.inl v ∈ (occurrences I).toFinset then f (a v) else 1) *
      ∏ h : H, ∑ x : D, if Sum.inr h ∈ (occurrences I).toFinset then f x else 1 := by
  unfold Instance.partition
  simp_rw [eval_simple I hs, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun (h : H) (x : D) =>
    if Sum.inr h ∈ (occurrences I).toFinset then f x else 1)).symm

/-- Retargeting to another unary profile changes neither occurrence count nor
simplicity. -/
theorem occurrences_retarget {f g : D → K} (I : Instance (unaryLanguage f) V H) :
    occurrences (I.retarget (fun _ x => g (x 0))) = occurrences I := by
  simp only [occurrences, Instance.retarget, List.map_map]
  rfl

/-- All finite simple unary instances depend only on the sum of the profile,
the domain size, and the values at constrained labels. -/
theorem all_simple_unary_equal [CommSemiring K] [Fintype D] [Fintype V] [Fintype H]
    [DecidableEq V] [DecidableEq H] (f g : D → K)
    (hsum : ∑ x, f x = ∑ x, g x) (a : V → D) (b : V → D)
    (hpin : ∀ v, f (a v) = g (b v))
    (I : Instance (unaryLanguage f) V H) (hs : PaperSimple I) :
    I.partition a = (I.retarget (fun _ x => g (x 0))).partition b := by
  have hs' : Simple I := (paperSimple_iff_simple I).mp hs
  have ht : Simple (I.retarget (fun _ x => g (x 0))) := by
    simpa only [Simple, occurrences_retarget] using hs'
  rw [partition_simple I hs', partition_simple _ ht, occurrences_retarget]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [hpin]
  · apply Finset.prod_congr rfl
    intro h _
    by_cases hc : Sum.inr h ∈ (occurrences I).toFinset
    · simpa only [if_pos hc] using hsum
    · simp only [if_neg hc]

/-- Both profiles are positive, injective, and have the same total weight. -/
def firstProfile : Fin 3 → ℚ := fun i => if i = 0 then 1 else if i = 1 then 2 else 5

def secondProfile : Fin 3 → ℚ := fun i => if i = 0 then 1 else if i = 1 then 3 else 4

def zeroPin : Fin 1 → Fin 3 := fun _ => 0

theorem firstProfile_pos (i : Fin 3) : 0 < firstProfile i := by
  fin_cases i <;> norm_num [firstProfile]

theorem secondProfile_pos (i : Fin 3) : 0 < secondProfile i := by
  fin_cases i <;> norm_num [secondProfile]

theorem firstProfile_injective : Function.Injective firstProfile := by decide

theorem secondProfile_injective : Function.Injective secondProfile := by decide

theorem profile_sums : (∑ x, firstProfile x) = ∑ x, secondProfile x := by
  norm_num [Fin.sum_univ_succ, firstProfile, secondProfile, show (2 : Fin 3) ≠ 1 by decide]

theorem profile_sum_value : (∑ x, firstProfile x) = 8 := by
  norm_num [Fin.sum_univ_succ, firstProfile, show (2 : Fin 3) ≠ 1 by decide]

theorem profile_pin : firstProfile 0 = secondProfile 0 := by decide

theorem secondProfile_ne_two (i : Fin 3) : secondProfile i ≠ 2 := by
  fin_cases i <;> norm_num [secondProfile]

/-- For a unary language, the paper's twin relation is exactly equality of the
single unary profile value. -/
theorem unary_twins_iff (f : D → K) (a b : D) :
    (unaryLanguage f).Twins a b ↔ f a = f b := by
  constructor
  · intro ht
    simpa [Language.Twins, unaryLanguage] using ht () 0 (fun _ => a)
  · intro he i j x
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [unaryLanguage, Function.update_self] using he

theorem firstProfile_twinFree {a b : Fin 3}
    (h : (unaryLanguage firstProfile).Twins a b) : a = b :=
  firstProfile_injective ((unary_twins_iff firstProfile a b).mp h)

theorem secondProfile_twinFree {a b : Fin 3}
    (h : (unaryLanguage secondProfile).Twins a b) : a = b :=
  secondProfile_injective ((unary_twins_iff secondProfile a b).mp h)

/-- Every constrained hidden variable contributes eight, every isolated hidden
variable contributes three, and the pinned variable contributes one. -/
theorem positive_profile_simple_value {H : Type} [Fintype H] [DecidableEq H]
    (I : Instance (unaryLanguage firstProfile) (Fin 1) H) (hs : PaperSimple I) :
    I.partition zeroPin = ∏ h : H,
      if Sum.inr h ∈ (occurrences I).toFinset then (8 : ℚ) else 3 := by
  rw [partition_simple I ((paperSimple_iff_simple I).mp hs)]
  have hb : (∏ v : Fin 1, if Sum.inl v ∈ (occurrences I).toFinset then
      firstProfile (zeroPin v) else 1) = 1 := by simp [zeroPin, firstProfile]
  rw [hb, one_mul]
  apply Finset.prod_congr rfl
  intro h _
  by_cases hc : Sum.inr h ∈ (occurrences I).toFinset
  · simpa only [if_pos hc] using profile_sum_value
  · simp [hc]

/-- Every actual finite simple unary instance has the same pinned value for
these two targets. The scope-list and finite-sum semantics are unchanged. -/
theorem positive_profiles_all_simple_equal {H : Type} [Fintype H] [DecidableEq H]
    (I : Instance (unaryLanguage firstProfile) (Fin 1) H) (hs : PaperSimple I) :
    I.partition zeroPin =
      (I.retarget (fun _ x => secondProfile (x 0))).partition zeroPin :=
  all_simple_unary_equal firstProfile secondProfile profile_sums zeroPin zeroPin
    (fun _ => profile_pin) I hs

/-- There is no domain isomorphism at all, hence certainly none satisfying the
pin-twin condition. The value two exists only in the first target. -/
theorem positive_profiles_not_isomorphic :
    ¬ ∃ e : Fin 3 ≃ Fin 3,
      (unaryLanguage firstProfile).IsTargetIso (fun _ x => secondProfile (x 0)) e := by
  intro ⟨e, he⟩
  have hv := he () (fun _ => (1 : Fin 3))
  have htwo : (2 : ℚ) = secondProfile (e 1) := by
    simpa only [unaryLanguage, firstProfile, Function.comp_apply] using hv
  exact secondProfile_ne_two (e 1) htwo.symm

/-- Literal falsification of the simple-instance implication in the paper's
Theorem 5.2, using one unary function and one boundary label. Quantification
over `Fin n` covers every finite number of hidden variables. -/
theorem printed_theorem_5_2_counterexample :
    (∀ (n : ℕ) (I : Instance (unaryLanguage firstProfile) (Fin 1) (Fin n)),
      PaperSimple I → I.partition zeroPin =
        (I.retarget (fun _ x => secondProfile (x 0))).partition zeroPin) ∧
    ¬ (∃ e : Fin 3 ≃ Fin 3,
      (unaryLanguage firstProfile).IsTargetIso (fun _ x => secondProfile (x 0)) e) :=
  ⟨fun _ I hs => positive_profiles_all_simple_equal I hs, positive_profiles_not_isomorphic⟩

/-- Two copies of the unary function at the same hidden variable are legal in
the unrestricted instance family but forbidden by the paper's simplicity rule. -/
def doubledUnary : Instance (unaryLanguage firstProfile) (Fin 1) (Fin 1) :=
  ⟨[⟨(), fun _ => Sum.inr 0⟩, ⟨(), fun _ => Sum.inr 0⟩]⟩

theorem doubledUnary_not_simple : ¬ PaperSimple doubledUnary := by
  rw [paperSimple_iff_simple]
  simp [Simple, occurrences, doubledUnary]

theorem doubledUnary_first_value : doubledUnary.partition zeroPin = 30 := by
  have he : doubledUnary.partition zeroPin = ∑ x, firstProfile x * firstProfile x := by
    unfold Instance.partition
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _
      (fun b => by simp [doubledUnary, Instance.eval, Constraint.eval, Equiv.funUnique])
  rw [he]
  norm_num [Fin.sum_univ_succ, firstProfile, show (2 : Fin 3) ≠ 1 by decide]

theorem doubledUnary_second_value :
    (doubledUnary.retarget (fun _ x => secondProfile (x 0))).partition zeroPin = 26 := by
  have he : (doubledUnary.retarget (fun _ x => secondProfile (x 0))).partition zeroPin =
      ∑ x, secondProfile x * secondProfile x := by
    unfold Instance.partition
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _
      (fun b => by simp [doubledUnary, Instance.eval, Instance.retarget, Language.retarget, Constraint.eval, Equiv.funUnique])
  rw [he]
  norm_num [Fin.sum_univ_succ, secondProfile, show (2 : Fin 3) ≠ 1 by decide]

end ComplexCSP.Theorem52Counterexample

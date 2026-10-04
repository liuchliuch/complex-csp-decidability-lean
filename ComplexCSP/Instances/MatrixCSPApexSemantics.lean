import ComplexCSP.Instances.MatrixCSPApexCode

/-! # Exact shared-apex partition identity on the raw CSP codec -/
namespace ComplexCSP.PositiveBinaryApex
open ComplexityCSPCode
open scoped BigOperators

variable {K : Type} [CommRing K]

def decodedEdges (B : Bool → Bool → K) (g : Code) (hg : Valid (MatrixCSP.language B) g) :
    List (Fin g.vertices × Fin g.vertices) :=
  g.constraints.attach.map (fun c =>
    (scope (MatrixCSP.language B) g c.val (hg c.val c.property) (0 : Fin 2),
      scope (MatrixCSP.language B) g c.val (hg c.val c.property) (1 : Fin 2)))

theorem eval_eq_graphWeight (B : Bool → Bool → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) (σ : Fin g.vertices → Bool) :
    eval (MatrixCSP.language B) g σ = graphWeight B (decodedEdges B g hg) σ := by
  unfold eval assignmentWord graphWeight decodedEdges
  simp only [List.map_map,Function.comp_def]
  congr 1
  symm
  calc
    _ = g.constraints.attach.map (fun c =>
        entryValue (MatrixCSP.language B) (constraintEntry (MatrixCSP.language B) g σ c.val)) := by
      apply List.map_congr_left
      intro c _
      rw [constraintEntry,dif_pos (hg c.val c.property)]
      rfl
    _ = _ := List.attach_map_val (l := g.constraints) (f := fun c =>
      entryValue (MatrixCSP.language B) (constraintEntry (MatrixCSP.language B) g σ c))

theorem addApex_scope (A B : Bool → Bool → K) (g : Code) (c : ℕ × List ℕ)
    (hc : ConstraintValid (MatrixCSP.language B) g.vertices c) (i : Fin 3) :
    scope (triangleLanguage A) (addApex g) (addApexConstraint g.vertices c)
      (addApex_constraint_valid A B g c hc) i =
      Fin.snoc (α := fun _ : Fin 3 => Fin (g.vertices+1)) (fun j : Fin 2 => (scope (MatrixCSP.language B) g c hc j).castSucc)
        (Fin.last g.vertices) i := by
  have hlen : c.2.length = 2 := hc.choose_spec.1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    apply Fin.ext
    change (c.2 ++ [g.vertices])[2]'(by simp [hlen]) = g.vertices
    rw [List.getElem_append_right (by omega)]
    simp [hlen]
  · rw [Fin.snoc_castSucc]
    apply Fin.ext
    change (c.2 ++ [g.vertices])[j.val]'(by simp only [List.length_append,List.length_singleton,hlen]; omega) =
      c.2[j.val]'(by omega)
    exact List.getElem_append_left (by omega)

theorem addApex_assignment_scope (A B : Bool → Bool → K) (g : Code) (c : ℕ × List ℕ)
    (hc : ConstraintValid (MatrixCSP.language B) g.vertices c)
    (σ : Fin g.vertices → Bool) (root : Bool) (i : Fin 3) :
    Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root (scope (triangleLanguage A) (addApex g) (addApexConstraint g.vertices c)
      (addApex_constraint_valid A B g c hc) i) =
      Fin.snoc (α := fun _ : Fin 3 => Bool)
        (fun j : Fin 2 => σ (scope (MatrixCSP.language B) g c hc j)) root i := by
  rw [addApex_scope A B g c hc]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root
      (Fin.snoc (α := fun _ : Fin 3 => Fin (g.vertices+1))
        (fun j : Fin 2 => (scope (MatrixCSP.language B) g c hc j).castSucc)
        (Fin.last g.vertices) (Fin.last 2)) =
      Fin.snoc (α := fun _ : Fin 3 => Bool)
        (fun j : Fin 2 => σ (scope (MatrixCSP.language B) g c hc j)) root (Fin.last 2)
    simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

theorem addApex_constraint_value (A B : Bool → Bool → K) (g : Code) (c : ℕ × List ℕ)
    (hc : ConstraintValid (MatrixCSP.language B) g.vertices c)
    (σ : Fin g.vertices → Bool) (root : Bool) :
    entryValue (triangleLanguage A)
      (constraintEntry (triangleLanguage A) (addApex g) (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root) (addApexConstraint g.vertices c)) =
      A (σ (scope (MatrixCSP.language B) g c hc (0 : Fin 2))) (σ (scope (MatrixCSP.language B) g c hc (1 : Fin 2))) *
        A (σ (scope (MatrixCSP.language B) g c hc (0 : Fin 2))) root *
        A (σ (scope (MatrixCSP.language B) g c hc (1 : Fin 2))) root := by
  rw [constraintEntry,dif_pos (addApex_constraint_valid A B g c hc)]
  have he : (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root ∘
      scope (triangleLanguage A) (addApex g) (addApexConstraint g.vertices c)
        (addApex_constraint_valid A B g c hc)) =
      Fin.snoc (α := fun _ : Fin 3 => Bool)
        (fun j : Fin 2 => σ (scope (MatrixCSP.language B) g c hc j)) root :=
    funext (addApex_assignment_scope A B g c hc σ root)
  exact congrArg ((triangleLanguage A).value 0) he

theorem addApex_eval (A B : Bool → Bool → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) (σ : Fin g.vertices → Bool) (root : Bool) :
    eval (triangleLanguage A) (addApex g) (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root) =
      ((decodedEdges B g hg).map (fun e =>
        A (σ e.1) (σ e.2) * A (σ e.1) root * A (σ e.2) root)).prod := by
  unfold eval assignmentWord addApex decodedEdges
  simp only [List.map_map,Function.comp_def]
  congr 1
  symm
  calc
    _ = g.constraints.attach.map (fun c => entryValue (triangleLanguage A)
        (constraintEntry (triangleLanguage A) (addApex g) (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root)
          (addApexConstraint g.vertices c.val))) := by
      apply List.map_congr_left
      intro c _
      exact (addApex_constraint_value A B g c.val (hg c.val c.property) σ root).symm
    _ = _ := List.attach_map_val (l := g.constraints) (f := fun c =>
      entryValue (triangleLanguage A) (constraintEntry (triangleLanguage A) (addApex g)
        (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root) (addApexConstraint g.vertices c)))

/-- The actual compiled output has exactly twice the biased-source partition. -/
theorem compileApex_twice_partition (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (hd : A false false = A true true)
    (g : Code) (hg : Valid (MatrixCSP.language (biased A)) g) :
    partition (MatrixCSP.language A) (compileApex A g) =
      2 * partition (MatrixCSP.language (biased A)) g := by
  rw [compileApex_partition A (biased A) g hg]
  unfold partition
  have he := (Fin.snocEquiv (fun _ : Fin (g.vertices+1) => Bool)).sum_comp
    (eval (triangleLanguage A) (addApex g))
  calc
    _ = ∑ p : Bool × (Fin g.vertices → Bool),
      eval (triangleLanguage A) (addApex g)
        (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) p.2 p.1) := he.symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ root : Bool, ∑ σ : Fin g.vertices → Bool,
        eval (triangleLanguage A) (addApex g) (Fin.snoc (α := fun _ : Fin (g.vertices+1) => Bool) σ root)) = _
      rw [Finset.sum_comm]
      simp only [addApex_eval A (biased A) g hg,eval_eq_graphWeight (biased A) g hg]
      exact shared_apex_partition A hs hd (decodedEdges (biased A) g hg)

end ComplexCSP.PositiveBinaryApex

import ComplexCSP.Complexity.CSPCountSharpP

/-! # COUNT membership for every fixed finite domain

A fixed color bijection changes no input bits, signature arities, target-field
coordinates or occurrence multiplicities. It only compiles fixed table entries
into the already constructed finite-color verifier.
-/
noncomputable section
namespace ComplexCSP.ComplexityCSPCountMembership
open PlanarHom PlanarHom.Complexity
open ComplexityCSPCode

variable {D K : Type} {s q : ℕ} (L : Language D K (Fin s))

/-- Compile a fixed domain into canonical finite colors, without changing scopes. -/
def finLanguage (e : D ≃ Fin q) : Language (Fin q) K (Fin s) where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := L.value i (e.symm ∘ a)

 theorem valid_finLanguage (e : D ≃ Fin q) (g : Code) :
    Valid (finLanguage L e) g ↔ Valid L g := Iff.rfl

 theorem eval_finLanguage [CommMonoid K] (e : D ≃ Fin q) (g : Code)
    (σ : Fin g.vertices → Fin q) :
    eval (finLanguage L e) g σ = eval L g (e.symm ∘ σ) := by
  unfold eval assignmentWord
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  change entryValue (finLanguage L e) (constraintEntry (finLanguage L e) g σ c) =
    entryValue L (constraintEntry L g (e.symm ∘ σ) c)
  by_cases hc : ConstraintValid L g.vertices c
  · have hc' : ConstraintValid (finLanguage L e) g.vertices c := hc
    simp only [constraintEntry,dif_pos hc,dif_pos hc',entryValue]
    rfl
  · have hc' : ¬ ConstraintValid (finLanguage L e) g.vertices c := hc
    simp only [constraintEntry,dif_neg hc,dif_neg hc',entryValue]

 theorem countAt_finLanguage [Fintype D] [CommMonoid K] [DecidableEq K]
    (e : D ≃ Fin q) (g : Code) (z : K) :
    countAt (finLanguage L e) g z = countAt L g z := by
  let E : {σ : Fin g.vertices → Fin q // eval (finLanguage L e) g σ = z} ≃
      {σ : Fin g.vertices → D // eval L g σ = z} := {
    toFun σ := ⟨e.symm ∘ σ.val,(eval_finLanguage L e g σ.val).symm.trans σ.property⟩
    invFun σ := ⟨e ∘ σ.val,by
      rw [eval_finLanguage]
      simpa only [Function.comp_def,Equiv.symm_apply_apply] using σ.property⟩
    left_inv σ := by apply Subtype.ext; funext i; exact e.apply_symm_apply _
    right_inv σ := by apply Subtype.ext; funext i; exact e.symm_apply_apply _ }
  simpa only [Fintype.card_subtype,countAt] using Fintype.card_congr E

/-- An independently defined accepting-path #P function agrees with fixed-language
COUNT on precisely its existing canonical valid-instance, same-field promise. -/
theorem countProblem_membership [Fintype D] [Field K] [Algebra ℚ K] [DecidableEq K]
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) :
    ∃ f : Bits → ℕ, SharpP f ∧ ∀ raw,
      (ComplexityCSPCountReduction.countProblem L basis).valid raw →
      (ComplexityCSPCountReduction.countProblem L basis).value raw = BitEncoding.nat.encode (f raw) := by
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  obtain ⟨f,hf,hcount⟩ := ComplexityCSPCountSharpP.countProblem_membership (finLanguage L e) basis
  refine ⟨f,hf,?_⟩
  rintro raw ⟨p,hp,rfl⟩
  have hv : (ComplexityCSPCountReduction.countProblem (finLanguage L e) basis).valid
      ((ComplexityCSPCountReduction.countEncoding basis).encode p) := ⟨p,hp,rfl⟩
  have h := hcount _ hv
  change encodedFunction _ _ _ _ _ = _ at h ⊢
  rw [encodedFunction_encode] at h ⊢
  rwa [countAt_finLanguage L e p.1 p.2] at h

end ComplexCSP.ComplexityCSPCountMembership

import ComplexCSP.Recognition.DegreeGenerated
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases

open scoped BigOperators
open ComplexCSP

namespace DegreeGeneratedRegressions

/-- Three binary constraints, each repeating its variable twice. -/
def language : Language Unit ℚ Unit where
  arity _ := 2
  arity_pos _ := by decide
  value _ _ := 3

def presentation : Presentation language (Fin 2) :=
  ⟨1, ⟨[⟨(), fun _ => Sum.inl 0⟩, ⟨(), fun _ => Sum.inl 1⟩,
    ⟨(), fun _ => Sum.inr 0⟩]⟩⟩

theorem presentation_even : presentation.DegreeDivisible 2 := by
  unfold Presentation.DegreeDivisible Instance.DegreeDivisible
  decide

example : presentation.inst.occurrenceDegree (Sum.inl 0) = 2 := by decide
example : presentation.inst.occurrenceDegree (Sum.inl 1) = 2 := by decide
example : presentation.inst.occurrenceDegree (Sum.inr ⟨0, by decide⟩) = 2 := by decide

-- Occurrence degree test.
#guard (presentation.degreeDivisibilityTest 2) == true
-- Occurrence degree test.
#guard (presentation.degreeDivisibilityTest 3) == false
example : presentation.degreeDivisibilityTest 2 = true := by decide
example : presentation.degreeDivisibilityTest 3 = false := by decide

-- Identifying two distinct boundary variables sums their full occurrence degrees.
example : (presentation.rename (fun _ => ())).inst.occurrenceDegree (Sum.inl ()) = 4 := by
  decide
example : (presentation.rename (fun _ => ())).DegreeDivisible 2 :=
  presentation_even.rename _

-- The hidden copies in actual powers remain distinct; boundary degrees add.
example : (presentation.power 2).inst.occurrenceDegree (Sum.inl 0) = 4 := by decide
example : (presentation.power 2).DegreeDivisible 2 := presentation_even.power 2
example : (presentation.power 0).DegreeDivisible 2 := presentation_even.power 0

def forMarginal : Presentation language (Unit ⊕ Fin 1) :=
  presentation.rename (fun i => if i = 0 then Sum.inl () else Sum.inr 0)

theorem forMarginal_even : forMarginal.DegreeDivisible 2 := presentation_even.rename _

-- Retaining one boundary variable and summing the other changes no variable degree.
example : forMarginal.marginal.inst.occurrenceDegree (Sum.inl ()) = 2 := by decide
example : forMarginal.marginal.DegreeDivisible 2 := forMarginal_even.marginal

-- A literal pp atom identifies both original boundary variables at its scope.
def atom : PresentedAtom language (Unit ⊕ Fin 0) :=
  ⟨2, presentation, fun _ => Sum.inl ()⟩

example : atom.lift.inst.occurrenceDegree (Sum.inl (Sum.inl ())) = 4 := by decide

-- The entire executable power-search/marginalization pp compiler is certified.
example : (PresentedAtom.compile [atom]).DegreeDivisible 2 := by
  apply PresentedAtom.degreeDivisible_compile
  intro A hA
  have h : A = atom := by simpa using hA
  subst A
  exact presentation_even


-- Degree-restricted semantics retains an actual finite presentation witness.
def semanticTable : DegreeGeneratedTable (B := Fin 2) language 2 :=
  DegreeGeneratedTable.ofPresentation presentation presentation_even

example : ∃ P : Presentation language (Fin 2), ∃ hP : P.DegreeDivisible 2,
    DegreeGeneratedTable.ofPresentation P hP = semanticTable :=
  DegreeGeneratedTable.exists_presentation semanticTable

example : DegreeGenerated language 1 presentation.table :=
  DegreeGenerated.at_one_iff.mpr presentation.table_generated


end DegreeGeneratedRegressions

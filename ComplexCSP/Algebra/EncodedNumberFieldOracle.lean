import ComplexCSP.Algebra.EncodedNumberFieldElement
import ComplexCSP.Recognition.IdentityOracle

/-! # Running the repaired identity oracle on rational-coordinate elements

This specialization supplies the actual executable arithmetic dictionaries.
Coefficient arithmetic uses only finite rational data; semantic validity and conjugation
validity are proof-only parameters. This is part of the separately labelled
corrected all-instance Theorem 5.2.
-/
namespace ComplexCSP.EncodedNumberField.Runtime
open Element

variable {n : ℕ} (c b : CoeffVector n) [Fact (Element.Valid n c)]
    (hb : Element.StarValid n c b)

variable {D ι V : Type} [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V]
    {r : ℕ}

/-- Actual finite target comparison and coefficient grouping on runtime field data. -/
def identityTest (L : Language D (Element n c) ι)
    (coords : Fin r → PinnedCoordinate V D)
    (P : PolynomialPrograms.Program (Element n c) r) : Bool := by
  letI := Element.starRing b hb
  exact Recognition.programIdentityTest L coords P

/-- The executed test has the full universal finite-presentation specification. -/
theorem identityTest_correct (L : Language D (Element n c) ι)
    (coords : Fin r → PinnedCoordinate V D)
    (P : PolynomialPrograms.Program (Element n c) r) :
    letI := Element.starRing b hb
    identityTest c b hb L coords P = true ↔
      ∀ Q : Presentation L V,
        PolynomialPrograms.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) P = 0 := by
  letI := Element.starRing b hb
  exact Recognition.programIdentityTest_correct L coords P

end ComplexCSP.EncodedNumberField.Runtime

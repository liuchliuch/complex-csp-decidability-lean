import ComplexCSP.Algebra.EffectiveRootsRuntimeAlphabet
import ComplexCSP.Algebra.EncodedNumberFieldPresentation

/-!
# Checked raw-input root alphabets on the executable field carrier

These public adapters take only the runtime integer tail and its successful
irreducibility check. The source field is the executable rational-coordinate
wrapper. Neither an external field nor a power-basis witness is supplied by the
caller, and finite/encodable roots are obtained from actual enumeration.
-/

namespace ComplexCSP.EffectiveRoots

open EncodedNumberField

variable {n : ℕ} (a : Fin n → ℤ)
variable [Fact (Element.Valid n (coefficientRelation a))]

abbrev CheckedRootField := Element n (coefficientRelation a)
abbrev CheckedRootSymbols := rootsOfUnity (rootExponentFromCoefficients n a) (CheckedRootField a)

/-- Runtime finite roots, derived from a successful raw polynomial check. -/
def checkedRootFintype (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    Fintype (CheckedRootSymbols a) :=
  runtimeRootFintype a (Element.generator (c := coefficientRelation a))
    (Element.integralPresentation_of_checkedTail a ha)

/-- Runtime encoding of those roots, using actual coordinate equality/powers. -/
def checkedRootEncodable (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    Encodable (CheckedRootSymbols a) :=
  runtimeRootEncodable a (Element.generator (c := coefficientRelation a))
    (Element.integralPresentation_of_checkedTail a ha)

/-- Executable root values, one and inverse lookup for the certificate compiler. -/
def checkedRootAlphabet : Certificates.RootAlphabet (CheckedRootField a) (CheckedRootSymbols a) :=
  runtimeRootAlphabet a

theorem checkedRootExponent_ge_two (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    2 ≤ rootExponentFromCoefficients n a :=
  presentation_rootExponent_ge_two (Element.integralPresentation_of_checkedTail a ha)

theorem checkedRootExponent_killsTorsion (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    RowDetector.KillsTorsion (CheckedRootField a) (rootExponentFromCoefficients n a) :=
  presentation_rootExponent_killsTorsion (Element.integralPresentation_of_checkedTail a ha)

/-- The actual complex realization can be supplied by the validated encoded
field embedding; no complex arithmetic is required by the root enumeration. -/
def checkedRootRealization (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (σ : CheckedRootField a →+* ℂ) : Certificates.ComplexRealization (checkedRootAlphabet a) :=
  Certificates.exponentRootRealization σ _
    (lt_of_lt_of_le (by decide) (checkedRootExponent_ge_two a ha))

end ComplexCSP.EffectiveRoots

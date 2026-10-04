import ComplexCSP.Algebra.InitialPrimitiveCoordinates
import ComplexCSP.Algebra.UniformCyclotomicExtensionRuntime

/-!
# Computing the initial conjugate-generator coordinates

A checked primitive expression in the input values and conjugates supplies
conjugation by swapping those inputs. No conjugation-stability assumption or
pre-supplied conjugate-generator vector is needed.
-/
namespace ComplexCSP.AlgebraicEncoding
open EncodedNumberField

variable {n m : ℕ} {relation : CoeffVector n} [Fact (Element.Valid n relation)]

/-- Literal finite program evaluation in the validated runtime coordinate field. -/
def initialConjugateCoordinates (coordinates : Fin m → CoeffVector n)
    (expression : PolynomialPrograms.Program ℚ m) (swap : Fin m → Fin m) : CoeffVector n :=
  (PolynomialPrograms.interpret (algebraMap ℚ (Element n relation))
    (fun i => (⟨coordinates i⟩ : Element n relation))
    (PolynomialPrograms.rename expression swap)).coeff

/-- The computed vector genuinely represents complex conjugation of the
primitive generator under the checked realization. -/
theorem initialConjugateCoordinates_correct (coordinates : Fin m → CoeffVector n)
    (expression : PolynomialPrograms.Program ℚ m) (swap : Fin m → Fin m)
    (x : Fin m → ℂ) (hswap : ∀ i, x (swap i) = star (x i))
    (Φ : Element n relation →+* ℂ)
    (hcoordinates : ∀ i, Φ (⟨coordinates i⟩ : Element n relation) = x i)
    (hexpression : PolynomialPrograms.interpret (algebraMap ℚ ℂ) x expression =
      Φ (Element.generator (c := relation))) :
    interpret (Φ (Element.generator (c := relation)))
      (initialConjugateCoordinates (relation := relation) coordinates expression swap) =
        star (Φ (Element.generator (c := relation))) := by
  let y := PolynomialPrograms.interpret (algebraMap ℚ (Element n relation))
    (fun i => (⟨coordinates i⟩ : Element n relation)) (PolynomialPrograms.rename expression swap)
  have hy : initialConjugateCoordinates (relation := relation) coordinates expression swap =
      y.coeff := rfl
  rw [hy, ← map_interpret Φ, Element.interpret_generator]
  change Φ y = _
  have hm := PolynomialPrograms.map_interpret (algebraMap ℚ (Element n relation)) Φ
    (fun i => (⟨coordinates i⟩ : Element n relation)) (PolynomialPrograms.rename expression swap)
  have hf : Φ.comp (algebraMap ℚ (Element n relation)) = algebraMap ℚ ℂ := by
    ext q
    simp
  have hv : (fun i => Φ (⟨coordinates i⟩ : Element n relation)) = x := funext hcoordinates
  rw [hf, hv] at hm
  exact hm.trans ((program_conjugate_by_input_swap x swap hswap expression).trans
    (congrArg star hexpression))

/-- Initial conjugation validity is a conclusion of finite expression and
coordinate certificates, not an assumed field-stability property. -/
theorem initialConjugateCoordinates_starValid (coordinates : Fin m → CoeffVector n)
    (expression : PolynomialPrograms.Program ℚ m) (swap : Fin m → Fin m)
    (x : Fin m → ℂ) (hswap : ∀ i, x (swap i) = star (x i))
    (Φ : Element n relation →+* ℂ)
    (hcoordinates : ∀ i, Φ (⟨coordinates i⟩ : Element n relation) = x i)
    (hexpression : PolynomialPrograms.interpret (algebraMap ℚ ℂ) x expression =
      Φ (Element.generator (c := relation))) :
    Element.StarValid n relation
      (initialConjugateCoordinates (relation := relation) coordinates expression swap) :=
  ⟨coordinateFieldModel n relation, Φ,
    initialConjugateCoordinates_correct coordinates expression swap x hswap Φ hcoordinates hexpression⟩

/-- Coordinate certificates checked by complex polynomial evaluation give the
same theorem, without requiring callers to rewrite the wrapped carrier values. -/
theorem initialConjugateCoordinates_starValid_of_interpret
    (coordinates : Fin m → CoeffVector n)
    (expression : PolynomialPrograms.Program ℚ m) (swap : Fin m → Fin m)
    (x : Fin m → ℂ) (hswap : ∀ i, x (swap i) = star (x i))
    (Φ : Element n relation →+* ℂ)
    (hcoordinates : ∀ i, interpret (Φ (Element.generator (c := relation))) (coordinates i) = x i)
    (hexpression : PolynomialPrograms.interpret (algebraMap ℚ ℂ) x expression =
      Φ (Element.generator (c := relation))) :
    Element.StarValid n relation
      (initialConjugateCoordinates (relation := relation) coordinates expression swap) := by
  apply initialConjugateCoordinates_starValid coordinates expression swap x hswap Φ _ hexpression
  intro i
  rw [← Element.interpret_generator (coordinates i), map_interpret]
  exact hcoordinates i

end ComplexCSP.AlgebraicEncoding

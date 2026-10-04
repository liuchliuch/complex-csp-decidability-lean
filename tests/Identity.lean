import ComplexCSP.Recognition.UniformAlgebraicIdentityDegree
import ComplexCSP.Algebra.AlgebraicInputCompleteness

open ComplexCSP ComplexCSP.Recognition ComplexCSP.AlgebraicEncoding
open ComplexCSP.ComplexRootCertificates
open Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def integerDescription (a : ℤ) : AlgebraicInput :=
  ⟨[-a,1], ⟨(a : ℚ)-1,(a : ℚ)+1,-1,1⟩⟩

private theorem integerDescription_represents (a : ℤ) :
    (integerDescription a).Represents (a : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
    simp only [integerListPolynomial_coeff, integerDescription, Polynomial.coeff_zero] at hc
    change (1 : ℤ) = 0 at hc
    exact one_ne_zero hc
  · simp [integerDescription, evalIntegerList]
  · simp [integerDescription, Rectangle.Contains]
  · intro w hw _
    simp only [integerDescription, evalIntegerList, List.foldr_cons, List.foldr_nil,
      mul_zero, add_zero, Int.cast_one, Int.cast_neg, mul_one] at hw
    linear_combination hw

private theorem integerDescription_valid (a : ℤ) : (integerDescription a).Valid :=
  ⟨a, integerDescription_represents a⟩

private def signedLanguage : Language (Fin 2) AlgebraicInput Unit where
  arity _ := 1
  arity_pos _ := by decide
  value _ a := integerDescription (if a 0 = 0 then 1 else -1)

private theorem signed_valid : ValidAlgebraicLanguage signedLanguage := by
  intro _ _
  exact integerDescription_valid _

private def oneLanguage : Language Unit AlgebraicInput Unit where
  arity _ := 1
  arity_pos _ := by decide
  value _ _ := integerDescription 1

private theorem one_valid : ValidAlgebraicLanguage oneLanguage := fun _ _ => integerDescription_valid 1

private def difference : PolynomialPrograms.Program AlgebraicInput 2 :=
  [⟨integerDescription 1, ![1,0]⟩, ⟨integerDescription (-1), ![0,1]⟩]
private theorem difference_valid : ∀ j : Fin difference.length, (difference.get j).coefficient.Valid := by
  intro j
  fin_cases j <;> exact integerDescription_valid _

private def directPins : Fin 2 → PinnedCoordinate (Fin 1) (Fin 2) := fun j => Sum.inl (fun _ => j)
private def conjugatePins : Fin 2 → PinnedCoordinate (Fin 1) (Fin 2) := fun j =>
  if j = 0 then Sum.inl (fun _ => 0) else Sum.inr (fun _ => 0)

private def nonhomogeneous : PolynomialPrograms.Program AlgebraicInput 1 :=
  [⟨integerDescription 1, ![1]⟩, ⟨integerDescription (-1), ![0]⟩]
private theorem nonhomogeneous_valid : ∀ j : Fin nonhomogeneous.length,
    (nonhomogeneous.get j).coefficient.Valid := by
  intro j
  fin_cases j <;> exact integerDescription_valid _

private def zeroProgram : PolynomialPrograms.Program AlgebraicInput 1 :=
  [⟨integerDescription 0, ![0]⟩]
private theorem zeroProgram_valid : ∀ j : Fin zeroProgram.length, (zeroProgram.get j).coefficient.Valid := by
  intro j
  fin_cases j
  exact integerDescription_valid 0

private def unitPins : Fin 1 → PinnedCoordinate (Fin 1) Unit := fun _ => Sum.inl (fun _ => ())

-- uniform ordinary unequal pins.
#guard (uniformAlgebraicIdentityTest
  signedLanguage signed_valid difference difference_valid directPins) == false
-- uniform independent conjugate coordinate.
#guard (uniformAlgebraicIdentityTest
  signedLanguage signed_valid difference difference_valid conjugatePins) == true
-- uniform nonhomogeneous identity.
#guard (uniformAlgebraicIdentityTest
  oneLanguage one_valid nonhomogeneous nonhomogeneous_valid unitPins) == true
-- uniform explicit zero coefficient.
#guard (uniformAlgebraicIdentityTest
  oneLanguage one_valid zeroProgram zeroProgram_valid unitPins) == true
-- uniform empty polynomial.
#guard (uniformAlgebraicIdentityTest oneLanguage one_valid
  ([] : PolynomialPrograms.Program AlgebraicInput 1) (fun j => Fin.elim0 j) unitPins) == true
-- uniform even-degree identity.
#guard (uniformAlgebraicDegreeIdentityTest
  signedLanguage signed_valid difference difference_valid 2 (by decide) directPins) == true
-- uniform degree-one rejection.
#guard (uniformAlgebraicDegreeIdentityTest
  signedLanguage signed_valid difference difference_valid 1 (by decide) directPins) == false
-- uniform even-degree nonhomogeneous identity.
#guard (uniformAlgebraicDegreeIdentityTest
  oneLanguage one_valid nonhomogeneous nonhomogeneous_valid 2 (by decide) unitPins) == true

-- Kernel-checked nonrational coefficient coverage (no expensive fallback execution).
private def outsideCoefficients (a b : AlgebraicInput) : PolynomialPrograms.Program AlgebraicInput 0 :=
  [⟨a, Fin.elim0⟩, ⟨b, Fin.elim0⟩]
private theorem outsideCoefficients_valid (a b : AlgebraicInput)
    (ha : a.Represents Complex.I) (hb : b.Represents (-Complex.I)) :
    ∀ j : Fin (outsideCoefficients a b).length,
      ((outsideCoefficients a b).get j).coefficient.Valid := by
  intro j
  fin_cases j
  · exact ⟨Complex.I, ha⟩
  · exact ⟨-Complex.I, hb⟩

private theorem outsideCoefficients_identity (a b : AlgebraicInput)
    (ha : a.Represents Complex.I) (hb : b.Represents (-Complex.I)) :
    uniformAlgebraicIdentityTest oneLanguage one_valid (outsideCoefficients a b)
      (outsideCoefficients_valid a b ha hb)
      (Fin.elim0 : Fin 0 → PinnedCoordinate (Fin 0) Unit) = true := by
  apply (uniformAlgebraicIdentityTest_correct oneLanguage one_valid (outsideCoefficients a b)
    (outsideCoefficients_valid a b ha hb) Fin.elim0 (fun _ _ => 1)
    (fun _ _ => by simpa only [oneLanguage, Int.cast_one] using integerDescription_represents 1)
    (![Complex.I, -Complex.I]) ?_).mpr
  · intro h I
    simp [programWithCoefficients, PolynomialPrograms.eval, PolynomialPrograms.interpret,
      PolynomialPrograms.interpretTerm, outsideCoefficients, List.ofFn_succ]
  · intro j
    fin_cases j
    · exact ha
    · exact hb

private theorem outsideCoefficients_degree_identity (a b : AlgebraicInput)
    (ha : a.Represents Complex.I) (hb : b.Represents (-Complex.I)) (δ : ℕ) (hδ : 0 < δ) :
    uniformAlgebraicDegreeIdentityTest oneLanguage one_valid (outsideCoefficients a b)
      (outsideCoefficients_valid a b ha hb) δ hδ
      (Fin.elim0 : Fin 0 → PinnedCoordinate (Fin 0) Unit) = true := by
  apply (uniformAlgebraicDegreeIdentityTest_correct oneLanguage one_valid (outsideCoefficients a b)
    (outsideCoefficients_valid a b ha hb) δ hδ Fin.elim0 (fun _ _ => 1)
    (fun _ _ => by simpa only [oneLanguage, Int.cast_one] using integerDescription_represents 1)
    (![Complex.I, -Complex.I]) ?_).mpr
  · intro h I hI
    simp [programWithCoefficients, PolynomialPrograms.eval, PolynomialPrograms.interpret,
      PolynomialPrograms.interpretTerm, outsideCoefficients, List.ofFn_succ]
  · intro j
    fin_cases j
    · exact ha
    · exact hb

example (q : ℚ) : (q : ℂ) ≠ Complex.I := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

example : ∃ a : AlgebraicInput, a.Represents Complex.I := by
  apply exists_algebraicInput_represents
  apply IsIntegral.isAlgebraic
  refine ⟨X^2 + C (1 : ℚ), monic_X_pow_add_C 1 (by decide), ?_⟩
  simp [Complex.I_sq]



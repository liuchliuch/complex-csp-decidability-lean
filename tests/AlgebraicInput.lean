import ComplexCSP.Algebra.InitialInputSearch

open ComplexCSP ComplexCSP.AlgebraicEncoding ComplexCSP.EncodedNumberField
open ComplexCSP.ComplexRootCertificates

private def zeroInput : AlgebraicInput := ⟨[0,1], ⟨-1,1,-1,1⟩⟩
private def halfInput : AlgebraicInput := ⟨[-1,2], ⟨0,1,-1,1⟩⟩
private def input : Fin 2 → AlgebraicInput := ![zeroInput, halfInput]

private theorem zero_represents : zeroInput.Represents 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [zeroInput, integerListPolynomial]
  · simp [zeroInput, evalIntegerList]
  · norm_num [zeroInput, Rectangle.Contains]
  · intro w hw _
    simpa [zeroInput, evalIntegerList] using hw

private theorem half_represents : halfInput.Represents (1/2 : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
    norm_num [halfInput, integerListPolynomial, Polynomial.coeff_one] at hc
  · norm_num [halfInput, evalIntegerList]
  · norm_num [halfInput, Rectangle.Contains]
  · intro w hw _
    simp only [halfInput, evalIntegerList, List.foldr_cons, List.foldr_nil, mul_zero,
      add_zero, Int.cast_ofNat, Int.cast_neg, Int.cast_one] at hw
    linear_combination (1/2 : ℂ) * hw

private theorem input_valid : ∀ i, (input i).Valid := by
  intro i
  fin_cases i
  · exact ⟨0, zero_represents⟩
  · exact ⟨1/2, half_represents⟩

private def repeatedRootInput : AlgebraicInput := ⟨[0,0,1], ⟨-1,1,-1,1⟩⟩
private theorem repeatedRoot_represents : repeatedRootInput.Represents 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
    norm_num [repeatedRootInput, integerListPolynomial, Polynomial.coeff_one] at hc
  · simp [repeatedRootInput, evalIntegerList]
  · norm_num [repeatedRootInput, Rectangle.Contains]
  · intro w hw _
    have he : w * w = 0 := by simpa [repeatedRootInput, evalIntegerList] using hw
    exact mul_self_eq_zero.mp he

private def repeatedInputs : Fin 3 → AlgebraicInput := ![zeroInput, halfInput, zeroInput]
private theorem repeatedInputs_valid : ∀ i, (repeatedInputs i).Valid := by
  intro i
  fin_cases i
  · exact ⟨0, zero_represents⟩
  · exact ⟨1/2, half_represents⟩
  · exact ⟨0, zero_represents⟩

private def summary {m : ℕ} (C : InitialInputCandidate m) :=
  (C.degree, List.ofFn C.tail, List.ofFn (fun i => List.ofFn (C.coordinates i)), C.radius)

-- rational seed accepted.
#guard ((rationalInitialSeed input).test input) == true
-- actual search code.
#guard (findInitialInputCode input input_valid) == 0
-- actual converted rational inputs.
#guard (summary (findInitialInputCandidate input input_valid)) == (1, [0], [[0], [1/2]], 1)
-- proof-carrying converted output.
#guard ((searchInitialInputs input input_valid).val.test input) == true
-- empty input actual search code.
#guard (findInitialInputCode
  (Fin.elim0 : Fin 0 → AlgebraicInput) (fun i => Fin.elim0 i)) == 0
-- nonlinear seed rejected.
#guard ((rationalInitialSeed
  (fun _ : Fin 1 => (⟨[1,0,1], ⟨-1,1,0,2⟩⟩ : AlgebraicInput))).test
    (fun _ : Fin 1 => ⟨[1,0,1], ⟨-1,1,0,2⟩⟩)) == false

-- repeated input actual search code.
#guard (findInitialInputCode repeatedInputs repeatedInputs_valid) == 0
-- repeated-root description actual search code.
#guard (findInitialInputCode
  (fun _ : Fin 1 => repeatedRootInput) (fun _ => ⟨0, repeatedRoot_represents⟩)) == 0
-- wrong root disk seed rejected.
#guard (({rationalInitialSeed input with center := ⟨2,0⟩}).test input) == false
-- wrong image rectangle seed rejected.
#guard ((rationalInitialSeed input).test
  (fun i => if i = 0 then {zeroInput with rectangle := ⟨1,2,1,2⟩} else halfInput)) == false


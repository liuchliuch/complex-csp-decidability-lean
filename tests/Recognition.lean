import ComplexCSP.Recognition.UniformAlgebraicDegreeGlobal

open ComplexCSP ComplexCSP.Recognition ComplexCSP.AlgebraicEncoding
open ComplexCSP.ComplexRootCertificates

private def halfInput : AlgebraicInput := ⟨[-1,2], ⟨0,1,-1,1⟩⟩
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

private def halfLanguage : Language (Fin 1) AlgebraicInput (Fin 1) :=
  ⟨fun _ => 1, fun _ => Nat.zero_lt_succ 0, fun _ _ => halfInput⟩
private theorem halfLanguage_valid : ValidAlgebraicLanguage halfLanguage :=
  fun _ _ => ⟨1/2,half_represents⟩

private def emptyLanguage : Language (Fin 1) AlgebraicInput (Fin 0) :=
  ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
private theorem emptyLanguage_valid : ValidAlgebraicLanguage emptyLanguage :=
  fun i => Fin.elim0 i

#guard (uniformAlgebraicGlobalTest halfLanguage halfLanguage_valid) == true
#guard (uniformAlgebraicDegreeGlobalTest halfLanguage halfLanguage_valid 1 (by decide)) == true
#guard (uniformAlgebraicDegreeGlobalTest halfLanguage halfLanguage_valid 2 (by decide)) == true
#guard (uniformAlgebraicGlobalTest emptyLanguage emptyLanguage_valid) == true
#guard (uniformAlgebraicDegreeGlobalTest emptyLanguage emptyLanguage_valid 2 (by decide)) == true


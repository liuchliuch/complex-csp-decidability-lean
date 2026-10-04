import ComplexCSP.Recognition.UniformAlgebraicDetector
open ComplexCSP ComplexCSP.AlgebraicEncoding ComplexCSP.Recognition
open ComplexCSP.ComplexRootCertificates
private def halfInput : AlgebraicInput := ⟨[-1,2],⟨0,1,-1,1⟩⟩
private theorem half_represents : halfInput.Represents (1/2 : ℂ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
    norm_num [halfInput,integerListPolynomial,Polynomial.coeff_one] at hc
  · norm_num [halfInput,evalIntegerList]
  · norm_num [halfInput,Rectangle.Contains]
  · intro w hw _
    simp only [halfInput,evalIntegerList,List.foldr_cons,List.foldr_nil,mul_zero,
      add_zero,Int.cast_ofNat,Int.cast_neg,Int.cast_one] at hw
    linear_combination (1/2 : ℂ)*hw
private def L : Language Unit AlgebraicInput Unit :=
  ⟨fun _ => 2,fun _ => Nat.zero_lt_succ 1,fun _ _ => halfInput⟩
private theorem hL : ValidAlgebraicLanguage L := fun _ _ => ⟨1/2,half_represents⟩
private def P : Presentation L (Fin 2) :=
  ⟨1,⟨[⟨(),fun i => if i.val = 0 then Sum.inl 0 else Sum.inr 0⟩]⟩⟩
private theorem hBO : HasAlgebraicBO L := by
  refine ⟨fun _ _ => 1/2,fun _ _ => half_represents,?_⟩
  apply (jointBO_iff_singletonBO _).mpr
  intro T _ _
  exact blockOrthogonal_subsingleton_rows T.singletonRows
private def output := uniformAlgebraicRowDetector L hL P (Nat.zero_lt_succ 0) hBO
-- raw encoded detector output.
#guard (output.time,output.exponent,
  output.presentation.hidden,output.presentation.inst.constraints.length) == (0,1,3,2)
-- original-syntax rational interpretation.
#guard ((output.presentation.reweight
  (fun _ _ => (1/2 : ℚ))).table (fun _ => ())) == (1/4 : ℚ)

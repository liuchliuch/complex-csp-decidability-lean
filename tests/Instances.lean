import ComplexCSP.Complexity.CSPCountCertificates

namespace ComplexCSP.CountMembershipRegression
open ComplexityCSPCode ComplexityCSPAssignmentVerifier

def signed : Language (Fin 2) ℚ (Fin 1) where
  arity _ := 1
  arity_pos _ := by decide
  value _ a := if a 0 = 0 then -1 else 0

def isolated : Code := ⟨2,[(0,[0])]⟩
def repeated : Code := ⟨2,[(0,[0]),(0,[0])]⟩
def emptyConstraints : Code := ⟨3,[]⟩

def diagonal : Language (Fin 2) ℚ (Fin 1) where
  arity _ := 2
  arity_pos _ := by decide
  value _ a := if a 0 = a 1 then (if a 0 = 0 then -2 else 3) else 7

def repeatedScope : Code := ⟨1,[(0,[0,0])]⟩

example : Valid signed isolated := by decide +kernel
example : Valid signed repeated := by decide +kernel
example : Valid diagonal repeatedScope := by decide +kernel
example : countAt signed isolated (-1) = 2 := by decide +kernel
example : countAt signed isolated 0 = 2 := by decide +kernel
example : countAt signed repeated 1 = 2 := by decide +kernel
example : countAt signed emptyConstraints 1 = 8 := by decide +kernel
example : countAt diagonal repeatedScope 7 = 0 := by decide +kernel

-- signed weight with isolated variable.
#guard (countAt signed isolated (-1)) == 2
-- zero weight retained.
#guard (countAt signed isolated 0) == 2
-- repeated constraint occurrence.
#guard (countAt signed repeated 1) == 2
-- empty constraints and isolated variables.
#guard (countAt signed emptyConstraints 1) == 8
-- repeated scope diagonal weights.
#guard (countAt diagonal repeatedScope (-2), countAt diagonal repeatedScope 3) == (1,1)
-- inconsistent off-diagonal weight excluded.
#guard (countAt diagonal repeatedScope 7) == 0
-- actual assignment product.
#guard (assignmentWeight signed isolated [true,false,false,true,false,false]) == (-1 : ℚ)
-- actual repeated-occurrence product.
#guard (assignmentWeight signed repeated [true,false,false,true,false,false]) == (1 : ℚ)
-- one-hot ambiguity rejected.
#guard (rowMatchCode 2 [true,true] 0 0) == false

end ComplexCSP.CountMembershipRegression

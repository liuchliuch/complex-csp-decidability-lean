import ComplexCSP.Recognition.CertificatesFiniteLocus
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneity of actual certificate equations -/

namespace ComplexCSP.Certificates

/-- Support and anchor equations have degree one; minor equations degree two. -/
def EquationIndex.degree {X D : Type*} : EquationIndex X D → ℕ
  | .support _ _ => 1
  | .twisted _ _ _ _ => 2
  | .ordinary _ _ _ _ => 2
  | .firstAnchor _ _ _ => 1
  | .secondAnchor _ _ _ => 1

theorem equationIndex_degree_bounds {X D : Type*} (i : EquationIndex X D) :
    1 ≤ i.degree ∧ i.degree ≤ 2 := by
  cases i <;> norm_num [EquationIndex.degree]

/-- Homogeneity is proved for every actual polynomial, including disabled zero
equations. Conjugation occurs only in root-retention arithmetic. -/
theorem equation_homogeneous {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (i : EquationIndex X D) :
    (equation roots c i).IsHomogeneous i.degree := by
  cases i with
  | support x z =>
    simp only [equation, EquationIndex.degree]
    split_ifs
    · exact MvPolynomial.isHomogeneous_zero _ _ _
    · exact MvPolynomial.isHomogeneous_X K (x, z)
  | twisted x y z w =>
    simp only [equation, EquationIndex.degree]
    split_ifs
    · exact ((MvPolynomial.isHomogeneous_X K (x, z)).mul
        (MvPolynomial.isHomogeneous_X K (y, w))).sub
        (((MvPolynomial.isHomogeneous_X K (x, w)).mul
          (MvPolynomial.isHomogeneous_X K (y, z))).C_mul _)
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | ordinary x y z w =>
    simp only [equation, EquationIndex.degree]
    split_ifs
    · exact ((MvPolynomial.isHomogeneous_X K (x, z)).mul
        (MvPolynomial.isHomogeneous_X K (y, w))).sub
        ((MvPolynomial.isHomogeneous_X K (x, w)).mul (MvPolynomial.isHomogeneous_X K (y, z)))
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | firstAnchor x y z =>
    simp only [equation, EquationIndex.degree]
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X K (x, z)).sub
        ((MvPolynomial.isHomogeneous_X K (x, (c.pair x y).group z)).C_mul _)
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | secondAnchor x y z =>
    simp only [equation, EquationIndex.degree]
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X K (y, z)).sub
        ((MvPolynomial.isHomogeneous_X K (y, (c.pair x y).group z)).C_mul _)
    · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem equation_totalDegree_le_two {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (i : EquationIndex X D) :
    (equation roots c i).totalDegree ≤ 2 :=
  (equation_homogeneous roots c i).totalDegree_le.trans (equationIndex_degree_bounds i).2

/-- The finite branch equation set consists entirely of positive-degree
homogeneous polynomials of degree at most two. -/
theorem equationSet_homogeneous {X D R K : Type*} [Fintype X] [DecidableEq X]
    [Fintype D] [DecidableEq D] [Field K] [DecidableEq K]
    (roots : RootAlphabet K R) (c : Certificate X D R)
    (p : MvPolynomial (X × D) K) (hp : p ∈ equationSet roots c) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ p.IsHomogeneous n := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨i.degree, (equationIndex_degree_bounds i).1, (equationIndex_degree_bounds i).2,
    equation_homogeneous roots c i⟩

end ComplexCSP.Certificates

import ComplexCSP.Algebra.PositiveBinaryApex
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import PlanarHom.ListContextMachines

/-! # Literal shared-apex code and triangle replacement

The single new vertex is shared by every source constraint. Each three-variable
triangle is then expanded by the independently proved fixed-gadget compiler.
No planar promise is asserted for the output.
-/
namespace ComplexCSP.PositiveBinaryApex
open ComplexityCSPCode
open PlanarHom PlanarHom.Complexity PairProjectionMachines

variable {K : Type} [CommSemiring K]

/-- Three incident edge factors, before summing the shared apex. -/
def triangleLanguage (A : Bool → Bool → K) : Language Bool K (Fin 1) :=
  ⟨fun _ => 3, fun _ => Nat.succ_pos 2,
    fun _ a => A (a 0) (a 1) * A (a 0) (a 2) * A (a 1) (a 2)⟩

def trianglePresentation (A : Bool → Bool → K) :
    Presentation (MatrixCSP.language A) (Fin 3) :=
  ⟨0,⟨[⟨0,![Sum.inl 0,Sum.inl 1]⟩,
    ⟨0,![Sum.inl 0,Sum.inl 2]⟩,⟨0,![Sum.inl 1,Sum.inl 2]⟩]⟩⟩

theorem trianglePresentation_table (A : Bool → Bool → K) (a : Fin 3 → Bool) :
    (trianglePresentation A).table a = (triangleLanguage A).value 0 a := by
  simp [trianglePresentation,Presentation.table,Instance.partition,Instance.eval,
    Constraint.eval,MatrixCSP.language,triangleLanguage,mul_assoc]

def triangleGadgets (A : Bool → Bool → K) :
    GadgetSubstitution.Gadgets (MatrixCSP.language A) (triangleLanguage A) :=
  fun _ => trianglePresentation A

theorem triangleGadgets_realizes (A : Bool → Bool → K) :
    GadgetSubstitution.Realizes (triangleGadgets A) := by
  intro j a
  exact trianglePresentation_table A a

/-- Append the same last vertex to every ordered source scope. -/
def addApexConstraint (n : ℕ) (c : ℕ × List ℕ) : ℕ × List ℕ := (c.1,c.2 ++ [n])

def addApex (g : Code) : Code :=
  ⟨g.vertices+1,g.constraints.map (addApexConstraint g.vertices)⟩

theorem addApex_constraint_valid (A B : Bool → Bool → K) (g : Code)
    (c : ℕ × List ℕ) (hc : ConstraintValid (MatrixCSP.language B) g.vertices c) :
    ConstraintValid (triangleLanguage A) (addApex g).vertices (addApexConstraint g.vertices c) := by
  obtain ⟨hs,hlen,hv⟩ := hc
  refine ⟨hs,?_,?_⟩
  · simpa [addApexConstraint,MatrixCSP.language,triangleLanguage] using hlen
  · intro v hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_succ_of_lt (hv v hm)
    · have he := List.mem_singleton.mp hm
      subst v
      exact Nat.lt_succ_self _

theorem addApex_valid (A B : Bool → Bool → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) : Valid (triangleLanguage A) (addApex g) := by
  intro c hc
  change c ∈ g.constraints.map (addApexConstraint g.vertices) at hc
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hc
  exact addApex_constraint_valid A B g old (hg old hold)

/-- Full general-graph output: one shared apex and three binary constraints for
all original edge occurrences, including loops and duplicates. -/
def compileApex (A : Bool → Bool → K) (g : Code) : Code :=
  ComplexityGadgetSubstitution.compile
    (ComplexityGadgetSubstitution.templates (triangleGadgets A)) (addApex g)

theorem compileApex_valid (A B : Bool → Bool → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) : Valid (MatrixCSP.language A) (compileApex A g) :=
  ComplexityGadgetSubstitution.compile_valid (triangleGadgets A) _ (addApex_valid A B g hg)

theorem compileApex_partition (A B : Bool → Bool → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) :
    partition (MatrixCSP.language A) (compileApex A g) = partition (triangleLanguage A) (addApex g) :=
  ComplexityGadgetSubstitution.compile_partition (triangleGadgets A)
    (triangleGadgets_realizes A) _ (addApex_valid A B g hg)

omit [CommSemiring K] in
theorem fp_addApexConstraint :
    FP (BitEncoding.unaryNat.prod constraintEncoding) constraintEncoding
      (fun p : ℕ × (ℕ × List ℕ) => addApexConstraint p.1 p.2) := by
  have hn := (fp_fst BitEncoding.unaryNat constraintEncoding).comp
    UnaryNatConversionMachine.fp_conversion
  have hc := fp_snd BitEncoding.unaryNat constraintEncoding
  have hl := hc.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hs := hc.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have singleton := (hn.pair (fp_const _ BitEncoding.nat.list [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  exact hl.pair ((hs.pair singleton).comp (ListMutationMachines.fp_append BitEncoding.nat))

omit [CommSemiring K] in
theorem fp_addApex : FP encoding encoding addApex := by
  have hn := ComplexityGadgetSubstitution.fp_vertices
  have hc := ComplexityGadgetSubstitution.fp_constraints
  have hv := (hn.pair (fp_const encoding BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add
  have hs := (hn.pair hc).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat constraintEncoding constraintEncoding
      (fun p => addApexConstraint p.1 p.2) fp_addApexConstraint)
  exact (hv.pair hs).transportOutput (fun _ => rfl)

theorem fp_compileApex (A : Bool → Bool → K) : FP encoding encoding (compileApex A) :=
  fp_addApex.comp (ComplexityGadgetSubstitution.fp_compile
    (ComplexityGadgetSubstitution.templates (triangleGadgets A)))

end ComplexCSP.PositiveBinaryApex

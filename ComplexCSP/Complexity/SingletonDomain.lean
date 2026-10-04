import ComplexCSP.Complexity.CSPValidation
import PlanarHom.MaterializedFieldListMachines

/-! # A genuine FP evaluator for every singleton-domain fixed language

This closes the domain-one boundary omitted by Lin's domain-at-least-two setup.
The evaluator validates every raw constraint and uses the stipulated unit default
on invalid rows, so correctness holds on all codes, not only the valid promise.
-/
namespace ComplexCSP.ComplexitySingletonDomain
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode ComplexityCSPValidation

variable {D K : Type} [Unique D] [Fintype D] [Field K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K)

def valueTable : List (ℕ × K) :=
  List.ofFn (fun i : Fin s => (i.val,L.value i (fun _ => default)))

def symbolValue (symbol : ℕ) : K := ComplexityFiniteLookup.lookup 1 (valueTable L) symbol

/-- Exact total row interpretation, including all raw validation conditions. -/
def constraintValue (p : ℕ × (ℕ × List ℕ)) : K :=
  if ConstraintValid L p.1 p.2 then symbolValue L p.2.1 else 1

/-- There is precisely one assignment, so partition evaluation is a field product. -/
def evaluate (g : Code) : K := (g.constraints.map (fun c => constraintValue L (g.vertices,c))).prod

omit [Fintype D] in
 theorem fp_constraintValue :
    FP (BitEncoding.unaryNat.prod constraintEncoding) (numberFieldEncoding basis) (constraintValue L) := by
  have hp : FP (BitEncoding.unaryNat.prod constraintEncoding) BitEncoding.bool
      (fun p => decide (ConstraintValid L p.1 p.2)) :=
    (fp_constraintValidTest L).congr (fun p => by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact constraintValidTest_correct L p.1 p.2)
  have hi := (fp_snd BitEncoding.unaryNat constraintEncoding).comp
    (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hv := hi.comp (ComplexityFiniteLookup.fp_lookup (numberFieldEncoding basis) 1 (valueTable L))
  exact hp.ite hv (fp_const _ _ 1)

omit [Fintype D] in
/-- This is a compiled, bit-costed FP machine, not a supplied evaluator premise. -/
theorem fp_evaluate : FP encoding (numberFieldEncoding basis) (evaluate L) := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat constraintEncoding
    (numberFieldEncoding basis) (constraintValue L) (fp_constraintValue L basis)
  exact (hv.comp hm).comp (MaterializedFieldListMachines.fp_product basis)

omit [Fintype D] [Algebra ℚ K] in
 theorem constraintValue_correct (g : Code) (c : ℕ × List ℕ) (σ : Fin g.vertices → D) :
    constraintValue L (g.vertices,c) = entryValue L (constraintEntry L g σ c) := by
  by_cases hc : ConstraintValid L g.vertices c
  · simp only [constraintValue,hc,↓reduceIte,constraintEntry,↓reduceDIte,entryValue]
    have hv := ComplexityFiniteLookup.lookup_fin_table 1
      (fun i : Fin s => L.value i (fun _ => default)) (⟨c.1,hc.choose⟩ : Fin s)
    change symbolValue L c.1 = L.value ⟨c.1,hc.choose⟩ (fun _ => default) at hv
    rw [hv]
    congr 1
    exact Subsingleton.elim _ _
  · simp [constraintValue,constraintEntry,hc,entryValue]

omit [Algebra ℚ K] in
/-- Exact total semantics, including empty constraints, isolated variables, zero
or signed coefficients, malformed rows and arity-zero witness edge cases. -/
theorem evaluate_correct (g : Code) : evaluate L g = partition L g := by
  simp only [partition,Fintype.sum_unique]
  unfold evaluate eval assignmentWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  exact constraintValue_correct L g c default

/-- The literal partition function itself belongs to genuine FP on this boundary. -/
theorem fp_partition : FP encoding (numberFieldEncoding basis) (partition L) :=
  (fp_evaluate L basis).congr (evaluate_correct L)

end ComplexCSP.ComplexitySingletonDomain

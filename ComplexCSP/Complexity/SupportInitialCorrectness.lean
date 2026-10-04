import ComplexCSP.Complexity.SupportInitialSemantics
import ComplexCSP.Complexity.WitnessReconstruction

/-! # Initial support compiler: actual FP, exact shape, and membership correctness -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}
variable (L : Language (Fin d) K (Fin s))

/-- The exact-dimensional shape proof is erased; the output is the same raw
materialized table/seed word produced by the proved FP compiler. -/
def compiledSupport (m : Fin d → Fin d → Fin d → Fin d) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) : {W : RawWitness // ShapedWitness (d:=d) W} :=
  ⟨rawSupportCompiler L m defaultValue g,by
    obtain ⟨W,hW⟩ := rawSupportCompiler_shape L m defaultValue g
    exact ⟨g.vertices,W,hW⟩⟩

theorem fp_compiledSupport (m : Fin d → Fin d → Fin d → Fin d) (defaultValue : Fin d) :
    FP ComplexityCSPCode.encoding (shapedWitnessCode d) (compiledSupport L m defaultValue) :=
  (fp_rawSupportCompiler L m defaultValue).transportOutput (fun _ => rfl)

/-- Exact support membership follows through the literal stored constructor.
The operation laws and original fixed table-preservation hypotheses are the
actual mathematical assumptions; no verifier, support or FP oracle is supplied. -/
theorem compiledSupport_member {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hL : ∀ i, Preserves m {x | L.value i x ≠ 0}) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (x : Tuple (Fin d) g.vertices) :
    memberRaw d (fun a b c => m (a,b,c))
      ((compiledSupport L (fun a b c => m (a,b,c)) defaultValue g).val.1,
        word x,(compiledSupport L (fun a b c => m (a,b,c)) defaultValue g).val.2) = true ↔
      ComplexityCSPCode.eval L g (view x) ≠ 0 := by
  change memberRaw d (fun a b c => m (a,b,c))
    ((rawSupportCompiler L (fun a b c => m (a,b,c)) defaultValue g).1,word x,
      (rawSupportCompiler L (fun a b c => m (a,b,c)) defaultValue g).2) = true ↔ _
  rw [rawSupportCompiler_stored L m defaultValue g hg]
  change memberRaw d (fun a b c => m (a,b,c)) (storedState (rawSupportWitness L m defaultValue g hg) x) = true ↔ _
  rw [memberRaw_stored]
  exact (construct_member_correct hm defaultValue (supportConstraints L g hg)
    (supportConstraints_preserved L m hL g hg) x).trans (supportConstraints_correct L g hg (view x))

end ComplexCSP.ComplexitySupportWitnessPrimitives

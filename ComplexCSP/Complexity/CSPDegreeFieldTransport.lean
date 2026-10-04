import ComplexCSP.Complexity.CSPCommonField
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import ComplexCSP.Recognition.DegreeConditionsTransport
import PlanarHom.PromisedFPReductionClosure

/-! # Charged coefficient conversion on the actual degree-valid promise -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityCSPDegreeFieldTransport
open PlanarHom PlanarHom.Complexity PairProjectionMachines ComplexityCSPCode
open ComplexityGadgetSubstitution
variable {D K R : Type} [Fintype D] [Field K] [Field R]
variable [Algebra ℚ K] [Algebra ℚ R] [DecidableEq K] [DecidableEq R]
variable {s d e : ℕ} (L : Language D K (Fin s))
variable (bK : Module.Basis (Fin d) ℚ K) (bR : Module.Basis (Fin e) ℚ R)
variable (φ : K →ₐ[ℚ] R) (δ : ℕ)

omit [Fintype D] [DecidableEq K] [DecidableEq R] in
theorem degreeValid_mapValues (g : Code) :
    DegreeValid (L.mapValues φ.toRingHom) δ g ↔ DegreeValid L δ g := by
  have ho (hg : Valid L g) :
      (toInstance (L.mapValues φ.toRingHom) g hg).occurrences=(toInstance L g hg).occurrences := by
    simp only [Instance.occurrences,toInstance,List.flatMap_map]
    rfl
  constructor <;> rintro ⟨hg,hd⟩ <;> refine ⟨hg,?_⟩
  · intro v
    have hh := hd v
    simpa only [Instance.occurrenceDegree,ho hg] using hh
  · intro v
    have hh := hd v
    simpa only [Instance.occurrenceDegree,ho hg] using hh

def descentReduction : PromisePolyTimeTuringReduction
    (degreePartitionProblem L bK δ)
    (degreePartitionProblem (L.mapValues φ.toRingHom) bR δ) := by
  let h := FixedFieldEncodingTransport.exists_fp_leftInverse bK bR φ.toLinearMap φ.injective
  let g := Classical.choose h
  have hg := Classical.choose_spec h
  let prepare : Code → Bits × List Code := fun a => ([],[a])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    exact (fp_const encoding BitEncoding.bits []).pair
      (((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding))
  let recover : Bits × List R → K := fun a => g (a.2.headD 0)
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding bR).list) (numberFieldEncoding bK) recover :=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding bR) 0)).comp hg.2
  let target := degreePartitionProblem L bK δ
  let source := degreePartitionProblem (L.mapValues φ.toRingHom) bR δ
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h,encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let bound := Classical.choose (exists_partition_output_bound (L.mapValues φ.toRingHom) bR)
  have hb := Classical.choose_spec (exists_partition_output_bound (L.mapValues φ.toRingHom) bR)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding bR)
    (numberFieldEncoding bK) target source prepare (partition (L.mapValues φ.toRingHom)) recover
    (Classical.choice hp) (Classical.choice hr) view hs ?_ ?_ ?_ bound ?_
  · intro raw h out hout
    have he : out=view raw h := List.mem_singleton.mp hout
    subst out
    exact ⟨_,(degreeValid_mapValues L φ δ _).mpr h.choose_spec.1,rfl⟩
  · intro out _
    exact encodedFunction_encode encoding (numberFieldEncoding bR) (partition (L.mapValues φ.toRingHom)) [] out
  · intro raw h
    change (numberFieldEncoding bK).encode (g (partition (L.mapValues φ.toRingHom) (view raw h))) =
      encodedFunction encoding (numberFieldEncoding bK) (partition L) [] raw
    rw [ComplexityCSPCoefficientTransport.partition_mapValues]
    conv_rhs => rw [←hs raw h,encodedFunction_encode]
    exact congrArg (numberFieldEncoding bK).encode (hg.1 (partition L (view raw h)))
  · intro raw h
    obtain ⟨a,ha,rfl⟩ := h
    simpa only [source,degreePartitionProblem,encodedFunction_encode] using hb a


/-- The converse direction computes the image of the source-field oracle answer
by the actual fixed-coordinate embedding machine. Every oracle answer is charged. -/
def embeddingReduction : PromisePolyTimeTuringReduction
    (degreePartitionProblem (L.mapValues φ.toRingHom) bR δ)
    (degreePartitionProblem L bK δ) := by
  let prepare : Code → Bits × List Code := fun a => ([],[a])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    exact (fp_const encoding BitEncoding.bits []).pair
      (((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding))
  let recover : Bits × List K → R := fun a => φ (a.2.headD 0)
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding bK).list) (numberFieldEncoding bR) recover :=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding bK) 0)).comp
      (FixedFieldEncodingTransport.fp_fieldEmbedding bK bR φ)
  let target := degreePartitionProblem (L.mapValues φ.toRingHom) bR δ
  let source := degreePartitionProblem L bK δ
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h,encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let bound := Classical.choose (exists_partition_output_bound L bK)
  have hb := Classical.choose_spec (exists_partition_output_bound L bK)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding bK)
    (numberFieldEncoding bR) target source prepare (partition L) recover
    (Classical.choice hp) (Classical.choice hr) view hs ?_ ?_ ?_ bound ?_
  · intro raw h out hout
    have he : out=view raw h := List.mem_singleton.mp hout
    subst out
    exact ⟨_,(degreeValid_mapValues L φ δ _).mp h.choose_spec.1,rfl⟩
  · intro out _
    exact encodedFunction_encode encoding (numberFieldEncoding bK) (partition L) [] out
  · intro raw h
    change (numberFieldEncoding bR).encode (φ (partition L (view raw h))) =
      encodedFunction encoding (numberFieldEncoding bR) (partition (L.mapValues φ.toRingHom)) [] raw
    conv_rhs => rw [←hs raw h,encodedFunction_encode,ComplexityCSPCoefficientTransport.partition_mapValues]
    rfl
  · intro raw h
    obtain ⟨a,ha,rfl⟩ := h
    simpa only [source,degreePartitionProblem,encodedFunction_encode] using hb a

end ComplexCSP.ComplexityCSPDegreeFieldTransport

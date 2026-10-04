import ComplexCSP.Complexity.CSPCountReduction

/-! # Partition evaluation reduces to natural weight multiplicities -/
namespace ComplexCSP.ComplexityPartitionCountReduction
open scoped BigOperators
open ComplexityCSPCode ComplexityCSPCountReduction
open PlanarHom PlanarHom.Complexity PairProjectionMachines
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def prepare (g : Code) : List K × List (Code × K) :=
  let ns := ComplexityCSPNodes.nodes L g.constraints.length
  (ns, ns.map (fun z => (g,z)))

def recover (p : List K × List ℕ) : K :=
  (List.zipWith (fun (z : K) (n : ℕ) => z * (n : K)) p.1 p.2).sum

theorem fp_prepare : FP encoding ((numberFieldEncoding basis).list.prod (countEncoding basis).list)
    (prepare L) := by
  let e := numberFieldEncoding basis
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := (hv.comp (fp_snd _ _)).comp (ListUnaryLengthMachine.fp_length constraintEncoding)
  have hn := hm.comp (ComplexityCSPNodes.fp_nodes L basis)
  have hrow : FP (encoding.prod e) (countEncoding basis) (fun p : Code × K => p) := fp_id _
  have hq := ((fp_id encoding).pair hn).comp
    (ListContextMachines.fp_mapWithContext encoding e (countEncoding basis) _ hrow)
  exact hn.pair hq

omit [DecidableEq K] in
theorem fp_recover : FP ((numberFieldEncoding basis).list.prod BitEncoding.nat.list)
    (numberFieldEncoding basis) (recover : List K × List ℕ → K) := by
  let e := numberFieldEncoding basis
  have hc := (fp_snd e.list BitEncoding.nat.list).comp
    (ListMapMachines.fp_map BitEncoding.nat e _ (ComplexityNaturalDecoder.fp_natCast basis))
  exact (((fp_fst e.list BitEncoding.nat.list).pair hc).comp
    (FieldDotProductMachines.fp_dot basis)).congr (fun p => by simp [recover,List.zipWith_map_right])

omit [Algebra ℚ K] in
theorem recovery_correct (g : Code) :
    recover ((prepare L g).1, (prepare L g).2.map (fun p => countAt L p.1 p.2)) = partition L g := by
  let μ := ComplexityCSPNodes.node L g.constraints.length
  have hn := ComplexityCSPNodes.nodes_eq_ofFn L g.constraints.length
  simp only [prepare,Function.comp_def,recover,hn,List.map_ofFn]
  rw [LagrangeRecoveryListSemantics.zipWith_ofFn,List.sum_ofFn]
  have hs := ComplexityCountRecovery.sum_grouped (eval L g) μ
    (ComplexityCSPNodes.node_injective L _) (ComplexityCSPNodes.eval_coverage L g)
    id rfl
  simpa only [μ,ComplexityCountRecovery.count,countAt,id_eq,mul_comm,partition] using hs

theorem count_answer_bound : ∃ p : Polynomial ℕ, ∀ raw,
    (countProblem L basis).valid raw → ((countProblem L basis).value raw).length ≤ p.eval raw.length := by
  refine ⟨Polynomial.C (Nat.size (Fintype.card D)) * Polynomial.X + 1, ?_⟩
  rintro raw ⟨⟨g,z⟩,hg,rfl⟩
  simp only [countProblem,encodedFunction_encode]
  have hc : countAt L g z ≤ Fintype.card D ^ g.vertices := by
    simpa [countAt,Fintype.card_fun] using
      (Finset.card_filter_le (s := Finset.univ) (p := fun a : Fin g.vertices → D => eval L g a=z))
  have hb := EncodingSizeBounds.nat_encoding_length_le_of_le_pow hc
  have hgsize := size_le_encoding_length g
  have hp : (encoding.encode g).length ≤ ((countEncoding basis).encode (g,z)).length := by
    simp only [countEncoding,BitEncoding.prod_length]
    omega
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith

/-- Actual single-batch oracle reduction with the polynomially bounded natural
answers charged by the independent oracle-machine model. -/
noncomputable def reduction : PromisePolyTimeTuringReduction
    (partitionProblem L basis) (countProblem L basis) := by
  classical
  let p := Classical.choose (count_answer_bound L basis)
  have hp := Classical.choose_spec (count_answer_bound L basis)
  let target := partitionProblem L basis
  let source := countProblem L basis
  let view : ∀ raw, target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h, encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  refine nonadaptiveReduction encoding (numberFieldEncoding basis).list (countEncoding basis)
    BitEncoding.nat (numberFieldEncoding basis) target source (prepare L)
    (fun p => countAt L p.1 p.2) recover (Classical.choice (fp_prepare L basis))
    (Classical.choice (fp_recover basis)) view hs ?_ ?_ ?_ p ?_
  · intro raw h q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨_,h.choose_spec.1,rfl⟩
  · intro q _
    exact encodedFunction_encode (countEncoding basis) BitEncoding.nat (fun p => countAt L p.1 p.2) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (recover ((prepare L (view raw h)).1,
        (prepare L (view raw h)).2.map (fun p => countAt L p.1 p.2))) =
      encodedFunction encoding (numberFieldEncoding basis) (partition L) [] raw
    rw [recovery_correct]
    conv_rhs => rw [←hs raw h,encodedFunction_encode]
  · exact hp

end ComplexCSP.ComplexityPartitionCountReduction

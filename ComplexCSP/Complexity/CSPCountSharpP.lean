import ComplexCSP.Complexity.CSPCountCertificates
import ComplexCSP.Complexity.CSPCountReduction

/-! # Genuine accepting-path #P membership of fixed-language COUNT

The total #P extension is built from an actual FP verifier. On the existing
canonical valid-code promise its accepting-path count is exactly `countAt`.
Targets remain in the same fixed rational-basis field, with its original codec.
-/
set_option maxHeartbeats 2000000
noncomputable section
namespace ComplexCSP.ComplexityCSPCountSharpP
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
open ComplexityCSPCode ComplexityCSPCountCertificates

variable {q s : ℕ} {K : Type} [Field K] [Algebra ℚ K]
variable (L : Language (Fin q) K (Fin s)) {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The parser extracts the raw target word without broadening its representation
promise or assuming a semantic algebraic-number decoding oracle. -/
def inputParser : BitEncoding.TotalParser payloadEncoding :=
  totalParser.prod BitEncoding.TotalParser.rawBits

theorem inputParser_encode (p : Code × Bits) :
    inputParser.run (payloadEncoding.encode p) = (true,p) := by
  have h := inputParser.correct (payloadEncoding.encode p)
  rw [payloadEncoding.decode_encode] at h
  cases hf : (inputParser.run (payloadEncoding.encode p)).1
  · simp [hf] at h
  · have hp : (inputParser.run (payloadEncoding.encode p)).2 = p := by simpa [hf] using h.symm
    exact Prod.ext hf hp

def verifier (p : Bits × Bits) : Bool :=
  let parsed := inputParser.run p.1
  parsed.1 && verify L basis (parsed.2,p.2)

theorem fp_verifier : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool (verifier L basis) := by
  have hx := fp_fst BitEncoding.bits BitEncoding.bits
  have hw := fp_snd BitEncoding.bits BitEncoding.bits
  have hp := hx.comp inputParser.fp
  have hflag := hp.comp (fp_fst BitEncoding.bool payloadEncoding)
  have hdata := hp.comp (fp_snd BitEncoding.bool payloadEncoding)
  have hv := (hdata.pair hw).comp (fp_verify L basis)
  exact (hflag.pair hv).comp (fp_bool_gate (fun p => p.1 && p.2))

/-- One-hot blocks plus forced zero padding give one witness per assignment. -/
def witnessPolynomial (q : ℕ) : Polynomial ℕ := (Polynomial.X + 1) * Polynomial.C q

def totalCount : Bits → ℕ := certificateCount (witnessPolynomial q) (verifier L basis)

theorem totalCount_certificateSharpP : CertificateSharpP (totalCount L basis) :=
  ⟨witnessPolynomial q,verifier L basis,fp_verifier L basis,fun _ => rfl⟩

/-- The independent nondeterministic accepting-path model, via the proved actual
certificate-to-machine compiler. -/
theorem totalCount_sharpP : SharpP (totalCount L basis) :=
  (totalCount_certificateSharpP L basis).sharpP

 theorem encoded_length_bound (g : Code) (z : K) :
    g.vertices ≤ ((ComplexityCSPCountReduction.countEncoding basis).encode (g,z)).length + 1 := by
  have h := size_le_encoding_length g
  change g.vertices ≤ ((encoding.prod (numberFieldEncoding basis)).encode (g,z)).length + 1
  rw [BitEncoding.prod_length]
  dsimp only
  omega

/-- Every valid canonical COUNT input has precisely the desired accepting count,
including zero weights, negative weights and isolated variables. -/
theorem totalCount_encode [DecidableEq K] (g : Code) (hg : Valid L g) (z : K) :
    totalCount L basis ((ComplexityCSPCountReduction.countEncoding basis).encode (g,z)) =
      countAt L g z := by
  let raw := (ComplexityCSPCountReduction.countEncoding basis).encode (g,z)
  have hr : raw = payloadEncoding.encode (g,(numberFieldEncoding basis).encode z) := rfl
  have hp : inputParser.run raw = (true,(g,(numberFieldEncoding basis).encode z)) := by
    rw [hr,inputParser_encode]
  have hlen : (witnessPolynomial q).eval raw.length = (raw.length+1)*q := by
    simp [witnessPolynomial]
  unfold totalCount certificateCount
  change Fintype.card {w : Fin ((witnessPolynomial q).eval raw.length) → Bool //
    verifier L basis (raw,List.ofFn w)=true} = _
  rw [hlen]
  simpa only [verifier,hp,Bool.true_and,WeightCertificate] using
    certificate_card L basis g hg z (raw.length+1) (encoded_length_bound basis g z)

/-- #P membership on the exact existing valid raw COUNT promise. This does not
claim a decoder for arbitrary external algebraic target descriptions. -/
theorem countProblem_membership [DecidableEq K] :
    ∃ f : Bits → ℕ, SharpP f ∧ ∀ raw,
      (ComplexityCSPCountReduction.countProblem L basis).valid raw →
      (ComplexityCSPCountReduction.countProblem L basis).value raw = BitEncoding.nat.encode (f raw) := by
  refine ⟨totalCount L basis,totalCount_sharpP L basis,?_⟩
  rintro raw ⟨⟨g,z⟩,hg,rfl⟩
  rw [totalCount_encode L basis g hg z]
  exact encodedFunction_encode _ _ _ _ _

end ComplexCSP.ComplexityCSPCountSharpP

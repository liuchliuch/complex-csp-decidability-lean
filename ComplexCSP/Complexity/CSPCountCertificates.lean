import ComplexCSP.Complexity.CSPAssignmentVerifier
import ComplexCSP.Complexity.CSPCountBits
import ComplexCSP.Complexity.CSPValidation
import PlanarHom.ZeroOneCertificateBijection

/-! # Parsimonious polynomial-length assignment certificates for COUNT

Every domain assignment has exactly one padded one-hot witness. The field target
is its canonical word in one fixed rational basis. Both positive and zero/signed
weights are retained by equality of the actual product, rather than support tests.
-/
noncomputable section
namespace ComplexCSP.ComplexityCSPCountCertificates
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives PlanarHom.ZeroOneSharpPMembership
open ComplexityCSPCode ComplexityCSPAssignmentVerifier ComplexityCSPCountBits
open ComplexityCSPValidation

variable {q s : ℕ} {K : Type} [Field K] [Algebra ℚ K]
variable (L : Language (Fin q) K (Fin s)) {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The edge-free graph checker is exactly canonical one-hot blocks plus unique
zero padding; it supplies no relation or CSP acceptance oracle. -/
def assignmentGraph (g : Code) : GraphCode := ⟨g.vertices,[]⟩

theorem assignmentGraph_valid (g : Code) : (assignmentGraph g).Valid := by
  intro e he
  simp [assignmentGraph] at he

def baseCheck (g : Code) (w : Bits) : Bool :=
  verifyGraph q (fun _ _ => true) (assignmentGraph g) w

abbrev payloadEncoding : BitEncoding (Code × Bits) := encoding.prod BitEncoding.bits

def verify (p : (Code × Bits) × Bits) : Bool :=
  validTest L p.1.1 && baseCheck (q := q) p.1.1 p.2 &&
    bitsEqual ((numberFieldEncoding basis).encode (assignmentWeight L p.1.1 p.2),p.1.2)

 theorem verify_true (g : Code) (target w : Bits) :
    verify L basis ((g,target),w) = true ↔
      Valid L g ∧ baseCheck (q := q) g w = true ∧
        (numberFieldEncoding basis).encode (assignmentWeight L g w) = target := by
  simp [verify,Bool.and_eq_true,bitsEqual,validTest_correct,and_assoc]

 theorem fp_baseCheck : FP (encoding.prod BitEncoding.bits) BitEncoding.bool
    (fun p => baseCheck (q := q) p.1 p.2) := by
  have hg := fp_fst encoding BitEncoding.bits
  have hw := fp_snd encoding BitEncoding.bits
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := (hg.comp hv).comp (fp_fst BitEncoding.unaryNat constraintEncoding.list)
  have hgraph : FP (encoding.prod BitEncoding.bits) GraphCode.encoding
      (fun p => assignmentGraph p.1) :=
    (hn.pair (fp_const _ (BitEncoding.nat.prod BitEncoding.nat).list [])).transportOutput
      (fun _ => rfl)
  exact (hgraph.pair hw).comp (fp_verifyGraph q (fun _ _ => true))

/-- Actual deterministic polynomial-time verifier, including exact materialized
field products and target word equality. -/
theorem fp_verify : FP (payloadEncoding.prod BitEncoding.bits) BitEncoding.bool (verify L basis) := by
  have hp := fp_fst payloadEncoding BitEncoding.bits
  have hw := fp_snd payloadEncoding BitEncoding.bits
  have hg := hp.comp (fp_fst encoding BitEncoding.bits)
  have hz := hp.comp (fp_snd encoding BitEncoding.bits)
  have hv := hg.comp (fp_validTest L)
  have hb := (hg.pair hw).comp (fp_baseCheck (q := q))
  have hvalue := (hg.pair hw).comp (fp_assignmentWeight L basis)
  have hword := hvalue.comp (fp_code_view (numberFieldEncoding basis) BitEncoding.bits
    (numberFieldEncoding basis).encode (fun _ => rfl))
  have heq := (hword.pair hz).comp fp_bitsEqual
  exact (((hv.pair hb).comp (fp_bool_gate (fun p => p.1 && p.2))).pair heq).comp
    (fp_bool_gate (fun p => p.1 && p.2))

abbrev WeightCertificate (g : Code) (z : K) (N : ℕ) :=
  {w : Fin (N*q) → Bool // verify L basis ((g,(numberFieldEncoding basis).encode z),List.ofFn w)=true}

abbrev WeightAssignment [DecidableEq K] (g : Code) (z : K) :=
  {σ : Fin g.vertices → Fin q // eval L g σ = z}

def baseCertificate {g : Code} {z : K} {N : ℕ} (w : WeightCertificate L basis g z N) :
    Certificate q (fun _ _ => true) (assignmentGraph g) N :=
  ⟨w.val,((verify_true L basis g _ _).mp w.property).2.1⟩

def certificateAssignment {g : Code} {z : K} {N : ℕ}
    (w : WeightCertificate L basis g z N) : Fin g.vertices → Fin q :=
  certificateColor (baseCertificate L basis w)

 theorem certificateAssignment_matches {g : Code} {z : K} {N : ℕ}
    (w : WeightCertificate L basis g z N) (v : Fin g.vertices) :
    Matches q (List.ofFn w.val) v.val (certificateAssignment L basis w v) :=
  certificateColor_matches (baseCertificate L basis w) v

 theorem certificateAssignment_weight {g : Code} {z : K} {N : ℕ}
    (w : WeightCertificate L basis g z N) : eval L g (certificateAssignment L basis w) = z := by
  obtain ⟨hg,_,he⟩ := (verify_true L basis g _ _).mp w.property
  apply (numberFieldEncoding basis).injective
  rw [← assignmentWeight_eq L g hg (certificateAssignment L basis w) _
    (certificateAssignment_matches L basis w)]
  exact he

 theorem verify_padded_assignment [DecidableEq K] (g : Code) (hg : Valid L g)
    (z : K) (N : ℕ) (hN : g.vertices ≤ N) (σ : WeightAssignment L g z) :
    verify L basis ((g,(numberFieldEncoding basis).encode z),List.ofFn (paddedWord σ.val N)) = true := by
  apply (verify_true L basis g _ _).mpr
  refine ⟨hg,?_,?_⟩
  · exact verify_padded (assignmentGraph_valid g) hN
      (⟨σ.val,by intro e; exact Fin.elim0 e⟩ : Hom q (fun _ _ => true)
        (assignmentGraph g) (assignmentGraph_valid g))
  · rw [assignmentWeight_eq L g hg σ.val _ (paddedWord_matches σ.val hN),σ.property]

/-- Unique padded certificates, not one witness per incidental representation. -/
def certificateEquiv [DecidableEq K] (g : Code) (hg : Valid L g)
    (z : K) (N : ℕ) (hN : g.vertices ≤ N) :
    WeightCertificate L basis g z N ≃ WeightAssignment L g z where
  toFun w := ⟨certificateAssignment L basis w,certificateAssignment_weight L basis w⟩
  invFun σ := ⟨paddedWord σ.val N,verify_padded_assignment L basis g hg z N hN σ⟩
  left_inv w := Subtype.ext (reconstruct_certificate (baseCertificate L basis w))
  right_inv σ := by
    apply Subtype.ext
    funext v
    exact matches_unique
      (certificateAssignment_matches L basis
        ⟨paddedWord σ.val N,verify_padded_assignment L basis g hg z N hN σ⟩ v)
      (paddedWord_matches σ.val hN v)

 theorem certificate_card [DecidableEq K] (g : Code) (hg : Valid L g)
    (z : K) (N : ℕ) (hN : g.vertices ≤ N) :
    Fintype.card (WeightCertificate L basis g z N) = countAt L g z := by
  rw [Fintype.card_congr (certificateEquiv L basis g hg z N hN)]
  simp only [WeightAssignment,Fintype.card_subtype,countAt]

end ComplexCSP.ComplexityCSPCountCertificates

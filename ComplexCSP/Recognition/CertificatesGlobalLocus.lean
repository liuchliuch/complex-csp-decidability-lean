import ComplexCSP.Recognition.CertificatesLegalTables
import ComplexCSP.Recognition.GlobalConditions

/-!
# The literal singleton-purification BO locus

These theorems connect the finite certificate construction to the project's
actual singleton-purification definition on finite-arity original tables.
-/

namespace ComplexCSP.Certificates

open GeneratingSet

variable {D : Type} [Fintype D] [DecidableEq D]

/-- View actual row entries in a subfield that contains them. -/
noncomputable def rowsInField (K : Subfield ℂ) (T : PositiveTable D)
    (hT : ∀ x z, T.rows x z ∈ K) : (Fin T.rowArity → D) → D → K :=
  fun x z ↦ ⟨T.rows x z, hT x z⟩

/-- The exact singleton-purification BO predicate has the finite certificate
characterization over the fixed working number field. -/
theorem singleton_BO_iff_certificate (K : Subfield ℂ) [NumberField K]
    (T : PositiveTable D) (hT : ∀ x z, T.rows x z ∈ K) :
    BlockOrthogonality.BlockOrthogonal T.singletonRows ↔
      ∃ c : Certificate (Fin T.rowArity → D) D (NumberFieldRoots K),
        c.Retained (numberFieldRootAlphabet K) ∧
        Satisfies (numberFieldRootAlphabet K) c (rowsInField K T hT) := by
  let L := LegalGeneratingSet.choose T.nonzeroValues
  have hcontains : LegalGeneratingSet.ContainsTable T.nonzeroValues T.rows := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x, z, rfl⟩
  exact legal_purified_blockOrthogonal_iff_certificate K L (rowsInField K T hT) hcontains

/-- The actual singleton locus is the zero locus of finitely many actual product
polynomials in the unbarred original field-valued coordinates. -/
theorem singleton_BO_iff_product_equations (K : Subfield ℂ) [NumberField K] [DecidableEq K]
    (T : PositiveTable D) (hT : ∀ x z, T.rows x z ∈ K) :
    BlockOrthogonality.BlockOrthogonal T.singletonRows ↔
      ∀ q ∈ boProductEquations (X := Fin T.rowArity → D) (D := D) (numberFieldRootAlphabet K),
        MvPolynomial.eval (fun p : (Fin T.rowArity → D) × D ↦ rowsInField K T hT p.1 p.2) q = 0 := by
  let L := LegalGeneratingSet.choose T.nonzeroValues
  have hcontains : LegalGeneratingSet.ContainsTable T.nonzeroValues T.rows := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x, z, rfl⟩
  exact legal_purified_blockOrthogonal_iff_product_equations K L (rowsInField K T hT) hcontains

end ComplexCSP.Certificates

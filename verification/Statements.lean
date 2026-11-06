import ComplexCSP

open scoped BigOperators

set_option linter.unusedVariables false

/-! Frozen paper propositions. Review these bodies independently of the proofs.
Verification never regenerates this file from the production theorems. -/

namespace ComplexCSP.PaperStatements

/-- Paper F.1.1; `ComplexCSP.Recognition.encodedGlobalTest_correct`. -/
def paper_thm_main_encodedGlobalTest_correct : Prop :=
  ∀ (L : ComplexCSP.Recognition.FiniteAlgebraicLanguage) (hL : L.Valid)
    (z : (i : Fin L.signatureSize) → (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ),
    (∀ (i : Fin L.signatureSize) (a : Fin (L.tables.arity i) → Fin L.domainSize),
        (L.tables.value i a).Represents (z i a)) →
      (ComplexCSP.Recognition.encodedGlobalTest L hL = true ↔
        ComplexCSP.CaiChenConditions (ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z))

/-- Paper F.1.1; `ComplexCSP.Recognition.exists_algebraic_language_description`. -/
def paper_thm_main_exists_algebraic_language_description : Prop :=
  ∀ {D ι : Type} (L : ComplexCSP.Language D ℂ ι),
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ∃ E z,
        (∀ (i : ι) (a : Fin (E.arity i) → D), (E.value i a).Represents (z i a)) ∧
          ComplexCSP.Recognition.realizedAlgebraicLanguage E z = L

/-- Paper F.1.1, F.9.2; `ComplexCSP.structural_collapse`. -/
def paper_thm_main_structural_collapse : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι) [Nonempty D] [Fintype ι],
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      (ComplexCSP.CaiChenConditions L ↔ ComplexCSP.JointBO L)

/-- Paper F.1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_correct`. -/
def paper_cor_degree_multiple_main_encodedDegreeGlobalTest_correct : Prop :=
  ∀ (L : ComplexCSP.Recognition.FiniteAlgebraicLanguage) (hL : L.Valid) (δ : ℕ) (hδ : 0 < δ)
    (z : (i : Fin L.signatureSize) → (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ),
    (∀ (i : Fin L.signatureSize) (a : Fin (L.tables.arity i) → Fin L.domainSize),
        (L.tables.value i a).Represents (z i a)) →
      (ComplexCSP.Recognition.encodedDegreeGlobalTest L hL δ hδ = true ↔
        ComplexCSP.DegreeCaiChenConditions
          (ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z) δ)

/-- Paper F.1.2; `ComplexCSP.degree_structural_collapse`. -/
def paper_cor_degree_multiple_main_degree_structural_collapse : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι) (δ : ℕ) [Nonempty D] [Fintype ι],
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      (ComplexCSP.DegreeCaiChenConditions L δ ↔ ComplexCSP.DegreeJointBO L δ)

/-- Paper F.1.2; `ComplexCSP.degreeCaiChenConditions_one_iff`. -/
def paper_cor_degree_multiple_main_degreeCaiChenConditions_one_iff : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.DegreeCaiChenConditions L 1 ↔ ComplexCSP.CaiChenConditions L

/-- Paper F.1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeJointBO`. -/
def paper_cor_degree_multiple_main_hard_of_not_degreeJointBO : Prop :=
  ∀ {D K : Type} [inst : Fintype D] [inst_1 : Field K] [inst_2 : Algebra ℚ K] {s d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : ComplexCSP.Language D K (Fin s)) (δ : ℕ),
    0 < δ →
      ¬ComplexCSP.DegreeJointBO (M.mapValues σ) δ →
        PlanarHom.Complexity.PromisedSharpPHard
          (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem M basis δ)

/-- Paper F.1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeConditions`. -/
def paper_cor_degree_multiple_main_hard_of_not_degreeConditions : Prop :=
  ∀ {D K : Type} [inst : Fintype D] [inst_1 : Field K] [inst_2 : Algebra ℚ K] {s d : ℕ} [Nonempty D]
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : ComplexCSP.Language D K (Fin s)) (δ : ℕ),
    0 < δ →
      ¬ComplexCSP.DegreeCaiChenConditions (M.mapValues σ) δ →
        PlanarHom.Complexity.PromisedSharpPHard
          (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem M basis δ)

/-- Paper F.1.2; `ComplexCSP.ComplexityPositiveFP.degreeConditions_inFP`. -/
def paper_cor_degree_multiple_main_degreeConditions_inFP : Prop :=
  ∀ {D K : Type} [inst : Fintype D] [inst_1 : Field K] [DecidableEq K] [inst_3 : Algebra ℚ K]
    {s dimension : ℕ} [Nonempty D] (L : ComplexCSP.Language D K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ) {δ : ℕ},
    0 < δ →
      ComplexCSP.DegreeCaiChenConditions (L.mapValues σ) δ →
        (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP

/-- Paper F.1.2; `ComplexCSP.ComplexityClassification.degree_conditions`. -/
def paper_cor_degree_multiple_main_degree_conditions : Prop :=
  ∀ {D K : Type} [inst : Fintype D] [inst_1 : Field K] [DecidableEq K] [inst_3 : Algebra ℚ K]
    {s dimension : ℕ} (L : ComplexCSP.Language D K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
    (σ : K →+* ℂ) [Nonempty D] (δ : ℕ),
    0 < δ →
      (ComplexCSP.DegreeCaiChenConditions (L.mapValues σ) δ →
          (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP) ∧
        (¬ComplexCSP.DegreeCaiChenConditions (L.mapValues σ) δ →
          PlanarHom.Complexity.PromisedSharpPHard
            (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem L basis δ))

/-- Paper F.1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity`. -/
def paper_cor_degree_multiple_main_encodedDegreeGlobalTest_complexity : Prop :=
  ∀ {K : Type} [inst : Field K] [DecidableEq K] [inst_2 : Algebra ℚ K] {dimension : ℕ}
    (L : ComplexCSP.Recognition.FiniteAlgebraicLanguage) (hL : L.Valid) (δ : ℕ) (hδ : 0 < δ)
    (z : (i : Fin L.signatureSize) → (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ),
    (∀ (i : Fin L.signatureSize) (a : Fin (L.tables.arity i) → Fin L.domainSize),
        (L.tables.value i a).Represents (z i a)) →
      ∀ (M : ComplexCSP.Language (Fin L.domainSize) K (Fin L.signatureSize))
        (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ),
        M.mapValues σ = ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z →
          (ComplexCSP.Recognition.encodedDegreeGlobalTest L hL δ hδ = true →
              (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem M basis δ).InFP) ∧
            (ComplexCSP.Recognition.encodedDegreeGlobalTest L hL δ hδ = false →
              PlanarHom.Complexity.PromisedSharpPHard
                (ComplexCSP.ComplexityGadgetSubstitution.degreePartitionProblem M basis δ))

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_agreement`. -/
def paper_lem_purification_invariance_table_ambient_agreement.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} [inst : Fintype D] {S T : Finset ℂˣ}
    (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S)
    (M : ComplexCSP.GeneratingSet.LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S G)
    (hT : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable T G),
    ComplexCSP.AmbientTableAgreement (L.purifyTable G hS) (M.purifyTable G hT)

/-- Paper F.3.1; `ComplexCSP.AmbientTableAgreement.disjoint_iff`. -/
def paper_lem_purification_invariance_disjoint_iff.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} [inst : Fintype D] {P Q : X → D → ℂ},
    ComplexCSP.AmbientTableAgreement P Q →
      ∀ (x y : X),
        Disjoint (ComplexCSP.BlockOrthogonality.support (P x))
            (ComplexCSP.BlockOrthogonality.support (P y)) ↔
          Disjoint (ComplexCSP.BlockOrthogonality.support (Q x))
            (ComplexCSP.BlockOrthogonality.support (Q y))

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_normalized_ambient_agreement`. -/
def paper_lem_purification_invariance_table_normalized_ambient_agreement.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} [inst : Fintype D] {S T : Finset ℂˣ}
    (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S)
    (M : ComplexCSP.GeneratingSet.LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S G)
    (hT : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable T G) {N K : ℝ},
    0 < N →
      0 < K →
        ComplexCSP.AmbientTableAgreement (fun x z => ↑N * L.purifyTable G hS x z) fun x z =>
          ↑K * M.purifyTable G hT x z

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_blockOrthogonal_iff`. -/
def paper_lem_purification_invariance_table_ambient_blockOrthogonal_iff.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} {S T : Finset ℂˣ} [inst : Fintype D]
    (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S)
    (M : ComplexCSP.GeneratingSet.LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S G)
    (hT : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable T G),
    ComplexCSP.BlockOrthogonality.BlockOrthogonal (L.purifyTable G hS) ↔
      ComplexCSP.BlockOrthogonality.BlockOrthogonal (M.purifyTable G hT)

/-- Paper F.3.2; `ComplexCSP.jointBO_iff_singletonBO`. -/
def paper_cor_singleton_purification_jointBO_iff_singletonBO : Prop :=
  ∀ {D : Type} [inst : Fintype D] {ι : Type} (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.JointBO L ↔ ComplexCSP.SingletonBO L

/-- Paper F.3.3; `ComplexCSP.paper_generated_diagonal_minor`. -/
def paper_lem_diagonal_minors_paper_generated_diagonal_minor : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} [inst : CommSemiring K] [inst_1 : Fintype D]
    {r s : ℕ} {G : (Fin r → D) → K},
    ComplexCSP.PaperGenerated L G →
      ∀ (π : Fin r → Fin s), ComplexCSP.PaperGenerated L fun a => G (a ∘ π)

/-- Paper F.3.3, F.5.1; `ComplexCSP.generated_iff_paperGenerated`. -/
def paper_lem_diagonal_minors_generated_iff_paperGenerated : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} [inst : CommSemiring K] [inst_1 : Fintype D]
    {r : ℕ} (G : (Fin r → D) → K), ComplexCSP.Instance.Generated L G ↔ ComplexCSP.PaperGenerated L G

/-- Paper F.3.4; `ComplexCSP.singletonBO_iff_bounded`. -/
def paper_lem_bo_arity_bound_singletonBO_iff_bounded : Prop :=
  ∀ {D : Type} [inst : Fintype D] {ι : Type} (L : ComplexCSP.Language D ℂ ι) [Nonempty D],
    ComplexCSP.SingletonBO L ↔ ComplexCSP.BoundedSingletonBO L

/-- Paper F.3.4; `ComplexCSP.bounded_external_arity_counterexample`. -/
def paper_lem_bo_arity_bound_bounded_external_arity_counterexample : Prop :=
  ∀ {D : Type} [inst : Fintype D] {ι : Type} (L : ComplexCSP.Language D ℂ ι) [Nonempty D],
    ¬ComplexCSP.SingletonBO L →
      ∃ T : ComplexCSP.PositiveTable D,
        ComplexCSP.Instance.Generated L T.value ∧
          0 < T.rowArity ∧
            T.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 ∧
              ¬ComplexCSP.BlockOrthogonality.BlockOrthogonal T.singletonRows

/-- Paper F.3.5; `ComplexCSP.Certificates.value_norm_eq_iff_numberFieldRoot`. -/
def paper_lem_intrinsic_purification_tests_value_norm_eq_iff_numberFieldRoot.{u_1, u_2} : Prop :=
  ∀ {K : Type u_1} {Γ : Type u_2} [inst : Field K] [inst_1 : CommGroup Γ] [inst_2 : NumberField K]
    (φ : K →+* ℂ) (ρ : Γ →* Kˣ),
    Function.Injective ⇑ρ →
      ∀ (P : ComplexCSP.Purification.PurificationMap Γ (ComplexCSP.Certificates.complexOriginal φ ρ))
        (a b : Γ),
        ‖P.value a‖ = ‖P.value b‖ ↔
          ∃ r,
            (ComplexCSP.Certificates.fieldValueHom ρ) a =
              (ComplexCSP.Certificates.numberFieldRootAlphabet K).value r *
                (ComplexCSP.Certificates.fieldValueHom ρ) b

/-- Paper F.3.5; `ComplexCSP.Certificates.entry_norm_products_iff_twisted`. -/
def paper_lem_intrinsic_purification_tests_entry_norm_products_iff_twisted.{u_1, u_2} : Prop :=
  ∀ {K : Type u_1} {Γ : Type u_2} [inst : Field K] [inst_1 : CommGroup Γ] [inst_2 : NumberField K]
    (φ : K →+* ℂ) (ρ : Γ →* Kˣ),
    Function.Injective ⇑ρ →
      ∀ (P : ComplexCSP.Purification.PurificationMap Γ (ComplexCSP.Certificates.complexOriginal φ ρ))
        (a b c d : Option Γ),
        ‖P.entry a * P.entry b‖ = ‖P.entry c * P.entry d‖ ↔
          ∃ r,
            ComplexCSP.Certificates.fieldEntry ρ a * ComplexCSP.Certificates.fieldEntry ρ b =
              (ComplexCSP.Certificates.numberFieldRootAlphabet K).value r *
                (ComplexCSP.Certificates.fieldEntry ρ c * ComplexCSP.Certificates.fieldEntry ρ d)

/-- Paper F.3.5; `ComplexCSP.Certificates.entry_products_iff_field_products`. -/
def paper_lem_intrinsic_purification_tests_entry_products_iff_field_products.{u_1, u_2} : Prop :=
  ∀ {K : Type u_1} {Γ : Type u_2} [inst : Field K] [inst_1 : CommGroup Γ] (φ : K →+* ℂ) (ρ : Γ →* Kˣ),
    Function.Injective ⇑ρ →
      ∀ (P : ComplexCSP.Purification.PurificationMap Γ (ComplexCSP.Certificates.complexOriginal φ ρ))
        (a b c d : Option Γ),
        P.entry a * P.entry b = P.entry c * P.entry d ↔
          ComplexCSP.Certificates.fieldEntry ρ a * ComplexCSP.Certificates.fieldEntry ρ b =
            ComplexCSP.Certificates.fieldEntry ρ c * ComplexCSP.Certificates.fieldEntry ρ d

/-- Paper F.3.5; `ComplexCSP.Certificates.value_root_covariance`. -/
def paper_lem_intrinsic_purification_tests_value_root_covariance.{u_1, u_2} : Prop :=
  ∀ {K : Type u_1} {Γ : Type u_2} [inst : Field K] [inst_1 : CommGroup Γ] [inst_2 : NumberField K]
    (φ : K →+* ℂ) (ρ : Γ →* Kˣ),
    Function.Injective ⇑ρ →
      ∀ (P : ComplexCSP.Purification.PurificationMap Γ (ComplexCSP.Certificates.complexOriginal φ ρ))
        (a b : Γ) (r : ↥(ComplexCSP.Certificates.NumberFieldRoots K)),
        (ComplexCSP.Certificates.fieldValueHom ρ) a =
            (ComplexCSP.Certificates.numberFieldRootAlphabet K).value r *
              (ComplexCSP.Certificates.fieldValueHom ρ) b →
          P.value a = φ ((ComplexCSP.Certificates.numberFieldRootAlphabet K).value r) * P.value b

/-- Paper F.3.5; `ComplexCSP.Certificates.intrinsicTests_legalTable`. -/
def paper_lem_intrinsic_purification_tests_intrinsicTests_legalTable.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} (K : Subfield ℂ) [inst : NumberField ↥K] {S : Finset ℂˣ}
    (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S) (A : X → D → ↥K)
    (hA : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S fun x z => ↑(A x z)),
    ComplexCSP.Certificates.IntrinsicTests (ComplexCSP.Certificates.numberFieldRootAlphabet ↥K)
      (ComplexCSP.Certificates.numberFieldRootRealization K.subtype) A
      (L.purifyTable (fun x z => ↑(A x z)) hA)

/-- Paper F.4.2; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_finite_union`. -/
def paper_thm_finite_bo_certificates_legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] [inst_2 : Fintype D]
    [inst_3 : DecidableEq D] (K : Subfield ℂ) [inst_4 : NumberField ↥K] [inst_5 : DecidableEq ↥K]
    {S : Finset ℂˣ} (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S) (A : X → D → ↥K)
    (hA : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S fun x z => ↑(A x z)),
    ComplexCSP.BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z => ↑(A x z)) hA) ↔
      ∃ c : ComplexCSP.Certificates.RetainedCertificate (X := X) (D := D)
        (ComplexCSP.Certificates.numberFieldRootAlphabet ↥K),
        (fun p => A p.1 p.2) ∈
          ComplexCSP.polynomialZeroLocus
            (ComplexCSP.Certificates.equationSet (ComplexCSP.Certificates.numberFieldRootAlphabet ↥K)
              ↑c)

/-- Paper F.4.2; `ComplexCSP.Certificates.certificate_complete`. -/
def paper_thm_finite_bo_certificates_certificate_complete.{u_1, u_2, u_3, u_4} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} {R : Type u_3} {K : Type u_4} [inst : Fintype D]
    [inst_1 : DecidableEq D] [inst_2 : Field K] {roots : ComplexCSP.Certificates.RootAlphabet K R}
    {realize : ComplexCSP.Certificates.ComplexRealization roots} {A : X → D → K} {P : X → D → ℂ},
    ComplexCSP.BlockOrthogonality.BlockOrthogonal P →
      ComplexCSP.Certificates.IntrinsicTests roots realize A P →
        ∃ c,
          ComplexCSP.Certificates.Certificate.Retained roots c ∧
            ComplexCSP.Certificates.Satisfies roots c A

/-- Paper F.4.2; `ComplexCSP.Certificates.certificate_sound`. -/
def paper_thm_finite_bo_certificates_certificate_sound.{u_1, u_2, u_3, u_4} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} {R : Type u_3} {K : Type u_4} [inst : Fintype D]
    [inst_1 : DecidableEq D] [inst_2 : Field K] {roots : ComplexCSP.Certificates.RootAlphabet K R}
    {realize : ComplexCSP.Certificates.ComplexRealization roots}
    {c : ComplexCSP.Certificates.Certificate X D R} {A : X → D → K} {P : X → D → ℂ},
    ComplexCSP.Certificates.Satisfies roots c A →
      ComplexCSP.Certificates.IntrinsicTests roots realize A P →
        ComplexCSP.Certificates.Certificate.Retained roots c →
          ComplexCSP.BlockOrthogonality.BlockOrthogonal P

/-- Paper F.4.4; `ComplexCSP.finite_union_zeroLocus_iff`. -/
def paper_cor_bo_product_identities_finite_union_zeroLocus_iff.{u_1, u_2, u_3} : Prop :=
  ∀ {J : Type u_1} {σ : Type u_2} {K : Type u_3} [inst : Fintype J] [inst_1 : DecidableEq J]
    [inst_2 : Field K] [inst_3 : DecidableEq K] [inst_4 : DecidableEq σ]
    (E : J → Finset (MvPolynomial σ K)) (x : σ → K),
    (∃ j, x ∈ ComplexCSP.polynomialZeroLocus (E j)) ↔
      x ∈ ComplexCSP.polynomialZeroLocus (ComplexCSP.productEquations E)

/-- Paper F.4.4; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_product_equations`. -/
def paper_cor_bo_product_identities_legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2} : Prop :=
  ∀ {X : Type u_1} {D : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] [inst_2 : Fintype D]
    [inst_3 : DecidableEq D] (K : Subfield ℂ) [inst_4 : NumberField ↥K] [inst_5 : DecidableEq ↥K]
    {S : Finset ℂˣ} (L : ComplexCSP.GeneratingSet.LegalGeneratingSet S) (A : X → D → ↥K)
    (hA : ComplexCSP.GeneratingSet.LegalGeneratingSet.ContainsTable S fun x z => ↑(A x z)),
    ComplexCSP.BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z => ↑(A x z)) hA) ↔
      ∀
        q ∈
          ComplexCSP.Certificates.boProductEquations
            (ComplexCSP.Certificates.numberFieldRootAlphabet ↥K),
        (MvPolynomial.eval fun p => A p.1 p.2) q = 0

/-- Paper F.4.4; `ComplexCSP.Certificates.allProductPrograms_zero_iff`. -/
def paper_cor_bo_product_identities_allProductPrograms_zero_iff : Prop :=
  ∀ {X D R K : Type} {n : ℕ} [inst : DecidableEq D] [inst_1 : CommRing K] [IsDomain K]
    [inst_3 : Fintype X] [inst_4 : DecidableEq X] [inst_5 : Encodable X] [inst_6 : Fintype D]
    [inst_7 : Encodable D] [inst_8 : Fintype R] [inst_9 : Encodable R] [inst_10 : DecidableEq K]
    (name : X × D ≃ Fin n) (roots : ComplexCSP.Certificates.RootAlphabet K R) (A : X → D → K),
    (∀ P ∈ ComplexCSP.Certificates.allProductPrograms (⇑name) roots,
        ComplexCSP.PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2) P = 0) ↔
      ∃ c,
        ComplexCSP.Certificates.Certificate.Retained roots c ∧
          ComplexCSP.Certificates.Satisfies roots c A

/-- Paper F.4.4; `ComplexCSP.Certificates.optimizedProductPrograms_zero_iff`. -/
def paper_cor_bo_product_identities_optimizedProductPrograms_zero_iff : Prop :=
  ∀ {X D R K : Type} {n : ℕ} [inst : DecidableEq D] [inst_1 : CommRing K] [IsDomain K]
    [inst_3 : Fintype X] [inst_4 : DecidableEq X] [inst_5 : Encodable X] [inst_6 : Fintype D]
    [inst_7 : Encodable D] [inst_8 : Fintype R] [inst_9 : Encodable R] [inst_10 : DecidableEq K]
    (name : X × D ≃ Fin n) (roots : ComplexCSP.Certificates.RootAlphabet K R) (A : X → D → K),
    (∀ P ∈ ComplexCSP.Certificates.optimizedProductPrograms (⇑name) roots,
        ComplexCSP.PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2) P = 0) ↔
      ∃ c,
        ComplexCSP.Certificates.Certificate.Retained roots c ∧
          ComplexCSP.Certificates.Satisfies roots c A

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.exists_presentation`. -/
def paper_lem_pinned_realization_exists_presentation : Prop :=
  ∀ {D K ι B : Type} [inst : CommSemiring K] [inst_1 : Fintype D] {L : ComplexCSP.Language D K ι}
    (G : ↥(ComplexCSP.GeneratedTable L B)), ∃ P, ComplexCSP.GeneratedTable.ofPresentation P = G

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.ofPresentation_mul`. -/
def paper_lem_pinned_realization_ofPresentation_mul : Prop :=
  ∀ {D K ι B : Type} [inst : CommSemiring K] [inst_1 : Fintype D] {L : ComplexCSP.Language D K ι}
    (P Q : ComplexCSP.Presentation L B),
    ComplexCSP.GeneratedTable.ofPresentation (P.mul Q) =
      ComplexCSP.GeneratedTable.ofPresentation P * ComplexCSP.GeneratedTable.ofPresentation Q

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.forall_iff_presentations`. -/
def paper_lem_pinned_realization_forall_iff_presentations : Prop :=
  ∀ {D K ι B : Type} [inst : CommSemiring K] [inst_1 : Fintype D] {L : ComplexCSP.Language D K ι}
    (Q : ((B → D) → K) → Prop),
    (∀ (G : ↥(ComplexCSP.GeneratedTable L B)), Q ↑G) ↔ ∀ (P : ComplexCSP.Presentation L B), Q P.table

/-- Paper F.5.1; `ComplexCSP.Instance.partition_glue`. -/
def paper_lem_pinned_realization_partition_glue : Prop :=
  ∀ {D K ι B : Type} {L : ComplexCSP.Language D K ι} {H₁ H₂ : Type} [inst : CommSemiring K]
    [inst_1 : Fintype D] [inst_2 : Fintype H₁] [inst_3 : Fintype H₂] [inst_4 : DecidableEq H₁]
    [inst_5 : DecidableEq H₂] (I : ComplexCSP.Instance L B H₁) (J : ComplexCSP.Instance L B H₂)
    (a : B → D), (I.glue J).partition a = I.partition a * J.partition a

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.printed_theorem_5_2_counterexample`. -/
def paper_rem_simple_instance_counterexample_printed_theorem_5_2_counterexample : Prop :=
  (∀ (n : ℕ)
      (I :
        ComplexCSP.Instance
          (ComplexCSP.Theorem52Counterexample.unaryLanguage
            ComplexCSP.Theorem52Counterexample.firstProfile)
          (Fin 1) (Fin n)),
      ComplexCSP.Theorem52Counterexample.PaperSimple I →
        I.partition ComplexCSP.Theorem52Counterexample.zeroPin =
          (I.retarget fun x x_1 => ComplexCSP.Theorem52Counterexample.secondProfile (x_1 0)).partition
            ComplexCSP.Theorem52Counterexample.zeroPin) ∧
    ¬∃ e,
        (ComplexCSP.Theorem52Counterexample.unaryLanguage
              ComplexCSP.Theorem52Counterexample.firstProfile).IsTargetIso
          (fun x x_1 => ComplexCSP.Theorem52Counterexample.secondProfile (x_1 0)) e

/-- Paper F.5.2; `ComplexCSP.Instance.partition_eq_of_iso_pin_twins`. -/
def paper_thm_young_pinned_partition_eq_of_iso_pin_twins : Prop :=
  ∀ {A B K ι V H : Type} {L : ComplexCSP.Language A K ι} [inst : CommSemiring K] [inst_1 : Fintype A]
    [inst_2 : Fintype B] [inst_3 : Fintype H] [inst_4 : DecidableEq H] (I : ComplexCSP.Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (e : A ≃ B),
    L.IsTargetIso g e →
      ∀ (a : V → A) (b : V → B),
        (∀ (v : V), (L.retarget g).Twins (e (a v)) (b v)) → I.partition a = (I.retarget g).partition b

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.all_instance_pinned_iso_iff`. -/
def paper_thm_young_pinned_all_instance_pinned_iso_iff : Prop :=
  ∀ {A B K ι V : Type} [inst : Field K] [CharZero K] [inst_2 : Fintype A] [inst_3 : Fintype B]
    (L : ComplexCSP.Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K) (a : V → A) (b : V → B),
    ComplexCSP.PinnedIsomorphism.AllPinnedEqual L g a b ↔
      ∃ e, L.IsTargetIso g e ∧ ∀ (v : V), (L.retarget g).Twins (e (a v)) (b v)

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.pinnedIsoCheck_correct_all_instances`. -/
def paper_thm_young_pinned_pinnedIsoCheck_correct_all_instances : Prop :=
  ∀ {A B K ι V : Type} [inst : Field K] [CharZero K] [inst_2 : Fintype A] [inst_3 : Fintype B]
    (L : ComplexCSP.Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K) [inst_4 : DecidableEq A]
    [inst_5 : DecidableEq B] [inst_6 : DecidableEq K] [inst_7 : Fintype ι] [inst_8 : Fintype V]
    (a : V → A) (b : V → B),
    L.pinnedIsoCheck g a b = true ↔ ComplexCSP.PinnedIsomorphism.AllPinnedEqual L g a b

/-- Paper F.5.4; `ComplexCSP.Instance.partition_tensorConjugate`. -/
def paper_lem_tensor_character_partition_tensorConjugate : Prop :=
  ∀ {D K ι B H : Type} [inst : CommSemiring K] [inst_1 : StarRing K] {L : ComplexCSP.Language D K ι}
    [inst_2 : Fintype D] [inst_3 : Fintype H] [inst_4 : DecidableEq H] (I : ComplexCSP.Instance L B H)
    (p q : ℕ) (a : Fin p → B → D) (b : Fin q → B → D),
    (I.tensorConjugate p q).partition (ComplexCSP.tensorPins a b) =
      (∏ j, I.partition (a j)) * ∏ j, star (I.partition (b j))

/-- Paper F.5.4; `ComplexCSP.Instance.partition_tensorConjugate_zero`. -/
def paper_lem_tensor_character_partition_tensorConjugate_zero : Prop :=
  ∀ {D K ι B H : Type} [inst : CommSemiring K] [inst_1 : StarRing K] {L : ComplexCSP.Language D K ι}
    [inst_2 : Fintype D] [inst_3 : Fintype H] [inst_4 : DecidableEq H]
    (I : ComplexCSP.Instance L B H),
    (I.tensorConjugate 0 0).partition (ComplexCSP.tensorPins (fun j => j.elim0) fun j => j.elim0) = 1

/-- Paper F.5.4; `ComplexCSP.tensor_realizes_pinnedMonomial`. -/
def paper_lem_tensor_character_tensor_realizes_pinnedMonomial : Prop :=
  ∀ {D K ι B : Type} [inst : CommSemiring K] [inst_1 : Fintype D] [inst_2 : StarRing K]
    (L : ComplexCSP.Language D K ι) (P : ComplexCSP.Presentation L B) (p q : ℕ) (a : Fin p → B → D)
    (b : Fin q → B → D),
    (P.inst.tensorConjugate p q).partition (ComplexCSP.tensorPins a b) =
      (ComplexCSP.pinnedMonomialCharacter L a b) (ComplexCSP.GeneratedTable.ofPresentation P)

/-- Paper F.5.5; `ComplexCSP.ScalarTags.exists_common_rational_tags`. -/
def paper_lem_scalar_tags_exists_common_rational_tags.{u_1, u_3, u_4, u_5} : Prop :=
  ∀ {K : Type u_1} [inst : Field K] [CharZero K] {ι : Type u_3} [Fintype ι] {E : ℕ → Type u_4}
    {F : ℕ → Type u_5} [inst_3 : (r : ℕ) → AddCommGroup (E r)]
    [inst_4 : (r : ℕ) → _root_.Module K (E r)] [inst_5 : (r : ℕ) → AddCommGroup (F r)]
    [inst_6 : (r : ℕ) → _root_.Module K (F r)] (arity : ι → ℕ) (h : (i : ι) → E (arity i))
    (g : (i : ι) → F (arity i)),
    (∀ (i j : ι), i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0) →
      (∀ (i j : ι), i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) →
        ∃ tag : ι → ℚ,
          (∀ (i : ι), 0 < tag i) ∧
            (Function.Injective (fun i => (⟨arity i, (tag i : K) • h i⟩ : (r : ℕ) × E r))) ∧
              Function.Injective (fun i => (⟨arity i, (tag i : K) • g i⟩ : (r : ℕ) × F r))

/-- Paper F.5.5; `ComplexCSP.ScalarTags.findRationalTags_spec`. -/
def paper_lem_scalar_tags_findRationalTags_spec.{u_1, u_3, u_4} : Prop :=
  ∀ {K : Type u_1} [inst : Field K] [inst_1 : CharZero K] {n : ℕ} {E : ℕ → Type u_3}
    {F : ℕ → Type u_4} [inst_2 : (r : ℕ) → AddCommGroup (E r)]
    [inst_3 : (r : ℕ) → _root_.Module K (E r)] [inst_4 : (r : ℕ) → AddCommGroup (F r)]
    [inst_5 : (r : ℕ) → _root_.Module K (F r)] [inst_6 : (r : ℕ) → DecidableEq (E r)]
    [inst_7 : (r : ℕ) → DecidableEq (F r)] (arity : Fin n → ℕ) (h : (i : Fin n) → E (arity i))
    (g : (i : Fin n) → F (arity i))
    (hh : ∀ (i j : Fin n), i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ (i j : Fin n), i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0),
    have tag := ComplexCSP.ScalarTags.findRationalTags (K := K) arity h g hh hg;
    (∀ (i : Fin n), 0 < tag i) ∧
      (Function.Injective (fun i => (⟨arity i, (tag i : K) • h i⟩ : (r : ℕ) × E r))) ∧
        Function.Injective (fun i => (⟨arity i, (tag i : K) • g i⟩ : (r : ℕ) × F r))

/-- Paper F.5.5; `ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged_correct`. -/
def paper_lem_scalar_tags_comparePaperTagged_correct : Prop :=
  ∀ {D K V : Type} {k : ℕ} [inst : Field K] [inst_1 : StarRing K] [inst_2 : CharZero K]
    [inst_3 : Fintype D] [inst_4 : DecidableEq D] [inst_5 : Fintype V] [inst_6 : DecidableEq K]
    (L : ComplexCSP.Language D K (Fin k)) (M N : ComplexCSP.Recognition.PinnedMonomial V D)
    (hM :
      ∀ (i j : Fin k),
        i ≠ j → L.arity i = L.arity j → (M.target L).value i ≠ 0 ∨ (M.target L).value j ≠ 0)
    (hN :
      ∀ (i j : Fin k),
        i ≠ j → L.arity i = L.arity j → (N.target L).value i ≠ 0 ∨ (N.target L).value j ≠ 0),
    ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged L M N hM hN = true ↔
      M.character L = N.character L

/-- Paper F.5.6; `ComplexCSP.Recognition.PinnedMonomial.characters_eq_iff_all_tensor_instances`. -/
def paper_lem_character_comparison_characters_eq_iff_all_tensor_instances : Prop :=
  ∀ {D K ι V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : Fintype D]
    (M N : ComplexCSP.Recognition.PinnedMonomial V D) (L : ComplexCSP.Language D K ι),
    M.character L = N.character L ↔
      ComplexCSP.PinnedIsomorphism.AllPinnedEqual (M.target L) (N.target L).value M.pin N.pin

/-- Paper F.5.6; `ComplexCSP.Recognition.PinnedMonomial.compare_correct`. -/
def paper_lem_character_comparison_compare_correct : Prop :=
  ∀ {D K ι V : Type} [inst : Field K] [inst_1 : StarRing K] [CharZero K] [inst_3 : Fintype D]
    [inst_4 : DecidableEq D] [inst_5 : Fintype ι] [inst_6 : Fintype V] [inst_7 : DecidableEq K]
    (L : ComplexCSP.Language D K ι) (M N : ComplexCSP.Recognition.PinnedMonomial V D),
    ComplexCSP.Recognition.PinnedMonomial.compare L M N = true ↔ M.character L = N.character L

/-- Paper F.5.6; `ComplexCSP.Recognition.partition_common_tags_iff`. -/
def paper_lem_character_comparison_partition_common_tags_iff : Prop :=
  ∀ {A B K ι V H : Type} [inst : Field K] (L : ComplexCSP.Language A K ι) [inst_1 : Fintype A]
    [inst_2 : Fintype B] [inst_3 : Fintype H] [inst_4 : DecidableEq H]
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (scalars : ι → K),
    (∀ (i : ι), scalars i ≠ 0) →
      ∀ (I : ComplexCSP.Instance L V H) (a : V → A) (b : V → B),
        (I.retarget (ComplexCSP.Recognition.scaleSymbols L scalars).value).partition a =
            (I.retarget (ComplexCSP.Recognition.scaleSymbols (L.retarget g) scalars).value).partition
              b ↔
          I.partition a = (I.retarget g).partition b

/-- Paper F.5.7; `ComplexCSP.characters_linearIndependent`. -/
def paper_lem_dedekind_independence_characters_linearIndependent.{u_1, u_2, u_3} : Prop :=
  ∀ {M : Type u_1} {K : Type u_2} {ι : Type u_3} [inst : Monoid M] [inst_1 : Field K]
    (χ : ι → M →* K), Function.Injective χ → LinearIndependent K fun i => ⇑(χ i)

/-- Paper F.5.7; `ComplexCSP.character_coefficients_eq_zero`. -/
def paper_lem_dedekind_independence_character_coefficients_eq_zero.{u_1, u_2, u_3} : Prop :=
  ∀ {M : Type u_1} {K : Type u_2} {ι : Type u_3} [inst : Monoid M] [inst_1 : Field K]
    (χ : ι → M →* K),
    Function.Injective χ →
      ∀ (s : Finset ι) (c : ι → K), (∀ (x : M), ∑ i ∈ s, c i * (χ i) x = 0) → ∀ i ∈ s, c i = 0

/-- Paper F.5.7; `ComplexCSP.grouped_character_zero_iff`. -/
def paper_lem_dedekind_independence_grouped_character_zero_iff.{u_1, u_2, u_3} : Prop :=
  ∀ {M : Type u_1} {K : Type u_2} {ι : Type u_3} [inst : Monoid M] [inst_1 : Field K]
    [inst_2 : DecidableEq (M →* K)] (s : Finset ι) (χ : ι → M →* K) (c : ι → K),
    (∀ (x : M), ∑ i ∈ s, c i * (χ i) x = 0) ↔
      ∀ ψ ∈ ComplexCSP.characterClasses s χ, ComplexCSP.characterClassCoefficient s χ c ψ = 0

/-- Paper F.5.8; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_correct`. -/
def paper_thm_universal_identity_uniformAlgebraicIdentityTest_correct : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : DecidableEq D] [inst_2 : Encodable D]
    [inst_3 : Fintype ι] [inst_4 : Encodable ι] {n k : ℕ}
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L)
    (P : ComplexCSP.PolynomialPrograms.Program ComplexCSP.AlgebraicEncoding.AlgebraicInput n)
    (hP : ∀ (j : Fin (List.length P)), (List.get P j).coefficient.Valid)
    (coords : Fin n → ComplexCSP.PinnedCoordinate (Fin k) D)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      ∀ (coefficients : Fin (List.length P) → ℂ),
        (∀ (j : Fin (List.length P)), (List.get P j).coefficient.Represents (coefficients j)) →
          (ComplexCSP.Recognition.uniformAlgebraicIdentityTest L hL P hP coords = true ↔
            ∀ (h : ℕ)
              (I :
                ComplexCSP.Instance (ComplexCSP.Recognition.realizedAlgebraicLanguage L z) (Fin k)
                  (Fin h)),
              ComplexCSP.PolynomialPrograms.eval
                  (fun j => Sum.elim I.partition (fun a => star (I.partition a)) (coords j))
                  (ComplexCSP.Recognition.programWithCoefficients P coefficients) =
                0)

/-- Paper F.5.8; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_rejects_iff`. -/
def paper_thm_universal_identity_uniformAlgebraicIdentityTest_rejects_iff : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : DecidableEq D] [inst_2 : Encodable D]
    [inst_3 : Fintype ι] [inst_4 : Encodable ι] {n k : ℕ}
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L)
    (P : ComplexCSP.PolynomialPrograms.Program ComplexCSP.AlgebraicEncoding.AlgebraicInput n)
    (hP : ∀ (j : Fin (List.length P)), (List.get P j).coefficient.Valid)
    (coords : Fin n → ComplexCSP.PinnedCoordinate (Fin k) D)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      ∀ (coefficients : Fin (List.length P) → ℂ),
        (∀ (j : Fin (List.length P)), (List.get P j).coefficient.Represents (coefficients j)) →
          (ComplexCSP.Recognition.uniformAlgebraicIdentityTest L hL P hP coords = false ↔
            ∃ h : ℕ, ∃ I : ComplexCSP.Instance (ComplexCSP.Recognition.realizedAlgebraicLanguage L z) (Fin k) (Fin h),
              ComplexCSP.PolynomialPrograms.eval
                  (fun j => Sum.elim I.partition (fun a => star (I.partition a)) (coords j))
                  (ComplexCSP.Recognition.programWithCoefficients P coefficients) ≠
                0)

/-- Paper F.5.8; `ComplexCSP.Recognition.programIdentityTest_mvPolynomial_correct`. -/
def paper_thm_universal_identity_programIdentityTest_mvPolynomial_correct : Prop :=
  ∀ {D K ι V : Type} {n : ℕ} [inst : Field K] [inst_1 : StarRing K] [CharZero K] [inst_3 : Fintype D]
    [inst_4 : DecidableEq D] [inst_5 : Fintype ι] [inst_6 : Fintype V] [inst_7 : DecidableEq K]
    (L : ComplexCSP.Language D K ι) (coords : Fin n → ComplexCSP.PinnedCoordinate V D)
    (P : ComplexCSP.PolynomialPrograms.Program K n),
    ComplexCSP.Recognition.programIdentityTest L coords P = true ↔
      ∀ (Q : ComplexCSP.Presentation L V),
        (MvPolynomial.eval fun j => Sum.elim Q.table (fun a => star (Q.table a)) (coords j))
            (ComplexCSP.PolynomialPrograms.denote P) =
          0

/-- Paper F.10.1; `ComplexCSP.Instance.degree_filter_identity`. -/
def paper_lem_degree_filtered_character_comparison_degree_filter_identity : Prop :=
  ∀ {D K ι B H : Type} [inst : Field K] {L : ComplexCSP.Language D K ι} [inst_1 : Fintype B]
    [inst_2 : Fintype H] [inst_3 : DecidableEq B] [inst_4 : DecidableEq H] [inst_5 : Fintype D]
    (I : ComplexCSP.Instance L B H) {δ : ℕ} {ζ : K},
    IsPrimitiveRoot ζ δ →
      ∀ (a : B → D),
        (∑ s : B → Fin δ, (I.degreeAugment δ ζ).partition fun v => (a v, s v)) =
          if ∀ (v : B ⊕ H), δ ∣ I.occurrenceDegree v then
            ↑δ ^ (Fintype.card B + Fintype.card H) * I.partition a
          else 0

/-- Paper F.10.1; `ComplexCSP.Recognition.PinnedMonomial.filtered_sum_formula`. -/
def paper_lem_degree_filtered_character_comparison_filtered_sum_formula : Prop :=
  ∀ {D K ι V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : Fintype D] [inst_3 : Fintype V]
    [inst_4 : DecidableEq V] {H : Type} [inst_5 : Fintype H] [inst_6 : DecidableEq H]
    (M : ComplexCSP.Recognition.PinnedMonomial V D) (L : ComplexCSP.Language D K ι) {δ : ℕ} {ζ : K},
    IsPrimitiveRoot ζ δ →
      ∀ (I : ComplexCSP.Instance L V H),
        ∑ s : V → Fin δ, (I.retarget (M.filteredTarget L δ ζ).value).partition (M.filteredPin s) =
          if ComplexCSP.Instance.DegreeDivisible δ I then
            ↑δ ^ (Fintype.card V + Fintype.card H) * (M.character L) ⟨I.partition, ComplexCSP.Instance.generated_partition I⟩
          else 0

/-- Paper F.10.1; `ComplexCSP.Recognition.PinnedMonomial.degreeCompare_correct`. -/
def paper_lem_degree_filtered_character_comparison_degreeCompare_correct : Prop :=
  ∀ {D K ι V : Type} [inst : Field K] [inst_1 : StarRing K] [CharZero K] [inst_3 : Fintype D]
    [inst_4 : DecidableEq D] [inst_5 : Fintype ι] [inst_6 : Fintype V] [inst_7 : DecidableEq V]
    [inst_8 : DecidableEq K] (L : ComplexCSP.Language D K ι) {δ : ℕ} {ζ : K},
    0 < δ →
      IsPrimitiveRoot ζ δ →
        ∀ (M N : ComplexCSP.Recognition.PinnedMonomial V D),
          ComplexCSP.Recognition.PinnedMonomial.degreeCompare L δ ζ M N = true ↔
            M.degreeCharacter L δ = N.degreeCharacter L δ

/-- Paper F.10.2; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_correct`. -/
def paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_correct : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : DecidableEq D] [inst_2 : Encodable D]
    [inst_3 : Fintype ι] [inst_4 : Encodable ι] {n k : ℕ}
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L)
    (P : ComplexCSP.PolynomialPrograms.Program ComplexCSP.AlgebraicEncoding.AlgebraicInput n)
    (hP : ∀ (j : Fin (List.length P)), (List.get P j).coefficient.Valid) (δ : ℕ) (hδ : 0 < δ)
    (coords : Fin n → ComplexCSP.PinnedCoordinate (Fin k) D)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      ∀ (coefficients : Fin (List.length P) → ℂ),
        (∀ (j : Fin (List.length P)), (List.get P j).coefficient.Represents (coefficients j)) →
          (ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest L hL P hP δ hδ coords = true ↔
            ∀ (h : ℕ)
              (I :
                ComplexCSP.Instance (ComplexCSP.Recognition.realizedAlgebraicLanguage L z) (Fin k)
                  (Fin h)),
              ComplexCSP.Instance.DegreeDivisible δ I →
                ComplexCSP.PolynomialPrograms.eval
                    (fun j => Sum.elim I.partition (fun a => star (I.partition a)) (coords j))
                    (ComplexCSP.Recognition.programWithCoefficients P coefficients) =
                  0)

/-- Paper F.10.2; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_rejects_iff`. -/
def paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_rejects_iff : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : DecidableEq D] [inst_2 : Encodable D]
    [inst_3 : Fintype ι] [inst_4 : Encodable ι] {n k : ℕ}
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L)
    (P : ComplexCSP.PolynomialPrograms.Program ComplexCSP.AlgebraicEncoding.AlgebraicInput n)
    (hP : ∀ (j : Fin (List.length P)), (List.get P j).coefficient.Valid) (δ : ℕ) (hδ : 0 < δ)
    (coords : Fin n → ComplexCSP.PinnedCoordinate (Fin k) D)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      ∀ (coefficients : Fin (List.length P) → ℂ),
        (∀ (j : Fin (List.length P)), (List.get P j).coefficient.Represents (coefficients j)) →
          (ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest L hL P hP δ hδ coords = false ↔
            ∃ h : ℕ, ∃ I : ComplexCSP.Instance (ComplexCSP.Recognition.realizedAlgebraicLanguage L z) (Fin k) (Fin h),
              ComplexCSP.Instance.DegreeDivisible δ I ∧
                ComplexCSP.PolynomialPrograms.eval
                    (fun j => Sum.elim I.partition (fun a => star (I.partition a)) (coords j))
                    (ComplexCSP.Recognition.programWithCoefficients P coefficients) ≠
                  0)

/-- Paper F.6.2; `ComplexCSP.Recognition.globalCertificateTest_exponent_correct_jointBO`. -/
def paper_thm_global_bo_decidable_globalCertificateTest_exponent_correct_jointBO : Prop :=
  ∀ {D K ι : Type} [inst : Field K] [NumberField K] [inst_2 : Fintype D] [inst_3 : DecidableEq D]
    [Nonempty D] [inst_5 : Encodable D] [inst_6 : Fintype ι] [inst_7 : StarRing K]
    [inst_8 : DecidableEq K] (E : ℕ) [inst_9 : Fintype ↥(rootsOfUnity E K)]
    [inst_10 : Encodable ↥(rootsOfUnity E K)],
    0 < E →
      ComplexCSP.RowDetector.KillsTorsion K E →
        ∀ (L : ComplexCSP.Language D K ι) (σ : K →+* ℂ),
          ComplexCSP.Recognition.globalCertificateTest L
                (ComplexCSP.Certificates.exponentRootAlphabet K E) =
              true ↔
            ComplexCSP.JointBO (L.mapValues σ)

/-- Paper F.6.2; `ComplexCSP.Recognition.uniformAlgebraicGlobalTest_correct_jointBO`. -/
def paper_thm_global_bo_decidable_uniformAlgebraicGlobalTest_correct_jointBO : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : DecidableEq D] [inst_2 : Encodable D]
    [inst_3 : Fintype ι] [inst_4 : Encodable ι] [Nonempty D]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      (ComplexCSP.Recognition.uniformAlgebraicGlobalTest L hL = true ↔
        ComplexCSP.JointBO (ComplexCSP.Recognition.realizedAlgebraicLanguage L z))

/-- Paper F.7.1; `ComplexCSP.infinite_simultaneous_multiset_powerSum_ne_zero`. -/
def paper_lem_simultaneous_power_sums_infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2} : Prop :=
  ∀ {ι : Type u_1} {K : Type u_2} [Fintype ι] [DecidableEq ι] [inst : CommRing K] [IsDomain K]
    [CharZero K] (A : ι → Multiset K),
    (∀ (i : ι), A i ≠ 0) →
      (∀ (i : ι), ∀ x ∈ A i, x ≠ 0) →
        {n | 0 < n ∧ ∀ (i : ι), (Multiset.map (fun x => x ^ n) (A i)).sum ≠ 0}.Infinite

/-- Paper F.7.1; `ComplexCSP.exists_simultaneous_powerSum_ne_zero_bounded`. -/
def paper_lem_simultaneous_power_sums_exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3} : Prop :=
  ∀ {ι : Type u_1} {K : Type u_2} [inst : Fintype ι] [DecidableEq ι] {κ : ι → Type u_3}
    [inst_2 : (i : ι) → Fintype (κ i)] [∀ (i : ι), Nonempty (κ i)] [inst_4 : CommRing K] [IsDomain K]
    [CharZero K] (a : (i : ι) → κ i → K),
    (∀ (i : ι) (j : κ i), a i j ≠ 0) →
      ∃ n, 0 < n ∧ n ≤ ∏ i, Fintype.card (κ i) ∧ ∀ (i : ι), ComplexCSP.powerSum (a i) n ≠ 0

/-- Paper F.7.1; `ComplexCSP.findSimultaneousPower_success`. -/
def paper_lem_simultaneous_power_sums_findSimultaneousPower_success.{u_1, u_2, u_3} : Prop :=
  ∀ {ι : Type u_1} {K : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι] {κ : ι → Type u_3}
    [inst_2 : (i : ι) → Fintype (κ i)] [∀ (i : ι), Nonempty (κ i)] [inst_4 : CommRing K] [IsDomain K]
    [CharZero K] [inst_7 : DecidableEq K] (a : (i : ι) → κ i → K),
    (∀ (i : ι) (j : κ i), a i j ≠ 0) → (ComplexCSP.findSimultaneousPower a).isSome = true

/-- Paper F.7.1; `ComplexCSP.findSimultaneousPower_sound`. -/
def paper_lem_simultaneous_power_sums_findSimultaneousPower_sound.{u_1, u_2, u_3} : Prop :=
  ∀ {ι : Type u_1} {K : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι] {κ : ι → Type u_3}
    [inst_2 : (i : ι) → Fintype (κ i)] [inst_3 : CommRing K] [inst_4 : DecidableEq K]
    (a : (i : ι) → κ i → K) {n : ℕ},
    ComplexCSP.findSimultaneousPower a = some n →
      0 < n ∧ n ≤ ∏ i, Fintype.card (κ i) ∧ ∀ (i : ι), ComplexCSP.powerSum (a i) n ≠ 0

/-- Paper F.7.2; `ComplexCSP.paper_generated_equalityfree_pp_support`. -/
def paper_lem_equality_free_support_realization_paper_generated_equalityfree_pp_support : Prop :=
  ∀ {D K ι A : Type} [inst : Fintype D] [Fintype A] [inst_2 : CommRing K] [IsDomain K] [CharZero K]
    {L : ComplexCSP.Language D K ι} {r h : ℕ} (arity : A → ℕ) (G : (i : A) → (Fin (arity i) → D) → K),
    (∀ (i : A), ComplexCSP.PaperGenerated L (G i)) →
      ∀ (scope : (i : A) → Fin (arity i) → Fin r ⊕ Fin h),
        ∃ F,
          ComplexCSP.PaperGenerated L F ∧
            ∀ (a : Fin r → D), F a ≠ 0 ↔ ∃ b, ∀ (i : A), G i (Sum.elim a b ∘ scope i) ≠ 0

/-- Paper F.7.2; `ComplexCSP.PresentedAtom.compile_correct`. -/
def paper_lem_equality_free_support_realization_compile_correct : Prop :=
  ∀ {D K ι B : Type} {L : ComplexCSP.Language D K ι} [inst : Fintype D] [inst_1 : Fintype B]
    [inst_2 : DecidableEq B] [inst_3 : CommRing K] [inst_4 : IsDomain K] [inst_5 : CharZero K]
    [inst_6 : DecidableEq K] {h : ℕ} (atoms : List (ComplexCSP.PresentedAtom L (B ⊕ Fin h)))
    (a : B → D),
    (ComplexCSP.PresentedAtom.compile atoms).table a ≠ 0 ↔
      ∃ b, ∀ atom ∈ atoms, atom.presentation.table (Sum.elim a b ∘ atom.scope) ≠ 0

/-- Paper F.7.2; `ComplexCSP.findSupportPower_spec`. -/
def paper_lem_equality_free_support_realization_findSupportPower_spec : Prop :=
  ∀ {R W K : Type} [inst : Fintype R] [inst_1 : Fintype W] [inst_2 : CommRing K] [inst_3 : IsDomain K]
    [inst_4 : CharZero K] [inst_5 : DecidableEq K] (F : R → W → K),
    0 < ComplexCSP.findSupportPower F ∧
      ∀ (r : R), ∑ w, F r w ^ ComplexCSP.findSupportPower F ≠ 0 ↔ ∃ w, F r w ≠ 0

/-- Paper F.7.3, F.7.4, F.8.2; `ComplexCSP.JointBO.original`. -/
def paper_cor_generated_singleton_rectangularity_original : Prop :=
  ∀ {D : Type} [inst : Fintype D] {ι : Type} (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.JointBO L → ComplexCSP.AllGeneratedOriginalBO L

/-- Paper F.7.3, F.7.4; `ComplexCSP.allGeneratedOriginalBO_supportRectangular`. -/
def paper_cor_generated_singleton_rectangularity_allGeneratedOriginalBO_supportRectangular : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] {L : ComplexCSP.Language D ℂ ι},
    ComplexCSP.AllGeneratedOriginalBO L → ComplexCSP.AllGeneratedSupportRectangular L

/-- Paper F.7.3, F.7.4; `ComplexCSP.generated_supports_equalityfree_rectangularity`. -/
def paper_cor_generated_singleton_rectangularity_generated_supports_equalityfree_rectangularity : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} [inst : Fintype D] [inst_1 : CommRing K]
    [IsDomain K] [CharZero K],
    ComplexCSP.AllGeneratedSupportRectangular L →
      ComplexCSP.MaltsevRelations.EqualityFreeSingletonRectangularity (ComplexCSP.generatedSupports L)

/-- Paper F.7.3; `ComplexCSP.MaltsevRelations.rectangular_iff_equal_or_disjoint`. -/
def paper_cor_generated_singleton_rectangularity_rectangular_iff_equal_or_disjoint.{u, v} : Prop :=
  ∀ {X : Type u} {Y : Type v} (R : X → Y → Prop),
    ComplexCSP.MaltsevRelations.Rectangular R ↔
      ∀ (x y : X), {a | R x a} = {a | R y a} ∨ Disjoint {a | R x a} {a | R y a}

/-- Paper F.7.4; `ComplexCSP.MaltsevRelations.finite_family_maltsev`. -/
def paper_lem_finite_support_maltsev_finite_family_maltsev.{u} : Prop :=
  ∀ {D : Type u} [Fintype D] {Γ : Set (ComplexCSP.MaltsevRelations.Relation D)},
    ComplexCSP.MaltsevRelations.EqualityFreeSingletonRectangularity Γ →
      ∀ (Δ : Finset (ComplexCSP.MaltsevRelations.Relation D)),
        (↑Δ : Set (ComplexCSP.MaltsevRelations.Relation D)) ⊆ Γ →
          ∃ m,
            ComplexCSP.MaltsevRelations.IsMaltsev m ∧
              ComplexCSP.MaltsevRelations.CommonPolymorphism ((↑Δ : Set (ComplexCSP.MaltsevRelations.Relation D))) m

/-- Paper F.7.5; `ComplexCSP.JointBO.common_support_maltsev`. -/
def paper_thm_common_support_maltsev_common_support_maltsev : Prop :=
  ∀ {D : Type} [inst : Fintype D] {ι : Type} (L : ComplexCSP.Language D ℂ ι) [Nonempty D],
    ComplexCSP.JointBO L →
      ∃ m,
        ComplexCSP.MaltsevRelations.IsMaltsev m ∧
          ComplexCSP.MaltsevRelations.CommonPolymorphism (ComplexCSP.generatedSupports L) m

/-- Paper F.7.5; `ComplexCSP.MaltsevRelations.common_maltsev_of_finite_subfamilies`. -/
def paper_thm_common_support_maltsev_common_maltsev_of_finite_subfamilies.{u} : Prop :=
  ∀ {D : Type u} [Fintype D] (Γ : Set (ComplexCSP.MaltsevRelations.Relation D)),
    (∀ (s : Finset (ComplexCSP.MaltsevRelations.Relation D)),
        (↑s : Set (ComplexCSP.MaltsevRelations.Relation D)) ⊆ Γ →
          ∃ m,
            ComplexCSP.MaltsevRelations.IsMaltsev m ∧
              ComplexCSP.MaltsevRelations.CommonPolymorphism ((↑s : Set (ComplexCSP.MaltsevRelations.Relation D))) m) →
      ∃ m,
        ComplexCSP.MaltsevRelations.IsMaltsev m ∧ ComplexCSP.MaltsevRelations.CommonPolymorphism Γ m

/-- Paper F.7.5; `ComplexCSP.common_maltsev_of_generated_support_rectangularity`. -/
def paper_thm_common_support_maltsev_common_maltsev_of_generated_support_rectangularity : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} [inst : Fintype D] [Nonempty D]
    [inst_2 : CommRing K] [IsDomain K] [CharZero K],
    ComplexCSP.AllGeneratedSupportRectangular L →
      ∃ m,
        ComplexCSP.MaltsevRelations.IsMaltsev m ∧
          ComplexCSP.MaltsevRelations.CommonPolymorphism (ComplexCSP.generatedSupports L) m

/-- Paper F.8.1; `ComplexCSP.paper_generated_pow`. -/
def paper_lem_generated_entrywise_powers_paper_generated_pow : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} [inst : CommSemiring K] [inst_1 : Fintype D]
    {r : ℕ} {G : (Fin r → D) → K},
    ComplexCSP.PaperGenerated L G → ∀ (n : ℕ), ComplexCSP.PaperGenerated L fun a => G a ^ n

/-- Paper F.8.1; `ComplexCSP.Presentation.table_power`. -/
def paper_lem_generated_entrywise_powers_table_power : Prop :=
  ∀ {D K ι B : Type} {L : ComplexCSP.Language D K ι} [inst : CommSemiring K] [inst_1 : Fintype D]
    (P : ComplexCSP.Presentation L B) (n : ℕ) (a : B → D), (P.power n).table a = P.table a ^ n

/-- Paper F.8.2; `ComplexCSP.BlockOrthogonality.finite_row_phases_of_power_BO`. -/
def paper_lem_finite_row_phases_finite_row_phases_of_power_BO.{u, v} : Prop :=
  ∀ {X : Type u} {D : Type v} [inst : Fintype D] (G : X → D → ℂ),
    (∀ (h : ℕ),
        0 < h →
          h ≤ Fintype.card D → ComplexCSP.BlockOrthogonality.BlockOrthogonal fun x z => G x z ^ h) →
      ∀ (x y : X) (z₀ : D),
        G x z₀ ≠ 0 →
          G y z₀ ≠ 0 →
            ComplexCSP.BlockOrthogonality.support (G x) =
                ComplexCSP.BlockOrthogonality.support (G y) ∧
              ComplexCSP.RowPhases.anchorScalar (G x) (G y) z₀ ≠ 0 ∧
                ComplexCSP.RowPhases.anchoredPhase (G x) (G y) z₀ z₀ = 1 ∧
                  ∀ (z : D),
                    G x z ≠ 0 →
                      G y z =
                          ComplexCSP.RowPhases.anchorScalar (G x) (G y) z₀ *
                              ComplexCSP.RowPhases.anchoredPhase (G x) (G y) z₀ z *
                            G x z ∧
                        IsOfFinOrder (ComplexCSP.RowPhases.anchoredPhase (G x) (G y) z₀ z) ∧
                          ComplexCSP.RowPhases.anchoredPhase (G x) (G y) z₀ z ^
                              ComplexCSP.RowPhases.phaseExponent (Fintype.card D) =
                            1

/-- Paper F.8.2; `ComplexCSP.Instance.generated_pow`. -/
def paper_lem_finite_row_phases_generated_pow : Prop :=
  ∀ {D K ι B : Type} {L : ComplexCSP.Language D K ι} [inst : CommSemiring K] [inst_1 : Fintype D]
    {G : (B → D) → K},
    ComplexCSP.Instance.Generated L G → ∀ (n : ℕ), ComplexCSP.Instance.Generated L fun a => G a ^ n

/-- Paper F.8.2; `ComplexCSP.Instance.generated_mem_workingField`. -/
def paper_lem_finite_row_phases_generated_mem_workingField : Prop :=
  ∀ {D ι B : Type} {L : ComplexCSP.Language D ℂ ι} [inst : Fintype D] {G : (B → D) → ℂ},
    ComplexCSP.Instance.Generated L G → ∀ (a : B → D), G a ∈ L.workingField

/-- Paper F.8.3; `ComplexCSP.lemma_8_3`. -/
def paper_lem_nondegenerate_exponential_sums_lemma_8_3 : Prop :=
  ∀ {s : ℕ},
    0 < s →
      ∀ (a b : Fin s → ℂ),
        (∀ (i : Fin s), IsAlgebraic ℚ (a i)) →
          (∀ (i : Fin s), IsAlgebraic ℚ (b i)) →
            (∀ (i : Fin s), a i ≠ 0) →
              (∀ (i : Fin s), b i ≠ 0) →
                (∀ (i j : Fin s), i ≠ j → ¬IsOfFinOrder (b i / b j)) →
                  {t | ∑ i, a i * b i ^ t = 0}.Finite

/-- Paper F.8.3; `ComplexCSP.finite_weightedPowerSum_zeros_algebraic`. -/
def paper_lem_nondegenerate_exponential_sums_finite_weightedPowerSum_zeros_algebraic : Prop :=
  ∀ {n : ℕ} (a b : Fin n → ℂ),
    (∀ (i : Fin n), IsAlgebraic ℚ (a i)) →
      (∀ (i : Fin n), IsAlgebraic ℚ (b i)) →
        (∃ i, a i ≠ 0) →
          (∀ (i : Fin n), b i ≠ 0) →
            (∀ (i j : Fin n), i ≠ j → ¬IsOfFinOrder (b i / b j)) →
              {k | ComplexCSP.weightedPowerSum a b k = 0}.Finite

/-- Paper F.8.4; `ComplexCSP.RowEquivalenceRealization.generated_row_equivalence_detector`. -/
def paper_thm_omega_support_realization_generated_row_equivalence_detector : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [Fintype ι] (L : ComplexCSP.Language D ℂ ι),
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L →
        ∀ {n : ℕ},
          0 < n →
            ∀ (G : (Fin (n + 1) → D) → ℂ),
              ComplexCSP.Instance.Generated L G →
                ∃ E t,
                  2 ≤ E ∧
                    ComplexCSP.Instance.Generated L
                        (ComplexCSP.rowDetector G
                          ((E - 1) * (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t))
                          (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t)) ∧
                      ∀ (a : Fin (n + n) → D),
                        ComplexCSP.rowDetector G
                              ((E - 1) *
                                (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t))
                              (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t) a ≠
                            0 ↔
                          a ∈ (ComplexCSP.RowTypes.omegaRelation G).tuples

/-- Paper F.8.4; `ComplexCSP.RowEquivalenceRealization.exists_detector_support`. -/
def paper_thm_omega_support_realization_exists_detector_support.{u, v} : Prop :=
  ∀ {X : Type u} {D : Type v} [Fintype X] [inst : Fintype D] (G : X → D → ℂ)
    (P :
      ComplexCSP.Purification.PurificationMap
        (↥(ComplexCSP.Purification.PurificationMap.entryGroup G))
        (ComplexCSP.Purification.PurificationMap.entryGroup G).subtype),
    ComplexCSP.BlockOrthogonality.BlockOrthogonal
        (ComplexCSP.Purification.PurificationMap.purifyTable G P) →
      (∀ (h : ℕ),
          0 < h →
            h ≤ Fintype.card D → ComplexCSP.BlockOrthogonality.BlockOrthogonal fun x z => G x z ^ h) →
        ∀ (K : Subfield ℂ) [inst_1 : NumberField ↥K],
          (∀ (x : X) (z : D), G x z ∈ K) →
            ∃ t,
              ∀ (x y : X),
                ComplexCSP.RowDetector.detector (G x) (G y) (ComplexCSP.RowDetector.fieldExponent ↥K)
                      (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t) ≠
                    0 ↔
                  ComplexCSP.RowTypes.NonzeroProportionalRows G x y

/-- Paper F.8.4; `ComplexCSP.paper_generated_rowDetector`. -/
def paper_thm_omega_support_realization_paper_generated_rowDetector : Prop :=
  ∀ {D K ι : Type} {L : ComplexCSP.Language D K ι} {n : ℕ} [inst : CommSemiring K]
    [inst_1 : Fintype D] {G : (Fin (n + 1) → D) → K},
    ComplexCSP.PaperGenerated L G →
      ∀ (p q : ℕ), ComplexCSP.PaperGenerated L (ComplexCSP.rowDetector G p q)

/-- Paper F.8.4; `ComplexCSP.RowDetector.findDetectorTime_success`. -/
def paper_thm_omega_support_realization_findDetectorTime_success.{u_1, u_2, u_3} : Prop :=
  ∀ {ι : Type u_1} {K : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι] {κ : ι → Type u_3}
    [inst_2 : (i : ι) → Fintype (κ i)] [∀ (i : ι), Nonempty (κ i)] [inst_4 : Field K] [CharZero K]
    [inst_6 : DecidableEq K] (u : (i : ι) → κ i → K),
    (∀ (i : ι) (j : κ i), u i j ≠ 0) →
      ∀ (E L : ℕ),
        0 < E →
          0 < L →
            ComplexCSP.RowDetector.KillsTorsion K E →
              (ComplexCSP.RowDetector.findDetectorTime u E L).isSome = true

/-- Paper F.8.4; `ComplexCSP.RowDetector.fieldExponent_killsTorsion`. -/
def paper_thm_omega_support_realization_fieldExponent_killsTorsion.{u_1} : Prop :=
  ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
    ComplexCSP.RowDetector.KillsTorsion K (ComplexCSP.RowDetector.fieldExponent K)

/-- Paper F.8.4; `ComplexCSP.RowDetectorEmbeddedExistence.generated_detector_exact_workingField`. -/
def paper_thm_omega_support_realization_generated_detector_exact_workingField : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Fintype ι] (L : ComplexCSP.Language D ℂ ι)
    (hAlg : ∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)),
    ComplexCSP.JointBO L →
      ∀ {n : ℕ},
        0 < n →
          ∀ (G : (Fin (n + 1) → D) → ℂ),
            ComplexCSP.Instance.Generated L G →
              letI := L.workingField_numberField hAlg
              ∃ t : ℕ,
                ComplexCSP.Instance.Generated L
                    (ComplexCSP.rowDetector G
                      ((ComplexCSP.RowDetector.fieldExponent ↥L.workingField - 1) *
                        (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t))
                      (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t)) ∧
                  ∀ (a : Fin (n + n) → D),
                    ComplexCSP.rowDetector G
                          ((ComplexCSP.RowDetector.fieldExponent ↥L.workingField - 1) *
                            (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t))
                          (1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * t) a ≠
                        0 ↔
                      a ∈ (ComplexCSP.RowTypes.omegaRelation G).tuples

/-- Paper F.8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_support`. -/
def paper_thm_omega_support_realization_validatedRowDetector_support : Prop :=
  ∀ {d : ℕ} (coefficients : Fin d → ℤ) {D ι : Type} [inst : Fintype D] [inst_1 : Fintype ι] {n : ℕ}
    (hvalid : ComplexCSP.EncodedNumberField.validTail coefficients = true)
    (L :
      ComplexCSP.Language D
        (ComplexCSP.EncodedNumberField.Element d
          (ComplexCSP.EffectiveRoots.coefficientRelation coefficients))
        ι)
    (P : ComplexCSP.Presentation L (Fin (n + 1))) (hn : 0 < n)
  ,
    letI : Fact (ComplexCSP.EncodedNumberField.Element.Valid d
        (ComplexCSP.EffectiveRoots.coefficientRelation coefficients)) :=
      ⟨ComplexCSP.EncodedNumberField.validTail_sound coefficients hvalid⟩
    ∀ (hBO : ComplexCSP.Presentation.HasComplexBO L)
    (σ :
      ComplexCSP.EncodedNumberField.Element d
          (ComplexCSP.EffectiveRoots.coefficientRelation coefficients) →+*
        ℂ)
    (a : Fin (n + n) → D),
    (ComplexCSP.EncodedNumberField.validatedRowDetector coefficients hvalid L P hn
                hBO).presentation.table
          a ≠
        0 ↔
      a ∈ (ComplexCSP.RowTypes.omegaRelation fun b => σ (P.table b)).tuples

/-- Paper F.8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_exact_formula`. -/
def paper_thm_omega_support_realization_validatedRowDetector_exact_formula : Prop :=
  ∀ {d : ℕ} (coefficients : Fin d → ℤ) {D ι : Type} [inst : Fintype D] [inst_1 : Fintype ι] {n : ℕ}
    (hvalid : ComplexCSP.EncodedNumberField.validTail coefficients = true)
    (L :
      ComplexCSP.Language D
        (ComplexCSP.EncodedNumberField.Element d
          (ComplexCSP.EffectiveRoots.coefficientRelation coefficients))
        ι)
    (P : ComplexCSP.Presentation L (Fin (n + 1))) (hn : 0 < n)
  ,
    letI : Fact (ComplexCSP.EncodedNumberField.Element.Valid d
        (ComplexCSP.EffectiveRoots.coefficientRelation coefficients)) :=
      ⟨ComplexCSP.EncodedNumberField.validTail_sound coefficients hvalid⟩
    ∀ (hBO : ComplexCSP.Presentation.HasComplexBO L),
    have output := ComplexCSP.EncodedNumberField.validatedRowDetector coefficients hvalid L P hn hBO;
    output.exponent = 1 + ComplexCSP.RowPhases.phaseExponent (Fintype.card D) * output.time ∧
      output.presentation.table =
        ComplexCSP.rowDetector P.table
          ((ComplexCSP.RowDetector.fieldExponent
                (ComplexCSP.EncodedNumberField.Element d
                  (ComplexCSP.EffectiveRoots.coefficientRelation coefficients)) -
              1) *
            output.exponent)
          output.exponent

/-- Paper F.8.4; `ComplexCSP.EffectiveRoots.torsion_exponent_eq_order`. -/
def paper_thm_omega_support_realization_torsion_exponent_eq_order.{u_1} : Prop :=
  ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K],
    Monoid.exponent ↥(NumberField.Units.torsion K) = NumberField.Units.torsionOrder K

/-- Paper F.8.4; `ComplexCSP.EffectiveRoots.checkedRootExponent_eq_fieldExponent`. -/
def paper_thm_omega_support_realization_checkedRootExponent_eq_fieldExponent : Prop :=
  ∀ {n : ℕ} (a : Fin n → ℤ)
    [inst :
      Fact
        (ComplexCSP.EncodedNumberField.Element.Valid n
          (ComplexCSP.EffectiveRoots.coefficientRelation a))],
    ComplexCSP.MonicIrreducibility.irreducibleMonicTail a = true →
      ComplexCSP.EffectiveRoots.rootExponentFromCoefficients n a =
        ComplexCSP.RowDetector.fieldExponent
          (ComplexCSP.EncodedNumberField.Element n (ComplexCSP.EffectiveRoots.coefficientRelation a))

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_support`. -/
def paper_thm_omega_support_realization_uniformAlgebraicRowDetector_support : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Encodable D] [inst_2 : Fintype ι] [inst_3 : Encodable ι]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) {n : ℕ}
    (P : ComplexCSP.Presentation L (Fin (n + 1))) (hn : 0 < n) (hBO : ComplexCSP.HasAlgebraicBO L)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    (∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)) →
      ∀ (a : Fin (n + n) → D),
        ((ComplexCSP.uniformAlgebraicRowDetector L hL P hn hBO).presentation.reweight z).table a ≠ 0 ↔
          a ∈ (ComplexCSP.RowTypes.omegaRelation (P.reweight z).table).tuples

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_exponent`. -/
def paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exponent : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Encodable D] [inst_2 : Fintype ι] [inst_3 : Encodable ι]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) {n : ℕ}
    (P : ComplexCSP.Presentation L (Fin (n + 1))) (hn : 0 < n) (hBO : ComplexCSP.HasAlgebraicBO L),
    (ComplexCSP.uniformAlgebraicRowDetector L hL P hn hBO).exponent =
      1 +
        ComplexCSP.RowPhases.phaseExponent (Fintype.card D) *
          (ComplexCSP.uniformAlgebraicRowDetector L hL P hn hBO).time

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_exact_formula`. -/
def paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exact_formula : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Encodable D] [inst_2 : Fintype ι] [inst_3 : Encodable ι]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) {n : ℕ}
    (P : ComplexCSP.Presentation L (Fin (n + 1))) (hn : 0 < n) (hBO : ComplexCSP.HasAlgebraicBO L)
    (z : (i : ι) → (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)),
    letI := (ComplexCSP.Recognition.realizedAlgebraicLanguage L z).workingField_numberField
      (fun i a => (hz i a).isAlgebraic)
    have output := ComplexCSP.uniformAlgebraicRowDetector L hL P hn hBO;
    (output.presentation.reweight z).table =
      ComplexCSP.rowDetector (P.reweight z).table
        ((ComplexCSP.RowDetector.fieldExponent
              ↥(ComplexCSP.Recognition.realizedAlgebraicLanguage L z).workingField -
            1) *
          output.exponent)
        output.exponent

/-- Paper F.8.4; `ComplexCSP.Recognition.identityPairedCandidate_fieldRange`. -/
def paper_thm_omega_support_realization_identityPairedCandidate_fieldRange : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Encodable D] [inst_2 : Fintype ι] [inst_3 : Encodable ι]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) (z : (i : ι) → (Fin (L.arity i) → D) → ℂ),
    let input := ComplexCSP.Recognition.algebraicDescriptions L;
    let hinput := ComplexCSP.Recognition.algebraicDescriptions_valid L hL;
    let C := ComplexCSP.Recognition.identityPairedCandidate input hinput;
    letI : Fact (ComplexCSP.EncodedNumberField.Element.Valid C.degree
        (ComplexCSP.EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨ComplexCSP.EncodedNumberField.validTail_sound C.tail
        (ComplexCSP.Recognition.identityPairedCandidate_valid input hinput)⟩
    ∀ (σ : C.FieldType →+* ℂ),
      (∀
          (i :
            Fin
              (Fintype.card (ComplexCSP.Recognition.AlgebraicEntryIndex L) +
                Fintype.card (ComplexCSP.Recognition.AlgebraicEntryIndex L))),
          σ (C.coordinateValue i) =
            ComplexCSP.AlgebraicEncoding.pairedInputs (ComplexCSP.Recognition.languageEntryValues L z)
              i) →
        σ.fieldRange = (ComplexCSP.Recognition.realizedAlgebraicLanguage L z).workingField.toSubfield

/-- Paper F.8.4; `ComplexCSP.Recognition.identityPairedCandidate_rootExponent_eq`. -/
def paper_thm_omega_support_realization_identityPairedCandidate_rootExponent_eq : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [inst_1 : Encodable D] [inst_2 : Fintype ι] [inst_3 : Encodable ι]
    (L : ComplexCSP.Language D ComplexCSP.AlgebraicEncoding.AlgebraicInput ι)
    (hL : ComplexCSP.Recognition.ValidAlgebraicLanguage L) (z : (i : ι) → (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ (i : ι) (a : Fin (L.arity i) → D), (L.value i a).Represents (z i a)),
    let input := ComplexCSP.Recognition.algebraicDescriptions L;
    let hinput := ComplexCSP.Recognition.algebraicDescriptions_valid L hL;
    have C := ComplexCSP.Recognition.identityPairedCandidate input hinput;
    letI := (ComplexCSP.Recognition.realizedAlgebraicLanguage L z).workingField_numberField
      (fun i a => (hz i a).isAlgebraic)
    ComplexCSP.EffectiveRoots.rootExponentFromCoefficients C.degree C.tail =
      ComplexCSP.RowDetector.fieldExponent
        ↥(ComplexCSP.Recognition.realizedAlgebraicLanguage L z).workingField

/-- Paper F.8.5; `ComplexCSP.RowEquivalenceRealization.omega_mem_generatedSupports`. -/
def paper_cor_omega_reduces_to_supports_omega_mem_generatedSupports : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [Fintype ι] (L : ComplexCSP.Language D ℂ ι),
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L →
        ∀ {n : ℕ},
          0 < n →
            ∀ (G : (Fin (n + 1) → D) → ℂ),
              ComplexCSP.Instance.Generated L G →
                ComplexCSP.RowTypes.omegaRelation G ∈ ComplexCSP.generatedSupports L

/-- Paper F.9.1; `ComplexCSP.RowTypes.complex_type_partition`. -/
def paper_lem_omega_implies_type_complex_type_partition.{u} : Prop :=
  ∀ {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ) {m : ComplexCSP.MaltsevRelations.Operation D},
    ComplexCSP.MaltsevRelations.IsMaltsev m →
      ComplexCSP.MaltsevRelations.Preserves m (ComplexCSP.RowTypes.omegaRelation G).tuples →
        ∀ {ℓ : ℕ} (hℓ : ℓ ≤ n) (α β : Fin ℓ → D),
          ComplexCSP.RowTypes.prefixType G hℓ α = ComplexCSP.RowTypes.prefixType G hℓ β ∨
            Disjoint (ComplexCSP.RowTypes.prefixType G hℓ α) (ComplexCSP.RowTypes.prefixType G hℓ β)

/-- Paper F.9.1; `ComplexCSP.RowTypes.rowEquivalence_iff`. -/
def paper_lem_omega_implies_type_rowEquivalence_iff.{u, v, w, u_1} : Prop :=
  ∀ {𝕜 : Type u} [inst : Field 𝕜] {D : Type v} {I : Type w} {J : Type u_1} (G : (I → D) → J → 𝕜)
    (x y : I → D),
    ComplexCSP.MaltsevRelations.RowEquivalence (ComplexCSP.RowTypes.rowClasses G) x y ↔
      ComplexCSP.RowTypes.NonzeroProportionalRows G x y

/-- Paper F.9.1; `ComplexCSP.RowTypes.preserves_omega_pairs`. -/
def paper_lem_omega_implies_type_preserves_omega_pairs.{u} : Prop :=
  ∀ {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ) {m : ComplexCSP.MaltsevRelations.Operation D},
    ComplexCSP.MaltsevRelations.Preserves m (ComplexCSP.RowTypes.omegaRelation G).tuples →
      ∀ (x₁ x₂ y₁ y₂ z₁ z₂ : Fin n → D),
        ComplexCSP.RowTypes.Omega G x₁ x₂ →
          ComplexCSP.RowTypes.Omega G y₁ y₂ →
            ComplexCSP.RowTypes.Omega G z₁ z₂ →
              ComplexCSP.RowTypes.Omega G (ComplexCSP.MaltsevRelations.map₃ m x₁ y₁ z₁)
                (ComplexCSP.MaltsevRelations.map₃ m x₂ y₂ z₂)

/-- Paper F.9.2; `ComplexCSP.JointBO.global_type_partition`. -/
def paper_thm_structural_collapse_global_type_partition : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι) [Nonempty D] [Fintype ι],
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L → ComplexCSP.GlobalTypePartition L

/-- Paper F.9.2; `ComplexCSP.JointBO.global_maltsev`. -/
def paper_thm_structural_collapse_global_maltsev : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι) [Nonempty D] [Fintype ι],
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L → ComplexCSP.GlobalMaltsev L

/-- Paper F.9.2; `ComplexCSP.RowEquivalenceRealization.common_support_and_row_maltsev`. -/
def paper_thm_structural_collapse_common_support_and_row_maltsev : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [Nonempty D] [Fintype ι] (L : ComplexCSP.Language D ℂ ι),
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L →
        ∃ m,
          ComplexCSP.MaltsevRelations.IsMaltsev m ∧
            ComplexCSP.MaltsevRelations.CommonPolymorphism (ComplexCSP.generatedSupports L) m ∧
              ∀ (n : ℕ),
                0 < n →
                  ∀ (G : (Fin (n + 1) → D) → ℂ),
                    ComplexCSP.Instance.Generated L G →
                      ComplexCSP.MaltsevRelations.Preserves m
                        (ComplexCSP.RowTypes.omegaRelation G).tuples

/-- Paper F.B.1; `ComplexCSP.PaperBridge.theorem_5_2_complex_counterexample`. -/
def paper_rem_simple_instance_counterexample_theorem_5_2_complex_counterexample : Prop :=
  (∀ (n : ℕ)
      (I :
        ComplexCSP.Instance
          (ComplexCSP.Theorem52Counterexample.unaryLanguage fun i =>
            (ComplexCSP.Theorem52Counterexample.firstProfile i : ℂ))
          (Fin 1) (Fin n)),
      ComplexCSP.Theorem52Counterexample.PaperSimple I →
        I.partition ComplexCSP.Theorem52Counterexample.zeroPin =
          (I.retarget fun x x_1 =>
                (ComplexCSP.Theorem52Counterexample.secondProfile (x_1 0) : ℂ)).partition
            ComplexCSP.Theorem52Counterexample.zeroPin) ∧
    ¬∃ e : Fin 3 ≃ Fin 3,
        (ComplexCSP.Theorem52Counterexample.unaryLanguage fun i =>
              (ComplexCSP.Theorem52Counterexample.firstProfile i : ℂ)).IsTargetIso
          (fun x x_1 => (ComplexCSP.Theorem52Counterexample.secondProfile (x_1 0) : ℂ)) e

/-- Paper F.1.1, F.1.2; `ComplexCSP.PaperBridge.workingField_realization`. -/
def paper_thm_main_workingField_realization : Prop :=
  ∀ {D : Type} [Fintype D] {s : ℕ} (L : ComplexCSP.Language D ℂ (Fin s)),
    (∀ (i : Fin s) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ∃ n : ℕ, ∃ _basis : _root_.Module.Basis (Fin n) ℚ L.workingField, L.workingFieldLanguage.mapValues L.workingField.subtype = L

/-- Paper F.7.3; `ComplexCSP.PaperBridge.lemma_7_3_pp_rectangularity`. -/
def paper_cor_generated_singleton_rectangularity_lemma_7_3_pp_rectangularity : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.JointBO L →
      ComplexCSP.MaltsevRelations.EqualityFreeSingletonRectangularity (ComplexCSP.generatedSupports L)

/-- Paper F.7.4; `ComplexCSP.PaperBridge.lemma_7_4`. -/
def paper_lem_finite_support_maltsev_lemma_7_4 : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.JointBO L →
      ∀ (Δ : Finset (ComplexCSP.MaltsevRelations.Relation D)),
        (↑Δ : Set (ComplexCSP.MaltsevRelations.Relation D)) ⊆ ComplexCSP.generatedSupports L →
          ∃ m,
            ComplexCSP.MaltsevRelations.IsMaltsev m ∧
              ComplexCSP.MaltsevRelations.CommonPolymorphism ((↑Δ : Set (ComplexCSP.MaltsevRelations.Relation D))) m

/-- Paper F.8.2; `ComplexCSP.PaperBridge.lemma_8_2`. -/
def paper_lem_finite_row_phases_lemma_8_2 : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] (L : ComplexCSP.Language D ℂ ι),
    ComplexCSP.JointBO L →
      ∀ {n : ℕ} (G : (Fin (n + 1) → D) → ℂ),
        ComplexCSP.Instance.Generated L G →
          ∀ (x y : Fin n → D) (z₀ : D),
            ComplexCSP.RowTypes.tableRows G x z₀ ≠ 0 →
              ComplexCSP.RowTypes.tableRows G y z₀ ≠ 0 →
                ComplexCSP.BlockOrthogonality.support (ComplexCSP.RowTypes.tableRows G x) =
                    ComplexCSP.BlockOrthogonality.support (ComplexCSP.RowTypes.tableRows G y) ∧
                  ComplexCSP.RowPhases.anchorScalar (ComplexCSP.RowTypes.tableRows G x)
                        (ComplexCSP.RowTypes.tableRows G y) z₀ ≠
                      0 ∧
                    ComplexCSP.RowPhases.anchorScalar (ComplexCSP.RowTypes.tableRows G x)
                          (ComplexCSP.RowTypes.tableRows G y) z₀ ∈
                        L.workingField ∧
                      ComplexCSP.RowPhases.anchoredPhase (ComplexCSP.RowTypes.tableRows G x)
                            (ComplexCSP.RowTypes.tableRows G y) z₀ z₀ =
                          1 ∧
                        ∀ (z : D),
                          ComplexCSP.RowTypes.tableRows G x z ≠ 0 →
                            ComplexCSP.RowTypes.tableRows G y z =
                                ComplexCSP.RowPhases.anchorScalar (ComplexCSP.RowTypes.tableRows G x)
                                      (ComplexCSP.RowTypes.tableRows G y) z₀ *
                                    ComplexCSP.RowPhases.anchoredPhase
                                      (ComplexCSP.RowTypes.tableRows G x)
                                      (ComplexCSP.RowTypes.tableRows G y) z₀ z *
                                  ComplexCSP.RowTypes.tableRows G x z ∧
                              ComplexCSP.RowPhases.anchoredPhase (ComplexCSP.RowTypes.tableRows G x)
                                    (ComplexCSP.RowTypes.tableRows G y) z₀ z ∈
                                  L.workingField ∧
                                IsOfFinOrder
                                    (ComplexCSP.RowPhases.anchoredPhase
                                      (ComplexCSP.RowTypes.tableRows G x)
                                      (ComplexCSP.RowTypes.tableRows G y) z₀ z) ∧
                                  ComplexCSP.RowPhases.anchoredPhase
                                        (ComplexCSP.RowTypes.tableRows G x)
                                        (ComplexCSP.RowTypes.tableRows G y) z₀ z ^
                                      ComplexCSP.RowPhases.phaseExponent (Fintype.card D) =
                                    1

/-- Paper F.8.5; `ComplexCSP.PaperBridge.lemma_8_5`. -/
def paper_cor_omega_reduces_to_supports_lemma_8_5 : Prop :=
  ∀ {D ι : Type} [inst : Fintype D] [Fintype ι] (L : ComplexCSP.Language D ℂ ι),
    (∀ (i : ι) (a : Fin (L.arity i) → D), IsAlgebraic ℚ (L.value i a)) →
      ComplexCSP.JointBO L →
        ∀ (m : ComplexCSP.MaltsevRelations.Operation D),
          (∀ (r : ℕ),
              0 < r →
                ∀ (F : (Fin r → D) → ℂ),
                  ComplexCSP.Instance.Generated L F →
                    ComplexCSP.MaltsevRelations.Preserves m {a | F a ≠ 0}) →
            ∀ {n : ℕ},
              0 < n →
                ∀ (G : (Fin (n + 1) → D) → ℂ),
                  ComplexCSP.Instance.Generated L G →
                    ComplexCSP.MaltsevRelations.Preserves m
                      (ComplexCSP.RowTypes.omegaRelation G).tuples

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_norm_iff`. -/
def paper_lem_intrinsic_purification_tests_normalization_norm_iff : Prop :=
  ∀ (c a b : ℂ), c ≠ 0 → (‖c * a‖ = ‖c * b‖ ↔ ‖a‖ = ‖b‖)

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_products_iff`. -/
def paper_lem_intrinsic_purification_tests_normalization_products_iff : Prop :=
  ∀ (c a b u v : ℂ), c ≠ 0 → (c * a * (c * b) = c * u * (c * v) ↔ a * b = u * v)

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_norm_products_iff`. -/
def paper_lem_intrinsic_purification_tests_normalization_norm_products_iff : Prop :=
  ∀ (c a b u v : ℂ), c ≠ 0 → (‖c * a * (c * b)‖ = ‖c * u * (c * v)‖ ↔ ‖a * b‖ = ‖u * v‖)

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_covariance_iff`. -/
def paper_lem_intrinsic_purification_tests_normalization_covariance_iff : Prop :=
  ∀ (c a b ρ : ℂ), c ≠ 0 → (c * a = ρ * (c * b) ↔ a = ρ * b)

/-- Paper F.1.1; `ComplexCSP.ComplexityClassification.ordinary_conditions`. -/
def paper_thm_main_ordinary_conditions : Prop :=
  ∀ {D K : Type} [inst : Fintype D] [inst_1 : Field K] [DecidableEq K] [inst_3 : Algebra ℚ K]
    {s dimension : ℕ} (L : ComplexCSP.Language D K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
    (σ : K →+* ℂ) [Nonempty D],
    (ComplexCSP.CaiChenConditions (L.mapValues σ) →
        (ComplexCSP.ComplexityCSPCountReduction.partitionProblem L basis).InFP) ∧
      (¬ComplexCSP.CaiChenConditions (L.mapValues σ) →
        PlanarHom.Complexity.PromisedSharpPHard
          (ComplexCSP.ComplexityCSPCountReduction.partitionProblem L basis))

/-- Paper F.1.1; `ComplexCSP.Recognition.encodedGlobalTest_complexity`. -/
def paper_thm_main_encodedGlobalTest_complexity : Prop :=
  ∀ {K : Type} [inst : Field K] [DecidableEq K] [inst_2 : Algebra ℚ K] {dimension : ℕ}
    (L : ComplexCSP.Recognition.FiniteAlgebraicLanguage) (hL : L.Valid)
    (z : (i : Fin L.signatureSize) → (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ),
    (∀ (i : Fin L.signatureSize) (a : Fin (L.tables.arity i) → Fin L.domainSize),
        (L.tables.value i a).Represents (z i a)) →
      ∀ (M : ComplexCSP.Language (Fin L.domainSize) K (Fin L.signatureSize))
        (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ),
        M.mapValues σ = ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z →
          (ComplexCSP.Recognition.encodedGlobalTest L hL = true →
              (ComplexCSP.ComplexityCSPCountReduction.partitionProblem M basis).InFP) ∧
            (ComplexCSP.Recognition.encodedGlobalTest L hL = false →
              PlanarHom.Complexity.PromisedSharpPHard
                (ComplexCSP.ComplexityCSPCountReduction.partitionProblem M basis))

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.all_instance_completeness`. -/
def paper_thm_young_pinned_all_instance_completeness : Prop :=
  ∀ {A B K ι V : Type} [inst : Field K] [CharZero K] [inst_2 : Fintype A] [inst_3 : Fintype B]
    (L : ComplexCSP.Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K) (a : V → A) (b : V → B),
    ComplexCSP.PinnedIsomorphism.AllPinnedEqual L g a b →
      ∃ e, L.IsTargetIso g e ∧ ∀ (v : V), (L.retarget g).Twins (e (a v)) (b v)

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.doubledUnary_first_value`. -/
def paper_rem_simple_instance_counterexample_doubledUnary_first_value : Prop :=
  ComplexCSP.Theorem52Counterexample.doubledUnary.partition
      ComplexCSP.Theorem52Counterexample.zeroPin =
    41

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.doubledUnary_second_value`. -/
def paper_rem_simple_instance_counterexample_doubledUnary_second_value : Prop :=
  (ComplexCSP.Theorem52Counterexample.doubledUnary.retarget fun x x_1 =>
          ComplexCSP.Theorem52Counterexample.secondProfile (x_1 0)).partition
      ComplexCSP.Theorem52Counterexample.zeroPin =
    35

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.paperSimple_iff_simple`. -/
def paper_rem_simple_instance_counterexample_paperSimple_iff_simple : Prop :=
  ∀ {D K V H : Type} {f : D → K}
    (I : ComplexCSP.Instance (ComplexCSP.Theorem52Counterexample.unaryLanguage f) V H),
    ComplexCSP.Theorem52Counterexample.PaperSimple I ↔ ComplexCSP.Theorem52Counterexample.Simple I

/-- Paper F.1.1; `ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode`. -/
def paper_thm_main_finiteAlgebraicLanguage_decode_encode : Prop :=
  ∀ (L : ComplexCSP.Recognition.FiniteAlgebraicLanguage),
    Encodable.decode (Encodable.encode L) = some L

/-! The newly explicit STOC contracts are written independently here. -/
open ComplexCSP.GeneratingSet ComplexCSP.GeneratingSet.LegalGeneratingSet

/-- Lemma F.3.1: extensions to the entire multiplicative group. -/
def paper_lem_purification_invariance_group_extensions : Prop :=
  ∀ {S : Finset ℂˣ} (L : LegalGeneratingSet S),
    (∀ a : S, L.exponentHom ⟨a.val, Subgroup.subset_closure a.property⟩ =
      Multiplicative.ofAdd (L.exponents a)) ∧
    (∀ x : EntryGroup S, L.exponentHom x = 1 ↔ IsOfFinOrder x) ∧
    (∀ x : EntryGroup S, IsOfFinOrder (L.phaseHom x)) ∧
    (∀ x : EntryGroup S, IsOfFinOrder x → L.phaseHom x = x.val) ∧
    (∀ x : EntryGroup S, L.purifiedHom x = L.phaseHom x *
      complexPrimeProduct L.rank (L.exponentHom x)) ∧
    Function.Injective L.purifiedHom ∧
    (∀ x : EntryGroup S, ‖(L.purifiedHom x : ℂ)‖ = 1 ↔ IsOfFinOrder x)

/-- Lemma F.3.1: singleton phases are roots of unity in the containing field. -/
def paper_lem_purification_invariance_singleton_phase_in_field : Prop :=
  ∀ {S : Finset ℂˣ} (L : LegalGeneratingSet S) (K : Subfield ℂ),
    (∀ a ∈ S, (a : ℂ) ∈ K) → ∀ x : EntryGroup S,
      (L.phaseHom x : ℂ) ∈ K ∧ IsOfFinOrder (L.phaseHom x)

/-- Lemma F.5.6: finite comparison for arbitrary indexed families on the
original templates, including repeated constraints and repeated scopes. -/
def paper_lem_character_comparison_indexed_family_comparison : Prop :=
  ∀ {D A B K ι V : Type} [Field K] [CharZero K]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [DecidableEq K] [Fintype ι] [Fintype V]
    (L : ComplexCSP.Language D K ι)
    (h : (i : ι) → (Fin (L.arity i) → A) → K)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (a : V → A) (b : V → B),
    (L.retarget h).pinnedIsoCheck g a b = true ↔
      ∀ (H : Type) [Fintype H] [DecidableEq H] (I : ComplexCSP.Instance L V H),
        (I.retarget h).partition a = (I.retarget g).partition b

open ComplexCSP.Theorem52Counterexample

/-- Remark F.B.1, including positivity, twins, all simple instances, and the
non-simple distinguishing instance. The profiles are fixed numerical data. -/
def paper_rem_simple_instance_counterexample_complete : Prop :=
  (∀ i, 0 < firstProfile i) ∧
  (∀ i, 0 < secondProfile i) ∧
  (∀ a b, (unaryLanguage firstProfile).Twins a b → a = b) ∧
  (∀ a b, (unaryLanguage secondProfile).Twins a b → a = b) ∧
  (∑ i, firstProfile i) = 9 ∧
  (∑ i, secondProfile i) = 9 ∧
  (∀ (H : Type) [Fintype H] [DecidableEq H]
    (I : ComplexCSP.Instance (unaryLanguage firstProfile) (Fin 1) H),
    PaperSimple I → I.partition zeroPin =
      (I.retarget (fun _ x => secondProfile (x 0))).partition zeroPin) ∧
  (¬ ∃ e : Fin 3 ≃ Fin 3,
    (unaryLanguage firstProfile).IsTargetIso (fun _ x => secondProfile (x 0)) e) ∧
  ¬ PaperSimple doubledUnary ∧
  doubledUnary.partition zeroPin = 41 ∧
  (doubledUnary.retarget (fun _ x => secondProfile (x 0))).partition zeroPin = 35

end ComplexCSP.PaperStatements

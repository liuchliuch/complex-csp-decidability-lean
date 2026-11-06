import verification.Statements

/-! Proofs of the fixed paper specification. -/

namespace ComplexCSP.PaperSpec

/-- Paper F.1.1; `ComplexCSP.Recognition.encodedGlobalTest_correct`. -/
theorem paper_thm_main_encodedGlobalTest_correct : ComplexCSP.PaperStatements.paper_thm_main_encodedGlobalTest_correct :=
  @ComplexCSP.Recognition.encodedGlobalTest_correct

/-- Paper F.1.1; `ComplexCSP.Recognition.exists_algebraic_language_description`. -/
theorem paper_thm_main_exists_algebraic_language_description : ComplexCSP.PaperStatements.paper_thm_main_exists_algebraic_language_description :=
  @ComplexCSP.Recognition.exists_algebraic_language_description

/-- Paper F.1.1, F.9.2; `ComplexCSP.structural_collapse`. -/
theorem paper_thm_main_structural_collapse : ComplexCSP.PaperStatements.paper_thm_main_structural_collapse :=
  @ComplexCSP.structural_collapse

/-- Paper F.1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_correct`. -/
theorem paper_cor_degree_multiple_main_encodedDegreeGlobalTest_correct : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_encodedDegreeGlobalTest_correct :=
  @ComplexCSP.Recognition.encodedDegreeGlobalTest_correct

/-- Paper F.1.2; `ComplexCSP.degree_structural_collapse`. -/
theorem paper_cor_degree_multiple_main_degree_structural_collapse : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_degree_structural_collapse :=
  @ComplexCSP.degree_structural_collapse

/-- Paper F.1.2; `ComplexCSP.degreeCaiChenConditions_one_iff`. -/
theorem paper_cor_degree_multiple_main_degreeCaiChenConditions_one_iff : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_degreeCaiChenConditions_one_iff :=
  @ComplexCSP.degreeCaiChenConditions_one_iff

/-- Paper F.1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeJointBO`. -/
theorem paper_cor_degree_multiple_main_hard_of_not_degreeJointBO : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_hard_of_not_degreeJointBO :=
  @ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeJointBO

/-- Paper F.1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeConditions`. -/
theorem paper_cor_degree_multiple_main_hard_of_not_degreeConditions : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_hard_of_not_degreeConditions :=
  @ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeConditions

/-- Paper F.1.2; `ComplexCSP.ComplexityPositiveFP.degreeConditions_inFP`. -/
theorem paper_cor_degree_multiple_main_degreeConditions_inFP : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_degreeConditions_inFP :=
  @ComplexCSP.ComplexityPositiveFP.degreeConditions_inFP

/-- Paper F.1.2; `ComplexCSP.ComplexityClassification.degree_conditions`. -/
theorem paper_cor_degree_multiple_main_degree_conditions : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_degree_conditions :=
  @ComplexCSP.ComplexityClassification.degree_conditions

/-- Paper F.1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity`. -/
theorem paper_cor_degree_multiple_main_encodedDegreeGlobalTest_complexity : ComplexCSP.PaperStatements.paper_cor_degree_multiple_main_encodedDegreeGlobalTest_complexity :=
  @ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_agreement`. -/
theorem paper_lem_purification_invariance_table_ambient_agreement.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_purification_invariance_table_ambient_agreement.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_agreement.{u_1, u_2}

/-- Paper F.3.1; `ComplexCSP.AmbientTableAgreement.disjoint_iff`. -/
theorem paper_lem_purification_invariance_disjoint_iff.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_purification_invariance_disjoint_iff.{u_1, u_2} :=
  @ComplexCSP.AmbientTableAgreement.disjoint_iff.{u_1, u_2}

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_normalized_ambient_agreement`. -/
theorem paper_lem_purification_invariance_table_normalized_ambient_agreement.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_purification_invariance_table_normalized_ambient_agreement.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_normalized_ambient_agreement.{u_1, u_2}

/-- Paper F.3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_blockOrthogonal_iff`. -/
theorem paper_lem_purification_invariance_table_ambient_blockOrthogonal_iff.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_purification_invariance_table_ambient_blockOrthogonal_iff.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_blockOrthogonal_iff.{u_1, u_2}

/-- Paper F.3.2; `ComplexCSP.jointBO_iff_singletonBO`. -/
theorem paper_cor_singleton_purification_jointBO_iff_singletonBO : ComplexCSP.PaperStatements.paper_cor_singleton_purification_jointBO_iff_singletonBO :=
  @ComplexCSP.jointBO_iff_singletonBO

/-- Paper F.3.3; `ComplexCSP.paper_generated_diagonal_minor`. -/
theorem paper_lem_diagonal_minors_paper_generated_diagonal_minor : ComplexCSP.PaperStatements.paper_lem_diagonal_minors_paper_generated_diagonal_minor :=
  @ComplexCSP.paper_generated_diagonal_minor

/-- Paper F.3.3, F.5.1; `ComplexCSP.generated_iff_paperGenerated`. -/
theorem paper_lem_diagonal_minors_generated_iff_paperGenerated : ComplexCSP.PaperStatements.paper_lem_diagonal_minors_generated_iff_paperGenerated :=
  @ComplexCSP.generated_iff_paperGenerated

/-- Paper F.3.4; `ComplexCSP.singletonBO_iff_bounded`. -/
theorem paper_lem_bo_arity_bound_singletonBO_iff_bounded : ComplexCSP.PaperStatements.paper_lem_bo_arity_bound_singletonBO_iff_bounded :=
  @ComplexCSP.singletonBO_iff_bounded

/-- Paper F.3.4; `ComplexCSP.bounded_external_arity_counterexample`. -/
theorem paper_lem_bo_arity_bound_bounded_external_arity_counterexample : ComplexCSP.PaperStatements.paper_lem_bo_arity_bound_bounded_external_arity_counterexample :=
  @ComplexCSP.bounded_external_arity_counterexample

/-- Paper F.3.5; `ComplexCSP.Certificates.value_norm_eq_iff_numberFieldRoot`. -/
theorem paper_lem_intrinsic_purification_tests_value_norm_eq_iff_numberFieldRoot.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_value_norm_eq_iff_numberFieldRoot.{u_1, u_2} :=
  @ComplexCSP.Certificates.value_norm_eq_iff_numberFieldRoot.{u_1, u_2}

/-- Paper F.3.5; `ComplexCSP.Certificates.entry_norm_products_iff_twisted`. -/
theorem paper_lem_intrinsic_purification_tests_entry_norm_products_iff_twisted.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_entry_norm_products_iff_twisted.{u_1, u_2} :=
  @ComplexCSP.Certificates.entry_norm_products_iff_twisted.{u_1, u_2}

/-- Paper F.3.5; `ComplexCSP.Certificates.entry_products_iff_field_products`. -/
theorem paper_lem_intrinsic_purification_tests_entry_products_iff_field_products.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_entry_products_iff_field_products.{u_1, u_2} :=
  @ComplexCSP.Certificates.entry_products_iff_field_products.{u_1, u_2}

/-- Paper F.3.5; `ComplexCSP.Certificates.value_root_covariance`. -/
theorem paper_lem_intrinsic_purification_tests_value_root_covariance.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_value_root_covariance.{u_1, u_2} :=
  @ComplexCSP.Certificates.value_root_covariance.{u_1, u_2}

/-- Paper F.3.5; `ComplexCSP.Certificates.intrinsicTests_legalTable`. -/
theorem paper_lem_intrinsic_purification_tests_intrinsicTests_legalTable.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_intrinsicTests_legalTable.{u_1, u_2} :=
  @ComplexCSP.Certificates.intrinsicTests_legalTable.{u_1, u_2}

/-- Paper F.4.2; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_finite_union`. -/
theorem paper_thm_finite_bo_certificates_legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2} : ComplexCSP.PaperStatements.paper_thm_finite_bo_certificates_legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2} :=
  @ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2}

/-- Paper F.4.2; `ComplexCSP.Certificates.certificate_complete`. -/
theorem paper_thm_finite_bo_certificates_certificate_complete.{u_1, u_2, u_3, u_4} : ComplexCSP.PaperStatements.paper_thm_finite_bo_certificates_certificate_complete.{u_1, u_2, u_3, u_4} :=
  @ComplexCSP.Certificates.certificate_complete.{u_1, u_2, u_3, u_4}

/-- Paper F.4.2; `ComplexCSP.Certificates.certificate_sound`. -/
theorem paper_thm_finite_bo_certificates_certificate_sound.{u_1, u_2, u_3, u_4} : ComplexCSP.PaperStatements.paper_thm_finite_bo_certificates_certificate_sound.{u_1, u_2, u_3, u_4} :=
  @ComplexCSP.Certificates.certificate_sound.{u_1, u_2, u_3, u_4}

/-- Paper F.4.4; `ComplexCSP.finite_union_zeroLocus_iff`. -/
theorem paper_cor_bo_product_identities_finite_union_zeroLocus_iff.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_cor_bo_product_identities_finite_union_zeroLocus_iff.{u_1, u_2, u_3} :=
  @ComplexCSP.finite_union_zeroLocus_iff.{u_1, u_2, u_3}

/-- Paper F.4.4; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_product_equations`. -/
theorem paper_cor_bo_product_identities_legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2} : ComplexCSP.PaperStatements.paper_cor_bo_product_identities_legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2} :=
  @ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2}

/-- Paper F.4.4; `ComplexCSP.Certificates.allProductPrograms_zero_iff`. -/
theorem paper_cor_bo_product_identities_allProductPrograms_zero_iff : ComplexCSP.PaperStatements.paper_cor_bo_product_identities_allProductPrograms_zero_iff :=
  @ComplexCSP.Certificates.allProductPrograms_zero_iff

/-- Paper F.4.4; `ComplexCSP.Certificates.optimizedProductPrograms_zero_iff`. -/
theorem paper_cor_bo_product_identities_optimizedProductPrograms_zero_iff : ComplexCSP.PaperStatements.paper_cor_bo_product_identities_optimizedProductPrograms_zero_iff :=
  @ComplexCSP.Certificates.optimizedProductPrograms_zero_iff

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.exists_presentation`. -/
theorem paper_lem_pinned_realization_exists_presentation : ComplexCSP.PaperStatements.paper_lem_pinned_realization_exists_presentation :=
  @ComplexCSP.GeneratedTable.exists_presentation

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.ofPresentation_mul`. -/
theorem paper_lem_pinned_realization_ofPresentation_mul : ComplexCSP.PaperStatements.paper_lem_pinned_realization_ofPresentation_mul :=
  @ComplexCSP.GeneratedTable.ofPresentation_mul

/-- Paper F.5.1; `ComplexCSP.GeneratedTable.forall_iff_presentations`. -/
theorem paper_lem_pinned_realization_forall_iff_presentations : ComplexCSP.PaperStatements.paper_lem_pinned_realization_forall_iff_presentations :=
  @ComplexCSP.GeneratedTable.forall_iff_presentations

/-- Paper F.5.1; `ComplexCSP.Instance.partition_glue`. -/
theorem paper_lem_pinned_realization_partition_glue : ComplexCSP.PaperStatements.paper_lem_pinned_realization_partition_glue :=
  @ComplexCSP.Instance.partition_glue

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.printed_theorem_5_2_counterexample`. -/
theorem paper_rem_simple_instance_counterexample_printed_theorem_5_2_counterexample : ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_printed_theorem_5_2_counterexample :=
  @ComplexCSP.Theorem52Counterexample.printed_theorem_5_2_counterexample

/-- Paper F.5.2; `ComplexCSP.Instance.partition_eq_of_iso_pin_twins`. -/
theorem paper_thm_young_pinned_partition_eq_of_iso_pin_twins : ComplexCSP.PaperStatements.paper_thm_young_pinned_partition_eq_of_iso_pin_twins :=
  @ComplexCSP.Instance.partition_eq_of_iso_pin_twins

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.all_instance_pinned_iso_iff`. -/
theorem paper_thm_young_pinned_all_instance_pinned_iso_iff : ComplexCSP.PaperStatements.paper_thm_young_pinned_all_instance_pinned_iso_iff :=
  @ComplexCSP.PinnedIsomorphism.all_instance_pinned_iso_iff

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.pinnedIsoCheck_correct_all_instances`. -/
theorem paper_thm_young_pinned_pinnedIsoCheck_correct_all_instances : ComplexCSP.PaperStatements.paper_thm_young_pinned_pinnedIsoCheck_correct_all_instances :=
  @ComplexCSP.PinnedIsomorphism.pinnedIsoCheck_correct_all_instances

/-- Paper F.5.4; `ComplexCSP.Instance.partition_tensorConjugate`. -/
theorem paper_lem_tensor_character_partition_tensorConjugate : ComplexCSP.PaperStatements.paper_lem_tensor_character_partition_tensorConjugate :=
  @ComplexCSP.Instance.partition_tensorConjugate

/-- Paper F.5.4; `ComplexCSP.Instance.partition_tensorConjugate_zero`. -/
theorem paper_lem_tensor_character_partition_tensorConjugate_zero : ComplexCSP.PaperStatements.paper_lem_tensor_character_partition_tensorConjugate_zero :=
  @ComplexCSP.Instance.partition_tensorConjugate_zero

/-- Paper F.5.4; `ComplexCSP.tensor_realizes_pinnedMonomial`. -/
theorem paper_lem_tensor_character_tensor_realizes_pinnedMonomial : ComplexCSP.PaperStatements.paper_lem_tensor_character_tensor_realizes_pinnedMonomial :=
  @ComplexCSP.tensor_realizes_pinnedMonomial

/-- Paper F.5.5; `ComplexCSP.ScalarTags.exists_common_rational_tags`. -/
theorem paper_lem_scalar_tags_exists_common_rational_tags.{u_1, u_3, u_4, u_5} : ComplexCSP.PaperStatements.paper_lem_scalar_tags_exists_common_rational_tags.{u_1, u_3, u_4, u_5} :=
  @ComplexCSP.ScalarTags.exists_common_rational_tags.{u_1, u_3, u_4, u_5}

/-- Paper F.5.5; `ComplexCSP.ScalarTags.findRationalTags_spec`. -/
theorem paper_lem_scalar_tags_findRationalTags_spec.{u_1, u_3, u_4} : ComplexCSP.PaperStatements.paper_lem_scalar_tags_findRationalTags_spec.{u_1, u_3, u_4} :=
  @ComplexCSP.ScalarTags.findRationalTags_spec.{u_1, u_3, u_4}

/-- Paper F.5.5; `ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged_correct`. -/
theorem paper_lem_scalar_tags_comparePaperTagged_correct : ComplexCSP.PaperStatements.paper_lem_scalar_tags_comparePaperTagged_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged_correct

/-- Paper F.5.6; `ComplexCSP.Recognition.PinnedMonomial.characters_eq_iff_all_tensor_instances`. -/
theorem paper_lem_character_comparison_characters_eq_iff_all_tensor_instances : ComplexCSP.PaperStatements.paper_lem_character_comparison_characters_eq_iff_all_tensor_instances :=
  @ComplexCSP.Recognition.PinnedMonomial.characters_eq_iff_all_tensor_instances

/-- Paper F.5.6; `ComplexCSP.Recognition.PinnedMonomial.compare_correct`. -/
theorem paper_lem_character_comparison_compare_correct : ComplexCSP.PaperStatements.paper_lem_character_comparison_compare_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.compare_correct

/-- Paper F.5.6; `ComplexCSP.Recognition.partition_common_tags_iff`. -/
theorem paper_lem_character_comparison_partition_common_tags_iff : ComplexCSP.PaperStatements.paper_lem_character_comparison_partition_common_tags_iff :=
  @ComplexCSP.Recognition.partition_common_tags_iff

/-- Paper F.5.7; `ComplexCSP.characters_linearIndependent`. -/
theorem paper_lem_dedekind_independence_characters_linearIndependent.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_dedekind_independence_characters_linearIndependent.{u_1, u_2, u_3} :=
  @ComplexCSP.characters_linearIndependent.{u_1, u_2, u_3}

/-- Paper F.5.7; `ComplexCSP.character_coefficients_eq_zero`. -/
theorem paper_lem_dedekind_independence_character_coefficients_eq_zero.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_dedekind_independence_character_coefficients_eq_zero.{u_1, u_2, u_3} :=
  @ComplexCSP.character_coefficients_eq_zero.{u_1, u_2, u_3}

/-- Paper F.5.7; `ComplexCSP.grouped_character_zero_iff`. -/
theorem paper_lem_dedekind_independence_grouped_character_zero_iff.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_dedekind_independence_grouped_character_zero_iff.{u_1, u_2, u_3} :=
  @ComplexCSP.grouped_character_zero_iff.{u_1, u_2, u_3}

/-- Paper F.5.8; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_correct`. -/
theorem paper_thm_universal_identity_uniformAlgebraicIdentityTest_correct : ComplexCSP.PaperStatements.paper_thm_universal_identity_uniformAlgebraicIdentityTest_correct :=
  @ComplexCSP.Recognition.uniformAlgebraicIdentityTest_correct

/-- Paper F.5.8; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_rejects_iff`. -/
theorem paper_thm_universal_identity_uniformAlgebraicIdentityTest_rejects_iff : ComplexCSP.PaperStatements.paper_thm_universal_identity_uniformAlgebraicIdentityTest_rejects_iff :=
  @ComplexCSP.Recognition.uniformAlgebraicIdentityTest_rejects_iff

/-- Paper F.5.8; `ComplexCSP.Recognition.programIdentityTest_mvPolynomial_correct`. -/
theorem paper_thm_universal_identity_programIdentityTest_mvPolynomial_correct : ComplexCSP.PaperStatements.paper_thm_universal_identity_programIdentityTest_mvPolynomial_correct :=
  @ComplexCSP.Recognition.programIdentityTest_mvPolynomial_correct

/-- Paper F.10.1; `ComplexCSP.Instance.degree_filter_identity`. -/
theorem paper_lem_degree_filtered_character_comparison_degree_filter_identity : ComplexCSP.PaperStatements.paper_lem_degree_filtered_character_comparison_degree_filter_identity :=
  @ComplexCSP.Instance.degree_filter_identity

/-- Paper F.10.1; `ComplexCSP.Recognition.PinnedMonomial.filtered_sum_formula`. -/
theorem paper_lem_degree_filtered_character_comparison_filtered_sum_formula : ComplexCSP.PaperStatements.paper_lem_degree_filtered_character_comparison_filtered_sum_formula :=
  @ComplexCSP.Recognition.PinnedMonomial.filtered_sum_formula

/-- Paper F.10.1; `ComplexCSP.Recognition.PinnedMonomial.degreeCompare_correct`. -/
theorem paper_lem_degree_filtered_character_comparison_degreeCompare_correct : ComplexCSP.PaperStatements.paper_lem_degree_filtered_character_comparison_degreeCompare_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.degreeCompare_correct

/-- Paper F.10.2; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_correct`. -/
theorem paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_correct : ComplexCSP.PaperStatements.paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_correct :=
  @ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_correct

/-- Paper F.10.2; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_rejects_iff`. -/
theorem paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_rejects_iff : ComplexCSP.PaperStatements.paper_thm_degree_multiple_universal_identity_uniformAlgebraicDegreeIdentityTest_rejects_iff :=
  @ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_rejects_iff

/-- Paper F.6.2; `ComplexCSP.Recognition.globalCertificateTest_exponent_correct_jointBO`. -/
theorem paper_thm_global_bo_decidable_globalCertificateTest_exponent_correct_jointBO : ComplexCSP.PaperStatements.paper_thm_global_bo_decidable_globalCertificateTest_exponent_correct_jointBO :=
  @ComplexCSP.Recognition.globalCertificateTest_exponent_correct_jointBO

/-- Paper F.6.2; `ComplexCSP.Recognition.uniformAlgebraicGlobalTest_correct_jointBO`. -/
theorem paper_thm_global_bo_decidable_uniformAlgebraicGlobalTest_correct_jointBO : ComplexCSP.PaperStatements.paper_thm_global_bo_decidable_uniformAlgebraicGlobalTest_correct_jointBO :=
  @ComplexCSP.Recognition.uniformAlgebraicGlobalTest_correct_jointBO

/-- Paper F.7.1; `ComplexCSP.infinite_simultaneous_multiset_powerSum_ne_zero`. -/
theorem paper_lem_simultaneous_power_sums_infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2} : ComplexCSP.PaperStatements.paper_lem_simultaneous_power_sums_infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2} :=
  @ComplexCSP.infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2}

/-- Paper F.7.1; `ComplexCSP.exists_simultaneous_powerSum_ne_zero_bounded`. -/
theorem paper_lem_simultaneous_power_sums_exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_simultaneous_power_sums_exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3} :=
  @ComplexCSP.exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3}

/-- Paper F.7.1; `ComplexCSP.findSimultaneousPower_success`. -/
theorem paper_lem_simultaneous_power_sums_findSimultaneousPower_success.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_simultaneous_power_sums_findSimultaneousPower_success.{u_1, u_2, u_3} :=
  @ComplexCSP.findSimultaneousPower_success.{u_1, u_2, u_3}

/-- Paper F.7.1; `ComplexCSP.findSimultaneousPower_sound`. -/
theorem paper_lem_simultaneous_power_sums_findSimultaneousPower_sound.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_lem_simultaneous_power_sums_findSimultaneousPower_sound.{u_1, u_2, u_3} :=
  @ComplexCSP.findSimultaneousPower_sound.{u_1, u_2, u_3}

/-- Paper F.7.2; `ComplexCSP.paper_generated_equalityfree_pp_support`. -/
theorem paper_lem_equality_free_support_realization_paper_generated_equalityfree_pp_support : ComplexCSP.PaperStatements.paper_lem_equality_free_support_realization_paper_generated_equalityfree_pp_support :=
  @ComplexCSP.paper_generated_equalityfree_pp_support

/-- Paper F.7.2; `ComplexCSP.PresentedAtom.compile_correct`. -/
theorem paper_lem_equality_free_support_realization_compile_correct : ComplexCSP.PaperStatements.paper_lem_equality_free_support_realization_compile_correct :=
  @ComplexCSP.PresentedAtom.compile_correct

/-- Paper F.7.2; `ComplexCSP.findSupportPower_spec`. -/
theorem paper_lem_equality_free_support_realization_findSupportPower_spec : ComplexCSP.PaperStatements.paper_lem_equality_free_support_realization_findSupportPower_spec :=
  @ComplexCSP.findSupportPower_spec

/-- Paper F.7.3, F.7.4, F.8.2; `ComplexCSP.JointBO.original`. -/
theorem paper_cor_generated_singleton_rectangularity_original : ComplexCSP.PaperStatements.paper_cor_generated_singleton_rectangularity_original :=
  @ComplexCSP.JointBO.original

/-- Paper F.7.3, F.7.4; `ComplexCSP.allGeneratedOriginalBO_supportRectangular`. -/
theorem paper_cor_generated_singleton_rectangularity_allGeneratedOriginalBO_supportRectangular : ComplexCSP.PaperStatements.paper_cor_generated_singleton_rectangularity_allGeneratedOriginalBO_supportRectangular :=
  @ComplexCSP.allGeneratedOriginalBO_supportRectangular

/-- Paper F.7.3, F.7.4; `ComplexCSP.generated_supports_equalityfree_rectangularity`. -/
theorem paper_cor_generated_singleton_rectangularity_generated_supports_equalityfree_rectangularity : ComplexCSP.PaperStatements.paper_cor_generated_singleton_rectangularity_generated_supports_equalityfree_rectangularity :=
  @ComplexCSP.generated_supports_equalityfree_rectangularity

/-- Paper F.7.3; `ComplexCSP.MaltsevRelations.rectangular_iff_equal_or_disjoint`. -/
theorem paper_cor_generated_singleton_rectangularity_rectangular_iff_equal_or_disjoint.{u, v} : ComplexCSP.PaperStatements.paper_cor_generated_singleton_rectangularity_rectangular_iff_equal_or_disjoint.{u, v} :=
  @ComplexCSP.MaltsevRelations.rectangular_iff_equal_or_disjoint.{u, v}

/-- Paper F.7.4; `ComplexCSP.MaltsevRelations.finite_family_maltsev`. -/
theorem paper_lem_finite_support_maltsev_finite_family_maltsev.{u} : ComplexCSP.PaperStatements.paper_lem_finite_support_maltsev_finite_family_maltsev.{u} :=
  @ComplexCSP.MaltsevRelations.finite_family_maltsev.{u}

/-- Paper F.7.5; `ComplexCSP.JointBO.common_support_maltsev`. -/
theorem paper_thm_common_support_maltsev_common_support_maltsev : ComplexCSP.PaperStatements.paper_thm_common_support_maltsev_common_support_maltsev :=
  @ComplexCSP.JointBO.common_support_maltsev

/-- Paper F.7.5; `ComplexCSP.MaltsevRelations.common_maltsev_of_finite_subfamilies`. -/
theorem paper_thm_common_support_maltsev_common_maltsev_of_finite_subfamilies.{u} : ComplexCSP.PaperStatements.paper_thm_common_support_maltsev_common_maltsev_of_finite_subfamilies.{u} :=
  @ComplexCSP.MaltsevRelations.common_maltsev_of_finite_subfamilies.{u}

/-- Paper F.7.5; `ComplexCSP.common_maltsev_of_generated_support_rectangularity`. -/
theorem paper_thm_common_support_maltsev_common_maltsev_of_generated_support_rectangularity : ComplexCSP.PaperStatements.paper_thm_common_support_maltsev_common_maltsev_of_generated_support_rectangularity :=
  @ComplexCSP.common_maltsev_of_generated_support_rectangularity

/-- Paper F.8.1; `ComplexCSP.paper_generated_pow`. -/
theorem paper_lem_generated_entrywise_powers_paper_generated_pow : ComplexCSP.PaperStatements.paper_lem_generated_entrywise_powers_paper_generated_pow :=
  @ComplexCSP.paper_generated_pow

/-- Paper F.8.1; `ComplexCSP.Presentation.table_power`. -/
theorem paper_lem_generated_entrywise_powers_table_power : ComplexCSP.PaperStatements.paper_lem_generated_entrywise_powers_table_power :=
  @ComplexCSP.Presentation.table_power

/-- Paper F.8.2; `ComplexCSP.BlockOrthogonality.finite_row_phases_of_power_BO`. -/
theorem paper_lem_finite_row_phases_finite_row_phases_of_power_BO.{u, v} : ComplexCSP.PaperStatements.paper_lem_finite_row_phases_finite_row_phases_of_power_BO.{u, v} :=
  @ComplexCSP.BlockOrthogonality.finite_row_phases_of_power_BO.{u, v}

/-- Paper F.8.2; `ComplexCSP.Instance.generated_pow`. -/
theorem paper_lem_finite_row_phases_generated_pow : ComplexCSP.PaperStatements.paper_lem_finite_row_phases_generated_pow :=
  @ComplexCSP.Instance.generated_pow

/-- Paper F.8.2; `ComplexCSP.Instance.generated_mem_workingField`. -/
theorem paper_lem_finite_row_phases_generated_mem_workingField : ComplexCSP.PaperStatements.paper_lem_finite_row_phases_generated_mem_workingField :=
  @ComplexCSP.Instance.generated_mem_workingField

/-- Paper F.8.3; `ComplexCSP.lemma_8_3`. -/
theorem paper_lem_nondegenerate_exponential_sums_lemma_8_3 : ComplexCSP.PaperStatements.paper_lem_nondegenerate_exponential_sums_lemma_8_3 :=
  @ComplexCSP.lemma_8_3

/-- Paper F.8.3; `ComplexCSP.finite_weightedPowerSum_zeros_algebraic`. -/
theorem paper_lem_nondegenerate_exponential_sums_finite_weightedPowerSum_zeros_algebraic : ComplexCSP.PaperStatements.paper_lem_nondegenerate_exponential_sums_finite_weightedPowerSum_zeros_algebraic :=
  @ComplexCSP.finite_weightedPowerSum_zeros_algebraic

/-- Paper F.8.4; `ComplexCSP.RowEquivalenceRealization.generated_row_equivalence_detector`. -/
theorem paper_thm_omega_support_realization_generated_row_equivalence_detector : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_generated_row_equivalence_detector :=
  @ComplexCSP.RowEquivalenceRealization.generated_row_equivalence_detector

/-- Paper F.8.4; `ComplexCSP.RowEquivalenceRealization.exists_detector_support`. -/
theorem paper_thm_omega_support_realization_exists_detector_support.{u, v} : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_exists_detector_support.{u, v} :=
  @ComplexCSP.RowEquivalenceRealization.exists_detector_support.{u, v}

/-- Paper F.8.4; `ComplexCSP.paper_generated_rowDetector`. -/
theorem paper_thm_omega_support_realization_paper_generated_rowDetector : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_paper_generated_rowDetector :=
  @ComplexCSP.paper_generated_rowDetector

/-- Paper F.8.4; `ComplexCSP.RowDetector.findDetectorTime_success`. -/
theorem paper_thm_omega_support_realization_findDetectorTime_success.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_findDetectorTime_success.{u_1, u_2, u_3} :=
  @ComplexCSP.RowDetector.findDetectorTime_success.{u_1, u_2, u_3}

/-- Paper F.8.4; `ComplexCSP.RowDetector.fieldExponent_killsTorsion`. -/
theorem paper_thm_omega_support_realization_fieldExponent_killsTorsion.{u_1} : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_fieldExponent_killsTorsion.{u_1} :=
  @ComplexCSP.RowDetector.fieldExponent_killsTorsion.{u_1}

/-- Paper F.8.4; `ComplexCSP.RowDetectorEmbeddedExistence.generated_detector_exact_workingField`. -/
theorem paper_thm_omega_support_realization_generated_detector_exact_workingField : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_generated_detector_exact_workingField :=
  @ComplexCSP.RowDetectorEmbeddedExistence.generated_detector_exact_workingField

/-- Paper F.8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_support`. -/
theorem paper_thm_omega_support_realization_validatedRowDetector_support : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_validatedRowDetector_support :=
  @ComplexCSP.EncodedNumberField.validatedRowDetector_support

/-- Paper F.8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_exact_formula`. -/
theorem paper_thm_omega_support_realization_validatedRowDetector_exact_formula : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_validatedRowDetector_exact_formula :=
  @ComplexCSP.EncodedNumberField.validatedRowDetector_exact_formula

/-- Paper F.8.4; `ComplexCSP.EffectiveRoots.torsion_exponent_eq_order`. -/
theorem paper_thm_omega_support_realization_torsion_exponent_eq_order.{u_1} : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_torsion_exponent_eq_order.{u_1} :=
  @ComplexCSP.EffectiveRoots.torsion_exponent_eq_order.{u_1}

/-- Paper F.8.4; `ComplexCSP.EffectiveRoots.checkedRootExponent_eq_fieldExponent`. -/
theorem paper_thm_omega_support_realization_checkedRootExponent_eq_fieldExponent : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_checkedRootExponent_eq_fieldExponent :=
  @ComplexCSP.EffectiveRoots.checkedRootExponent_eq_fieldExponent

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_support`. -/
theorem paper_thm_omega_support_realization_uniformAlgebraicRowDetector_support : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_uniformAlgebraicRowDetector_support :=
  @ComplexCSP.uniformAlgebraicRowDetector_support

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_exponent`. -/
theorem paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exponent : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exponent :=
  @ComplexCSP.uniformAlgebraicRowDetector_exponent

/-- Paper F.8.4; `ComplexCSP.uniformAlgebraicRowDetector_exact_formula`. -/
theorem paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exact_formula : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_uniformAlgebraicRowDetector_exact_formula :=
  @ComplexCSP.uniformAlgebraicRowDetector_exact_formula

/-- Paper F.8.4; `ComplexCSP.Recognition.identityPairedCandidate_fieldRange`. -/
theorem paper_thm_omega_support_realization_identityPairedCandidate_fieldRange : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_identityPairedCandidate_fieldRange :=
  @ComplexCSP.Recognition.identityPairedCandidate_fieldRange

/-- Paper F.8.4; `ComplexCSP.Recognition.identityPairedCandidate_rootExponent_eq`. -/
theorem paper_thm_omega_support_realization_identityPairedCandidate_rootExponent_eq : ComplexCSP.PaperStatements.paper_thm_omega_support_realization_identityPairedCandidate_rootExponent_eq :=
  @ComplexCSP.Recognition.identityPairedCandidate_rootExponent_eq

/-- Paper F.8.5; `ComplexCSP.RowEquivalenceRealization.omega_mem_generatedSupports`. -/
theorem paper_cor_omega_reduces_to_supports_omega_mem_generatedSupports : ComplexCSP.PaperStatements.paper_cor_omega_reduces_to_supports_omega_mem_generatedSupports :=
  @ComplexCSP.RowEquivalenceRealization.omega_mem_generatedSupports

/-- Paper F.9.1; `ComplexCSP.RowTypes.complex_type_partition`. -/
theorem paper_lem_omega_implies_type_complex_type_partition.{u} : ComplexCSP.PaperStatements.paper_lem_omega_implies_type_complex_type_partition.{u} :=
  @ComplexCSP.RowTypes.complex_type_partition.{u}

/-- Paper F.9.1; `ComplexCSP.RowTypes.rowEquivalence_iff`. -/
theorem paper_lem_omega_implies_type_rowEquivalence_iff.{u, v, w, u_1} : ComplexCSP.PaperStatements.paper_lem_omega_implies_type_rowEquivalence_iff.{u, v, w, u_1} :=
  @ComplexCSP.RowTypes.rowEquivalence_iff.{u, v, w, u_1}

/-- Paper F.9.1; `ComplexCSP.RowTypes.preserves_omega_pairs`. -/
theorem paper_lem_omega_implies_type_preserves_omega_pairs.{u} : ComplexCSP.PaperStatements.paper_lem_omega_implies_type_preserves_omega_pairs.{u} :=
  @ComplexCSP.RowTypes.preserves_omega_pairs.{u}

/-- Paper F.9.2; `ComplexCSP.JointBO.global_type_partition`. -/
theorem paper_thm_structural_collapse_global_type_partition : ComplexCSP.PaperStatements.paper_thm_structural_collapse_global_type_partition :=
  @ComplexCSP.JointBO.global_type_partition

/-- Paper F.9.2; `ComplexCSP.JointBO.global_maltsev`. -/
theorem paper_thm_structural_collapse_global_maltsev : ComplexCSP.PaperStatements.paper_thm_structural_collapse_global_maltsev :=
  @ComplexCSP.JointBO.global_maltsev

/-- Paper F.9.2; `ComplexCSP.RowEquivalenceRealization.common_support_and_row_maltsev`. -/
theorem paper_thm_structural_collapse_common_support_and_row_maltsev : ComplexCSP.PaperStatements.paper_thm_structural_collapse_common_support_and_row_maltsev :=
  @ComplexCSP.RowEquivalenceRealization.common_support_and_row_maltsev

/-- Paper F.B.1; `ComplexCSP.PaperBridge.theorem_5_2_complex_counterexample`. -/
theorem paper_rem_simple_instance_counterexample_theorem_5_2_complex_counterexample : ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_theorem_5_2_complex_counterexample :=
  @ComplexCSP.PaperBridge.theorem_5_2_complex_counterexample

/-- Paper F.1.1, F.1.2; `ComplexCSP.PaperBridge.workingField_realization`. -/
theorem paper_thm_main_workingField_realization : ComplexCSP.PaperStatements.paper_thm_main_workingField_realization :=
  @ComplexCSP.PaperBridge.workingField_realization

/-- Paper F.7.3; `ComplexCSP.PaperBridge.lemma_7_3_pp_rectangularity`. -/
theorem paper_cor_generated_singleton_rectangularity_lemma_7_3_pp_rectangularity : ComplexCSP.PaperStatements.paper_cor_generated_singleton_rectangularity_lemma_7_3_pp_rectangularity :=
  @ComplexCSP.PaperBridge.lemma_7_3_pp_rectangularity

/-- Paper F.7.4; `ComplexCSP.PaperBridge.lemma_7_4`. -/
theorem paper_lem_finite_support_maltsev_lemma_7_4 : ComplexCSP.PaperStatements.paper_lem_finite_support_maltsev_lemma_7_4 :=
  @ComplexCSP.PaperBridge.lemma_7_4

/-- Paper F.8.2; `ComplexCSP.PaperBridge.lemma_8_2`. -/
theorem paper_lem_finite_row_phases_lemma_8_2 : ComplexCSP.PaperStatements.paper_lem_finite_row_phases_lemma_8_2 :=
  @ComplexCSP.PaperBridge.lemma_8_2

/-- Paper F.8.5; `ComplexCSP.PaperBridge.lemma_8_5`. -/
theorem paper_cor_omega_reduces_to_supports_lemma_8_5 : ComplexCSP.PaperStatements.paper_cor_omega_reduces_to_supports_lemma_8_5 :=
  @ComplexCSP.PaperBridge.lemma_8_5

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_norm_iff`. -/
theorem paper_lem_intrinsic_purification_tests_normalization_norm_iff : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_normalization_norm_iff :=
  @ComplexCSP.PaperBridge.normalization_norm_iff

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_products_iff`. -/
theorem paper_lem_intrinsic_purification_tests_normalization_products_iff : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_normalization_products_iff :=
  @ComplexCSP.PaperBridge.normalization_products_iff

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_norm_products_iff`. -/
theorem paper_lem_intrinsic_purification_tests_normalization_norm_products_iff : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_normalization_norm_products_iff :=
  @ComplexCSP.PaperBridge.normalization_norm_products_iff

/-- Paper F.3.5; `ComplexCSP.PaperBridge.normalization_covariance_iff`. -/
theorem paper_lem_intrinsic_purification_tests_normalization_covariance_iff : ComplexCSP.PaperStatements.paper_lem_intrinsic_purification_tests_normalization_covariance_iff :=
  @ComplexCSP.PaperBridge.normalization_covariance_iff

/-- Paper F.1.1; `ComplexCSP.ComplexityClassification.ordinary_conditions`. -/
theorem paper_thm_main_ordinary_conditions : ComplexCSP.PaperStatements.paper_thm_main_ordinary_conditions :=
  @ComplexCSP.ComplexityClassification.ordinary_conditions

/-- Paper F.1.1; `ComplexCSP.Recognition.encodedGlobalTest_complexity`. -/
theorem paper_thm_main_encodedGlobalTest_complexity : ComplexCSP.PaperStatements.paper_thm_main_encodedGlobalTest_complexity :=
  @ComplexCSP.Recognition.encodedGlobalTest_complexity

/-- Paper F.5.2; `ComplexCSP.PinnedIsomorphism.all_instance_completeness`. -/
theorem paper_thm_young_pinned_all_instance_completeness : ComplexCSP.PaperStatements.paper_thm_young_pinned_all_instance_completeness :=
  @ComplexCSP.PinnedIsomorphism.all_instance_completeness

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.doubledUnary_first_value`. -/
theorem paper_rem_simple_instance_counterexample_doubledUnary_first_value : ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_doubledUnary_first_value :=
  @ComplexCSP.Theorem52Counterexample.doubledUnary_first_value

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.doubledUnary_second_value`. -/
theorem paper_rem_simple_instance_counterexample_doubledUnary_second_value : ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_doubledUnary_second_value :=
  @ComplexCSP.Theorem52Counterexample.doubledUnary_second_value

/-- Paper F.B.1; `ComplexCSP.Theorem52Counterexample.paperSimple_iff_simple`. -/
theorem paper_rem_simple_instance_counterexample_paperSimple_iff_simple : ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_paperSimple_iff_simple :=
  @ComplexCSP.Theorem52Counterexample.paperSimple_iff_simple

/-- Paper F.1.1; `ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode`. -/
theorem paper_thm_main_finiteAlgebraicLanguage_decode_encode : ComplexCSP.PaperStatements.paper_thm_main_finiteAlgebraicLanguage_decode_encode :=
  @ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode


/-- STOC snapshot: explicit contract in Statements.lean. -/
theorem paper_lem_purification_invariance_group_extensions :
    ComplexCSP.PaperStatements.paper_lem_purification_invariance_group_extensions :=
  @ComplexCSP.Paper.purification_group_extensions

/-- STOC snapshot: explicit contract in Statements.lean. -/
theorem paper_lem_purification_invariance_singleton_phase_in_field :
    ComplexCSP.PaperStatements.paper_lem_purification_invariance_singleton_phase_in_field :=
  @ComplexCSP.Paper.singleton_phase_in_field

/-- STOC snapshot: explicit contract in Statements.lean. -/
theorem paper_lem_character_comparison_indexed_family_comparison :
    ComplexCSP.PaperStatements.paper_lem_character_comparison_indexed_family_comparison :=
  @ComplexCSP.Paper.indexed_family_comparison


/-- The complete current Remark F.B.1 counterexample. -/
theorem paper_rem_simple_instance_counterexample_complete :
    ComplexCSP.PaperStatements.paper_rem_simple_instance_counterexample_complete :=
  @ComplexCSP.Paper.appendix_simple_instance_counterexample

end ComplexCSP.PaperSpec

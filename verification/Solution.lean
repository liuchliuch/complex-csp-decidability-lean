import verification.Statements

/-! Proofs of the fixed paper specification. -/

namespace ComplexCSP.PaperSpec

/-- Paper 1.1; `ComplexCSP.Recognition.encodedGlobalTest_correct`. -/
theorem paper_1_1_encodedGlobalTest_correct : ComplexCSP.PaperStatements.paper_1_1_encodedGlobalTest_correct :=
  @ComplexCSP.Recognition.encodedGlobalTest_correct

/-- Paper 1.1; `ComplexCSP.Recognition.exists_algebraic_language_description`. -/
theorem paper_1_1_exists_algebraic_language_description : ComplexCSP.PaperStatements.paper_1_1_exists_algebraic_language_description :=
  @ComplexCSP.Recognition.exists_algebraic_language_description

/-- Paper 1.1, 9.2; `ComplexCSP.structural_collapse`. -/
theorem paper_1_1_structural_collapse : ComplexCSP.PaperStatements.paper_1_1_structural_collapse :=
  @ComplexCSP.structural_collapse

/-- Paper 1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_correct`. -/
theorem paper_1_2_encodedDegreeGlobalTest_correct : ComplexCSP.PaperStatements.paper_1_2_encodedDegreeGlobalTest_correct :=
  @ComplexCSP.Recognition.encodedDegreeGlobalTest_correct

/-- Paper 1.2; `ComplexCSP.degree_structural_collapse`. -/
theorem paper_1_2_degree_structural_collapse : ComplexCSP.PaperStatements.paper_1_2_degree_structural_collapse :=
  @ComplexCSP.degree_structural_collapse

/-- Paper 1.2; `ComplexCSP.degreeCaiChenConditions_one_iff`. -/
theorem paper_1_2_degreeCaiChenConditions_one_iff : ComplexCSP.PaperStatements.paper_1_2_degreeCaiChenConditions_one_iff :=
  @ComplexCSP.degreeCaiChenConditions_one_iff

/-- Paper 1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeJointBO`. -/
theorem paper_1_2_hard_of_not_degreeJointBO : ComplexCSP.PaperStatements.paper_1_2_hard_of_not_degreeJointBO :=
  @ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeJointBO

/-- Paper 1.2; `ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeConditions`. -/
theorem paper_1_2_hard_of_not_degreeConditions : ComplexCSP.PaperStatements.paper_1_2_hard_of_not_degreeConditions :=
  @ComplexCSP.ComplexityDegreeHardness.hard_of_not_degreeConditions

/-- Paper 1.2; `ComplexCSP.ComplexityPositiveFP.degreeConditions_inFP`. -/
theorem paper_1_2_degreeConditions_inFP : ComplexCSP.PaperStatements.paper_1_2_degreeConditions_inFP :=
  @ComplexCSP.ComplexityPositiveFP.degreeConditions_inFP

/-- Paper 1.2; `ComplexCSP.ComplexityClassification.degree_conditions`. -/
theorem paper_1_2_degree_conditions : ComplexCSP.PaperStatements.paper_1_2_degree_conditions :=
  @ComplexCSP.ComplexityClassification.degree_conditions

/-- Paper 1.2; `ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity`. -/
theorem paper_1_2_encodedDegreeGlobalTest_complexity : ComplexCSP.PaperStatements.paper_1_2_encodedDegreeGlobalTest_complexity :=
  @ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity

/-- Paper 3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_agreement`. -/
theorem paper_3_1_table_ambient_agreement.{u_1, u_2} : ComplexCSP.PaperStatements.paper_3_1_table_ambient_agreement.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_agreement.{u_1, u_2}

/-- Paper 3.1; `ComplexCSP.AmbientTableAgreement.disjoint_iff`. -/
theorem paper_3_1_disjoint_iff.{u_1, u_2} : ComplexCSP.PaperStatements.paper_3_1_disjoint_iff.{u_1, u_2} :=
  @ComplexCSP.AmbientTableAgreement.disjoint_iff.{u_1, u_2}

/-- Paper 3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_normalized_ambient_agreement`. -/
theorem paper_3_1_table_normalized_ambient_agreement.{u_1, u_2} : ComplexCSP.PaperStatements.paper_3_1_table_normalized_ambient_agreement.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_normalized_ambient_agreement.{u_1, u_2}

/-- Paper 3.1; `ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_blockOrthogonal_iff`. -/
theorem paper_3_1_table_ambient_blockOrthogonal_iff.{u_1, u_2} : ComplexCSP.PaperStatements.paper_3_1_table_ambient_blockOrthogonal_iff.{u_1, u_2} :=
  @ComplexCSP.GeneratingSet.LegalGeneratingSet.table_ambient_blockOrthogonal_iff.{u_1, u_2}

/-- Paper 3.2; `ComplexCSP.jointBO_iff_singletonBO`. -/
theorem paper_3_2_jointBO_iff_singletonBO : ComplexCSP.PaperStatements.paper_3_2_jointBO_iff_singletonBO :=
  @ComplexCSP.jointBO_iff_singletonBO

/-- Paper 3.3; `ComplexCSP.paper_generated_diagonal_minor`. -/
theorem paper_3_3_paper_generated_diagonal_minor : ComplexCSP.PaperStatements.paper_3_3_paper_generated_diagonal_minor :=
  @ComplexCSP.paper_generated_diagonal_minor

/-- Paper 3.3, 5.1; `ComplexCSP.generated_iff_paperGenerated`. -/
theorem paper_3_3_generated_iff_paperGenerated : ComplexCSP.PaperStatements.paper_3_3_generated_iff_paperGenerated :=
  @ComplexCSP.generated_iff_paperGenerated

/-- Paper 3.4; `ComplexCSP.singletonBO_iff_bounded`. -/
theorem paper_3_4_singletonBO_iff_bounded : ComplexCSP.PaperStatements.paper_3_4_singletonBO_iff_bounded :=
  @ComplexCSP.singletonBO_iff_bounded

/-- Paper 3.4; `ComplexCSP.bounded_external_arity_counterexample`. -/
theorem paper_3_4_bounded_external_arity_counterexample : ComplexCSP.PaperStatements.paper_3_4_bounded_external_arity_counterexample :=
  @ComplexCSP.bounded_external_arity_counterexample

/-- Paper 4.1; `ComplexCSP.Certificates.value_norm_eq_iff_numberFieldRoot`. -/
theorem paper_4_1_value_norm_eq_iff_numberFieldRoot.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_1_value_norm_eq_iff_numberFieldRoot.{u_1, u_2} :=
  @ComplexCSP.Certificates.value_norm_eq_iff_numberFieldRoot.{u_1, u_2}

/-- Paper 4.1; `ComplexCSP.Certificates.entry_norm_products_iff_twisted`. -/
theorem paper_4_1_entry_norm_products_iff_twisted.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_1_entry_norm_products_iff_twisted.{u_1, u_2} :=
  @ComplexCSP.Certificates.entry_norm_products_iff_twisted.{u_1, u_2}

/-- Paper 4.1; `ComplexCSP.Certificates.entry_products_iff_field_products`. -/
theorem paper_4_1_entry_products_iff_field_products.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_1_entry_products_iff_field_products.{u_1, u_2} :=
  @ComplexCSP.Certificates.entry_products_iff_field_products.{u_1, u_2}

/-- Paper 4.1; `ComplexCSP.Certificates.value_root_covariance`. -/
theorem paper_4_1_value_root_covariance.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_1_value_root_covariance.{u_1, u_2} :=
  @ComplexCSP.Certificates.value_root_covariance.{u_1, u_2}

/-- Paper 4.1; `ComplexCSP.Certificates.intrinsicTests_legalTable`. -/
theorem paper_4_1_intrinsicTests_legalTable.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_1_intrinsicTests_legalTable.{u_1, u_2} :=
  @ComplexCSP.Certificates.intrinsicTests_legalTable.{u_1, u_2}

/-- Paper 4.2; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_finite_union`. -/
theorem paper_4_2_legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_2_legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2} :=
  @ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_finite_union.{u_1, u_2}

/-- Paper 4.2; `ComplexCSP.Certificates.certificate_complete`. -/
theorem paper_4_2_certificate_complete.{u_1, u_2, u_3, u_4} : ComplexCSP.PaperStatements.paper_4_2_certificate_complete.{u_1, u_2, u_3, u_4} :=
  @ComplexCSP.Certificates.certificate_complete.{u_1, u_2, u_3, u_4}

/-- Paper 4.2; `ComplexCSP.Certificates.certificate_sound`. -/
theorem paper_4_2_certificate_sound.{u_1, u_2, u_3, u_4} : ComplexCSP.PaperStatements.paper_4_2_certificate_sound.{u_1, u_2, u_3, u_4} :=
  @ComplexCSP.Certificates.certificate_sound.{u_1, u_2, u_3, u_4}

/-- Paper 4.4; `ComplexCSP.finite_union_zeroLocus_iff`. -/
theorem paper_4_4_finite_union_zeroLocus_iff.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_4_4_finite_union_zeroLocus_iff.{u_1, u_2, u_3} :=
  @ComplexCSP.finite_union_zeroLocus_iff.{u_1, u_2, u_3}

/-- Paper 4.4; `ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_product_equations`. -/
theorem paper_4_4_legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2} : ComplexCSP.PaperStatements.paper_4_4_legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2} :=
  @ComplexCSP.Certificates.legal_purified_blockOrthogonal_iff_product_equations.{u_1, u_2}

/-- Paper 4.4; `ComplexCSP.Certificates.allProductPrograms_zero_iff`. -/
theorem paper_4_4_allProductPrograms_zero_iff : ComplexCSP.PaperStatements.paper_4_4_allProductPrograms_zero_iff :=
  @ComplexCSP.Certificates.allProductPrograms_zero_iff

/-- Paper 4.4; `ComplexCSP.Certificates.optimizedProductPrograms_zero_iff`. -/
theorem paper_4_4_optimizedProductPrograms_zero_iff : ComplexCSP.PaperStatements.paper_4_4_optimizedProductPrograms_zero_iff :=
  @ComplexCSP.Certificates.optimizedProductPrograms_zero_iff

/-- Paper 5.1; `ComplexCSP.GeneratedTable.exists_presentation`. -/
theorem paper_5_1_exists_presentation : ComplexCSP.PaperStatements.paper_5_1_exists_presentation :=
  @ComplexCSP.GeneratedTable.exists_presentation

/-- Paper 5.1; `ComplexCSP.GeneratedTable.ofPresentation_mul`. -/
theorem paper_5_1_ofPresentation_mul : ComplexCSP.PaperStatements.paper_5_1_ofPresentation_mul :=
  @ComplexCSP.GeneratedTable.ofPresentation_mul

/-- Paper 5.1; `ComplexCSP.GeneratedTable.forall_iff_presentations`. -/
theorem paper_5_1_forall_iff_presentations : ComplexCSP.PaperStatements.paper_5_1_forall_iff_presentations :=
  @ComplexCSP.GeneratedTable.forall_iff_presentations

/-- Paper 5.1; `ComplexCSP.Instance.partition_glue`. -/
theorem paper_5_1_partition_glue : ComplexCSP.PaperStatements.paper_5_1_partition_glue :=
  @ComplexCSP.Instance.partition_glue

/-- Paper 5.2; `ComplexCSP.Theorem52Counterexample.printed_theorem_5_2_counterexample`. -/
theorem paper_5_2_printed_theorem_5_2_counterexample : ComplexCSP.PaperStatements.paper_5_2_printed_theorem_5_2_counterexample :=
  @ComplexCSP.Theorem52Counterexample.printed_theorem_5_2_counterexample

/-- Paper 5.2; `ComplexCSP.Instance.partition_eq_of_iso_pin_twins`. -/
theorem paper_5_2_partition_eq_of_iso_pin_twins : ComplexCSP.PaperStatements.paper_5_2_partition_eq_of_iso_pin_twins :=
  @ComplexCSP.Instance.partition_eq_of_iso_pin_twins

/-- Paper 5.2; `ComplexCSP.PinnedIsomorphism.all_instance_pinned_iso_iff`. -/
theorem paper_5_2_all_instance_pinned_iso_iff : ComplexCSP.PaperStatements.paper_5_2_all_instance_pinned_iso_iff :=
  @ComplexCSP.PinnedIsomorphism.all_instance_pinned_iso_iff

/-- Paper 5.2; `ComplexCSP.PinnedIsomorphism.pinnedIsoCheck_correct_all_instances`. -/
theorem paper_5_2_pinnedIsoCheck_correct_all_instances : ComplexCSP.PaperStatements.paper_5_2_pinnedIsoCheck_correct_all_instances :=
  @ComplexCSP.PinnedIsomorphism.pinnedIsoCheck_correct_all_instances

/-- Paper 5.3; `ComplexCSP.Instance.partition_tensorConjugate`. -/
theorem paper_5_3_partition_tensorConjugate : ComplexCSP.PaperStatements.paper_5_3_partition_tensorConjugate :=
  @ComplexCSP.Instance.partition_tensorConjugate

/-- Paper 5.3; `ComplexCSP.Instance.partition_tensorConjugate_zero`. -/
theorem paper_5_3_partition_tensorConjugate_zero : ComplexCSP.PaperStatements.paper_5_3_partition_tensorConjugate_zero :=
  @ComplexCSP.Instance.partition_tensorConjugate_zero

/-- Paper 5.3; `ComplexCSP.tensor_realizes_pinnedMonomial`. -/
theorem paper_5_3_tensor_realizes_pinnedMonomial : ComplexCSP.PaperStatements.paper_5_3_tensor_realizes_pinnedMonomial :=
  @ComplexCSP.tensor_realizes_pinnedMonomial

/-- Paper 5.4; `ComplexCSP.ScalarTags.exists_common_rational_tags`. -/
theorem paper_5_4_exists_common_rational_tags.{u_1, u_3, u_4, u_5} : ComplexCSP.PaperStatements.paper_5_4_exists_common_rational_tags.{u_1, u_3, u_4, u_5} :=
  @ComplexCSP.ScalarTags.exists_common_rational_tags.{u_1, u_3, u_4, u_5}

/-- Paper 5.4; `ComplexCSP.ScalarTags.findRationalTags_spec`. -/
theorem paper_5_4_findRationalTags_spec.{u_1, u_3, u_4} : ComplexCSP.PaperStatements.paper_5_4_findRationalTags_spec.{u_1, u_3, u_4} :=
  @ComplexCSP.ScalarTags.findRationalTags_spec.{u_1, u_3, u_4}

/-- Paper 5.4; `ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged_correct`. -/
theorem paper_5_4_comparePaperTagged_correct : ComplexCSP.PaperStatements.paper_5_4_comparePaperTagged_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.comparePaperTagged_correct

/-- Paper 5.5; `ComplexCSP.Recognition.PinnedMonomial.characters_eq_iff_all_tensor_instances`. -/
theorem paper_5_5_characters_eq_iff_all_tensor_instances : ComplexCSP.PaperStatements.paper_5_5_characters_eq_iff_all_tensor_instances :=
  @ComplexCSP.Recognition.PinnedMonomial.characters_eq_iff_all_tensor_instances

/-- Paper 5.5; `ComplexCSP.Recognition.PinnedMonomial.compare_correct`. -/
theorem paper_5_5_compare_correct : ComplexCSP.PaperStatements.paper_5_5_compare_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.compare_correct

/-- Paper 5.5; `ComplexCSP.Recognition.partition_common_tags_iff`. -/
theorem paper_5_5_partition_common_tags_iff : ComplexCSP.PaperStatements.paper_5_5_partition_common_tags_iff :=
  @ComplexCSP.Recognition.partition_common_tags_iff

/-- Paper 5.6; `ComplexCSP.characters_linearIndependent`. -/
theorem paper_5_6_characters_linearIndependent.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_5_6_characters_linearIndependent.{u_1, u_2, u_3} :=
  @ComplexCSP.characters_linearIndependent.{u_1, u_2, u_3}

/-- Paper 5.6; `ComplexCSP.character_coefficients_eq_zero`. -/
theorem paper_5_6_character_coefficients_eq_zero.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_5_6_character_coefficients_eq_zero.{u_1, u_2, u_3} :=
  @ComplexCSP.character_coefficients_eq_zero.{u_1, u_2, u_3}

/-- Paper 5.6; `ComplexCSP.grouped_character_zero_iff`. -/
theorem paper_5_6_grouped_character_zero_iff.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_5_6_grouped_character_zero_iff.{u_1, u_2, u_3} :=
  @ComplexCSP.grouped_character_zero_iff.{u_1, u_2, u_3}

/-- Paper 5.7; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_correct`. -/
theorem paper_5_7_uniformAlgebraicIdentityTest_correct : ComplexCSP.PaperStatements.paper_5_7_uniformAlgebraicIdentityTest_correct :=
  @ComplexCSP.Recognition.uniformAlgebraicIdentityTest_correct

/-- Paper 5.7; `ComplexCSP.Recognition.uniformAlgebraicIdentityTest_rejects_iff`. -/
theorem paper_5_7_uniformAlgebraicIdentityTest_rejects_iff : ComplexCSP.PaperStatements.paper_5_7_uniformAlgebraicIdentityTest_rejects_iff :=
  @ComplexCSP.Recognition.uniformAlgebraicIdentityTest_rejects_iff

/-- Paper 5.7; `ComplexCSP.Recognition.programIdentityTest_mvPolynomial_correct`. -/
theorem paper_5_7_programIdentityTest_mvPolynomial_correct : ComplexCSP.PaperStatements.paper_5_7_programIdentityTest_mvPolynomial_correct :=
  @ComplexCSP.Recognition.programIdentityTest_mvPolynomial_correct

/-- Paper 5.8; `ComplexCSP.Instance.degree_filter_identity`. -/
theorem paper_5_8_degree_filter_identity : ComplexCSP.PaperStatements.paper_5_8_degree_filter_identity :=
  @ComplexCSP.Instance.degree_filter_identity

/-- Paper 5.8; `ComplexCSP.Recognition.PinnedMonomial.filtered_sum_formula`. -/
theorem paper_5_8_filtered_sum_formula : ComplexCSP.PaperStatements.paper_5_8_filtered_sum_formula :=
  @ComplexCSP.Recognition.PinnedMonomial.filtered_sum_formula

/-- Paper 5.8; `ComplexCSP.Recognition.PinnedMonomial.degreeCompare_correct`. -/
theorem paper_5_8_degreeCompare_correct : ComplexCSP.PaperStatements.paper_5_8_degreeCompare_correct :=
  @ComplexCSP.Recognition.PinnedMonomial.degreeCompare_correct

/-- Paper 5.9; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_correct`. -/
theorem paper_5_9_uniformAlgebraicDegreeIdentityTest_correct : ComplexCSP.PaperStatements.paper_5_9_uniformAlgebraicDegreeIdentityTest_correct :=
  @ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_correct

/-- Paper 5.9; `ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_rejects_iff`. -/
theorem paper_5_9_uniformAlgebraicDegreeIdentityTest_rejects_iff : ComplexCSP.PaperStatements.paper_5_9_uniformAlgebraicDegreeIdentityTest_rejects_iff :=
  @ComplexCSP.Recognition.uniformAlgebraicDegreeIdentityTest_rejects_iff

/-- Paper 6.2; `ComplexCSP.Recognition.globalCertificateTest_exponent_correct_jointBO`. -/
theorem paper_6_2_globalCertificateTest_exponent_correct_jointBO : ComplexCSP.PaperStatements.paper_6_2_globalCertificateTest_exponent_correct_jointBO :=
  @ComplexCSP.Recognition.globalCertificateTest_exponent_correct_jointBO

/-- Paper 6.2; `ComplexCSP.Recognition.uniformAlgebraicGlobalTest_correct_jointBO`. -/
theorem paper_6_2_uniformAlgebraicGlobalTest_correct_jointBO : ComplexCSP.PaperStatements.paper_6_2_uniformAlgebraicGlobalTest_correct_jointBO :=
  @ComplexCSP.Recognition.uniformAlgebraicGlobalTest_correct_jointBO

/-- Paper 7.1; `ComplexCSP.infinite_simultaneous_multiset_powerSum_ne_zero`. -/
theorem paper_7_1_infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2} : ComplexCSP.PaperStatements.paper_7_1_infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2} :=
  @ComplexCSP.infinite_simultaneous_multiset_powerSum_ne_zero.{u_1, u_2}

/-- Paper 7.1; `ComplexCSP.exists_simultaneous_powerSum_ne_zero_bounded`. -/
theorem paper_7_1_exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_7_1_exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3} :=
  @ComplexCSP.exists_simultaneous_powerSum_ne_zero_bounded.{u_1, u_2, u_3}

/-- Paper 7.1; `ComplexCSP.findSimultaneousPower_success`. -/
theorem paper_7_1_findSimultaneousPower_success.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_7_1_findSimultaneousPower_success.{u_1, u_2, u_3} :=
  @ComplexCSP.findSimultaneousPower_success.{u_1, u_2, u_3}

/-- Paper 7.1; `ComplexCSP.findSimultaneousPower_sound`. -/
theorem paper_7_1_findSimultaneousPower_sound.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_7_1_findSimultaneousPower_sound.{u_1, u_2, u_3} :=
  @ComplexCSP.findSimultaneousPower_sound.{u_1, u_2, u_3}

/-- Paper 7.2; `ComplexCSP.paper_generated_equalityfree_pp_support`. -/
theorem paper_7_2_paper_generated_equalityfree_pp_support : ComplexCSP.PaperStatements.paper_7_2_paper_generated_equalityfree_pp_support :=
  @ComplexCSP.paper_generated_equalityfree_pp_support

/-- Paper 7.2; `ComplexCSP.PresentedAtom.compile_correct`. -/
theorem paper_7_2_compile_correct : ComplexCSP.PaperStatements.paper_7_2_compile_correct :=
  @ComplexCSP.PresentedAtom.compile_correct

/-- Paper 7.2; `ComplexCSP.findSupportPower_spec`. -/
theorem paper_7_2_findSupportPower_spec : ComplexCSP.PaperStatements.paper_7_2_findSupportPower_spec :=
  @ComplexCSP.findSupportPower_spec

/-- Paper 7.3, 7.4, 8.2; `ComplexCSP.JointBO.original`. -/
theorem paper_7_3_original : ComplexCSP.PaperStatements.paper_7_3_original :=
  @ComplexCSP.JointBO.original

/-- Paper 7.3, 7.4; `ComplexCSP.allGeneratedOriginalBO_supportRectangular`. -/
theorem paper_7_3_allGeneratedOriginalBO_supportRectangular : ComplexCSP.PaperStatements.paper_7_3_allGeneratedOriginalBO_supportRectangular :=
  @ComplexCSP.allGeneratedOriginalBO_supportRectangular

/-- Paper 7.3, 7.4; `ComplexCSP.generated_supports_equalityfree_rectangularity`. -/
theorem paper_7_3_generated_supports_equalityfree_rectangularity : ComplexCSP.PaperStatements.paper_7_3_generated_supports_equalityfree_rectangularity :=
  @ComplexCSP.generated_supports_equalityfree_rectangularity

/-- Paper 7.3; `ComplexCSP.MaltsevRelations.rectangular_iff_equal_or_disjoint`. -/
theorem paper_7_3_rectangular_iff_equal_or_disjoint.{u, v} : ComplexCSP.PaperStatements.paper_7_3_rectangular_iff_equal_or_disjoint.{u, v} :=
  @ComplexCSP.MaltsevRelations.rectangular_iff_equal_or_disjoint.{u, v}

/-- Paper 7.4; `ComplexCSP.MaltsevRelations.finite_family_maltsev`. -/
theorem paper_7_4_finite_family_maltsev.{u} : ComplexCSP.PaperStatements.paper_7_4_finite_family_maltsev.{u} :=
  @ComplexCSP.MaltsevRelations.finite_family_maltsev.{u}

/-- Paper 7.5; `ComplexCSP.JointBO.common_support_maltsev`. -/
theorem paper_7_5_common_support_maltsev : ComplexCSP.PaperStatements.paper_7_5_common_support_maltsev :=
  @ComplexCSP.JointBO.common_support_maltsev

/-- Paper 7.5; `ComplexCSP.MaltsevRelations.common_maltsev_of_finite_subfamilies`. -/
theorem paper_7_5_common_maltsev_of_finite_subfamilies.{u} : ComplexCSP.PaperStatements.paper_7_5_common_maltsev_of_finite_subfamilies.{u} :=
  @ComplexCSP.MaltsevRelations.common_maltsev_of_finite_subfamilies.{u}

/-- Paper 7.5; `ComplexCSP.common_maltsev_of_generated_support_rectangularity`. -/
theorem paper_7_5_common_maltsev_of_generated_support_rectangularity : ComplexCSP.PaperStatements.paper_7_5_common_maltsev_of_generated_support_rectangularity :=
  @ComplexCSP.common_maltsev_of_generated_support_rectangularity

/-- Paper 8.1; `ComplexCSP.paper_generated_pow`. -/
theorem paper_8_1_paper_generated_pow : ComplexCSP.PaperStatements.paper_8_1_paper_generated_pow :=
  @ComplexCSP.paper_generated_pow

/-- Paper 8.1; `ComplexCSP.Presentation.table_power`. -/
theorem paper_8_1_table_power : ComplexCSP.PaperStatements.paper_8_1_table_power :=
  @ComplexCSP.Presentation.table_power

/-- Paper 8.2; `ComplexCSP.BlockOrthogonality.finite_row_phases_of_power_BO`. -/
theorem paper_8_2_finite_row_phases_of_power_BO.{u, v} : ComplexCSP.PaperStatements.paper_8_2_finite_row_phases_of_power_BO.{u, v} :=
  @ComplexCSP.BlockOrthogonality.finite_row_phases_of_power_BO.{u, v}

/-- Paper 8.2; `ComplexCSP.Instance.generated_pow`. -/
theorem paper_8_2_generated_pow : ComplexCSP.PaperStatements.paper_8_2_generated_pow :=
  @ComplexCSP.Instance.generated_pow

/-- Paper 8.2; `ComplexCSP.Instance.generated_mem_workingField`. -/
theorem paper_8_2_generated_mem_workingField : ComplexCSP.PaperStatements.paper_8_2_generated_mem_workingField :=
  @ComplexCSP.Instance.generated_mem_workingField

/-- Paper 8.3; `ComplexCSP.lemma_8_3`. -/
theorem paper_8_3_lemma_8_3 : ComplexCSP.PaperStatements.paper_8_3_lemma_8_3 :=
  @ComplexCSP.lemma_8_3

/-- Paper 8.3; `ComplexCSP.finite_weightedPowerSum_zeros_algebraic`. -/
theorem paper_8_3_finite_weightedPowerSum_zeros_algebraic : ComplexCSP.PaperStatements.paper_8_3_finite_weightedPowerSum_zeros_algebraic :=
  @ComplexCSP.finite_weightedPowerSum_zeros_algebraic

/-- Paper 8.4; `ComplexCSP.RowEquivalenceRealization.generated_row_equivalence_detector`. -/
theorem paper_8_4_generated_row_equivalence_detector : ComplexCSP.PaperStatements.paper_8_4_generated_row_equivalence_detector :=
  @ComplexCSP.RowEquivalenceRealization.generated_row_equivalence_detector

/-- Paper 8.4; `ComplexCSP.RowEquivalenceRealization.exists_detector_support`. -/
theorem paper_8_4_exists_detector_support.{u, v} : ComplexCSP.PaperStatements.paper_8_4_exists_detector_support.{u, v} :=
  @ComplexCSP.RowEquivalenceRealization.exists_detector_support.{u, v}

/-- Paper 8.4; `ComplexCSP.paper_generated_rowDetector`. -/
theorem paper_8_4_paper_generated_rowDetector : ComplexCSP.PaperStatements.paper_8_4_paper_generated_rowDetector :=
  @ComplexCSP.paper_generated_rowDetector

/-- Paper 8.4; `ComplexCSP.RowDetector.findDetectorTime_success`. -/
theorem paper_8_4_findDetectorTime_success.{u_1, u_2, u_3} : ComplexCSP.PaperStatements.paper_8_4_findDetectorTime_success.{u_1, u_2, u_3} :=
  @ComplexCSP.RowDetector.findDetectorTime_success.{u_1, u_2, u_3}

/-- Paper 8.4; `ComplexCSP.RowDetector.fieldExponent_killsTorsion`. -/
theorem paper_8_4_fieldExponent_killsTorsion.{u_1} : ComplexCSP.PaperStatements.paper_8_4_fieldExponent_killsTorsion.{u_1} :=
  @ComplexCSP.RowDetector.fieldExponent_killsTorsion.{u_1}

/-- Paper 8.4; `ComplexCSP.RowDetectorEmbeddedExistence.generated_detector_exact_workingField`. -/
theorem paper_8_4_generated_detector_exact_workingField : ComplexCSP.PaperStatements.paper_8_4_generated_detector_exact_workingField :=
  @ComplexCSP.RowDetectorEmbeddedExistence.generated_detector_exact_workingField

/-- Paper 8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_support`. -/
theorem paper_8_4_validatedRowDetector_support : ComplexCSP.PaperStatements.paper_8_4_validatedRowDetector_support :=
  @ComplexCSP.EncodedNumberField.validatedRowDetector_support

/-- Paper 8.4; `ComplexCSP.EncodedNumberField.validatedRowDetector_exact_formula`. -/
theorem paper_8_4_validatedRowDetector_exact_formula : ComplexCSP.PaperStatements.paper_8_4_validatedRowDetector_exact_formula :=
  @ComplexCSP.EncodedNumberField.validatedRowDetector_exact_formula

/-- Paper 8.4; `ComplexCSP.EffectiveRoots.torsion_exponent_eq_order`. -/
theorem paper_8_4_torsion_exponent_eq_order.{u_1} : ComplexCSP.PaperStatements.paper_8_4_torsion_exponent_eq_order.{u_1} :=
  @ComplexCSP.EffectiveRoots.torsion_exponent_eq_order.{u_1}

/-- Paper 8.4; `ComplexCSP.EffectiveRoots.checkedRootExponent_eq_fieldExponent`. -/
theorem paper_8_4_checkedRootExponent_eq_fieldExponent : ComplexCSP.PaperStatements.paper_8_4_checkedRootExponent_eq_fieldExponent :=
  @ComplexCSP.EffectiveRoots.checkedRootExponent_eq_fieldExponent

/-- Paper 8.4; `ComplexCSP.uniformAlgebraicRowDetector_support`. -/
theorem paper_8_4_uniformAlgebraicRowDetector_support : ComplexCSP.PaperStatements.paper_8_4_uniformAlgebraicRowDetector_support :=
  @ComplexCSP.uniformAlgebraicRowDetector_support

/-- Paper 8.4; `ComplexCSP.uniformAlgebraicRowDetector_exponent`. -/
theorem paper_8_4_uniformAlgebraicRowDetector_exponent : ComplexCSP.PaperStatements.paper_8_4_uniformAlgebraicRowDetector_exponent :=
  @ComplexCSP.uniformAlgebraicRowDetector_exponent

/-- Paper 8.4; `ComplexCSP.uniformAlgebraicRowDetector_exact_formula`. -/
theorem paper_8_4_uniformAlgebraicRowDetector_exact_formula : ComplexCSP.PaperStatements.paper_8_4_uniformAlgebraicRowDetector_exact_formula :=
  @ComplexCSP.uniformAlgebraicRowDetector_exact_formula

/-- Paper 8.4; `ComplexCSP.Recognition.identityPairedCandidate_fieldRange`. -/
theorem paper_8_4_identityPairedCandidate_fieldRange : ComplexCSP.PaperStatements.paper_8_4_identityPairedCandidate_fieldRange :=
  @ComplexCSP.Recognition.identityPairedCandidate_fieldRange

/-- Paper 8.4; `ComplexCSP.Recognition.identityPairedCandidate_rootExponent_eq`. -/
theorem paper_8_4_identityPairedCandidate_rootExponent_eq : ComplexCSP.PaperStatements.paper_8_4_identityPairedCandidate_rootExponent_eq :=
  @ComplexCSP.Recognition.identityPairedCandidate_rootExponent_eq

/-- Paper 8.5; `ComplexCSP.RowEquivalenceRealization.omega_mem_generatedSupports`. -/
theorem paper_8_5_omega_mem_generatedSupports : ComplexCSP.PaperStatements.paper_8_5_omega_mem_generatedSupports :=
  @ComplexCSP.RowEquivalenceRealization.omega_mem_generatedSupports

/-- Paper 9.1; `ComplexCSP.RowTypes.complex_type_partition`. -/
theorem paper_9_1_complex_type_partition.{u} : ComplexCSP.PaperStatements.paper_9_1_complex_type_partition.{u} :=
  @ComplexCSP.RowTypes.complex_type_partition.{u}

/-- Paper 9.1; `ComplexCSP.RowTypes.rowEquivalence_iff`. -/
theorem paper_9_1_rowEquivalence_iff.{u, v, w, u_1} : ComplexCSP.PaperStatements.paper_9_1_rowEquivalence_iff.{u, v, w, u_1} :=
  @ComplexCSP.RowTypes.rowEquivalence_iff.{u, v, w, u_1}

/-- Paper 9.1; `ComplexCSP.RowTypes.preserves_omega_pairs`. -/
theorem paper_9_1_preserves_omega_pairs.{u} : ComplexCSP.PaperStatements.paper_9_1_preserves_omega_pairs.{u} :=
  @ComplexCSP.RowTypes.preserves_omega_pairs.{u}

/-- Paper 9.2; `ComplexCSP.JointBO.global_type_partition`. -/
theorem paper_9_2_global_type_partition : ComplexCSP.PaperStatements.paper_9_2_global_type_partition :=
  @ComplexCSP.JointBO.global_type_partition

/-- Paper 9.2; `ComplexCSP.JointBO.global_maltsev`. -/
theorem paper_9_2_global_maltsev : ComplexCSP.PaperStatements.paper_9_2_global_maltsev :=
  @ComplexCSP.JointBO.global_maltsev

/-- Paper 9.2; `ComplexCSP.RowEquivalenceRealization.common_support_and_row_maltsev`. -/
theorem paper_9_2_common_support_and_row_maltsev : ComplexCSP.PaperStatements.paper_9_2_common_support_and_row_maltsev :=
  @ComplexCSP.RowEquivalenceRealization.common_support_and_row_maltsev

/-- Paper 5.2; `ComplexCSP.PaperBridge.theorem_5_2_complex_counterexample`. -/
theorem paper_5_2_theorem_5_2_complex_counterexample : ComplexCSP.PaperStatements.paper_5_2_theorem_5_2_complex_counterexample :=
  @ComplexCSP.PaperBridge.theorem_5_2_complex_counterexample

/-- Paper 1.1, 1.2; `ComplexCSP.PaperBridge.workingField_realization`. -/
theorem paper_1_1_workingField_realization : ComplexCSP.PaperStatements.paper_1_1_workingField_realization :=
  @ComplexCSP.PaperBridge.workingField_realization

/-- Paper 7.3; `ComplexCSP.PaperBridge.lemma_7_3_pp_rectangularity`. -/
theorem paper_7_3_lemma_7_3_pp_rectangularity : ComplexCSP.PaperStatements.paper_7_3_lemma_7_3_pp_rectangularity :=
  @ComplexCSP.PaperBridge.lemma_7_3_pp_rectangularity

/-- Paper 7.4; `ComplexCSP.PaperBridge.lemma_7_4`. -/
theorem paper_7_4_lemma_7_4 : ComplexCSP.PaperStatements.paper_7_4_lemma_7_4 :=
  @ComplexCSP.PaperBridge.lemma_7_4

/-- Paper 8.2; `ComplexCSP.PaperBridge.lemma_8_2`. -/
theorem paper_8_2_lemma_8_2 : ComplexCSP.PaperStatements.paper_8_2_lemma_8_2 :=
  @ComplexCSP.PaperBridge.lemma_8_2

/-- Paper 8.5; `ComplexCSP.PaperBridge.lemma_8_5`. -/
theorem paper_8_5_lemma_8_5 : ComplexCSP.PaperStatements.paper_8_5_lemma_8_5 :=
  @ComplexCSP.PaperBridge.lemma_8_5

/-- Paper 4.1; `ComplexCSP.PaperBridge.normalization_norm_iff`. -/
theorem paper_4_1_normalization_norm_iff : ComplexCSP.PaperStatements.paper_4_1_normalization_norm_iff :=
  @ComplexCSP.PaperBridge.normalization_norm_iff

/-- Paper 4.1; `ComplexCSP.PaperBridge.normalization_products_iff`. -/
theorem paper_4_1_normalization_products_iff : ComplexCSP.PaperStatements.paper_4_1_normalization_products_iff :=
  @ComplexCSP.PaperBridge.normalization_products_iff

/-- Paper 4.1; `ComplexCSP.PaperBridge.normalization_norm_products_iff`. -/
theorem paper_4_1_normalization_norm_products_iff : ComplexCSP.PaperStatements.paper_4_1_normalization_norm_products_iff :=
  @ComplexCSP.PaperBridge.normalization_norm_products_iff

/-- Paper 4.1; `ComplexCSP.PaperBridge.normalization_covariance_iff`. -/
theorem paper_4_1_normalization_covariance_iff : ComplexCSP.PaperStatements.paper_4_1_normalization_covariance_iff :=
  @ComplexCSP.PaperBridge.normalization_covariance_iff

/-- Paper 1.1; `ComplexCSP.ComplexityClassification.ordinary_conditions`. -/
theorem paper_1_1_ordinary_conditions : ComplexCSP.PaperStatements.paper_1_1_ordinary_conditions :=
  @ComplexCSP.ComplexityClassification.ordinary_conditions

/-- Paper 1.1; `ComplexCSP.Recognition.encodedGlobalTest_complexity`. -/
theorem paper_1_1_encodedGlobalTest_complexity : ComplexCSP.PaperStatements.paper_1_1_encodedGlobalTest_complexity :=
  @ComplexCSP.Recognition.encodedGlobalTest_complexity

/-- Paper 5.2; `ComplexCSP.PinnedIsomorphism.all_instance_completeness`. -/
theorem paper_5_2_all_instance_completeness : ComplexCSP.PaperStatements.paper_5_2_all_instance_completeness :=
  @ComplexCSP.PinnedIsomorphism.all_instance_completeness

/-- Paper 5.2; `ComplexCSP.Theorem52Counterexample.doubledUnary_first_value`. -/
theorem paper_5_2_doubledUnary_first_value : ComplexCSP.PaperStatements.paper_5_2_doubledUnary_first_value :=
  @ComplexCSP.Theorem52Counterexample.doubledUnary_first_value

/-- Paper 5.2; `ComplexCSP.Theorem52Counterexample.doubledUnary_second_value`. -/
theorem paper_5_2_doubledUnary_second_value : ComplexCSP.PaperStatements.paper_5_2_doubledUnary_second_value :=
  @ComplexCSP.Theorem52Counterexample.doubledUnary_second_value

/-- Paper 5.2; `ComplexCSP.Theorem52Counterexample.paperSimple_iff_simple`. -/
theorem paper_5_2_paperSimple_iff_simple : ComplexCSP.PaperStatements.paper_5_2_paperSimple_iff_simple :=
  @ComplexCSP.Theorem52Counterexample.paperSimple_iff_simple

/-- Paper 1.1; `ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode`. -/
theorem paper_1_1_finiteAlgebraicLanguage_decode_encode : ComplexCSP.PaperStatements.paper_1_1_finiteAlgebraicLanguage_decode_encode :=
  @ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode

end ComplexCSP.PaperSpec

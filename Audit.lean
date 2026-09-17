import NoncompactOrbit
import ReducedBasisBounds
import MahlerCompactness
import MahlerPotential
import MahlerBasisChanges
import MahlerGram
import MahlerSizeReduction
import MahlerDualGram
import MahlerBoundedBasis
import FinalTheorem
import PrincipalRepresentation
import PrincipalFixed
import PrincipalFlag
import PrincipalCurves
import PrincipalDescent
import PrincipalSection
import NormalizerCoordinates
import PrincipalClosure
import MargulisLemma5
import MinimalCollision
import LatticeCollision
import MinimalSubsystem
import OrbitQuotientTopology
import UnipotentOneNormalizer
import CompactGroupQuotient
import CompactHOrbit
import AffineSubgroup
import AffineTranslations
import AffineClassification
import AffineMatrixBridge
import PositiveNormalizerQuotient
import DiagonalInvariance
import CollisionInvariant
import MargulisTheorem2
import IrrationalIntegerStabilizer
import NoncompactTernaryStabilizer
import StandardizedQuotient
import TernaryForm
import Quantifiers
import PositiveWitness
import StandardForm
import FormStabilizer
import UnipotentGroups
import SmallVectors
import LatticeSpace
import MinimalInvariant
import CompactRepresentatives
import CompactLattices
import CompactStabilizers
import DiagonalContraction
import UpperUnipotentCompact
import ShearLemma6C
import ShearFixedSpace
import ConnectedCompactLimits
import ShearCurves
import ShearFixedRays
import ShearNormalization
import ShearLemma6B2
import MargulisLemma6
import UpperDiagonalEscape
import MargulisLemma7
import MinimalHitting

#print axioms JSP400.ternaryForm_indefinite
#print axioms JSP400.ternaryForm_nondegenerate
#print axioms JSP400.ternaryForm_not_proportionalToRational
#print axioms JSP400.dual_statement_iff
#print axioms JSP400.approximation_large_denominator
#print axioms JSP400.small_values_iff_approximation
#print axioms JSP400.standardForm_standardizingSL
#print axioms JSP400.standardizingSL_conjugates
#print axioms JSP400.unipotentOne_add
#print axioms JSP400.unipotentTwo_add
#print axioms JSP400.unipotentOne_commute_unipotentTwo
#print axioms JSP400.unipotentOne_mem_standardStabilizer
#print axioms JSP400.unipotentTwo_mem_standardStabilizer_iff
#print axioms JSP400.diagonalFlow_mem_standardStabilizer
#print axioms JSP400.diagonalFlow_unipotentOne
#print axioms JSP400.diagonalFlow_unipotentTwo
#print axioms JSP400.ternaryForm_abs_le_norm
#print axioms JSP400.ternaryForm_integer_ne_zero
#print axioms JSP400.small_values_of_short_vectors
#print axioms JSP400.integerGamma_isClosed
#print axioms JSP400.quotientLatticePoints_smul
#print axioms JSP400.quotientLatticePoints_injective
#print axioms JSP400.exists_minimal_closed_invariant
#print axioms JSP400.minimal_invariant_orbit_closure
#print axioms JSP400.integerVector_norm_ge_one
#print axioms JSP400.matrix_mulVec_norm_le
#print axioms JSP400.compact_representatives_lower_bound
#print axioms JSP400.compact_lift_of_open_quotient
#print axioms JSP400.compact_lattice_representatives
#print axioms JSP400.compact_lattices_lower_bound
#print axioms JSP400.compact_lattice_stabilizers_discrete
#print axioms JSP400.small_stabilizers_escape_compacts
#print axioms JSP400.conjugating_stabilizer_escapes_compacts
#print axioms JSP400.contractingDiagonal_upper_tendsto_one
#print axioms JSP400.upper_stabilizer_trivial_of_compact_diagonal_orbit
#print axioms JSP400.upper_subgroup_stabilizer_inf_eq_bot
#print axioms JSP400.upper_subgroup_not_isCompact
#print axioms JSP400.upper_stabilizer_quotient_not_compact
#print axioms JSP400.shearLevelSet_component_not_isCompact
#print axioms JSP400.shearConjugate_has_continuous_leftInverse
#print axioms JSP400.shearConjugate_isClosedEmbedding
#print axioms JSP400.shearOrbitSlice_component_not_isCompact
#print axioms JSP400.nilpotent_upperTriangular_diag_eq_zero
#print axioms JSP400.margulis_lemma6_C
#print axioms JSP400.matrix3_isNilpotent_iff_cube
#print axioms JSP400.isClosed_nilpotentMatrices
#print axioms JSP400.shear_fixed_iff_mem_lieAlgebra
#print axioms JSP400.shear_lieAlgebra_slice_eq_line
#print axioms JSP400.shearConjugate_isNilpotent
#print axioms JSP400.matrix_smul_isNilpotent
#print axioms JSP400.closure_shear_orbits_nilpotent
#print axioms JSP400.preconnected_compact_limit
#print axioms JSP400.compact_limit_meets_closed
#print axioms JSP400.compact_limit_contains_point
#print axioms JSP400.exists_connected_compact_limit
#print axioms JSP400.compact_subsequence_limit_subset_upperSetLimit
#print axioms JSP400.exists_unbounded_shear_parameter_curve
#print axioms JSP400.exists_unbounded_shear_curve
#print axioms JSP400.noncompact_real_connected_contains_ray
#print axioms JSP400.shear_fixed_line_contains_ray
#print axioms JSP400.continuousAt_shearNormalize
#print axioms JSP400.mem_closure_normalizedShearSet
#print axioms JSP400.normalizedShearSet_properties
#print axioms JSP400.shearConjugate_recover_from_normalization
#print axioms JSP400.isClosed_upperSetLimit
#print axioms JSP400.upperSetLimit_subset_of_eventually_subset_closed
#print axioms JSP400.upperSetLimit_subset_continuous_fiber
#print axioms JSP400.upperSetLimit_contains_limit_point
#print axioms JSP400.unbounded_curve_compact_segment
#print axioms JSP400.upper_limit_connected_witness
#print axioms JSP400.upper_limit_component_not_compact
#print axioms JSP400.compact_connected_boundary_bumping
#print axioms JSP400.compact_connected_set_boundary_bumping
#print axioms JSP400.upper_limit_fixed_component_boundary
#print axioms JSP400.shearFlag_zero
#print axioms JSP400.mem_shearFlag_two
#print axioms JSP400.mem_shearFlag_eight
#print axioms JSP400.shearConjugate_sub_mem_previousFlag
#print axioms JSP400.isClosed_shearFlag
#print axioms JSP400.shearFlag_step_coordinate_invariant
#print axioms JSP400.shearConjugate_comp
#print axioms JSP400.closure_shearOrbitUnion_invariant
#print axioms JSP400.closure_shearOrbitUnion_nilpotent
#print axioms JSP400.upper_limit_shear_slices_previousFlag
#print axioms JSP400.shear_fixed_component_noncompact_of_layer
#print axioms JSP400.margulis_lemma6_B2
#print axioms JSP400.missing_point_local_normalization
#print axioms JSP400.margulis_lemma6_B1
#print axioms JSP400.adjointAction_base_eq_iff_mem_shearGroup
#print axioms JSP400.mem_normalizer_of_adjoint_base_mem_lie
#print axioms JSP400.margulis_lemma6_A2
#print axioms JSP400.nilpotentFrame_intertwines
#print axioms JSP400.continuous_nilpotentSection
#print axioms JSP400.nilpotentSection_conjugates
#print axioms JSP400.nilpotentSection_fixedLine
#print axioms JSP400.fixedLine_closure_lifts_to_shearDoubleOrbit
#print axioms JSP400.closure_shearDoubleOrbit_mul_right
#print axioms JSP400.upperUnipotent_mem_closure_of_fixedLine
#print axioms JSP400.generated_upper_inter_eq_of_half
#print axioms JSP400.margulis_lemma6_A
#print axioms JSP400.margulis_lemma6
#print axioms JSP400.lattice_has_nonzero_last_coordinate
#print axioms JSP400.upper_eliminate_first_coordinates
#print axioms JSP400.diagonal_after_elimination_makes_vector_short
#print axioms JSP400.diagonal_upper_makes_vector_short
#print axioms JSP400.diagonalUpperOrbit_not_relatively_compact
#print axioms JSP400.shear_eliminate_first_coordinates
#print axioms JSP400.margulis_lemma10
#print axioms JSP400.margulis_lemma11
#print axioms JSP400.positiveShearOrbit_not_relatively_compact
#print axioms JSP400.negativeShearOrbit_not_relatively_compact
#print axioms JSP400.isClosed_hittingSet
#print axioms JSP400.normalizer_minimal_hit_subset
#print axioms JSP400.margulis_lemma1
#print axioms JSP400.margulis_lemma2
#print axioms JSP400.margulis_lemma3
#print axioms JSP400.gramShear_coordinates
#print axioms JSP400.gramShear_sub_mem_previousFlag
#print axioms JSP400.mem_gramFlag_two
#print axioms JSP400.gramFixed_of_det_one
#print axioms JSP400.isClosed_gramFlag
#print axioms JSP400.gramShear_has_linear_coordinate
#print axioms JSP400.exists_unbounded_gram_curve
#print axioms JSP400.gram_fixed_component_noncompact_of_layer
#print axioms JSP400.gram_orbit_closure_contains_ray
#print axioms JSP400.gramMatrix_eq_standard_iff
#print axioms JSP400.gramMatrix_eq_iff_mul_inv_mem
#print axioms JSP400.lemma7_fixed_case
#print axioms JSP400.GramSection.triangularFactor_congruence
#print axioms JSP400.GramSection.triangularFactor_det_pos
#print axioms JSP400.GramSection.continuousAt_triangularFactor
#print axioms JSP400.GramSection.isOpen_sectionDomain
#print axioms JSP400.GramSection.continuous_gramSection
#print axioms JSP400.GramSection.gramSection_standardGram
#print axioms JSP400.GramSection.gramMatrix_gramSection
#print axioms JSP400.mem_closure_of_gramMatrix_mem_closure
#print axioms JSP400.margulis_lemma7

#print axioms JSP400.unipotentOne_inv
#print axioms JSP400.unipotentOne_eq_shearElement
#print axioms JSP400.principalUnipotent_eq_inf
#print axioms JSP400.coadjointForm_standard
#print axioms JSP400.principalOrbitMap_eq
#print axioms JSP400.coadjointForm_mul
#print axioms JSP400.principalAction_mul
#print axioms JSP400.continuous_principalAction
#print axioms JSP400.continuous_principalOrbitMap
#print axioms JSP400.principalOrbitMap_eq_base_iff
#print axioms JSP400.principalAction_injective
#print axioms JSP400.principalOrbitMap_eq_iff_inv_mul_mem
#print axioms JSP400.principalBase_skew
#print axioms JSP400.adjoint_coadjoint_skew
#print axioms JSP400.principalOrbitMap_skew
#print axioms JSP400.unipotentOne_matrix_polynomial
#print axioms JSP400.adjointAction_add
#print axioms JSP400.adjointAction_smul
#print axioms JSP400.adjointAction_matrix_one
#print axioms JSP400.conjugate_unipotentOne_of_adjoint_base
#print axioms JSP400.mem_principalNormalizer_of_adjoint_base
#print axioms JSP400.principal_adjoint_fixed_iff
#print axioms JSP400.gramShear_fixed_iff
#print axioms JSP400.coadjointForm_unipotentOne
#print axioms JSP400.mem_principalNormalizer_of_fixed_orbit
#print axioms JSP400.principalCoordinates_add
#print axioms JSP400.principalCoordinates_sub
#print axioms JSP400.principalCoordinates_smul
#print axioms JSP400.mem_principalFlag
#print axioms JSP400.principalFlag_mono
#print axioms JSP400.mem_principalFlag_fourteen
#print axioms JSP400.principalAction_unipotentOne
#print axioms JSP400.principalCoordinates_from_blocks
#print axioms JSP400.principalAction_sub_mem_previousFlag
#print axioms JSP400.principalFlag_four_fixed
#print axioms JSP400.principalFlag_invariant
#print axioms JSP400.principalFlag_step_coordinate
#print axioms JSP400.principalFlag_step_coordinate_invariant
#print axioms JSP400.continuous_principalCoordinate
#print axioms JSP400.isClosed_principalFlag
#print axioms JSP400.principal_adjoint_has_linear_coordinate
#print axioms JSP400.shearCoordinate_abs_le
#print axioms JSP400.exists_unbounded_principal_curve
#print axioms JSP400.principalLayer_inter_fixed
#print axioms JSP400.principalOrbit_mem_flag
#print axioms JSP400.upper_limit_principal_orbits_previousFlag
#print axioms JSP400.principal_fixed_component_noncompact_of_layer
#print axioms JSP400.isOpen_principalSectionDomain
#print axioms JSP400.principalBase_mem_sectionDomain
#print axioms JSP400.continuous_principalFrame
#print axioms JSP400.continuous_principalCorrection
#print axioms JSP400.continuous_principalSection
#print axioms JSP400.principalFrame_base
#print axioms JSP400.principalSection_base
#print axioms JSP400.principalSection_right_coset
#print axioms JSP400.principalOrbitMap_principalSection
#print axioms JSP400.principalOrbitMap_principalSection_of_closure
#print axioms JSP400.adjointAction_sub
#print axioms JSP400.unipotentOne_log_polynomial
#print axioms JSP400.principalNormalizer_adjoint_base
#print axioms JSP400.factor_of_adjoint_base_scaled
#print axioms JSP400.principalNormalizer_factor
#print axioms JSP400.subset_principalOrbitUnion
#print axioms JSP400.closure_principalOrbitUnion_invariant
#print axioms JSP400.principalOrbitUnion_subset_range
#print axioms JSP400.principalSection_mem_doubleOrbit
#print axioms JSP400.principalSection_mem_closure_doubleOrbit
#print axioms JSP400.mem_closure_diff_singleton_of_preconnected_noncompact
#print axioms JSP400.principal_normalizer_enlargement_of_outside_normalizer
#print axioms JSP400.principalDoubleOrbit_mono
#print axioms JSP400.principalNormalizerReturn_mono
#print axioms JSP400.subset_principalDoubleOrbit
#print axioms JSP400.principalNormalizerReturn_subset_enlargementGroup
#print axioms JSP400.principalUnipotent_le_enlargementGroup
#print axioms JSP400.margulis_lemma5_II_alternative
#print axioms JSP400.compact_stabilizer_quotient_of_local_cover
#print axioms JSP400.margulis_lemma4_of_open_orbit
#print axioms JSP400.isOpenMap_latticeOrbit
#print axioms JSP400.exists_compact_minimal_subgroup
#print axioms JSP400.subgroupInvariant_orbit_closure
#print axioms JSP400.exists_minimal_subsystem_of_compact_orbit_closure
#print axioms JSP400.isCompact_orbit_of_compact_stabilizer_quotient
#print axioms JSP400.mem_orbit_of_no_transverse_returns
#print axioms JSP400.principalUnipotent_le_standardStabilizer
#print axioms JSP400.unipotentTwo_conjugates_one
#print axioms JSP400.unipotentTwo_mem_principalNormalizer
#print axioms JSP400.diagonalFlow_conjugates_one
#print axioms JSP400.diagonalFlow_mem_principalNormalizer
#print axioms JSP400.compactSpace_of_compact_subgroup_quotient
#print axioms JSP400.compact_quotient_of_surjective_hom
#print axioms JSP400.compact_stabilizer_quotient_smul
#print axioms JSP400.lemma7Hull_subset_hitting
#print axioms JSP400.no_transverse_returns_of_diagonal_minimal
#print axioms JSP400.standardStabilizer_isClosed
#print axioms JSP400.compact_H_orbit_of_diagonal_minimal
#print axioms JSP400.compact_H_stabilizer_quotient_of_diagonal_minimal
#print axioms JSP400.AffineClassification.ext
#print axioms JSP400.AffineClassification.continuous_slope
#print axioms JSP400.AffineClassification.continuous_offset
#print axioms JSP400.AffineClassification.translation_zero
#print axioms JSP400.AffineClassification.translation_add
#print axioms JSP400.AffineClassification.translation_neg
#print axioms JSP400.AffineClassification.continuous_translation
#print axioms JSP400.AffineClassification.isClosed_translations
#print axioms JSP400.AffineClassification.conjugate_translation
#print axioms JSP400.AffineClassification.commutator_translation
#print axioms JSP400.AffineClassification.closed_addSubgroup_eq_top_of_zero_accumulation
#print axioms JSP400.AffineClassification.closed_addSubgroup_eq_top_of_contraction
#print axioms JSP400.AffineClassification.all_translations_of_nontrivial_translation_and_slope
#print axioms JSP400.AffineClassification.eq_translation_of_slope_one
#print axioms JSP400.AffineClassification.eq_one_of_slope_offset
#print axioms JSP400.AffineClassification.all_translations_of_only_translations
#print axioms JSP400.AffineClassification.fixedDilationExp_zero
#print axioms JSP400.AffineClassification.fixedDilationExp_add
#print axioms JSP400.AffineClassification.fixedDilationExp_neg
#print axioms JSP400.AffineClassification.continuous_fixedDilationExp
#print axioms JSP400.AffineClassification.isClosed_fixedDilationTimes
#print axioms JSP400.AffineClassification.all_fixedDilations_of_common_fixed_point
#print axioms JSP400.AffineClassification.nondiscrete_closed_affine_subgroup
#print axioms JSP400.diagonalFlow_mul
#print axioms JSP400.affineMatrix_one
#print axioms JSP400.affineMatrix_mul
#print axioms JSP400.continuous_affineMatrix
#print axioms JSP400.affineMatrix_translation
#print axioms JSP400.affineMatrix_fixedDilation
#print axioms JSP400.affineMatrix_coordinates
#print axioms JSP400.continuous_SLentry
#print axioms JSP400.isOpen_positiveMatrixDomain
#print axioms JSP400.one_mem_positiveMatrixDomain
#print axioms JSP400.continuous_positiveMatrixAffine
#print axioms JSP400.positiveMatrixAffine_one
#print axioms JSP400.positiveNormalizer_factor
#print axioms JSP400.affine_comap_nondiscrete
#print axioms JSP400.closed_matrix_subgroup_affine_alternative
#print axioms JSP400.diagonal_translation_commutator
#print axioms JSP400.compact_standard_invariant_no_signed_ray
#print axioms JSP400.diagonal_invariant_of_subgroup_alternative
#print axioms JSP400.preservingSubgroup_isClosed
#print axioms JSP400.mem_preservingSubgroup_of_image_eq
#print axioms JSP400.principalDoubleOrbit_eq_mixedDoubleSet
#print axioms JSP400.principalEnlargementGroup_invariant
#print axioms JSP400.principalUnipotent_isClosed
#print axioms JSP400.principalUnipotent_ne_bot
#print axioms JSP400.principalUnipotent_upper
#print axioms JSP400.compact_principal_minimal_diagonal_invariant
#print axioms JSP400.margulis_theorem2_quotient
#print axioms JSP400.integer_coefficients_of_irrational_relation
#print axioms JSP400.integral_column_separation
#print axioms JSP400.integral_stabilizer_entry_bound
#print axioms JSP400.irrational_integer_stabilizer_matrix_norm_le
#print axioms JSP400.continuous_ternaryForm
#print axioms JSP400.ternaryStabilizer_isClosed
#print axioms JSP400.irrational_integer_stabilizer_isCompact
#print axioms JSP400.standardStabilizer_not_isCompact
#print axioms JSP400.ternaryStabilizer_not_isCompact
#print axioms JSP400.irrational_ternary_stabilizer_quotient_not_compact
#print axioms JSP400.continuous_standardToTernaryHom
#print axioms JSP400.standardToTernaryHom_surjective
#print axioms JSP400.standardToTernaryHom_stabilizer
#print axioms JSP400.standardized_stabilizer_quotient_not_compact

#print axioms JSP400.standardized_orbit_not_relatively_compact
#print axioms JSP400.irrational_ternary_orbit_not_relatively_compact
#print axioms JSP400.reduced_gram_lengths_sq_bound
#print axioms JSP400.reduced_gram_lengths_bound
#print axioms JSP400.reduced_qr_columns_bound
#print axioms JSP400.integerVector_eq_zero_iff
#print axioms JSP400.smul_integerVector_ne_zero
#print axioms JSP400.compact_closure_latticesWithLowerBound
#print axioms JSP400.short_vector_of_noncompact_family
#print axioms JSP400.short_vectors_of_bounded_representatives
#print axioms JSP400.Mahler.energy_nonneg
#print axioms JSP400.Mahler.energy_pos
#print axioms JSP400.Mahler.coordinate_sq_le_energy
#print axioms JSP400.Mahler.norm_le_sqrt_energy
#print axioms JSP400.Mahler.integerVector_norm
#print axioms JSP400.Mahler.finite_integer_energy_sublevel
#print axioms JSP400.Mahler.integer_energy_lower_bound
#print axioms JSP400.Mahler.firstColumn_mul
#print axioms JSP400.Mahler.lastInverseRow_mul
#print axioms JSP400.Mahler.integerFlag_nonzero
#print axioms JSP400.Mahler.potential_mul_eq_flag
#print axioms JSP400.Mahler.exists_minimum_potential
#print axioms JSP400.Mahler.exists_reduced_potential
#print axioms JSP400.Mahler.columnShear_inv
#print axioms JSP400.Mahler.firstColumn_columnShear
#print axioms JSP400.Mahler.lastInverseRow_columnShear
#print axioms JSP400.Mahler.potential_columnShear
#print axioms JSP400.Mahler.IsPotentialMinimum.shear_minimum
#print axioms JSP400.Mahler.swapFirst_inv
#print axioms JSP400.Mahler.swapLast_inv
#print axioms JSP400.Mahler.potential_swapFirst
#print axioms JSP400.Mahler.energy_neg
#print axioms JSP400.Mahler.potential_swapLast
#print axioms JSP400.Mahler.column_ne_zero
#print axioms JSP400.Mahler.inverseRow_ne_zero
#print axioms JSP400.Mahler.IsPotentialMinimum.first_length
#print axioms JSP400.Mahler.IsPotentialMinimum.second_area
#print axioms JSP400.Mahler.inner3_self
#print axioms JSP400.Mahler.inner3_comm
#print axioms JSP400.Mahler.inner3_sub_right
#print axioms JSP400.Mahler.inner3_smul_right
#print axioms JSP400.Mahler.energy_add
#print axioms JSP400.Mahler.energy_smul
#print axioms JSP400.Mahler.energy_zero
#print axioms JSP400.Mahler.volume3_qr
#print axioms JSP400.Mahler.volume3_second_reduce
#print axioms JSP400.Mahler.volume3_columns
#print axioms JSP400.Mahler.volume3_gram
#print axioms JSP400.Mahler.gramOne_energy_pos
#print axioms JSP400.Mahler.gram_volume
#print axioms JSP400.Mahler.gramTwo_energy_pos
#print axioms JSP400.Mahler.gramThree_energy_pos
#print axioms JSP400.Mahler.gram_one_two_orthogonal
#print axioms JSP400.Mahler.gram_one_three_orthogonal
#print axioms JSP400.Mahler.gram_two_three_orthogonal
#print axioms JSP400.Mahler.gram_energy_product
#print axioms JSP400.Mahler.column_one_qr
#print axioms JSP400.Mahler.column_two_qr
#print axioms JSP400.Mahler.energy_column_one
#print axioms JSP400.Mahler.inner3_add_right
#print axioms JSP400.Mahler.columnShear_column_zero
#print axioms JSP400.Mahler.columnShear_column_one
#print axioms JSP400.Mahler.columnShear_column_two
#print axioms JSP400.Mahler.columnShear_gramOne
#print axioms JSP400.Mahler.columnShear_mu21
#print axioms JSP400.Mahler.columnShear_gramTwo
#print axioms JSP400.Mahler.columnShear_mu31
#print axioms JSP400.Mahler.gram_two_column_one
#print axioms JSP400.Mahler.columnShear_mu32
#print axioms JSP400.Mahler.columnShear_gramThree
#print axioms JSP400.Mahler.exists_size_reduction
#print axioms JSP400.Mahler.cross3_energy
#print axioms JSP400.Mahler.cross3_smul_add_self
#print axioms JSP400.Mahler.inverse_last_row_cross
#print axioms JSP400.Mahler.inverse_middle_row_cross
#print axioms JSP400.Mahler.lastInverseRow_energy_gram
#print axioms JSP400.Mahler.inverse_middle_row_energy_gram
#print axioms JSP400.Mahler.half_bound_sq
#print axioms JSP400.Mahler.reduced_first_gram_inequality
#print axioms JSP400.Mahler.reduced_second_gram_inequality
#print axioms JSP400.Mahler.energy_column_two
#print axioms JSP400.Mahler.norm_sq_le_energy
#print axioms JSP400.Mahler.matrix_norm_bound_of_reduced
#print axioms JSP400.Mahler.bounded_reduced_representatives
#print axioms JSP400.arbitrarily_short_vectors
#print axioms JSP400.integer_small_values
#print axioms JSP400.positive_statement
#print axioms JSP400.erdos_496
#print axioms JSP400.erdos_496_large_denominator

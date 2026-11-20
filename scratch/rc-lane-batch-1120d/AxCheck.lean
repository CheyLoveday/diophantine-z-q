import ZInQKernel.Contrib.OneProof.RC.EisForm.Attachment
import ZInQKernel.Contrib.OneProof.RC.EisForm.Expansion
import ZInQKernel.Contrib.OneProof.RC.EisForm.Lipschitz
import ZInQKernel.Contrib.OneProof.RC.EisForm.Modularity
import ZInQKernel.Contrib.OneProof.RC.EisForm.Occurrence
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Bounds
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Characters
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Fourier
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Lattice
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Mean
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Reduction
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Regroup
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Residues
import ZInQKernel.Contrib.OneProof.RC.TwoFresh.Main
import ZInQKernel.Contrib.OneProof.RC.TwoFresh.Stage

#print axioms ZInQ.Manuscript.RC.EisForm.divisorCoeff_eq_eisenstein
#print axioms ZInQ.Manuscript.RC.EisForm.pair_goodRec
#print axioms ZInQ.Manuscript.RC.EisForm.old_goodRec
#print axioms ZInQ.Manuscript.RC.EisForm.weightTwist_eq_one_of_inertia
#print axioms ZInQ.Manuscript.RC.EisForm.normalizedRep_unramified
#print axioms ZInQ.Manuscript.RC.EisForm.normalizedRep_goodAttachment
#print axioms ZInQ.Manuscript.RC.EisForm.baseForm_good_trace
#print axioms ZInQ.Manuscript.RC.EisForm.continuous_finiteChar
#print axioms ZInQ.Manuscript.RC.EisForm.continuous_splitTrace
#print axioms ZInQ.Manuscript.RC.EisForm.repInput_of_split_choice
#print axioms ZInQ.Manuscript.RC.EisForm.divisorCoeff_eq_sum_divisors
#print axioms ZInQ.Manuscript.RC.EisForm.norm_divisorCoeff_le
#print axioms ZInQ.Manuscript.RC.EisForm.summable_seriesCoeff
#print axioms ZInQ.Manuscript.RC.EisForm.series_radius
#print axioms ZInQ.Manuscript.RC.EisForm.hasSum_series
#print axioms ZInQ.Manuscript.RC.EisForm.series_holo
#print axioms ZInQ.Manuscript.RC.EisForm.series_periodic
#print axioms ZInQ.Manuscript.RC.EisForm.series_boundedAtInfty
#print axioms ZInQ.Manuscript.RC.EisForm.coeff_of_hasSum
#print axioms ZInQ.Manuscript.RC.EisForm.qExpansion_series
#print axioms ZInQ.Manuscript.RC.EisForm.summable_lambertTerm
#print axioms ZInQ.Manuscript.RC.EisForm.series_eq_lambert
#print axioms ZInQ.Manuscript.RC.EisForm.primitive_ringHomComp
#print axioms ZInQ.Manuscript.RC.EisForm.qParam_shift_pow
#print axioms ZInQ.Manuscript.RC.EisForm.lipschitzRow_eq
#print axioms ZInQ.Manuscript.RC.EisForm.gaussInv_ne_zero
#print axioms ZInQ.Manuscript.RC.EisForm.series_eq_lipschitz
#print axioms ZInQ.Manuscript.RC.EisForm.pairSeries_eq_lipschitz
#print axioms ZInQ.Manuscript.RC.EisForm.pairSeries_positive
#print axioms ZInQ.Manuscript.RC.EisForm.pairSeries_holo
#print axioms ZInQ.Manuscript.RC.EisForm.pairSeries_boundedAtInfty
#print axioms ZInQ.Manuscript.RC.EisForm.baseForm_of_modularity
#print axioms ZInQ.Manuscript.RC.EisForm.atLevel_coeff_degree
#print axioms ZInQ.Manuscript.RC.EisForm.scale_of_labeled_line
#print axioms ZInQ.Manuscript.RC.EisForm.column_of_labeled_line
#print axioms ZInQ.Manuscript.RC.EisForm.realizedCoordinate_of_labeled_line
#print axioms ZInQ.Manuscript.RC.EisSlash.gridRow_eq_kernel
#print axioms ZInQ.Manuscript.RC.EisSlash.rowKernel_neg
#print axioms ZInQ.Manuscript.RC.EisSlash.rowKernel_zero
#print axioms ZInQ.Manuscript.RC.EisSlash.positiveShift_im
#print axioms ZInQ.Manuscript.RC.EisSlash.rowKernel_fourier
#print axioms ZInQ.Manuscript.RC.EisSlash.decay_lt_one
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_decay
#print axioms ZInQ.Manuscript.RC.EisSlash.rowKernel_bound_pos
#print axioms ZInQ.Manuscript.RC.EisSlash.gridRow_majorant
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_gridRows
#print axioms ZInQ.Manuscript.RC.EisSlash.gridSeries_bounded
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_eq_gridSeries_sub
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_shift
#print axioms ZInQ.Manuscript.RC.EisSlash.rowWeight_grid
#print axioms ZInQ.Manuscript.RC.EisSlash.characterWeight_on_row
#print axioms ZInQ.Manuscript.RC.EisSlash.rowWeight_transform
#print axioms ZInQ.Manuscript.RC.EisSlash.characterWeight_pullback
#print axioms ZInQ.Manuscript.RC.EisSlash.pairNebentypus_value
#print axioms ZInQ.Manuscript.RC.EisSlash.pairWeight_pullback
#print axioms ZInQ.Manuscript.RC.EisSlash.rowWeight_mul
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRow_mul
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRow_zero
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRow_even
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRows_restrict
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRow_positive
#print axioms ZInQ.Manuscript.RC.EisSlash.ordered_grid_fourier
#print axioms ZInQ.Manuscript.RC.EisSlash.inv_apply_neg_one
#print axioms ZInQ.Manuscript.RC.EisSlash.ramified_complex_ne_one
#print axioms ZInQ.Manuscript.RC.EisSlash.pair_grid_fourier
#print axioms ZInQ.Manuscript.RC.EisSlash.pair_modularity
#print axioms ZInQ.Manuscript.RC.EisSlash.pair_baseForm
#print axioms ZInQ.Manuscript.RC.EisSlash.linear_eq_zero_iff
#print axioms ZInQ.Manuscript.RC.EisSlash.summand_eq
#print axioms ZInQ.Manuscript.RC.EisSlash.grid_injective
#print axioms ZInQ.Manuscript.RC.EisSlash.linear_grid_bigO
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_lattice_diff
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_add
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_slash
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_gridRow_inner
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_gridDiff_prod
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_eq_rows
#print axioms ZInQ.Manuscript.RC.EisSlash.gridSeries_shift
#print axioms ZInQ.Manuscript.RC.EisSlash.splitResidue_val
#print axioms ZInQ.Manuscript.RC.EisSlash.sum_residue_second
#print axioms ZInQ.Manuscript.RC.EisSlash.sum_residue_first
#print axioms ZInQ.Manuscript.RC.EisSlash.characterWeight_sum_zero
#print axioms ZInQ.Manuscript.RC.EisSlash.orderedScale_ne_zero
#print axioms ZInQ.Manuscript.RC.EisSlash.pairScale_ne_zero
#print axioms ZInQ.Manuscript.RC.EisSlash.pair_checks_of_grid_eq
#print axioms ZInQ.Manuscript.RC.EisSlash.missingModularity_of_gridFourier
#print axioms ZInQ.Manuscript.RC.EisSlash.baseForm_of_gridFourier
#print axioms ZInQ.Manuscript.RC.EisSlash.summable_finite_prod
#print axioms ZInQ.Manuscript.RC.EisSlash.sum_residue_rows
#print axioms ZInQ.Manuscript.RC.EisSlash.residue_vec
#print axioms ZInQ.Manuscript.RC.EisSlash.grid_residue_vec
#print axioms ZInQ.Manuscript.RC.EisSlash.weightedRow_on_residue
#print axioms ZInQ.Manuscript.RC.EisSlash.gridCombination_eq_weightedRows
#print axioms ZInQ.Manuscript.RC.EisSlash.rowResidue_lift
#print axioms ZInQ.Manuscript.RC.EisSlash.exists_grid_of_residue_eq
#print axioms ZInQ.Manuscript.RC.EisSlash.rowResidue_vecMul
#print axioms ZInQ.Manuscript.RC.EisSlash.gridCombination_eq_rows
#print axioms ZInQ.Manuscript.RC.EisSlash.latticeDiff_residue_slash
#print axioms ZInQ.Manuscript.RC.EisSlash.gridCombination_slash
#print axioms ZInQ.Manuscript.RC.EisSlash.gridCombination_slash_scalar
#print axioms ZInQ.Manuscript.RC.EisSlash.gridCombination_bounded_slash
#print axioms ZInQ.Manuscript.RC.TwoFresh.two_hecke_coeff
#print axioms ZInQ.Manuscript.RC.TwoFresh.dense_twoFreshTests
#print axioms ZInQ.Manuscript.RC.TwoFresh.continuous_twoTraces
#print axioms ZInQ.Manuscript.RC.TwoFresh.h2fresh
#print axioms ZInQ.Manuscript.RC.TwoFresh.fresh_squarefree_weight
#print axioms ZInQ.Manuscript.RC.TwoFresh.ne_unary_of_oddPart
#print axioms ZInQ.Manuscript.RC.TwoFresh.map_TL
#print axioms ZInQ.Manuscript.RC.TwoFresh.dvd_of_stage_dvd
#print axioms ZInQ.Manuscript.RC.TwoFresh.fresh_normalizations

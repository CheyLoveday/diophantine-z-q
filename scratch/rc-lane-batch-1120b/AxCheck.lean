import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Central
import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Clearing
import ZInQKernel.Contrib.OneProof.RC.AppE32Fixed.Fixed
import ZInQKernel.Contrib.OneProof.RC.AppEK1.CoefficientCohomology
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Coefficients
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Comparison
import ZInQKernel.Contrib.OneProof.RC.AppEK1.FiniteIdentity
import ZInQKernel.Contrib.OneProof.RC.AppEK1.ShapiroTransfer
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Analytic
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Assembly
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Generic
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Sign
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Specialization
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Uniformization
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Family
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry
import ZInQKernel.Contrib.OneProof.RC.CMField2.AnalyticDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.CoordinateDescent
import ZInQKernel.Contrib.OneProof.RC.CMField2.CosetLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.Cyclic
import ZInQKernel.Contrib.OneProof.RC.CMField2.Degree
import ZInQKernel.Contrib.OneProof.RC.CMField2.Descent
import ZInQKernel.Contrib.OneProof.RC.CMField2.Diagonal
import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrder
import ZInQKernel.Contrib.OneProof.RC.CMField2.ExactOrderProof
import ZInQKernel.Contrib.OneProof.RC.CMField2.Factorization
import ZInQKernel.Contrib.OneProof.RC.CMField2.Frobenius
import ZInQKernel.Contrib.OneProof.RC.CMField2.HeegnerLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.IdealDictionary
import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality
import ZInQKernel.Contrib.OneProof.RC.CMField2.Kronecker
import ZInQKernel.Contrib.OneProof.RC.CMField2.Lattices
import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelOne
import ZInQKernel.Contrib.OneProof.RC.CMField2.LevelTwo
import ZInQKernel.Contrib.OneProof.RC.CMField2.Membership
import ZInQKernel.Contrib.OneProof.RC.CMField2.MembershipDegree
import ZInQKernel.Contrib.OneProof.RC.CMField2.Multipliers
import ZInQKernel.Contrib.OneProof.RC.CMField2.NormCriterion
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrderGenerator
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrientedIdeals
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimeComparison
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimitiveNorms
import ZInQKernel.Contrib.OneProof.RC.CMField2.Results
import ZInQKernel.Contrib.OneProof.RC.CMField2.ScalarWitness
import ZInQKernel.Contrib.OneProof.RC.CMField2.SplitPrime
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Calibration
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.LocalOrders
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Suppliers
import ZInQKernel.Contrib.OneProof.RC.CalPres.Actions
import ZInQKernel.Contrib.OneProof.RC.CalPres.Presentations
import ZInQKernel.Contrib.OneProof.RC.CalPres.SplitModel
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Finiteness
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Prints
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Reduction
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Jacobi
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Mask
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.MaskCore
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Operators
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Ordinary
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Permutation
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Projector
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.SeriesBounds
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Unary
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Affine
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Character
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Dilation
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Matrices
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.PrimeGauss
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Theta
import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Translate
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Characters
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Cusps
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Finite
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Lines
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OddDenominator
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.OrdinaryPhase
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.PrimeGauss
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Relative
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Shell
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Transform
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Application
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Level
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Realize
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Atkin
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Integral
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Row
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.AffineLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BaseValue
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BranchExpansion
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ChartComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspOrbits
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Endpoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Factor
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FormalBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.GeometricTorsion
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LaurentLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LimitUniqueness
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelSource
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.PointedCurve
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAbelian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveUniformization
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.SourceLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.TranslatedBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Triangular
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeierstrassPeriods
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeightedComparison
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Finite
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Interface
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Print
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Determinant
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Old
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Operator
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Packet
import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Shift
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.ActualFamily
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.At
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Character
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Family
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Filter
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Ideals
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.IdeleClass
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Join
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Parametrization
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Schwartz
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Character.Basis
import ZInQKernel.Contrib.OneProof.RC.O7Character.Character
import ZInQKernel.Contrib.OneProof.RC.O7Character.Stage
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Local
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Norm
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Orientation
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Transport
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Weights
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Artin
import ZInQKernel.Contrib.OneProof.RC.O7Residual.At
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Family
import ZInQKernel.Contrib.OneProof.RC.O7Residual.IdealNorm
import ZInQKernel.Contrib.OneProof.RC.O7Residual.Orbit
import ZInQKernel.Contrib.OneProof.RC.O7Residual.OrbitQuotient
import ZInQKernel.Contrib.OneProof.RC.O7Residual.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.SelectorTotal.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.MatrixTest
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Roots
import ZInQKernel.Contrib.OneProof.RC.ThetaClose.Support
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.AdelicNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Invariance
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LevelTheta
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Neighbour
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.NormCharacter
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.ReducedNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Support
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Norm
import ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Model
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Overlap
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Specialize
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Unramified
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleElkik
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionCoordinates
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionFormula
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveChartGluing
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupIdentities
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupLaw
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveSchemeCharts

#print axioms ZInQ.Manuscript.RC.AppE32Fixed.det_rows_eq_zero_iff
#print axioms ZInQ.Manuscript.RC.AppE32Fixed.central_zero_iff_of_wedge
#print axioms ZInQ.Manuscript.RC.AppE32Fixed.uterWitness_of_completed_coefficients
#print axioms ZInQ.Manuscript.RC.AppE32Fixed.appEOutputs_of_kato_fixed
#print axioms ZInQ.Manuscript.RC.AppE32Fixed.evenScalar32_of_kato_fixed
#print axioms ZInQ.Manuscript.RC.AtkinPin.slash_eq_signUnit_smul
#print axioms ZInQ.Manuscript.RC.AtkinPin.hasDerivAt_eichlerPotential
#print axioms ZInQ.Manuscript.RC.AtkinPin.scaled_eichler_transform
#print axioms ZInQ.Manuscript.RC.AtkinPin.periodClass_transform
#print axioms ZInQ.Manuscript.RC.AtkinPin.consumerNewform
#print axioms ZInQ.Manuscript.RC.AtkinPin.stageLevel_eq
#print axioms ZInQ.Manuscript.RC.AtkinPin.ddStagedOfPinnedParamValues
#print axioms ZInQ.Manuscript.RC.AtkinPin.atkinGL_chart_congr
#print axioms ZInQ.Manuscript.RC.AtkinPin.atkinGL_sq_chart
#print axioms ZInQ.Manuscript.RC.AtkinPin.atkinInterior_apply
#print axioms ZInQ.Manuscript.RC.AtkinPin.atkinInterior_involutive
#print axioms ZInQ.Manuscript.RC.AtkinPin.phiAn_transform
#print axioms ZInQ.Manuscript.RC.AtkinPin.projectiveValue_transform_chart
#print axioms ZInQ.Manuscript.RC.AtkinPin.actualParametrization_transform_chart
#print axioms ZInQ.Manuscript.RC.AtkinPin.anslatedAtkinOnPoints
#print axioms ZInQ.Manuscript.RC.AtkinPin.anslatedAtkinAtInfinity
#print axioms ZInQ.Manuscript.RC.AtkinPin.signUnit_cast
#print axioms ZInQ.Manuscript.RC.AtkinPin.wNew_cast
#print axioms ZInQ.Manuscript.RC.AtkinPin.atkin_quotient_of_specialization
#print axioms ZInQ.Manuscript.RC.AtkinPin.pinned_atkin_quotient_of_specialization
#print axioms ZInQ.Manuscript.RC.AtkinPin.cast_point_some
#print axioms ZInQ.Manuscript.RC.AtkinPin.weierPt_add
#print axioms ZInQ.Manuscript.RC.AtkinSign.actualRowFamily
#print axioms ZInQ.Manuscript.RC.AtkinSign.ddStagedActual
#print axioms ZInQ.Manuscript.RC.AtkinSign.SpecialFibreAtSigns
#print axioms ZInQ.Manuscript.RC.AtkinSign.SpecialFibreAtSigns.toSpecialFibre
#print axioms ZInQ.Manuscript.RC.AtkinSign.SpecialFibreAtSigns.atkinSign_eq
#print axioms ZInQ.Manuscript.RC.AtkinSign.SpecialFibreAtSigns.ofSpecialFibre
#print axioms ZInQ.Manuscript.RC.CMField2.eq_cmPoint_of_quadratic
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_le_of_primitive_equation
#print axioms ZInQ.Manuscript.RC.CMField2.cmFieldOfDefinition_modelOne_of
#print axioms ZInQ.Manuscript.RC.CMField2.heegner_coordinates_mem_ringClass_of
#print axioms ZInQ.Manuscript.RC.CMField2.branchDescends_one
#print axioms ZInQ.Manuscript.RC.CMField2.exists_cyclic_sublattice_of_modularPolynomial_root
#print axioms ZInQ.Manuscript.RC.CMField2.exists_analyticJ_eq
#print axioms ZInQ.Manuscript.RC.CMField2.conjugate_has_cyclic_self_of_root
#print axioms ZInQ.Manuscript.RC.CMField2.isAddCyclic_quotient_of_primitive
#print axioms ZInQ.Manuscript.RC.CMField2.isAddCyclic_sublatticeQuotient_of_primitive
#print axioms ZInQ.Manuscript.RC.CMField2.primitive_of_isAddCyclic_quotient
#print axioms ZInQ.Manuscript.RC.CMField2.primitive_of_isAddCyclic_sublatticeQuotient
#print axioms ZInQ.Manuscript.RC.CMField2.ConjugateSingularModulus
#print axioms ZInQ.Manuscript.RC.CMField2.finrank_adjoin_le_of_conjugate_family
#print axioms ZInQ.Manuscript.RC.CMField2.mkPic_picRepresentative
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_le_of_conjugate
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_over_base_le_of_conjugate
#print axioms ZInQ.Manuscript.RC.CMField2.BranchDescends
#print axioms ZInQ.Manuscript.RC.CMField2.affineEval_factor
#print axioms ZInQ.Manuscript.RC.CMField2.chart_mem
#print axioms ZInQ.Manuscript.RC.CMField2.fieldPoint_of_affineEval_range
#print axioms ZInQ.Manuscript.RC.CMField2.fieldPoint_of_finitePointEval_range
#print axioms ZInQ.Manuscript.RC.CMField2.fieldPoint_iff_finitePointEval_range
#print axioms ZInQ.Manuscript.RC.CMField2.cmFieldOfDefinition_of
#print axioms ZInQ.Manuscript.RC.CMField2.fieldPoint_of_eval_mem_adjoin_coordinates
#print axioms ZInQ.Manuscript.RC.CMField2.fieldPoint_of_eval_rational_in_coordinates
#print axioms ZInQ.Manuscript.RC.CMField2.eval_diagonal
#print axioms ZInQ.Manuscript.RC.CMField2.Multiplicity_specialization_eq_of_embeddings
#print axioms ZInQ.Manuscript.RC.CMField2.isIntegral_jLattice_of_cyclicSelf
#print axioms ZInQ.Manuscript.RC.CMField2.exists_nonsquare_quadratic_value
#print axioms ZInQ.Manuscript.RC.CMField2.ExactMultiplierOrderOfDiagonalMultiplicities
#print axioms ZInQ.Manuscript.RC.CMField2.conjugateSingularModulus_of_exactMultiplier
#print axioms ZInQ.Manuscript.RC.CMField2.periodMultipliers_idealPeriod
#print axioms ZInQ.Manuscript.RC.CMField2.same_normalized_order
#print axioms ZInQ.Manuscript.RC.CMField2.exactMultiplierOrderOfDiagonalMultiplicities
#print axioms ZInQ.Manuscript.RC.CMField2.conjugateSingularModulus
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_le
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_over_base_le
#print axioms ZInQ.Manuscript.RC.CMField2.coe_cosetParameter
#print axioms ZInQ.Manuscript.RC.CMField2.coe_slDenom_ne_zero
#print axioms ZInQ.Manuscript.RC.CMField2.injOn_coset_j_of_transcendental
#print axioms ZInQ.Manuscript.RC.CMField2.modularPolynomial_eq_coset_product
#print axioms ZInQ.Manuscript.RC.CMField2.exists_coset_of_modularPolynomial_root
#print axioms ZInQ.Manuscript.RC.CMField2.pow_eq_of_kronecker_diagonal
#print axioms ZInQ.Manuscript.RC.CMField2.mem_of_separating_reductions
#print axioms ZInQ.Manuscript.RC.CMField2.coe_cmPoint_of_neg
#print axioms ZInQ.Manuscript.RC.CMField2.heegner_middle_coprime
#print axioms ZInQ.Manuscript.RC.CMField2.heegner_scaled_form
#print axioms ZInQ.Manuscript.RC.CMField2.int_mem_pairLattice
#print axioms ZInQ.Manuscript.RC.CMField2.mega_mem_pairLattice
#print axioms ZInQ.Manuscript.RC.CMField2.heegner_pairLattice_mul
#print axioms ZInQ.Manuscript.RC.CMField2.dilate_cmPoint_eq
#print axioms ZInQ.Manuscript.RC.CMField2.primitive_quadratic_equation
#print axioms ZInQ.Manuscript.RC.CMField2.exists_noninteger
#print axioms ZInQ.Manuscript.RC.CMField2.mul_mem_of_mem_pair
#print axioms ZInQ.Manuscript.RC.CMField2.proper_iff_isUnit
#print axioms ZInQ.Manuscript.RC.CMField2.exists_singularModulus_of_exact_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.cast_sublatticeIndex_scale
#print axioms ZInQ.Manuscript.RC.CMField2.exists_order_basis_one
#print axioms ZInQ.Manuscript.RC.CMField2.derBasis_im_ne_zero
#print axioms ZInQ.Manuscript.RC.CMField2.primitive_scale_of_order_basis
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_isIntegral
#print axioms ZInQ.Manuscript.RC.CMField2.cast_absNorm_span_singleton_complex
#print axioms ZInQ.Manuscript.RC.CMField2.prime_diagonal_eq_of_order_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.swap
#print axioms ZInQ.Manuscript.RC.CMField2.swap_reduce
#print axioms ZInQ.Manuscript.RC.CMField2.jqMod_eq_jqModC
#print axioms ZInQ.Manuscript.RC.CMField2.modularPolynomial_reduced_root
#print axioms ZInQ.Manuscript.RC.CMField2.kroneckerCongruence_of_prime
#print axioms ZInQ.Manuscript.RC.CMField2.pow_eq_of_modularPolynomial_diagonal_root
#print axioms ZInQ.Manuscript.RC.CMField2.exists_ideal_basis
#print axioms ZInQ.Manuscript.RC.CMField2.embedding_indep
#print axioms ZInQ.Manuscript.RC.CMField2.idealPeriod
#print axioms ZInQ.Manuscript.RC.CMField2.idealPeriod_lattice
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus
#print axioms ZInQ.Manuscript.RC.CMField2.jLattice_eq_of_lattice_eq
#print axioms ZInQ.Manuscript.RC.CMField2.jLattice_scale
#print axioms ZInQ.Manuscript.RC.CMField2.lattice_scale
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_eq_of_mkPic_eq
#print axioms ZInQ.Manuscript.RC.CMField2.jPull_one_surjective
#print axioms ZInQ.Manuscript.RC.CMField2.finiteEval_jPull
#print axioms ZInQ.Manuscript.RC.CMField2.finiteEval_jPull_mem_range
#print axioms ZInQ.Manuscript.RC.CMField2.finiteChart_finiteTest
#print axioms ZInQ.Manuscript.RC.CMField2.finitePointEval_one_mem_range
#print axioms ZInQ.Manuscript.RC.CMField2.modelOne_fieldPoint_of_analyticJ
#print axioms ZInQ.Manuscript.RC.CMField2.levelTwo_heegner
#print axioms ZInQ.Manuscript.RC.CMField2.hs
#print axioms ZInQ.Manuscript.RC.CMField2.hplus
#print axioms ZInQ.Manuscript.RC.CMField2.hminus
#print axioms ZInQ.Manuscript.RC.CMField2.hshift
#print axioms ZInQ.Manuscript.RC.CMField2.hquad
#print axioms ZInQ.Manuscript.RC.CMField2.hprod
#print axioms ZInQ.Manuscript.RC.CMField2.levelTwo_reflection
#print axioms ZInQ.Manuscript.RC.CMField2.S_plus
#print axioms ZInQ.Manuscript.RC.CMField2.S_minus
#print axioms ZInQ.Manuscript.RC.CMField2.T_dilate
#print axioms ZInQ.Manuscript.RC.CMField2.levelTwo_coordinates
#print axioms ZInQ.Manuscript.RC.CMField2.middleCoefficient_mod_four
#print axioms ZInQ.Manuscript.RC.CMField2.levelTwo_distinct
#print axioms ZInQ.Manuscript.RC.CMField2.SingularModulusMemRingClass
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_finrank_over_base_le_of_mem
#print axioms ZInQ.Manuscript.RC.CMField2.periodMultipliers
#print axioms ZInQ.Manuscript.RC.CMField2.mega_one_mem
#print axioms ZInQ.Manuscript.RC.CMField2.secondCoord
#print axioms ZInQ.Manuscript.RC.CMField2.exists_int_of_secondCoord_eq_zero
#print axioms ZInQ.Manuscript.RC.CMField2.exists_multiplier_basis_one
#print axioms ZInQ.Manuscript.RC.CMField2.integral_trace_norm_of_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.exists_normalized_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.periodMultipliers_scale
#print axioms ZInQ.Manuscript.RC.CMField2.periodMultipliers_eq_of_jLattice_eq
#print axioms ZInQ.Manuscript.RC.CMField2.int_coords_eq
#print axioms ZInQ.Manuscript.RC.CMField2.normSq_of_coords
#print axioms ZInQ.Manuscript.RC.CMField2.scale_le_of_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.scale_primitive_iff_gcd
#print axioms ZInQ.Manuscript.RC.CMField2.diagonal_root_iff_ofTau
#print axioms ZInQ.Manuscript.RC.CMField2.diagonal_root_iff_primitive_norm
#print axioms ZInQ.Manuscript.RC.CMField2.discr_of_basis_one
#print axioms ZInQ.Manuscript.RC.CMField2.exists_heegner_generator
#print axioms ZInQ.Manuscript.RC.CMField2.exists_heegner_generator_in_embedding
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_coe
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_restrictScalars
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_mul_conjugate
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_isUnit
#print axioms ZInQ.Manuscript.RC.CMField2.analyticJ_eq_singularModulus_of_generator
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_mul_scaled
#print axioms ZInQ.Manuscript.RC.CMField2.formIdeal_scaled_eq_levelInverse_mul
#print axioms ZInQ.Manuscript.RC.CMField2.exists_heegner_singularModuli_in_embedding
#print axioms ZInQ.Manuscript.RC.CMField2.exists_heegner_singularModuli
#print axioms ZInQ.Manuscript.RC.CMField2.ational_prime_span_ne_bot
#print axioms ZInQ.Manuscript.RC.CMField2.absNorm_under_eq_of_pow_fixed
#print axioms ZInQ.Manuscript.RC.CMField2.absNorm_under_eq_of_frob_fixes
#print axioms ZInQ.Manuscript.RC.CMField2.not_mem_of_norm_lt
#print axioms ZInQ.Manuscript.RC.CMField2.splitPrime_of_frob_fixes_ringClass
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulusMemRingClass
#print axioms ZInQ.Manuscript.RC.CMField2.primitiveNormLevels
#print axioms ZInQ.Manuscript.RC.CMField2.min_generic
#print axioms ZInQ.Manuscript.RC.CMField2.generic_trace_one_gap
#print axioms ZInQ.Manuscript.RC.CMField2.not_primitive_of_even
#print axioms ZInQ.Manuscript.RC.CMField2.gaussian_no_three
#print axioms ZInQ.Manuscript.RC.CMField2.gaussian_no_four
#print axioms ZInQ.Manuscript.RC.CMField2.eisenstein_no_four
#print axioms ZInQ.Manuscript.RC.CMField2.eisenstein_no_mod_three
#print axioms ZInQ.Manuscript.RC.CMField2.quadraticNormParameters_eq_of_primitiveNormLevels
#print axioms ZInQ.Manuscript.RC.CMField2.cmFieldOfDefinition
#print axioms ZInQ.Manuscript.RC.CMField2.cmFieldOfDefinition_modelOne
#print axioms ZInQ.Manuscript.RC.CMField2.cmFieldOfDefinition_one
#print axioms ZInQ.Manuscript.RC.CMField2.heegner_coordinates_mem_ringClass
#print axioms ZInQ.Manuscript.RC.CMField2.exists_invariant_scaling
#print axioms ZInQ.Manuscript.RC.CMField2.exists_homothetic_of_jLattice_eq
#print axioms ZInQ.Manuscript.RC.CMField2.exists_int_eq_of_real_multiplier
#print axioms ZInQ.Manuscript.RC.CMField2.conjugate_has_nonreal_multiplier_of_root
#print axioms ZInQ.Manuscript.RC.CMField2.singularModulus_reduction_pow_eq_of_split
#print axioms ZInQ.Contrib.RC53Assist.Calibration.centralChar_coe
#print axioms ZInQ.Contrib.RC53Assist.Calibration.central_tmul_smul
#print axioms ZInQ.Contrib.RC53Assist.Calibration.central_smul_of_torsion_fixed
#print axioms ZInQ.Contrib.RC53Assist.Calibration.centralSignedTateAction
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingInertiaAction
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeInertiaAction
#print axioms ZInQ.Contrib.RC53Assist.Calibration.signedReduced_subScalar
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingReduced_subScalar
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeSignedTate_subOne_even
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeReduced_apply
#print axioms ZInQ.Contrib.RC53Assist.Calibration.kummerFirstCoordinate
#print axioms ZInQ.Contrib.RC53Assist.Calibration.presentationOfSplit
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingBlock
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingOrdinary
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeBlock
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingPresentation
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activePresentation
#print axioms ZInQ.Contrib.RC53Assist.Calibration.presentationAtZero
#print axioms ZInQ.Contrib.RC53Assist.Calibration.splitLocalModel
#print axioms ZInQ.Contrib.RC53Assist.Calibration.splitLocalH1
#print axioms ZInQ.Contrib.RC53Assist.Calibration.splitLocalH2
#print axioms ZInQ.Contrib.RC53Assist.Calibration.quotientOfFirstCoordinate
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeMiddleCoordinates
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeMiddleCoordinates_d0
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeMiddleCoordinates_d1
#print axioms ZInQ.Contrib.RC53Assist.Calibration.cx3Hom_isIso
#print axioms ZInQ.Contrib.RC53Assist.Calibration.movingTameNormalization
#print axioms ZInQ.Contrib.RC53Assist.Calibration.ameNorm_negId
#print axioms ZInQ.Contrib.RC53Assist.Calibration.activeTameNormalization
#print axioms ZInQ.Manuscript.RC.ElkikPrint.cuspClass_finiteRange_of_cuspOrbits
#print axioms ZInQ.Manuscript.RC.ElkikPrint.maninDrinfeld_of_torsion
#print axioms ZInQ.Manuscript.RC.ElkikPrint.hElkikMD_of_elkikTorsion
#print axioms ZInQ.Manuscript.RC.EvenExpansion.moving_nil
#print axioms ZInQ.Manuscript.RC.EvenExpansion.moving_of_step
#print axioms ZInQ.Manuscript.RC.EvenExpansion.weightTwoBlock
#print axioms ZInQ.Manuscript.RC.EvenExpansion.subscripts_dvd
#print axioms ZInQ.Manuscript.RC.EvenExpansion.unaryLevel_dvd
#print axioms ZInQ.Manuscript.RC.EvenExpansion.includeUnary_mem
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenWeightTwo
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenVector_eval
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenExpansion
#print axioms ZInQ.Manuscript.RC.EvenExpansion.lower_add
#print axioms ZInQ.Manuscript.RC.EvenExpansion.ansform_characterization
#print axioms ZInQ.Manuscript.RC.EvenExpansion.mem_thetaStabilizer
#print axioms ZInQ.Manuscript.RC.EvenExpansion.T_mem_stabilizer
#print axioms ZInQ.Manuscript.RC.EvenExpansion.neg_one_mem_stabilizer
#print axioms ZInQ.Manuscript.RC.EvenExpansion.jacobiTheta_fricke_fourth
#print axioms ZInQ.Manuscript.RC.EvenExpansion.lower_one_mem_stabilizer
#print axioms ZInQ.Manuscript.RC.EvenExpansion.lower_mem_stabilizer
#print axioms ZInQ.Manuscript.RC.EvenExpansion.iangular_mem
#print axioms ZInQ.Manuscript.RC.EvenExpansion.centre
#print axioms ZInQ.Manuscript.RC.EvenExpansion.Tmul_entries
#print axioms ZInQ.Manuscript.RC.EvenExpansion.lowerMul_entry
#print axioms ZInQ.Manuscript.RC.EvenExpansion.stabilizer_of_c
#print axioms ZInQ.Manuscript.RC.EvenExpansion.jacobiTheta_fourth_transform
#print axioms ZInQ.Manuscript.RC.EvenExpansion.hreeHalves_of_cusp
#print axioms ZInQ.Manuscript.RC.EvenExpansion.hasThreeHalves_of_cusp
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenMasked
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenMasked_reference
#print axioms ZInQ.Manuscript.RC.EvenExpansion.evenMasked_expansion
#print axioms ZInQ.Manuscript.RC.EvenExpansion.squareTwist_sq
#print axioms ZInQ.Manuscript.RC.EvenExpansion.quadraticProjection
#print axioms ZInQ.Manuscript.RC.EvenExpansion.up_translation
#print axioms ZInQ.Manuscript.RC.EvenExpansion.qParam_dilate
#print axioms ZInQ.Manuscript.RC.EvenExpansion.qParam_undilate
#print axioms ZInQ.Manuscript.RC.EvenExpansion.series_Vp
#print axioms ZInQ.Manuscript.RC.EvenExpansion.series_Up
#print axioms ZInQ.Manuscript.RC.EvenExpansion.series_Up_sq_Vp
#print axioms ZInQ.Manuscript.RC.EvenExpansion.movingOp_series
#print axioms ZInQ.Manuscript.RC.EvenExpansion.dinaryTheta_cusps
#print axioms ZInQ.Manuscript.RC.EvenExpansion.dinaryTheta_fourth
#print axioms ZInQ.Manuscript.RC.EvenExpansion.dinaryThetaLaw
#print axioms ZInQ.Manuscript.RC.EvenExpansion.fractionalPermutation
#print axioms ZInQ.Manuscript.RC.EvenExpansion.upSquare_permutation
#print axioms ZInQ.Manuscript.RC.EvenExpansion.upSquare_conjugation
#print axioms ZInQ.Manuscript.RC.EvenExpansion.dual_orthogonality
#print axioms ZInQ.Manuscript.RC.EvenExpansion.summable_squareShell
#print axioms ZInQ.Manuscript.RC.EvenExpansion.exists_unary_parity
#print axioms ZInQ.Manuscript.RC.EvenExpansion.unary_shell
#print axioms ZInQ.Manuscript.RC.EvenExpansion.unary_hasSum
#print axioms ZInQ.Manuscript.RC.GoodReduction.atkinQuotient_of_affine
#print axioms ZInQ.Manuscript.RC.GoodReduction.atkinQuotient_of_integralRelation
#print axioms ZInQ.Manuscript.RC.GoodReduction.existsUnique_integralMap
#print axioms ZInQ.Manuscript.RC.GoodReduction.exists_integralPoint
#print axioms ZInQ.Manuscript.RC.GoodReduction.integralAffine_baseChange
#print axioms ZInQ.Manuscript.RC.GoodReduction.hpi_of_integralDiagram
#print axioms ZInQ.Manuscript.RC.J0Cusps.maps_to_rat_unique
#print axioms ZInQ.Manuscript.RC.J0Cusps.sectionEval
#print axioms ZInQ.Manuscript.RC.J0Cusps.sectionMap_factor
#print axioms ZInQ.Manuscript.RC.J0Cusps.specPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.ensorMap
#print axioms ZInQ.Manuscript.RC.J0Cusps.ensorProjection
#print axioms ZInQ.Manuscript.RC.J0Cusps.ensorPoint_eq
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_specPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_complexLift_of_sections
#print axioms ZInQ.Manuscript.RC.J0Cusps.cusp_at_infinity_maps_to_unit
#print axioms ZInQ.Manuscript.RC.J0Cusps.jGenField
#print axioms ZInQ.Manuscript.RC.J0Cusps.jNGenField
#print axioms ZInQ.Manuscript.RC.J0Cusps.fieldGerm_first
#print axioms ZInQ.Manuscript.RC.J0Cusps.germ_inverse
#print axioms ZInQ.Manuscript.RC.J0Cusps.branch_expansion
#print axioms ZInQ.Manuscript.RC.J0Cusps.complexLift_comp
#print axioms ZInQ.Manuscript.RC.J0Cusps.value_eq_of_chart_limit
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspLimit_eq_zero_of_jacobi_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspComparison_of_zero_chart_limit
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspIndex
#print axioms ZInQ.Manuscript.RC.J0Cusps.bitOfSL
#print axioms ZInQ.Manuscript.RC.J0Cusps.bitOfSL_surjective
#print axioms ZInQ.Manuscript.RC.J0Cusps.bitOfSL_eq
#print axioms ZInQ.Manuscript.RC.J0Cusps.at_label_real
#print axioms ZInQ.Manuscript.RC.J0Cusps.anslated_limit_congr
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp
#print axioms ZInQ.Manuscript.RC.J0Cusps.extendPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.extendPoint_injective
#print axioms ZInQ.Manuscript.RC.J0Cusps.ationalAsGeometric
#print axioms ZInQ.Manuscript.RC.J0Cusps.extend_rationalAsGeometric
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp_limit
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp_infinity
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp_zero_rational
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCusp_infinity_rational
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspAssignment_zero_limit
#print axioms ZInQ.Manuscript.RC.J0Cusps.scalarSpec
#print axioms ZInQ.Manuscript.RC.J0Cusps.extendJacobian
#print axioms ZInQ.Manuscript.RC.J0Cusps.extendJacobian_class
#print axioms ZInQ.Manuscript.RC.J0Cusps.cusp_comparison_of_factor
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_gamma0_smul_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspOrbit_eq_zero_of_coprime
#print axioms ZInQ.Manuscript.RC.J0Cusps.cuspOrbit_eq_zero_of_jacobi_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.analyticJ_invariant
#print axioms ZInQ.Manuscript.RC.J0Cusps.qParam_one_zpow
#print axioms ZInQ.Manuscript.RC.J0Cusps.qParam_at_cusp
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_infinity
#print axioms ZInQ.Manuscript.RC.J0Cusps.dilate_S_dilate
#print axioms ZInQ.Manuscript.RC.J0Cusps.contract
#print axioms ZInQ.Manuscript.RC.J0Cusps.dilate_contract
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_contract
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.factor_isMonHom
#print axioms ZInQ.Manuscript.RC.J0Cusps.abelJacobi_comp_factor
#print axioms ZInQ.Manuscript.RC.J0Cusps.abelJacobi_comp_isBased
#print axioms ZInQ.Manuscript.RC.J0Cusps.usHom_pointClass
#print axioms ZInQ.Manuscript.RC.J0Cusps.usHom_cuspClass_of_jacobi_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.hElkikMD_atScale_of_projectiveGroup
#print axioms ZInQ.Manuscript.RC.J0Cusps.argetPeriodEquiv
#print axioms ZInQ.Manuscript.RC.J0Cusps.argetPeriodEquiv_lift
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCuspClass_comparison_atScale
#print axioms ZInQ.Manuscript.RC.J0Cusps.hElkikMD_atScale_of_geometricTorsion
#print axioms ZInQ.Manuscript.RC.J0Cusps.equation
#print axioms ZInQ.Manuscript.RC.J0Cusps.liftEquation
#print axioms ZInQ.Manuscript.RC.J0Cusps.liftBranch
#print axioms ZInQ.Manuscript.RC.J0Cusps.liftBranch_j
#print axioms ZInQ.Manuscript.RC.J0Cusps.liftBranch_jN
#print axioms ZInQ.Manuscript.RC.J0Cusps.firstAtCusp
#print axioms ZInQ.Manuscript.RC.J0Cusps.firstAtCusp_j
#print axioms ZInQ.Manuscript.RC.J0Cusps.firstAtCusp_eval
#print axioms ZInQ.Manuscript.RC.J0Cusps.iangular_root
#print axioms ZInQ.Manuscript.RC.J0Cusps.iangularField
#print axioms ZInQ.Manuscript.RC.J0Cusps.iangularField_j
#print axioms ZInQ.Manuscript.RC.J0Cusps.iangularField_jN
#print axioms ZInQ.Manuscript.RC.J0Cusps.zero_root
#print axioms ZInQ.Manuscript.RC.J0Cusps.zeroField
#print axioms ZInQ.Manuscript.RC.J0Cusps.zeroField_j
#print axioms ZInQ.Manuscript.RC.J0Cusps.zeroField_jN
#print axioms ZInQ.Manuscript.RC.J0Cusps.formalBranch
#print axioms ZInQ.Manuscript.RC.J0Cusps.formalBranch_generic
#print axioms ZInQ.Manuscript.RC.J0Cusps.branchPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.zeroPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.zeroPoint_overQ
#print axioms ZInQ.Manuscript.RC.J0Cusps.geometricCuspidalSubgroup_finite
#print axioms ZInQ.Manuscript.RC.J0Cusps.hElkikMD_of_geometricTorsion
#print axioms ZInQ.Manuscript.RC.J0Cusps.powerSeries_analytic_sum
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_powerSeries_eval
#print axioms ZInQ.Manuscript.RC.J0Cusps.evaluation_eq_sectionMap
#print axioms ZInQ.Manuscript.RC.J0Cusps.2_of_affine_pair
#print axioms ZInQ.Manuscript.RC.J0Cusps.source_t2
#print axioms ZInQ.Manuscript.RC.J0Cusps.complexLift_injective
#print axioms ZInQ.Manuscript.RC.J0Cusps.source_limit_unique
#print axioms ZInQ.Manuscript.RC.J0Cusps.infinity
#print axioms ZInQ.Manuscript.RC.J0Cusps.modelCurve
#print axioms ZInQ.Manuscript.RC.J0Cusps.modelPicard_exists
#print axioms ZInQ.Manuscript.RC.J0Cusps.modelPicard
#print axioms ZInQ.Manuscript.RC.J0Cusps.modelPicardRep
#print axioms ZInQ.Manuscript.RC.J0Cusps.J0
#print axioms ZInQ.Manuscript.RC.J0Cusps.aj0
#print axioms ZInQ.Manuscript.RC.J0Cusps.aj0_classifies
#print axioms ZInQ.Manuscript.RC.J0Cusps.isJacobian_aj0
#print axioms ZInQ.Manuscript.RC.J0Cusps.source
#print axioms ZInQ.Manuscript.RC.J0Cusps.model_smooth_one
#print axioms ZInQ.Manuscript.RC.J0Cusps.ationalPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.isCurve_of_point
#print axioms ZInQ.Manuscript.RC.J0Cusps.pointedSourceCurve
#print axioms ZInQ.Manuscript.RC.J0Cusps.basedJacobian
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveAbVar
#print axioms ZInQ.Manuscript.RC.J0Cusps.evalAway_mk
#print axioms ZInQ.Manuscript.RC.J0Cusps.chart_mem_iff
#print axioms ZInQ.Manuscript.RC.J0Cusps.evalZero_Y
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierstrassOrigin
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierstrassOrigin_point
#print axioms ZInQ.Manuscript.RC.J0Cusps.unique_over_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.zOpen_ne_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.ange_zOpen
#print axioms ZInQ.Manuscript.RC.J0Cusps.zRingMap_toRingHom
#print axioms ZInQ.Manuscript.RC.J0Cusps.value_ne_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_eq_zero_iff
#print axioms ZInQ.Manuscript.RC.J0Cusps.pointInZ_factor
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_bijective
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveGroup_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.vectorEval_coord
#print axioms ZInQ.Manuscript.RC.J0Cusps.evalAway_overlap
#print axioms ZInQ.Manuscript.RC.J0Cusps.vectorOnChart_independent
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_nonzero_coord
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveVectorPoint_left
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_vector_affine
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_vector_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.endsto_projectiveVectorPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.complexProjection_lift
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTorusValue_lift
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTorusValue_lift_of_eval
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_t2
#print axioms ZInQ.Manuscript.RC.J0Cusps.periodQuotient_compact
#print axioms ZInQ.Manuscript.RC.J0Cusps.pointVector_equation
#print axioms ZInQ.Manuscript.RC.J0Cusps.pointVector_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.pointVector_evaluates
#print axioms ZInQ.Manuscript.RC.J0Cusps.complexProjectiveValues_vector
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierPt_at_lattice
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierPt_off_lattice
#print axioms ZInQ.Manuscript.RC.J0Cusps.periodToProjective_continuous
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectivePeriodHomeomorph
#print axioms ZInQ.Manuscript.RC.J0Cusps.continuous_projectiveTorusValue
#print axioms ZInQ.Manuscript.RC.J0Cusps.interior
#print axioms ZInQ.Manuscript.RC.J0Cusps.branchComplex
#print axioms ZInQ.Manuscript.RC.J0Cusps.preimage_top_comp
#print axioms ZInQ.Manuscript.RC.J0Cusps.sectionField
#print axioms ZInQ.Manuscript.RC.J0Cusps.interiorSection
#print axioms ZInQ.Manuscript.RC.J0Cusps.egular_interiorSection
#print axioms ZInQ.Manuscript.RC.J0Cusps.chart_mem_of_regular
#print axioms ZInQ.Manuscript.RC.J0Cusps.eventually_chart_mem
#print axioms ZInQ.Manuscript.RC.J0Cusps.generic_hits_open
#print axioms ZInQ.Manuscript.RC.J0Cusps.chart_section_value
#print axioms ZInQ.Manuscript.RC.J0Cusps.sectionValue_comp
#print axioms ZInQ.Manuscript.RC.J0Cusps.sourceLimit_of_generator_expansions
#print axioms ZInQ.Manuscript.RC.J0Cusps.Qbar
#print axioms ZInQ.Manuscript.RC.J0Cusps.qbarToComplex
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_cusp_root
#print axioms ZInQ.Manuscript.RC.J0Cusps.qParam_level_pow
#print axioms ZInQ.Manuscript.RC.J0Cusps.hasSum_first
#print axioms ZInQ.Manuscript.RC.J0Cusps.second_form
#print axioms ZInQ.Manuscript.RC.J0Cusps.coeffMap_qExpand
#print axioms ZInQ.Manuscript.RC.J0Cusps.coeffMap_qTwist
#print axioms ZInQ.Manuscript.RC.J0Cusps.anslated_generator_expansions
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_algebraic_cusp_limit
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_primitive_triangular
#print axioms ZInQ.Manuscript.RC.J0Cusps.shortChange_eq
#print axioms ZInQ.Manuscript.RC.J0Cusps.lattice_discriminant
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierstrassCoordinates_nonsingular
#print axioms ZInQ.Manuscript.RC.J0Cusps.shortPointEquiv_toPoint
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierstrassPeriodEquiv
#print axioms ZInQ.Manuscript.RC.J0Cusps.weierstrassPeriodEquiv_mk
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCuspClass
#print axioms ZInQ.Manuscript.RC.J0Cusps.algebraicCuspClass_factors
#print axioms ZInQ.Manuscript.RC.J0Cusps.modularFactor
#print axioms ZInQ.Manuscript.RC.J0Cusps.modularFactor_isMonHom
#print axioms ZInQ.Manuscript.RC.J0Cusps.aj0_comp_modularFactor
#print axioms ZInQ.Manuscript.RC.J0Cusps.cusp_comparison
#print axioms ZInQ.Manuscript.RC.J0Cusps.weighted_comparison
#print axioms ZInQ.Manuscript.RC.J0Cusps.weighted_comparison_from_limits
#print axioms ZInQ.Manuscript.RC.TorusWeights.NormFactors.rightProduct
#print axioms ZInQ.Manuscript.RC.TorusWeights.SchwartzFactors.eval_order
#print axioms ZInQ.Manuscript.RC.TorusWeights.sign_square
#print axioms ZInQ.Manuscript.RC.TorusWeights.frame_transport
#print axioms ZInQ.Manuscript.RC.TorusWeights.us_character
#print axioms ZInQ.Manuscript.RC.TorusWeights.bit_transport
#print axioms ZInQ.Manuscript.RC.TorusWeights.actualWeights
#print axioms ZInQ.Manuscript.RC.TorusWeights.datumWeights
#print axioms ZInQ.Manuscript.RC.TorusWeights.localNrd
#print axioms ZInQ.Manuscript.RC.TorusWeights.NormFactors.onIntegralNorm
#print axioms ZInQ.Manuscript.RC.TorusWeights.descent_of_filter
#print axioms ZInQ.Manuscript.RC.X0Model3.affineEval
#print axioms ZInQ.Manuscript.RC.X0Model3.affineEval_factor
#print axioms ZInQ.Manuscript.RC.X0Model3.affineEval_congr
#print axioms ZInQ.Manuscript.RC.X0Model3.affineEval_injective
#print axioms ZInQ.Manuscript.RC.X0Model3.mem_basicOpen_iff_eval_ne_zero
#print axioms ZInQ.Manuscript.RC.X0Model3.finiteChart
#print axioms ZInQ.Manuscript.RC.X0Model3.finiteChart_affine
#print axioms ZInQ.Manuscript.RC.X0Model3.chart_mem_finiteChart
#print axioms ZInQ.Manuscript.RC.X0Model3.eventually_chart_mem
#print axioms ZInQ.Manuscript.RC.X0Model3.chartEval
#print axioms ZInQ.Manuscript.RC.X0Model3.chartEval_center
#print axioms ZInQ.Manuscript.RC.X0Model3.chartEval_at_mem
#print axioms ZInQ.Manuscript.RC.X0Model3.chartEval_local
#print axioms ZInQ.Manuscript.RC.X0Model3.chartEval_analyticAt
#print axioms ZInQ.Manuscript.RC.X0Model3.finitePointEval
#print axioms ZInQ.Manuscript.RC.X0Model3.finitePointEval_eq
#print axioms ZInQ.Manuscript.RC.X0Model3.exists_analyticJN_ratio
#print axioms ZInQ.Manuscript.RC.X0Model3.exists_stabilizer_germ_match
#print axioms ZInQ.Manuscript.RC.X0Model3.complexPoint_eq_iff
#print axioms ZInQ.Manuscript.RC.X0Model3.model
#print axioms ZInQ.Manuscript.RC.X0Model3.smooth_one
#print axioms ZInQ.Manuscript.RC.X0Model3.exists_etale_affine
#print axioms ZInQ.Manuscript.RC.X0Model3.etaleCoordinate_agree
#print axioms ZInQ.Manuscript.RC.X0Model3.j_not_eventually_constant
#print axioms ZInQ.Manuscript.RC.X0Model3.holomorphic_match
#print axioms ZInQ.Manuscript.RC.X0Model3.eventually_overlap_of_complexPoint_eq
#print axioms ZInQ.Manuscript.RC.X0Model3.projectiveValue_eq_of_complexPoint
#print axioms ZInQ.Manuscript.RC.X0Model3.datumReduction_projectiveValue
#print axioms ZInQ.Manuscript.RC.X0Model3.hpi_iff_specialize_projectiveValue
#print axioms ZInQ.Manuscript.RC.X0Model3.specialize_of_integral_extension
#print axioms ZInQ.Manuscript.RC.X0Model3.pairEval
#print axioms ZInQ.Manuscript.RC.X0Model3.pairEval_tmul
#print axioms ZInQ.Manuscript.RC.X0Model3.pairEval_self
#print axioms ZInQ.Manuscript.RC.X0Model3.continuousPairTest
#print axioms ZInQ.Manuscript.RC.X0Model3.eventually_eq_of_unramified
#print axioms ZInQ.Manuscript.RC.J0Cusps.hElkikMD_atScale
#print axioms ZInQ.Manuscript.RC.J0Cusps.additionShortChange_short
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_map
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_smul
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_equiv
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_equation
#print axioms ZInQ.Manuscript.RC.J0Cusps.nonsingular_of_equation_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.linearCoordinates_toAffine
#print axioms ZInQ.Manuscript.RC.J0Cusps.additionCoordinates_fields
#print axioms ZInQ.Manuscript.RC.J0Cusps.additionCoordinates_map
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_map
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_smul
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_comm
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_atInfinity
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_secant
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_opposite
#print axioms ZInQ.Manuscript.RC.J0Cusps.short_eqn_affine
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_dbl_affine
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_affine
#print axioms ZInQ.Manuscript.RC.J0Cusps.vector_atInfinity
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_eq_smul_add
#print axioms ZInQ.Manuscript.RC.J0Cusps.symmetricAddition_diagonal
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveNonsingular_ne_zero
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveAddition_cover
#print axioms ZInQ.Manuscript.RC.J0Cusps.schemeMapsToRat_unique
#print axioms ZInQ.Manuscript.RC.J0Cusps.overlapEq
#print axioms ZInQ.Manuscript.RC.J0Cusps.fieldPoint_lifts
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveMorphism_of_local
#print axioms ZInQ.Manuscript.RC.J0Cusps.equation_of_field_evaluations
#print axioms ZInQ.Manuscript.RC.J0Cusps.openLift_ring_map
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChart_covers
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveMorphism_of_formulas
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveUnit_value
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveHom_ext
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveHom_ext_value
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_reduced
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_product_reduced
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_square_reduced
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_unit_product_reduced
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveTarget_product_unit_reduced
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveGroupOfOperations
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_projectiveMultiplication
#print axioms ZInQ.Manuscript.RC.J0Cusps.exists_projectiveInversion
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveGroup_exists
#print axioms ZInQ.Manuscript.RC.J0Cusps.denominatorUnit_val
#print axioms ZInQ.Manuscript.RC.J0Cusps.chartFraction_val
#print axioms ZInQ.Manuscript.RC.J0Cusps.chartRatio_val
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChartRatio_self
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChart_dehomogenize
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChart_equation
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChart_ringHom_ext
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChartEval_ratio
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChartMorphism_map
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveEvalAway_fraction
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveEvalAway_overlap
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveChartMorphism_independent
#print axioms ZInQ.Manuscript.RC.J0Cusps.zChartInclusion_point_ne_origin
#print axioms ZInQ.Manuscript.RC.J0Cusps.chartCoord_mem_iff
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_chartMorphism
#print axioms ZInQ.Manuscript.RC.J0Cusps.projectiveValue_fromChart

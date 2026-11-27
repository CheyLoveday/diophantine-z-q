import ZInQKernel.Contrib.OneProof.RC.AppGCoarse.Intrinsic
import ZInQKernel.Contrib.OneProof.RC.AppGCoarse.Prepared
import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Assembly
import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Source
import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Types
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Assemble
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Constituents
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Descent
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Diamond
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Fourier
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Galois
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Sieve
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Window
import ZInQKernel.Contrib.OneProof.RC.CompanionUnit.Provider
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Birch
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Periods
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Prints
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.QuadraticFourier
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Reduction
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Compare
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Divided
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Place
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Realization
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Source
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.TwoTrace
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Valuation
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.BudgetBinding
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.KSplitBinding
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Place
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Producer
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Scalars
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Singleton
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Source
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Sources
import ZInQKernel.Contrib.OneProof.RC.EvenReading.DensityLeaf
import ZInQKernel.Contrib.OneProof.RC.EvenReading.Leaf
import ZInQKernel.Contrib.OneProof.RC.EvenReading.Normalization
import ZInQKernel.Contrib.OneProof.RC.EvenReading.Source
import ZInQKernel.Contrib.OneProof.RC.GaussSign.Congruence
import ZInQKernel.Contrib.OneProof.RC.GaussSign.Product
import ZInQKernel.Contrib.OneProof.RC.GaussSign.Roots
import ZInQKernel.Contrib.OneProof.RC.GaussSign.Sign
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Assembly
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Character
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Curve
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Forms
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Primitive
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Selector
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.StageSupport
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.AtScale
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Comparison
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Conductors
import ZInQKernel.Contrib.OneProof.RC.Intertwine.AdelicFourier
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Characters
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Comparison
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Cosets
import ZInQKernel.Contrib.OneProof.RC.Intertwine.FinitePlaces
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Fourier
import ZInQKernel.Contrib.OneProof.RC.Intertwine.Normalization
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Comparison
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Index
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Local
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Measure
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Operators
import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Alignment
import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Comparison
import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Source
import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Transport
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Density
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Fresh
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Seed
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Sieve
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Valuation
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Ambient
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Assembly
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.CompletedIntegers
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Conjugacy
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.QuadraticCompletion
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Realization
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.SplitRealization
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Torus
import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Fourier
import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Functions
import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Generators
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CentralCover
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CentralTensor
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonLocal
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonRectangular
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonSections
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Covariance
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.FiniteAssembly
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.FiniteSign
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Gaussian
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.IntegerLifts
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.IntegralAction
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Matrices
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.NormalForm
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Presentation
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Projective
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.RectangularRestriction
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Relations
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Restricted
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Sandwich
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.SignArithmetic
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.SignedRelations
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Spherical
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Splitting
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.TensorComparison
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.TensorFaithful
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.WeylRelations
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.AtScale
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Classification
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Compositum
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Cosets
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.CuspGrowth
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.FormalOrbit
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Interior
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.LevelOne
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Orbit
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.PrimitivePole
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.ProjectiveIdentity
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Cusps
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Degree
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Descent
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Equation
import ZInQKernel.Contrib.OneProof.RC.ModFnField.FieldMembership
import ZInQKernel.Contrib.OneProof.RC.ModFnField.FunctionField
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Infinity
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Laurent
import ZInQKernel.Contrib.OneProof.RC.ModFnField.RationalExpansion
import ZInQKernel.Contrib.OneProof.RC.ModFnField.RationalTaylor
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Tail
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Weierstrass
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Arithmetic
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Conjugacy
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Genus
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orbits
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orientation
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Reduction
import ZInQKernel.Contrib.OneProof.RC.O7Actual.SplitLocal
import ZInQKernel.Contrib.OneProof.RC.O7Actual.StageRead
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Actual
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Admissible
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Classify
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Coordinates
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Local
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.LocalArithmetic
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.MaximalSplit
import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Reference
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Coset
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Local
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Series
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Stage
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Transform
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Words
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Comparison
import ZInQKernel.Contrib.OneProof.RC.PMAdelic.Geometry
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.AffineComparison
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Algebraization
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Consumers
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Cusps
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.SchemeComparison
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.AtScale
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Cusps
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.RingValues
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.AdelicFactor
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Assembly
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.BasedFiber
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Grouped
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.IdeleClass
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.LocalConjugacy
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.OrbitQuotient
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.RationalCentralizer
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Realization
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Representatives
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.TorusComparison
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Consumers
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Descent
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Prints
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Fourier
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.LocalFactor
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Reference
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Stage
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Transport
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Unipotents
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Apply
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Detector
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Filter
import ZInQKernel.Contrib.OneProof.RC.StageJoin.Actual
import ZInQKernel.Contrib.OneProof.RC.StageJoin.Consumers
import ZInQKernel.Contrib.OneProof.RC.StageJoin.Sieve
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Actual
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Assemble
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Reference
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Selector
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Transport
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Wiring
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Character
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Forms
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Selector
import ZInQKernel.Contrib.OneProof.RC.TypeCoverage.Consumers
import ZInQKernel.Contrib.OneProof.RC.TypeCoverage.Coverage
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Actual
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Character
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Determinant
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Gauss
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Integral
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Local
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Product
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Real
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Reciprocity
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.ResidueHaar
import ZInQKernel.Contrib.OneProof.RC.X0Branch.AffineEval
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Overlap
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Unramified
import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart
import ZInQKernel.Contrib.OneProof.RC.X0Model.ComplexGerms
import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import ZInQKernel.Contrib.OneProof.RC.X0Model.Rational
import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import ZInQKernel.Contrib.OneProof.RC.X0Model.Specialization
import ZInQKernel.Contrib.OneProof.RC.X0Model2.BranchLabels
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam
import ZInQKernel.Contrib.OneProof.RC.X0Model2.JOrbit
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LatticeRigidity
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LaurentConvergence
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LocalSheets
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ModelOne
import ZInQKernel.Contrib.OneProof.RC.X0Model2.Projection
import ZInQKernel.Contrib.OneProof.RC.X0Model2.SectionExpansion
import ZInQKernel.Contrib.OneProof.ShimuraPointDictGerms
#print axioms ZInQ.Manuscript.RC.AppGCoarse.onFilter
#print axioms ZInQ.Manuscript.RC.AppGCoarse.coarse_on_filter
#print axioms ZInQ.Manuscript.RC.AppGCoarse.fixed_witness_on_filter
#print axioms ZInQ.Manuscript.RC.AppGCoarse.minimum_on_filter
#print axioms ZInQ.Manuscript.RC.AppGCoarse.depths_on_filter
#print axioms ZInQ.Manuscript.RC.AppGCoarse.restricted_minimum_iff
#print axioms ZInQ.Manuscript.RC.AppGCoarse.preparedSpec_of_intrinsic
#print axioms ZInQ.Manuscript.RC.AppGCoarse.depths_of_prepared_stages
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenAp
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.sievedCoeff
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.BudgetRealization
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.rules_and_seed
#print axioms ZInQ.Manuscript.RC.AuxInputs.SourceFamily
#print axioms ZInQ.Manuscript.RC.AuxInputs.sourceFamily_of_prints
#print axioms ZInQ.Manuscript.RC.AuxInputs.symbolFamily
#print axioms ZInQ.Manuscript.RC.AuxInputs.lstar_zero_of_noReference
#print axioms ZInQ.Manuscript.RC.AuxInputs.symbolFamily_rules
#print axioms ZInQ.Manuscript.RC.AuxInputs.symbolFamily_off
#print axioms ZInQ.Manuscript.RC.AuxInputs.symbolFamily_seed
#print axioms ZInQ.Manuscript.RC.AuxInputs.partitionCertificate
#print axioms ZInQ.Manuscript.RC.AuxInputs.withPartitionCertificate
#print axioms ZInQ.Manuscript.RC.AuxInputs.withPartitionCertificate_eq
#print axioms ZInQ.Manuscript.RC.AuxInputs.auxFactorInputs_of_realizations
#print axioms ZInQ.Manuscript.RC.AuxInputs.auxFactorInputs_of_compatible_partition
#print axioms ZInQ.Manuscript.RC.AuxInputs.auxFactor_of_realizations
#print axioms ZInQ.Manuscript.RC.AuxInputs.f3Target_of_realizations
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenFilter
#print axioms ZInQ.Manuscript.RC.AuxInputs.HasReference
#print axioms ZInQ.Manuscript.RC.AuxInputs.lstarTarget_of_normalization
#print axioms ZInQ.Manuscript.RC.AuxInputs.prepared_hasReference
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenSource_of_phase
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenSource_of_prints
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.reading
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.symbol
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.symbol_off
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.symbol_primeFactors
#print axioms ZInQ.Manuscript.RC.AuxInputs.EvenSource.unitSeed
#print axioms ZInQ.Manuscript.RC.AuxInputs.conductor
#print axioms ZInQ.Manuscript.RC.AuxInputs.conductor_pos
#print axioms ZInQ.Manuscript.RC.AuxInputs.eight_dvd_conductor
#print axioms ZInQ.Manuscript.RC.AuxInputs.conductor_support
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenSign
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenTypes
#print axioms ZInQ.Manuscript.RC.AuxInputs.evenTypes_sign
#print axioms ZInQ.Manuscript.RC.AuxInputs.quadratic_character_factors
#print axioms ZInQ.Manuscript.RC.AuxInputs.coprime_conductor
#print axioms ZInQ.Manuscript.RC.AuxInputs.total_of_good_primes
#print axioms ZInQ.Manuscript.RC.AuxInputs.good_primeFactors
#print axioms ZInQ.Manuscript.RC.AuxInputs.s0Filter_iff_type
#print axioms ZInQ.Manuscript.RC.BlocksPerU.realize_of_stage
#print axioms ZInQ.Manuscript.RC.BlocksPerU.IntrinsicGood
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.level
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.expansion
#print axioms ZInQ.Manuscript.RC.BlocksPerU.restrictSource
#print axioms ZInQ.Manuscript.RC.BlocksPerU.restrictSource_a
#print axioms ZInQ.Manuscript.RC.BlocksPerU.restrictSource_χ
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.baseAt
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.baseAt_a
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.baseAt_χ
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.toBasis
#print axioms ZInQ.Manuscript.RC.BlocksPerU.HasWeightTwoExpansion
#print axioms ZInQ.Manuscript.RC.BlocksPerU.SpansAt
#print axioms ZInQ.Manuscript.RC.BlocksPerU.coordinates_of_span
#print axioms ZInQ.Manuscript.RC.BlocksPerU.diamond_of_coordinates
#print axioms ZInQ.Manuscript.RC.BlocksPerU.SpansOverComplex
#print axioms ZInQ.Manuscript.RC.BlocksPerU.spansAt_of_complex
#print axioms ZInQ.Manuscript.RC.BlocksPerU.representative
#print axioms ZInQ.Manuscript.RC.BlocksPerU.representative_modEq
#print axioms ZInQ.Manuscript.RC.BlocksPerU.diamondCharacters
#print axioms ZInQ.Manuscript.RC.BlocksPerU.bCharacter
#print axioms ZInQ.Manuscript.RC.BlocksPerU.unaryCharacter
#print axioms ZInQ.Manuscript.RC.BlocksPerU.bCharacter_value
#print axioms ZInQ.Manuscript.RC.BlocksPerU.unaryCharacter_value
#print axioms ZInQ.Manuscript.RC.BlocksPerU.qExpansion_theta_product
#print axioms ZInQ.Manuscript.RC.BlocksPerU.weightTwoExpansion_of_halfIntegral
#print axioms ZInQ.Manuscript.RC.BlocksPerU.blockModularity_of_halfIntegral
#print axioms ZInQ.Manuscript.RC.BlocksPerU.GoodValues
#print axioms ZInQ.Manuscript.RC.BlocksPerU.UnramifiedAt
#print axioms ZInQ.Manuscript.RC.BlocksPerU.SourceAttachment.ofCusp
#print axioms ZInQ.Manuscript.RC.BlocksPerU.SourceAttachment.ofEis
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.sourceLevel_dvd
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.cusp_data
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.eis_data
#print axioms ZInQ.Manuscript.RC.BlocksPerU.Inventory.attachment
#print axioms ZInQ.Manuscript.RC.BlocksPerU.normalize_B
#print axioms ZInQ.Manuscript.RC.BlocksPerU.LevelSetup.old_dvd
#print axioms ZInQ.Manuscript.RC.BlocksPerU.OldStageLaw
#print axioms ZInQ.Manuscript.RC.BlocksPerU.MovingSieveLaw
#print axioms ZInQ.Manuscript.RC.BlocksPerU.UnaryStageLaw
#print axioms ZInQ.Manuscript.RC.BlocksPerU.blockModularity_of_stage
#print axioms ZInQ.Manuscript.RC.BlocksPerU.cuspNorm
#print axioms ZInQ.Manuscript.RC.BlocksPerU.thetaFun_holo
#print axioms ZInQ.Manuscript.RC.BlocksPerU.theta_product_slash
#print axioms ZInQ.Manuscript.RC.BlocksPerU.theta_product_modular
#print axioms ZInQ.Manuscript.RC.BlocksPerU.HasThreeHalvesExpansion
#print axioms ZInQ.Manuscript.RC.BlocksPerU.StageTernaryTransformation
#print axioms ZInQ.Manuscript.RC.BlocksPerU.LevelSetup.common_four
#print axioms ZInQ.Manuscript.RC.BlocksPerU.LevelSetup.test_coprime
#print axioms ZInQ.Manuscript.RC.BlocksPerU.LevelSetup.b_dvd
#print axioms ZInQ.Manuscript.RC.BlocksPerU.LevelSetup.unary_dvd
#print axioms ZInQ.Manuscript.RC.BlocksPerU.realize
#print axioms ZInQ.Manuscript.RC.CompanionUnit.levelPrimes
#print axioms ZInQ.Manuscript.RC.CompanionUnit.exclusions
#print axioms ZInQ.Manuscript.RC.CompanionUnit.finalSupport
#print axioms ZInQ.Manuscript.RC.CompanionUnit.NegativeFilter
#print axioms ZInQ.Manuscript.RC.CompanionUnit.two_mem_levelPrimes
#print axioms ZInQ.Manuscript.RC.CompanionUnit.signed_class_iff
#print axioms ZInQ.Manuscript.RC.CompanionUnit.negativeFilter_iff_oldRetained
#print axioms ZInQ.Manuscript.RC.CompanionUnit.rootNumberAt_newformLevel
#print axioms ZInQ.Manuscript.RC.CompanionUnit.oldSource_of_negative_reference
#print axioms ZInQ.Manuscript.RC.CompanionUnit.exists_negative_reference
#print axioms ZInQ.Manuscript.RC.CompanionUnit.exists_selection_of_source
#print axioms ZInQ.Manuscript.RC.CompanionUnit.exists_selection_of_prints
#print axioms ZInQ.Manuscript.RC.CompanionUnit.Selection.leaf_and_oldUnit
#print axioms ZInQ.Manuscript.RC.CompanionUnit.Selection.fresh_ramification
#print axioms ZInQ.Manuscript.RC.ElkikMD.quadraticCuspSum_eq_twisted_value
#print axioms ZInQ.Manuscript.RC.ElkikMD.cuspSymbol
#print axioms ZInQ.Manuscript.RC.ElkikMD.cuspSymbols_clear_denominator
#print axioms ZInQ.Manuscript.RC.ElkikMD.lval_eq_ofReal_re
#print axioms ZInQ.Manuscript.RC.ElkikMD.imaginaryLattice_generator
#print axioms ZInQ.Manuscript.RC.ElkikMD.quadraticCuspSum
#print axioms ZInQ.Manuscript.RC.ElkikMD.hElkikMD_of_cuspidalSubgroup
#print axioms ZInQ.Manuscript.RC.ElkikMD.ManinDrinfeld
#print axioms ZInQ.Manuscript.RC.ElkikMD.cuspidalImage_annihilator
#print axioms ZInQ.Manuscript.RC.ElkikMD.jacobiCharacter
#print axioms ZInQ.Manuscript.RC.ElkikMD.jacobiCharacter_intCast
#print axioms ZInQ.Manuscript.RC.ElkikMD.jacobiCharacter_isPrimitive
#print axioms ZInQ.Manuscript.RC.ElkikMD.jacobiCharacter_fourier
#print axioms ZInQ.Manuscript.RC.ElkikMD.chiD_eq_kronecker_pos
#print axioms ZInQ.Manuscript.RC.ElkikMD.genusPartner_twisted_coeff
#print axioms ZInQ.Manuscript.RC.ElkikMD.hElkikMD_of_maninDrinfeld
#print axioms ZInQ.Manuscript.RC.ElkikMD.curveNewform_eq_assemblyForm
#print axioms ZInQ.Manuscript.RC.ElkikMD.hElkikMD_of_assemblyForm
#print axioms ZInQ.Manuscript.RC.EvenBudget.map_rawNumerator_scaled
#print axioms ZInQ.Manuscript.RC.EvenBudget.halfDivided
#print axioms ZInQ.Manuscript.RC.EvenBudget.commonCoeff_complex
#print axioms ZInQ.Manuscript.RC.EvenBudget.commonCoeff_place
#print axioms ZInQ.Manuscript.RC.EvenBudget.unary_timesTheta_mem
#print axioms ZInQ.Manuscript.RC.EvenBudget.raw_bound
#print axioms ZInQ.Manuscript.RC.EvenBudget.raw_shell_bound
#print axioms ZInQ.Manuscript.RC.EvenBudget.scaled_witness
#print axioms ZInQ.Manuscript.RC.EvenBudget.normalized_double
#print axioms ZInQ.Manuscript.RC.EvenBudget.two_fresh_weight
#print axioms ZInQ.Manuscript.RC.EvenBudget.timesTheta_congr
#print axioms ZInQ.Manuscript.RC.EvenBudget.unaryCoeff
#print axioms ZInQ.Manuscript.RC.EvenBudget.rawNumerator
#print axioms ZInQ.Manuscript.RC.EvenBudget.rawNumerator_off
#print axioms ZInQ.Manuscript.RC.EvenBudget.rawNumerator_dvd
#print axioms ZInQ.Manuscript.RC.EvenBudget.dividedCoeff
#print axioms ZInQ.Manuscript.RC.EvenBudget.dividedCoeff_spec
#print axioms ZInQ.Manuscript.RC.EvenBudget.source_at_place_phase
#print axioms ZInQ.Manuscript.RC.EvenBudget.place_zero
#print axioms ZInQ.Manuscript.RC.EvenBudget.source_at_place_recur
#print axioms ZInQ.Manuscript.RC.EvenBudget.ap_mod_four
#print axioms ZInQ.Manuscript.RC.EvenBudget.source_at_place
#print axioms ZInQ.Manuscript.RC.EvenBudget.eta_phase_of_character
#print axioms ZInQ.Manuscript.RC.EvenBudget.TL_perm_primes
#print axioms ZInQ.Manuscript.RC.EvenBudget.Model
#print axioms ZInQ.Manuscript.RC.EvenBudget.evenH
#print axioms ZInQ.Manuscript.RC.EvenBudget.evenH_off
#print axioms ZInQ.Manuscript.RC.EvenBudget.evenH_two_fresh
#print axioms ZInQ.Manuscript.RC.EvenBudget.even_two_hecke
#print axioms ZInQ.Manuscript.RC.EvenBudget.even_source_symbol
#print axioms ZInQ.Manuscript.RC.EvenBudget.thetaDataOfEven
#print axioms ZInQ.Manuscript.RC.EvenBudget.budgetRealization_of_blocks
#print axioms ZInQ.Manuscript.RC.EvenBudget.good_iff
#print axioms ZInQ.Manuscript.RC.EvenBudget.fixed_support
#print axioms ZInQ.Manuscript.RC.EvenBudget.fresh_domains
#print axioms ZInQ.Manuscript.RC.EvenBudget.stationary_radicals
#print axioms ZInQ.Manuscript.RC.EvenBudget.keep_mul_sq
#print axioms ZInQ.Manuscript.RC.EvenBudget.squarefree_phase
#print axioms ZInQ.Manuscript.RC.EvenBudget.sieved_off_squarefree
#print axioms ZInQ.Manuscript.RC.EvenBudget.sieved_recurrence
#print axioms ZInQ.Manuscript.RC.EvenBudget.even_level_ne_zero
#print axioms ZInQ.Manuscript.RC.EvenBudget.sieved_mem_Qbar
#print axioms ZInQ.Manuscript.RC.EvenBudget.algebraicCoeff
#print axioms ZInQ.Manuscript.RC.EvenBudget.algebraicCoeff_complex
#print axioms ZInQ.Manuscript.RC.EvenBudget.two_trace_mem
#print axioms ZInQ.Manuscript.RC.EvenBudget.phase_rational_residue
#print axioms ZInQ.Manuscript.RC.EvenBudget.phase_rational_dvd
#print axioms ZInQ.Manuscript.RC.EvenPlace.phaseScalarsAt_of_order
#print axioms ZInQ.Manuscript.RC.EvenPlace.common_phase_scalars
#print axioms ZInQ.Manuscript.RC.EvenPlace.budget_shift_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.sourceAtPlace
#print axioms ZInQ.Manuscript.RC.EvenPlace.sourceAtPlace_eta_phase
#print axioms ZInQ.Manuscript.RC.EvenPlace.sourceAtPlace_exists
#print axioms ZInQ.Manuscript.RC.EvenPlace.singletonCoefficientsAt_of_shell
#print axioms ZInQ.Manuscript.RC.EvenPlace.common_place_for_sources
#print axioms ZInQ.Manuscript.RC.EvenPlace.kSplitSeed_of_trace_at_place
#print axioms ZInQ.Manuscript.RC.EvenPlace.PhaseField
#print axioms ZInQ.Manuscript.RC.EvenPlace.phaseField_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.place_exists
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.LocalField
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.LocalIntegers
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.complexIntegers
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.mem_complexIntegers_iff
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.root_mem_complexIntegers
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.odd_inv_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.half_not_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.padic
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.padicInt
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.padic_agree
#print axioms ZInQ.Manuscript.RC.EvenPlace.phaseData_forget_order
#print axioms ZInQ.Manuscript.RC.EvenPlace.phaseData_with_order_of_prints
#print axioms ZInQ.Manuscript.RC.EvenPlace.character_value_pow
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.character_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.fieldLift
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.fieldLift_complex
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.localLift
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.localLift_eq
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.localLift_pow
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.rat_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.scaled_phase_factor
#print axioms ZInQ.Manuscript.RC.EvenPlace.common_place_for_characters
#print axioms ZInQ.Manuscript.RC.EvenPlace.singleton_divisions
#print axioms ZInQ.Manuscript.RC.EvenPlace.singleton_of_shell
#print axioms ZInQ.Manuscript.RC.EvenPlace.all_mem_of_recurrence
#print axioms ZInQ.Manuscript.RC.EvenPlace.recur_scale
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.unshiftedLift
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.unshiftedLift_complex
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.unshiftedLift_local
#print axioms ZInQ.Manuscript.RC.EvenPlace.Place.source_shift_mem
#print axioms ZInQ.Manuscript.RC.EvenPlace.sourceHyp_of_complex
#print axioms ZInQ.Manuscript.RC.EvenPlace.evenSource_with_order_of_prints
#print axioms ZInQ.Manuscript.RC.EvenPlace.sourceFamily_with_order_of_prints
#print axioms ZInQ.Manuscript.RC.EvenPlace.genuineEvenSource_with_order_of_prints
#print axioms ZInQ.Manuscript.RC.EvenReading.evenFilter_of_genuineEven
#print axioms ZInQ.Manuscript.RC.EvenReading.genuineEvenSource_for_labels
#print axioms ZInQ.Manuscript.RC.EvenReading.AddressDensityLeafGenuineEven
#print axioms ZInQ.Manuscript.RC.EvenReading.addressDensityLeaf_of_genuineEven
#print axioms ZInQ.Manuscript.RC.EvenReading.freshPrime_of_support
#print axioms ZInQ.Manuscript.RC.EvenReading.omegaN_prod_primes
#print axioms ZInQ.Manuscript.RC.EvenReading.revGen_eq_one
#print axioms ZInQ.Manuscript.RC.EvenReading.genuineEvenSource_of_companion
#print axioms ZInQ.Manuscript.RC.EvenReading.lstar_eq_of_revGen
#print axioms ZInQ.Manuscript.RC.EvenReading.evenReading_of_genuineEven
#print axioms ZInQ.Manuscript.RC.EvenReading.transportedNormalization
#print axioms ZInQ.Manuscript.RC.EvenReading.exists_evenSupport
#print axioms ZInQ.Manuscript.RC.EvenReading.RevGen
#print axioms ZInQ.Manuscript.RC.EvenReading.genuineEvenSource_of_prints
#print axioms ZInQ.Manuscript.RC.GaussSign.squarePolynomial
#print axioms ZInQ.Manuscript.RC.GaussSign.oddProductPolynomial
#print axioms ZInQ.Manuscript.RC.GaussSign.eval_squarePolynomial_eq_of_sq
#print axioms ZInQ.Manuscript.RC.GaussSign.gaussGamma_eq_finiteGamma
#print axioms ZInQ.Manuscript.RC.GaussSign.gaussGamma_productFormula
#print axioms ZInQ.Manuscript.RC.GaussSign.gaussGamma_rectangular_products
#print axioms ZInQ.Manuscript.RC.GaussSign.eval_oddProduct_sq
#print axioms ZInQ.Manuscript.RC.GaussSign.negativeRoot
#print axioms ZInQ.Manuscript.RC.GaussSign.negativeRoot_primitive
#print axioms ZInQ.Manuscript.RC.GaussSign.eval_oddProduct_negativeRoot
#print axioms ZInQ.Manuscript.RC.GaussSign.oddGauss_one
#print axioms ZInQ.Manuscript.RC.Gz34Instance.instanceOfParamValues
#print axioms ZInQ.Manuscript.RC.Gz34Instance.gz34CompAt_of_paramValues
#print axioms ZInQ.Manuscript.RC.Gz34Instance.gz34Target_of_paramValues
#print axioms ZInQ.Manuscript.RC.Gz34Instance.exists_ringCharacter
#print axioms ZInQ.Manuscript.RC.Gz34Instance.curve_elliptic
#print axioms ZInQ.Manuscript.RC.Gz34Instance.curve_form
#print axioms ZInQ.Manuscript.RC.Gz34Instance.curve_level_support
#print axioms ZInQ.Manuscript.RC.Gz34Instance.curve_lattice
#print axioms ZInQ.Manuscript.RC.Gz34Instance.curve_scale
#print axioms ZInQ.Manuscript.RC.Gz34Instance.squareAt_of_padic
#print axioms ZInQ.Manuscript.RC.Gz34Instance.genusPartner_of_support
#print axioms ZInQ.Manuscript.RC.Gz34Instance.prepared_of_support
#print axioms ZInQ.Manuscript.RC.Gz34Instance.companion_of_rough
#print axioms ZInQ.Manuscript.RC.Gz34Instance.exists_ringHeegnerForm
#print axioms ZInQ.Manuscript.RC.Gz34Instance.companion_formConditions
#print axioms ZInQ.Manuscript.RC.Gz34Instance.exists_companion_form
#print axioms ZInQ.Manuscript.RC.Gz34Instance.ringCharacter_primitive
#print axioms ZInQ.Manuscript.RC.Gz34Instance.companionForm
#print axioms ZInQ.Manuscript.RC.Gz34Instance.RingParamValue
#print axioms ZInQ.Manuscript.RC.Gz34Instance.datumOfCompanion
#print axioms ZInQ.Manuscript.RC.Gz34Instance.selectGenus
#print axioms ZInQ.Manuscript.RC.Gz34Instance.selectRing
#print axioms ZInQ.Manuscript.RC.Gz34Instance.selectGenus_isSome
#print axioms ZInQ.Manuscript.RC.Gz34Instance.selectRing_isSome
#print axioms ZInQ.Manuscript.RC.Gz34Instance.filterInputs_of_stageSupport
#print axioms ZInQ.Manuscript.RC.HeegnerAnchor.cmPointsAtScale
#print axioms ZInQ.Manuscript.RC.HeegnerAnchor.genuineHeegnerAnchor
#print axioms ZInQ.Manuscript.RC.HeegnerAnchor.cmPointValue
#print axioms ZInQ.Manuscript.RC.HeegnerAnchor.conductorOrder_discr
#print axioms ZInQ.Manuscript.RC.HeegnerAnchor.conductorForm
#print axioms ZInQ.Manuscript.RC.Intertwine.integralAdeles_open
#print axioms ZInQ.Manuscript.RC.Intertwine.integralAdeles_compact
#print axioms ZInQ.Manuscript.RC.Intertwine.rectangular_open
#print axioms ZInQ.Manuscript.RC.Intertwine.rectangular_compact
#print axioms ZInQ.Manuscript.RC.Intertwine.rectangularCompacts
#print axioms ZInQ.Manuscript.RC.Intertwine.coordinateHaar
#print axioms ZInQ.Manuscript.RC.Intertwine.normalizedHaar
#print axioms ZInQ.Manuscript.RC.Intertwine.normalizedHaar_volume
#print axioms ZInQ.Manuscript.RC.Intertwine.continuous_finitePhase
#print axioms ZInQ.Manuscript.RC.Intertwine.integrable_latticeCharacter
#print axioms ZInQ.Manuscript.RC.Intertwine.adelic_annihilator_placewise
#print axioms ZInQ.Manuscript.RC.Intertwine.adelic_fourier
#print axioms ZInQ.Manuscript.RC.Intertwine.adelic_phase
#print axioms ZInQ.Manuscript.RC.Intertwine.adelic_comparison
#print axioms ZInQ.Manuscript.RC.Intertwine.adelic_pair_comparison
#print axioms ZInQ.Manuscript.RC.Intertwine.rationalPhase
#print axioms ZInQ.Manuscript.RC.Intertwine.rationalPhase_add
#print axioms ZInQ.Manuscript.RC.Intertwine.rationalPhase_eq_one
#print axioms ZInQ.Manuscript.RC.Intertwine.rationalPhase_congr
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase_spec
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase_add
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase_eq_one
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase_eq_product
#print axioms ZInQ.Manuscript.RC.Intertwine.representative
#print axioms ZInQ.Manuscript.RC.Intertwine.center
#print axioms ZInQ.Manuscript.RC.Intertwine.lattice
#print axioms ZInQ.Manuscript.RC.Intertwine.dual
#print axioms ZInQ.Manuscript.RC.Intertwine.quad
#print axioms ZInQ.Manuscript.RC.Intertwine.polar
#print axioms ZInQ.Manuscript.RC.Intertwine.center_mul
#print axioms ZInQ.Manuscript.RC.Intertwine.coset_dual
#print axioms ZInQ.Manuscript.RC.Intertwine.phase_on_coset
#print axioms ZInQ.Manuscript.RC.Intertwine.annihilator_iff
#print axioms ZInQ.Manuscript.RC.Intertwine.pairing_on_coset
#print axioms ZInQ.Manuscript.RC.Intertwine.common_weyl_scalar
#print axioms ZInQ.Manuscript.RC.Intertwine.generatorScalar
#print axioms ZInQ.Manuscript.RC.Intertwine.comparison
#print axioms ZInQ.Manuscript.RC.Intertwine.weighted_table_of_common_comparison
#print axioms ZInQ.Manuscript.RC.Intertwine.coset_exists
#print axioms ZInQ.Manuscript.RC.Intertwine.coset_unique
#print axioms ZInQ.Manuscript.RC.Intertwine.residue
#print axioms ZInQ.Manuscript.RC.Intertwine.residue_eq_some
#print axioms ZInQ.Manuscript.RC.Intertwine.residue_eq_none
#print axioms ZInQ.Manuscript.RC.Intertwine.J
#print axioms ZInQ.Manuscript.RC.Intertwine.J_injective
#print axioms ZInQ.Manuscript.RC.Intertwine.J_twist
#print axioms ZInQ.Manuscript.RC.Intertwine.Place
#print axioms ZInQ.Manuscript.RC.Intertwine.RationalFiniteAdeles
#print axioms ZInQ.Manuscript.RC.Intertwine.integralAdeles
#print axioms ZInQ.Manuscript.RC.Intertwine.rat_mem_at
#print axioms ZInQ.Manuscript.RC.Intertwine.diagonalRat
#print axioms ZInQ.Manuscript.RC.Intertwine.diagonal_apply
#print axioms ZInQ.Manuscript.RC.Intertwine.rational_integral
#print axioms ZInQ.Manuscript.RC.Intertwine.exists_local_fraction
#print axioms ZInQ.Manuscript.RC.Intertwine.prime_fraction_integral_elsewhere
#print axioms ZInQ.Manuscript.RC.Intertwine.localFraction
#print axioms ZInQ.Manuscript.RC.Intertwine.localFraction_spec
#print axioms ZInQ.Manuscript.RC.Intertwine.localFraction_elsewhere
#print axioms ZInQ.Manuscript.RC.Intertwine.sum_localFraction_spec
#print axioms ZInQ.Manuscript.RC.Intertwine.rationalFiniteModel
#print axioms ZInQ.Manuscript.RC.Intertwine.finitePhase_local_product
#print axioms ZInQ.Manuscript.RC.Intertwine.coset
#print axioms ZInQ.Manuscript.RC.Intertwine.latticeCharacter
#print axioms ZInQ.Manuscript.RC.Intertwine.polar_add
#print axioms ZInQ.Manuscript.RC.Intertwine.lattice_integral
#print axioms ZInQ.Manuscript.RC.Intertwine.integrable_coset
#print axioms ZInQ.Manuscript.RC.Intertwine.integrate_coset
#print axioms ZInQ.Manuscript.RC.Intertwine.J_mul_character
#print axioms ZInQ.Manuscript.RC.Intertwine.haarFourier
#print axioms ZInQ.Manuscript.RC.Intertwine.J_fourier
#print axioms ZInQ.Manuscript.RC.Intertwine.determinant
#print axioms ZInQ.Manuscript.RC.Intertwine.primeFactorPlace
#print axioms ZInQ.Manuscript.RC.Intertwine.badPlaces
#print axioms ZInQ.Manuscript.RC.Intertwine.localNorm
#print axioms ZInQ.Manuscript.RC.Intertwine.product_localNorm
#print axioms ZInQ.Manuscript.RC.Intertwine.localNorm_good
#print axioms ZInQ.Manuscript.RC.Intertwine.finiteVolume
#print axioms ZInQ.Manuscript.RC.Intertwine.finiteVolume_eq
#print axioms ZInQ.Manuscript.RC.Intertwine2.classDelta
#print axioms ZInQ.Manuscript.RC.Intertwine2.classDelta_eval
#print axioms ZInQ.Manuscript.RC.Intertwine2.GeneratorTensorAction
#print axioms ZInQ.Manuscript.RC.Intertwine2.generator_descriptions
#print axioms ZInQ.Manuscript.RC.Intertwine2.pair_of_tensor_generators
#print axioms ZInQ.Manuscript.RC.Intertwine2.FiniteIndexFamily
#print axioms ZInQ.Manuscript.RC.Intertwine2.rationalDiagonal
#print axioms ZInQ.Manuscript.RC.Intertwine2.realIndex
#print axioms ZInQ.Manuscript.RC.Intertwine2.indexAt
#print axioms ZInQ.Manuscript.RC.Intertwine2.finiteIndex
#print axioms ZInQ.Manuscript.RC.Intertwine2.WeilIndexProductFormula
#print axioms ZInQ.Manuscript.RC.Intertwine2.realIndex_positive_ternary
#print axioms ZInQ.Manuscript.RC.Intertwine2.realIndex_reference
#print axioms ZInQ.Manuscript.RC.Intertwine2.index_products
#print axioms ZInQ.Manuscript.RC.Intertwine2.localPhase
#print axioms ZInQ.Manuscript.RC.Intertwine2.localPhase_add
#print axioms ZInQ.Manuscript.RC.Intertwine2.localPhase_eq_one
#print axioms ZInQ.Manuscript.RC.Intertwine2.finitePhase_finprod
#print axioms ZInQ.Manuscript.RC.Intertwine2.localDual
#print axioms ZInQ.Manuscript.RC.Intertwine2.local_annihilator
#print axioms ZInQ.Manuscript.RC.Intertwine2.localCoset
#print axioms ZInQ.Manuscript.RC.Intertwine2.localUpper
#print axioms ZInQ.Manuscript.RC.Intertwine2.localFourier
#print axioms ZInQ.Manuscript.RC.Intertwine2.localFourier_coset
#print axioms ZInQ.Manuscript.RC.Intertwine2.FiniteVectors
#print axioms ZInQ.Manuscript.RC.Intertwine2.LocalVectors
#print axioms ZInQ.Manuscript.RC.Intertwine2.atPlace
#print axioms ZInQ.Manuscript.RC.Intertwine2.localLattice
#print axioms ZInQ.Manuscript.RC.Intertwine2.padicIntegers_compact
#print axioms ZInQ.Manuscript.RC.Intertwine2.padicIntegers_open
#print axioms ZInQ.Manuscript.RC.Intertwine2.localLattice_compact
#print axioms ZInQ.Manuscript.RC.Intertwine2.localLattice_open
#print axioms ZInQ.Manuscript.RC.Intertwine2.padicCompacts
#print axioms ZInQ.Manuscript.RC.Intertwine2.padicHaar
#print axioms ZInQ.Manuscript.RC.Intertwine2.localHaar
#print axioms ZInQ.Manuscript.RC.Intertwine2.localHaar_volume
#print axioms ZInQ.Manuscript.RC.Intertwine2.localHaar_volume_good
#print axioms ZInQ.Manuscript.RC.Intertwine2.rectangular_iff_local
#print axioms ZInQ.Manuscript.RC.Intertwine2.cylinderMass
#print axioms ZInQ.Manuscript.RC.Intertwine2.nuF
#print axioms ZInQ.Manuscript.RC.Intertwine2.cylinderMass_eq
#print axioms ZInQ.Manuscript.RC.Intertwine2.nuF_volume
#print axioms ZInQ.Manuscript.RC.Intertwine2.nuF_eq_normalizedHaar
#print axioms ZInQ.Manuscript.RC.Intertwine2.cosetIndicator
#print axioms ZInQ.Manuscript.RC.Intertwine2.cosetIndicator_tensor
#print axioms ZInQ.Manuscript.RC.Intertwine2.upper
#print axioms ZInQ.Manuscript.RC.Intertwine2.weyl
#print axioms ZInQ.Manuscript.RC.Intertwine2.upper_description
#print axioms ZInQ.Manuscript.RC.Intertwine2.weyl_description
#print axioms ZInQ.Manuscript.RC.Intertwine2.upper_tensor
#print axioms ZInQ.Manuscript.RC.Intertwine2.fourier_tensor
#print axioms ZInQ.Manuscript.RC.Intertwine2.weyl_tensor
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.mul_old_filter
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.coprime_of_new_support
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.old_transport_inputs
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.oldRetained
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.oldSource_of_phase
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.oldRetained_of_companion_avoidance
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.oldRetained_mul_of_new_filter
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.CompanionOldUnit
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.companionOldUnit_iff
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.exists_companionOldUnit
#print axioms ZInQ.Manuscript.RC.KSplitOldUnit.transported_lower_of_companion_old_unit
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenGood_iff
#print axioms ZInQ.Manuscript.RC.KSplitSeed.not_dvd_even_level
#print axioms ZInQ.Manuscript.RC.KSplitSeed.densityOfFiniteFields
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenDensityModels_of_constituent_fields
#print axioms ZInQ.Manuscript.RC.KSplitSeed.oddDensityModels_of_stage_fields
#print axioms ZInQ.Manuscript.RC.KSplitSeed.exists_fresh_trace_match
#print axioms ZInQ.Manuscript.RC.KSplitSeed.matched_product_in_filter
#print axioms ZInQ.Manuscript.RC.KSplitSeed.ratCast_pow_two_factor
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenCoeff_factor_of_no_reading
#print axioms ZInQ.Manuscript.RC.KSplitSeed.dirichletValue_unit_of_coprime
#print axioms ZInQ.Manuscript.RC.KSplitSeed.eight_dvd_of_trace_match
#print axioms ZInQ.Manuscript.RC.KSplitSeed.kSplitSeed_of_singleton_trace
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenUnitSieve
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenCoeff
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenCoeff_squarefree
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenCoeff_one
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenUnitSieve_mul_sq
#print axioms ZInQ.Manuscript.RC.KSplitSeed.evenCoeff_shell
#print axioms ZInQ.Manuscript.RC.KSplitSeed.transported_lower_of_old_unit
#print axioms ZInQ.Manuscript.RC.KSplitSeed.revGen_eq_one_iff
#print axioms ZInQ.Manuscript.RC.KSplitSeed.transport_valuation
#print axioms ZInQ.Manuscript.RC.KSplitSeed.revGen_empty
#print axioms ZInQ.Manuscript.RC.KSplitSeed.succ_le_padicValRat_of_revGen_zero
#print axioms ZInQ.Manuscript.RC.LocalTorus.local_reference_root
#print axioms ZInQ.Manuscript.RC.LocalTorus.split_reference
#print axioms ZInQ.Manuscript.RC.LocalTorus.picardFibers
#print axioms ZInQ.Manuscript.RC.LocalTorus.orbitFibers
#print axioms ZInQ.Manuscript.RC.LocalTorus.PlacesAbove
#print axioms ZInQ.Manuscript.RC.LocalTorus.dvd_of_local_valuation
#print axioms ZInQ.Manuscript.RC.LocalTorus.valuation_prime_lt_one
#print axioms ZInQ.Manuscript.RC.LocalTorus.completedScalar
#print axioms ZInQ.Manuscript.RC.LocalTorus.completedScalar_ratCast
#print axioms ZInQ.Manuscript.RC.LocalTorus.continuous_completedScalar
#print axioms ZInQ.Manuscript.RC.LocalTorus.completedScalar_mem
#print axioms ZInQ.Manuscript.RC.LocalTorus.denseRange_diagonal_integers
#print axioms ZInQ.Manuscript.RC.LocalTorus.local_centralizer_span
#print axioms ZInQ.Manuscript.RC.LocalTorus.split_ambient_conj
#print axioms ZInQ.Manuscript.RC.LocalTorus.division_ambient_conj
#print axioms ZInQ.Manuscript.RC.LocalTorus.AdicProduct
#print axioms ZInQ.Manuscript.RC.LocalTorus.generator
#print axioms ZInQ.Manuscript.RC.LocalTorus.affine_relation
#print axioms ZInQ.Manuscript.RC.LocalTorus.generator_linear_independent
#print axioms ZInQ.Manuscript.RC.LocalTorus.generator_rational_span
#print axioms ZInQ.Manuscript.RC.LocalTorus.affineEval
#print axioms ZInQ.Manuscript.RC.LocalTorus.affineEval_rat
#print axioms ZInQ.Manuscript.RC.LocalTorus.affineEval_mem_iff
#print axioms ZInQ.Manuscript.RC.LocalTorus.integral_eval_surjective
#print axioms ZInQ.Manuscript.RC.LocalTorus.eval_surjective
#print axioms ZInQ.Manuscript.RC.LocalTorus.eval_injective
#print axioms ZInQ.Manuscript.RC.LocalTorus.completedQuadratic
#print axioms ZInQ.Manuscript.RC.LocalTorus.completedQuadratic_apply
#print axioms ZInQ.Manuscript.RC.LocalTorus.realize_division
#print axioms ZInQ.Manuscript.RC.LocalTorus.hasLocalRealizations
#print axioms ZInQ.Manuscript.RC.LocalTorus.eq_of_two_distinct_bits
#print axioms ZInQ.Manuscript.RC.LocalTorus.conj_map_equiv
#print axioms ZInQ.Manuscript.RC.LocalTorus.realize_split
#print axioms ZInQ.Manuscript.RC.LocalTorus.localTorusChart
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle_volume
#print axioms ZInQ.Manuscript.RC.Metaplectic.gramUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic.dualScale
#print axioms ZInQ.Manuscript.RC.Metaplectic.dualScale_dualScale
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle_annihilator
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle_volume_mul_dual
#print axioms ZInQ.Manuscript.RC.Metaplectic.fourier_rectangle
#print axioms ZInQ.Manuscript.RC.Metaplectic.fourier_mem_and_sq
#print axioms ZInQ.Manuscript.RC.Metaplectic.fourier
#print axioms ZInQ.Manuscript.RC.Metaplectic.fourier_apply
#print axioms ZInQ.Manuscript.RC.Metaplectic.fourier_sq
#print axioms ZInQ.Manuscript.RC.Metaplectic.schwartzBruhat
#print axioms ZInQ.Manuscript.RC.Metaplectic.SchwartzBruhat
#print axioms ZInQ.Manuscript.RC.Metaplectic.isLocallyConstant_phase
#print axioms ZInQ.Manuscript.RC.Metaplectic.continuous_quad
#print axioms ZInQ.Manuscript.RC.Metaplectic.continuous_polar
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle
#print axioms ZInQ.Manuscript.RC.Metaplectic.mem_rectangle
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle_open
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangle_compact
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleCoset
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleCoset_open
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleCoset_compact
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleIndicator
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleIndicator_mem
#print axioms ZInQ.Manuscript.RC.Metaplectic.rectangleIndicator_one
#print axioms ZInQ.Manuscript.RC.Metaplectic.mem_span_rectangles
#print axioms ZInQ.Manuscript.RC.Metaplectic.upperUnipotent
#print axioms ZInQ.Manuscript.RC.Metaplectic.elementaryCoset
#print axioms ZInQ.Manuscript.RC.Metaplectic.upper_elementary
#print axioms ZInQ.Manuscript.RC.Metaplectic.gaussIndex
#print axioms ZInQ.Manuscript.RC.Metaplectic.weyl
#print axioms ZInQ.Manuscript.RC.Metaplectic.weyl_elementary
#print axioms ZInQ.Manuscript.RC.Metaplectic.weyl_elementary_value
#print axioms ZInQ.Manuscript.RC.Metaplectic.weyl_sq
#print axioms ZInQ.Manuscript.RC.Metaplectic2.Cover
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coverProjection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coverOperator
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coverLift
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coverProjection_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coverKernelElement
#print axioms ZInQ.Manuscript.RC.Metaplectic2.cover_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.cover_kernel_pair
#print axioms ZInQ.Manuscript.RC.Metaplectic2.cover_kernel_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.cover_of_relations
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restrictedAction_scalar
#print axioms ZInQ.Manuscript.RC.Metaplectic2.firstTensorAction_center
#print axioms ZInQ.Manuscript.RC.Metaplectic2.secondTensorAction_center
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonFirst
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSecond
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonFirst_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSecond_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.OperatorPair
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalScalar
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalScalar_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.negativeOperator
#print axioms ZInQ.Manuscript.RC.Metaplectic2.negativeOperator_apply
#print axioms ZInQ.Manuscript.RC.Metaplectic2.negativeOperator_not_fixed
#print axioms ZInQ.Manuscript.RC.Metaplectic2.negativeOperator_ne_one
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairProject
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairUpper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairDiagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairWeyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairProjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pairProjective_generators
#print axioms ZInQ.Manuscript.RC.Metaplectic2.LocalCommon
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localProjection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localOperators
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localFirst
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localSecond
#print axioms ZInQ.Manuscript.RC.Metaplectic2.liftUpper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.liftDiagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.liftWeyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localSign_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localSign_square
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localProjection_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localProjection_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.rectangularFirst
#print axioms ZInQ.Manuscript.RC.Metaplectic2.rectangularSecond
#print axioms ZInQ.Manuscript.RC.Metaplectic2.rectangular_first_tests
#print axioms ZInQ.Manuscript.RC.Metaplectic2.rectangular_second_tests
#print axioms ZInQ.Manuscript.RC.Metaplectic2.rectangular_sign_actions
#print axioms ZInQ.Manuscript.RC.Metaplectic2.common_rectangular_comparison
#print axioms ZInQ.Manuscript.RC.Metaplectic2.map_upperMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.map_diagonalMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.map_weylMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.Good
#print axioms ZInQ.Manuscript.RC.Metaplectic2.eventually_good
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSection_first
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSection_second
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSection_upper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonSection_weyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_dilation
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_diagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.sectionSubgroup
#print axioms ZInQ.Manuscript.RC.Metaplectic2.FiniteLocalCover
#print axioms ZInQ.Manuscript.RC.Metaplectic2.FiniteSL
#print axioms ZInQ.Manuscript.RC.Metaplectic2.sectionSubgroup_projection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.sectionSubgroup_fixes
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteProjection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteProjection_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.firstTuple
#print axioms ZInQ.Manuscript.RC.Metaplectic2.secondTuple
#print axioms ZInQ.Manuscript.RC.Metaplectic2.firstTensorAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.secondTensorAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.FiniteCenter
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteCenter_cases
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteCenter_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralScalar
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralScalar_finite
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralScalar_mul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralProduct
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralProduct_cases
#print axioms ZInQ.Manuscript.RC.Metaplectic2.singleSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.centralProduct_singleSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.neutralSigns
#print axioms ZInQ.Manuscript.RC.Metaplectic2.neutralSigns_le_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.FiniteCommon
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteQuotient
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonProjection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonProjection_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteSign_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.commonProjection_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.primeUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.vectorCutoff
#print axioms ZInQ.Manuscript.RC.Metaplectic2.mem_vectorCutoff
#print axioms ZInQ.Manuscript.RC.Metaplectic2.eventually_vectorCutoff
#print axioms ZInQ.Manuscript.RC.Metaplectic2.phase_sum
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gaussianCutoff
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gaussianCutoff_eventually
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerDiagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.IntegerCommon
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerProjection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerLiftFinite
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerProjection_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerSign_central
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerProjection_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerFirst
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerSecond
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerSign_actions
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerLiftStep
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerLiftStep_projection
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerLiftStep_first
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integerLiftStep_second
#print axioms ZInQ.Manuscript.RC.Metaplectic2.common_first_generatorTensorAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.common_second_generatorTensorAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.includeIntegral
#print axioms ZInQ.Manuscript.RC.Metaplectic2.local_integral_action
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upperMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weylMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalMatrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integral_generators
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.eval
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.matrix
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.open_entries
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.matrix_injective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.matrix_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.appendUpper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.appendDiagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.appendWeyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.eval_appendUpper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.eval_appendDiagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.eval_appendWeyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.NormalForm.representation_of_relations
#print axioms ZInQ.Manuscript.RC.Metaplectic2.LocalEnd
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upperUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilationUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourierUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weylUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coe_upperUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coe_diagonalUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.coe_weylUnit
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scalarSubgroup
#print axioms ZInQ.Manuscript.RC.Metaplectic2.ProjectiveOperators
#print axioms ZInQ.Manuscript.RC.Metaplectic2.project
#print axioms ZInQ.Manuscript.RC.Metaplectic2.local_projective_representation
#print axioms ZInQ.Manuscript.RC.Metaplectic2.GridImage
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridEmbedding
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridEvaluation
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridEmbedding_surjective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridEvaluation_injective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridEvaluation_embedding
#print axioms ZInQ.Manuscript.RC.Metaplectic2.grid_generator_preserves
#print axioms ZInQ.Manuscript.RC.Metaplectic2.grid_invariant
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restrictGridAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restricted_grid_tests
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upper_mul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upper_zero
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilationFactor
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pullback
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation_apply
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilationFactor_mul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation_one
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation_mul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation_neg_one
#print axioms ZInQ.Manuscript.RC.Metaplectic2.quad_scale
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localCoefficient
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localCoefficient_val
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex_one
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonalRatio
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal
#print axioms ZInQ.Manuscript.RC.Metaplectic2.dilation_upper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal_upper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal_one
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal_mul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex_inv
#print axioms ZInQ.Manuscript.RC.Metaplectic2.Elementary
#print axioms ZInQ.Manuscript.RC.Metaplectic2.replace
#print axioms ZInQ.Manuscript.RC.Metaplectic2.RestrictedTensor
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pure
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pure_add
#print axioms ZInQ.Manuscript.RC.Metaplectic2.pure_smul
#print axioms ZInQ.Manuscript.RC.Metaplectic2.tensorLift
#print axioms ZInQ.Manuscript.RC.Metaplectic2.tensorLift_pure
#print axioms ZInQ.Manuscript.RC.Metaplectic2.tensor_ext
#print axioms ZInQ.Manuscript.RC.Metaplectic2.stabilizes
#print axioms ZInQ.Manuscript.RC.Metaplectic2.RestrictedOperators
#print axioms ZInQ.Manuscript.RC.Metaplectic2.actFamily
#print axioms ZInQ.Manuscript.RC.Metaplectic2.act
#print axioms ZInQ.Manuscript.RC.Metaplectic2.act_pure
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restrictedAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluateFamily
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluate
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluate_pure
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluate_act
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upperTuple
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weylTuple
#print axioms ZInQ.Manuscript.RC.Metaplectic2.elementaryFamily
#print axioms ZInQ.Manuscript.RC.Metaplectic2.elementary_grid
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restricted_upper
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restricted_weyl
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_upper_kernel
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_upper_sandwich
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertExponent
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertSign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertSign_cases
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertExponent_double
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertExponent_mul_left
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteExponent_defect
#print axioms ZInQ.Manuscript.RC.Metaplectic2.hilbertExponent_comm
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteExponent_neg
#print axioms ZInQ.Manuscript.RC.Metaplectic2.finiteWeilIndexAxioms
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal_defect_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_square_defect_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_upper_defect_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.spherical_apply
#print axioms ZInQ.Manuscript.RC.Metaplectic2.spherical_ne_zero
#print axioms ZInQ.Manuscript.RC.Metaplectic2.upper_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.self_dual_lattice
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.index_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.diagonal_spherical
#print axioms ZInQ.Manuscript.RC.Metaplectic2.sphericalStabilizer
#print axioms ZInQ.Manuscript.RC.Metaplectic2.integral_spherical_section
#print axioms ZInQ.Manuscript.RC.Metaplectic2.localUnitAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.RestrictedUnits
#print axioms ZInQ.Manuscript.RC.Metaplectic2.forgetUnits
#print axioms ZInQ.Manuscript.RC.Metaplectic2.operatorStep
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridTensor
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridTensor_delta
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluate_gridTensor
#print axioms ZInQ.Manuscript.RC.Metaplectic2.gridTensor_injective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.restricted_generatorTensorAction
#print axioms ZInQ.Manuscript.RC.Metaplectic2.evaluate_injective
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_square
#print axioms ZInQ.Manuscript.RC.Metaplectic2.fourier_sandwich
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex_eighth
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_upper_cube
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_cube_scalar_is_sign
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_square_scalar
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_upper_bruhat
#print axioms ZInQ.Manuscript.RC.Metaplectic2.scaledIndex_fourth
#print axioms ZInQ.Manuscript.RC.Metaplectic2.weyl_upper_cube_at_two
#print axioms ZInQ.Manuscript.RC.ModFnClassify.algebraicParametrizationAtScale
#print axioms ZInQ.Manuscript.RC.ModFnClassify.curve_algebraicParametrizationAtScale
#print axioms ZInQ.Manuscript.RC.ModFnClassify.prepared_values
#print axioms ZInQ.Manuscript.RC.ModFnClassify.missing_values
#print axioms ZInQ.Manuscript.RC.ModFnClassify.oriented_cm_values
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jNFunction
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jNFunction_invariant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jN_translate_analytic
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGrowth_root_of_monic
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jN_translate_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.realizes_jN
#print axioms ZInQ.Manuscript.RC.ModFnClassify.complex_jN_minpoly_degree
#print axioms ZInQ.Manuscript.RC.ModFnClassify.complexCuspClassification
#print axioms ZInQ.Manuscript.RC.ModFnClassify.mem_adjoin_of_linear_degree_bound
#print axioms ZInQ.Manuscript.RC.ModFnClassify.LevelCosets
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cosetsToProjectiveLine
#print axioms ZInQ.Manuscript.RC.ModFnClassify.card_levelCosets_le
#print axioms ZInQ.Manuscript.RC.ModFnClassify.CuspGrowth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGerm_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGrowth_changeWidth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGrowth_const
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGrowth_mul
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGrowth_sub
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGerm_of_periodic_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.complexJField
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGerm_realizes
#print axioms ZInQ.Manuscript.RC.ModFnClassify.realizes_j
#print axioms ZInQ.Manuscript.RC.ModFnClassify.realizes_finsetSum
#print axioms ZInQ.Manuscript.RC.ModFnClassify.realizes_complexPolynomial
#print axioms ZInQ.Manuscript.RC.ModFnClassify.realizes_mem_complexJField
#print axioms ZInQ.Manuscript.RC.ModFnClassify.formal_degree_bound_of_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.formal_degree_bound
#print axioms ZInQ.Manuscript.RC.ModFnClassify.complexCusp_degree_bound
#print axioms ZInQ.Manuscript.RC.ModFnClassify.upperDomain
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jFunction
#print axioms ZInQ.Manuscript.RC.ModFnClassify.isCompact_truncatedFundamentalDomain
#print axioms ZInQ.Manuscript.RC.ModFnClassify.finite_bad_in_fd
#print axioms ZInQ.Manuscript.RC.ModFnClassify.LevelOneInvariant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.jFunction_invariant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.invariant_order
#print axioms ZInQ.Manuscript.RC.ModFnClassify.clear_interior_poles
#print axioms ZInQ.Manuscript.RC.ModFnClassify.CuspGerm
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGerm_analytic_tail
#print axioms ZInQ.Manuscript.RC.ModFnClassify.j_cusp_unit
#print axioms ZInQ.Manuscript.RC.ModFnClassify.levelOne_polynomial_of_cleared_cusp
#print axioms ZInQ.Manuscript.RC.ModFnClassify.levelOne_rational_in_j
#print axioms ZInQ.Manuscript.RC.ModFnClassify.LevelInvariant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.permuteCosets
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitValue
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitValue_permute
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitPoly
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitPoly_invariant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitPoly_root
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitPoly_monic_degree
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitCoefficient_cusp_of_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.cuspGerm_translates_analytic_growth
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitCoefficient_cusp
#print axioms ZInQ.Manuscript.RC.ModFnClassify.orbitCoefficient_rational_in_j
#print axioms ZInQ.Manuscript.RC.ModFnClassify.scaledPrimitive_not_constant
#print axioms ZInQ.Manuscript.RC.ModFnClassify.xCoordinate_no_analytic_germ_at_lattice
#print axioms ZInQ.Manuscript.RC.ModFnClassify.qParam_one_zpow
#print axioms ZInQ.Manuscript.RC.ModFnClassify.evalSection_ZOverY_at_identity
#print axioms ZInQ.Manuscript.RC.ModFnClassify.pullback_expansion
#print axioms ZInQ.Manuscript.RC.ModFnClassify.projective_identity_iff_lattice
#print axioms ZInQ.Manuscript.RC.ModFnClassify.projectiveValue_on_affine
#print axioms ZInQ.Manuscript.RC.ModFnClassify.projective_value_of_expansions
#print axioms ZInQ.Manuscript.RC.ModFnField.translatedLevel
#print axioms ZInQ.Manuscript.RC.ModFnField.scaledPrimitive_cusp
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_cusp_meromorphic
#print axioms ZInQ.Manuscript.RC.ModFnField.integral_degree_of_orbit_product
#print axioms ZInQ.Manuscript.RC.ModFnField.intermediateField_eq_top_of_degree_bound
#print axioms ZInQ.Manuscript.RC.ModFnField.complexify
#print axioms ZInQ.Manuscript.RC.ModFnField.complexify_coeff
#print axioms ZInQ.Manuscript.RC.ModFnField.mem_rat_adjoin_of_complexify_mem
#print axioms ZInQ.Manuscript.RC.ModFnField.modularFunctionField_descent
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes.const
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes.add
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes.mul
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes.pow
#print axioms ZInQ.Manuscript.RC.ModFnField.Realizes.eq_of_eventuallyEq
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_laurent_equation
#print axioms ZInQ.Manuscript.RC.ModFnField.ComplexCuspClassification
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_in_modularFunctionField_with_equation
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_in_modularFunctionField
#print axioms ZInQ.Manuscript.RC.ModFnField.fieldHom_of_transcendental_point
#print axioms ZInQ.Manuscript.RC.ModFnField.functionField_coordinates
#print axioms ZInQ.Manuscript.RC.ModFnField.dominant_morphism_of_classification
#print axioms ZInQ.Manuscript.RC.ModFnField.primitive_rationalTaylor
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_rationalTaylor
#print axioms ZInQ.Manuscript.RC.ModFnField.hasSum_laurent_shift
#print axioms ZInQ.Manuscript.RC.ModFnField.meromorphicAt_hasSum_laurent
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_cusp_hasSum
#print axioms ZInQ.Manuscript.RC.ModFnField.rationalLaurent_of_cleared
#print axioms ZInQ.Manuscript.RC.ModFnField.coordinates_rationalLaurent
#print axioms ZInQ.Manuscript.RC.ModFnField.rationalConstants
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.const
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.id_zero
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.add
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.sub
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.mul
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.pow
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.comp
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.inv
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.deriv
#print axioms ZInQ.Manuscript.RC.ModFnField.RationalTaylor.factor_at_zero
#print axioms ZInQ.Manuscript.RC.ModFnField.laurent_unique_of_tail
#print axioms ZInQ.Manuscript.RC.ModFnField.hasSum_mul_of_tail
#print axioms ZInQ.Manuscript.RC.ModFnField.regularPart
#print axioms ZInQ.Manuscript.RC.ModFnField.weierstrassP_split
#print axioms ZInQ.Manuscript.RC.ModFnField.derivWeierstrassP_split
#print axioms ZInQ.Manuscript.RC.ModFnField.regularPart_derivatives_rational
#print axioms ZInQ.Manuscript.RC.O7Actual.quadratic_parameter_le
#print axioms ZInQ.Manuscript.RC.O7Actual.quadratic_norm_one
#print axioms ZInQ.Manuscript.RC.O7Actual.classOrder
#print axioms ZInQ.Manuscript.RC.O7Actual.HalfIntegral
#print axioms ZInQ.Manuscript.RC.O7Actual.exists_basisHom
#print axioms ZInQ.Manuscript.RC.O7Actual.halfIntegral_of_basisHom
#print axioms ZInQ.Manuscript.RC.O7Actual.order_isIntegral
#print axioms ZInQ.Manuscript.RC.O7Actual.optimal_of_maps_integers
#print axioms ZInQ.Manuscript.RC.O7Actual.twoPower_mul
#print axioms ZInQ.Manuscript.RC.O7Actual.unit_of_twoPower
#print axioms ZInQ.Manuscript.RC.O7Actual.ring_two
#print axioms ZInQ.Manuscript.RC.O7Actual.actualVisibility
#print axioms ZInQ.Manuscript.RC.O7Actual.stageStabilizer
#print axioms ZInQ.Manuscript.RC.O7Actual.actual_stabilizer
#print axioms ZInQ.Manuscript.RC.O7Actual.TorusWeights.phase
#print axioms ZInQ.Manuscript.RC.O7Actual.TorusWeights.weight
#print axioms ZInQ.Manuscript.RC.O7Actual.TorusWeights.phase_unit
#print axioms ZInQ.Manuscript.RC.O7Actual.orbitWeight
#print axioms ZInQ.Manuscript.RC.O7Actual.Normalizers.orientation
#print axioms ZInQ.Manuscript.RC.O7Actual.comparisonInputs
#print axioms ZInQ.Manuscript.RC.O7Actual.actual_representative
#print axioms ZInQ.Manuscript.RC.O7Actual.rational_conjugacy
#print axioms ZInQ.Manuscript.RC.O7Actual.OptimalAt
#print axioms ZInQ.Manuscript.RC.O7Actual.halfIntegral_iff_optimal
#print axioms ZInQ.Manuscript.RC.O7Actual.supp_iff_optimal_on_sphere
#print axioms ZInQ.Manuscript.RC.O7Actual.Voight1467VToIII
#print axioms ZInQ.Manuscript.RC.O7Actual.classG_norm_one
#print axioms ZInQ.Manuscript.RC.O7Actual.centralizer_span
#print axioms ZInQ.Manuscript.RC.O7Actual.basis_norm
#print axioms ZInQ.Manuscript.RC.O7Actual.optimal_commuting_unit_sign
#print axioms ZInQ.Manuscript.RC.O7Actual.StageAt.visibility
#print axioms ZInQ.Manuscript.RC.O7Actual.classOrder_mem_adelic
#print axioms ZInQ.Manuscript.RC.O7Actual.IntegralSupport.classGroup
#print axioms ZInQ.Manuscript.RC.O7Actual.IntegralSupport.stabilizer
#print axioms ZInQ.Manuscript.RC.O7Actual.DatumAt.representative
#print axioms ZInQ.Manuscript.RC.O7Actual.DatumAt.inputs
#print axioms ZInQ.Manuscript.RC.O7Actual.thetaComparison_actual
#print axioms ZInQ.Manuscript.RC.O7Actual.NormCharacterDescent
#print axioms ZInQ.Manuscript.RC.O7Actual.norm_character_self_prime
#print axioms ZInQ.Manuscript.RC.O7Actual.norm_character_self_ideal
#print axioms ZInQ.Manuscript.RC.O7Actual.normCharacterDescent_self
#print axioms ZInQ.Manuscript.RC.O7Actual.OrbitSet
#print axioms ZInQ.Manuscript.RC.O7Actual.OrbitFibers.param
#print axioms ZInQ.Manuscript.RC.O7Actual.doubleCoset_restrict
#print axioms ZInQ.Manuscript.RC.O7Actual.doubleCoset_orbitEquiv
#print axioms ZInQ.Manuscript.RC.O7Actual.torsor_weight
#print axioms ZInQ.Manuscript.RC.O7Actual.Orientations
#print axioms ZInQ.Manuscript.RC.O7Actual.card_orientations
#print axioms ZInQ.Manuscript.RC.O7Actual.flip
#print axioms ZInQ.Manuscript.RC.O7Actual.bit_induction
#print axioms ZInQ.Manuscript.RC.O7Actual.cancel_edge_sign
#print axioms ZInQ.Manuscript.RC.O7Actual.orientation_sum
#print axioms ZInQ.Manuscript.RC.O7Actual.atkin_edge
#print axioms ZInQ.Manuscript.RC.O7Actual.uniformizer_edge
#print axioms ZInQ.Manuscript.RC.O7Actual.cj_reference_class
#print axioms ZInQ.Manuscript.RC.O7Actual.cj_lamOf_reduction
#print axioms ZInQ.Manuscript.RC.O7Actual.firstProjector
#print axioms ZInQ.Manuscript.RC.O7Actual.projector_first_normalForm
#print axioms ZInQ.Manuscript.RC.O7Actual.projector_forms_distinct
#print axioms ZInQ.Manuscript.RC.O7Actual.projector_two_normalForms
#print axioms ZInQ.Manuscript.RC.O7Actual.levelRoot_projector_normalForm
#print axioms ZInQ.Manuscript.RC.O7Actual.card_residue_embeddings
#print axioms ZInQ.Manuscript.RC.O7Actual.actual_reference_read
#print axioms ZInQ.Manuscript.RC.O7Orbits.ActualOrder
#print axioms ZInQ.Manuscript.RC.O7Orbits.index
#print axioms ZInQ.Manuscript.RC.O7Orbits.disc
#print axioms ZInQ.Manuscript.RC.O7Orbits.ActualSupport
#print axioms ZInQ.Manuscript.RC.O7Orbits.SupportBridge
#print axioms ZInQ.Manuscript.RC.O7Orbits.SupportBridge.half
#print axioms ZInQ.Manuscript.RC.O7Orbits.integralSupport
#print axioms ZInQ.Manuscript.RC.O7Orbits.actualSupport_iff_optimal
#print axioms ZInQ.Manuscript.RC.O7Orbits.splitOrderChart
#print axioms ZInQ.Manuscript.RC.O7Orbits.divisionOrderChart
#print axioms ZInQ.Manuscript.RC.O7Orbits.unitConjRing
#print axioms ZInQ.Manuscript.RC.O7Orbits.unitConjRing_apply
#print axioms ZInQ.Manuscript.RC.O7Orbits.unitConjRing_map
#print axioms ZInQ.Manuscript.RC.O7Orbits.unitConjRing_mul
#print axioms ZInQ.Manuscript.RC.O7Orbits.localGenerator
#print axioms ZInQ.Manuscript.RC.O7Orbits.localGenerator_spec
#print axioms ZInQ.Manuscript.RC.O7Orbits.localClassUnit_mem
#print axioms ZInQ.Manuscript.RC.O7Orbits.conjugateSupport
#print axioms ZInQ.Manuscript.RC.O7Orbits.localGenerator_conj
#print axioms ZInQ.Manuscript.RC.O7Orbits.residue_eq_of_unitConj
#print axioms ZInQ.Manuscript.RC.O7Orbits.residueBit
#print axioms ZInQ.Manuscript.RC.O7Orbits.levelPrime
#print axioms ZInQ.Manuscript.RC.O7Orbits.levelPrime_ne_detecting
#print axioms ZInQ.Manuscript.RC.O7Orbits.generatorOrientation
#print axioms ZInQ.Manuscript.RC.O7Orbits.orientation
#print axioms ZInQ.Manuscript.RC.O7Orbits.PicardFibers
#print axioms ZInQ.Manuscript.RC.O7Orbits.orbitFibers
#print axioms ZInQ.Manuscript.RC.O7Orbits.quadratic_hom_conj_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.levelPrime_exp
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_branch_of_splitsIn
#print axioms ZInQ.Manuscript.RC.O7Orbits.level_bit_of_filter
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_bit_of_filter
#print axioms ZInQ.Manuscript.RC.O7Orbits.residueBit_swap_ne
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_level_residue_cases
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_level_bit_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_bit_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.actual_level_bit_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.divisionGenerator
#print axioms ZInQ.Manuscript.RC.O7Orbits.divisionGenerator_square
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_red_ne_zero_of_sq
#print axioms ZInQ.Manuscript.RC.O7Orbits.generatorOrientation_last
#print axioms ZInQ.Manuscript.RC.O7Orbits.actual_division_bit_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.actual_maximal_split_normalForm
#print axioms ZInQ.Manuscript.RC.O7Orbits.splitOrderChart_compatible
#print axioms ZInQ.Manuscript.RC.O7Orbits.localGenerator_square
#print axioms ZInQ.Manuscript.RC.O7Orbits.matrix_trace_det_of_affine
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_generator_trace_det
#print axioms ZInQ.Manuscript.RC.O7Orbits.UnitConj
#print axioms ZInQ.Manuscript.RC.O7Orbits.unitConj_iff_level_of_projectors
#print axioms ZInQ.Manuscript.RC.O7Orbits.projector_recovers
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_level_conj_iff
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_level_labels
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_conj_iff_red
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_labels
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_branch_of_residue
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_branch_odd
#print axioms ZInQ.Manuscript.RC.O7Orbits.split_branch_two
#print axioms ZInQ.Manuscript.RC.O7Orbits.division_root_exists
#print axioms ZInQ.Manuscript.RC.O7Orbits.padic_prime_sq_not_dvd
#print axioms ZInQ.Manuscript.RC.O7Orbits.cyclicColumns
#print axioms ZInQ.Manuscript.RC.O7Orbits.exists_cyclicColumns
#print axioms ZInQ.Manuscript.RC.O7Orbits.cyclicColumns_companion
#print axioms ZInQ.Manuscript.RC.O7Orbits.maximal_split_normalForm
#print axioms ZInQ.Manuscript.RC.O7Orbits.detecting_nonsquare
#print axioms ZInQ.Manuscript.RC.O7Orbits.padic_nonsquare_of_residue
#print axioms ZInQ.Manuscript.RC.O7Orbits.tensor_isField_of_nonsquare
#print axioms ZInQ.Manuscript.RC.O7Orbits.exists_reference_embedding
#print axioms ZInQ.Manuscript.RC.OldStageLaw.kernel
#print axioms ZInQ.Manuscript.RC.OldStageLaw.line
#print axioms ZInQ.Manuscript.RC.OldStageLaw.line_hasSum
#print axioms ZInQ.Manuscript.RC.OldStageLaw.line_holo
#print axioms ZInQ.Manuscript.RC.OldStageLaw.line_inversion
#print axioms ZInQ.Manuscript.RC.OldStageLaw.cosetSum
#print axioms ZInQ.Manuscript.RC.OldStageLaw.cosetSum_holo
#print axioms ZInQ.Manuscript.RC.OldStageLaw.cosetSum_inversion
#print axioms ZInQ.Manuscript.RC.OldStageLaw.Grid
#print axioms ZInQ.Manuscript.RC.OldStageLaw.offset
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta
#print axioms ZInQ.Manuscript.RC.OldStageLaw.energy
#print axioms ZInQ.Manuscript.RC.OldStageLaw.twist
#print axioms ZInQ.Manuscript.RC.OldStageLaw.pairing
#print axioms ZInQ.Manuscript.RC.OldStageLaw.finiteFourier
#print axioms ZInQ.Manuscript.RC.OldStageLaw.inversionFactor
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_holo
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_translate
#print axioms ZInQ.Manuscript.RC.OldStageLaw.twist_eq_of_integral
#print axioms ZInQ.Manuscript.RC.OldStageLaw.intResidues
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_inversion
#print axioms ZInQ.Manuscript.RC.OldStageLaw.pairing_add_left
#print axioms ZInQ.Manuscript.RC.OldStageLaw.finiteFourier_zero_of_translate
#print axioms ZInQ.Manuscript.RC.OldStageLaw.twist_finiteFourier_eq
#print axioms ZInQ.Manuscript.RC.OldStageLaw.extracted_unit_action
#print axioms ZInQ.Manuscript.RC.OldStageLaw.diagonal_factorization
#print axioms ZInQ.Manuscript.RC.OldStageLaw.extracted_reciprocity
#print axioms ZInQ.Manuscript.RC.OldStageLaw.GridPoint
#print axioms ZInQ.Manuscript.RC.OldStageLaw.intCoords
#print axioms ZInQ.Manuscript.RC.OldStageLaw.exponent
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_hasSum
#print axioms ZInQ.Manuscript.RC.OldStageLaw.kernel_nat
#print axioms ZInQ.Manuscript.RC.OldStageLaw.coord
#print axioms ZInQ.Manuscript.RC.OldStageLaw.quatPoint
#print axioms ZInQ.Manuscript.RC.OldStageLaw.mass
#print axioms ZInQ.Manuscript.RC.OldStageLaw.stageWeight
#print axioms ZInQ.Manuscript.RC.OldStageLaw.stageGridWeight
#print axioms ZInQ.Manuscript.RC.OldStageLaw.stageGrid_twist_eq
#print axioms ZInQ.Manuscript.RC.OldStageLaw.stageGrid_hasSum
#print axioms ZInQ.Manuscript.RC.OldStageLaw.oldStageLaw_of_finiteAction
#print axioms ZInQ.Manuscript.RC.OldStageLaw.referenceForm
#print axioms ZInQ.Manuscript.RC.OldStageLaw.referenceWeight
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_reference
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_scale
#print axioms ZInQ.Manuscript.RC.OldStageLaw.RelativeFiniteAction
#print axioms ZInQ.Manuscript.RC.OldStageLaw.halfIntegral_of_finiteAction
#print axioms ZInQ.Manuscript.RC.OldStageLaw.Step.matrix
#print axioms ZInQ.Manuscript.RC.OldStageLaw.wordMatrix
#print axioms ZInQ.Manuscript.RC.OldStageLaw.wordAction
#print axioms ZInQ.Manuscript.RC.OldStageLaw.wordFactor
#print axioms ZInQ.Manuscript.RC.OldStageLaw.exists_word
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_word
#print axioms ZInQ.Manuscript.RC.OldStageLaw.norm_wordFactor
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_bounded
#print axioms ZInQ.Manuscript.RC.OldStageLaw.gridTheta_cusps
#print axioms ZInQ.Manuscript.RC.PMAdelic.adelic
#print axioms ZInQ.Manuscript.RC.PMAdelic.neighbourMultiset_eq
#print axioms ZInQ.Manuscript.RC.PMAdelic.atkinOnDoubleCosets
#print axioms ZInQ.Manuscript.RC.PMAdelic.uniformizerOnDoubleCosets
#print axioms ZInQ.Manuscript.RC.PMAdelic.JetchevKane.idealClasses
#print axioms ZInQ.Manuscript.RC.PMAdelic.JetchevKane.hecke_compare
#print axioms ZInQ.Manuscript.RC.PMAdelic.JetchevKane.atkin_compare
#print axioms ZInQ.Manuscript.RC.PMAdelic.JetchevKane.frobenius_compare
#print axioms ZInQ.Manuscript.RC.PMAdelic.JetchevKane.frobenius_ss
#print axioms ZInQ.Manuscript.RC.PMAdelic.geometricInput
#print axioms ZInQ.Manuscript.RC.PMAdelic.geometry
#print axioms ZInQ.Manuscript.RC.ParamAtScale.sectionYOverZ
#print axioms ZInQ.Manuscript.RC.ParamAtScale.projFunctionFieldEquiv_sectionYOverZ
#print axioms ZInQ.Manuscript.RC.ParamAtScale.affine_germ_agreement_of_expansions
#print axioms ZInQ.Manuscript.RC.ParamAtScale.model_dimension
#print axioms ZInQ.Manuscript.RC.ParamAtScale.morphism_of_functionField
#print axioms ZInQ.Manuscript.RC.ParamAtScale.prepared_and_missing_at_scale
#print axioms ZInQ.Manuscript.RC.ParamAtScale.oriented_cm_values_at_scale
#print axioms ZInQ.Manuscript.RC.ParamAtScale.scaledPrimitive
#print axioms ZInQ.Manuscript.RC.ParamAtScale.xCoordinate
#print axioms ZInQ.Manuscript.RC.ParamAtScale.yCoordinate
#print axioms ZInQ.Manuscript.RC.ParamAtScale.scaledPrimitive_analytic
#print axioms ZInQ.Manuscript.RC.ParamAtScale.rational_primitive_hasSum
#print axioms ZInQ.Manuscript.RC.ParamAtScale.coordinates_meromorphic
#print axioms ZInQ.Manuscript.RC.ParamAtScale.coordinates_equation
#print axioms ZInQ.Manuscript.RC.ParamAtScale.coordinates_smul
#print axioms ZInQ.Manuscript.RC.ParamAtScale.section_meromorphic_germ
#print axioms ZInQ.Manuscript.RC.ParamAtScale.torusValue
#print axioms ZInQ.Manuscript.RC.ParamAtScale.torusValue_smul
#print axioms ZInQ.Manuscript.RC.ParamAtScale.torusValue_tendsto_infty
#print axioms ZInQ.Manuscript.RC.ParamAtScale.torusValue_tendsto_cusp
#print axioms ZInQ.Manuscript.RC.ParamAtScale.rational_cusp_comparison
#print axioms ZInQ.Manuscript.RC.ParamAtScale.evalSection_comp
#print axioms ZInQ.Manuscript.RC.ParamAtScale.germToFunctionField_pullback
#print axioms ZInQ.Manuscript.RC.ParamJoin.genus_values
#print axioms ZInQ.Manuscript.RC.ParamJoin.gz34CompAt
#print axioms ZInQ.Manuscript.RC.ParamJoin.algebraicParametrizationAtScale
#print axioms ZInQ.Manuscript.RC.ParamJoin.prepared_values
#print axioms ZInQ.Manuscript.RC.ParamJoin.missing_values
#print axioms ZInQ.Manuscript.RC.ParamJoin.algebraicParametrizationAtScale_and_cuspLimits
#print axioms ZInQ.Manuscript.RC.ParamJoin.ring_values
#print axioms ZInQ.Manuscript.RC.PicardFibers.transportedUnit
#print axioms ZInQ.Manuscript.RC.PicardFibers.adelicCentralizer
#print axioms ZInQ.Manuscript.RC.PicardFibers.adelic_factor_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.AdmissibleD.disc_neg
#print axioms ZInQ.Manuscript.RC.PicardFibers.referenceAffine
#print axioms ZInQ.Manuscript.RC.PicardFibers.referenceUnit
#print axioms ZInQ.Manuscript.RC.PicardFibers.referenceAffine_spec
#print axioms ZInQ.Manuscript.RC.PicardFibers.referenceUnit_sphere
#print axioms ZInQ.Manuscript.RC.PicardFibers.picardFibers_of_local
#print axioms ZInQ.Manuscript.RC.PicardFibers.orbitFibers_of_local
#print axioms ZInQ.Manuscript.RC.PicardFibers.diagonalCentralizer
#print axioms ZInQ.Manuscript.RC.PicardFibers.diagonalCentralizer_le
#print axioms ZInQ.Manuscript.RC.PicardFibers.centralizer_mul_admissible
#print axioms ZInQ.Manuscript.RC.PicardFibers.basedFiberEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.picardFibers_of_comparison
#print axioms ZInQ.Manuscript.RC.PicardFibers.blockIntegral
#print axioms ZInQ.Manuscript.RC.PicardFibers.regroup
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalPrimeUnder
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalPrimeUnder_finite
#print axioms ZInQ.Manuscript.RC.PicardFibers.GroupedLocalUnits
#print axioms ZInQ.Manuscript.RC.PicardFibers.groupedIntegral
#print axioms ZInQ.Manuscript.RC.PicardFibers.GroupedIdeles
#print axioms ZInQ.Manuscript.RC.PicardFibers.groupIdeles
#print axioms ZInQ.Manuscript.RC.PicardFibers.groupIdeles_apply
#print axioms ZInQ.Manuscript.RC.PicardFibers.mem_ker_ideleToIdeal_iff_grouped
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalPrime
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalPrimeEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleExponent
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleExponent_eq_zero_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleExponent_mul
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleExponent_cofinite
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleToIdeal
#print axioms ZInQ.Manuscript.RC.PicardFibers.count_ideleToIdeal
#print axioms ZInQ.Manuscript.RC.PicardFibers.mem_ker_ideleToIdeal
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleToIdeal_surjective
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleToIdeal_diagonal
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleClassSubgroup
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleClassMap
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleClassMap_surjective
#print axioms ZInQ.Manuscript.RC.PicardFibers.ker_ideleClassMap
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleClassEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.AdmissibleD.mod_eight
#print axioms ZInQ.Manuscript.RC.PicardFibers.AdmissibleD.disc_squarefree
#print axioms ZInQ.Manuscript.RC.PicardFibers.actual_local_conj_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.reframe
#print axioms ZInQ.Manuscript.RC.PicardFibers.actual_orientation_factor_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleOrbitEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalCentralizer
#print axioms ZInQ.Manuscript.RC.PicardFibers.rationalCentralizer_eq_range
#print axioms ZInQ.Manuscript.RC.PicardFibers.levelBit
#print axioms ZInQ.Manuscript.RC.PicardFibers.divisionBit
#print axioms ZInQ.Manuscript.RC.PicardFibers.LabelAt
#print axioms ZInQ.Manuscript.RC.PicardFibers.HasLocalRealizations
#print axioms ZInQ.Manuscript.RC.PicardFibers.realize_tuple
#print axioms ZInQ.Manuscript.RC.PicardFibers.AdelicAdmissible
#print axioms ZInQ.Manuscript.RC.PicardFibers.patch_admissible_adele
#print axioms ZInQ.Manuscript.RC.PicardFibers.local_mem_conj_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.adelicClass
#print axioms ZInQ.Manuscript.RC.PicardFibers.exists_frame
#print axioms ZInQ.Manuscript.RC.PicardFibers.supportFromFrame
#print axioms ZInQ.Manuscript.RC.PicardFibers.orbitFromRep
#print axioms ZInQ.Manuscript.RC.PicardFibers.orbitFromRep_eq_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.orbitFromRep_surjective
#print axioms ZInQ.Manuscript.RC.PicardFibers.orbitFromRep_orientation_iff
#print axioms ZInQ.Manuscript.RC.PicardFibers.primeBelow
#print axioms ZInQ.Manuscript.RC.PicardFibers.PrimeBlock
#print axioms ZInQ.Manuscript.RC.PicardFibers.primeBlockIntegral
#print axioms ZInQ.Manuscript.RC.PicardFibers.PrimeBlocks
#print axioms ZInQ.Manuscript.RC.PicardFibers.idelePrimeBlocks
#print axioms ZInQ.Manuscript.RC.PicardFibers.blocksCentralizerEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleCentralizerEquiv
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleCentralizerEquiv_diagonal
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleCentralizerEquiv_integral
#print axioms ZInQ.Manuscript.RC.PicardFibers.ideleCentralizerEquiv_rational
#print axioms ZInQ.Manuscript.RC.PreparedParam.genusParamValues
#print axioms ZInQ.Manuscript.RC.PreparedParam.missingParamValues
#print axioms ZInQ.Manuscript.RC.PreparedParam.gz34CompAt_of_scaledParametrization
#print axioms ZInQ.Manuscript.RC.PreparedParam.value_of_cmFieldOfDefinition
#print axioms ZInQ.Manuscript.RC.PreparedParam.preparedParamValues
#print axioms ZInQ.Manuscript.RC.PreparedParam.projectiveOverQ
#print axioms ZInQ.Manuscript.RC.PreparedParam.projectiveValue
#print axioms ZInQ.Manuscript.RC.PreparedParam.projectiveValue_map
#print axioms ZInQ.Manuscript.RC.PreparedParam.AlgebraicParametrizationAtScale
#print axioms ZInQ.Manuscript.RC.PreparedParam.FieldPoint
#print axioms ZInQ.Manuscript.RC.PreparedParam.FieldPoint.map
#print axioms ZInQ.Manuscript.RC.PreparedParam.FieldPoint.comp
#print axioms ZInQ.Manuscript.RC.PreparedParam.FieldPoint.evalSection
#print axioms ZInQ.Manuscript.RC.PreparedParam.CMFieldOfDefinition
#print axioms ZInQ.Manuscript.RC.RelativeAction.finiteFourier_sq
#print axioms ZInQ.Manuscript.RC.RelativeAction.finiteFourier_four
#print axioms ZInQ.Manuscript.RC.RelativeAction.conjugate_fixes
#print axioms ZInQ.Manuscript.RC.RelativeAction.triangular_pair
#print axioms ZInQ.Manuscript.RC.RelativeAction.conjugate_lower_matrix
#print axioms ZInQ.Manuscript.RC.RelativeAction.fixes_of_generators
#print axioms ZInQ.Manuscript.RC.RelativeAction.spherical_pair
#print axioms ZInQ.Manuscript.RC.RelativeAction.extracted_unit_cell
#print axioms ZInQ.Manuscript.RC.RelativeAction.inverse_upper_left
#print axioms ZInQ.Manuscript.RC.RelativeAction.positive_odd_representative
#print axioms ZInQ.Manuscript.RC.RelativeAction.extracted_squarefree_symbols
#print axioms ZInQ.Manuscript.RC.RelativeAction.extracted_product_scalar
#print axioms ZInQ.Manuscript.RC.RelativeAction.reference_word
#print axioms ZInQ.Manuscript.RC.RelativeAction.stageGrid_paired_upper
#print axioms ZInQ.Manuscript.RC.RelativeAction.stageGrid_paired_lower
#print axioms ZInQ.Manuscript.RC.RelativeAction.extendCosets
#print axioms ZInQ.Manuscript.RC.RelativeAction.extendCosets_injective
#print axioms ZInQ.Manuscript.RC.RelativeAction.extendCosets_twist
#print axioms ZInQ.Manuscript.RC.RelativeAction.IntertwinesGenerators
#print axioms ZInQ.Manuscript.RC.RelativeAction.inverseLiftWord
#print axioms ZInQ.Manuscript.RC.RelativeAction.inverseLiftWord_projects
#print axioms ZInQ.Manuscript.RC.RelativeAction.intertwines_word
#print axioms ZInQ.Manuscript.RC.RelativeAction.paired_of_lifted_eigen
#print axioms ZInQ.Manuscript.RC.RelativeAction.product_eigen
#print axioms ZInQ.Manuscript.RC.RelativeAction.twist_finiteFourier_reference
#print axioms ZInQ.Manuscript.RC.RelativeAction.lowerWord
#print axioms ZInQ.Manuscript.RC.RelativeAction.lowerWord_matrix
#print axioms ZInQ.Manuscript.RC.RelativeAction.lowerWord_fixes
#print axioms ZInQ.Manuscript.RC.RelativeAction.lowerWord_fixes_iff
#print axioms ZInQ.Manuscript.RC.RelativeAction.lowerWord_reference
#print axioms ZInQ.Manuscript.RC.RelativeAction.twist_reference
#print axioms ZInQ.Manuscript.RC.RelativeAction.PairedActionAt
#print axioms ZInQ.Manuscript.RC.RelativeAction.paired_upper
#print axioms ZInQ.Manuscript.RC.RelativeAction.paired_lower
#print axioms ZInQ.Manuscript.RC.RelativeAction.paired_neg_one
#print axioms ZInQ.Manuscript.RC.RelativeAction.matrix_append
#print axioms ZInQ.Manuscript.RC.RelativeAction.action_append
#print axioms ZInQ.Manuscript.RC.RelativeAction.action_smul
#print axioms ZInQ.Manuscript.RC.RelativeAction.PairedActionAt.append
#print axioms ZInQ.Manuscript.RC.StageIdent.level_eq
#print axioms ZInQ.Manuscript.RC.StageIdent.detectorAt
#print axioms ZInQ.Manuscript.RC.StageIdent.detectorAt_lam
#print axioms ZInQ.Manuscript.RC.StageIdent.pmStage_parameters
#print axioms ZInQ.Manuscript.RC.StageIdent.pmStage_weight
#print axioms ZInQ.Manuscript.RC.StageIdent.inputs_of_selected
#print axioms ZInQ.Manuscript.RC.StageIdent.reducedEquation
#print axioms ZInQ.Manuscript.RC.StageIdent.reducedEquation_elliptic
#print axioms ZInQ.Manuscript.RC.StageIdent.finiteRow_fixed_of_agree
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedCurve_elliptic
#print axioms ZInQ.Manuscript.RC.StageIdent.residueAt
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedEvaluation
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedEvaluation_lam
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedCurveOn_elliptic
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedEvaluationOn
#print axioms ZInQ.Manuscript.RC.StageIdent.selectedEvaluationOn_lam
#print axioms ZInQ.Manuscript.RC.StageIdent.sourceFilter
#print axioms ZInQ.Manuscript.RC.StageIdent.stageTest_not_dvd
#print axioms ZInQ.Manuscript.RC.StageIdent.labelsAtStages
#print axioms ZInQ.Manuscript.RC.StageIdent.labelsAtStages_prime_precision
#print axioms ZInQ.Manuscript.RC.StageIdent.sourceFilter_eq
#print axioms ZInQ.Manuscript.RC.StageIdent.bad_mem_support
#print axioms ZInQ.Manuscript.RC.StageIdent.support_dvd_type
#print axioms ZInQ.Manuscript.RC.StageIdent.pmLocal_base_support
#print axioms ZInQ.Manuscript.RC.StageIdent.rodd_atStage
#print axioms ZInQ.Manuscript.RC.StageIdent.reading_budget
#print axioms ZInQ.Manuscript.RC.StageJoin.Scoeff
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedStage
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedSource
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedLift
#print axioms ZInQ.Manuscript.RC.StageJoin.pmStage_good_outside
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedStage_good_iff
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedStage_good
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedStage_aθ
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedLift_aθ
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSievedLift_support
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSieved_parameters
#print axioms ZInQ.Manuscript.RC.StageJoin.pmSieved_newformLevel
#print axioms ZInQ.Manuscript.RC.StageJoin.coefficientSupport_pm
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedType
#print axioms ZInQ.Manuscript.RC.StageJoin.labelRefinedType
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedChar
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedType_primeFactors
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedChar_spec
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedType_stage_good
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedWindow
#print axioms ZInQ.Manuscript.RC.StageJoin.refined_fresh_domains
#print axioms ZInQ.Manuscript.RC.StageJoin.refined_old_good
#print axioms ZInQ.Manuscript.RC.StageJoin.refinedLevelSetup
#print axioms ZInQ.Manuscript.RC.StageJoin.refined_test_coprime_common
#print axioms ZInQ.Manuscript.RC.StageJoin.LateSieve.Keep
#print axioms ZInQ.Manuscript.RC.StageJoin.LateSieve.KeepNorm
#print axioms ZInQ.Manuscript.RC.StageJoin.keepNorm_extract
#print axioms ZInQ.Manuscript.RC.StageJoin.sieveStage
#print axioms ZInQ.Manuscript.RC.StageJoin.sieveStage_aθ
#print axioms ZInQ.Manuscript.RC.StageJoin.sieveLift
#print axioms ZInQ.Manuscript.RC.StageJoin.sieveLift_aθ
#print axioms ZInQ.Manuscript.RC.StageJoin.SievedSource.stage
#print axioms ZInQ.Manuscript.RC.StageJoin.SievedSource.lift
#print axioms ZInQ.Manuscript.RC.StageKummer.RingClassAt
#print axioms ZInQ.Manuscript.RC.StageKummer.complexAlgebraic
#print axioms ZInQ.Manuscript.RC.StageKummer.witnessComplex
#print axioms ZInQ.Manuscript.RC.StageKummer.witnessEmbeddings
#print axioms ZInQ.Manuscript.RC.StageKummer.witnessEmbeddings_at_witness
#print axioms ZInQ.Manuscript.RC.StageKummer.anchoredEmbeddings_complex
#print axioms ZInQ.Manuscript.RC.StageKummer.datumPlace
#print axioms ZInQ.Manuscript.RC.StageKummer.datumPlace_under
#print axioms ZInQ.Manuscript.RC.StageKummer.datumPlace_liesOver
#print axioms ZInQ.Manuscript.RC.StageKummer.datumReduction_eq
#print axioms ZInQ.Manuscript.RC.StageKummer.datumReduction_witness
#print axioms ZInQ.Manuscript.RC.StageKummer.ev_eq_comp
#print axioms ZInQ.Manuscript.RC.StageKummer.witness_detector
#print axioms ZInQ.Manuscript.RC.StageKummer.formOnModel
#print axioms ZInQ.Manuscript.RC.StageKummer.datumOnModel
#print axioms ZInQ.Manuscript.RC.StageKummer.selectorOnModel
#print axioms ZInQ.Manuscript.RC.StageKummer.evOnModel
#print axioms ZInQ.Manuscript.RC.StageKummer.selectorOnModel_some
#print axioms ZInQ.Manuscript.RC.StageKummer.lamOf_onModel
#print axioms ZInQ.Manuscript.RC.StageKummer.stageGood
#print axioms ZInQ.Manuscript.RC.StageKummer.datumPlaceOn
#print axioms ZInQ.Manuscript.RC.StageKummer.evActual
#print axioms ZInQ.Manuscript.RC.StageKummer.evActual_off_support
#print axioms ZInQ.Manuscript.RC.StageKummer.evActual_witness
#print axioms ZInQ.Manuscript.RC.StageKummer.phaseAt
#print axioms ZInQ.Manuscript.RC.StageKummer.phaseAt_eq
#print axioms ZInQ.Manuscript.RC.StageKummer.thetaSide
#print axioms ZInQ.Manuscript.RC.StageKummer.toOddStagedInstanceOfReference
#print axioms ZInQ.Manuscript.RC.StageKummer.ArtinMatch
#print axioms ZInQ.Manuscript.RC.StageKummer.place
#print axioms ZInQ.Manuscript.RC.StageKummer.detector
#print axioms ZInQ.Manuscript.RC.StageKummer.detector_lam
#print axioms ZInQ.Manuscript.RC.StageKummer.chosenDatum
#print axioms ZInQ.Manuscript.RC.StageKummer.chosenDatumPlace
#print axioms ZInQ.Manuscript.RC.StageKummer.goodAt
#print axioms ZInQ.Manuscript.RC.StageKummer.reduceDatum
#print axioms ZInQ.Manuscript.RC.StageKummer.hev_at
#print axioms ZInQ.Manuscript.RC.StageKummer.reference_reduction
#print axioms ZInQ.Manuscript.RC.StageKummer.stage_mod_four
#print axioms ZInQ.Manuscript.RC.StageKummer.level
#print axioms ZInQ.Manuscript.RC.StageKummer.referenceStage
#print axioms ZInQ.Manuscript.RC.StageKummer.datumAt
#print axioms ZInQ.Manuscript.RC.StageKummer.positiveLevel
#print axioms ZInQ.Manuscript.RC.StageKummer.preparedGlue
#print axioms ZInQ.Manuscript.RC.StageKummer.MissingParamValues
#print axioms ZInQ.Manuscript.RC.StageKummer.extendedSelector
#print axioms ZInQ.Manuscript.RC.StageKummer.selected_of_admissible
#print axioms ZInQ.Manuscript.RC.StageKummer.withExtendedIndex
#print axioms ZInQ.Manuscript.RC.StageKummer.extendedIndex_at_simpleZero
#print axioms ZInQ.Manuscript.RC.StageKummer.extendedGenus
#print axioms ZInQ.Manuscript.RC.StageKummer.extendedSetup
#print axioms ZInQ.Manuscript.RC.StageKummer.extendedSetup_ev
#print axioms ZInQ.Manuscript.RC.StageKummer.datumComposite
#print axioms ZInQ.Manuscript.RC.StageKummer.evActual_eq_comp
#print axioms ZInQ.Manuscript.RC.StageKummer.Setup.embeddings
#print axioms ZInQ.Manuscript.RC.StageKummer.Setup.ev
#print axioms ZInQ.Manuscript.RC.StageKummer.Setup.hev
#print axioms ZInQ.Manuscript.RC.StageKummer.Setup.stageTest_of_admissible
#print axioms ZInQ.Manuscript.RC.StageKummer.Setup.toOddStagedInstance
#print axioms ZInQ.Manuscript.RC.StageSelector.sqrt_mem_conductorOne
#print axioms ZInQ.Manuscript.RC.StageSelector.exists_genusCharacter
#print axioms ZInQ.Manuscript.RC.StageSelector.prepared_discriminant
#print axioms ZInQ.Manuscript.RC.StageSelector.qsqrt_discr
#print axioms ZInQ.Manuscript.RC.StageSelector.exists_heegnerForm
#print axioms ZInQ.Manuscript.RC.StageSelector.formAtLevel
#print axioms ZInQ.Manuscript.RC.StageSelector.PreparedParamValue
#print axioms ZInQ.Manuscript.RC.StageSelector.datumOfPrepared
#print axioms ZInQ.Manuscript.RC.StageSelector.extendSelG
#print axioms ZInQ.Manuscript.RC.StageSelector.extendSelG_eq_some
#print axioms ZInQ.Manuscript.RC.StageSelector.extendSelG_witness
#print axioms ZInQ.Manuscript.RC.StageSelector.extendSelG_isSome_of_admissible
#print axioms ZInQ.Manuscript.RC.StageSelector.exists_selected_of_admissible
#print axioms ZInQ.Manuscript.RC.StageSelector.jgen_extendSelG_at_simpleZero
#print axioms ZInQ.Manuscript.RC.StageSelector.preparedGlue_of_withStages
#print axioms ZInQ.Manuscript.RC.TypeCoverage.fresh_outside_support
#print axioms ZInQ.Manuscript.RC.TypeCoverage.old_good
#print axioms ZInQ.Manuscript.RC.TypeCoverage.test_coprime_old
#print axioms ZInQ.Manuscript.RC.TypeCoverage.levelSetup
#print axioms ZInQ.Manuscript.RC.TypeCoverage.test_coprime_common
#print axioms ZInQ.Manuscript.RC.TypeCoverage.inertiaOn_of_atLevel
#print axioms ZInQ.Manuscript.RC.TypeCoverage.window_hseed
#print axioms ZInQ.Manuscript.RC.TypeCoverage.window_hexcl
#print axioms ZInQ.Manuscript.RC.TypeCoverage.unchanged_char_cannot_detect
#print axioms ZInQ.Manuscript.RC.TypeCoverage.coefficientSupport
#print axioms ZInQ.Manuscript.RC.TypeCoverage.extraSupport
#print axioms ZInQ.Manuscript.RC.TypeCoverage.fixedModulus
#print axioms ZInQ.Manuscript.RC.TypeCoverage.mem_coefficientSupport
#print axioms ZInQ.Manuscript.RC.TypeCoverage.prime_of_mem_coefficientSupport
#print axioms ZInQ.Manuscript.RC.TypeCoverage.dvd_fixedModulus
#print axioms ZInQ.Manuscript.RC.TypeCoverage.fixedModulus_pos
#print axioms ZInQ.Manuscript.RC.TypeCoverage.moving_coprime
#print axioms ZInQ.Manuscript.RC.TypeCoverage.coveredType
#print axioms ZInQ.Manuscript.RC.TypeCoverage.coveredType_primeFactors
#print axioms ZInQ.Manuscript.RC.TypeCoverage.good_not_mem_support
#print axioms ZInQ.Manuscript.RC.TypeCoverage.good_iff_old_good_and_outside
#print axioms ZInQ.Manuscript.RC.TypeCoverage.stage_good
#print axioms ZInQ.Manuscript.RC.TypeCoverage.projectType
#print axioms ZInQ.Manuscript.RC.TypeCoverage.project_type_of_good
#print axioms ZInQ.Manuscript.RC.TypeCoverage.project_sign
#print axioms ZInQ.Manuscript.RC.TypeCoverage.project_realization
#print axioms ZInQ.Manuscript.RC.TypeCoverage.coveredChar
#print axioms ZInQ.Manuscript.RC.TypeCoverage.isTypeChar_covered
#print axioms ZInQ.Manuscript.RC.TypeCoverage.project_coveredChar
#print axioms ZInQ.Manuscript.RC.TypeCoverage.openTypeKernel_covered
#print axioms ZInQ.Manuscript.RC.TypeCoverage.detects_radicals_covered
#print axioms ZInQ.Manuscript.RC.TypeCoverage.exists_good_of_type
#print axioms ZInQ.Manuscript.RC.TypeCoverage.two_mem_type_support
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussGamma_rational_finite
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussGamma_indexAt_finite
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussGamma_odd_unit_defect
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussGamma_dyadic_unit_defect
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddDeterminant
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantCharacter
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantCharacter_intCast
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinant_reciprocity
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantCharacter_natCast
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantCharacter_neg_one
#print axioms ZInQ.Manuscript.RC.WeilIndex.oldCharacter
#print axioms ZInQ.Manuscript.RC.WeilIndex.oldCharacter_natCast
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddFactors_eq_jacobi
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadic_sign
#print axioms ZInQ.Manuscript.RC.WeilIndex.oldCharacter_comp_eq_iff
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.determinantExponent_value
#print axioms ZInQ.Manuscript.RC.WeilIndex.odd_unit_determinantExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadic_unit_determinantExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.negativeChar
#print axioms ZInQ.Manuscript.RC.WeilIndex.quadraticSum
#print axioms ZInQ.Manuscript.RC.WeilIndex.localPhase_fraction
#print axioms ZInQ.Manuscript.RC.WeilIndex.quadraticSum_eq_gaussSum
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddGauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddGauss_sq
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddGauss_twist
#print axioms ZInQ.Manuscript.RC.WeilIndex.quadraticSum_four
#print axioms ZInQ.Manuscript.RC.WeilIndex.quadraticSum_eight
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadic_evenGauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadic_oddGauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.lineHaar
#print axioms ZInQ.Manuscript.RC.WeilIndex.lineHaar_integerBall
#print axioms ZInQ.Manuscript.RC.WeilIndex.integral_completeSquare
#print axioms ZInQ.Manuscript.RC.WeilIndex.localPhase_congr_integer
#print axioms ZInQ.Manuscript.RC.WeilIndex.localPhase_integer_div_pow
#print axioms ZInQ.Manuscript.RC.WeilIndex.odd_unit_integral
#print axioms ZInQ.Manuscript.RC.WeilIndex.integral_linearPhase
#print axioms ZInQ.Manuscript.RC.WeilIndex.integral_quadratic_coset
#print axioms ZInQ.Manuscript.RC.WeilIndex.cutoffLattice
#print axioms ZInQ.Manuscript.RC.WeilIndex.cutoffLattice_measurable
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffLattice
#print axioms ZInQ.Manuscript.RC.WeilIndex.cutoffGaussian
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffGaussian
#print axioms ZInQ.Manuscript.RC.WeilIndex.polarDualLattice
#print axioms ZInQ.Manuscript.RC.WeilIndex.integral_quadratic_polarDual
#print axioms ZInQ.Manuscript.RC.WeilIndex.scaledLattice
#print axioms ZInQ.Manuscript.RC.WeilIndex.scaledLattice_compact
#print axioms ZInQ.Manuscript.RC.WeilIndex.polarDualLattice_scaled
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffGaussian_polarDual
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffGaussian_at_valuation
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_odd_unit_integral
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadicPlace
#print axioms ZInQ.Manuscript.RC.WeilIndex.exponentRoot
#print axioms ZInQ.Manuscript.RC.WeilIndex.exponentRoot_add
#print axioms ZInQ.Manuscript.RC.WeilIndex.exponentRoot_zero
#print axioms ZInQ.Manuscript.RC.WeilIndex.exponentRoot_one
#print axioms ZInQ.Manuscript.RC.WeilIndex.exponentRoot_neg
#print axioms ZInQ.Manuscript.RC.WeilIndex.valAt
#print axioms ZInQ.Manuscript.RC.WeilIndex.unitAt
#print axioms ZInQ.Manuscript.RC.WeilIndex.unitAt_coe
#print axioms ZInQ.Manuscript.RC.WeilIndex.valAt_mul
#print axioms ZInQ.Manuscript.RC.WeilIndex.unitAt_mul
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddUnitResidue
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadicUnitResidue
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadicUnitResidue_mul
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddUnitResidue_mul
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteGamma
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteExponent_dyadic
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteExponent_odd
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteGamma_even_odd_place
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteExponent_mul_sq
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteGamma_mul_sq
#print axioms ZInQ.Manuscript.RC.WeilIndex.unitAt_of_int_times_pow
#print axioms ZInQ.Manuscript.RC.WeilIndex.atPrime
#print axioms ZInQ.Manuscript.RC.WeilIndex.atReal
#print axioms ZInQ.Manuscript.RC.WeilIndex.rational_weil_product
#print axioms ZInQ.Manuscript.RC.WeilIndex.finiteGamma_productFormula
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussianParameter
#print axioms ZInQ.Manuscript.RC.WeilIndex.real_normalized_gauss_limit
#print axioms ZInQ.Manuscript.RC.WeilIndex.signExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.oddBase
#print axioms ZInQ.Manuscript.RC.WeilIndex.dyadicExponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.signExponent_mul
#print axioms ZInQ.Manuscript.RC.WeilIndex.odd_prod
#print axioms ZInQ.Manuscript.RC.WeilIndex.prime_coprime_prod
#print axioms ZInQ.Manuscript.RC.WeilIndex.odd_squarefree_exponents
#print axioms ZInQ.Manuscript.RC.WeilIndex.total_exponent
#print axioms ZInQ.Manuscript.RC.WeilIndex.coefficientSign
#print axioms ZInQ.Manuscript.RC.WeilIndex.twoPart
#print axioms ZInQ.Manuscript.RC.WeilIndex.odd_coprime_two
#print axioms ZInQ.Manuscript.RC.WeilIndex.signed_odd_squarefree_exponents
#print axioms ZInQ.Manuscript.RC.WeilIndex.integral_scaledLattice_residue
#print axioms ZInQ.Manuscript.RC.WeilIndex.lineHaar_scaledLattice_div
#print axioms ZInQ.Manuscript.RC.WeilIndex.lineHaar_scaledLattice_zpow
#print axioms ZInQ.Manuscript.RC.WeilIndex.scaledLattice_eq_of_valuation
#print axioms ZInQ.Manuscript.RC.WeilIndex.unitResidueSum
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffGaussian_eq_quadraticSum
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_odd_evenGauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_odd_oddGauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_dyadic_Gauss
#print axioms ZInQ.Manuscript.RC.WeilIndex.gaussGamma
#print axioms ZInQ.Manuscript.RC.WeilIndex.eventually_cutoffGaussian_gaussGamma
#print axioms ZInQ.Manuscript.RC.X0Branch.affineEval
#print axioms ZInQ.Manuscript.RC.X0Branch.affineEval_congr
#print axioms ZInQ.Manuscript.RC.X0Branch.affineEval_injective
#print axioms ZInQ.Manuscript.RC.X0Branch.finiteChart
#print axioms ZInQ.Manuscript.RC.X0Branch.eventually_chart_mem
#print axioms ZInQ.Manuscript.RC.X0Branch.chartEval
#print axioms ZInQ.Manuscript.RC.X0Branch.chartEval_center
#print axioms ZInQ.Manuscript.RC.X0Branch.chartEval_at_mem
#print axioms ZInQ.Manuscript.RC.X0Branch.chartEval_analyticAt
#print axioms ZInQ.Manuscript.RC.X0Branch.finitePointEval
#print axioms ZInQ.Manuscript.RC.X0Branch.finitePointEval_eq
#print axioms ZInQ.Manuscript.RC.X0Branch.exists_analyticJN_ratio
#print axioms ZInQ.Manuscript.RC.X0Branch.exists_stabilizer_germ_match
#print axioms ZInQ.Manuscript.RC.X0Branch.complexPoint_eq_iff
#print axioms ZInQ.Manuscript.RC.X0Branch.model
#print axioms ZInQ.Manuscript.RC.X0Branch.eventually_overlap_of_complexPoint_eq
#print axioms ZInQ.Manuscript.RC.X0Branch.eventually_eq_of_unramified
#print axioms ZInQ.Manuscript.RC.X0Model.fieldGerm
#print axioms ZInQ.Manuscript.RC.X0Model.fieldGerm_j
#print axioms ZInQ.Manuscript.RC.X0Model.fieldGerm_jN
#print axioms ZInQ.Manuscript.RC.X0Model.analyticArc
#print axioms ZInQ.Manuscript.RC.X0Model.analyticArc_generic
#print axioms ZInQ.Manuscript.RC.X0Model.complexPoint
#print axioms ZInQ.Manuscript.RC.X0Model.complexPoint_overQ
#print axioms ZInQ.Manuscript.RC.X0Model.MeromorphicGerm
#print axioms ZInQ.Manuscript.RC.X0Model.meromorphicIncl
#print axioms ZInQ.Manuscript.RC.X0Model.meromorphicValuation
#print axioms ZInQ.Manuscript.RC.X0Model.valueOfGerm
#print axioms ZInQ.Manuscript.RC.X0Model.valueOfGerm_isLocalHom
#print axioms ZInQ.Manuscript.RC.X0Model.constantGerm
#print axioms ZInQ.Manuscript.RC.X0Model.jPolynomial
#print axioms ZInQ.Manuscript.RC.X0Model.jPolynomial_injective
#print axioms ZInQ.Manuscript.RC.X0Model.analyticJ
#print axioms ZInQ.Manuscript.RC.X0Model.dilate
#print axioms ZInQ.Manuscript.RC.X0Model.analyticJN
#print axioms ZInQ.Manuscript.RC.X0Model.analyticOn_j
#print axioms ZInQ.Manuscript.RC.X0Model.analyticOn_jN
#print axioms ZInQ.Manuscript.RC.X0Model.hasSum_j
#print axioms ZInQ.Manuscript.RC.X0Model.hasSum_jN
#print axioms ZInQ.Manuscript.RC.X0Model.jCoordinate
#print axioms ZInQ.Manuscript.RC.X0Model.jCoordinate_X
#print axioms ZInQ.Manuscript.RC.X0Model.secondCoordinate
#print axioms ZInQ.Manuscript.RC.X0Model.integral_jN
#print axioms ZInQ.Manuscript.RC.X0Model.jAlgebra
#print axioms ZInQ.Manuscript.RC.X0Model.finite_jAlgebra
#print axioms ZInQ.Manuscript.RC.X0Model.curve
#print axioms ZInQ.Manuscript.RC.X0Model.overQ
#print axioms ZInQ.Manuscript.RC.X0Model.integral
#print axioms ZInQ.Manuscript.RC.X0Model.proper
#print axioms ZInQ.Manuscript.RC.X0Model.smooth
#print axioms ZInQ.Manuscript.RC.X0Model.functionField
#print axioms ZInQ.Manuscript.RC.X0Model.sectionGerm
#print axioms ZInQ.Manuscript.RC.X0Model.sectionAnalyticAt
#print axioms ZInQ.Manuscript.RC.X0Model.exists_meromorphicContinuation
#print axioms ZInQ.Manuscript.RC.X0Model.sectionMeromorphicContinuation
#print axioms ZInQ.Manuscript.RC.X0Model.genericMap
#print axioms ZInQ.Manuscript.RC.X0Model.existsUnique_specialization
#print axioms ZInQ.Manuscript.RC.X0Model.sectionMap
#print axioms ZInQ.Manuscript.RC.X0Model.sectionMap_comp
#print axioms ZInQ.Manuscript.RC.X0Model.sectionMap_generic
#print axioms ZInQ.Manuscript.RC.X0Model.formalQArc
#print axioms ZInQ.Manuscript.RC.X0Model.formalQArc_generic
#print axioms ZInQ.Manuscript.RC.X0Model.cusp
#print axioms ZInQ.Manuscript.RC.X0Model.cusp_overQ
#print axioms ZInQ.Manuscript.RC.X0Model2.gamma0_of_analyticJN_eq_at_transcendental
#print axioms ZInQ.Manuscript.RC.X0Model2.gamma0_of_eventuallyEq_analyticJN
#print axioms ZInQ.Manuscript.RC.X0Model2.rightOrbit_of_eventuallyEq_analyticJN
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_eq_of_reparam
#print axioms ZInQ.Manuscript.RC.X0Model2.slMoebius
#print axioms ZInQ.Manuscript.RC.X0Model2.coe_sl_smul
#print axioms ZInQ.Manuscript.RC.X0Model2.slMoebius_tendsto
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_smul
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_eq_of_gamma0_orbit
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_eq_of_rightOrbit
#print axioms ZInQ.Manuscript.RC.X0Model2.analyticJ_smul
#print axioms ZInQ.Manuscript.RC.X0Model2.analyticJ_eq_iff
#print axioms ZInQ.Manuscript.RC.X0Model2.lattice_eq_of_weierstrass_invariants
#print axioms ZInQ.Manuscript.RC.X0Model2.eventually_hasSum_laurent_mul
#print axioms ZInQ.Manuscript.RC.X0Model2.eventually_hasSum_laurent_inv
#print axioms ZInQ.Manuscript.RC.X0Model2.finite_sl_stabilizer
#print axioms ZInQ.Manuscript.RC.X0Model2.exists_nhds_local_j_orbit
#print axioms ZInQ.Manuscript.RC.X0Model2.exists_nhds_germ_match_of_overlap
#print axioms ZInQ.Manuscript.RC.X0Model2.sl_orbit_of_complexPoint_eq
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_one_eq_iff
#print axioms ZInQ.Manuscript.RC.X0Model2.modelOne
#print axioms ZInQ.Manuscript.RC.X0Model2.jProjection
#print axioms ZInQ.Manuscript.RC.X0Model2.jLinePoint
#print axioms ZInQ.Manuscript.RC.X0Model2.complexPoint_jProjection
#print axioms ZInQ.Manuscript.RC.X0Model2.analyticJ_eq_of_complexPoint_eq
#print axioms ZInQ.Manuscript.RC.X0Model2.hasSum_meromorphicContinuation
#print axioms ZInQ.Manuscript.RC.X0Model2.exists_hasSum_meromorphicContinuation
#print axioms ZInQ.Manuscript.RC.X0Model2.sectionExpansion
#print axioms ShimuraPointDict.PuncturedGerm
#print axioms ShimuraPointDict.HasValue
#print axioms ShimuraPointDict.hasValue_coe
#print axioms ShimuraPointDict.hasValue_unique
#print axioms ShimuraPointDict.isUnit_germ_of_eventually_ne_zero
#print axioms ShimuraPointDict.finiteSubring
#print axioms ShimuraPointDict.hasValue_inv_of_not_mem
#print axioms ShimuraPointDict.finiteValuationSubring
#print axioms ShimuraPointDict.finiteValue
#print axioms ShimuraPointDict.finiteValue_spec

import ZInQKernel.Contrib.OneProof.CMHeight62Full.NormAssembly
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Weierstrass
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Reduction
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Lattice
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeBasis
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Hartogs
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GenericComparison
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructure
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1
import ZInQKernel.Contrib.OneProof.CMHeight62Full.DepthTwoHartogs
import ZInQKernel.Contrib.OneProof.CMHeight62Full.IdentityPointDepth
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreValuation
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeFinite
import ZInQKernel.Contrib.OneProof.CMHeight62Full.PoleLadder
import ZInQKernel.Contrib.OneProof.CMHeight62Full.IntegralModel
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalParameter
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructureScheme
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreFunctionField
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TranslationNoFixedPlace
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeStatements
import ZInQKernel.Contrib.OneProof.CMHeight62Full.PoleRegCore

/-!
# Axiom check for `PoleRegCore.lean` (L3, the algebraic core of the N6-bridge)

Imports `PoleRegCore` together with every source file of waves 1 and 2, so a declaration-name
clash with those files would fail here, and prints the axioms of every declaration of
`PoleRegCore` (15 theorems and 3 definitions). Each should depend only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace ZInQ.Contrib.CMHeight62Full

-- definitions
#print axioms placeOfDVR
#print axioms genericSubring
#print axioms atPrimeAlgebra

-- the place of a discrete valuation ring
#print axioms dvrValuation_le_one_iff
#print axioms valuation_eq_one_of_le_one_of_inv_le_one
#print axioms placeOfDVR_valuation
#print axioms placeOfDVR_valuation_apply_le_one_iff
#print axioms mem_genericSubring_iff
#print axioms mem_range_of_mem_poleSpaceIn
#print axioms mem_of_mem_poleSpaceIn

-- localizations of `A` at primes
#print axioms isUnit_algebraMap_primeCompl
#print axioms atPrime_isScalarTower
#print axioms atPrime_isFractionRing
#print axioms atPrime_mem_range_iff

-- the pole bounds
#print axioms algebraMap_notMem_of_ne_zero
#print axioms algebraMap_mem_atPrime
#print axioms poleBounds_of_place
#print axioms exists_finite_span_of_place

end ZInQ.Contrib.CMHeight62Full

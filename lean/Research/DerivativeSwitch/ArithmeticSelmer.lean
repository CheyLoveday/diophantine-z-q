import Research.DerivativeSwitch.ContinuousSelmer
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The finite-support arithmetic Selmer diagram

The global group is the quotient of the absolute Galois group fixing every
finite Galois extension unramified outside the given finite support. The
local groups are absolute Galois groups of the adic completions. The chosen
embeddings of the algebraic closures determine the restriction maps.
-/

namespace Research.DerivativeSwitch.ArithmeticSelmer

open CategoryTheory ContinuousSelmer
open scoped NumberField

universe u
variable (K : Type u) [Field K] [NumberField K]

noncomputable section

abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)

variable (S : Finset (FinitePrime K))

/-- Finite Galois subextensions of the chosen closure that are unramified
at every finite prime outside `S`. This uses the ordinary local prime
predicate on the rings of integers. -/
structure SupportedExtension where
  carrier : IntermediateField K (AlgebraicClosure K)
  finite : FiniteDimensional K carrier
  galois : IsGalois K carrier
  unramified : ∀ v : FinitePrime K, v ∉ S →
    Algebra.IsUnramifiedIn (𝓞 carrier) v.asIdeal

def supportKernel : Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ E : SupportedExtension K S, E.carrier.fixingSubgroup

instance supportKernel_normal : (supportKernel K S).Normal :=
  Subgroup.normal_iInf_normal fun E =>
    letI := E.galois
    inferInstanceAs E.carrier.fixingSubgroup.Normal

omit [NumberField K] in
theorem supportKernel_closed :
    IsClosed (supportKernel K S : Set (Field.absoluteGaloisGroup K)) := by
  change IsClosed ((↑(⨅ E : SupportedExtension K S, E.carrier.fixingSubgroup)) :
    Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun E =>
    letI := E.finite
    E.carrier.fixingSubgroup_isClosed

/-- The global group for the finite support. -/
abbrev globalGroup := Field.absoluteGaloisGroup K ⧸ supportKernel K S

def supportProjection : Field.absoluteGaloisGroup K →ₜ* globalGroup K S where
  __ := QuotientGroup.mk' (supportKernel K S)
  continuous_toFun := QuotientGroup.continuous_mk

abbrev completion (v : FinitePrime K) := v.adicCompletion K

abbrev localGroup (v : FinitePrime K) := Field.absoluteGaloisGroup (completion K v)

abbrev PlaceEmbedding (v : FinitePrime K) :=
  AlgebraicClosure K →ₐ[K] AlgebraicClosure (completion K v)

/-- Localization at the specified place above `v`, using the chosen
embedding on the algebraic closures. -/
def absoluteLocalization (v : FinitePrime K) (e : PlaceEmbedding K v) :
    localGroup K v →ₜ* Field.absoluteGaloisGroup K :=
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure (completion K v)) := e.toRingHom.toAlgebra
  letI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure (completion K v)) :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  Field.absoluteGaloisGroup.mapOfAlgebra K (completion K v)

def placeLocalization (v : FinitePrime K) (e : PlaceEmbedding K v) :
    localGroup K v →ₜ* globalGroup K S :=
  (supportProjection K S).comp (absoluteLocalization K v e)

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  (M : TopRep.{u} R (globalGroup K S)) (e : ∀ v : S, PlaceEmbedding K v.1)

abbrev localizations (v : S) := placeLocalization K S v.1 (e v)

abbrev arithmeticCompactSupport := compactSupport M (localizations K S e)

variable (U : ∀ v : S, LocalCondition (localCochains M (localizations K S e) v))

abbrev arithmeticSelmer := selmerComplex M (localizations K S e) U

/-- Arithmetic specialization of the local-condition witness equation at
every selected finite place. -/
theorem arithmetic_selmer_cycle (z : (arithmeticSelmer K S M e U).X 0)
    (hz : (arithmeticSelmer K S M e U).d 0 1 z = 0) (v : S) :
    ((U v).inclusion.f 1 (z.1.2 v)) =
      (restrict M (placeLocalization K S v.1 (e v))).f 1 z.1.1 +
        (localCochains M (localizations K S e) v).d 0 1 (z.2 v) :=
  selmer_cycle_at_place M (localizations K S e) U z hz v

end

end Research.DerivativeSwitch.ArithmeticSelmer

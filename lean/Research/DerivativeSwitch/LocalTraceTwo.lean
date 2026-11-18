import Research.DerivativeSwitch.FirstSelmerPrecision
import Research.DerivativeSwitch.FiniteSelmerInjective
import Research.DerivativeSwitch.LocalInvariantTwo
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Local trace and degree-zero/degree-two duality at precision two

The trace agrees with the normalized Brauer invariant on degree-two
cycles. The degree-zero factor is the scalar in the constant cocycle.
The trace pairing in these two degrees is perfect for the sign line.
-/

namespace Research.DerivativeSwitch.LocalTraceTwo

open CategoryTheory HomologicalComplex ContinuousSelmer ArithmeticSelmer FiniteTateTwist
open LocalInvariantTwo
open scoped NumberField

noncomputable section

local notation "R" => ZMod 2

private theorem signLine_action {G : Type} [Group G] (g : G) (a : R) :
    (signLine G).ρ g a = a := rfl

/-- The localized finite Tate line and the sign line have the same action. -/
theorem restrictedSign_eq {G H : Type} [Group G] [Group H] (chi : G →* Rˣ) (r : H →* G) :
    TopRep.res r (coefficientLine (i := 0) (RingHom.id R) chi) = signLine H := by
  let trivial := signLine H
  have action : (TopRep.res r (coefficientLine (i := 0) (RingHom.id R) chi)).ρ = trivial.ρ :=
    DFunLike.ext _ _ fun g => ContinuousLinearMap.ext fun a =>
      FirstSelmerPrecision.coefficientLine_action chi (r g) a
  exact congrArg (fun ρ : ContRepresentation R H R => { trivial with ρ := ρ }) action

/-- The identification acts as the identity on coefficient values. -/
def restrictedSignIso {G H : Type} [Group G] [Group H] (chi : G →* Rˣ) (r : H →* G) :
    TopRep.res r (coefficientLine (i := 0) (RingHom.id R) chi) ≅ signLine H :=
  eqToIso (restrictedSign_eq chi r)

private def completionInvariant (K : Type) [Field K] [NumberField K] (v : FinitePrime K) :
    (cochains (signLine (localGroup K v))).homology 2 ≃ₗ[R] R :=
  invariant (completion K v)

/-- The invariant has the exact source of a localization term in the
arithmetic compact-support cone at the first precision. -/
def invariantAtPlace (K : Type) [Field K] [NumberField K] (S : Finset (FinitePrime K))
    (e : ∀ v : S, PlaceEmbedding K v.1) (chi : globalGroup K S →* Rˣ) (v : S) :
    (localCochains (coefficientLine (i := 0) (RingHom.id R) chi) (localizations K S e) v).homology 2
      ≃ₗ[R] R := by
  change (cochains (TopRep.res (localizations K S e v).toMonoidHom
    (coefficientLine (i := 0) (RingHom.id R) chi))).homology 2 ≃ₗ[R] R
  rw [restrictedSign_eq chi (localizations K S e v).toMonoidHom]
  exact completionInvariant K v.1

section CompactSupport

open scoped BigOperators

variable (K : Type) [Field K] [NumberField K] (S : Finset (FinitePrime K))
  (e : ∀ v : S, PlaceEmbedding K v.1) (chi : globalGroup K S →* Rˣ)

local notation "Tate" => coefficientLine (i := 0) (RingHom.id R) chi
local notation "CC" => arithmeticCompactSupport K S Tate e

set_option maxHeartbeats 1000000 in
/-- Given reciprocity on the supported global cochains, the first precision
has a compact-support trace with the constructed local invariants. -/
theorem exists_compact_support_trace
    (reciprocity : ∀ a : (cochains Tate).homology 2,
      ∑ v : S, invariantAtPlace K S e chi v
        (homologyMap (restrict Tate (localizations K S e v)) 2 a) = 0) :
    ∃ tr : (CC).X 2 →ₗ[R] R,
      (∀ b : (CC).X 1, tr ((CC).d 1 2 b) = 0) ∧
      ContinuousSelmerTrace.IsNormalized Tate (localizations K S e)
        (fun v => (invariantAtPlace K S e chi v).toLinearMap) tr := by
  let injective : Module.Injective R R := FiniteSelmerCoefficients.zmod_selfInjective 2 (by decide)
  exact ContinuousSelmerTrace.exists_normalized_trace Tate (localizations K S e)
    (fun v => (invariantAtPlace K S e chi v).toLinearMap) reciprocity

end CompactSupport

variable (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "G" => Field.absoluteGaloisGroup F
local notation "C" => cochains (signLine G)

/-- Extend the invariant to degree-two cochains and specify its value on
cycles. The extension automatically vanishes on degree-two boundaries. -/
theorem exists_local_trace : ∃ tr : (C).X 2 →ₗ[R] R,
    (∀ z : (C).cycles 2, tr ((C).iCycles 2 z) = invariant F ((C).homologyπ 2 z)) ∧
    (∀ b : (C).X 1, tr ((C).d 1 2 b) = 0) := by
  let injective : Module.Injective R R := FiniteSelmerCoefficients.zmod_selfInjective 2 (by decide)
  let j := (C).iCycles 2
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective j).mp inferInstance
  obtain ⟨tr, htr⟩ := Module.Injective.out j.hom hj
    ((invariant F).toLinearMap.comp ((C).homologyπ 2).hom)
  refine ⟨tr, htr, fun b => ?_⟩
  have hb := congrArg (fun f : (C).X 1 ⟶ (C).X 2 => f b) ((C).toCycles_i 1 2)
  have hp := congrArg (fun f : (C).X 1 ⟶ (C).homology 2 => f b)
    ((C).toCycles_comp_homologyπ 1 2)
  change (C).iCycles 2 ((C).toCycles 1 2 b) = (C).d 1 2 b at hb
  change (C).homologyπ 2 ((C).toCycles 1 2 b) = 0 at hp
  rw [← hb, htr]
  change invariant F ((C).homologyπ 2 ((C).toCycles 1 2 b)) = 0
  rw [hp, map_zero]

private def signInvariantsEquiv : (signLine G).ρ.invariants ≃ₗ[R] R :=
  LinearEquiv.ofBijective (signLine G).ρ.invariants.subtype
    ⟨Subtype.val_injective, fun a => ⟨⟨a, (ContRepresentation.mem_invariants _).mpr
      (fun g => signLine_action g a)⟩, rfl⟩⟩

/-- The constant value of a degree-zero cocycle. -/
def degreeZero : (C).homology 0 ≃ₗ[R] R :=
  ((cochainsHomologyIso (signLine G) 0).toLinearEquiv.trans
    (((forget₂ (TopModuleCat R) (ModuleCat R)).mapIso
      (ContinuousCohomology.zeroIso (signLine G))).toLinearEquiv)).trans (signInvariantsEquiv F)

/-- The adjoint of the degree-(0,2) pairing given by scalar multiplication
followed by the local invariant. -/
def duality02 : (C).homology 2 ≃ₗ[R] Module.Dual R ((C).homology 0) :=
  ((invariant F).trans (LinearMap.ringLmapEquivSelf R R R).symm).trans
    (LinearEquiv.arrowCongr (degreeZero F).symm (LinearEquiv.refl R R))

theorem duality02_apply (a : (C).homology 0) (x : (C).homology 2) :
    duality02 F x a = degreeZero F a * invariant F x := rfl

/-- Evaluating the cup with a constant degree-zero cocycle by any normalized
local chain trace gives the degree-(0,2) pairing. -/
theorem trace_duality02 (tr : (C).X 2 →ₗ[R] R)
    (normalization : ∀ z : (C).cycles 2, tr ((C).iCycles 2 z) = invariant F ((C).homologyπ 2 z))
    (a : (C).homology 0) (z : (C).cycles 2) :
    tr (degreeZero F a • (C).iCycles 2 z) = duality02 F ((C).homologyπ 2 z) a := by
  rw [map_smul, normalization, duality02_apply]
  rfl

end

end Research.DerivativeSwitch.LocalTraceTwo

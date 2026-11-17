import Research.DerivativeSwitch.CochainsHomology
import Research.DerivativeSwitch.ContinuousSelmerTrace
import ZInQKernel.Contrib.BrauerT14T15.LocalT15

/-!
# The local invariant at precision two

The mod-two Tate line is the trivial sign representation. This comparison
uses the Kummer sign map on continuous cochains and Tau Ceti's normalized
local Brauer invariant. The resulting linear equivalence has as its domain
the local cohomology of the very cochain model used in the Selmer cones.
-/

namespace Research.DerivativeSwitch.LocalInvariantTwo

open CategoryTheory HomologicalComplex ContinuousSelmer
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Contrib.BrauerT14T15

noncomputable section

/-- At precision two, `μ₂` is the sign line written additively. -/
abbrev signLine (G : Type) [Group G] : TopRep (ZMod 2) G :=
  TopRep.of (ContRepresentation.trivial (ZMod 2) G (ZMod 2))

local instance trivialAction (G : Type) [Group G] : DistribMulAction G (ZMod 2) :=
  (signLine G).distribMulAction

local instance continuousTrivialAction (G : Type) [Group G] [TopologicalSpace G] :
    ContinuousSMul G (ZMod 2) := ⟨continuous_snd⟩

private theorem trivial_smul {G : Type} [Group G] (g : G) (x : ZMod 2) : g • x = x := rfl

variable (F : Type) [Field F]

local notation "A" => Field.absoluteGaloisGroup F
local notation "S" => AbsoluteGaloisGroup F
local notation "U" => UnitsCoeff F

private def sepClasses : H2 A (ZMod 2) ≃+ H2 S (ZMod 2) :=
  explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F).symm
    (AddEquiv.refl _) continuous_id continuous_id (by
      intro g a
      rfl)

private def signCoeff : ZMod 2 →+[S] U where
  __ := sgn F
  map_smul' g a := (smul_sgn g a).symm

private def signClasses : H2 S (ZMod 2) →+ H2 S U :=
  explicitCoeff2 _ _ (signCoeff F) continuous_of_discreteTopology

private theorem asCocycle (c : Z2 S (ZMod 2)) : PkgI6.IsCocycle2 (fun g h => c.1 (g, h)) := by
  refine ⟨(mem_Z2_iff.mp c.2).1, fun g h k => ?_⟩
  have he := (mem_Z2_iff.mp c.2).2 g h k
  rw [trivial_smul] at he
  linear_combination -he

private theorem signClasses_mk (c : Z2 S (ZMod 2)) :
    signClasses F (H2pi _ _ c) =
      H2pi S U ⟨fun q => sgn F (c.1 q), sgn_mem_Z2 (asCocycle F c)⟩ := rfl

private theorem signClasses_injective [CharZero F] : Function.Injective (signClasses F) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  change signClasses F (H2pi _ _ c) = 0 at hx
  rw [signClasses_mk F c] at hx
  obtain ⟨f, hf, he⟩ := isCoboundary2_of_sgn_mem_B2 (K := F) two_ne_zero (asCocycle F c)
    (H2pi_eq_zero_iff.mp hx)
  apply H2pi_eq_zero_iff.mpr
  exact mem_B2_iff'.mpr ⟨f, hf, fun g h => (he g h).symm⟩

private theorem exists_signClasses [CharZero F] (x : H2 S U) (hx : 2 • x = 0) :
    ∃ a, signClasses F a = x := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨ε, hε, h⟩ := exists_sgn_eq_of_two_nsmul (K := F) two_ne_zero z hx
  let c : Z2 S (ZMod 2) := ⟨fun q => ε q.1 q.2, mem_Z2_iff.mpr ⟨hε.1, fun g h k => by
    rw [trivial_smul]
    have hc := hε.2 g h k
    linear_combination -hc⟩⟩
  exact ⟨H2pi _ _ c, (signClasses_mk F c).trans h⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private def explicitCircleInvariant : H2 A (ZMod 2) →+ AddCircle (1 : ℚ) :=
  (explicitInv F).toAddMonoidHom.comp ((signClasses F).comp (sepClasses F).toAddMonoidHom)

private theorem two_nsmul_modTwo (x : ZMod 2) : 2 • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  change (0 : ZMod 2) • x = 0
  exact zero_smul _ _

/-- The normalized Brauer value on the actual module-cochain `H²`.
The coefficient map is `a ↦ (-1)^a` on cocycles on the separable Galois group. -/
def circleInvariant : (cochains (signLine A)).homology 2 →+ AddCircle (1 : ℚ) := by
  letI : CompactSpace A := inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  exact (explicitCircleInvariant F).comp
    (((signLine A).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm.toAddMonoidHom.comp
      (cochainsHomologyIso (signLine A) 2).hom.hom.toAddMonoidHom)

theorem circleInvariant_injective [CharZero F] : Function.Injective (circleInvariant F) := by
  let compact : CompactSpace A := inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  exact (explicitInv F).injective.comp ((signClasses_injective F).comp
    ((sepClasses F).injective.comp
      ((signLine A).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.injective.comp
        ((ModuleCat.mono_iff_injective _).mp inferInstance))))

private theorem exists_circleInvariant [CharZero F] {y : AddCircle (1 : ℚ)} (hy : 2 • y = 0) :
    ∃ x, circleInvariant F x = y := by
  let compact : CompactSpace A := inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  have h : 2 • (explicitInv F).symm y = 0 := by rw [← map_nsmul, hy, map_zero]
  obtain ⟨x, hx⟩ := exists_signClasses F _ h
  let e := (cochainsHomologyIso (signLine A) 2).toLinearEquiv
  let b := (signLine A).explicitH2AddEquivContinuousCohomologyOfDiscrete
  refine ⟨e.symm (b ((sepClasses F).symm x)), ?_⟩
  change explicitInv F (signClasses F ((sepClasses F) (b.symm (e (e.symm _))))) = y
  rw [e.apply_symm_apply, b.symm_apply_apply, AddEquiv.apply_symm_apply, hx,
    AddEquiv.apply_symm_apply]

private theorem circleInvariant_two_nsmul (x : (cochains (signLine A)).homology 2) :
    2 • circleInvariant F x = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  change circleInvariant F ((0 : ZMod 2) • x) = 0
  rw [zero_smul, map_zero]

private def residueValue (x : (cochains (signLine A)).homology 2) : ZMod 2 :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero 2 (circleInvariant_two_nsmul F x)).choose

private theorem residueValue_spec (x : (cochains (signLine A)).homology 2) :
    ZMod.toRatAddCircle 2 (residueValue F x) = circleInvariant F x :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero 2 (circleInvariant_two_nsmul F x)).choose_spec

private def residueInvariant : (cochains (signLine A)).homology 2 →+ ZMod 2 where
  toFun := residueValue F
  map_zero' := ZMod.toRatAddCircle_injective 2 <| by rw [residueValue_spec, map_zero, map_zero]
  map_add' x y := ZMod.toRatAddCircle_injective 2 <| by
    rw [map_add (ZMod.toRatAddCircle 2), residueValue_spec, residueValue_spec, residueValue_spec, map_add]

/-- The invariant on `H²(F, μ₂)` sends the normalized Brauer value `1/2` to `1`. -/
def invariant [CharZero F] : (cochains (signLine A)).homology 2 ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap 2 (residueInvariant F)) (by
    constructor
    · intro x y he
      apply circleInvariant_injective F
      rw [← residueValue_spec F x, ← residueValue_spec F y]
      exact congrArg (ZMod.toRatAddCircle 2) he
    · intro a
      obtain ⟨x, hx⟩ := exists_circleInvariant F
        (show 2 • (ZMod.toRatAddCircle 2 a) = 0 by rw [← map_nsmul, two_nsmul_modTwo, map_zero])
      refine ⟨x, ZMod.toRatAddCircle_injective 2 ?_⟩
      exact (residueValue_spec F x).trans hx)

theorem invariant_normalization [CharZero F] (x : (cochains (signLine A)).homology 2) :
    ZMod.toRatAddCircle 2 (invariant F x) = circleInvariant F x := residueValue_spec F x

/-- The dyadic completion, at the first positive precision. -/
def invariantQ2 : (cochains (signLine (Field.absoluteGaloisGroup ℚ_[2]))).homology 2 ≃ₗ[ZMod 2]
    ZMod 2 := invariant ℚ_[2]

end

end Research.DerivativeSwitch.LocalInvariantTwo

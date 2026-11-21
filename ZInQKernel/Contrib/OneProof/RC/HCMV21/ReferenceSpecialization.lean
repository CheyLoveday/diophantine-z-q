import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorOrientation
import ZInQKernel.Contrib.OneProof.RC.HCMV21.InertReduction

/-! The cotangent line used at the selected detector place.
Tex 9146–9148, 9245–9263, and 9273–9279. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic IsLocalRing PointedScheme PMGeometry
open ZInQ.Contrib.ChebFD.C10 (Qbar GQ)
open scoped CategoryTheory.MonObj NumberField TensorProduct

section Reduction

variable {V K O k M : Type} [CommRing V] [Field K] [Field k]
  [CommRing O] [AddCommGroup M] [Module V M]

/-- Compare the arithmetic scalar with the cotangent pullback of the
specialized endomorphism. The integral module and its generator are
supplied by the good model. The comparison of the two pullbacks is
tested on this generator. -/
theorem specialized_cotangentCharacter (A : PkgI3.AbVar k)
    (e : (ofAbVar A).cotangent ≃ₗ[k] k) (action : O →+* A.End)
    (ρ : O →+* V) (i : V →+* K) (hi : Function.Injective i) (r : V →+* k)
    (v : M)
    (gen : M →ₗ[V] V)
    (g : O → M →+ M) (sp : M →+ (ofAbVar A).cotangent)
    (hsp : ∀ (x : V) (w : M), sp (x • w) = r x • sp w)
    (hv : sp v ≠ 0)
    (hline : ∀ w, w = gen w • v)
    (hgeneric : ∀ a : O, i (gen (g a v)) = i (ρ a))
    (hspecial : ∀ a : O, sp (g a v) =
      ZInQ.Contrib.AbVarBC.MulRigidity.cotangentMap A (action a).hom (sp v)) :
    (cotangentCharacter A e).comp action = r.comp ρ := by
  ext a
  have h := hspecial a
  rw [hline (g a v), hsp, hi (hgeneric a), cotangentMap_eq_character_smul A e] at h
  exact ((smul_left_injective k hv) h).symm

end Reduction

variable {q : ℕ} [Fact q.Prime] [Fact (q % 4 = 3)] {a b : ℚ}
  {F : Type} [Field F] [NumberField F] {g : GQ}
  (place : WitnessSpec.FrobeniusPlace g q) (typeMap : F →ₐ[ℚ] Qbar)

include typeMap in
omit [Fact (q % 4 = 3)] in
/-- The forward inert criterion for the reference at the selected place.
The point equivalence compares the reduced equation with its abelian
variety model. -/
theorem detector_reference_supersingular
    (A : PkgI3.AbVar (ResidueAt place)) [DecidableEq (ResidueAt place)]
    (W : WeierstrassCurve.Affine (ResidueAt place)) [W.IsElliptic]
    [Module (𝓞 F) W.Point]
    (hp : Multiplicative W.Point ≃* A.Pt (ResidueAt place))
    (hF : Module.finrank ℚ F = 2) (hInert : legendreSym q (NumberField.discr F) = -1) :
    ∀ P : A.Pt (ResidueAt place), P ^ q = 1 → P = 1 := by
  let : CharP (ResidueAt place) q := place.valuationResidue_charP
  obtain ⟨hprime, hcard⟩ := detector_inert_prime place typeMap hF hInert
  let : (Ideal.span {(q : 𝓞 F)}).IsMaximal := hprime ▸ place.restrictPrime_isMaximal typeMap
  have hcard' : Nat.card (𝓞 F ⧸ Ideal.span {(q : 𝓞 F)}) = q ^ 2 := hprime ▸ hcard
  intro P hP
  apply hp.symm.injective
  have hq : hp.symm P ^ q = 1 := by
    rw [← map_pow, hP, map_one]
  rw [map_one]
  exact supersingular_of_inert_action q W hcard' (Multiplicative.toAdd (hp.symm P))
    (congrArg Multiplicative.toAdd hq)

include typeMap in
/-- Put the endomorphism ring of the inert reference in the pinned
rational quaternion algebra. -/
theorem exists_detectorEndOrder (hD : DeuringSupersingularEndOrder)
    (hV : QuaternionRamificationUniqueness)
    (A : PkgI3.AbVar (ResidueAt place)) (hdim : A.dim = 1)
    [DecidableEq (ResidueAt place)]
    (W : WeierstrassCurve.Affine (ResidueAt place)) [W.IsElliptic]
    [Module (𝓞 F) W.Point]
    (hp : Multiplicative W.Point ≃* A.Pt (ResidueAt place))
    (hF : Module.finrank ℚ F = 2) (hInert : legendreSym q (NumberField.discr F) = -1) :
    ∃ S : Order (-1) (-(q : ℚ)), Nonempty (A.End ≃+* S.ring) ∧
      ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring := by
  let : CharP (ResidueAt place) q := place.valuationResidue_charP
  exact exists_referenceEndOrder hD hV q
    (ExplicitSplit.explicit_ramifiedExactlyAtEll0Infty Fact.out Fact.out) hdim
    (detector_reference_supersingular place typeMap A W hp hF hInert)

omit [Fact (q % 4 = 3)] in
/-- The scalar test on the chosen reference at the actual detector place.
The integral differential is taken over the valuation ring inside the
same algebraic closure as the chosen CM type. -/
theorem detector_reference_cotangent
    (A : PkgI3.AbVar (ResidueAt place)) (hdim : A.dim = 1)
    (action : 𝓞 F →+* A.End)
    {M : Type} [AddCommGroup M] [Module place.valuationRing.valuation.valuationSubring M]
    (v : M) (gen : M →ₗ[place.valuationRing.valuation.valuationSubring]
      place.valuationRing.valuation.valuationSubring)
    (g : 𝓞 F → M →+ M) (sp : M →+ (ofAbVar A).cotangent)
    (hsp : ∀ (x : place.valuationRing.valuation.valuationSubring) (w : M),
      sp (x • w) = residue _ x • sp w)
    (hv : sp v ≠ 0) (hline : ∀ w, w = gen w • v)
    (htype : ∀ a : 𝓞 F, ((gen (g a v) : place.valuationRing.valuation.valuationSubring) : Qbar) =
      (detectorOrderScalars place typeMap a : Qbar))
    (hspEnd : ∀ a : 𝓞 F, sp (g a v) =
      ZInQ.Contrib.AbVarBC.MulRigidity.cotangentMap A (action a).hom (sp v)) :
    (cotangentCharacter A (cotangentLine A hdim)).comp action =
      (residue _).comp (detectorOrderScalars place typeMap) :=
  specialized_cotangentCharacter A _ action _
    place.valuationRing.valuation.valuationSubring.subtype Subtype.val_injective _ v gen g sp
    hsp hv hline htype hspEnd

/-- The unique embedding of the explicit division residue field that
reads the geometric scalar on the chosen cotangent line. Its restriction
to the specialized CM action reads the fixed CM type at this place. -/
theorem reference_divisionCharacter
    (A : PkgI3.AbVar (ResidueAt place)) (hdim : A.dim = 1)
    (S : Order a b) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring)
    (chart : Bp q a b ≃ₐ[ℤ_[q]] LocalDivision.D q)
    (action : 𝓞 F →+* A.End)
    (hplace : place.restrictPrime typeMap = Ideal.span {(q : 𝓞 F)})
    (hχ : (cotangentCharacter A (cotangentLine A hdim)).comp action =
      (residue _).comp (detectorOrderScalars place typeMap)) :
    letI : CharP (ResidueAt place) q := place.valuationResidue_charP
    let comp := completedReferenceDivision (⟨q, Fact.out⟩ : Prime) S j hmax chart
    let χ := cotangentCharacter A (cotangentLine A hdim)
    ∃! iota : GaloisField q 2 →+* ResidueAt place,
      iota.comp (LocalDivision.red.comp comp.toRingHom) = completeScalarCharacter χ ∧
      ∀ x : 𝓞 F,
        iota (LocalDivision.red (comp (1 ⊗ₜ[ℤ] action x))) =
          detectorResidueCharacter place typeMap hplace (Ideal.Quotient.mk _ x) := by
  let : CharP (ResidueAt place) q := place.valuationResidue_charP
  dsimp only
  let comp := completedReferenceDivision (⟨q, Fact.out⟩ : Prime) S j hmax chart
  let χ := cotangentCharacter A (cotangentLine A hdim)
  obtain ⟨iota, hiota, huniq⟩ := completeScalarCharacter_factors χ comp.toRingEquiv
  refine ⟨iota, ⟨hiota, fun x => ?_⟩, fun iota' hiota' => huniq iota' hiota'.1⟩
  have h := DFunLike.congr_fun hiota ((1 : ℤ_[q]) ⊗ₜ[ℤ] action x)
  change iota (LocalDivision.red (comp (1 ⊗ₜ[ℤ] action x))) =
    completeScalarCharacter χ ((1 : ℤ_[q]) ⊗ₜ[ℤ] action x) at h
  rw [h, completeScalarCharacter_one_tmul]
  calc
    χ (action x) = residue _ (detectorOrderScalars place typeMap x) :=
      DFunLike.congr_fun hχ x
    _ = detectorResidueCharacter place typeMap hplace (Ideal.Quotient.mk _ x) := by
      rw [detectorResidueCharacter_eq_scalar_reduction, residueCharacter_mk]

end ZInQ.Manuscript.RC.HCMV21

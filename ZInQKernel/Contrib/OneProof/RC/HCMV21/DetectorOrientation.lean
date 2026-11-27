import ZInQKernel.Contrib.OneProof.RC.HCMV21.SpecialOrientation
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Heegner

/-! The character in the actual geometric residue field used to specialize the
detector, by restriction of its selected absolute place. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsLocalRing TauCeti WitnessSpec PMGeometry
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open scoped NumberField
attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {q : ℕ} [Fact q.Prime] (v : FrobeniusPlace g q)
  {F : Type} [Field F] [NumberField F] (e : F →ₐ[ℚ] Qbar)

/-- Reduce the fixed type at the selected place. At an inert prime the
contracted prime is `(q)`, so the source is the quadratic residue field. -/
def detectorResidueCharacter (h : v.restrictPrime e = Ideal.span {(q : 𝓞 F)}) :
    𝓞 F ⧸ Ideal.span {(q : 𝓞 F)} →+* ResidueAt v :=
  v.valuationResidueEquiv.toRingHom.comp
    ((v.residueMap e).comp (Ideal.Quotient.factor h.ge))

/-- On each integer of the maximal order the character is exactly reduction
of its image under the chosen embedding. -/
theorem detectorResidueCharacter_mk (h : v.restrictPrime e = Ideal.span {(q : 𝓞 F)})
    (x : 𝓞 F) : detectorResidueCharacter v e h (Ideal.Quotient.mk _ x) =
      v.valuationResidueEquiv (Ideal.Quotient.mk v.prime (FrobeniusPlace.integersMap e x)) := by
  change v.valuationResidueEquiv (v.residueMap e (Ideal.Quotient.factor h.ge
    (Ideal.Quotient.mk _ x))) = _
  rw [Ideal.Quotient.factor_mk, v.residueMap_mk]

/-- The scalars of the chosen embedding belong to the valuation ring
of the detector. -/
def detectorOrderScalars : 𝓞 F →+* v.valuationRing.valuation.valuationSubring :=
  v.localValuationEquiv.toRingHom.comp
    ((algebraMap Zbar v.localRing.toSubring).comp (FrobeniusPlace.integersMap e))

/-- The detector character is also the reduction of the integral scalar map
through the tangent-line residue construction. -/
theorem detectorResidueCharacter_eq_scalar_reduction
    (h : v.restrictPrime e = Ideal.span {(q : 𝓞 F)}) :
    detectorResidueCharacter v e h = residueCharacter q (detectorOrderScalars v e) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply, detectorResidueCharacter_mk, residueCharacter_mk]
  change ResidueField.mapEquiv v.localValuationEquiv
    (residue v.localRing.toSubring (algebraMap Zbar _ (FrobeniusPlace.integersMap e x))) = _
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue]
  rfl

/-- The contracted prime really is `(q)` and its residue degree is two
for the inert discriminant sign in `DatumPlace`. -/
theorem detector_inert_prime (hF : Module.finrank ℚ F = 2)
    (hs : legendreSym q (discr F) = -1) :
    v.restrictPrime e = Ideal.span {(q : 𝓞 F)} ∧
      Nat.card (𝓞 F ⧸ v.restrictPrime e) = q ^ 2 := by
  have hD : ¬ (q : ℤ) ∣ discr F := fun h => by
    have hz := (legendreSym.eq_zero_iff q (discr F)).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (discr F) q).mpr h)
    rw [hs] at hz
    norm_num at hz
  let u := v.restrictHeightOne e
  obtain ⟨hu, hd⟩ := inertPrime_of_legendre hF u (v.rationalPrimeBelow_restrict e) hD hs
  refine ⟨hu, ?_⟩
  change u.asIdeal.absNorm = _
  rw [absNorm_eq_rationalPrimeBelow_pow u, v.rationalPrimeBelow_restrict e, hd]

/-- The opposite orientation at this detector is obtained by residue
Frobenius. It differs from the character of the chosen CM type. -/
theorem detector_frobenius_switches (hF : Module.finrank ℚ F = 2)
    (hs : legendreSym q (discr F) = -1) :
    let h := (detector_inert_prime v e hF hs).1
    (frobenius (ResidueAt v) q).comp (detectorResidueCharacter v e h) ≠
      detectorResidueCharacter v e h := by
  let h := (detector_inert_prime v e hF hs).1
  letI : CharP (ResidueAt v) q := v.valuationResidue_charP
  letI : (Ideal.span {(q : 𝓞 F)}).IsMaximal := h ▸ v.restrictPrime_isMaximal e
  have hc : Nat.card (𝓞 F ⧸ Ideal.span {(q : 𝓞 F)}) = q ^ 2 :=
    h ▸ (detector_inert_prime v e hF hs).2
  letI : Finite (𝓞 F ⧸ Ideal.span {(q : 𝓞 F)}) :=
    Nat.finite_of_card_ne_zero (hc.symm ▸ pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {(q : 𝓞 F)})
  exact frobenius_comp_ne_of_card_sq q (detectorResidueCharacter v e h)
    ((Nat.card_eq_fintype_card).symm.trans hc)

end ZInQ.Manuscript.RC.HCMV21

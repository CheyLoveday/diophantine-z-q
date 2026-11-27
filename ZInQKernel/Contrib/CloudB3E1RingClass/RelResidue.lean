import ZInQKernel.Contrib.CloudB3E1RingClass.RelGenerator

/-!
# Residues at a Frobenius place versus residues modulo the split pair

Manuscript `diophantine_zq.tex`, tex 3576–3579: the residue `x_a = res_v(α_a) ∈ 𝐅_r^×` at the place
`v`, compared with the residues of `β_a` modulo `𝔯 = v ∩ 𝒪_K` and `𝔯̄`.

For `z ∈ 𝒪_K` and a split pair `sp` with `sp.P = v ∩ 𝒪_K`, `kummerRes v z` is the `𝐅_r`-element
of `z mod 𝔯`, read through lane E2's `resEquiv` (`kummerRes_integral`). The proof uses the residue
map `𝒪_K/𝔯 → κ(v)` and the uniqueness of ring maps out of `𝐅_r`. Conjugation then gives
`res_𝔯(σβ) = res_𝔯̄(β)` (`resEquiv_conj`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain IsLocalRing
open ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3E2.RingClassDelta
open scoped nonZeroDivisors Pointwise

variable (s : Qbar) {r : ℕ} [hr : Fact r.Prime] (v : kummerPlaces r)

/-- `𝒪_K → 𝒪_{K,𝔯}` for `𝔯 = v ∩ 𝒪_K`. Kind: definition. -/
def toPlaceRing : 𝓞 (quadField s) →+*
    ((placeRestrict s v).valuation (quadField s)).valuationSubring :=
  (algebraMap (𝓞 (quadField s)) (quadField s)).codRestrict
    ((placeRestrict s v).valuation (quadField s)).valuationSubring
    (fun z => (placeRestrict s v).valuation_le_one z)

/-- **The residue map `𝒪_K → κ(v)`.** Kind: definition. -/
def resToV : 𝓞 (quadField s) →+* ResidueField v.2.valuationRing.valuation.valuationSubring :=
  (residue v.2.valuationRing.valuation.valuationSubring).comp
    ((v.2.valuationRingMap (quadField s).val).comp (toPlaceRing s v))

theorem val_integral_le_one (z : 𝓞 (quadField s)) :
    v.2.valuationRing.valuation (((z : quadField s) : Qbar)) ≤ 1 :=
  (v.2.valuation_le_one_restrict (quadField s).val (z : quadField s)).mpr
    ((placeRestrict s v).valuation_le_one z)

theorem resToV_apply (z : 𝓞 (quadField s)) :
    resToV s v z = residue v.2.valuationRing.valuation.valuationSubring
      ⟨((z : quadField s) : Qbar), val_integral_le_one s v z⟩ := by
  change residue _ (v.2.valuationRingMap (quadField s).val (toPlaceRing s v z)) = _
  congr 1
  exact Subtype.ext (v.2.coe_valuationRingMap (quadField s).val (toPlaceRing s v z))

theorem resToV_eq_zero {z : 𝓞 (quadField s)} (hz : z ∈ (placeRestrict s v).asIdeal) :
    resToV s v z = 0 := by
  change residue _ (v.2.valuationRingMap (quadField s).val (toPlaceRing s v z)) = 0
  rw [residue_eq_zero_iff]
  intro hu
  have hu' := isUnit_of_map_unit (v.2.valuationRingMap (quadField s).val) _ hu
  have hlt : (placeRestrict s v).valuation (quadField s) (algebraMap _ _ z) < 1 :=
    ((placeRestrict s v).valuation_lt_one_iff_mem z).mpr hz
  have hm : toPlaceRing s v z ∈
      maximalIdeal ((placeRestrict s v).valuation (quadField s)).valuationSubring :=
    (Valuation.mem_maximalIdeal_iff (v := (placeRestrict s v).valuation (quadField s))).mpr hlt
  exact (mem_maximalIdeal _).mp hm hu'

variable {s v}

/-- **The residue of an integral element, as an `𝐅_r`-element** (tex 3576–3579): for `z ∈ 𝒪_K` and a
split pair with `sp.P = v ∩ 𝒪_K`, the `𝐅_r`-element of `z mod 𝔯` maps to the residue of `z` at `v`.
Kind: PROVED. -/
theorem castHom_integral (hK : Module.finrank ℚ (quadField s) = 2) (hr' : (max r 1).Prime)
    (sp : SplitPair (quadField s) (max r 1)) (hP : sp.P = placeRestrict s v)
    (z : 𝓞 (quadField s)) :
    ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring)
        ((ZMod.ringEquivCongr (eq_max hr')).symm
          ((sp.resEquiv hr' hK).symm (Ideal.Quotient.mk sp.P.asIdeal z))) =
      residue v.2.valuationRing.valuation.valuationSubring
        ⟨((z : quadField s) : Qbar), val_integral_le_one s v z⟩ := by
  let ψ : 𝓞 (quadField s) ⧸ sp.P.asIdeal →+*
      ResidueField v.2.valuationRing.valuation.valuationSubring :=
    Ideal.Quotient.lift sp.P.asIdeal (resToV s v) (fun z hz => resToV_eq_zero s v (hP ▸ hz))
  have hsub : ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) =
      (ψ.comp (sp.resEquiv hr' hK).toRingHom).comp
        (ZMod.ringEquivCongr (eq_max hr')).toRingHom := Subsingleton.elim _ _
  rw [hsub]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  rw [Ideal.Quotient.lift_mk, resToV_apply]

/-- **The residue of an integral element at the Frobenius place** (tex 3576–3579): for `z ∈ 𝒪_K`
and a split pair with `sp.P = v ∩ 𝒪_K`, `kummerRes v z` is the `𝐅_r`-element of `z mod 𝔯`.
Kind: PROVED. -/
theorem kummerRes_integral (hK : Module.finrank ℚ (quadField s) = 2) (hr' : (max r 1).Prime)
    (sp : SplitPair (quadField s) (max r 1)) (hP : sp.P = placeRestrict s v)
    (z : 𝓞 (quadField s)) :
    kummerRes v (((z : quadField s) : Qbar)) = (ZMod.ringEquivCongr (eq_max hr')).symm
      ((sp.resEquiv hr' hK).symm (Ideal.Quotient.mk sp.P.asIdeal z)) :=
  kummerRes_spec v (val_integral_le_one s v z) (castHom_integral hK hr' sp hP z)

/-- **Conjugation exchanges the residues of the split pair** (tex 3576–3579): if `σ𝔯̄ = 𝔯`, then
`res_𝔯(σβ) = res_𝔯̄(β)` in `𝐅_r`. Kind: PROVED. -/
theorem resEquiv_conj {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {f : ℕ} (hf : f.Prime) (sp : SplitPair K f) (σ : K ≃ₐ[ℚ] K)
    (hσ : σ • sp.Q.asIdeal = sp.P.asIdeal) (β : 𝓞 K) :
    (sp.resEquiv hf hK).symm (Ideal.Quotient.mk sp.P.asIdeal (σ • β)) =
      (sp.swap.resEquiv hf hK).symm (Ideal.Quotient.mk sp.Q.asIdeal β) := by
  let e := MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ
  have hmap : sp.P.asIdeal = sp.Q.asIdeal.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [← hσ, Ideal.pointwise_smul_def]
    rfl
  let τ := Ideal.quotientEquiv sp.Q.asIdeal sp.P.asIdeal e hmap
  have hsub : (τ : 𝓞 K ⧸ sp.Q.asIdeal →+* 𝓞 K ⧸ sp.P.asIdeal).comp
      ((sp.swap.resEquiv hf hK : ZMod f →+* 𝓞 K ⧸ sp.swap.P.asIdeal)) =
      (sp.resEquiv hf hK : ZMod f →+* 𝓞 K ⧸ sp.P.asIdeal) := Subsingleton.elim _ _
  have hτ : τ (Ideal.Quotient.mk sp.Q.asIdeal β) = Ideal.Quotient.mk sp.P.asIdeal (σ • β) := rfl
  rw [← hτ]
  apply (sp.resEquiv hf hK).injective
  rw [RingEquiv.apply_symm_apply]
  have h2 := RingHom.congr_fun hsub
    ((sp.swap.resEquiv hf hK).symm (Ideal.Quotient.mk sp.Q.asIdeal β))
  have h3 : sp.swap.resEquiv hf hK ((sp.swap.resEquiv hf hK).symm
      (Ideal.Quotient.mk sp.Q.asIdeal β)) = Ideal.Quotient.mk sp.Q.asIdeal β :=
    RingEquiv.apply_symm_apply _ _
  change τ (sp.swap.resEquiv hf hK ((sp.swap.resEquiv hf hK).symm
      (Ideal.Quotient.mk sp.Q.asIdeal β))) = _ at h2
  rw [h3] at h2
  exact h2

/-- `σ𝔯̄ = 𝔯` for a split pair over a prime. Kind: PROVED. -/
theorem conj_smul_splitPair {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {σ : K ≃ₐ[ℚ] K} (hσ : ∀ τ : K ≃ₐ[ℚ] K, τ ≠ 1 → τ = σ) {f : ℕ} (hf : f.Prime)
    (sp : SplitPair K f) : σ • sp.Q.asIdeal = sp.P.asIdeal :=
  conj_smul_split hK hσ hf sp.ne.symm (by rw [mul_comm, ← sp.span_eq, Int.cast_natCast])

end ZInQ.Contrib.CloudB3E1RingClass

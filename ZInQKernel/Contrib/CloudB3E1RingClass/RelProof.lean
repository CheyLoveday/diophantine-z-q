import ZInQKernel.Contrib.CloudB3E1RingClass.RelResidue
import ZInQKernel.Contrib.CloudB3E1RingClass.DeltaWire

/-!
# The principal relations `rel`

Manuscript `diophantine_zq.tex`, tex 3576–3579: "since `(β_a) = ∏_j 𝔭_j^{m_j}` … the class
`∑_j m_j q_j` is the Artin class of the principal ideal `(β_a)`, which is `δ` of the residue of `β_a`;
so `∑_j m_j q_j + δ(x_a) = 0`".

Part 1, `artin_relIdeal`. Take a relation `m`, a generator `β ∈ 𝒪_K` of `J_m = ∏_j 𝔭_j^{m_j⁺} 𝔭̄_j^{m_j⁻}`,
and a prime `r` different from the `p_j`. Then `∑_j m_j • setupQ C r j` is the Galois image
`galResidue(u)` of the residue unit `u ≡ β` modulo the conductor `r𝒪_K`. This uses
`[𝔭̄_j] = −[𝔭_j]` in `Pic(ℤ + r𝒪_K)`, since `𝔭_j𝔭̄_j = (p_j)` with `p_j` in the order, and lane E2's
`residuePic_span`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3E2.RingClassDelta
open scoped nonZeroDivisors

variable {s : Qbar} {S : ℕ}

theorem not_mem_𝔭_of_ne (C : RingClassSetup (quadField s) S) {r : ℕ} (hr : r.Prime)
    (hrp : ∀ j, r ≠ C.p j) (j : Fin S) :
    ((max r 1 : ℕ) : 𝓞 (quadField s)) ∉ (C.𝔭 j).asIdeal ∧
      ((max r 1 : ℕ) : 𝓞 (quadField s)) ∉ (C.𝔭bar j).asIdeal :=
  not_mem_of_ne C j r hr (hrp j)

/-- **The Artin class of the relation ideal** (tex 3576–3579): `∑_j m_j • q_j = galResidue(u)`
for the residue unit `u ≡ β` modulo the conductor. Kind: PROVED. -/
theorem artin_relIdeal (C : RingClassSetup (quadField s) S) (m : Fin S → ℤ)
    (β : 𝓞 (quadField s)) (hβ : relIdeal C m = Ideal.span {β}) {r : ℕ} (hr : r.Prime)
    (hrp : ∀ j, r ≠ C.p j) :
    ∃ u : (𝓞 (quadField s) ⧸
        (ringClassOrder (K := quadField s) (max r 1) (max_one_ne_zero r)).conductor)ˣ,
      (u : 𝓞 (quadField s) ⧸
          (ringClassOrder (K := quadField s) (max r 1) (max_one_ne_zero r)).conductor) =
        Ideal.Quotient.mk _ β ∧
      ∑ j, m j • setupQ C r j = Additive.ofMul
        (galResidue (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) u) := by
  let O := ringClassOrder (K := quadField s) (max r 1) (max_one_ne_zero r)
  have hn := not_mem_𝔭_of_ne C hr hrp
  let Jp : Fin S → integralIdealsPrimeTo O.conductorModulus := fun j =>
    primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭 j) (hn j).1
  let Jb : Fin S → integralIdealsPrimeTo O.conductorModulus := fun j =>
    primeToIdeal (max r 1) (max_one_ne_zero r) (C.𝔭bar j) (hn j).2
  let J : integralIdealsPrimeTo O.conductorModulus :=
    ∏ j, Jp j ^ (m j).toNat * Jb j ^ (-m j).toNat
  have hJ : (J : Ideal (𝓞 (quadField s))) = Ideal.span {β} := by
    rw [← hβ]
    simp [J, Jp, Jb, relIdeal, primeToIdeal]
  have hbar : ∀ j, O.picClass (Jb j) = (O.picClass (Jp j))⁻¹ := by
    intro j
    rw [eq_inv_iff_mul_eq_one, ← map_mul, O.picClass_eq_one_iff]
    refine ⟨(((C.p j : ℤ)) : 𝓞 (quadField s)), ?_, ?_⟩
    · rw [mem_toRingOfIntegers]
      exact Subalgebra.intCast_mem _ _
    · change (C.𝔭bar j).asIdeal * (C.𝔭 j).asIdeal = _
      rw [mul_comm, C.𝔭_mul j]
  have hpic : O.picClass J = ∏ j, O.picClass (Jp j) ^ m j := by
    simp only [J, map_prod, map_mul, map_pow, hbar, zpow_toNat_mul_inv]
  obtain ⟨u, hu, hres⟩ := residuePic_span O β J hJ
  refine ⟨u, hu, ?_⟩
  have hq : ∀ j, setupQ C r j = Additive.ofMul (artinClass (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (Jp j)) :=
    fun j => setupQ_eq (C := C) (hn j).1
  simp only [hq, ← ofMul_zpow, ← ofMul_prod]
  refine congrArg Additive.ofMul ?_
  change ∏ j, (ringClassPicEquiv (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (O.picClass (Jp j))) ^ m j =
    ringClassPicEquiv (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (residuePic O u)
  rw [hres, hpic, map_prod]
  simp only [map_zpow]

open ZInQ.Manuscript.RC.WitnessSpec IsLocalRing in
/-- A unit at `v ∩ 𝒪_K` is a unit at the Frobenius place `v`. Kind: PROVED. -/
theorem val_eq_one_of_restrict {r : ℕ} [Fact r.Prime] (v : kummerPlaces r) {x : quadField s}
    (hx : (placeRestrict s v).valuation (quadField s) x = 1) :
    v.2.valuationRing.valuation ((x : Qbar)) = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [map_zero] at hx; exact zero_ne_one hx
  have le1 : v.2.valuationRing.valuation ((quadField s).val x) ≤ 1 :=
    (v.2.valuation_le_one_restrict (quadField s).val x).mpr hx.le
  have le2 : v.2.valuationRing.valuation ((quadField s).val x⁻¹) ≤ 1 :=
    (v.2.valuation_le_one_restrict (quadField s).val x⁻¹).mpr (by
      change (placeRestrict s v).valuation (quadField s) x⁻¹ ≤ 1
      rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at le2
  have hV0 : v.2.valuationRing.valuation ((quadField s).val x) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact (map_ne_zero _).mpr hx0
  rw [inv_le_one₀ (zero_lt_iff.mpr hV0)] at le2
  exact le_antisymm le1 le2

open ZInQ.Manuscript.RC.WitnessSpec IsLocalRing in
/-- **The residue of a quotient** at the Frobenius place. Kind: PROVED. -/
theorem kummerRes_div_of_spec {r : ℕ} [Fact r.Prime] (v : kummerPlaces r) {x y : Qbar}
    (hx : v.2.valuationRing.valuation x ≤ 1) (hy : v.2.valuationRing.valuation y = 1)
    {a b : ZMod r}
    (ha : ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) a =
      residue v.2.valuationRing.valuation.valuationSubring ⟨x, hx⟩)
    (hb : ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) b =
      residue v.2.valuationRing.valuation.valuationSubring ⟨y, hy.le⟩) :
    kummerRes v (x / y) = a / b := by
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [map_zero] at hy; exact zero_ne_one hy
  have hxy : v.2.valuationRing.valuation (x / y) ≤ 1 := by
    rw [map_div₀, hy, div_one]; exact hx
  refine kummerRes_spec v hxy ?_
  have hres0 := residue_ne_zero_of_val v hy
  have hmul : (⟨x / y, hxy⟩ : v.2.valuationRing.valuation.valuationSubring) * ⟨y, hy.le⟩ =
      ⟨x, hx⟩ := Subtype.ext (div_mul_cancel₀ x hy0)
  have h1 := congrArg (residue v.2.valuationRing.valuation.valuationSubring) hmul
  rw [map_mul] at h1
  rw [map_div₀, ha, hb, ← h1, mul_div_cancel_right₀ _ hres0]

/-- **The principal relations on the genuine data** (tex 3576–3579). Take a relation `m` and a
generator `β ∈ 𝒪_K` of `J_m`. With `α = σβ/β`, at every good prime `r` and every Frobenius place
`v` over it, `∑_j m_j q_j + δ(x_v(α)) = 0`. Kind: PROVED. -/
theorem rel_genuine (hK : Module.finrank ℚ (quadField s) = 2) (C : RingClassSetup (quadField s) S)
    {σ : quadField s ≃ₐ[ℚ] quadField s} (hσ : ∀ τ : quadField s ≃ₐ[ℚ] quadField s, τ ≠ 1 → τ = σ)
    (m : Fin S → ℤ) (β : 𝓞 (quadField s)) (hβ : relIdeal C m = Ideal.span {β})
    (E : WeierstrassCurve ℚ) (Sexc : Finset ℕ)
    (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    (p_mem : ∀ j, C.p j ∈ Sexc) {r : ℕ} (hgood : GoodPrime E s Sexc r) (v : kummerPlaces r) :
    ∑ j, m j • setupQ C r j + kummerDelta hK E Sexc hSdisc C r v
      (kummerX ((((σ • β : 𝓞 (quadField s)) : quadField s) / (β : quadField s) : quadField s) :
        Qbar) v) = 0 := by
  have hr := hgood.1
  have : Fact r.Prime := ⟨hr⟩
  have hrp : ∀ j, r ≠ C.p j := fun j h => hgood.2.2.2.1 (h ▸ p_mem j)
  have hr' := max_prime_of_good hgood
  have : Fact (max r 1).Prime := ⟨hr'⟩
  obtain ⟨u, hu, hsum⟩ := artin_relIdeal C m β hβ hr hrp
  rw [hsum, kummerDelta_of_good hK hSdisc C hgood v]
  set sp := splitPairOf hK hgood (not_dvd_discr_of_good hSdisc hgood) v
  have hP : sp.P = placeRestrict s v := rfl
  rw [sp.galResidue_eq_deltaMul hr' hK (C.Sr r) (C.hSr r) u]
  set a := (sp.unitsCrt hr' hK u).1
  set b := (sp.unitsCrt hr' hK u).2
  have ha : (a : ZMod (max r 1)) = (sp.resEquiv hr' hK).symm (Ideal.Quotient.mk sp.P.asIdeal β) := by
    change (sp.crtEquiv hr' hK (u : 𝓞 (quadField s) ⧸ _)).1 = _
    rw [hu]; rfl
  have hb : (b : ZMod (max r 1)) =
      (sp.swap.resEquiv hr' hK).symm (Ideal.Quotient.mk sp.Q.asIdeal β) := by
    change (sp.crtEquiv hr' hK (u : 𝓞 (quadField s) ⧸ _)).2 = _
    rw [hu]; rfl
  -- the residue of `α = σβ/β` at `v`
  have hrw : ((r : ℤ) : 𝓞 (quadField s)) ∈ (placeRestrict s v).asIdeal := by
    have hm : (r : ℤ) ∈ (placeRestrict s v).asIdeal.under ℤ := by
      rw [placeRestrict_under]; exact Ideal.mem_span_singleton_self _
    simpa using hm
  have hvβ : (placeRestrict s v).valuation (quadField s) (β : quadField s) = 1 :=
    valuation_relGenerator_away C m β hβ hr hrp hrw
  have hVβ := val_eq_one_of_restrict v hvβ
  have hres := kummerRes_div_of_spec v (val_integral_le_one s v (σ • β)) hVβ
    (castHom_integral hK hr' sp hP (σ • β)) (castHom_integral hK hr' sp hP β)
  rw [resEquiv_conj hK hr' sp σ (conj_smul_splitPair hK hσ hr' sp), ← ha, ← hb] at hres
  have hα : ((((σ • β : 𝓞 (quadField s)) : quadField s) / (β : quadField s) : quadField s) :
      Qbar) = (((σ • β : 𝓞 (quadField s)) : quadField s) : Qbar) /
        ((β : quadField s) : Qbar) := IntermediateField.coe_div _ _ _
  rw [← hα] at hres
  set c : ZMod r := (ZMod.ringEquivCongr (eq_max hr')).symm (b : ZMod (max r 1)) /
    (ZMod.ringEquivCongr (eq_max hr')).symm (a : ZMod (max r 1))
  have hcu : IsUnit (kummerRes v ((((σ • β : 𝓞 (quadField s)) : quadField s) /
      (β : quadField s) : quadField s) : Qbar)) := by
    rw [hres]
    refine (isUnit_iff_ne_zero).mpr (div_ne_zero ?_ ?_)
    · exact (map_ne_zero _).mpr b.ne_zero
    · exact (map_ne_zero _).mpr a.ne_zero
  have hx : kummerX ((((σ • β : 𝓞 (quadField s)) : quadField s) / (β : quadField s) :
      quadField s) : Qbar) v = Additive.ofMul hcu.unit := by
    rw [kummerX, dite_eq_left_of_eq_true (eq_true hcu)]
  rw [hx]
  have hcast : unitsCast hr' hcu.unit = b * a⁻¹ := by
    apply Units.ext
    change (ZMod.ringEquivCongr (eq_max hr')) (kummerRes v _) = _
    rw [hres, map_div₀, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have hd : deltaR hr' sp hK (C.Sr r) (C.hSr r) (Additive.ofMul hcu.unit) =
      Additive.ofMul (sp.deltaMul hr' (C.Sr r) (C.hSr r) hK (unitsCast hr' hcu.unit)) := rfl
  rw [hd, hcast, ← ofMul_mul, ← map_mul, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, map_one]
  rfl

end ZInQ.Contrib.CloudB3E1RingClass

import ZInQKernel.Contrib.OneProof.BergerComparison.FrobeniusTeichLog

/-! Localization of the integral Frobenius map on the actual crystalline
and maximal period rings. The maximal ring is obtained by inverting
the product p t in its integral subring. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne FontaineSt PowerSeries
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 600000

/-- The actual embedded crystalline coefficient algebra. -/
abbrev CrystallineRing {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :=
  BcrisOf p h (xi p) (theta_xi' p)

private def maxBdR : Amax p →+* BdR p := (toBdR p).comp (Amax p).subtype

private def maxEmbed : Amax p →+* Bmax p :=
  (maxBdR p).codRestrict (Bmax p) (fun a => Algebra.subset_adjoin (Or.inl ⟨a, a.property, rfl⟩))

private def crisEmbed {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    crystallineIntegral p →+* CrystallineRing p h :=
  ((toBdR p).comp (crystallineIntegral p).subtype).codRestrict (CrystallineRing p h)
    (fun b => Algebra.subset_adjoin (Or.inl ⟨b, (mem_crystallineIntegral p _).mp b.property, rfl⟩))

private def logA {ε : PreTilt 𝓞_ℂ_[p] p} (hε : ε.untilt = 1) : Amax p :=
  ⟨logTeich p hε, logTeich_mem_amax p hε⟩

private def denominator {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) : Amax p :=
  p * logA p h.1

private def integralToCris {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Amax p →+* CrystallineRing p h :=
  (crisEmbed p h).comp (integralFrobenius p)

private theorem p_nat_q : (p : BdR p) = algebraMap ℚ_[p] (BdR p) (p : ℚ_[p]) :=
  (map_natCast _ p).symm

private theorem p_nat_q_nat (n : ℕ) : (n : BdR p) = algebraMap ℚ_[p] (BdR p) (n : ℚ_[p]) :=
  (map_natCast _ n).symm

private theorem p_mul_inv : (p : BdR p) * algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) = 1 := by
  rw [p_nat_q, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero), map_one]

private theorem t_mul_inv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    tOf p h * Ring.inverse (tOf p h) = 1 := by
  have ht : tOf p h ≠ 0 := by
    intro he
    apply logTeich_ne_zero p h.1 (ne_one_of_isGenEps p h)
    apply toBdR_injective p
    simpa only [map_zero, tOf] using he
  obtain ⟨v, hv⟩ := (isField_BDeRham p).mul_inv_cancel ht
  exact Ring.mul_inverse_cancel _ (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)

private def maxInv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) : Bmax p :=
  ⟨algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) * Ring.inverse (tOf p h),
   (Bmax p).mul_mem (Subalgebra.algebraMap_mem _ _)
     (Algebra.subset_adjoin (Or.inr ⟨ε, h.1, ne_one_of_isGenEps p h, rfl⟩))⟩

private theorem max_mul_inv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    maxEmbed p (denominator p h) * maxInv p h = 1 := by
  apply Subtype.ext
  change toBdR p ((p : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p h.1) *
    (algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) * Ring.inverse (tOf p h)) = 1
  rw [map_mul, map_natCast]
  change (p : BdR p) * tOf p h * _ = 1
  linear_combination ((p : BdR p) * algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹)) * t_mul_inv p h +
    p_mul_inv p

private def crisInv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) : CrystallineRing p h :=
  ⟨algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹ ^ 2) * Ring.inverse (tOf p h),
   (CrystallineRing p h).mul_mem (Subalgebra.algebraMap_mem _ _)
     (Algebra.subset_adjoin (Or.inr rfl))⟩

private theorem integralToCris_log {ε ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (hε : ε.untilt = 1) :
    ((integralToCris p h (logA p hε) : CrystallineRing p h) : BdR p) =
      p * toBdR p (logTeich p hε) := by
  change toBdR p (integralFrobenius p ⟨_, logTeich_mem_amax p hε⟩).val = _
  rw [integralFrobenius_logTeich p hε, map_mul, map_natCast]

private theorem cris_mul_inv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    integralToCris p h (denominator p h) * crisInv p h = 1 := by
  unfold denominator
  rw [map_mul, map_natCast]
  apply Subtype.ext
  change (p : BdR p) * ((integralToCris p h (logA p h.1) : CrystallineRing p h) : BdR p) *
    (algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹ ^ 2) * Ring.inverse (tOf p h)) = 1
  rw [integralToCris_log, map_pow]
  change (p : BdR p) * ((p : BdR p) * tOf p h) * _ = 1
  have hh : ((p : BdR p) * algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹))^2 = 1 := by
    rw [p_mul_inv, one_pow]
  linear_combination ((p : BdR p) * algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹))^2 *
    t_mul_inv p h + hh

private abbrev LocalizedMax {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :=
  Localization.Away (denominator p h)

private def maxLift {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    LocalizedMax p h →+* Bmax p :=
  Localization.awayLift (maxEmbed p) _ (isUnit_iff_exists_inv.mpr ⟨_, max_mul_inv p h⟩)

private def crisLift {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    LocalizedMax p h →+* CrystallineRing p h :=
  Localization.awayLift (integralToCris p h) _ (isUnit_iff_exists_inv.mpr ⟨_, cris_mul_inv p h⟩)

private theorem maxLift_inj {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Function.Injective (maxLift p h) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (denominator p h)) _).mpr
  intro a b
  simp only [maxLift, IsLocalization.Away.lift_eq]
  have he : Function.Injective (maxEmbed p) := fun _ _ he =>
    Subtype.ext (toBdR_injective p (congrArg Subtype.val he))
  constructor
  · intro hh
    simpa only [maxLift, IsLocalization.Away.lift_eq] using congrArg (maxLift p h) hh
  · intro hh
    exact congrArg _ (he hh)

private theorem maxLift_surj {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Function.Surjective (maxLift p h) := by
  let M := LocalizedMax p h
  let f := (Bmax p).val.toRingHom.comp (maxLift p h)
  have hInt (x : Amax p) : f (algebraMap (Amax p) M x) = maxBdR p x := by
    change ((maxLift p h (algebraMap (Amax p) M x) : Bmax p) : BdR p) = _
    rw [maxLift, IsLocalization.Away.lift_eq]
    rfl
  have hFrac (x : Amax p) :
      f (Localization.mk x ⟨(denominator p h)^1, 1, rfl⟩) =
        maxBdR p x * (maxInv p h : BdR p) := by
    change ((maxLift p h (Localization.mk x ⟨(denominator p h)^1, 1, rfl⟩) : Bmax p) : BdR p) = _
    rw [maxLift, Localization.awayLift_mk _ _ _ _ (max_mul_inv p h), pow_one]
    rfl
  have hpinv : algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) ∈ f.range := by
    refine ⟨Localization.mk (logA p h.1) ⟨(denominator p h)^1, 1, rfl⟩, ?_⟩
    rw [hFrac]
    change tOf p h * (algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) *
      Ring.inverse (tOf p h)) = _
    linear_combination (algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹)) * t_mul_inv p h
  have htinv : Ring.inverse (tOf p h) ∈ f.range := by
    refine ⟨Localization.mk (p : Amax p) ⟨(denominator p h)^1, 1, rfl⟩, ?_⟩
    rw [hFrac, map_natCast]
    change (p : BdR p) * (algebraMap ℚ_[p] (BdR p) ((p : ℚ_[p])⁻¹) *
      Ring.inverse (tOf p h)) = _
    linear_combination (Ring.inverse (tOf p h)) * p_mul_inv p
  intro x
  suffices hx : (x : BdR p) ∈ f.range by
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  have hmem (y : BdR p) (hy : y ∈ Bmax p) : y ∈ f.range := by
    rw [← bmaxOf_eq p h, BmaxOf] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with (⟨a, ha, rfl⟩ | rfl)
      · exact ⟨_, hInt ⟨a, ha⟩⟩
      · exact htinv
    | algebraMap q =>
      obtain ⟨k, hk⟩ := exists_pow_mul_mem p q
      let z : ℤ_[p] := ⟨_, (PadicInt.mem_subring_iff p).mpr hk⟩
      have hz : toBdR p (zpB p z) ∈ f.range := ⟨_, hInt ⟨_, zpB_mem p z⟩⟩
      have h := f.range.mul_mem (f.range.pow_mem hpinv k) hz
      rwa [toBdR_zpB, ← map_pow, ← map_mul, show algebraMap ℤ_[p] ℚ_[p] z = (p : ℚ_[p])^k*q
        from rfl, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
        one_pow, one_mul] at h
    | add _ _ _ _ hx hy => exact f.range.add_mem hx hy
    | mul _ _ _ _ hx hy => exact f.range.mul_mem hx hy
  exact hmem _ x.property

private def maxEquiv {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    LocalizedMax p h ≃+* Bmax p :=
  RingEquiv.ofBijective _ ⟨maxLift_inj p h, maxLift_surj p h⟩

/-- Frobenius on the two actual coefficient rings, including their
inverted generators. -/
def localizedFrobenius {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Bmax p →+* CrystallineRing p h :=
  (crisLift p h).comp (maxEquiv p h).symm.toRingHom

/-- The localized map restricts to integral Frobenius. -/
theorem localizedFrobenius_integral {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (b : Amax p) :
    localizedFrobenius p h (maxEmbed p b) = integralToCris p h b := by
  have hh : maxEquiv p h (algebraMap (Amax p) (LocalizedMax p h) b) = maxEmbed p b := by
    change maxLift p h _ = _
    rw [maxLift, IsLocalization.Away.lift_eq]
  rw [← hh]
  change crisLift p h ((maxEquiv p h).symm ((maxEquiv p h) _)) = _
  rw [RingEquiv.symm_apply_apply, crisLift, IsLocalization.Away.lift_eq]

/-- Frobenius scales the cyclotomic period and every logarithm appearing
as a Galois shift of the semistable coordinate. -/
theorem localizedFrobenius_logTeich {ε ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (hε : ε.untilt = 1) :
    (localizedFrobenius p h ⟨toBdR p (logTeich p hε), LogPTransc.logTeich_mem_bmax p hε⟩ :
      BdR p) = p * toBdR p (logTeich p hε) := by
  change ((localizedFrobenius p h (maxEmbed p (logA p hε)) : CrystallineRing p h) :
    BdR p) = _
  rw [localizedFrobenius_integral, integralToCris_log]

private theorem localized_scalar {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) (q : ℚ_[p]) :
    localizedFrobenius p h (algebraMap ℚ_[p] (Bmax p) q) =
      algebraMap ℚ_[p] (CrystallineRing p h) q := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem p q
  let z : ℤ_[p] := ⟨_, (PadicInt.mem_subring_iff p).mpr hk⟩
  have h₁ : (algebraMap ℚ_[p] (Bmax p)) ((p : ℚ_[p])^k*q) =
      maxEmbed p ⟨zpB p z, zpB_mem p z⟩ := by
    apply Subtype.ext
    change _ = toBdR p (zpB p z)
    rw [toBdR_zpB]
    rfl
  have h₂ : integralToCris p h ⟨zpB p z, zpB_mem p z⟩ =
      algebraMap ℚ_[p] (CrystallineRing p h) ((p : ℚ_[p])^k*q) := by
    apply Subtype.ext
    change toBdR p (integralFrobenius p ⟨zpB p z, zpB_mem p z⟩).val = _
    rw [integralFrobenius_zp, toBdR_zpB]
    rfl
  have hh := (congrArg (localizedFrobenius p h) h₁).trans
    ((localizedFrobenius_integral p h _).trans h₂)
  simp only [map_mul, map_pow, map_natCast] at hh
  have hpU : IsUnit (p : CrystallineRing p h) := by
    simpa only [map_natCast] using ((IsUnit.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero)).map
      (algebraMap ℚ_[p] (CrystallineRing p h)))
  exact (hpU.pow k).mul_left_cancel hh

/-- Frobenius on the actual coefficient images as a p-adic algebra map. -/
def coefficientFrobenius {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Bmax p →ₐ[ℚ_[p]] CrystallineRing p h :=
  { localizedFrobenius p h with commutes' := localized_scalar p h }

/-- The Galois action on the maximal coefficient ring. -/
def maxGalois (σ : GQp p) : Bmax p →ₐ[ℚ_[p]] Bmax p :=
  ((bdrAlg p σ).comp (Bmax p).val).codRestrict (Bmax p)
    (fun b => bmax_stable p σ b.property)

/-- The localized coefficient Frobenius commutes with the actual
Galois action, including on the inverted generators. -/
theorem coefficientFrobenius_galois {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (σ : GQp p) (x : Bmax p) :
    (coefficientFrobenius p h (maxGalois p σ x) : BdR p) =
      bdrAct p σ (coefficientFrobenius p h x : BdR p) := by
  let F := (CrystallineRing p h).val.toRingHom.comp (localizedFrobenius p h)
  let G := (maxGalois p σ).toRingHom
  let j₁ := (F.comp G).comp (maxLift p h)
  let j₂ := ((bdrAct p σ).comp F).comp (maxLift p h)
  have jEq : j₁ = j₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator p h))
    apply RingHom.ext
    intro a
    have hm : maxLift p h (algebraMap (Amax p) (LocalizedMax p h) a) = maxEmbed p a := by
      rw [maxLift, IsLocalization.Away.lift_eq]
    have hg : G (maxEmbed p a) = maxEmbed p (galoisMaximal p σ a) := by
      apply Subtype.ext
      exact bdrAct_toBdR p σ a.val
    change (localizedFrobenius p h
      (G (maxLift p h (algebraMap (Amax p) (LocalizedMax p h) a))) : BdR p) =
      bdrAct p σ (localizedFrobenius p h (maxLift p h (algebraMap (Amax p) (LocalizedMax p h) a)) :
        BdR p)
    rw [hm, hg, localizedFrobenius_integral, localizedFrobenius_integral]
    change toBdR p (integralFrobenius p (galoisMaximal p σ a)).val =
      bdrAct p σ (toBdR p (integralFrobenius p a).val)
    rw [bdrAct_toBdR]
    exact congrArg (toBdR p) (integralFrobenius_galois p σ a)
  obtain ⟨y, rfl⟩ := maxLift_surj p h x
  exact DFunLike.congr_fun jEq y

end ZInQ.Manuscript.BergerComparison

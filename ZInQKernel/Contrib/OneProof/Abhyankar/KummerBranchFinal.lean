import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBranch

/-!
# abhyankar: `KummerUnramBranch` (the base change from `A₁_(t₁)` to `A''_P`)

* `finrank_le_of_adjoin` — if `Ω₁ = L[t₁]` and `t₁` lies in a subfield `KR ⊇ K`, then `[Ω₁ : KR] ≤ [L : K]`
  (`Ω₁` is the `KR`-span of a `K`-basis of `L`);
* `sep_of_finrank_lt` — over a DVR of residue characteristic `0` or `p`, residue extensions of degree `< p` of a
  finite separable extension of degree `< p` are separable.
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem finrank_le_of_adjoin {K KR L Ω₁ : Type} [Field K] [Field KR] [Field L] [Field Ω₁]
    [Algebra K KR] [Algebra K L] [Algebra K Ω₁] [Algebra KR Ω₁] [Algebra L Ω₁]
    [IsScalarTower K KR Ω₁] [IsScalarTower K L Ω₁] [FiniteDimensional K L] (t₁ : Ω₁)
    (ht : t₁ ∈ Set.range (algebraMap KR Ω₁)) (hadj : Algebra.adjoin L {t₁} = ⊤) :
    FiniteDimensional KR Ω₁ ∧ Module.finrank KR Ω₁ ≤ Module.finrank K L := by
  classical
  let b := Module.finBasis K L
  let V : Submodule KR Ω₁ := Submodule.span KR (Set.range (fun i => algebraMap L Ω₁ (b i)))
  have hL : ∀ l : L, algebraMap L Ω₁ l ∈ V := by
    intro l
    rw [← b.sum_repr l, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have : algebraMap L Ω₁ (b.repr l i • b i) =
        algebraMap K KR (b.repr l i) • algebraMap L Ω₁ (b i) := by
      rw [algebraMap_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmul : ∀ x y, x ∈ V → y ∈ V → x * y ∈ V := by
    intro x y hx hy
    have h1 : x * y ∈ V * V := Submodule.mul_mem_mul hx hy
    have h2 : V * V ≤ V := by
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      show algebraMap L Ω₁ (b i) * algebraMap L Ω₁ (b j) ∈ V
      rw [← map_mul]
      exact hL _
    exact h2 h1
  have ht' : t₁ ∈ V := by
    obtain ⟨k, rfl⟩ := ht
    have : algebraMap KR Ω₁ k = k • algebraMap L Ω₁ 1 := by rw [map_one, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hL 1)
  have htop : ∀ x : Ω₁, x ∈ V := by
    intro x
    have hx : x ∈ Algebra.adjoin L {t₁} := by rw [hadj]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact ht'
    | algebraMap l => exact hL l
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact hmul x y hx hy
  have hVtop : V = ⊤ := eq_top_iff.mpr (fun x _ => htop x)
  haveI : FiniteDimensional KR V := FiniteDimensional.span_of_finite KR (Set.finite_range _)
  haveI : FiniteDimensional KR Ω₁ :=
    Module.Finite.equiv ((LinearEquiv.ofEq V ⊤ hVtop).trans Submodule.topEquiv)
  refine ⟨inferInstance, ?_⟩
  have h1 := finrank_range_le_card (R := KR) (b := fun i => algebraMap L Ω₁ (b i))
  rw [Fintype.card_fin] at h1
  rw [← finrank_top KR Ω₁, ← hVtop]
  exact h1

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 3200000 in
/-- The branch case once `T₁ = A₁_(t₁)` and `T = A''_P` are given: `Ω₁/Frac(T₁)` is unramified over `T₁`
(index `1` by `branch_e`, separable residue fields since the degree is `< p`), then base change. -/
theorem branch_final {A K L Ω Ω₁ : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
    [Field Ω] [Field Ω₁] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra L Ω₁] [Algebra K Ω₁] [Algebra A Ω₁]
    [IsScalarTower A K Ω₁] [IsScalarTower K L Ω₁] [Algebra.IsSeparable K Ω₁]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [FiniteDimensional K Ω] [Algebra.IsSeparable K Ω]
    (p : ℕ) (hp : p.Prime) (hpm : (p : A) ∈ maximalIdeal A) (hdeg : Module.finrank K L < p)
    (t₁ : Ω₁) (hadj₁ : Algebra.adjoin L {t₁} = ⊤)
    (A₁ : Subalgebra A Ω₁) [IsLocalRing A₁] [Algebra.IsIntegral A A₁] (s : A₁) (hs : (s : Ω₁) = t₁)
    (hsp : (Ideal.span {s}).IsPrime) (hsm : s ∈ maximalIdeal A₁)
    (hbe : ∀ Q₁ : Ideal (integralClosure A₁ Ω₁), [Q₁.IsPrime] → Q₁.under A₁ = Ideal.span {s} →
      Q₁.ramificationIdx A₁ = 1)
    (B : Subalgebra A Ω) [IsNoetherianRing B] [IsIntegrallyClosed B]
    (Q : Ideal (integralClosure B Ω)) [Q.IsPrime] (hP : (Q.under B).height = 1)
    (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra B T]
    [IsLocalization.AtPrime T (Q.under B)] [Algebra T Ω] [IsScalarTower B T Ω]
    (T₁ : Type) [CommRing T₁] [IsDomain T₁] [IsDiscreteValuationRing T₁] [Algebra A₁ T₁]
    [IsLocalization.AtPrime T₁ (Ideal.span {s})] [Algebra T₁ Ω₁] [IsScalarTower A₁ T₁ Ω₁]
    (ι : Ω₁ →+* Ω) (σ : T₁ →+* T) (hσ : ∀ x, algebraMap T Ω (σ x) = ι (algebraMap T₁ Ω₁ x))
    (hgen : letI := ι.toAlgebra; IntermediateField.adjoin Ω₁ (Set.range (algebraMap B Ω)) = ⊤) :
    Algebra.IsUnramifiedAt B Q := by
  classical
  haveI := hsp
  have hBΩ : Function.Injective (algebraMap B Ω) := Subtype.val_injective
  have hA₁Ω₁ : Function.Injective (algebraMap A₁ Ω₁) := Subtype.val_injective
  have hT₁Ω₁ : Function.Injective (algebraMap T₁ Ω₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {s}).primeCompl x
    have h1 : algebraMap T₁ Ω₁ (IsLocalization.mk' T₁ b c) * algebraMap A₁ Ω₁ c = algebraMap A₁ Ω₁ b := by
      rw [IsScalarTower.algebraMap_apply A₁ T₁ Ω₁ c, IsScalarTower.algebraMap_apply A₁ T₁ Ω₁ b, ← map_mul,
        IsLocalization.mk'_spec]
    simp only at hx
    rw [hx, zero_mul] at h1
    have hb : b = 0 := hA₁Ω₁ (by rw [← h1, map_zero])
    simp [hb]
  haveI : FaithfulSMul T₁ Ω₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hT₁Ω₁
  letI : Algebra (FractionRing T₁) Ω₁ := FractionRing.liftAlgebra T₁ Ω₁
  haveI : IsScalarTower T₁ (FractionRing T₁) Ω₁ := FractionRing.isScalarTower_liftAlgebra _ _
  have hAΩ₁ : Function.Injective (algebraMap A Ω₁) := by
    rw [IsScalarTower.algebraMap_eq A K Ω₁]
    exact (algebraMap K Ω₁).injective.comp (IsFractionRing.injective A K)
  have hcomp : ∀ z : A, algebraMap (FractionRing T₁) Ω₁
      (((algebraMap T₁ (FractionRing T₁)).comp ((algebraMap A₁ T₁).comp (algebraMap A A₁))) z) =
      algebraMap A Ω₁ z := by
    intro z
    show algebraMap (FractionRing T₁) Ω₁ (algebraMap T₁ (FractionRing T₁)
      (algebraMap A₁ T₁ (algebraMap A A₁ z))) = _
    rw [← IsScalarTower.algebraMap_apply T₁ (FractionRing T₁) Ω₁,
      ← IsScalarTower.algebraMap_apply A₁ T₁ Ω₁, ← IsScalarTower.algebraMap_apply A A₁ Ω₁]
  have hinjK : Function.Injective ((algebraMap T₁ (FractionRing T₁)).comp
      ((algebraMap A₁ T₁).comp (algebraMap A A₁))) := by
    intro x y hxy
    apply hAΩ₁
    have := congrArg (algebraMap (FractionRing T₁) Ω₁) hxy
    rwa [hcomp, hcomp] at this
  letI : Algebra K (FractionRing T₁) := (IsFractionRing.lift hinjK).toAlgebra
  haveI : IsScalarTower K (FractionRing T₁) Ω₁ := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A K Ω₁]
    show algebraMap A Ω₁ a = algebraMap _ Ω₁ (IsFractionRing.lift hinjK (algebraMap A K a))
    rw [IsFractionRing.lift_algebraMap, hcomp])
  obtain ⟨hfd, hfr⟩ := finrank_le_of_adjoin (K := K) (KR := FractionRing T₁) (L := L) t₁
    ⟨algebraMap T₁ (FractionRing T₁) (algebraMap A₁ T₁ s), by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]; exact hs⟩ hadj₁
  haveI := hfd
  haveI : Algebra.IsSeparable (FractionRing T₁) Ω₁ := Algebra.isSeparable_tower_top_of_isSeparable K _ Ω₁
  have hP0 : ∀ x ∈ (Ideal.span {s}).primeCompl, algebraMap A₁ Ω₁ x ≠ 0 := fun x hx h0 =>
    hx (by rw [hA₁Ω₁ (h0.trans (map_zero _).symm)]; exact Ideal.zero_mem _)
  letI : Algebra (integralClosure A₁ Ω₁) (integralClosure T₁ Ω₁) := (TsKummer.intClIncl A₁ T₁ Ω₁).toAlgebra
  obtain ⟨hI1, hI2, hI3⟩ := TsKummer.intCl_isLocalization A₁ T₁ Ω₁ (Ideal.span {s}).primeCompl hP0
  have hL₁ : ∀ (Q₀ : Ideal (integralClosure T₁ Ω₁)) [Q₀.IsPrime] [Q₀.LiesOver (maximalIdeal T₁)],
      Q₀.ramificationIdx T₁ = 1 ∧
      Algebra.IsSeparable (T₁ ⧸ maximalIdeal T₁) (integralClosure T₁ Ω₁ ⧸ Q₀) := by
    intro Q₀ _ _
    constructor
    · set P0' := Q₀.comap (algebraMap (integralClosure A₁ Ω₁) (integralClosure T₁ Ω₁))
      haveI : P0'.LiesOver (Ideal.span {s}) :=
        IsLocalization.AtPrime.liesOver_comap_of_liesOver (Ideal.span {s}) T₁ Q₀
      haveI : P0'.IsPrime := Ideal.IsPrime.comap _
      have hQ : Q₀ = P0'.map (algebraMap _ _) :=
        (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure A₁ Ω₁)
          (Ideal.span {s}).primeCompl) (integralClosure T₁ Ω₁) Q₀).symm
      rw [hQ, IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx (Ideal.span {s}) T₁
        (integralClosure T₁ Ω₁) P0']
      exact hbe P0' (Ideal.LiesOver.over (P := P0') (p := Ideal.span {s})).symm
    · haveI : Q₀.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := T₁) Q₀
        (by rw [← Ideal.LiesOver.over (P := Q₀) (p := maximalIdeal T₁)]; infer_instance)
      letI : Field (T₁ ⧸ maximalIdeal T₁) := Ideal.Quotient.field _
      letI : Field (integralClosure T₁ Ω₁ ⧸ Q₀) := Ideal.Quotient.field _
      haveI : IsDedekindDomain (integralClosure T₁ Ω₁) :=
        IsIntegralClosure.isDedekindDomain T₁ (FractionRing T₁) Ω₁ _
      haveI : IsFractionRing (integralClosure T₁ Ω₁) Ω₁ :=
        integralClosure.isFractionRing_of_finite_extension (FractionRing T₁) Ω₁
      haveI : Module.Finite T₁ (integralClosure T₁ Ω₁) :=
        IsIntegralClosure.finite T₁ (FractionRing T₁) Ω₁ _
      haveI : Module.IsTorsionFree T₁ (integralClosure T₁ Ω₁) := by
        rw [Module.isTorsionFree_iff_algebraMap_injective]
        intro x y hxy
        exact hT₁Ω₁ (congrArg Subtype.val hxy)
      haveI : NoZeroSMulDivisors T₁ (integralClosure T₁ Ω₁) := ⟨fun {c x} h => by
        rw [Algebra.smul_def] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · left
          exact hT₁Ω₁ (by rw [map_zero]; exact congrArg Subtype.val h1)
        · exact Or.inr h1⟩
      have hne : maximalIdeal T₁ ≠ ⊥ := IsDiscreteValuationRing.not_a_field T₁
      have hdeg' := Ideal.inertiaDeg_le_finrank (integralClosure T₁ Ω₁) (FractionRing T₁) Ω₁ Q₀ hne
      rw [Ideal.inertiaDeg_algebraMap] at hdeg'
      have hfin : Module.finrank (T₁ ⧸ maximalIdeal T₁) (integralClosure T₁ Ω₁ ⧸ Q₀) < p :=
        lt_of_le_of_lt (hdeg'.trans hfr) hdeg
      haveI : Module.Finite (T₁ ⧸ maximalIdeal T₁) (integralClosure T₁ Ω₁ ⧸ Q₀) := inferInstance
      rcases CharP.char_is_prime_or_zero (T₁ ⧸ maximalIdeal T₁) (ringChar (T₁ ⧸ maximalIdeal T₁))
        with hq | hq
      · have hqp : ringChar (T₁ ⧸ maximalIdeal T₁) = p := by
          by_contra hne'
          have hqm : ((ringChar (T₁ ⧸ maximalIdeal T₁) : ℕ) : T₁) ∈ maximalIdeal T₁ := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]
          have hq₁ : ((ringChar (T₁ ⧸ maximalIdeal T₁) : ℕ) : A₁) ∈ maximalIdeal A₁ := by
            have h1 : ((ringChar (T₁ ⧸ maximalIdeal T₁) : ℕ) : A₁) ∈ (maximalIdeal T₁).under A₁ := by
              rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hqm
            rw [IsLocalization.AtPrime.under_maximalIdeal T₁ (Ideal.span {s})] at h1
            exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsm)) h1
          have hqA : ((ringChar (T₁ ⧸ maximalIdeal T₁) : ℕ) : A) ∈ maximalIdeal A := by
            have h1 : ((ringChar (T₁ ⧸ maximalIdeal T₁) : ℕ) : A) ∈ (maximalIdeal A₁).under A := by
              rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hq₁
            rwa [IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A (maximalIdeal A₁))] at h1
          have := isUnit_natCast_of_not_dvd hp hpm (n := ringChar (T₁ ⧸ maximalIdeal T₁))
            (fun h => hne' ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm)
          exact (mem_maximalIdeal _).mp hqA this
        haveI : CharP (T₁ ⧸ maximalIdeal T₁) p := hqp ▸ ringChar.charP _
        haveI : Fact p.Prime := ⟨hp⟩
        exact PropTSGlue.isSeparable_of_finrank_lt p hfin
      · haveI : CharP (T₁ ⧸ maximalIdeal T₁) 0 := hq ▸ ringChar.charP _
        haveI : CharZero (T₁ ⧸ maximalIdeal T₁) := CharP.charP_to_charZero _
        haveI : Algebra.IsAlgebraic (T₁ ⧸ maximalIdeal T₁) (integralClosure T₁ Ω₁ ⧸ Q₀) :=
          Algebra.IsIntegral.isAlgebraic
        exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact unram_of_baseChange (A₀ := A) (K₀ := K) hBΩ Q hP T T₁ (FractionRing T₁) Ω₁ ι σ hσ hgen hL₁

end Abhyankar

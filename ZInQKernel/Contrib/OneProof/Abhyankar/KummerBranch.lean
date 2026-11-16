import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnram

/-!
# abhyankar: `KummerUnramBranch` (Abhyankar's lemma for DVRs at `(f)`)

* `branch_e` — for `Ω₁ = L(t₁)`, `t₁^N = f`, and `A₁ = A[t₁, g] ⊆ Ω₁` (regular local of dimension 2 with
  maximal ideal `(t₁, g)`, `KummerBase`), every prime of the integral closure of `A₁` in `Ω₁` over `(t₁)` has
  ramification index `1` over `A₁`: Abhyankar's lemma for DVRs (`HDec.HSyn.t2_proved`) at `A_(f)` gives index `N`
  over `A`, `(t₁)` has index `N` over `A` (`A₁_(t₁)` is a DVR with uniformizer `t₁`, `f = t₁^N`), and indices
  multiply (`A₁ → A₁^{Ω₁}` is free, `TPurity3.normalFreeDim2`). Adapted from `TsKummer.abhyankar_core`
  (ZInQKernel/OneProof/H/TailG.lean), without its `ℚ`-algebra and Dedekind hypotheses.
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem kummerBase' (A Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field Ω]
    [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω)) (hdim : ringKrullDim A = 2)
    (f g : A) (hm : maximalIdeal A = Ideal.span {f, g}) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (t u : Ω) (ht : t ^ a = algebraMap A Ω f) (hu : u ^ b = algebraMap A Ω g)
    (A₁ : Subalgebra A Ω) (hA₁ : A₁ = Algebra.adjoin A {t, u}) (s v : A₁) (hs : (s : Ω) = t)
    (hv : (v : Ω) = u) :
    IsRegularLocalRing A₁ ∧ ringKrullDim A₁ = 2 ∧ ∃ _ : IsLocalRing A₁, maximalIdeal A₁ = Ideal.span {s, v} := by
  subst hA₁
  obtain ⟨hreg, hdim', hmax⟩ := kummerBase A Ω hinj hdim f g hm a b ha hb t u ht hu
  have e1 : s = ⟨t, Algebra.subset_adjoin (by simp)⟩ := Subtype.ext hs
  have e2 : v = ⟨u, Algebra.subset_adjoin (by simp)⟩ := Subtype.ext hv
  subst e1 e2
  exact ⟨hreg, hdim', hreg.toIsLocalRing, (IsLocalRing.eq_maximalIdeal hmax).symm⟩

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 3200000 in
theorem branch_e (A K L Ω₁ : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K]
    [Field L] [Field Ω₁] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L Ω₁] [Algebra K Ω₁]
    [Algebra A Ω₁] [IsScalarTower A K Ω₁] [IsScalarTower K L Ω₁] [FiniteDimensional L Ω₁]
    (hdim : ringKrullDim A = 2) (f g : A) (hm : maximalIdeal A = Ideal.span {f, g})
    (hfp : (Ideal.span {f}).IsPrime) (p : ℕ) (hp : p.Prime) (hpm : (p : A) ∈ maximalIdeal A)
    (hdeg : Module.finrank K L < p) (t₁ : Ω₁) (ht₁ : t₁ ^ Module.finrank K L = algebraMap A Ω₁ f)
    (hadj₁ : IntermediateField.adjoin L {t₁} = ⊤)
    (A₁ : Subalgebra A Ω₁) (hA₁ : A₁ = Algebra.adjoin A {t₁, algebraMap A Ω₁ g}) (s g₁ : A₁)
    (hs : (s : Ω₁) = t₁) (hg₁ : (g₁ : Ω₁) = algebraMap A Ω₁ g)
    (Q₁ : Ideal (integralClosure A₁ Ω₁)) [hQ₁p : Q₁.IsPrime] (hQ₁ : Q₁.under A₁ = Ideal.span {s}) :
    Q₁.ramificationIdx A₁ = 1 := by
  classical
  set N := Module.finrank K L with hNdef
  have hN : 0 < N := Module.finrank_pos
  have hAΩ : Function.Injective (algebraMap A Ω₁) := by
    rw [IsScalarTower.algebraMap_eq A K Ω₁]
    exact (algebraMap K Ω₁).injective.comp (IsFractionRing.injective A K)
  obtain ⟨hreg₁, hdim₁, hloc₁, hmaxA₁⟩ := kummerBase' A Ω₁ hAΩ hdim f g hm N 1 hN one_pos t₁
    (algebraMap A Ω₁ g) ht₁ (pow_one _) A₁ hA₁ s g₁ hs hg₁
  haveI := hreg₁
  haveI hsp : (Ideal.span {s}).IsPrime :=
    span_prime_of_pair hdim₁ (x := g₁) (y := s) (by rw [hmaxA₁, TPurity3.span_pair_comm])
  haveI : IsIntegrallyClosed A := TPurity3.isIntegrallyClosed_of_dim2 hdim
  haveI : IsIntegrallyClosed A₁ := TPurity3.isIntegrallyClosed_of_dim2 hdim₁
  have hf0 : f ≠ 0 := TPurity3.ne_zero_of_pair hm (TPurity3.height_maximalIdeal_of_dim2 hdim)
  have hfm : f ∈ maximalIdeal A := by rw [hm]; exact Ideal.subset_span (by simp)
  have hp₀1 : (Ideal.span {f}).height = 1 := by
    apply le_antisymm (Ideal.height_span_singleton_le_one ((mem_maximalIdeal f).mp hfm))
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    have := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [Ideal.span_singleton_eq_bot] at this
    exact hf0 this
  haveI : IsDomain (Localization.AtPrime (Ideal.span {f})) :=
    IsLocalization.isDomain_localization (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f})) := dvr_atPrime (Ideal.span {f}) hp₀1
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) K := IsLocalization.localizationAlgebraOfSubmonoidLe _ K
    (Ideal.span {f}).primeCompl (nonZeroDivisors A) (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K _ _ (Ideal.span {f}).primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing (Localization.AtPrime (Ideal.span {f})) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {f}).primeCompl _ K
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) L :=
    ((algebraMap K L).comp (algebraMap (Localization.AtPrime (Ideal.span {f})) K)).toAlgebra
  letI : Algebra (Localization.AtPrime (Ideal.span {f})) Ω₁ :=
    ((algebraMap K Ω₁).comp (algebraMap (Localization.AtPrime (Ideal.span {f})) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime (Ideal.span {f})) K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (Localization.AtPrime (Ideal.span {f})) K Ω₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L x = algebraMap K L (algebraMap (Localization.AtPrime (Ideal.span {f})) K (algebraMap A _ x))
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) K,
      ← IsScalarTower.algebraMap_apply A K L])
  haveI : IsScalarTower A (Localization.AtPrime (Ideal.span {f})) Ω₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A Ω₁ x = algebraMap K Ω₁ (algebraMap (Localization.AtPrime (Ideal.span {f})) K (algebraMap A _ x))
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) K,
      ← IsScalarTower.algebraMap_apply A K Ω₁])
  have hPM : ∀ x ∈ (Ideal.span {f}).primeCompl, algebraMap A Ω₁ x ≠ 0 := fun x hx h0 =>
    hx (by rw [hAΩ (h0.trans (map_zero _).symm)]; exact (Ideal.span {f}).zero_mem)
  have hmaxRp : maximalIdeal (Localization.AtPrime (Ideal.span {f})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {f})) f} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])
  have hirr : Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmaxRp
  have hunit : IsUnit (N : Localization.AtPrime (Ideal.span {f})) := by
    have := (isUnit_natCast_of_not_dvd hp hpm (n := N)
      (fun h => absurd (Nat.le_of_dvd hN h) (not_le.mpr hdeg))).map (algebraMap A (Localization.AtPrime (Ideal.span {f})))
    rwa [map_natCast] at this
  have htame := tame_at p hp hpm hdeg (Ideal.span {f}) (Localization.AtPrime (Ideal.span {f})) (K := K) (L := L)
  have hyp : ∀ (Q : Ideal (integralClosure (Localization.AtPrime (Ideal.span {f})) L)) [Q.IsPrime]
      [Q.LiesOver (maximalIdeal (Localization.AtPrime (Ideal.span {f})))],
      IsUnit ((Q.ramificationIdx (Localization.AtPrime (Ideal.span {f})) : ℕ) : Localization.AtPrime (Ideal.span {f})) ∧
      Q.ramificationIdx (Localization.AtPrime (Ideal.span {f})) ∣ N ∧
      Algebra.IsSeparable (Localization.AtPrime (Ideal.span {f}) ⧸ maximalIdeal (Localization.AtPrime (Ideal.span {f})))
        (integralClosure (Localization.AtPrime (Ideal.span {f})) L ⧸ Q) :=
    fun Q _ _ => ⟨(htame Q).2.1, (htame Q).1, (htame Q).2.2⟩
  have ht : t₁ ^ N = algebraMap (Localization.AtPrime (Ideal.span {f})) Ω₁ (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) := by
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f})) Ω₁]; exact ht₁
  have key := HDec.HSyn.t2_proved (Localization.AtPrime (Ideal.span {f})) K L Ω₁
    (algebraMap A (Localization.AtPrime (Ideal.span {f})) f) hirr N hN hunit hyp t₁ ht hadj₁
  sorry

end Abhyankar

import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalFinal
import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Count

/-!
# GenusOdd: the inert clause of `LocalFactorK` at a prime of good reduction (PROVED)

At a prime `𝔭` of `K` with `N𝔭 = p²` above a prime `p` of good reduction for `E`, the rational
model `W₀ = C₀ • E` that is minimal over `ℚ_v` has unit discriminant, so it is minimal over `𝓞_𝔭`
too (as in clause 2, `localFactorK_clause_good`). Its reduction over `𝓞_𝔭` is the base change of its
reduction `Ẽ` over `𝔽_p` along a ring homomorphism `𝔽_p → k_𝔭` (`reduction_map_eq_of_rat_hom`),
and `k_𝔭` has `p²` elements, so `#Ẽ(k_𝔭) = p² + 1 − (a_p² − 2p)`
(`Frobenius.natCard_points_quadratic_trace`). Hence `L_𝔭(T²) = L_p(T) L_p(−T)`
(`localFactorInert_good`).

* `LocalFactorInertGood`: the inert clause when `E` is good at `p`. PROVED.
* `LocalFactorInertBad`: the inert clause when `E` is bad at `p` (multiplicative or additive
  reduction under an unramified quadratic extension). GLUE.
* `localFactorInert_of_bad`: `LocalFactorInertBad → LocalFactorInert` (PROVED), so the bad case
  is the only remaining local input of `ArtinFactorization`
  (`artinFactorization_of_inertBad`, `genusLower34_of_inertBad`).
-/

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve Rat.HeightOneSpectrum IsLocalRing

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

section RatCompareHom

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {R' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  {F' : Type*} [Field F'] [Algebra R' F'] [IsFractionRing R' F']

/-- A ring homomorphism of residue fields of characteristic `p` maps the residue of an integral lift
of a rational number to the residue of any other integral lift (PROVED). -/
theorem residue_lift_compat_hom {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p]
    [CharP (ResidueField R') p] (ψ : ResidueField R →+* ResidueField R') {ι : ℚ →+* F}
    {ι' : ℚ →+* F'} {x : ℚ} {r : R} {r' : R'} (hr : algebraMap R F r = ι x)
    (hr' : algebraMap R' F' r' = ι' x) : ψ (residue R r) = residue R' r' := by
  have h := residue_mul_den hr
  have h' := residue_mul_den hr'
  have hd := den_ne_zero_of_lift (p := p) hr
  have hd' := den_ne_zero_of_lift (p := p) hr'
  have e1 : residue R r = (x.num : ResidueField R) / (x.den : ResidueField R) := by
    rw [eq_div_iff hd, h]
  have e2 : residue R' r' = (x.num : ResidueField R') / (x.den : ResidueField R') := by
    rw [eq_div_iff hd', h']
  rw [e1, e2, map_div₀, map_intCast, map_natCast]

/-- **The reductions of a rational Weierstrass curve over two DVRs correspond through any ring
homomorphism of the residue fields** (PROVED; `reduction_map_eq_of_rat` for an isomorphism). -/
theorem reduction_map_eq_of_rat_hom {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p]
    [CharP (ResidueField R') p] (ψ : ResidueField R →+* ResidueField R') (ι : ℚ →+* F)
    (ι' : ℚ →+* F') (W₀ : WeierstrassCurve ℚ) [IsMinimal R (W₀.map ι)]
    [IsMinimal R' (W₀.map ι')] :
    (W₀.map ι').reduction R' = ((W₀.map ι).reduction R).map ψ := by
  have c := fun {x : ℚ} {r : R} {r' : R'} (hr : algebraMap R F r = ι x)
    (hr' : algebraMap R' F' r' = ι' x) => residue_lift_compat_hom (p := p) ψ hr hr'
  ext
  · exact (c (integralModel_a₁_eq R (W₀.map ι)) (integralModel_a₁_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₂_eq R (W₀.map ι)) (integralModel_a₂_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₃_eq R (W₀.map ι)) (integralModel_a₃_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₄_eq R (W₀.map ι)) (integralModel_a₄_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₆_eq R (W₀.map ι)) (integralModel_a₆_eq R' (W₀.map ι'))).symm

end RatCompareHom

section Place

variable {K : Type} [Field K] [NumberField K]

/-- **The inert clause of `LocalFactorK` at a prime of good reduction** (PROVED): if `N𝔭 = p²`
and `E` is good at `p`, then `L_𝔭(T²) = L_p(T) L_p(−T)`. (Unramifiedness is not needed.) -/
theorem localFactorInert_good (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : 𝔭 ∈ primesAbove K (natGenerator v)) (hN : Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2)
    (hgood : GoodAt E v) :
    Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
      localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X) := by
  have hp := prime_natGenerator v
  set ιv := algebraMap ℚ (v.adicCompletion ℚ)
  obtain ⟨C₀, hC₀⟩ := exists_isMinimal_map (v.adicCompletionIntegers ℚ) ιv
    (decomp_D1 hp (mem_primesAbove_rat v) (absNorm_rat v) (unramifiedOver_rat v) _)
    (decomp_D2 hp (mem_primesAbove_rat v) (unramifiedOver_rat v) _) E
  -- good reduction of the rational model over `ℚ_v`
  have hEΔ : (E.map ιv).Δ ≠ 0 := by rw [map_Δ]; exact (map_ne_zero ιv).mpr E.isUnit_Δ.ne_zero
  have hgood₀ : ((C₀ • E).map ιv).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
    have h1 : (C₀ • E).map ιv = ((C₀.map ιv) *
        ((E.map ιv).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose⁻¹) •
        (E.map ιv).minimal (v.adicCompletionIntegers ℚ) := by
      rw [ZInQ.Literature.minimal_eq_smul, mul_smul, inv_smul_smul, map_variableChange]
    have hm : (((E.map ιv).minimal (v.adicCompletionIntegers ℚ))).Δ ≠ 0 := by
      rw [ZInQ.Literature.minimal_eq_smul, variableChange_Δ]
      exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hEΔ
    have : IsMinimal (v.adicCompletionIntegers ℚ) ((C₀.map ιv *
        ((E.map ιv).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose⁻¹) •
        (E.map ιv).minimal (v.adicCompletionIntegers ℚ)) := h1 ▸ hC₀
    have hg : ((E.map ιv).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
        (v.adicCompletionIntegers ℚ) := hgood
    rw [h1]
    exact (ZInQ.Manuscript.RC.TwistDictionary.hasGoodReduction_smul_iff _ hm _).mpr hg
  -- the rational discriminant is a `p`-adic unit
  have hunit := isUnit_integralModel_Δ (R := v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
  have hΔv : ιv (C₀ • E).Δ ≠ 0 ∧ ιv (C₀ • E).Δ ∈ v.adicCompletionIntegers ℚ ∧
      (ιv (C₀ • E).Δ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    have := (isUnit_lift_iff _).mp hunit
    have e : ((integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).Δ :
        v.adicCompletion ℚ) = ιv (C₀ • E).Δ := by
      have := integralModel_Δ_eq (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
      rw [map_Δ] at this
      exact this
    rwa [e] at this
  have hpΔ := (iota_unit_iff hp (mem_primesAbove_rat v) ιv _).mp hΔv
  have hΔk := (iota_unit_iff hp h𝔭 (iotaK 𝔭) _).mpr hpΔ
  -- integral over `𝓞_𝔭`, with unit discriminant: minimal
  have hint : IsIntegral (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) :=
    isIntegral_map_of_hint (𝔭.adicCompletionIntegers K) (iotaK 𝔭) ιv
      (hint_rat hp h𝔭 (mem_primesAbove_rat v) _ _) (C₀ • E) inferInstance
  have hmin : IsMinimal (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) := by
    have hI := integralModel_Δ_eq (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))
    rw [map_Δ] at hI
    have hu : IsUnit (integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ := by
      rw [isUnit_lift_iff]
      have e : ((integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ :
          𝔭.adicCompletion K) = iotaK 𝔭 (C₀ • E).Δ := hI
      rw [e]; exact hΔk
    have hnot : (integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ ∉
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ 12 := fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_le_self (by norm_num) h) hu
    have := ZInQ.Literature.isMinimal_baseChange_of_notMem (K := 𝔭.adicCompletion K) _ hnot
    rwa [baseChange_integralModel_eq] at this
  -- the residue fields
  have : Fact (natGenerator v).Prime := ⟨hp⟩
  have hfinv := finite_residueField (𝔭 := v)
  have hfink := finite_residueField (𝔭 := 𝔭)
  have hcv : Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = natGenerator v := by
    rw [natCard_residueField', absNorm_rat]
  have hck : Nat.card (ResidueField (𝔭.adicCompletionIntegers K)) = natGenerator v ^ 2 := by
    rw [natCard_residueField', hN]
  have := charP_residueField hp (mem_primesAbove_rat v)
  have := charP_residueField hp h𝔭
  let ψ : ResidueField (v.adicCompletionIntegers ℚ) →+* ResidueField (𝔭.adicCompletionIntegers K) :=
    (ZMod.castHom dvd_rfl _).comp
      (ringEquivOfCard hp hcv (by rw [Nat.card_eq_fintype_card, ZMod.card]) :
        ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (natGenerator v)).toRingHom
  have hred := reduction_map_eq_of_rat_hom (p := natGenerator v) ψ ιv (iotaK 𝔭) (C₀ • E)
  -- good reduction over `𝓞_𝔭`
  have hgoodk : ((C₀ • E).map (iotaK 𝔭)).HasGoodReduction (𝔭.adicCompletionIntegers K) := by
    rw [hasGoodReduction_iff_reduction_Δ, hred, map_Δ]
    exact (map_ne_zero ψ).mpr ((hasGoodReduction_iff_reduction_Δ _).mp hgood₀)
  have hΔ1 : ((C₀ • E).map ιv).Δ ≠ 0 := by
    rw [map_Δ]; exact (map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  have hΔ2 : ((C₀ • E).map (iotaK 𝔭)).Δ ≠ 0 := by
    rw [map_Δ]; exact (map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  rw [localPolyK_eq, localPolyQ_eq, ← localPolynomial_map_smul (iotaK 𝔭) E C₀,
    ← localPolynomial_map_smul ιv E C₀,
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal _ hΔ1,
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal _ hΔ2, ite_eq_left hgood₀,
    ite_eq_left hgoodk, hcv, hck]
  -- the point count over `k_𝔭 ≅ 𝔽_{p²}`
  have : ((C₀ • E).map ιv).reduction (v.adicCompletionIntegers ℚ) |>.IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction _).mp hgood₀
  let _ := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers ℚ))
  let _ := Fintype.ofFinite (ResidueField (𝔭.adicCompletionIntegers K))
  have hL : Fintype.card (ResidueField (𝔭.adicCompletionIntegers K)) =
      Fintype.card (ResidueField (v.adicCompletionIntegers ℚ)) ^ 2 := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcv, hck]
  have hcount := Frobenius.natCard_points_quadratic_trace
    (((C₀ • E).map ιv).reduction (v.adicCompletionIntegers ℚ)).toAffine ψ hL
  rw [Fintype.card_eq_nat_card, hcv] at hcount
  have hpts : Nat.card (((C₀ • E).map (iotaK 𝔭)).reduction (𝔭.adicCompletionIntegers K)).toAffine.Point
      = Nat.card ((((C₀ • E).map ιv).reduction (v.adicCompletionIntegers ℚ)).toAffine.map ψ).Point := by
    rw [hred]
  rw [hpts, hcount]
  push_cast
  simp only [map_sub, map_add, map_mul, map_pow, map_one, Polynomial.expand_X, Polynomial.expand_C,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.one_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.pow_comp,
    Polynomial.C_neg, map_ofNat]
  ring

end Place

/-- **Node `LocalFactorInertGood`** (the inert clause of `LocalFactorK` at a prime of good
reduction; the inert-prime case of the Euler-factor comparison behind `ArtinFactorization` and
(3.4)): for `N𝔭 = p²`, `𝔭² ∤ p` and `E` good at `p`, `L_𝔭(T²) = L_p(T) L_p(−T)`.
PROVED (`localFactorInertGood_proof`). -/
def LocalFactorInertGood : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (natGenerator v) →
      Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        GoodAt E v →
          Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
            localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)

theorem localFactorInertGood_proof : LocalFactorInertGood :=
  fun E _ _ _ _ 𝔭 v h𝔭 hN _ hg => localFactorInert_good E 𝔭 v h𝔭 hN hg

/-- **Node `LocalFactorInertBad`** (GLUE; the remaining local input of (3.4)): the inert clause of
`LocalFactorK` when `E` is bad at `p`. For `N𝔭 = p²`, `𝔭² ∤ p` (`K_𝔭/ℚ_p` unramified quadratic) and
`E` not good at `p`: `L_𝔭(T²) = L_p(T) L_p(−T)`, i.e. split multiplicative reduction stays split,
non-split becomes split, and additive stays additive. -/
def LocalFactorInertBad : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (natGenerator v) →
      Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        ¬ GoodAt E v →
          Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
            localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)

/-- **`LocalFactorInert` from its bad-reduction case** (PROVED): the good case is
`localFactorInertGood_proof`. -/
theorem localFactorInert_of_bad (h : LocalFactorInertBad) : LocalFactorInert := by
  intro E _ K _ _ 𝔭 v h𝔭 hN hu
  by_cases hg : GoodAt E v
  · exact localFactorInertGood_proof E K 𝔭 v h𝔭 hN hu hg
  · exact h E K 𝔭 v h𝔭 hN hu hg

/-- **`ArtinFactorization` from `HasseConvergence`, `ModularNewform` and `LocalFactorInertBad`**
(PROVED reduction). -/
theorem artinFactorization_of_inertBad (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInertBad) : ArtinFactorization :=
  artinFactorization_of_newform hH hMN (localFactorInert_of_bad h)

/-- **(3.4) from the printed leaves, `HasseConvergence`, `ModularNewform` and
`LocalFactorInertBad`** (PROVED reduction). -/
theorem genusLower34_of_inertBad (P : Prints) (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInertBad) : GenusLower34 :=
  genusLower34_of_newform P hH hMN (localFactorInert_of_bad h)

end ZInQ.Contrib.CloudB3RC53.GenusOdd

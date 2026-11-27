import ZInQKernel.Contrib.OneProof.RC.Height.ModelInvariance
import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST
import ZInQKernel.Contrib.OneProof.RC.Height.NonVacuity
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Glue
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Lane RC27 (item 7): RC19's G2 `LFactorizationConductorOne` from batch 3's `ArtinFactorization`

Lane RC19 (`BaseZeroCST.lean`) takes the conductor-one factorization of the 11/5 manuscript
(`diophantine_zq.tex`), tex 5736 "`L(E/K,s) = L(E,s)L(E^{(k)},s)`", read at tex 4345–4346 ("the
conductor-one height formula"), as its GLUE `LFactorizationConductorOne E K k`:

  `LSeries (twistedLFunction E (chiAt (conductorOrder K 1) 1)) s = L(E, s) L(E^{(k)}, s)`
  on `Re s > 3/2`, for `K = ℚ(√k)`.

The shared top layer states the ring-class factorization `GenusOdd.ArtinFactorization` (GLUE,
tex 2432 "the two Rankin products have the common factor `L(E^{(h)},s)`"): for `K` imaginary
quadratic of odd discriminant with the level primes split, `d₁ d₂ = disc(K) c²` (conditions as
there) and `χ = χ_{d₁} ∘ N` on `Pic(O_c)`,
`L(E/K, χ, s) = L(E^{(d₁)}, s) L(E^{(d₂)}, s)`. Lane RC22 recorded the two as MISMATCHED: the case
`c = 1`, `d₁ = 1` of the second gives `L(E^{(1)}, s) L(E^{(disc K)}, s)`, with the models
`qtwist E 1` and `qtwist E (disc K)`, not `L(E, s) L(E^{(k)}, s)`. This file closes the gap.

* `lFactorizationConductorOne_of_artin_of_odd`: **G2 from `ArtinFactorization`** at `c = 1`,
  `d₁ = 1`, `d₂ = disc K`, `χ = 1`, for `K` with odd discriminant and `k = disc(K) q²`, `q ≠ 0`.
  The side conditions of the Artin statement are checked (`isQuadRingClassChar_one`: `χ = 1` is
  `χ_1 ∘ N`; `disc K` prime to the level, `coprime_discr_of_splitsIn`), and the right side is moved
  to `L(E, s) L(E^{(k)}, s)` by the model invariance of Mathlib's `L`-series
  (`ModelInvariance.lean`: `L(E^{(1)}) = L(E)`, `L(E^{(d q²)}) = L(E^{(d)})`).
* `lFactorizationConductorOne_of_artin`: the same with the manuscript's hypotheses on `K`:
  **`K = ℚ(√k)`** (a square root `t ∈ K \ ℚ` of `k`; tex 2599 "Fix `k` and `K = ℚ(√k)`") and
  **`K` split at `2`** (tex 2720 "Let `K = ℚ(√k)` be imaginary, split at `2N`"; tex 2596 "negative
  discriminants square at `2N`"). Then `k = disc(K) q²` (`exists_eq_discr_mul_sq`, from batch 3's
  `Splitting.discr_eq_mul_sq`) and `disc K` is odd (`odd_discr_of_splitsIn_two`: a split prime is
  unramified, hence prime to the discriminant, `not_dvd_discr_of_splitsIn`, by Dedekind's
  criterion `NumberField.not_dvd_discr_iff_forall_liesOver`).
  `lFactorizationConductorOne_of_artin_of_two_dvd`: if `2` divides the level, the splitting at `2`
  is already a case of RC19's `hsplit`.
* `hheight_of_CST_of_artin`, `not_isOfFinAddOrder_of_CST_of_artin`: RC19's two consumers with the
  hypothesis `hL` replaced by `ArtinFactorization`, `SplitsIn K 2` and `K = ℚ(√k)`.
* `artinG2_field_hypotheses_nonvacuous`: **non-vacuity** of every hypothesis on `K` of the composed
  forms (RC19's `finrank = 2`, totally complex, `disc K ∉ {−3, −4}`, and the new ones: split at `2`,
  `t ∉ ℚ`, `t² = k`), all at once, by `K = ℚ(√−7)`, `k = −7`.

What remains GLUE is `ArtinFactorization` itself (batch 3; it is reduced there to local statements
in `GenusOdd/ArtinLocal.lean`). Every theorem in this file is PROVED. No DEPARTURE of substance:
the field `ℚ(√k)` is given as an abstract number field `K` with a square root of `k` outside `ℚ`.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex Polynomial

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

/-! ### The arithmetic side conditions -/

section Arith

variable {K : Type} [Field K] [NumberField K]

/-- **The trivial character of `Pic(O_1)` is `χ_1 ∘ N`** (PROVED): it is quadratic, and
`χ_1(N𝔭) = (N𝔭 / 1) = 1`. This is the hypothesis `IsQuadRingClassChar K c d₁ χ` of
`ArtinFactorization` at `c = 1`, `d₁ = 1`, `χ = 1`. -/
theorem isQuadRingClassChar_one (K : Type) [Field K] [NumberField K] :
    GenusOdd.IsQuadRingClassChar K 1 1 1 := by
  refine ⟨fun t => by simp, fun 𝔭 h _ => ?_⟩
  simp [GenusOdd.chiD, jacobiSym.one_right]

/-- **A split prime does not divide the discriminant** (PROVED; Dedekind's criterion,
`NumberField.not_dvd_discr_iff_forall_liesOver`): if `p 𝓞_K = 𝔭 𝔮` with `𝔭 ≠ 𝔮` maximal, every
prime above `p` is `𝔭` or `𝔮` and occurs once in `p 𝓞_K`, so it is unramified. -/
theorem not_dvd_discr_of_splitsIn {p : ℕ} (hp : p.Prime) (h : SplitsIn K p) :
    ¬ (p : ℤ) ∣ discr K := by
  obtain ⟨𝔭, 𝔮, h𝔭, h𝔮, hne, hpq⟩ := h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K) hpZ]
  intro P hP hlo
  have := hP.isPrime
  have hspan : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = 𝔭 * 𝔮 := by
    rw [Ideal.map_span, Set.image_singleton, ← hpq]
    simp
  have hne0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    simp [hp.ne_zero]
  have h𝔭0 : 𝔭 ≠ ⊥ := fun h0 => hne0 (by rw [hspan, h0, Ideal.bot_mul])
  have h𝔮0 : 𝔮 ≠ ⊥ := fun h0 => hne0 (by rw [hspan, h0, Ideal.mul_bot])
  have hPle : 𝔭 * 𝔮 ≤ P := by
    rw [← hspan, Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})).le
  have hPeq : P = 𝔭 ∨ P = 𝔮 := by
    rcases hP.isPrime.mul_le.mp hPle with h1 | h1
    · exact Or.inl (h𝔭.eq_of_le hP.ne_top h1).symm
    · exact Or.inr (h𝔮.eq_of_le hP.ne_top h1).symm
  have he : P.ramificationIdx ℤ = 1 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ P hne0, hspan,
      UniqueFactorizationMonoid.normalizedFactors_mul h𝔭0 h𝔮0,
      UniqueFactorizationMonoid.normalizedFactors_irreducible
        (Ideal.prime_of_isPrime h𝔭0 h𝔭.isPrime).irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible
        (Ideal.prime_of_isPrime h𝔮0 h𝔮.isPrime).irreducible,
      normalize_eq, normalize_eq, Multiset.count_add]
    rcases hPeq with rfl | rfl
    · simp [hne]
    · simp [Ne.symm hne]
  exact Ideal.ramificationIdx_eq_one_iff.mp he

/-- **`K` split at `2` has odd discriminant** (PROVED, from `not_dvd_discr_of_splitsIn`). This is
the hypothesis `Odd (disc K)` of `ArtinFactorization`; in the manuscript `K = ℚ(√k)` is split at
`2N` (tex 2720). -/
theorem odd_discr_of_splitsIn_two (h2 : SplitsIn K 2) : Odd (discr K) := by
  have h := not_dvd_discr_of_splitsIn Nat.prime_two h2
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact_mod_cast h

/-- **If every prime of `N` splits in `K`, then `disc K` is prime to `N`** (PROVED, from
`not_dvd_discr_of_splitsIn`). With `N` the level this is the hypothesis
`Nat.Coprime (d₁ d₂).natAbs N` of `ArtinFactorization` at `d₁ d₂ = disc K`. -/
theorem coprime_discr_of_splitsIn {N : ℕ} (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → SplitsIn K p) :
    Nat.Coprime (discr K).natAbs N := by
  refine Nat.coprime_of_dvd fun p hp hpD hpN => ?_
  exact not_dvd_discr_of_splitsIn hp (hsplit p hp hpN) (Int.natCast_dvd.mpr hpD)

/-- **`K = ℚ(√k)` gives `k = disc(K) q²` with `q ≠ 0`** (PROVED): for a square root `t ∈ K \ ℚ` of
`k`, the algebraic integer `θ = den(k) t` has `θ² = num(k) den(k)`, so (batch 3's
`Splitting.discr_eq_mul_sq`, change of basis from `(1, θ)` to an integral basis)
`disc K = 4 num(k) den(k) q₀² = k (2 den(k) q₀)²`. -/
theorem exists_eq_discr_mul_sq (hK2 : Module.finrank ℚ K = 2) {k : ℚ} {t : K}
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    ∃ q : ℚ, q ≠ 0 ∧ k = discr K * q ^ 2 := by
  set N : ℤ := k.num * k.den with hN
  have hden : (k.den : K) ≠ 0 := by exact_mod_cast k.den_nz
  have hkK : algebraMap ℚ K k = (k.num : K) / (k.den : K) := by
    rw [eq_ratCast, Rat.cast_def]
  set θK : K := (k.den : K) * t with hθK
  have hθ2 : θK ^ 2 = (N : K) := by
    rw [hθK, mul_pow, htk, hkK, hN]
    push_cast
    field_simp
  have hint : IsIntegral ℤ θK := by
    refine ⟨X ^ 2 - C N, by monicity!, ?_⟩
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hθ2, algebraMap_int_eq, eq_intCast,
      sub_self]
  have hθr : θK ∉ (algebraMap ℚ K).range := by
    rintro ⟨r, hr⟩
    apply ht
    refine ⟨r / k.den, ?_⟩
    rw [map_div₀, hr, map_natCast, hθK]
    field_simp
  let θ : 𝓞 K := ⟨θK, hint⟩
  have hmin : minpoly ℚ (θ : K) = X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((-N : ℤ) : ℚ) := by
    refine ZInQ.Contrib.CloudB3RC53.Splitting.minpoly_eq_of_aeval hK2 hθr 0 (-N) ?_
    rw [hθ2]
    push_cast
    ring
  obtain ⟨q, hq⟩ := ZInQ.Contrib.CloudB3RC53.Splitting.discr_eq_mul_sq hK2 hmin
  have hD0 : (discr K : ℚ) ≠ 0 := by exact_mod_cast discr_ne_zero K
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hD0
    rw [hq]
    ring
  have hden' : (k.den : ℚ) ≠ 0 := by exact_mod_cast k.den_nz
  refine ⟨(2 * k.den * q)⁻¹, by positivity, ?_⟩
  rw [hq, hN]
  push_cast
  conv_lhs => rw [← Rat.num_div_den k]
  field_simp
  ring

end Arith

/-! ### G2 from the Artin factorization -/

section G2

/-- **RC19's G2 from batch 3's `ArtinFactorization`, odd-discriminant form** (tex 5736, read at
tex 4345–4346; the Artin factorization of tex 2432 at conductor one). PROVED from the GLUE
`ArtinFactorization`: apply it at `c = 1`, `d₁ = 1`, `d₂ = disc K`, `χ = 1` (its side conditions:
`1 · disc K = disc K · 1²`, `1 ≡ 1 (mod 4)`, `1` squarefree, `1 ∣ 1`, `gcd(1, disc K) = 1`,
`disc K` prime to the level by `coprime_discr_of_splitsIn`, and `χ = 1` is `χ_1 ∘ N` by
`isQuadRingClassChar_one`), which gives `L(E/K, 1, s) = L(E^{(1)}, s) L(E^{(disc K)}, s)`; then
`L(E^{(1)}, s) = L(E, s)` (`LSeries_qtwist_one`) and `L(E^{(disc K)}, s) = L(E^{(k)}, s)` for
`k = disc(K) q²` (`LSeries_qtwist_of_eq_mul_sq`). -/
theorem lFactorizationConductorOne_of_artin_of_odd (hA : GenusOdd.ArtinFactorization)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hKc : IsTotallyComplex K) (hodd : Odd (discr K))
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    {k q : ℚ} (hq : q ≠ 0) (hk : k = discr K * q ^ 2) :
    LFactorizationConductorOne E K k := by
  intro s hs
  have hcop : Nat.Coprime ((1 : ℤ) * discr K).natAbs (newformLevel E) := by
    rw [one_mul]
    exact coprime_discr_of_splitsIn hsplit
  have h := hA E K hK2 hKc hodd hsplit 1 1 (discr K) (by push_cast; ring) (by norm_num)
    squarefree_one (by simp) (Nat.coprime_one_left _) hcop 1 (isQuadRingClassChar_one K) s hs
  rw [h, Int.cast_one, LSeries_qtwist_one, LSeries_qtwist_of_eq_mul_sq E hq hk]

/-- **RC19's G2 from batch 3's `ArtinFactorization`** (tex 5736 with tex 4345–4346; tex 2599
"Fix `k` and `K = ℚ(√k)`", tex 2720 "`K = ℚ(√k)` … imaginary, split at `2N`"). PROVED from the
GLUE `ArtinFactorization`, for `K` imaginary quadratic with the level primes split (RC19's
hypotheses), split at `2`, and `K = ℚ(√k)` in the form of a square root `t ∈ K \ ℚ` of `k`:
`k = disc(K) q²` by `exists_eq_discr_mul_sq` and `disc K` is odd by `odd_discr_of_splitsIn_two`;
then `lFactorizationConductorOne_of_artin_of_odd`. Non-vacuity of the hypotheses on `K`:
`artinG2_field_hypotheses_nonvacuous`. -/
theorem lFactorizationConductorOne_of_artin (hA : GenusOdd.ArtinFactorization)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hKc : IsTotallyComplex K) (h2 : SplitsIn K 2)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    {k : ℚ} {t : K} (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    LFactorizationConductorOne E K k := by
  obtain ⟨q, hq, hk⟩ := exists_eq_discr_mul_sq hK2 ht htk
  exact lFactorizationConductorOne_of_artin_of_odd hA E K hK2 hKc
    (odd_discr_of_splitsIn_two h2) hsplit hq hk

/-- **G2 when `2` divides the level** (PROVED): the splitting of `2` in `K` is then a case of
RC19's `hsplit`, so only `K = ℚ(√k)` is added to RC19's hypotheses. -/
theorem lFactorizationConductorOne_of_artin_of_two_dvd (hA : GenusOdd.ArtinFactorization)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hKc : IsTotallyComplex K)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (h2N : 2 ∣ newformLevel E)
    {k : ℚ} {t : K} (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    LFactorizationConductorOne E K k :=
  lFactorizationConductorOne_of_artin hA E K hK2 hKc (hsplit 2 Nat.prime_two h2N) hsplit ht htk

end G2

/-! ### RC19's consumers with `hL` replaced by `ArtinFactorization` -/

section Consumers

open Classical in
/-- **RC15's `hheight` from Cai–Shu–Tian and `ArtinFactorization`** (tex 4345–4346; tex 5736).
PROVED: RC19's `hheight_of_CST` with its GLUE hypothesis `hL : LFactorizationConductorOne E K k`
supplied by `lFactorizationConductorOne_of_artin` from batch 3's GLUE `ArtinFactorization`, `K`
split at `2` (`h2`, tex 2720) and `K = ℚ(√k)` (`t`, `ht`, `htk`, tex 2599). The other hypotheses
are RC19's, verbatim. -/
theorem hheight_of_CST_of_artin (E : WeierstrassCurve ℚ) [E.IsElliptic] (k : ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hA : GenusOdd.ArtinFactorization) (h2 : SplitsIn K 2) (t : K)
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    CSTThm11Split → ProductOrderGeTwo E k → IsOfFinAddOrder P :=
  hheight_of_CST E k f hf Lat hLat hnCM κ hκ K hK2 hKc hD3 hD4 hsplit A B C' hH ι y hy P hP
    (lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk)

open Classical in
/-- **The height formula makes the trace nontorsion at a known simple zero, with
`ArtinFactorization`** (tex 2464, 8268–8272). PROVED: RC19's `not_isOfFinAddOrder_of_CST` with
`hL` supplied by `lFactorizationConductorOne_of_artin` (hypotheses as in
`hheight_of_CST_of_artin`). -/
theorem not_isOfFinAddOrder_of_CST_of_artin (E : WeierstrassCurve ℚ) [E.IsElliptic] (k : ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hA : GenusOdd.ArtinFactorization) (h2 : SplitsIn K 2) (t : K)
    (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) (hCST : CSTThm11Split)
    (F : ℂ → ℂ) (hFd : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s * (qtwist E k).LSeries s)
    (hderiv : deriv F 1 ≠ 0) : ¬IsOfFinAddOrder P :=
  not_isOfFinAddOrder_of_CST E k f hf Lat hLat hnCM κ hκ K hK2 hKc hD3 hD4 hsplit A B C' hH ι y
    hy P hP (lFactorizationConductorOne_of_artin hA E K hK2 hKc h2 hsplit ht htk) hCST F hFd
    hFeq hderiv

end Consumers

/-! ### Non-vacuity: `K = ℚ(√−7)` -/

section NonVacuity

/-- `−7` is not a square in `ℚ` (PROVED), as an instance: it makes `ℚ(√−7)` a field. -/
instance fact_not_isSquare_neg_seven : Fact (¬IsSquare (-7 : ℚ)) :=
  ⟨by
    rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]⟩

/-- `√−7 ∉ ℚ` (PROVED). -/
theorem root_neg_seven_not_mem_range :
    SqrtField.root (-7) ∉ (algebraMap ℚ (SqrtField (-7))).range := by
  rintro ⟨r, hr⟩
  have h := SqrtField.root_sq (-7)
  rw [← hr, ← map_pow] at h
  have h' : r ^ 2 = -7 := (algebraMap ℚ (SqrtField (-7))).injective h
  nlinarith [sq_nonneg r]

/-- `ℚ(√−7)` is totally complex (PROVED, from `(√−7)² = −7 < 0`). -/
theorem isTotallyComplex_sqrtField_neg_seven : IsTotallyComplex (SqrtField (-7)) :=
  NumberField.isTotallyComplex_of_sq_ratCast_of_neg (SqrtField.root_sq (-7)) (by norm_num)

/-- **`2` splits in `ℚ(√−7)`** (PROVED): `θ = (1 + √−7)/2` is an algebraic integer with minimal
polynomial `X² − X + 2 ≡ X (X − 1) (mod 2)` and `2 ∤ disc(X² − X + 2) = −7`, so batch 3's
Kummer–Dedekind criterion `Splitting.splitsIn_of_factor` applies. -/
theorem splitsIn_two_sqrtField_neg_seven : SplitsIn (SqrtField (-7)) 2 := by
  have hK2 : Module.finrank ℚ (SqrtField (-7)) = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ (SqrtField (-7))
  have hr := SqrtField.root_sq (-7)
  rw [eq_ratCast] at hr
  set θK : SqrtField (-7) := (1 + SqrtField.root (-7)) / 2 with hθK
  have hθ : θK ^ 2 + ((-1 : ℤ) : SqrtField (-7)) * θK + ((2 : ℤ) : SqrtField (-7)) = 0 := by
    rw [hθK]
    push_cast at hr ⊢
    linear_combination (1 / 4 : SqrtField (-7)) * hr
  have hint : IsIntegral ℤ θK := by
    refine ⟨X ^ 2 - X + C 2, by monicity!, ?_⟩
    rw [← aeval_def, map_add, map_sub, map_pow, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast]
    have h := hθ
    push_cast at h ⊢
    linear_combination h
  have hθr : θK ∉ (algebraMap ℚ (SqrtField (-7))).range := by
    rintro ⟨r, hr'⟩
    apply root_neg_seven_not_mem_range
    refine ⟨2 * r - 1, ?_⟩
    rw [map_sub, map_mul, hr', map_one, map_ofNat, hθK]
    ring
  let θ : 𝓞 (SqrtField (-7)) := ⟨θK, hint⟩
  have hmin : minpoly ℚ (θ : SqrtField (-7)) =
      X ^ 2 + C ((-1 : ℤ) : ℚ) * X + C ((2 : ℤ) : ℚ) :=
    ZInQ.Contrib.CloudB3RC53.Splitting.minpoly_eq_of_aeval hK2 hθr (-1) 2 hθ
  exact ZInQ.Contrib.CloudB3RC53.Splitting.splitsIn_of_factor hK2 hmin (p := 2) (by norm_num) 0 1
    (by norm_num) (by norm_num) (by norm_num)

/-- **Non-vacuity of the hypotheses on `K`** (PROVED): `K = ℚ(√−7)`, `k = −7`, `t = √−7` satisfy at
once every hypothesis on `K` of `hheight_of_CST_of_artin` and `not_isOfFinAddOrder_of_CST_of_artin`
except the level-dependent `hsplit` (RC19's): `[K : ℚ] = 2`, `K` totally complex,
`disc K ≠ −3`, `disc K ≠ −4` (RC19's), and the new `K` split at `2`, `t ∉ ℚ`, `t² = k`. The
discriminant conditions follow from `−7 = disc(K) q²` (`exists_eq_discr_mul_sq`): `disc K` is odd,
and `−7 = −3 q²` has no rational solution (`3`-adic valuation `0 = 1 + 2 v₃(q)`). -/
theorem artinG2_field_hypotheses_nonvacuous :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (k : ℚ) (t : K),
      Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ discr K ≠ -3 ∧ discr K ≠ -4 ∧
        SplitsIn K 2 ∧ t ∉ (algebraMap ℚ K).range ∧ t ^ 2 = algebraMap ℚ K k := by
  have hK2 : Module.finrank ℚ (SqrtField (-7)) = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ (SqrtField (-7))
  have hodd := odd_discr_of_splitsIn_two splitsIn_two_sqrtField_neg_seven
  obtain ⟨q, hq, hk⟩ := exists_eq_discr_mul_sq hK2 root_neg_seven_not_mem_range
    (SqrtField.root_sq (-7))
  refine ⟨SqrtField (-7), inferInstance, inferInstance, -7, SqrtField.root (-7), hK2,
    isTotallyComplex_sqrtField_neg_seven, ?_, ?_, splitsIn_two_sqrtField_neg_seven,
    root_neg_seven_not_mem_range, SqrtField.root_sq (-7)⟩
  · intro hD
    rw [hD] at hk
    have h3 := congrArg (padicValRat 3) hk
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hq), padicValRat.pow] at h3
    have e7 : padicValRat 3 (-7 : ℚ) = 0 := by
      rw [show (-7 : ℚ) = -((7 : ℕ) : ℚ) by norm_num, padicValRat.neg, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]
    have e3 : padicValRat 3 ((-3 : ℤ) : ℚ) = 1 := by
      rw [show ((-3 : ℤ) : ℚ) = -((3 : ℕ) : ℚ) by norm_num, padicValRat.neg,
        padicValRat.self (by norm_num)]
    rw [e7, e3] at h3
    omega
  · intro hD
    rw [hD] at hodd
    exact absurd hodd (by decide)

end NonVacuity

end ZInQ.Manuscript.RC.Height

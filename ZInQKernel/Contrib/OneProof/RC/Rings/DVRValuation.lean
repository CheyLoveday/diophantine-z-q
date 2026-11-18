import Mathlib

/-!
# Lane RC20: the `ℤ`-valued valuation of the fraction field of a discrete valuation ring

Manuscript (`diophantine_zq.tex`, 11/5 version): Section 9 uses the two-adic valuation `v_𝒪` of the
complete DVR `𝒪 = \widehat{Λ_{(2)}}` on its fraction field (tex 4916–4918: "`v₂ u_prim ≥ −C(E,A)` ...
where the first valuation is that of `𝒪`"; tex 4830 "the two-adic valuation of `𝒪`, where `t` is a
unit"; tex 5698–5700 "`v_𝒪(f_x) ≤ c` ... `v_𝒪(ũ_x) ≥ −c`"), and the valuation of the DVR `Λ_{(2)}`
(tex 2747–2748). Mathlib has the `ℕ∞`-valued `IsDiscreteValuationRing.addVal` on a DVR but no ready
`ℤ`-valued valuation on its fraction field in the additive form `AddValuation K (WithTop ℤ)` used by
lane RC16 (`ValuationOfO`). This file constructs it for an arbitrary DVR `R` with a chosen uniformizer
`ϖ` and an arbitrary fraction field `K`:

* `exists_zpow_mul_unit`, `zpow_mul_unit_inj` : every nonzero `x ∈ K` is `ϖⁿ u` with `n ∈ ℤ` and
  `u ∈ Rˣ`, and `n` is unique;
* `dvrAddVal hϖ : AddValuation K (WithTop ℤ)`, `x = ϖⁿ u ↦ n`, `0 ↦ ⊤`;
* `dvrAddVal_zpow_mul_unit`, `dvrAddVal_uniformizer` (`v ϖ = 1`), `dvrAddVal_unit`,
  `dvrAddVal_eq_top_iff`, `dvrAddVal_nonneg_iff` (`0 ≤ v x ↔ x ∈ R`), `pow_dvd_iff_le_dvrAddVal`
  (`ϖᵏ ∣ r ↔ k ≤ v r`), `dvrAddVal_pos_iff` (`0 < v x ↔ x ∈ 𝔪_R`);
* `dvrAddVal_map`, `dvrAddVal_comap` : the valuation is compatible with every ring map of DVRs sending
  the uniformizer to the uniformizer (an unramified extension, such as `Λ_{(2)} → 𝒪`).

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

section DVRValuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The image of a nonzero element of `R` in `K` is nonzero. -/
theorem algebraMap_ne_zero_of_ne_zero' {r : R} (hr : r ≠ 0) : algebraMap R K r ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr

omit [IsDiscreteValuationRing R] in
/-- The image of a unit of `R` in `K` is nonzero. -/
theorem algebraMap_unit_ne_zero (u : Rˣ) : algebraMap R K (u : R) ≠ 0 :=
  algebraMap_ne_zero_of_ne_zero' u.ne_zero

/-- **Tex 2747–2748, 4916–4918, 4830 (PROVED).** Every nonzero element of the fraction field `K` of a
DVR `R` with uniformizer `ϖ` is `ϖⁿ u` with `n ∈ ℤ` and `u ∈ Rˣ`. -/
theorem exists_zpow_mul_unit (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = algebraMap R K ϖ ^ n * algebraMap R K (u : R) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := algebraMap_ne_zero_of_ne_zero' hϖ.ne_zero
  have hwK : algebraMap R K (w : R) ≠ 0 := algebraMap_unit_ne_zero w
  refine ⟨(m : ℤ) - n, u * w⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_mul, map_mul, map_pow, map_pow, zpow_sub₀ hϖK, zpow_natCast,
    zpow_natCast, map_units_inv]
  field_simp

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Tex 2747–2748, 4916–4918 (PROVED).** The exponent in `x = ϖⁿ u` is unique. -/
theorem zpow_mul_unit_inj (hϖ : Irreducible ϖ) {n m : ℤ} {u w : Rˣ}
    (h : algebraMap R K ϖ ^ n * algebraMap R K (u : R) =
      algebraMap R K ϖ ^ m * algebraMap R K (w : R)) : n = m := by
  wlog hnm : n ≤ m generalizing n m u w
  · exact (this h.symm (le_of_not_ge hnm)).symm
  obtain ⟨k, rfl⟩ := Int.le.dest hnm
  have hϖK : algebraMap R K ϖ ≠ 0 := algebraMap_ne_zero_of_ne_zero' hϖ.ne_zero
  rw [zpow_add₀ hϖK, zpow_natCast, mul_assoc] at h
  have h2 := mul_left_cancel₀ (zpow_ne_zero n hϖK) h
  rw [← map_pow, ← map_mul] at h2
  have h3 : (u : R) = ϖ ^ k * w := IsFractionRing.injective R K h2
  rcases k with _ | k
  · simp
  · exfalso
    apply hϖ.not_isUnit
    have hdvd : ϖ ∣ (u : R) := ⟨ϖ ^ k * w, by rw [h3, pow_succ]; ring⟩
    exact isUnit_of_dvd_unit hdvd u.isUnit

open Classical in
/-- The function underlying `dvrAddVal`: `0 ↦ ⊤`, `ϖⁿ u ↦ n`. -/
noncomputable def dvrValFun (hϖ : Irreducible ϖ) (x : K) : WithTop ℤ :=
  if hx : x = 0 then ⊤ else ((exists_zpow_mul_unit hϖ hx).choose : WithTop ℤ)

theorem dvrValFun_zero (hϖ : Irreducible ϖ) : dvrValFun hϖ (0 : K) = ⊤ := by
  simp [dvrValFun]

omit [IsDiscreteValuationRing R] in
theorem zpow_mul_unit_ne_zero (hϖ : Irreducible ϖ) (n : ℤ) (u : Rˣ) :
    algebraMap R K ϖ ^ n * algebraMap R K (u : R) ≠ 0 :=
  mul_ne_zero (zpow_ne_zero n (algebraMap_ne_zero_of_ne_zero' hϖ.ne_zero))
    (algebraMap_unit_ne_zero u)

theorem dvrValFun_eq (hϖ : Irreducible ϖ) {x : K} {n : ℤ} {u : Rˣ}
    (h : x = algebraMap R K ϖ ^ n * algebraMap R K (u : R)) : dvrValFun hϖ x = n := by
  have hx : x ≠ 0 := h ▸ zpow_mul_unit_ne_zero hϖ n u
  simp only [dvrValFun, hx, ↓reduceDIte]
  obtain ⟨u', hu'⟩ := (exists_zpow_mul_unit hϖ hx).choose_spec
  rw [zpow_mul_unit_inj hϖ (hu'.symm.trans h)]

theorem le_dvrValFun_add (hϖ : Irreducible ϖ) {n m : ℤ} (hnm : n ≤ m) (u w : Rˣ) :
    (n : WithTop ℤ) ≤ dvrValFun hϖ (algebraMap R K ϖ ^ n * algebraMap R K (u : R) +
      algebraMap R K ϖ ^ m * algebraMap R K (w : R)) := by
  obtain ⟨k, rfl⟩ := Int.le.dest hnm
  have hϖK : algebraMap R K ϖ ≠ 0 := algebraMap_ne_zero_of_ne_zero' hϖ.ne_zero
  set r : R := (u : R) + ϖ ^ k * w with hr_def
  have hsum : algebraMap R K ϖ ^ n * algebraMap R K (u : R) +
      algebraMap R K ϖ ^ (n + (k : ℤ)) * algebraMap R K (w : R) =
      algebraMap R K ϖ ^ n * algebraMap R K r := by
    rw [zpow_add₀ hϖK, zpow_natCast, hr_def, map_add, map_mul, map_pow]
    ring
  rw [hsum]
  by_cases hr : r = 0
  · rw [hr, map_zero, mul_zero, dvrValFun_zero]
    exact le_top
  · obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hrep : algebraMap R K ϖ ^ n * algebraMap R K r =
        algebraMap R K ϖ ^ (n + (j : ℤ)) * algebraMap R K (v : R) := by
      rw [hv, map_mul, map_pow, zpow_add₀ hϖK, zpow_natCast]
      ring
    rw [dvrValFun_eq hϖ hrep]
    exact_mod_cast (le_add_of_nonneg_right (Int.natCast_nonneg j))

/-- **The valuation of a DVR on its fraction field** (tex 2747–2748, 4830, 4916–4918, 5698–5700;
`PROVED`). For a DVR `R` with uniformizer `ϖ` and fraction field `K`, `dvrAddVal hϖ` is the additive
valuation `K → ℤ ∪ {⊤}` sending `ϖⁿ u` (`u ∈ Rˣ`) to `n` and `0` to `⊤`. -/
noncomputable def dvrAddVal (hϖ : Irreducible ϖ) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (dvrValFun hϖ) (dvrValFun_zero hϖ)
    (by
      have h1 : (1 : K) = algebraMap R K ϖ ^ (0 : ℤ) * algebraMap R K ((1 : Rˣ) : R) := by simp
      rw [dvrValFun_eq hϖ h1]
      rfl)
    (by
      intro x y
      by_cases hx : x = 0
      · rw [hx, zero_add, dvrValFun_zero]
        exact min_le_right _ _
      by_cases hy : y = 0
      · rw [hy, add_zero, dvrValFun_zero]
        exact min_le_left _ _
      obtain ⟨n, u, rfl⟩ := exists_zpow_mul_unit hϖ hx
      obtain ⟨m, w, rfl⟩ := exists_zpow_mul_unit hϖ hy
      rw [dvrValFun_eq hϖ rfl, dvrValFun_eq hϖ rfl]
      rcases le_total n m with hnm | hmn
      · rw [min_eq_left (by exact_mod_cast hnm)]
        exact le_dvrValFun_add hϖ hnm u w
      · rw [min_eq_right (by exact_mod_cast hmn), add_comm]
        exact le_dvrValFun_add hϖ hmn w u)
    (by
      intro x y
      by_cases hx : x = 0
      · rw [hx, zero_mul, dvrValFun_zero, top_add]
      by_cases hy : y = 0
      · rw [hy, mul_zero, dvrValFun_zero, add_top]
      obtain ⟨n, u, rfl⟩ := exists_zpow_mul_unit hϖ hx
      obtain ⟨m, w, rfl⟩ := exists_zpow_mul_unit hϖ hy
      have hϖK : algebraMap R K ϖ ≠ 0 := algebraMap_ne_zero_of_ne_zero' hϖ.ne_zero
      have hprod : algebraMap R K ϖ ^ n * algebraMap R K (u : R) *
          (algebraMap R K ϖ ^ m * algebraMap R K (w : R)) =
          algebraMap R K ϖ ^ (n + m) * algebraMap R K ((u * w : Rˣ) : R) := by
        rw [zpow_add₀ hϖK, Units.val_mul, map_mul]
        ring
      rw [hprod, dvrValFun_eq hϖ rfl, dvrValFun_eq hϖ rfl, dvrValFun_eq hϖ rfl, WithTop.coe_add])

theorem dvrAddVal_apply (hϖ : Irreducible ϖ) (x : K) : dvrAddVal hϖ x = dvrValFun hϖ x := rfl

/-- **Tex 2747–2748, 4916–4918 (PROVED).** `v(ϖⁿ u) = n` for `n ∈ ℤ`, `u ∈ Rˣ`. -/
theorem dvrAddVal_zpow_mul_unit (hϖ : Irreducible ϖ) (n : ℤ) (u : Rˣ) :
    dvrAddVal hϖ (algebraMap R K ϖ ^ n * algebraMap R K (u : R)) = n :=
  dvrValFun_eq hϖ rfl

/-- **Tex 2747–2748, 4916–4918 (PROVED).** `v(x) = n` whenever `x = ϖⁿ u`, `u ∈ Rˣ`. -/
theorem dvrAddVal_eq_of_eq (hϖ : Irreducible ϖ) {x : K} {n : ℤ} {u : Rˣ}
    (h : x = algebraMap R K ϖ ^ n * algebraMap R K (u : R)) : dvrAddVal hϖ x = n :=
  dvrValFun_eq hϖ h

/-- **Tex 4729 "uniformizer two" (PROVED).** The uniformizer has valuation one. -/
theorem dvrAddVal_uniformizer (hϖ : Irreducible ϖ) : dvrAddVal hϖ (algebraMap R K ϖ) = 1 := by
  have h : algebraMap R K ϖ = algebraMap R K ϖ ^ (1 : ℤ) * algebraMap R K ((1 : Rˣ) : R) := by
    simp
  rw [dvrAddVal_eq_of_eq hϖ h]
  rfl

/-- **Tex 2747–2748 (PROVED).** Units of `R` have valuation zero. -/
theorem dvrAddVal_unit (hϖ : Irreducible ϖ) (u : Rˣ) : dvrAddVal hϖ (algebraMap R K (u : R)) = 0 := by
  have h : algebraMap R K (u : R) = algebraMap R K ϖ ^ (0 : ℤ) * algebraMap R K (u : R) := by simp
  rw [dvrAddVal_eq_of_eq hϖ h]
  rfl

/-- **Tex 2747–2748 (PROVED).** `v(ϖⁿ u) = n` for `n ∈ ℕ`, computed on `R`. -/
theorem dvrAddVal_algebraMap_pow_mul_unit (hϖ : Irreducible ϖ) (n : ℕ) (u : Rˣ) :
    dvrAddVal hϖ (algebraMap R K (ϖ ^ n * u)) = (n : ℤ) := by
  apply dvrAddVal_eq_of_eq hϖ
  rw [map_mul, map_pow, zpow_natCast]

/-- **Tex 2747–2748 (PROVED).** `v(x) = ⊤` iff `x = 0`. -/
theorem dvrAddVal_eq_top_iff (hϖ : Irreducible ϖ) {x : K} : dvrAddVal hϖ x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨n, u, rfl⟩ := exists_zpow_mul_unit hϖ hx
    rw [dvrAddVal_zpow_mul_unit] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    exact (dvrAddVal hϖ).map_zero

/-- **Tex 4916–4918, 5698–5700, 7604–7609 (PROVED).** `0 ≤ v(x)` iff `x` lies in (the image of) `R`. -/
theorem dvrAddVal_nonneg_iff (hϖ : Irreducible ϖ) {x : K} :
    0 ≤ dvrAddVal hϖ x ↔ x ∈ (algebraMap R K).range := by
  constructor
  · intro h
    by_cases hx : x = 0
    · rw [hx]
      exact (algebraMap R K).range.zero_mem
    obtain ⟨n, u, rfl⟩ := exists_zpow_mul_unit hϖ hx
    rw [dvrAddVal_zpow_mul_unit] at h
    have hn : (0 : ℤ) ≤ n := by exact_mod_cast h
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact ⟨ϖ ^ k * u, by rw [map_mul, map_pow, zpow_natCast]⟩
  · rintro ⟨r, rfl⟩
    by_cases hr : r = 0
    · rw [hr, map_zero, (dvrAddVal hϖ).map_zero]
      exact le_top
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    rw [mul_comm, dvrAddVal_algebraMap_pow_mul_unit]
    exact_mod_cast Int.natCast_nonneg n

/-- **Tex 2747–2748, 5698–5700 (PROVED).** Divisibility by powers of the uniformizer is read off the
valuation: `ϖᵏ ∣ r ↔ k ≤ v(r)`. -/
theorem pow_dvd_iff_le_dvrAddVal (hϖ : Irreducible ϖ) (k : ℕ) (r : R) :
    ϖ ^ k ∣ r ↔ ((k : ℤ) : WithTop ℤ) ≤ dvrAddVal hϖ (algebraMap R K r) := by
  by_cases hr : r = 0
  · rw [hr, map_zero, (dvrAddVal hϖ).map_zero]
    exact iff_of_true (dvd_zero _) le_top
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [mul_comm, dvrAddVal_algebraMap_pow_mul_unit, WithTop.coe_le_coe, Nat.cast_le,
    Units.dvd_mul_right, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]

/-- **Tex 2747–2748 (PROVED).** `0 < v(x)` iff `x` lies in (the image of) the maximal ideal of `R`. -/
theorem dvrAddVal_pos_iff (hϖ : Irreducible ϖ) {x : K} :
    0 < dvrAddVal hϖ x ↔ ∃ r ∈ IsLocalRing.maximalIdeal R, x = algebraMap R K r := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := (dvrAddVal_nonneg_iff hϖ).mp h.le
    refine ⟨r, ?_, rfl⟩
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    rw [← pow_one ϖ, pow_dvd_iff_le_dvrAddVal (K := K) hϖ 1 r]
    have h1 : ((0 : ℤ) : WithTop ℤ) < dvrAddVal hϖ (algebraMap R K r) := h
    induction hv : dvrAddVal hϖ (algebraMap R K r) using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [hv] at h1
      have : (0 : ℤ) < m := by exact_mod_cast h1
      exact_mod_cast (show ((1 : ℕ) : ℤ) ≤ m by omega)
  · rintro ⟨r, hr, rfl⟩
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    have h1 := (pow_dvd_iff_le_dvrAddVal (K := K) hϖ 1 r).mp (by rwa [pow_one])
    exact lt_of_lt_of_le (by exact_mod_cast (show (0 : ℤ) < ((1 : ℕ) : ℤ) by norm_num)) h1

section Map

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] {ϖ' : S}

/-- **Tex 2747–2748, 3728–3730, 4916–4918 (PROVED).** Compatibility of the valuations along a ring map
of DVRs `f : R → S` sending the uniformizer to the uniformizer (unramified), with an extension
`φ : K → L` of the fraction fields: `v_S (φ x) = v_R x`. Applied to `Λ_{(2)} → 𝒪`, `2 ↦ 2`, it
identifies the valuation of `𝒪` on `Frac Λ` with that of `Λ_{(2)}`. -/
theorem dvrAddVal_map (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (f : R →+* S) (hf : f ϖ = ϖ')
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) (x : K) :
    dvrAddVal hϖ' (φ x) = dvrAddVal hϖ x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, (dvrAddVal hϖ').map_zero, (dvrAddVal hϖ).map_zero]
  obtain ⟨n, u, rfl⟩ := exists_zpow_mul_unit hϖ hx
  rw [dvrAddVal_zpow_mul_unit]
  apply dvrAddVal_eq_of_eq hϖ' (u := Units.map f.toMonoidHom u)
  rw [map_mul, map_zpow₀, hφ, hφ, hf]
  rfl

/-- **Tex 2747–2748, 3728–3730, 4916–4918 (PROVED).** The same compatibility as an equality of
valuations: `v_S ∘ φ = v_R`. -/
theorem dvrAddVal_comap (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (f : R →+* S) (hf : f ϖ = ϖ')
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) :
    (dvrAddVal hϖ').comap φ = dvrAddVal hϖ := by
  ext x
  exact dvrAddVal_map hϖ hϖ' f hf φ hφ x

end Map

end DVRValuation

end ZInQ.Manuscript.RC.Rings

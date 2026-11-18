import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Lane RC18-twist: twists at ramified primes

If `E` has good reduction at `p` and `p ∣ D` for a fundamental discriminant `D`, the twist
`E^{(D)}` has additive reduction at `p`, so its local polynomial is `1` (and `χ_D(p) = 0`):

* not multiplicative: `j(E^{(D)}) = j(E)` is integral (`not_hasMultiplicativeReduction_of_twist`);
* not good, when `D` is not a unit times a square (odd `p`, or `8 ∣ D`): a minimal model with unit
  discriminant would give `v(D⁶) = v(u¹²)` (`not_hasGoodReduction_of_twist`);
* not good at `p = 2` when `D = 4m`, `m ≡ 3 (mod 4)`: Kraus's congruences for integral models with
  unit discriminant (`c₆ ≡ −1 (mod 4)` if `c₄` is odd, `c₆ ≡ 8 (mod 32)` if `c₄` is even) are not
  preserved by `c₆ ↦ u⁻⁶ m³ c₆` (`not_hasGoodReduction_twist_two`).
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

/-- In `ℤᵐ⁰`, `x ^ n = 1` with `n ≠ 0` forces `x = 1`. -/
theorem eq_one_of_pow_eq_one_withZero {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h (pow_lt_one₀ zero_le hx hn).ne
  · exact hx
  · exact absurd h (one_lt_pow₀ hx hn).ne'

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

/-- An element of `R` has valuation `1` exactly when it is a unit. -/
theorem vK_algebraMap_eq_one_iff (r : R) : vK (algebraMap R K r) = 1 ↔ IsUnit r := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal

/-- An element of `K` of valuation `1` is the image of a unit of `R`. -/
theorem exists_isUnit_of_vK_eq_one {x : K} (hx : vK x = 1) :
    ∃ w : R, IsUnit w ∧ algebraMap R K w = x := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx.le
  refine ⟨w, ?_, hw⟩
  rw [← vK_algebraMap_eq_one_iff (K := K), hw, hx]

/-- **A twist of a curve with good reduction has no multiplicative reduction** (PROVED): the
`j`-invariant `c₄³/Δ` of the twist equals that of `M`, which is integral. -/
theorem not_hasMultiplicativeReduction_of_twist (h2 : (2 : K) ≠ 0) (M : WeierstrassCurve K)
    [M.HasGoodReduction R] {d : K} (_hd : d ≠ 0) (W : WeierstrassCurve K) (C : VariableChange K)
    (hW : W = C • twistK M d) [IsMinimal R W] : ¬ W.HasMultiplicativeReduction R := by
  intro hmult
  have hMΔ : vK M.Δ = 1 := ‹M.HasGoodReduction R›.goodReduction
  have hMc : vK M.c₄ ≤ 1 := by
    rw [← integralModel_c₄_eq R M]; exact valuation_le_one _ _
  have hc : vK W.c₄ = 1 := hmult.multiplicativeReduction
  have hΔ : vK W.Δ < 1 := hmult.badReduction
  have hj : W.c₄ ^ 3 * M.Δ = M.c₄ ^ 3 * W.Δ := by
    rw [hW, variableChange_c₄, variableChange_Δ, twistK_c₄ M h2, twistK_Δ M h2]; ring
  have hj' := congrArg vK hj
  simp only [map_mul, map_pow, hc, hMΔ, one_pow, one_mul] at hj'
  have hlt : vK M.c₄ ^ 3 * vK W.Δ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hMc)) hΔ
  exact hlt.ne hj'.symm

/-- **A twist by a non-(unit × square) of a curve with good reduction has no good reduction**
(PROVED). -/
theorem not_hasGoodReduction_of_twist (h2 : (2 : K) ≠ 0) (M : WeierstrassCurve K)
    [M.HasGoodReduction R] {d : K} (_hd : d ≠ 0)
    (hsq : ∀ (x : K) (w : R), IsUnit w → d ≠ x ^ 2 * algebraMap R K w)
    (W : WeierstrassCurve K) (C : VariableChange K) (hW : W = C • twistK M d) [IsMinimal R W] :
    ¬ W.HasGoodReduction R := by
  intro hgood
  have hMΔ : vK M.Δ = 1 := ‹M.HasGoodReduction R›.goodReduction
  have hWΔ : vK W.Δ = 1 := hgood.goodReduction
  have hu : ((C.u⁻¹ : Kˣ) : K) * (C.u : K) = 1 := by simp
  have hrel : W.Δ = (((C.u⁻¹ : Kˣ) : K) ^ 2 * d) ^ 6 * M.Δ := by
    rw [hW, variableChange_Δ, twistK_Δ M h2]; ring
  have h6 : vK (((C.u⁻¹ : Kˣ) : K) ^ 2 * d) ^ 6 = 1 := by
    have := congrArg vK hrel
    rw [hWΔ, map_mul, map_pow, hMΔ, mul_one] at this
    exact this.symm
  obtain ⟨w, hw, hwx⟩ := exists_isUnit_of_vK_eq_one (eq_one_of_pow_eq_one_withZero (by norm_num) h6)
  apply hsq (C.u : K) w hw
  rw [hwx]
  linear_combination (-d * (((C.u⁻¹ : Kˣ) : K) * (C.u : K) + 1)) * hu

end Generic

section TwoAdic

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "vK" => valuation (v.adicCompletion ℚ)
  (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers ℚ))

/-- `2 ≠ 0` in `ℚ_v` (PROVED). -/
theorem two_ne_zero_adicCompletion : (2 : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 2]
  exact (map_ne_zero _).mpr two_ne_zero

/-- A nonzero integer is nonzero in `ℚ_v` (PROVED). -/
theorem intCast_ne_zero_adicCompletion {n : ℤ} (hn : n ≠ 0) : (n : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) n]
  exact (map_ne_zero _).mpr (Int.cast_ne_zero.mpr hn)

variable {v}

/-- At `v ∣ 2`, a non-unit of `𝒪_v` is divisible by `2` (PROVED). -/
theorem two_dvd_of_not_isUnit (hv : natGenerator v = 2) {x : v.adicCompletionIntegers ℚ}
    (hx : ¬ IsUnit x) : ∃ y, x = 2 * y := by
  have hm : x ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal x).mpr hx
  rw [ZInQ.Literature.maximalIdeal_eq_span, hv, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨y, by simpa using hy⟩

/-- At `v ∣ 2`, `2` is not a unit of `𝒪_v` (PROVED). -/
theorem not_isUnit_two (hv : natGenerator v = 2) : ¬ IsUnit (2 : v.adicCompletionIntegers ℚ) := by
  have := (ZInQ.Literature.irreducible_natGenerator v).not_isUnit
  rwa [hv, Nat.cast_ofNat] at this

/-- At `v ∣ 2`, `2x` is not a unit of `𝒪_v` (PROVED). -/
theorem not_isUnit_two_mul (hv : natGenerator v = 2) (y : v.adicCompletionIntegers ℚ) :
    ¬ IsUnit (2 * y) := fun h => not_isUnit_two hv (isUnit_of_mul_isUnit_left h)

/-- At `v ∣ 2`, `1 + 2x` is a unit of `𝒪_v` (PROVED). -/
theorem isUnit_one_add_two_mul (hv : natGenerator v = 2) (y : v.adicCompletionIntegers ℚ) :
    IsUnit (1 + 2 * y) := by
  by_contra h
  obtain ⟨z, hz⟩ := two_dvd_of_not_isUnit hv h
  exact not_isUnit_two hv (IsUnit.of_mul_eq_one (z - y) (by linear_combination -hz))

/-- The residue field of `𝒪_v` is `𝔽₂`: a unit is `1 + 2y`. -/
theorem exists_eq_one_add_two_mul (hv : natGenerator v = 2) {x : v.adicCompletionIntegers ℚ}
    (hx : IsUnit x) : ∃ y, x = 1 + 2 * y := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range (ZInQ.Literature.ePadic v x)
  have hn' : n < 2 := by
    have : ((primesEquiv v : Nat.Primes) : ℕ) = natGenerator v := rfl
    rw [this, hv] at hn; exact hn
  interval_cases n
  · exfalso
    have h1 := (IsLocalRing.mem_maximalIdeal _).mp hmem
    rw [mem_nonunits_iff] at h1
    apply h1
    simpa using (isUnit_map_iff (ZInQ.Literature.ePadic v) x).mpr hx
  · have h1 := (IsLocalRing.mem_maximalIdeal _).mp hmem
    rw [mem_nonunits_iff] at h1
    have h2 : ¬ IsUnit (x - 1) := by
      rw [← isUnit_map_iff (ZInQ.Literature.ePadic v), map_sub, map_one]
      simpa using h1
    obtain ⟨y, hy⟩ := two_dvd_of_not_isUnit hv h2
    exact ⟨y, by linear_combination hy⟩

/-- **Kraus at `2`, odd `c₄`**: an integral model over `𝒪_v` (`v ∣ 2`) with `c₄` a unit has
`c₆ ≡ −1 (mod 4)`. -/
theorem kraus_c₆_of_isUnit (hv : natGenerator v = 2) (V : WeierstrassCurve (v.adicCompletionIntegers ℚ))
    (hc : IsUnit V.c₄) : ∃ P, V.c₆ = -1 + 4 * P := by
  have ha : IsUnit V.a₁ := by
    by_contra h
    obtain ⟨α, hα⟩ := two_dvd_of_not_isUnit hv h
    apply not_isUnit_two_mul hv (8 * (α ^ 2 + V.a₂) ^ 2 - 12 * V.b₄)
    have hb2 : V.b₂ = 4 * (α ^ 2 + V.a₂) := by rw [b₂, hα]; ring
    convert hc using 1
    rw [c₄, hb2]; ring
  obtain ⟨t, ht⟩ := exists_eq_one_add_two_mul hv ha
  have hb2 : V.b₂ = 1 + 4 * (t + t ^ 2 + V.a₂) := by rw [b₂, ht]; ring
  refine ⟨-3 * (t + t ^ 2 + V.a₂) - 12 * (t + t ^ 2 + V.a₂) ^ 2 - 16 * (t + t ^ 2 + V.a₂) ^ 3 +
    9 * V.b₂ * V.b₄ - 54 * V.b₆, ?_⟩
  rw [c₆, hb2]; ring

/-- **Kraus at `2`, even `c₄`**: an integral model over `𝒪_v` (`v ∣ 2`) with unit discriminant and
`c₄` not a unit has `c₆ ≡ 8 (mod 32)`. -/
theorem kraus_c₆_of_not_isUnit (hv : natGenerator v = 2)
    (V : WeierstrassCurve (v.adicCompletionIntegers ℚ)) (hΔ : IsUnit V.Δ) (hc : ¬ IsUnit V.c₄) :
    ∃ P, V.c₆ = 8 + 32 * P := by
  have ha1 : ¬ IsUnit V.a₁ := by
    intro ha
    obtain ⟨t, ht⟩ := exists_eq_one_add_two_mul hv ha
    have hb2 : V.b₂ = 1 + 4 * (t + t ^ 2 + V.a₂) := by rw [b₂, ht]; ring
    apply hc
    have : V.c₄ = 1 + 2 * (4 * (t + t ^ 2 + V.a₂) + 8 * (t + t ^ 2 + V.a₂) ^ 2 - 12 * V.b₄) := by
      rw [c₄, hb2]; ring
    rw [this]; exact isUnit_one_add_two_mul hv _
  obtain ⟨α, hα⟩ := two_dvd_of_not_isUnit hv ha1
  have hb2 : V.b₂ = 4 * (α ^ 2 + V.a₂) := by rw [b₂, hα]; ring
  have ha3 : IsUnit V.a₃ := by
    by_contra h
    obtain ⟨δ, hδ⟩ := two_dvd_of_not_isUnit hv h
    have hb6 : V.b₆ = 4 * (δ ^ 2 + V.a₆) := by rw [b₆, hδ]; ring
    apply not_isUnit_two_mul hv (-8 * (α ^ 2 + V.a₂) ^ 2 * V.b₈ - 4 * V.b₄ ^ 3 -
      216 * (δ ^ 2 + V.a₆) ^ 2 + 72 * (α ^ 2 + V.a₂) * V.b₄ * (δ ^ 2 + V.a₆))
    convert hΔ using 1
    rw [Δ, hb2, hb6]; ring
  obtain ⟨t, ht⟩ := exists_eq_one_add_two_mul hv ha3
  have hb4 : V.b₄ = 2 * (α * V.a₃ + V.a₄) := by rw [b₄, hα]; ring
  have hb6 : V.b₆ = (1 + 2 * t) ^ 2 + 4 * V.a₆ := by rw [b₆, ht]
  refine ⟨-2 * (α ^ 2 + V.a₂) ^ 3 + 9 * (α ^ 2 + V.a₂) * (α * V.a₃ + V.a₄) - 7 - 27 * t -
    27 * t ^ 2 - 27 * V.a₆, ?_⟩
  rw [c₆, hb2, hb4, hb6]; ring

variable (v)

/-- **Kraus at `2`** (PROVED): if `M` has good reduction at `v ∣ 2` and `m ≡ 3 (mod 4)`, no model
of the twist `M^{(m)}` has good reduction. -/
theorem not_hasGoodReduction_twist_two (hv : natGenerator v = 2)
    (M : WeierstrassCurve (v.adicCompletion ℚ)) [M.HasGoodReduction (v.adicCompletionIntegers ℚ)]
    {m : ℤ} (hm : m % 4 = 3) (W : WeierstrassCurve (v.adicCompletion ℚ))
    (C : VariableChange (v.adicCompletion ℚ)) (hW : W = C • twistK M (m : v.adicCompletion ℚ))
    [IsMinimal (v.adicCompletionIntegers ℚ) W] :
    ¬ W.HasGoodReduction (v.adicCompletionIntegers ℚ) := by
  intro hgood
  have h2 := two_ne_zero_adicCompletion v
  have hMΔ : vK M.Δ = 1 := ‹M.HasGoodReduction _›.goodReduction
  have hWΔ : vK W.Δ = 1 := hgood.goodReduction
  have hmu : IsUnit (m : v.adicCompletionIntegers ℚ) :=
    (ZInQ.Literature.isUnit_intCast_iff v m).mpr (by rw [hv]; push_cast; omega)
  have hvm : vK (m : v.adicCompletion ℚ) = 1 := by
    rw [← map_intCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)),
      vK_algebraMap_eq_one_iff]
    exact hmu
  have hrelΔ : W.Δ = ((C.u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ 12 *
      ((m : v.adicCompletion ℚ) ^ 6 * M.Δ) := by
    rw [hW, variableChange_Δ, twistK_Δ M h2]
  have hvu : vK ((C.u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    have := congrArg vK hrelΔ
    rw [hWΔ, map_mul, map_mul, map_pow, map_pow, hvm, hMΔ, one_pow, one_mul, mul_one] at this
    exact eq_one_of_pow_eq_one_withZero (by norm_num) this.symm
  obtain ⟨w, hwu, hw⟩ := exists_isUnit_of_vK_eq_one hvu
  have hinj := IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
  set A := integralModel (v.adicCompletionIntegers ℚ) M with hA
  set B := integralModel (v.adicCompletionIntegers ℚ) W with hB
  have hc4 : B.c₄ = w ^ 4 * ((m : v.adicCompletionIntegers ℚ) ^ 2 * A.c₄) := by
    apply hinj
    rw [integralModel_c₄_eq, map_mul, map_pow, map_mul, map_pow, map_intCast,
      integralModel_c₄_eq, hw, hW, variableChange_c₄, twistK_c₄ M h2]
  have hc6 : B.c₆ = w ^ 6 * ((m : v.adicCompletionIntegers ℚ) ^ 3 * A.c₆) := by
    apply hinj
    rw [integralModel_c₆_eq, map_mul, map_pow, map_mul, map_pow, map_intCast,
      integralModel_c₆_eq, hw, hW, variableChange_c₆, twistK_c₆ M h2]
  have hAΔ : IsUnit A.Δ := by
    rw [← vK_algebraMap_eq_one_iff (K := v.adicCompletion ℚ), integralModel_Δ_eq]; exact hMΔ
  have hBΔ : IsUnit B.Δ := by
    rw [← vK_algebraMap_eq_one_iff (K := v.adicCompletion ℚ), integralModel_Δ_eq]; exact hWΔ
  obtain ⟨z, hz⟩ := exists_eq_one_add_two_mul hv (hwu.pow 3)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 3 + 4 * k := ⟨m / 4, by omega⟩
  have hmR : (m : v.adicCompletionIntegers ℚ) = 3 + 4 * (k : v.adicCompletionIntegers ℚ) := by
    rw [hk]; push_cast; ring
  have hw6 : w ^ 6 = (1 + 2 * z) ^ 2 := by rw [← hz]; ring
  have h2R : (2 : v.adicCompletionIntegers ℚ) ≠ 0 := fun h => h2 (by
    simpa using congrArg (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) h)
  apply not_isUnit_two hv
  by_cases hcA : IsUnit A.c₄
  · have hcB : IsUnit B.c₄ := by rw [hc4]; exact (hwu.pow 4).mul ((hmu.pow 2).mul hcA)
    obtain ⟨P, hP⟩ := kraus_c₆_of_isUnit hv A hcA
    obtain ⟨Q, hQ⟩ := kraus_c₆_of_isUnit hv B hcB
    rw [hP, hQ, hmR, hw6] at hc6
    set N := 6 + 27 * k + 36 * k ^ 2 + 16 * k ^ 3
    set Z := z + z ^ 2
    set E := (N : v.adicCompletionIntegers ℚ) + 3 * Z + 4 * Z * N
    refine IsUnit.of_mul_eq_one (3 * P - E + 4 * E * P - Q) (mul_left_cancel₀ h2R ?_)
    simp only [N, Z, E]; push_cast
    linear_combination -hc6
  · have hcB : ¬ IsUnit B.c₄ := by
      rw [hc4]; intro h
      exact hcA (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h))
    obtain ⟨P, hP⟩ := kraus_c₆_of_not_isUnit hv A hAΔ hcA
    obtain ⟨Q, hQ⟩ := kraus_c₆_of_not_isUnit hv B hBΔ hcB
    rw [hP, hQ, hmR, hw6] at hc6
    set N := 6 + 27 * k + 36 * k ^ 2 + 16 * k ^ 3
    set Z := z + z ^ 2
    set E := (N : v.adicCompletionIntegers ℚ) + 3 * Z + 4 * Z * N
    have h16 : (16 : v.adicCompletionIntegers ℚ) ≠ 0 := by
      have h : (16 : v.adicCompletionIntegers ℚ) = 2 ^ 4 := by norm_num
      rw [h]; exact pow_ne_zero 4 h2R
    refine IsUnit.of_mul_eq_one (Q - 3 * P - E - 4 * E * P) (mul_left_cancel₀ h16 ?_)
    simp only [N, Z, E]; push_cast
    linear_combination hc6

/-- The cases of a fundamental discriminant `D` divisible by a prime `p`: either `p` divides `D` to
an odd power, or `p = 2` and `D = 4m` with `m ≡ 3 (mod 4)`. -/
theorem fundamental_cases {p : ℕ} (hp : p.Prime) {D : ℤ}
    (hD : ZInQ.Manuscript.RC.PrintsAnalytic.IsFundamentalDiscriminant D) (hpD : (p : ℤ) ∣ D) :
    (∃ (k : ℕ) (e : ℤ), Odd k ∧ D = (p : ℤ) ^ k * e ∧ ¬ (p : ℤ) ∣ e) ∨
      (p = 2 ∧ ∃ m : ℤ, D = 4 * m ∧ m % 4 = 3) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot4 : p ≠ 2 → ¬ (p : ℤ) ∣ 4 := by
    intro hp2 h
    have h' : p ∣ 2 ^ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
  obtain ⟨-, ⟨hD4, hsqD⟩ | ⟨m, rfl, hm4, hsqm⟩⟩ := hD
  · obtain ⟨e, rfl⟩ := hpD
    left
    refine ⟨1, e, odd_one, by ring, fun he => ?_⟩
    obtain ⟨f, rfl⟩ := he
    exact hpz.not_isUnit (hsqD (p : ℤ) ⟨f, by ring⟩)
  · by_cases hp2 : p = 2
    · subst hp2
      rcases hm4 with hm4 | hm4
      · left
        refine ⟨3, m / 2, ⟨1, rfl⟩, ?_, ?_⟩
        · push_cast; omega
        · push_cast; omega
      · right; exact ⟨rfl, m, rfl, hm4⟩
    · left
      have hpm : (p : ℤ) ∣ m := by
        rcases hpz.dvd_or_dvd hpD with h | h
        · exact absurd h (hnot4 hp2)
        · exact h
      obtain ⟨e, rfl⟩ := hpm
      refine ⟨1, 4 * e, odd_one, by ring, fun he => ?_⟩
      rcases hpz.dvd_or_dvd he with h | h
      · exact hnot4 hp2 h
      · obtain ⟨f, rfl⟩ := h
        exact hpz.not_isUnit (hsqm (p : ℤ) ⟨f, by ring⟩)

variable {v} in
/-- If `p` divides `D` to an odd power, `D` is not a unit times a square in `ℚ_v`. -/
theorem ne_sq_mul_unit_of_odd_pow {D : ℤ} {k : ℕ} (hk : Odd k) {e : ℤ}
    (hDe : D = (natGenerator v : ℤ) ^ k * e) (he : ¬ (natGenerator v : ℤ) ∣ e) :
    ∀ (x : v.adicCompletion ℚ) (w : v.adicCompletionIntegers ℚ), IsUnit w →
      (D : v.adicCompletion ℚ) ≠ x ^ 2 * algebraMap _ (v.adicCompletion ℚ) w := by
  intro x w hw hx
  have heu : IsUnit (e : v.adicCompletionIntegers ℚ) :=
    (ZInQ.Literature.isUnit_intCast_iff v e).mpr he
  have hπ := ZInQ.Literature.irreducible_natGenerator v
  set π : v.adicCompletionIntegers ℚ := ((natGenerator v : ℕ) : v.adicCompletionIntegers ℚ)
  have hDR : (D : v.adicCompletion ℚ) =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (π ^ k * e) := by
    rw [hDe, map_mul, map_pow, map_intCast, map_natCast]; push_cast; rfl
  have hwv : vK (algebraMap _ (v.adicCompletion ℚ) w) = 1 := (vK_algebraMap_eq_one_iff w).mpr hw
  have hxle : vK x ≤ 1 := by
    refine le_of_not_gt fun hlt => ?_
    have h1 : vK (D : v.adicCompletion ℚ) ≤ 1 := by rw [hDR]; exact valuation_le_one _ _
    rw [hx, map_mul, map_pow, hwv, mul_one] at h1
    exact absurd h1 (not_le.mpr (one_lt_pow₀ hlt two_ne_zero))
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hxle
  have hy : π ^ k * e = y ^ 2 * w := by
    apply IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
    rw [← hDR, hx, map_mul, map_pow]
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul] at hy
    exact (mul_ne_zero (pow_ne_zero k hπ.ne_zero) heu.ne_zero) hy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have hkn := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ heu.unit (u ^ 2 * hw.unit) k
    (2 * n) (by
      simp only [IsUnit.unit_spec, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [mul_comm, hy, hu]; ring)
  obtain ⟨j, hj⟩ := hk
  omega

/-- **The local polynomial of a twist at a ramified prime** (PROVED): if `D` is a fundamental
discriminant, `p = natGenerator v` divides `D`, and `E` has good reduction at `v`, then the twist
`E^{(D)}` has additive reduction at `v` and its local polynomial is `1`. -/
theorem localPolynomial_qtwist_of_dvd (E : WeierstrassCurve ℚ) [E.IsElliptic] {D : ℤ}
    (hD : ZInQ.Manuscript.RC.PrintsAnalytic.IsFundamentalDiscriminant D)
    (hpD : (natGenerator v : ℤ) ∣ D)
    (hgood : ((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    ((ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = 1 := by
  have h2 := two_ne_zero_adicCompletion v
  have hD0 : D ≠ 0 := by
    obtain ⟨-, ⟨hD4, -⟩ | ⟨m, rfl, hm4, -⟩⟩ := hD <;> omega
  have hDK := intCast_ne_zero_adicCompletion v hD0
  set EK := E.baseChange (v.adicCompletion ℚ) with hEK
  set M := EK.minimal (v.adicCompletionIntegers ℚ) with hMdef
  have : M.HasGoodReduction (v.adicCompletionIntegers ℚ) := hgood
  set C₀ := (EK.exists_isMinimal (v.adicCompletionIntegers ℚ)).choose with hC₀
  have hM : M = C₀ • EK := ZInQ.Literature.minimal_eq_smul EK
  set C₁ : VariableChange (v.adicCompletion ℚ) := ⟨C₀⁻¹.u, (D : v.adicCompletion ℚ) * C₀⁻¹.r, 0, 0⟩
    with hC₁
  have hT : (ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ) =
      C₁ • twistK M (D : v.adicCompletion ℚ) := by
    rw [qtwist_eq_twistK, hC₁, ← twistK_smul M h2, hM, inv_smul_smul]
    change (twistK E D).map (algebraMap ℚ (v.adicCompletion ℚ)) = _
    rw [twistK_map, map_intCast]
    rfl
  set T := (ZInQ.Contrib.CloudB3RC53.qtwist E D).baseChange (v.adicCompletion ℚ) with hTdef
  have hTmin : T.minimal (v.adicCompletionIntegers ℚ) =
      ((T.exists_isMinimal (v.adicCompletionIntegers ℚ)).choose * C₁) •
        twistK M (D : v.adicCompletion ℚ) := by
    rw [ZInQ.Literature.minimal_eq_smul, mul_smul, ← hT]
  set W := T.minimal (v.adicCompletionIntegers ℚ) with hWdef
  have hnm : ¬ W.HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
    not_hasMultiplicativeReduction_of_twist h2 M hDK W _ hTmin
  have hng : ¬ W.HasGoodReduction (v.adicCompletionIntegers ℚ) := by
    rcases fundamental_cases (prime_natGenerator v) hD hpD with ⟨k, e, hk, hDe, he⟩ |
      ⟨hp2, m, hDm, hm⟩
    · exact not_hasGoodReduction_of_twist h2 M hDK (ne_sq_mul_unit_of_odd_pow hk hDe he) W _ hTmin
    · have hDsq : (D : v.adicCompletion ℚ) = (m : v.adicCompletion ℚ) * 2 ^ 2 := by
        rw [hDm]; push_cast; ring
      rw [hDsq, twistK_mul_sq M h2 (m : v.adicCompletion ℚ) h2, smul_smul] at hTmin
      exact not_hasGoodReduction_twist_two v hp2 M hm W _ hTmin
  have hns : ¬ W.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
    fun h => hnm h.toHasMultiplicativeReduction
  unfold localPolynomial
  simp only [← hWdef, hng, hns, hnm, ↓reduceIte]

end TwoAdic

end ZInQ.Manuscript.RC.TwistDictionary

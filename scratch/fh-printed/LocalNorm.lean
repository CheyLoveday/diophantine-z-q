import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.FieldTheory.Finite.Basic

namespace ZInQ.FHPrinted

open PadicInt Polynomial

/-- `x` is a norm from `K(√d)`: `x = y² − d z²` with `y, z ∈ K`. -/
def IsLocalNorm (K : Type*) [Field K] (d : ℤ) (x : K) : Prop :=
  ∃ y z : K, x = y ^ 2 - d * z ^ 2

section General

variable {K : Type*} [Field K] {d : ℤ}

theorem IsLocalNorm.mul {x x' : K} (h : IsLocalNorm K d x) (h' : IsLocalNorm K d x') :
    IsLocalNorm K d (x * x') := by
  obtain ⟨y, z, rfl⟩ := h
  obtain ⟨y', z', rfl⟩ := h'
  exact ⟨y * y' + d * z * z', y * z' + y' * z, by ring⟩

theorem IsLocalNorm.sq_mul {x : K} (c : K) (h : IsLocalNorm K d x) :
    IsLocalNorm K d (c ^ 2 * x) := by
  obtain ⟨y, z, rfl⟩ := h
  exact ⟨c * y, c * z, by ring⟩

theorem isLocalNorm_sq (c : K) : IsLocalNorm K d (c ^ 2) := ⟨c, 0, by ring⟩

theorem isLocalNorm_neg_self : IsLocalNorm K d (-(d : K)) := ⟨0, 1, by ring⟩

theorem isLocalNorm_of_eq_sq (h2 : (2 : K) ≠ 0) {w : K} (hw0 : w ≠ 0) (hw : (d : K) = w ^ 2)
    (x : K) : IsLocalNorm K d x :=
  ⟨(x + 1) / 2, (x - 1) / (2 * w), by rw [hw]; field_simp; ring⟩

end General

section Hensel

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_maximalIdeal_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) :
    x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [← ker_toZMod]; exact h

theorem norm_lt_one_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) : ‖x‖ < 1 :=
  mem_nonunits.mp (mem_maximalIdeal_of_toZMod h)

theorem dvd_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) : (p : ℤ_[p]) ∣ x :=
  (norm_lt_one_iff_dvd x).mp (norm_lt_one_of_toZMod h)

theorem isUnit_of_toZMod {x : ℤ_[p]} (h : toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h (by rw [← RingHom.mem_ker, ker_toZMod]; exact hx)

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

/-- **Hensel**: a `p`-adic integer (`p` odd) that is a nonzero square modulo `p` is a square. -/
theorem isSquare_of_toZMod (hp2 : p ≠ 2) {u : ℤ_[p]} {c : ZMod p} (hc : c ≠ 0)
    (hu : toZMod u = c ^ 2) : IsSquare u := by
  set a : ℤ_[p] := ((c.val : ℕ) : ℤ_[p]) with ha_def
  have ha : toZMod a = c := by simp [a]
  let F : Polynomial ℤ_[p] := X ^ 2 - C u
  have hF : F.aeval a = a ^ 2 - u := by simp [F]
  have hF' : F.derivative.aeval a = 2 * a := by simp [F]; norm_num
  have h1 : ‖F.aeval a‖ < 1 := by
    rw [hF]; apply norm_lt_one_of_toZMod; simp [ha, hu]
  have h2 : ‖F.derivative.aeval a‖ = 1 := by
    rw [hF', ← PadicInt.isUnit_iff]; apply isUnit_of_toZMod
    rw [map_mul, ha, map_ofNat]
    exact mul_ne_zero (two_ne_zero_zmod hp2) hc
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  linear_combination -this

/-- **Hensel at `2`**: a `2`-adic integer `≡ 1 (mod 8)` is a square. -/
theorem isSquare_of_toZModPow_three {u : ℤ_[2]} (hu : toZModPow 3 u = 1) : IsSquare u := by
  let F : Polynomial ℤ_[2] := X ^ 2 - C u
  have h1 : ‖F.aeval (1 : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
    rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker]
    simp [F, hu]
  have hd : F.derivative.aeval (1 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by simp [F]; norm_num
  have h2 : ‖F.derivative.aeval (1 : ℤ_[2])‖ = ((2 : ℕ) : ℝ)⁻¹ := by
    rw [hd]; exact PadicInt.norm_p
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := 1) (by
    rw [h2]
    refine lt_of_le_of_lt h1 ?_
    norm_num)
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  linear_combination -this

/-- An integer prime to `p` (odd) that is a square modulo `p` is a nonzero square in `ℚ_p`. -/
theorem exists_sq_of_int (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hsq : IsSquare (a : ZMod p)) : ∃ w : ℚ_[p], w ≠ 0 ∧ (a : ℚ_[p]) = w ^ 2 := by
  obtain ⟨c, hc⟩ := hsq
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact ha0 hc
  obtain ⟨z, hz⟩ := isSquare_of_toZMod hp2 hc0 (u := (a : ℤ_[p])) (by rw [map_intCast, hc]; ring)
  have hz' : (a : ℚ_[p]) = (z : ℚ_[p]) ^ 2 := by
    rw [← PadicInt.coe_intCast, hz]; push_cast; ring
  refine ⟨z, fun h0 => ?_, hz'⟩
  rw [h0] at hz'
  have : (a : ℚ_[p]) = 0 := by simpa using hz'
  exact ha (by rw [Int.cast_eq_zero.mp this]; exact dvd_zero _)

/-- An integer `≡ 1 (mod 8)` is a nonzero square in `ℚ_2`. -/
theorem exists_sq_of_int_two {a : ℤ} (ha : a % 8 = 1) :
    ∃ w : ℚ_[2], w ≠ 0 ∧ (a : ℚ_[2]) = w ^ 2 := by
  have h8 : (a : ZMod (2 ^ 3)) = 1 := by
    have e : a = 8 * (a / 8) + 1 := by omega
    rw [e]; push_cast
    have : (8 : ZMod (2 ^ 3)) = 0 := by decide
    rw [this]; ring
  obtain ⟨z, hz⟩ := isSquare_of_toZModPow_three (u := (a : ℤ_[2])) (by rw [map_intCast, h8])
  have hz' : (a : ℚ_[2]) = (z : ℚ_[2]) ^ 2 := by
    rw [← PadicInt.coe_intCast, hz]; push_cast; ring
  refine ⟨z, fun h0 => ?_, hz'⟩
  rw [h0] at hz'
  have : (a : ℚ_[2]) = 0 := by simpa using hz'
  have := Int.cast_eq_zero.mp this
  omega

end Hensel


section Descent

variable {p : ℕ} [hp : Fact p.Prime]

theorem p_ne_zero_padicInt : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- **Descent for the norm form.** If `x ∈ ℤ_p` is not `Y² − d Z²` with `Y, Z ∈ ℤ_p`, and every
representation of `p^{2(k+1)} x` has `p ∣ Y`, `p ∣ Z`, then `x` is not a norm from `ℚ_p(√d)`. -/
theorem not_isLocalNorm_of_descent {d : ℤ} {x : ℤ_[p]}
    (h0 : ∀ Y Z : ℤ_[p], x ≠ Y ^ 2 - (d : ℤ_[p]) * Z ^ 2)
    (hstep : ∀ (k : ℕ) (Y Z : ℤ_[p]), (p : ℤ_[p]) ^ (2 * (k + 1)) * x = Y ^ 2 - (d : ℤ_[p]) * Z ^ 2 →
      (p : ℤ_[p]) ∣ Y ∧ (p : ℤ_[p]) ∣ Z) :
    ¬ IsLocalNorm ℚ_[p] d (x : ℚ_[p]) := by
  have key : ∀ k : ℕ, ∀ Y Z : ℤ_[p], (p : ℤ_[p]) ^ (2 * k) * x ≠ Y ^ 2 - (d : ℤ_[p]) * Z ^ 2 := by
    intro k
    induction k with
    | zero => intro Y Z; simpa using h0 Y Z
    | succ k ih =>
      intro Y Z hYZ
      obtain ⟨⟨Y', rfl⟩, ⟨Z', rfl⟩⟩ := hstep k Y Z hYZ
      apply ih Y' Z'
      have hp0 : (p : ℤ_[p]) ^ 2 ≠ 0 := pow_ne_zero 2 p_ne_zero_padicInt
      apply mul_left_cancel₀ hp0
      have e : (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) ^ (2 * k) * x) =
          (p : ℤ_[p]) ^ (2 * (k + 1)) * x := by ring
      rw [e, hYZ]; ring
  rintro ⟨y, z, hyz⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max ‖y‖ ‖z‖)
    (by exact_mod_cast hp.out.one_lt : (1 : ℝ) < p)
  have hle : ∀ w : ℚ_[p], ‖w‖ ≤ max ‖y‖ ‖z‖ → ‖(p : ℚ_[p]) ^ k * w‖ ≤ 1 := by
    intro w hw
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
    rw [inv_mul_le_iff₀ hpk, mul_one]; linarith
  apply key k ⟨(p : ℚ_[p]) ^ k * y, hle y (le_max_left _ _)⟩
    ⟨(p : ℚ_[p]) ^ k * z, hle z (le_max_right _ _)⟩
  apply PadicInt.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub,
    PadicInt.coe_intCast]
  change (p : ℚ_[p]) ^ (2 * k) * (x : ℚ_[p]) =
    ((p : ℚ_[p]) ^ k * y) ^ 2 - (d : ℚ_[p]) * ((p : ℚ_[p]) ^ k * z) ^ 2
  rw [hyz]; ring

/-- Modulo `p`: if `d` is not a square mod `p`, `Y² ≡ d Z²` forces `Y ≡ Z ≡ 0`. -/
theorem toZMod_eq_zero_of_nonsquare {d : ℤ} (hd : ¬ IsSquare (d : ZMod p)) {Y Z : ℤ_[p]}
    (h : toZMod (Y ^ 2 - (d : ℤ_[p]) * Z ^ 2) = 0) : toZMod Y = 0 ∧ toZMod Z = 0 := by
  simp only [map_sub, map_mul, map_pow, map_intCast] at h
  by_cases hZ : toZMod Z = 0
  · rw [hZ] at h
    refine ⟨?_, hZ⟩
    have : toZMod Y ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · exfalso; apply hd
    refine ⟨toZMod Y / toZMod Z, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hZ hZ)]
    linear_combination -h

theorem toZMod_p : toZMod (p : ℤ_[p]) = 0 := by simp

/-- **`p` is not a norm from the unramified quadratic extension**: if `d` is not a square
modulo `p`, then `p ∉ N(ℚ_p(√d)^×)`. -/
theorem not_isLocalNorm_p {d : ℤ} (hd : ¬ IsSquare (d : ZMod p)) :
    ¬ IsLocalNorm ℚ_[p] d (p : ℚ_[p]) := by
  rw [← PadicInt.coe_natCast]
  apply not_isLocalNorm_of_descent
  · intro Y Z h
    obtain ⟨hY, hZ⟩ := toZMod_eq_zero_of_nonsquare hd (Y := Y) (Z := Z) (by rw [← h]; simp)
    obtain ⟨Y', rfl⟩ := dvd_of_toZMod hY
    obtain ⟨Z', rfl⟩ := dvd_of_toZMod hZ
    have h1 : (p : ℤ_[p]) * 1 = p * (p * (Y' ^ 2 - (d : ℤ_[p]) * Z' ^ 2)) := by
      linear_combination h
    have h2 := congrArg toZMod (mul_left_cancel₀ p_ne_zero_padicInt h1)
    simp at h2
  · intro k Y Z h
    obtain ⟨hY, hZ⟩ := toZMod_eq_zero_of_nonsquare hd (Y := Y) (Z := Z) (by
      rw [← h, map_mul, toZMod_p, mul_zero])
    exact ⟨dvd_of_toZMod hY, dvd_of_toZMod hZ⟩

/-- **A nonsquare unit is not a norm from a ramified quadratic extension**: if `p ∥ d` and `u`
is not a square modulo `p`, then `u ∉ N(ℚ_p(√d)^×)`. -/
theorem not_isLocalNorm_of_ramified {d u : ℤ} (hpd : (p : ℤ) ∣ d) (hpd2 : ¬ (p : ℤ) ^ 2 ∣ d)
    (hu : ¬ IsSquare (u : ZMod p)) : ¬ IsLocalNorm ℚ_[p] d (u : ℚ_[p]) := by
  obtain ⟨d', rfl⟩ := hpd
  have hd' : ¬ (p : ℤ) ∣ d' := fun h => hpd2 (by obtain ⟨e, rfl⟩ := h; exact ⟨e, by ring⟩)
  have hd'0 : (d' : ZMod p) ≠ 0 := fun h => hd' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← PadicInt.coe_intCast]
  apply not_isLocalNorm_of_descent
  · intro Y Z h
    apply hu
    refine ⟨toZMod Y, ?_⟩
    have := congrArg toZMod h
    simp only [map_sub, map_mul, map_pow, map_intCast, Int.cast_mul, Int.cast_natCast,
      map_natCast, ZMod.natCast_self, zero_mul, sub_zero] at this
    rw [this]; ring
  · intro k Y Z h
    have h1 := congrArg toZMod h
    simp only [map_sub, map_mul, map_pow, map_intCast, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, sub_zero, map_natCast] at h1
    have hY : toZMod Y = 0 := by
      have : toZMod Y ^ 2 = 0 := by rw [← h1]; simp
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    obtain ⟨Y', rfl⟩ := dvd_of_toZMod hY
    refine ⟨⟨Y', rfl⟩, dvd_of_toZMod ?_⟩
    have h2 : (p : ℤ_[p]) * ((d' : ℤ_[p]) * Z ^ 2) =
        p * (p * Y' ^ 2 - (p : ℤ_[p]) ^ (2 * k + 1) * u) := by
      push_cast at h
      linear_combination h
    have h3 := congrArg toZMod (mul_left_cancel₀ p_ne_zero_padicInt h2)
    simp only [map_sub, map_mul, map_pow, map_intCast, map_natCast, ZMod.natCast_self,
      zero_mul, zero_sub, zero_pow (Nat.succ_ne_zero _), sub_zero, neg_zero] at h3
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hd'0
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4

end Descent

end ZInQ.FHPrinted

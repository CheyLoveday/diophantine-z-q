import ZInQKernel.Contrib.CloudB3E1RingClass.Instance
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# The field `K = ℚ(√k)` of the final companion

Manuscript `diophantine_zq.tex`, tex 2595–2603 and 2716–2721: "Let `K = ℚ(√k)` be imaginary, split at
`2N`, and different from `ℚ(i)` and `ℚ(√−3)`."

For `K = ℚ(s) ⊂ ℚ̄` with `s² = k`, `k < 0` squarefree, `k ≡ 1 (mod 4)`:
* `finrank_quadField_of_neg` (from `FromPairs.lean`): `[K : ℚ] = 2`;
* `discr_quadField`: `disc K = k`;
* `sq_rat_k`: `y² ∈ ℚ` forces `y ∈ ℚ` or `y ∈ ℚ s`;
* `no_sqrt_neg_one_k`, `no_cube_root_k`: `K ≠ ℚ(i)` for `k ≠ −1`, and `K ≠ ℚ(√−3)` for `k ≠ −3`;
* `units_k`: `𝒪_K^× = {±1}`;
* `splitsIn_of_squareAt`: a prime at which `k` is a unit square splits (`splittingCriterion_proof`).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open Neg7 (g)

variable {s : Qbar} {k : ℤ}

/-- `s² = k` in `K`. Kind: PROVED. -/
theorem g_sq_k (hs : s ^ 2 = algebraMap ℚ Qbar k) : g s ^ 2 = (k : quadField s) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  change s ^ 2 = ((k : quadField s) : Qbar)
  rw [hs]
  simp

/-- `[ℚ(s) : ℚ] = 2` for `s² = k < 0`. Kind: PROVED. -/
theorem hK_k (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) :
    Module.finrank ℚ (quadField s) = 2 :=
  finrank_quadField_of_neg (D := (k : ℚ)) (by simpa using hs) (by exact_mod_cast hk0)

/-- **`disc ℚ(√k) = k`** for `k` squarefree, `k ≡ 1 (mod 4)`, `k < 0`. Kind: PROVED. -/
theorem discr_quadField (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) (hksq : Squarefree k)
    (hk4 : k % 4 = 1) : discr (quadField s) = k :=
  ZInQ.Contrib.CloudB3RC53.Companion.discr_eq_of_sq (hK_k hs hk0) hksq hk4 (by omega)
    (g_sq_k hs)

/-- The non-trivial automorphism sends `s` to `−s`. Kind: PROVED. -/
theorem conj_g (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) :
    conjσ (hK_k hs hk0) (g s) = -g s := by
  set σ := conjσ (hK_k hs hk0)
  have h2 : (σ (g s)) ^ 2 = (g s) ^ 2 := by rw [← map_pow, g_sq_k hs, map_intCast]
  have h3 : (σ (g s) - g s) * (σ (g s) + g s) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · exfalso
    have hσ1 : σ = 1 := by
      have : σ.toAlgHom = (1 : quadField s ≃ₐ[ℚ] quadField s).toAlgHom :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := quadField s) (s := {s}) rfl
          (fun x hx => by
            obtain rfl := Set.mem_singleton_iff.mp hx
            change σ (g x) = g x
            exact sub_eq_zero.mp h)
      exact AlgEquiv.ext fun x => congrArg (fun φ : quadField s →ₐ[ℚ] quadField s => φ x) this
    exact (exists_conj (hK_k hs hk0)).choose_spec.1 hσ1
  · exact eq_neg_of_add_eq_zero_left h

/-- **Squares of rationals in `ℚ(√k)`**: if `y² ∈ ℚ` then `y ∈ ℚ` or `y ∈ ℚ s`. Kind: PROVED. -/
theorem sq_rat_k (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) {y : quadField s} {a : ℚ}
    (hy : y ^ 2 = algebraMap ℚ (quadField s) a) :
    (∃ r : ℚ, y = algebraMap ℚ _ r) ∨ (∃ r : ℚ, y = algebraMap ℚ _ r * g s) := by
  have hK := hK_k hs hk0
  have := isGalois_of_finrank_two hK
  set σ := conjσ hK
  have hfix : ∀ z : quadField s, σ z = z → z ∈ Set.range (algebraMap ℚ (quadField s)) := by
    intro z hz
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [conjσ_spec hK f hf]; exact hz
  have h2 : (σ y) ^ 2 = y ^ 2 := by rw [← map_pow, hy, AlgEquiv.commutes]
  have h3 : (σ y - y) * (σ y + y) = 0 := by ring_nf; rw [h2]; ring
  have hg0 : g s ≠ 0 := fun h => by
    have := g_sq_k hs; rw [h, zero_pow two_ne_zero] at this
    have hk : ((k : ℚ) : quadField s) = 0 := by exact_mod_cast this.symm
    have : (k : ℚ) = 0 := (algebraMap ℚ (quadField s)).injective (by simpa using hk)
    have : k = 0 := by exact_mod_cast this
    omega
  rcases mul_eq_zero.mp h3 with h | h
  · obtain ⟨r, hr⟩ := hfix y (sub_eq_zero.mp h)
    exact Or.inl ⟨r, hr.symm⟩
  · obtain ⟨r, hr⟩ := hfix (y / g s) (by
      rw [map_div₀, conj_g hs hk0, eq_neg_of_add_eq_zero_left h, neg_div_neg_eq])
    refine Or.inr ⟨r, ?_⟩
    rw [hr, div_mul_cancel₀ _ hg0]

/-- If `r² k = −m` with `m ∈ {1, 3}` and `k` squarefree, then `k = −m`. Kind: PROVED. -/
theorem eq_of_rat_sq_mul {r : ℚ} {m : ℤ} (hm : m = 1 ∨ m = 3) (hksq : Squarefree k)
    (h : r ^ 2 * k = -m) : k = -m := by
  have hr0 : r ≠ 0 := by rintro rfl; rcases hm with rfl | rfl <;> norm_num at h
  -- write `r = a/b` in lowest terms
  set a := r.num
  set b := (r.den : ℤ)
  have hb0 : (b : ℚ) ≠ 0 := by
    have : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    simp [b]
  have hrab : r = a / b := (Rat.num_div_den r).symm
  have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr r.reduced
  have hint : a ^ 2 * k = -m * b ^ 2 := by
    have := h
    rw [hrab, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hb0)] at this
    exact_mod_cast this
  -- `a² ∣ m`, so `a = ±1`
  have ha2 : a ^ 2 ∣ m := by
    have h1 : a ^ 2 ∣ m * b ^ 2 := ⟨-k, by linear_combination hint⟩
    exact (IsCoprime.pow hcop).dvd_of_dvd_mul_right h1
  have ha1 : a ^ 2 = 1 := by
    have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
    have hle := Int.le_of_dvd (by rcases hm with rfl | rfl <;> norm_num) ha2
    have hpos : 0 < a ^ 2 := by
      have : a ≠ 0 := Rat.num_ne_zero.mpr hr0
      positivity
    rcases hm with rfl | rfl
    · omega
    · have h3 : a ^ 2 = 1 ∨ a ^ 2 = 3 := by
        have : a ^ 2 ≤ 3 := hle
        interval_cases h4 : a ^ 2 <;> simp_all
      rcases h3 with h3 | h3
      · exact h3
      · exfalso
        have : IsSquare (3 : ℤ) := ⟨a, by rw [← h3]; ring⟩
        obtain ⟨c, hc⟩ := this
        have hc2 : c ^ 2 ≤ 4 := by nlinarith
        have hcb : -2 ≤ c ∧ c ≤ 2 := by constructor <;> nlinarith
        obtain ⟨h1, h2⟩ := hcb
        interval_cases c <;> omega
  rw [ha1, one_mul] at hint
  -- `k = −m b²` squarefree forces `b² = 1`
  have hb1 : b ^ 2 = 1 := by
    have hsq : b * b ∣ k := ⟨-m, by rw [hint]; ring⟩
    have hu := hksq b hsq
    have : b ^ 2 = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> norm_num
    exact this
  rw [hint, hb1, mul_one]

/-- **`K ≠ ℚ(i)`** for `k ≠ −1` squarefree. Kind: PROVED. -/
theorem no_sqrt_neg_one_k (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) (hksq : Squarefree k)
    (hk1 : k ≠ -1) : ∀ x : quadField s, x ^ 2 ≠ -1 := by
  intro x hx
  have hy : x ^ 2 = algebraMap ℚ (quadField s) (-1) := by rw [hx]; simp
  rcases sq_rat_k hs hk0 hy with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, ← map_pow] at hy
    have := (algebraMap ℚ (quadField s)).injective hy
    nlinarith [sq_nonneg r]
  · rw [hr, mul_pow, g_sq_k hs, ← map_pow] at hy
    have h7 : algebraMap ℚ (quadField s) (r ^ 2 * k) = algebraMap ℚ (quadField s) (-1) := by
      rw [map_mul]; simpa using hy
    have := (algebraMap ℚ (quadField s)).injective h7
    exact hk1 (by
      have := eq_of_rat_sq_mul (r := r) (m := 1) (Or.inl rfl) hksq (by push_cast; exact this)
      simpa using this)

/-- **`K ≠ ℚ(√−3)`** for `k ≠ −3` squarefree. Kind: PROVED. -/
theorem no_cube_root_k (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) (hksq : Squarefree k)
    (hk3 : k ≠ -3) : ∀ x : quadField s, x ^ 2 + x + 1 ≠ 0 := by
  intro x hx
  have hy : (2 * x + 1) ^ 2 = algebraMap ℚ (quadField s) (-3) := by
    rw [map_neg, map_ofNat]; linear_combination 4 * hx
  rcases sq_rat_k hs hk0 hy with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, ← map_pow] at hy
    have := (algebraMap ℚ (quadField s)).injective hy
    nlinarith [sq_nonneg r]
  · rw [hr, mul_pow, g_sq_k hs, ← map_pow] at hy
    have h7 : algebraMap ℚ (quadField s) (r ^ 2 * k) = algebraMap ℚ (quadField s) (-3) := by
      rw [map_mul]; simpa using hy
    have := (algebraMap ℚ (quadField s)).injective h7
    exact hk3 (by
      have := eq_of_rat_sq_mul (r := r) (m := 3) (Or.inr rfl) hksq (by push_cast; exact this)
      simpa using this)

/-- **`𝒪_K^× = {±1}`** for `K = ℚ(√k)`, `k < 0` squarefree, `k ≠ −1, −3` (tex 2720).
Kind: PROVED. -/
theorem units_k (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0) (hksq : Squarefree k)
    (hk1 : k ≠ -1) (hk3 : k ≠ -3) : ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1 :=
  units_quadField (D := (k : ℚ)) (by simpa using hs) (by exact_mod_cast hk0)
    (no_sqrt_neg_one_k hs hk0 hksq hk1) (no_cube_root_k hs hk0 hksq hk3)

/-- **A prime at which `k` is a unit square splits in `ℚ(√k)`** (tex 2604–2613, 2720).
Kind: PROVED. -/
theorem splitsIn_of_squareAt (hs : s ^ 2 = algebraMap ℚ Qbar k) (hk0 : k < 0)
    (hksq : Squarefree k) (hk4 : k % 4 = 1) {p : ℕ} (hp : p.Prime)
    (hsq : ZInQ.Contrib.CloudB3RC53.GenusOdd.SquareAt p k) :
    ZInQ.Contrib.CloudB3RC53.CST.SplitsIn (quadField s) p :=
  ZInQ.Contrib.CloudB3RC53.Splitting.splittingCriterion_proof (quadField s) (hK_k hs hk0) p hp
    (by rw [discr_quadField hs hk0 hksq hk4]; exact hsq)

end ZInQ.Contrib.CloudB3E1RingClass

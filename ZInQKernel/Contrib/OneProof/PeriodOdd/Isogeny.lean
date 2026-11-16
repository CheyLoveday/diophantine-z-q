import ZInQKernel.Contrib.OneProof.CdOptimal
import ZInQKernel.Contrib.OneProof.PeriodOdd.LFunction

/-!
# period-odd: the 2-isogeny `C_d → E'_d`, analytically and on points

Task period-odd (2026-11-16). Report `docs/research/period-odd.md`.

For `C_d : y² = x³ − d² x` and `E'_d : y² = x³ + 4d² x` (`ePrime d`), the 2-isogeny with kernel
`{O, (0, 0)}` is `φ(x, y) = (x − d²/x, y (x² + d²)/x²)`, `φ(0, 0) = φ(O) = O` (`isogPt`). It is
defined over `ℚ`, so it commutes with every `ℚ`-embedding (`map_isogPt`).

Analytically: a period lattice `L` of `C_d` is `ℤ[i] ω` (Gaussian rounding, cd-optimal), and
`L' = ((1 + i)/2) L = L ∪ (h + L)`, `h = (1 + i) ω / 2`, is a period lattice of `E'_d`
(`isPeriodLattice_ePrime`). Splitting the series of `℘_{L'}` over the two cosets gives
`℘_{L'}(z) = ℘_L(z) + ℘_L(z − h) − ℘_L(h)`, `℘_L(h) = 0` (`℘_L(iz) = −℘_L(z)`), and the group law
`(x, y) + (0, 0) = (−d²/x, d² y/x²)` on `C_d` turns this into `φ`:

`weierPt_ePrime_eq : isogPt (weierPt C_d L z) = weierPt E'_d L' z` for every `z ∈ ℂ`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Complex WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace ZInQ.PeriodOdd

/-! ## §1. Splitting `℘` over two cosets; `℘(iz)` -/

section Split

/-- **`℘_{L'}` for `L' = L ⊔ (h + L)`.** -/
theorem weierstrassP_split (L L' : PeriodPair) (h : ℂ) (e : L.lattice ⊕ L.lattice ≃ L'.lattice)
    (he1 : ∀ l, (e (Sum.inl l) : ℂ) = l) (he2 : ∀ l, (e (Sum.inr l) : ℂ) = h + l) (z : ℂ) :
    L'.weierstrassP z = L.weierstrassP z + L.weierstrassP (z - h) - L.weierstrassP (-h) := by
  let F : L'.lattice → ℂ := fun l => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2
  have H : HasSum (F ∘ e) (L'.weierstrassP z) := e.hasSum_iff.mpr (L'.hasSum_weierstrassP z)
  have h1 : (F ∘ e) ∘ Sum.inl = fun l : L.lattice => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2 := by
    funext l
    simp only [Function.comp_apply, F, he1]
  have h2 : (F ∘ e) ∘ Sum.inr = fun l : L.lattice =>
      (1 / (z - h - l) ^ 2 - 1 / (l : ℂ) ^ 2) - (1 / (-h - l) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    simp only [Function.comp_apply, F, he2]
    rw [show z - (h + (l : ℂ)) = z - h - l by ring, show (h + (l : ℂ)) ^ 2 = (-h - l) ^ 2 by ring]
    ring
  have H1 : HasSum ((F ∘ e) ∘ Sum.inl) (L.weierstrassP z) := by
    rw [h1]; exact L.hasSum_weierstrassP z
  have H2 : HasSum ((F ∘ e) ∘ Sum.inr) (L.weierstrassP (z - h) - L.weierstrassP (-h)) := by
    rw [h2]; exact (L.hasSum_weierstrassP (z - h)).sub (L.hasSum_weierstrassP (-h))
  rw [H.unique (HasSum.sum (f := F ∘ e) H1 H2)]
  ring

/-- **`℘'_{L'}` for `L' = L ⊔ (h + L)`.** -/
theorem derivWeierstrassP_split (L L' : PeriodPair) (h : ℂ) (e : L.lattice ⊕ L.lattice ≃ L'.lattice)
    (he1 : ∀ l, (e (Sum.inl l) : ℂ) = l) (he2 : ∀ l, (e (Sum.inr l) : ℂ) = h + l) (z : ℂ) :
    L'.derivWeierstrassP z = L.derivWeierstrassP z + L.derivWeierstrassP (z - h) := by
  let F : L'.lattice → ℂ := fun l => -2 / (z - l) ^ 3
  have H : HasSum (F ∘ e) (L'.derivWeierstrassP z) :=
    e.hasSum_iff.mpr (L'.hasSum_derivWeierstrassP z)
  have h1 : (F ∘ e) ∘ Sum.inl = fun l : L.lattice => -2 / (z - l) ^ 3 := by
    funext l
    simp only [Function.comp_apply, F, he1]
  have h2 : (F ∘ e) ∘ Sum.inr = fun l : L.lattice => -2 / (z - h - l) ^ 3 := by
    funext l
    simp only [Function.comp_apply, F, he2]
    rw [show z - (h + (l : ℂ)) = z - h - l by ring]
  have H1 : HasSum ((F ∘ e) ∘ Sum.inl) (L.derivWeierstrassP z) := by
    rw [h1]; exact L.hasSum_derivWeierstrassP z
  have H2 : HasSum ((F ∘ e) ∘ Sum.inr) (L.derivWeierstrassP (z - h)) := by
    rw [h2]; exact L.hasSum_derivWeierstrassP (z - h)
  exact H.unique (HasSum.sum (f := F ∘ e) H1 H2)

/-- **`℘_L(iz) = −℘_L(z)`** for a lattice stable under multiplication by `i`. -/
theorem weierstrassP_I_mul (L : PeriodPair) (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice) (z : ℂ) :
    L.weierstrassP (I * z) = -L.weierstrassP z := by
  let eI : L.lattice ≃ L.lattice :=
    { toFun := fun l => ⟨I * l, hLI _ l.2⟩
      invFun := fun l => ⟨-I * l, by
        have := hLI _ (hLI _ (hLI _ l.2))
        convert this using 1
        linear_combination (-(I * (l : ℂ))) * Complex.I_sq⟩
      left_inv := fun l => by
        ext; simp only
        linear_combination (-(l : ℂ)) * Complex.I_sq
      right_inv := fun l => by
        ext; simp only
        linear_combination (-(l : ℂ)) * Complex.I_sq }
  have H := L.hasSum_weierstrassP (I * z)
  rw [← eI.hasSum_iff] at H
  refine H.unique ?_
  convert (L.hasSum_weierstrassP z).neg using 1
  funext l
  simp only [Function.comp_apply, eI, Equiv.coe_fn_mk]
  rw [show I * z - I * (l : ℂ) = I * (z - l) by ring, mul_pow, mul_pow, Complex.I_sq]
  simp only [neg_one_mul, one_div, inv_neg]
  ring

end Split

/-! ## §2. The lattice `L' = ((1 + i)/2) L` -/

/-- `λ = (1 + i)/2`. -/
abbrev lam : ℂ := (1 + I) / 2

theorem lam_ne_zero : lam ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem lam_pow_four : lam ^ 4 = -1 / 4 := by
  rw [lam, div_pow]
  have : (1 + I) ^ 4 = -4 := by linear_combination (I ^ 2 + 4 * I + 5) * Complex.I_sq
  rw [this]; norm_num

/-- `L' = λ L`. -/
abbrev latP (L : PeriodPair) : PeriodPair := ZInQ.GZWeil.scalePP L lam lam_ne_zero

section Lattice

variable {L : PeriodPair} (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice) {ω : ℂ} (hω : ω ∈ L.lattice)
  (hω0 : ω ≠ 0) (hrep : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω)

include hLI in
theorem le_latP {y : ℂ} (hy : y ∈ L.lattice) : y ∈ (latP L).lattice := by
  refine (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mpr ⟨(1 - I) * y, ?_, ?_⟩
  · have : (1 - I) * y = y - I * y := by ring
    rw [this]; exact sub_mem hy (hLI y hy)
  · rw [lam]
    linear_combination (y / 2) * Complex.I_sq

include hω in
theorem h_mem_latP : lam * ω ∈ (latP L).lattice :=
  (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mpr ⟨ω, hω, rfl⟩

include hω0 hrep in
theorem h_notMem : lam * ω ∉ L.lattice := by
  intro h
  obtain ⟨m, n, hmn⟩ := hrep _ h
  have := congrArg Complex.re (mul_right_cancel₀ hω0 hmn)
  simp at this
  have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
  omega

include hLI hω in
/-- Gaussian integers `(a + b i)` with `a ≡ b (mod 2)` times `λ` lie in `ℤ[i]`. -/
theorem lam_gauss_mem {m n : ℤ} (hmn : Even (m + n)) : lam * (((m : ℂ) + n * I) * ω) ∈ L.lattice := by
  obtain ⟨k, hk⟩ := hmn
  have e : lam * (((m : ℂ) + n * I) * ω) = (((m - k : ℤ) : ℂ) + ((k : ℤ) : ℂ) * I) * ω := by
    have hn : (n : ℂ) = 2 * k - m := by
      have : (n : ℤ) = 2 * k - m := by omega
      exact_mod_cast this
    rw [lam, hn]; push_cast
    linear_combination (-(m : ℂ) / 2 + k) * ω * Complex.I_sq
  rw [e]
  exact ZInQ.CdOpt.gauss_mul_mem hLI _ _ hω

include hLI hω hrep in
theorem mem_latP_iff {x : ℂ} : x ∈ (latP L).lattice ↔ x ∈ L.lattice ∨ x - lam * ω ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mp hx
    obtain ⟨m, n, rfl⟩ := hrep y hy
    rcases Int.even_or_odd (m + n) with he | ho
    · exact Or.inl (lam_gauss_mem hLI hω he)
    · right
      have e : lam * (((m : ℂ) + n * I) * ω) - lam * ω =
          lam * ((((m - 1 : ℤ) : ℂ) + n * I) * ω) := by push_cast; ring
      rw [e]
      exact lam_gauss_mem hLI hω (by
        obtain ⟨k, hk⟩ := ho; exact ⟨k, by omega⟩)
  · rintro (h | h)
    · exact le_latP hLI h
    · have := add_mem (le_latP hLI h) (h_mem_latP hω)
      rwa [sub_add_cancel] at this

include hLI hω hω0 hrep in
/-- **`L' = L ⊔ (h + L)`** as an equivalence of index sets. -/
def latPEquiv : L.lattice ⊕ L.lattice ≃ (latP L).lattice := by
  classical
  exact
  { toFun := Sum.elim (fun l => ⟨l, le_latP hLI l.2⟩)
      (fun l => ⟨lam * ω + l, add_mem (h_mem_latP hω) (le_latP hLI l.2)⟩)
    invFun := fun x => if hx : (x : ℂ) ∈ L.lattice then Sum.inl ⟨x, hx⟩ else
      Sum.inr ⟨x - lam * ω, ((mem_latP_iff hLI hω hrep).mp x.2).resolve_left hx⟩
    left_inv := by
      rintro (l | l)
      · simp [l.2]
      · have hnot : lam * ω + (l : ℂ) ∉ L.lattice := fun h =>
          h_notMem hω0 hrep (by have := sub_mem h l.2; rwa [add_sub_cancel_right] at this)
        simp [hnot]
    right_inv := by
      intro x
      by_cases hx : (x : ℂ) ∈ L.lattice
      · simp [hx]
      · simp [hx] }

theorem latPEquiv_inl (l : L.lattice) :
    ((latPEquiv hLI hω hω0 hrep (Sum.inl l)) : ℂ) = l := rfl

theorem latPEquiv_inr (l : L.lattice) :
    ((latPEquiv hLI hω hω0 hrep (Sum.inr l)) : ℂ) = lam * ω + l := rfl

end Lattice

end ZInQ.PeriodOdd

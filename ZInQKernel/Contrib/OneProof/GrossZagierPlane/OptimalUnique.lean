import ZInQKernel.Contrib.OneProof.GrossZagierPlane

/-!
# gz-dict2: `IsOptimalParam` determines the parametrization up to sign (for D3)

Task gz-dict2 (2026-11-16/17). Report: `docs/research/gz-dict2.md` §4.

`isOptimalParam_unique`: two parametrizations of `E` satisfying gz-optimal's `IsOptimalParam` for the
same newform agree at every `τ ∈ ℍ` or are opposite at every `τ`. So the leaf
`GZDict2.GrossZagierPlaneOptCd` (and `GZAlg.GrossZagierAlgOptCd`) applies to at most `±φ` for one `φ`:
its optimality hypothesis assumes nothing beyond fixing the strong Weil parametrization up to `[−1]`.
Helpers: `℘_L`, `℘'_L` and `weierPt E L` depend only on the lattice (`weierPt_congr`), and
`weierPt E L` is odd (`weierPt_neg`).

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZDict2

/-! ## D3: `IsOptimalParam` determines `φ` up to sign -/

/-- `℘_L` depends only on the lattice. -/
theorem weierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.weierstrassP = L'.weierstrassP := by
  funext z
  have key : ∀ S T : Submodule ℤ ℂ, S = T → ∀ g : ℂ → ℂ, ∑' l : S, g l = ∑' l : T, g l := by
    rintro S T rfl g; rfl
  exact key _ _ h (fun l => 1 / (z - l) ^ 2 - 1 / l ^ 2)

/-- `℘'_L` depends only on the lattice. -/
theorem derivWeierstrassP_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  funext z
  have key : ∀ S T : Submodule ℤ ℂ, S = T → ∀ g : ℂ → ℂ, ∑' l : S, g l = ∑' l : T, g l := by
    rintro S T rfl g; rfl
  simp only [PeriodPair.derivWeierstrassP]
  rw [key _ _ h (fun l => 2 / (z - l) ^ 3)]

open Classical in
/-- `weierPt E L z` as a function of `(L.lattice, ℘_L, ℘'_L)`. -/
def wp (E : WeierstrassCurve ℚ) (S : Submodule ℤ ℂ) (P D : ℂ → ℂ) (z : ℂ) : (E⁄ℂ).Point :=
  if h : z ∉ S ∧ (E⁄ℂ).Nonsingular (P z - (E⁄ℂ).b₂ / 12)
      ((D z - (E⁄ℂ).a₁ * (P z - (E⁄ℂ).b₂ / 12) - (E⁄ℂ).a₃) / 2)
  then .some _ _ h.2 else 0

theorem weierPt_eq_wp (E : WeierstrassCurve ℚ) (L : PeriodPair) (z : ℂ) :
    ZInQ.GZHL3.weierPt E L z = wp E L.lattice L.weierstrassP L.derivWeierstrassP z := rfl

theorem weierPt_congr (E : WeierstrassCurve ℚ) {L L' : PeriodPair} (h : L.lattice = L'.lattice)
    (z : ℂ) : ZInQ.GZHL3.weierPt E L z = ZInQ.GZHL3.weierPt E L' z := by
  rw [weierPt_eq_wp, weierPt_eq_wp, h, weierstrassP_congr h, derivWeierstrassP_congr h]

/-- `weierPt` is odd: `℘` is even and `℘'` odd, and `-(x, y) = (x, -y - a₁x - a₃)`. -/
theorem weierPt_neg (E : WeierstrassCurve ℚ) (L : PeriodPair) (z : ℂ) :
    ZInQ.GZHL3.weierPt E L (-z) = -ZInQ.GZHL3.weierPt E L z := by
  rw [weierPt_eq_wp, weierPt_eq_wp]
  unfold wp
  set x := L.weierstrassP z - (E⁄ℂ).b₂ / 12 with hx
  set y := (L.derivWeierstrassP z - (E⁄ℂ).a₁ * x - (E⁄ℂ).a₃) / 2 with hyd
  have hP : L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12 = x := by rw [L.weierstrassP_neg]
  have hD : (L.derivWeierstrassP (-z) - (E⁄ℂ).a₁ * (L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12) -
      (E⁄ℂ).a₃) / 2 = (E⁄ℂ).negY x y := by
    rw [hP, L.derivWeierstrassP_neg, hyd]; simp only [WeierstrassCurve.Affine.negY]; ring
  by_cases h : z ∉ L.lattice ∧ (E⁄ℂ).Nonsingular x y
  · have h' : -z ∉ L.lattice ∧ (E⁄ℂ).Nonsingular (L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12)
        ((L.derivWeierstrassP (-z) - (E⁄ℂ).a₁ * (L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12) -
          (E⁄ℂ).a₃) / 2) := by
      rw [hD, hP, neg_mem_iff]
      exact ⟨h.1, (WeierstrassCurve.Affine.nonsingular_neg ..).2 h.2⟩
    rw [dite_eq_left h', dite_eq_left h, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hP, hD⟩
  · have h' : ¬ (-z ∉ L.lattice ∧ (E⁄ℂ).Nonsingular (L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12)
        ((L.derivWeierstrassP (-z) - (E⁄ℂ).a₁ * (L.weierstrassP (-z) - (E⁄ℂ).b₂ / 12) -
          (E⁄ℂ).a₃) / 2)) := by
      rw [hD, hP, neg_mem_iff, WeierstrassCurve.Affine.nonsingular_neg]
      exact h
    rw [dite_eq_right h', dite_eq_right h]
    rfl

/-- **`IsOptimalParam` pins `φ` up to sign.** Two parametrizations satisfying `IsOptimalParam` for the
same `f` and `E` agree at every `τ ∈ ℍ` or are opposite at every `τ`: both period lattices are the
lattice of `E` (`g₂, g₃` determine it), so `c Λ_f = c' Λ_f`, whence `c'/c ∈ ℤ` and `c/c' ∈ ℤ`, i.e.
`c' = ±c`. -/
theorem isOptimalParam_unique {N : ℕ} [NeZero N] {f : Newform N 2} {E : WeierstrassCurve ℚ}
    {X Y X' Y' : ℍ → ℂ} (h : ZInQ.GZOptimal.IsOptimalParam N f E X Y)
    (h' : ZInQ.GZOptimal.IsOptimalParam N f E X' Y') :
    (∀ τ, ZInQ.GZModuli.modPt E X' Y' τ = ZInQ.GZModuli.modPt E X Y τ) ∨
    (∀ τ, ZInQ.GZModuli.modPt E X' Y' τ = -ZInQ.GZModuli.modPt E X Y τ) := by
  obtain ⟨L, c, hL, hlat, hpt⟩ := h
  obtain ⟨L', c', hL', hlat', hpt'⟩ := h'
  have hLL : L.lattice = L'.lattice :=
    ZInQ.CdOpt.lattice_eq_of_g₂_g₃ (hL.1.trans hL'.1.symm) (hL.2.trans hL'.2.symm)
  -- `L.ω₁ = c w = c' w'` with `w, w' ∈ Λ_f`
  have hω : L.ω₁ ∈ L.lattice := L.ω₁_mem_lattice
  obtain ⟨w, hw, hcw⟩ := Submodule.mem_map.1 (hlat ▸ hω)
  obtain ⟨w', hw', hcw'⟩ := Submodule.mem_map.1 ((hLL ▸ hlat') ▸ hω)
  simp only [LinearMap.mulLeft_apply] at hcw hcw'
  have hω0 := ZInQ.GZOptimal.ω₁_ne_zero L
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcw; exact hω0 hcw.symm
  have hc0' : c' ≠ 0 := by rintro rfl; simp at hcw'; exact hω0 hcw'.symm
  -- `c' w ∈ L.lattice`, `c w' ∈ L.lattice`
  have h1 : (c' : ℂ) * w ∈ L.lattice := by
    rw [hLL, hlat']; exact Submodule.mem_map.2 ⟨w, hw, rfl⟩
  have h2 : (c : ℂ) * w' ∈ L.lattice := by
    rw [hlat]; exact Submodule.mem_map.2 ⟨w', hw', rfl⟩
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hcC' : (c' : ℂ) ≠ 0 := by exact_mod_cast hc0'
  obtain ⟨m, hm⟩ := ZInQ.GZOptimal.rat_mem_int (L := L) (q := c' / c) (by
    have : ((c' / c : ℚ) : ℂ) * L.ω₁ = (c' : ℂ) * w := by
      rw [← hcw]; push_cast; field_simp
    rw [this]; exact h1)
  obtain ⟨m', hm'⟩ := ZInQ.GZOptimal.rat_mem_int (L := L) (q := c / c') (by
    have : ((c / c' : ℚ) : ℂ) * L.ω₁ = (c : ℂ) * w' := by
      rw [← hcw']; push_cast; field_simp
    rw [this]; exact h2)
  have hmm : m * m' = 1 := by
    have : ((m * m' : ℤ) : ℚ) = 1 := by
      push_cast; rw [← hm, ← hm']; field_simp
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with hm1 | hm1
  · left
    have hcc : c' = c := by
      have : c' / c = 1 := by rw [hm, hm1]; simp
      field_simp at this; linarith
    intro τ
    rw [hpt', hpt, hcc, weierPt_congr E hLL.symm]
  · right
    have hcc : c' = -c := by
      have : c' / c = -1 := by rw [hm, hm1]; simp
      field_simp at this; linarith
    intro τ
    rw [hpt', hpt, hcc, weierPt_congr E hLL.symm, ← weierPt_neg]
    congr 1; push_cast; ring

end ZInQ.GZDict2

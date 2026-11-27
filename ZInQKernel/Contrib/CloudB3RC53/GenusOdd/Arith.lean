import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-!
# GenusOdd: elementary facts used by (3.4) (PROVED)

* `qtwist_Δ`, `qtwist_isElliptic`: `Δ(E^{(d)}) = d⁶ Δ(E)`, so `E^{(d)}` is elliptic for `d ≠ 0`.
* `analyticRank_zero_iff`, `analyticRank_one`: `ord_{s=1} = 0` means `L(1) ≠ 0`; `ord_{s=1} = 1`
  gives `L(1) = 0` and `L'(1) ≠ 0`.
* `SquareAt` arithmetic: products, `p ∤ d`.
-/

noncomputable section

open Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

theorem qtwist_Δ (E : WeierstrassCurve ℚ) (d : ℚ) : (qtwist E d).Δ = d ^ 6 * E.Δ := by
  simp only [qtwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem qtwist_isElliptic (E : WeierstrassCurve ℚ) [E.IsElliptic] {d : ℚ} (hd : d ≠ 0) :
    (qtwist E d).IsElliptic :=
  ⟨by rw [qtwist_Δ]; exact (IsUnit.mk0 _ (pow_ne_zero 6 hd)).mul E.isUnit_Δ⟩

theorem analyticRank_zero_iff {E : WeierstrassCurve ℚ} :
    AnalyticRank E 0 ↔ ∃ F, IsLContinuation E F ∧ F 1 ≠ 0 := by
  constructor
  · rintro ⟨F, hd, hagree, hord⟩
    refine ⟨F, ⟨hd, hagree⟩, ?_⟩
    have := analyticOrderAt_eq_zero.mp (by exact_mod_cast hord)
    exact this.resolve_left (not_not.mpr (hd.analyticAt 1))
  · rintro ⟨F, ⟨hd, hagree⟩, h1⟩
    exact ⟨F, hd, hagree, by exact_mod_cast analyticOrderAt_eq_zero.mpr (Or.inr h1)⟩

theorem analyticRank_zero_of_Lval_ne_zero {E : WeierstrassCurve ℚ} (h : Lval E ≠ 0) :
    AnalyticRank E 0 := by
  unfold Lval at h
  split_ifs at h with hex
  · exact analyticRank_zero_iff.mpr ⟨_, Classical.choose_spec hex, h⟩
  · exact absurd rfl h

theorem analyticRank_one {E : WeierstrassCurve ℚ} (h : AnalyticRank E 1) :
    ∃ F, IsLContinuation E F ∧ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  obtain ⟨F, hd, hagree, hord⟩ := h
  have hF1 : F 1 = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [hord]; norm_num)
  refine ⟨F, ⟨hd, hagree⟩, hF1, ?_⟩
  have key := (hd.analyticAt (1 : ℂ)).analyticOrderAt_deriv_add_one
  simp only [hF1, sub_zero] at key
  rw [show (fun x => F x) = F from rfl, hord] at key
  have h0 : analyticOrderAt (deriv F) 1 = 0 := by
    by_contra hne
    have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv F) 1 := Order.one_le_iff_ne_zero.mpr hne
    have h2 : (1 : ℕ∞) + 1 ≤ analyticOrderAt (deriv F) 1 + 1 := add_le_add h1 le_rfl
    rw [key] at h2
    norm_num at h2
  have := analyticOrderAt_eq_zero.mp h0
  exact this.resolve_left (not_not.mpr ((hd.analyticAt 1).deriv))

/-! ### Square classes -/

theorem SquareAt.not_dvd {p : ℕ} {d : ℤ} (h : SquareAt p d) : ¬ (p : ℤ) ∣ d := h.1

theorem SquareAt.mul {p : ℕ} {a b : ℤ} (ha : SquareAt p a) (hb : SquareAt p b) (hp : p.Prime) :
    SquareAt p (a * b) := by
  refine ⟨fun hdvd => ?_, fun h2 => ?_, fun h2 => ?_⟩
  · have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hp'.dvd_or_dvd hdvd with h | h
    · exact ha.1 h
    · exact hb.1 h
  · rw [Int.mul_emod, ha.2.1 h2, hb.2.1 h2]; rfl
  · obtain ⟨x, hx⟩ := ha.2.2 h2
    obtain ⟨y, hy⟩ := hb.2.2 h2
    exact ⟨x * y, by push_cast; rw [hx, hy]; ring⟩

theorem SquareAt.mod_four {d : ℤ} (h : SquareAt 2 d) : d % 4 = 1 := by
  have := h.2.1 rfl
  omega

theorem SquareAt.odd {d : ℤ} (h : SquareAt 2 d) : Odd d := by
  have := h.2.1 rfl
  exact Int.odd_iff.mpr (by omega)

end ZInQ.Contrib.CloudB3RC53.GenusOdd

import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Two

/-!
# Mattuck: non-vacuity of the full rational `2`-torsion hypothesis

The curve `y² = x³ − x` (`a₄ = −1`, all other coefficients `0`, `Δ = 64`) over any field of
characteristic zero is elliptic and has exactly the four rational `2`-torsion points
`O, (0, 0), (1, 0), (−1, 0)` (`natCard_twoTorsion_W0`). Over the completed integers `𝒪_w` at any
finite place of a number field it is an integral model with `|E(K_w)[2]| = 4`
(`exists_curve_card_twoTorsion_eq_four`), so the hypotheses of `MattuckOdd`, `MattuckTwo` and
`hkum_of_mattuck_all` are satisfiable; at a place above `2` the conclusion reads
`dim E(K_w)/2 = 2 + [K_w : ℚ₂]` (`mattuckTwo_nonvacuous`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open WeierstrassCurve IsDedekindDomain NumberField ZInQ.Contrib.CloudB3RC53.RankCounts

/-- `y² = x³ − x`. -/
def W0 (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

section Field

variable (F : Type*) [Field F] [CharZero F]

theorem isElliptic_W0 : (W0 F).IsElliptic := by
  refine ⟨?_⟩
  have : (W0 F).Δ = 64 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, W0]
    norm_num
  rw [this]
  exact IsUnit.mk0 _ (by norm_num)

omit [CharZero F] in
theorem nonsingular_W0 {x : F} (hx : x ^ 3 - x = 0) (hx' : 3 * x ^ 2 - 1 ≠ 0) :
    (W0 F).toAffine.Nonsingular x 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩
  · simp only [W0]; linear_combination -hx
  · simp only [W0]; intro h; apply hx'; linear_combination -h

variable [DecidableEq F]

/-- The four `2`-torsion points. -/
def tor2 : Fin 4 → (W0 F).toAffine.Point
  | 0 => 0
  | 1 => .some 0 0 (nonsingular_W0 F (by ring) (by norm_num))
  | 2 => .some 1 0 (nonsingular_W0 F (by ring) (by norm_num))
  | 3 => .some (-1) 0 (nonsingular_W0 F (by ring) (by norm_num))

theorem two_nsmul_eq_zero_iff (P : (W0 F).toAffine.Point) :
    2 • P = 0 ↔ ∃ i, tor2 F i = P := by
  constructor
  · intro h
    rcases P with _ | ⟨x, y, hxy⟩
    · exact ⟨0, rfl⟩
    rw [two_nsmul] at h
    have hy : y = (W0 F).toAffine.negY x y := by
      by_contra hne
      rw [Affine.Point.add_self_of_Y_ne hne] at h
      exact Affine.Point.some_ne_zero _ h
    have hy0 : y = 0 := by
      simp only [Affine.negY, W0, zero_mul, sub_zero] at hy
      have h2y : (2 : F) * y = 0 := by linear_combination hy
      exact (mul_eq_zero.mp h2y).resolve_left two_ne_zero
    subst hy0
    have he := hxy.1
    rw [Affine.equation_iff'] at he
    simp only [W0] at he
    have hx : x * (x - 1) * (x + 1) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp hx with hx | hx
    · rcases mul_eq_zero.mp hx with hx | hx
      · subst hx; exact ⟨1, rfl⟩
      · obtain rfl : x = 1 := by linear_combination hx
        exact ⟨2, rfl⟩
    · obtain rfl : x = -1 := by linear_combination hx
      exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [two_nsmul]
    fin_cases i
    · rfl
    all_goals
      apply Affine.Point.add_self_of_Y_eq
      simp [Affine.negY, W0]

omit [DecidableEq F] in
theorem tor2_injective : Function.Injective (tor2 F) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tor2] <;> norm_num at h

/-- **`|E(F)[2]| = 4` for `y² = x³ − x`.** PROVED. -/
theorem natCard_twoTorsion_W0 :
    Nat.card (Submodule.torsionBy ℤ (W0 F).toAffine.Point 2) = 4 := by
  have hmem : ∀ i, tor2 F i ∈ Submodule.torsionBy ℤ (W0 F).toAffine.Point 2 := fun i => by
    rw [Submodule.mem_torsionBy_iff, two_zsmul, ← two_nsmul]
    exact (two_nsmul_eq_zero_iff F _).mpr ⟨i, rfl⟩
  rw [← Nat.card_eq_of_bijective (fun i => (⟨tor2 F i, hmem i⟩ :
      Submodule.torsionBy ℤ (W0 F).toAffine.Point 2)) ⟨fun i j h => tor2_injective F
      (congrArg Subtype.val h), fun P => ?_⟩, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hP : 2 • (P : (W0 F).toAffine.Point) = 0 := by
    have := (Submodule.mem_torsionBy_iff _ _).mp P.2
    rwa [two_zsmul, ← two_nsmul] at this
  obtain ⟨i, hi⟩ := (two_nsmul_eq_zero_iff F _).mp hP
  exact ⟨i, Subtype.ext hi⟩

end Field

section Place

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem baseChange_W0 :
    (W0 (w.adicCompletionIntegers K)).baseChange (w.adicCompletion K) =
      W0 (w.adicCompletion K) := by
  ext <;> simp [W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem charZero_adicCompletion : CharZero (w.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (w.adicCompletion K)).injective

open scoped Classical in
/-- **Non-vacuity of the full rational `2`-torsion hypothesis**: at every finite place `w` of a
number field there is a Weierstrass curve over `𝒪_w`, elliptic over `K_w`, with
`|E(K_w)[2]| = 4` (`y² = x³ − x`). PROVED. -/
theorem exists_curve_card_twoTorsion_eq_four :
    ∃ (C : WeierstrassCurve (w.adicCompletionIntegers K))
      (_ : (C.baseChange (w.adicCompletion K)).IsElliptic),
      Nat.card (Submodule.torsionBy ℤ (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4 := by
  have := charZero_adicCompletion K w
  refine ⟨W0 _, ?_, ?_⟩
  · rw [baseChange_W0]; exact isElliptic_W0 _
  · rw [baseChange_W0]; exact natCard_twoTorsion_W0 _

open scoped Classical in
/-- **`MattuckTwo` is not vacuous**: at a place above `2`, `y² = x³ − x` over `𝒪_w` has
`dim E(K_w)/2 = 2 + [K_w : ℚ₂]`. PROVED. -/
theorem mattuckTwo_nonvacuous [w.asIdeal.LiesOver (vP two).asIdeal] :
    letI := qpAlg K two w
    ∃ (C : WeierstrassCurve (w.adicCompletionIntegers K))
      (_ : (C.baseChange (w.adicCompletion K)).IsElliptic),
      Module.finrank (ZMod 2) (ModN (C.baseChange (w.adicCompletion K)).toAffine.Point 2) =
        2 + Module.finrank ℚ_[2] (w.adicCompletion K) := by
  obtain ⟨C, hC, h4⟩ := exists_curve_card_twoTorsion_eq_four K w
  exact ⟨C, hC, (finrank_two K w C h4).2⟩

end Place

end ZInQ.Contrib.CloudB3RC53.Mattuck

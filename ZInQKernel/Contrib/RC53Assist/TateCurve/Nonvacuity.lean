import ZInQKernel.Contrib.RC53Assist.TateCurve.TateReading
import ZInQKernel.Contrib.RC53Assist.TateCurve.AdditiveReading

/-!
# Non-vacuity checks

There are genuine admissible parameters in the local fields used by the
Tate print. Compatible Kummer roots exist in their algebraic closures.
A nonidentity order-two `SL₂` operator supplies a concrete model of the
finite-inertia argument. The explicit rational curve below has nonzero
`c₄`, `c₆`, and discriminant, so the quadratic-descent hypotheses are not
empty either.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module WeierstrassCurve
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped Classical WithZero

/-- **PROVED**: the actual rational completion at any prime contains a
nonzero element of valuation less than one.
Locator: surjectivity of its normalized discrete valuation. -/
theorem admissible_parameter_exists (p : ℕ) (hp : p.Prime) :
    ∃ q : ((primeIdealQ p hp).adicCompletion ℚ)ˣ,
      Valued.v (q : (primeIdealQ p hp).adicCompletion ℚ) < 1 := by
  let t : ℤᵐ⁰ := ↑(Multiplicative.ofAdd (-1 : ℤ))
  obtain ⟨q, hq⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
    (K := ℚ) (v := primeIdealQ p hp) t
  have ht0 : t ≠ 0 := WithZero.coe_ne_zero
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, map_zero] at hq
    exact ht0 hq.symm
  refine ⟨Units.mk0 q hq0, ?_⟩
  change Valued.v q < 1
  rw [hq]
  exact WithZero.coe_lt_coe.mpr (by decide)

/-- **PROVED**: the compatible-root hypotheses used by the basis
construction are populated for every genuine local parameter.
Locator: `kummerRoots_nonempty`. -/
theorem local_kummer_roots_exist (p : ℕ) (hp : p.Prime) (ℓ : ℕ) [Fact ℓ.Prime]
    (q : ((primeIdealQ p hp).adicCompletion ℚ)ˣ) :
    Nonempty (KummerRoots (closureParameter q) ℓ) :=
  kummerRoots_nonempty (closureParameter q)

/-- **PROVED**: a concrete nonidentity finite-order `SL₂` operator has an
invertible augmentation defect. Locator: the matrix `-1` on `ℚ²`. -/
theorem finite_inertia_matrix_model :
    ∃ A : Matrix (Fin 2) (Fin 2) ℚ,
      A.det = 1 ∧ A ≠ 1 ∧ A ^ 2 = 1 ∧ (A - 1).det ≠ 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := -1
  have hd : A.det = 1 := by simp [A, Matrix.det_neg, Fintype.card_fin]
  have hn : A ≠ 1 := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
    norm_num [A, Matrix.one_apply] at h00
  have hp : A ^ 2 = 1 := by simp [A, sq]
  exact ⟨A, hd, hn, hp,
    matrix_finite_order_sub_one_det_ne_zero A hd hn 2 (by decide) hp⟩

/-- **DEFINITION**: a rational Weierstrass equation with a nonintegral
`5`-adic `j`-invariant. Its invariants are checked below.
Locator: the Weierstrass invariant formulas. -/
def rational_tate_example : WeierstrassCurve ℚ := ⟨1, 0, 0, 0, 5⟩

/-- **PROVED**: the displayed rational equation is genuinely elliptic.
Locator: its discriminant `-10805`. -/
instance rational_tate_example_elliptic : rational_tate_example.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [rational_tate_example, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **PROVED**: nonzero invariants for the explicit curve.
Locator: the Weierstrass invariant formulas. -/
theorem rational_tate_example_invariants :
    rational_tate_example.c₄ = 1 ∧ rational_tate_example.c₆ = -4321 ∧
      rational_tate_example.Δ = -10805 ∧ rational_tate_example.j = -1 / 10805 := by
  norm_num [rational_tate_example, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
    WeierstrassCurve.j_eq, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end ZInQ.Contrib.RC53Assist.TateCurve

import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Bundle
import ZInQKernel.Contrib.CloudB3RC53.OpenImage.Basic

/-!
# Lane RC22 (glue sweep), Tate share: lane RC9's former field `GlueArith.det` is false

Lane RC9 (`RC/PrintsArith/Bundle.lean`) bundled two textbook facts:

```
structure GlueArith : Prop where
  cmj : CMjInteger
  det : ∀ E : WeierstrassCurve ℚ, DetTateTwoCyclotomic E
```

The field `det` quantified over **all** Weierstrass curves over `ℚ`, with no `[E.IsElliptic]`, while
`TateMod E 2` is the vendored Tate module of the group of *nonsingular* points `(E⁄ℚ̄)(ℚ̄)`, which is
defined for singular cubics too. For the cuspidal cubic `y² = x³` that group has no nonzero
`2`-power torsion (a point `P = -P` has `y = 0`, hence `x = 0`, and `(0, 0)` is singular), so its
`2`-adic Tate module is zero and `det ρ₂(σ) = 1` for every `σ ∈ G_ℚ`; `DetTateTwoCyclotomic` would then
say that every `σ` fixes `μ_{2^∞}`, but complex conjugation moves `√-1`. Hence
`not_forall_detTateTwoCyclotomic` (PROVED): the old bundle was uninhabitable, and lane RC9's
`ecurve_hasNoCM`, `ecurve_serre_scalar`, `ecurve_serre_SL2_part`, `ecurve_kato_hyp_v` were vacuous.

**Fixed at the source (lane RC27).** The field `det` has been dropped from `GlueArith`, which now holds
only `CMjInteger` (`PrintsArith.glueArith_iff`); the direction `DetTateTwoCyclotomic E` is true, and
proved in the tree, for every *elliptic* `E/ℚ`
(`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`, recorded in lane RC9's file as
`PrintsArith.detTateTwoCyclotomic_of_isElliptic`), and lane RC9's four theorems discharge the
determinant with it. The counterexample below stays as the record of why the unrestricted field
cannot be reinstated; the bridges of `TatePrintsArith.lean`, which need only `CMjInteger` and the
prints, now agree with lane RC9's theorems.

Manuscript (11/5 version, `diophantine_zq.tex`): the GLUE is used at tex 3597–3605
(`ex:arith-moving-character`, "the determinant is the cyclotomic character") and, through
`kato_hyp_v`, at tex 7228–7231; the manuscript applies it only to the elliptic curves `E_ℓ`
(`c₄ = 208ℓ²`, `Δ = 2304ℓ⁶`, tex 1765), so the defect was in the Lean bundle, not in the text.
-/
noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith
open scoped WeierstrassCurve

/-- The cuspidal cubic `y² = x³` over `ℚ` (all Weierstrass coefficients zero). -/
def cusp : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 0⟩

/-- `y² = x³` is singular: its discriminant is `0`, so it is not elliptic (PROVED). -/
theorem cusp_Δ : cusp.Δ = 0 := by
  simp [cusp, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The coefficient `a₁` of `y² = x³` over `ℚ̄` is `0` (PROVED). -/
theorem cuspQbar_a₁ : (cusp⁄Qbar).toAffine.a₁ = 0 := by simp [cusp]
/-- The coefficient `a₂` of `y² = x³` over `ℚ̄` is `0` (PROVED). -/
theorem cuspQbar_a₂ : (cusp⁄Qbar).toAffine.a₂ = 0 := by simp [cusp]
/-- The coefficient `a₃` of `y² = x³` over `ℚ̄` is `0` (PROVED). -/
theorem cuspQbar_a₃ : (cusp⁄Qbar).toAffine.a₃ = 0 := by simp [cusp]
/-- The coefficient `a₄` of `y² = x³` over `ℚ̄` is `0` (PROVED). -/
theorem cuspQbar_a₄ : (cusp⁄Qbar).toAffine.a₄ = 0 := by simp [cusp]
/-- The coefficient `a₆` of `y² = x³` over `ℚ̄` is `0` (PROVED). -/
theorem cuspQbar_a₆ : (cusp⁄Qbar).toAffine.a₆ = 0 := by simp [cusp]

/-- No nonzero nonsingular point of `y² = x³` over `ℚ̄` is killed by `2` (PROVED): `P = -P` forces
`y = 0`, then `x = 0`, and `(0, 0)` is the singular point. -/
theorem cusp_two_torsion (P : (cusp⁄Qbar).toAffine.Point) (hP : 2 • P = 0) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · exfalso
    have h1 : WeierstrassCurve.Affine.Point.some x y h =
        -WeierstrassCurve.Affine.Point.some x y h := by
      rw [two_nsmul] at hP
      exact eq_neg_of_add_eq_zero_left hP
    rw [WeierstrassCurve.Affine.Point.neg_some] at h1
    simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and] at h1
    have hy0 : y = 0 := by
      have h2 : y = -y - (cusp⁄Qbar).toAffine.a₁ * x - (cusp⁄Qbar).toAffine.a₃ := h1
      rw [cuspQbar_a₁, cuspQbar_a₃] at h2
      have h3 : (2 : Qbar) * y = 0 := by linear_combination h2
      exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
    rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff'] at h
    obtain ⟨heq, hns⟩ := h
    simp only [cuspQbar_a₁, cuspQbar_a₂, cuspQbar_a₃, cuspQbar_a₄, cuspQbar_a₆, hy0] at heq hns
    have hx0 : x = 0 := by
      have : x ^ 3 = 0 := by linear_combination -heq
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    rw [hx0] at hns
    norm_num at hns

/-- No nonzero nonsingular point of `y² = x³` over `ℚ̄` is killed by a power of `2` (PROVED). -/
theorem cusp_twoPow_torsion (n : ℕ) (P : (cusp⁄Qbar).toAffine.Point) (hP : 2 ^ n • P = 0) :
    P = 0 := by
  induction n generalizing P with
  | zero => simpa using hP
  | succ n ih =>
    apply cusp_two_torsion
    apply ih
    rw [smul_smul, ← pow_succ]
    exact hP

/-- **The `2`-adic Tate module of `y² = x³` is zero** (PROVED): every level `E[2^n]` of the vendored
Tate module of the nonsingular points over `ℚ̄` is trivial. -/
instance subsingleton_tateMod_cusp : Subsingleton (TateMod cusp 2) := by
  constructor
  intro a b
  ext n
  have h0 : ∀ z : TauCeti.TateModuleLevel 2 (cusp⁄Qbar).toAffine.Point n, z = 0 := by
    intro z
    apply Subtype.ext
    apply cusp_twoPow_torsion n
    exact AddSubgroup.torsionBy.nsmul_iff.mp z.2
  rw [h0 (TauCeti.TateModule.proj n a), h0 (TauCeti.TateModule.proj n b)]

/-- For `y² = x³`, `det ρ₂(σ) = 1` for every `σ ∈ G_ℚ` (PROVED: the Tate module is zero). -/
theorem det_tateRep_cusp (σ : GalQ) : LinearMap.det (tateRep cusp 2 σ) = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

/-- Some `σ ∈ G_ℚ` moves a `4`-th root of unity (PROVED: complex conjugation, in the form
`ZInQ.Contrib.CloudB3RC53.OpenImage.complexConj`, moves a square root of `-1`). -/
theorem exists_moves_root_of_unity :
    ∃ (σ : GalQ) (ζ : Qbar), ζ ^ (2 ^ 2) = 1 ∧ σ ζ ≠ ζ := by
  obtain ⟨s, hs⟩ := ZInQ.Contrib.CloudB3RC53.OpenImage.exists_sqrt (-1)
  refine ⟨ZInQ.Contrib.CloudB3RC53.OpenImage.complexConj, s, ?_, ?_⟩
  · rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hs]
    simp
  · have h := ZInQ.Contrib.CloudB3RC53.OpenImage.complexConj_not_mem (k := -1) (by norm_num) hs
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h
    exact h

/-- **Lane RC9's GLUE `DetTateTwoCyclotomic` is false for the singular cubic `y² = x³`** (PROVED).
Consumer: the former field `GlueArith.det` (lane RC9, `RC/PrintsArith/Bundle.lean`; dropped by lane
RC27), used at tex 3597–3605 through `ecurve_serre_SL2_part` and at tex 7228–7231 through
`ecurve_kato_hyp_v`. Kind: PROVED (a counterexample; standard axioms only). -/
theorem not_detTateTwoCyclotomic_cusp : ¬ DetTateTwoCyclotomic cusp := by
  intro h
  obtain ⟨σ, ζ, hζ, hσ⟩ := exists_moves_root_of_unity
  exact hσ (h σ (det_tateRep_cusp σ) 2 ζ hζ)

/-- **`det ρ₂ = χ₂` cannot hold for all Weierstrass curves over `ℚ`** (PROVED, from
`not_detTateTwoCyclotomic_cusp`). The statement is true, and proved in the tree, under
`[E.IsElliptic]` (`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`). -/
theorem not_forall_detTateTwoCyclotomic : ¬ ∀ E : WeierstrassCurve ℚ, DetTateTwoCyclotomic E :=
  fun h => not_detTateTwoCyclotomic_cusp (h cusp)

end ZInQ.Manuscript.RC.GlueSweep.Tate

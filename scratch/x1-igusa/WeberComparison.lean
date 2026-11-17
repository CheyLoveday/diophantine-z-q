import ZInQKernel.Contrib.OneProof.X1Igusa
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! # x1-igusa (scratch): the `K_N = ℚ(j, f₁)` comparison, stated

isj1-dict's `AfTateCharPolyPicZero` is a direct instance of Diamond–Shurman Thm 9.5.4 once DS's `X₁(N)_alg`, whose
function field DS define as `ℚ(j, f₁)` inside the meromorphic functions on `ℍ` (`f₁ = (g₂g₃/Δ)·℘_τ(1/N)`, Weber's
function), is a model in the kernel's sense (`IsX1Model N`, function field `ℚ(j)(x(P))`).  The function-field half of
that is the statement below: the ideal of polynomial relations `F(j, f₁) = 0` over `ℚ` is the ideal of relations
`F(j, w(P)) = 0` in `\overline{ℚ(j)}`, for one point `P` of exact order `N` of the kernel's `E_j`, where
`w(P) = x_DS(P)/(g_j − 27)` and `x_DS = αx(P) − 3/2` is the `x`-coordinate on Diamond–Shurman's model (`X1Igusa.cDS`).
Equal ideals give `ℚ(j, f₁) ≅ Frac(ℚ[J,T]/I) ≅ ℚ(j)(w(P)) = ℚ(j)(x(P))`.

Rating: GLUE (provable: uniformization `ℂ/⟨1,τ⟩ ≅ E_{j(τ)}`, the division polynomial at `℘(1/N)`, the identity
theorem on `ℍ`, and `j` non-constant; proof sketch in docs/research/x1-igusa.md §4).  Not used by the discharge. -/

noncomputable section

namespace X1Igusa.Weber

open LeafModCurves WeierstrassCurve T5Glue

/-- The kernel-model expression of Weber's function at `P`: `w(P) = (α x(P) − 3/2)/(g_j − 27)`. -/
def wOf (P : EjBar.toAffine.Point) : Kbar :=
  (algebraMap Qj Kbar alpha * xCoord P + algebraMap Qj Kbar (-3 / 2)) / algebraMap Qj Kbar (gDS - 27)

/-- `F(J, T) ∈ ℚ[J][T]` at `(J, T) = (j(τ), f₁(τ))`, `f₁(τ) = weber(⟨1, τ⟩, 1/N)`. -/
def evAn (N : ℕ) (F : Polynomial (Polynomial ℚ)) (τ : UpperHalfPlane) : ℂ :=
  (F.map (Polynomial.eval₂RingHom (Rat.castHom ℂ) (jL (pp τ)))).eval (weber (pp τ) (1 / (N : ℂ)))

/-- `F(J, T)` at `(J, T) = (j, w(P))` in `\overline{ℚ(j)}`. -/
def evAlg (F : Polynomial (Polynomial ℚ)) (P : EjBar.toAffine.Point) : Kbar :=
  (F.map ((algebraMap Qj Kbar).comp (algebraMap (Polynomial ℚ) Qj))).eval (wOf P)

/-- **GLUE (the `K_N = ℚ(j, f₁)` comparison; Diamond–Shurman §7.5–7.7, Shimura 1971 Ch. 6).** For `N ≥ 2` some
point `P` of exact order `N` of `E_j` has: a polynomial `F ∈ ℚ[J][T]` vanishes at `(j(τ), f₁(τ))` for every `τ ∈ ℍ`
with `g₂(τ)g₃(τ) ≠ 0` iff it vanishes at `(j, w(P))`. -/
def WeberFieldComparison : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ P : EjBar.toAffine.Point, addOrderOf P = N ∧
    ∀ F : Polynomial (Polynomial ℚ),
      (∀ τ : UpperHalfPlane, (pp τ).g₂ ≠ 0 → (pp τ).g₃ ≠ 0 → evAn N F τ = 0) ↔ evAlg F P = 0

/-- `ℚ(j)(w(P)) = ℚ(j)(x(P))`: `w` is a `ℚ(j)`-affine function of `x` with nonzero slope. -/
theorem adjoin_wOf (P : EjBar.toAffine.Point) :
    IntermediateField.adjoin Qj {wOf P} = fieldX1 P := by
  have hα : algebraMap Qj Kbar alpha ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]; exact alpha_ne_zero
  have hg : algebraMap Qj Kbar (gDS - 27) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective, gDS_sub]
    exact div_ne_zero (by norm_num) X_sub_1728_ne_zero
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hx : xCoord P ∈ fieldX1 P := IntermediateField.mem_adjoin_simple_self Qj _
    unfold wOf
    refine div_mem (add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hx)
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.algebraMap_mem _ _)
  · unfold fieldX1
    rw [IntermediateField.adjoin_simple_le_iff]
    have hw : wOf P ∈ IntermediateField.adjoin Qj {wOf P} := IntermediateField.mem_adjoin_simple_self Qj _
    have hx : xCoord P = (wOf P * algebraMap Qj Kbar (gDS - 27) - algebraMap Qj Kbar (-3 / 2)) /
        algebraMap Qj Kbar alpha := by
      unfold wOf
      field_simp
      ring
    rw [hx]
    exact div_mem (sub_mem (mul_mem hw (IntermediateField.algebraMap_mem _ _))
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.algebraMap_mem _ _)

end X1Igusa.Weber

#print axioms X1Igusa.Weber.adjoin_wOf

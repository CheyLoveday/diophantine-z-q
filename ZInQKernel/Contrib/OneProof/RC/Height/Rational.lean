import ZInQKernel.Contrib.OneProof.RC.Height.Transfer
import ZInQKernel.Contrib.OneProof.RC.Height.FieldRational

/-!
# Lane RC19 (height): functoriality `ĥ(φ P) = deg φ · ĥ(P)` for maps given by a rational function

For an isogeny `φ : E → E'` of degree `d` over a field `F`, the function `x ∘ φ` is even, so
`x(φ P) = R(x(P))` for a rational function `R = f/g` with `f, g` coprime and
`max(deg f, deg g) = d` (both `x` have degree two; Silverman, *The Arithmetic of Elliptic Curves*,
2nd ed., Chapters II and III; textbook reference, locator UNVERIFIED). On points this means:
`x(φ P) = f(x)/g(x)` when `g(x) ≠ 0`, and `φ P = O` when `g(x) = 0`; equivalently the projective
`x`-coordinates satisfy `[x(φ P) : 1] = [f(x) : g(x)]`.

This file proves **functoriality of the canonical height in degree `d`** for every additive map
with this property: `ĥ(φ P) = d ĥ(P)` (the functoriality of canonical heights, Silverman, op. cit.,
Chapter VIII, §9; Hindry–Silverman, *Diophantine Geometry*, Part B; locators UNVERIFIED). The
proof combines the height estimate for a rational map of `ℙ¹` of degree `d`
(`abs_logHeight_eval_sub_le`, `FieldRational.lean`) with the transfer principle (`Transfer.lean`).
The identification of `x ∘ φ` with a degree-`d` rational function of `x` for a given isogeny is the
textbook input (GLUE) and enters as the hypothesis `hφ`; for the 2-isogenies of `E_ℓ` it is Vélu's
formula (`TwoIsogeny.lean`), for `[n]` the division polynomials (the vendored
`canonicalHeight_zsmul` already gives `ĥ(nP) = n² ĥ(P)`).

Every declaration in this file is PROVED.

* `canonicalHeight_map_of_xRep_eval`: `ĥ(φ P) = d ĥ(P)`.
* `neronTatePairing_map_of_xRep_eval`: `⟨φ P, φ Q⟩ = d ⟨P, Q⟩`.
* `neronTatePairing_adjoint_of_xRep_eval`: with a map `ψ` such that `φ ∘ ψ = [d]` (the dual
  isogeny), `⟨φ P, Q⟩ = ⟨P, ψ Q⟩`.
-/

open Height Polynomial

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Functoriality of the canonical height for a map given by a rational function of degree `d`**:
if the projective `x`-coordinate of `φ(x, y)` is `[f(x) : g(x)]` (`f, g` coprime of degree at most
`d`, one of them of degree exactly `d`), then `ĥ(φ P) = d ĥ(P)`. PROVED. -/
theorem canonicalHeight_map_of_xRep_eval (f g : F[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hdeg : f.natDegree = d ∨ g.natDegree = d)
    (hcop : IsCoprime f g) (φ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : F) (h : W₁.toAffine.Nonsingular x y),
      ∃ c : F, c ≠ 0 ∧ (φ (Point.some x y h)).xRep = c • ![f.eval x, g.eval x])
    (P : W₁.toAffine.Point) :
    (φ P).canonicalHeight = d * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := abs_logHeight_eval_sub_le f g d hd hf hg hdeg hcop
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine canonicalHeight_map_eq_of_abs_naiveHeight_sub_le φ d C (fun Q => ?_) P
  rcases Q with _ | ⟨x, y, h⟩
  · simpa [← Point.zero_def] using hC0
  · obtain ⟨c, hc, hx⟩ := hφ x y h
    rw [Point.naiveHeight_eq_logHeight, hx, logHeight_smul_eq_logHeight _ hc, naiveHeight_some]
    exact hC x

/-- **The polarized form**: `⟨φ P, φ Q⟩ = d ⟨P, Q⟩`. PROVED. -/
theorem neronTatePairing_map_of_xRep_eval (f g : F[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hdeg : f.natDegree = d ∨ g.natDegree = d)
    (hcop : IsCoprime f g) (φ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : F) (h : W₁.toAffine.Nonsingular x y),
      ∃ c : F, c ≠ 0 ∧ (φ (Point.some x y h)).xRep = c • ![f.eval x, g.eval x])
    (P Q : W₁.toAffine.Point) :
    W₂.toAffine.neronTatePairing (φ P) (φ Q) = d * W₁.toAffine.neronTatePairing P Q :=
  neronTatePairing_map_eq_of_canonicalHeight φ d
    (canonicalHeight_map_of_xRep_eval f g d hd hf hg hdeg hcop φ hφ) P Q

/-- **The adjunction** `⟨φ P, Q⟩ = ⟨P, ψ Q⟩` for a map `φ` of degree `d` as above and a map `ψ`
with `φ ∘ ψ = [d]` (the dual isogeny). PROVED. -/
theorem neronTatePairing_adjoint_of_xRep_eval (f g : F[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hdeg : f.natDegree = d ∨ g.natDegree = d)
    (hcop : IsCoprime f g) (φ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : F) (h : W₁.toAffine.Nonsingular x y),
      ∃ c : F, c ≠ 0 ∧ (φ (Point.some x y h)).xRep = c • ![f.eval x, g.eval x])
    (ψ : W₂.toAffine.Point →+ W₁.toAffine.Point) (hφψ : ∀ Q, φ (ψ Q) = (d : ℤ) • Q)
    (P : W₁.toAffine.Point) (Q : W₂.toAffine.Point) :
    W₂.toAffine.neronTatePairing (φ P) Q = W₁.toAffine.neronTatePairing P (ψ Q) :=
  neronTatePairing_adjoint φ ψ d (by exact_mod_cast hd.ne')
    (fun P => by rw [canonicalHeight_map_of_xRep_eval f g d hd hf hg hdeg hcop φ hφ P]; norm_cast)
    hφψ P Q

end ZInQ.Manuscript.RC.Height

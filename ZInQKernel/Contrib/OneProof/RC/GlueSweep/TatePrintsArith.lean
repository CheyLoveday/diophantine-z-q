import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Bundle
import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Basic

/-!
# Lane RC22 (glue sweep), Tate share: lane RC9's Serre forms without the determinant GLUE

Lane RC9 (`RC/PrintsArith/Serre.lean`, `KatoHypV.lean`, `Bundle.lean`) derives the forms of Serre's
open image theorem used in Sections 7–8 and Appendix E of the 11/5 manuscript from the PRINT
`SerreThm3`, non-CM, and the GLUE `DetTateTwoCyclotomic E` (`det ρ₂(σ) = 1` implies that `σ` fixes
`μ_{2^∞}`). That GLUE is PROVED in the tree for every elliptic `E/ℚ`
(`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`, from the vendored Weil pairing).

The bridges below are lane RC9's statements with the determinant hypothesis removed:
* `serre_SL2_part_of` (tex 3597–3605) and `kato_hyp_v_of` (tex 7228–7231, 1887–1889), for every
  elliptic non-CM `E/ℚ`, from `SerreThm3` only;
* for the curves `E_ℓ` (`ZInQ.Contrib.CloudB3RC53.Ecurve ℓ`, `ℓ > 0`), the replacements of lane RC9's
  `ecurve_hasNoCM`, `ecurve_serre_scalar`, `ecurve_serre_SL2_part`, `ecurve_kato_hyp_v`, which take
  the uninhabitable bundle `GlueArith` (`TateGlueArith.not_glueArith`) together with the bundle
  `ArithPrints`, of which only the field `serre` is used: here they take only Serre's print
  `SerreThm3` (supplied by `P.serre` for `P : ArithPrints`) and the GLUE `CMjInteger`.

`CMjInteger` (rational CM `j`-invariants are integers; Silverman, *Advanced Topics*, II.6.1) is not
proved anywhere in the tree; it is a true statement over the vendored morphism type
`TauCeti.Isogeny.Hom` (non-unital algebra maps of the coordinate ring to the function field sending
the point at infinity to itself, i.e. `End_{ℚ̄}(E)` with the zero map), so the bridges for `E_ℓ` are
not vacuous.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53
open scoped WeierstrassCurve

/-! ### General elliptic curves -/

/-- **`Γ_d ⊆ J = ρ₂(G_{ℚ(μ_{2^∞})})` for every non-CM elliptic `E/ℚ`** (tex 3597–3605). Kind: PROVED
from `SerreThm3` (PRINT) and `HasNoCM E`. Consumer: lane RC9's `serre_SL2_part` (its hypothesis
`hdet : DetTateTwoCyclotomic E` is discharged by
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`). -/
theorem serre_SL2_part_of (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : HasNoCM E) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ α : TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2,
      LinearMap.det α.toLinearMap = 1 →
      (∀ x : TateMod E 2, ∃ y : TateMod E 2, α x = x + (2 : ℤ_[2]) ^ d • y) →
      ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧
        tateRep E 2 σ = α.toLinearMap :=
  serre_SL2_part hS E hE (DetTateCyclotomic.detTateTwoCyclotomic E)

/-- **Kato's hypothesis (v) of Theorem 13.4 for `T₂E ⊗ χ`, every non-CM elliptic `E/ℚ`**
(tex 7228–7231, 1887–1889): for every quadratic character `χ` there is `σ ∈ G_{ℚ(μ_{2^∞})}` with
`χ(σ) = 1` whose fixed module in `T₂E` has rank one. Kind: PROVED from `SerreThm3` (PRINT) and
`HasNoCM E`. Consumer: lane RC9's `kato_hyp_v` (hypothesis `hdet` discharged by
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`). -/
theorem kato_hyp_v_of (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : HasNoCM E) (χ : GalQ →* ℤˣ) :
    ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧ χ σ = 1 ∧
      Module.finrank ℤ_[2] (LinearMap.ker (tateRep E 2 σ - 1)) = 1 :=
  kato_hyp_v E hS hE (DetTateCyclotomic.detTateTwoCyclotomic E) χ

/-! ### The curves `E_ℓ` -/

/-- **`E_ℓ` has no complex multiplication** (tex 1765–1767, 1012–1013: `j = 35152/9 ∉ ℤ`). Kind:
PROVED from `CMjInteger` (GLUE). Consumer: lane RC9's `ecurve_hasNoCM`, which takes the
uninhabitable `GlueArith`; discharger: lane RC9's `curve_hasNoCM` (needs only `CMjInteger`). -/
theorem ecurve_hasNoCM_of (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    @HasNoCM (Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')

/-- **The scalar element of tex 2883–2887 for `E_ℓ`**: `ρ₂(g) = (1 + 2^n) · id` on `T₂E_ℓ` for some
`n ≥ 2`, `g ∈ G_ℚ`. Kind: PROVED from `SerreThm3` (PRINT; lane RC9's `ArithPrints.serre`) and
`CMjInteger` (GLUE). Consumer: lane RC9's `ecurve_serre_scalar` (hypotheses `P : ArithPrints`, of
which only `P.serre` is used, and `G : GlueArith`, uninhabitable, replaced by `CMjInteger`);
discharger of non-CM: `ecurve_hasNoCM_of`. -/
theorem ecurve_serre_scalar_of (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : GalQ,
      ∀ x : TateMod (Ecurve ℓ) 2, tateRep (Ecurve ℓ) 2 g x = (1 + (2 : ℤ_[2]) ^ n) • x :=
  @serre_scalar hS (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM_of hcm hℓ)

/-- **`Γ_d ⊆ J` for `E_ℓ`** (tex 3597–3605). Kind: PROVED from `SerreThm3` (PRINT; lane RC9's
`ArithPrints.serre`) and `CMjInteger` (GLUE). Consumer: lane RC9's `ecurve_serre_SL2_part`
(hypotheses `P : ArithPrints`, only `P.serre` used, and `G : GlueArith`, uninhabitable);
dischargers: `ecurve_hasNoCM_of` and
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic` (through `serre_SL2_part_of`). -/
theorem ecurve_serre_SL2_part_of (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ α : TateMod (Ecurve ℓ) 2 ≃ₗ[ℤ_[2]] TateMod (Ecurve ℓ) 2,
      LinearMap.det α.toLinearMap = 1 →
      (∀ x, ∃ y, α x = x + (2 : ℤ_[2]) ^ d • y) →
      ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧
        tateRep (Ecurve ℓ) 2 σ = α.toLinearMap :=
  @serre_SL2_part_of hS (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM_of hcm hℓ)

/-- **Kato's hypothesis (v) for `T₂E_ℓ ⊗ χ`** (tex 7228–7231). Kind: PROVED from `SerreThm3`
(PRINT; lane RC9's `ArithPrints.serre`) and `CMjInteger` (GLUE). Consumer: lane RC9's
`ecurve_kato_hyp_v` (hypotheses `P : ArithPrints`, only `P.serre` used, and `G : GlueArith`,
uninhabitable); dischargers: `ecurve_hasNoCM_of` and
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic` (through `kato_hyp_v_of`). -/
theorem ecurve_kato_hyp_v_of (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (χ : GalQ →* ℤˣ) :
    ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧ χ σ = 1 ∧
      Module.finrank ℤ_[2] (LinearMap.ker (tateRep (Ecurve ℓ) 2 σ - 1)) = 1 :=
  @kato_hyp_v_of hS (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM_of hcm hℓ) χ

end ZInQ.Manuscript.RC.GlueSweep.Tate

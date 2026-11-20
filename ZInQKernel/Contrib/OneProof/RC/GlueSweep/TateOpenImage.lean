import ZInQKernel.Contrib.CloudB3RC53.OpenImage.Basic
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrintsArith

/-!
# Lane RC22 (glue sweep), Tate share: lane RC10's open-image input for `E_ℓ`

Lane RC10 (`RC/HeegnerAlgebra/Interfaces.lean`) takes Serre's open image theorem, at tex 2881–2900
(Proposition `ex:arith-finite-heegner`, step 1), as the abstract structure `OpenImageInput G V`
consumed by `H2_assembled`. The shared top layer instantiated it over the genuine objects
(`ZInQ.Contrib.CloudB3RC53.OpenImage.openImageInput E hS hE k hk`: `G_ℚ` acting on `E[2^∞](ℚ̄)`,
the scalar from lane RC17's `serre_scalar_torsion`, an actual complex conjugation, and `G_K` of
index two) and proved (H2) there (`h2_genuine`), from `SerreThm3` and `HasNoCM E`: ALREADY
DISCHARGED IN TREE for every non-CM elliptic `E/ℚ`.

Here, for the curves `E_ℓ` actually used:
* `openImageInputEcurve` and `h2_ecurve`: the same, from `SerreThm3` (PRINT) and `CMjInteger`
  (GLUE) only, with the uniformity of the exponent in `K` made explicit
  (`openImageInputEcurve_n_eq`: `n` does not depend on `k`);
* `h2_point`, `h2_point_ecurve`: (H2) for every point of `E(ℚ̄)` killed by a power of `2`, in the
  form of the field `hH2` of lane RC10's `DerivativePrimeInput` (tex 3097–3190) for `G = G_ℚ`,
  `V = E(ℚ̄)` with the coordinatewise action.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.OpenImage
open scoped WeierstrassCurve

/-- **Lane RC10's `OpenImageInput` for `E_ℓ`, `ℓ > 0`, over the genuine objects** (tex 2881–2900):
the tree's `ZInQ.Contrib.CloudB3RC53.OpenImage.openImageInput` with non-CM supplied by
`CMjInteger`. Hypotheses:
`SerreThm3` (PRINT), `CMjInteger` (GLUE), `k` not a square (`K = ℚ(√k)`). -/
def openImageInputEcurve (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) (k : ℚ)
    (hk : ¬ IsSquare k) : OpenImageInput GalQ (TwoPowerTors (Ecurve ℓ)) :=
  @openImageInput (Ecurve ℓ) (ecurve_isElliptic hℓ) hS (ecurve_hasNoCM_of hcm hℓ) k hk

/-- The exponent `n` of `openImageInputEcurve` does not depend on the field `K = ℚ(√k)` (PROVED,
definitionally): the annihilator `2^{n+2}` of (H2) is uniform in `K` (tex 2896–2900). -/
theorem openImageInputEcurve_n_eq (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (k k' : ℚ) (hk : ¬ IsSquare k) (hk' : ¬ IsSquare k') :
    (openImageInputEcurve hS hcm hℓ k hk).n = (openImageInputEcurve hS hcm hℓ k' hk').n :=
  rfl

/-- **(H2) for `E_ℓ`** (tex 2881–2900): for `K = ℚ(√k)` and every normal `N ≤ G_ℚ` such that the
actual complex conjugation `complexConj` inverts `G_K` modulo `N` (the ring-class situation), every
point of `E_ℓ[2^∞](ℚ̄)` fixed by `N` is killed by `2^{n+2}`. Kind: PROVED from `SerreThm3` (PRINT)
and `CMjInteger` (GLUE). Consumer: lane RC10's `H2_assembled` (its input `OpenImageInput` built
by `openImageInputEcurve`); discharger: the tree's `ZInQ.Contrib.CloudB3RC53.OpenImage.h2_genuine`. -/
theorem h2_ecurve (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) (k : ℚ)
    (hk : ¬ IsSquare k) (N : Subgroup GalQ) [N.Normal]
    (hτ : ∀ x ∈ GK (exists_sqrt k).choose, complexConj * x * complexConj⁻¹ * x ∈ N)
    (P : TwoPowerTors (Ecurve ℓ)) (hP : ∀ x ∈ N, x • P = P) :
    ((2 : ℤ) ^ ((openImageInputEcurve hS hcm hℓ k hk).n + 2)) • P = 0 :=
  @h2_genuine (Ecurve ℓ) (ecurve_isElliptic hℓ) hS (ecurve_hasNoCM_of hcm hℓ) k hk N _ hτ P hP

/-- **(H2) on all of `E(ℚ̄)`** (tex 2892–2900; the field `hH2` of lane RC10's
`DerivativePrimeInput`, tex 3097–3190, for `G = G_ℚ` and `V = E(ℚ̄)` with the coordinatewise
action): for a non-CM elliptic `E/ℚ`, every point of `E(ℚ̄)` fixed by `N` and killed by some power of
`2` is killed by `2^{n+2}`. Kind: PROVED from `SerreThm3` (PRINT) and `HasNoCM E`. Discharger: the
tree's `ZInQ.Contrib.CloudB3RC53.OpenImage.h2_genuine`. -/
theorem h2_point (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : HasNoCM E)
    (k : ℚ) (hk : ¬ IsSquare k) (N : Subgroup GalQ) [N.Normal]
    (hτ : ∀ x ∈ GK (exists_sqrt k).choose, complexConj * x * complexConj⁻¹ * x ∈ N)
    (P : (E⁄Qbar).toAffine.Point)
    (hP : ∀ x ∈ N, WeierstrassCurve.Affine.Point.map x.toAlgHom P = P)
    (htors : ∃ j : ℕ, 2 ^ j • P = 0) :
    ((2 : ℤ) ^ ((openImageInput E hS hE k hk).n + 2)) • P = 0 := by
  obtain ⟨j, hj⟩ := htors
  have hmem : P ∈ AddCommGroup.primaryComponent (E⁄Qbar).toAffine.Point 2 :=
    AddCommGroup.mem_primaryComponent.mpr ⟨j, hj⟩
  have h := h2_genuine E hS hE k hk N hτ ⟨P, hmem⟩ fun x hx => Subtype.ext (hP x hx)
  have h' := congrArg Subtype.val h
  rwa [AddSubgroup.coe_zsmul, AddSubgroup.coe_zero] at h'

/-- **(H2) on all of `E_ℓ(ℚ̄)`** (tex 2892–2900, the field `hH2` of lane RC10's
`DerivativePrimeInput` for `G = G_ℚ`, `V = E_ℓ(ℚ̄)`). Kind: PROVED from `SerreThm3` (PRINT) and
`CMjInteger` (GLUE). -/
theorem h2_point_ecurve (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) (k : ℚ)
    (hk : ¬ IsSquare k) (N : Subgroup GalQ) [N.Normal]
    (hτ : ∀ x ∈ GK (exists_sqrt k).choose, complexConj * x * complexConj⁻¹ * x ∈ N)
    (P : ((Ecurve ℓ)⁄Qbar).toAffine.Point)
    (hP : ∀ x ∈ N, WeierstrassCurve.Affine.Point.map x.toAlgHom P = P)
    (htors : ∃ j : ℕ, 2 ^ j • P = 0) :
    ((2 : ℤ) ^ ((openImageInputEcurve hS hcm hℓ k hk).n + 2)) • P = 0 :=
  @h2_point hS (Ecurve ℓ) (ecurve_isElliptic hℓ) (ecurve_hasNoCM_of hcm hℓ) k hk N _ hτ P hP htors

end ZInQ.Manuscript.RC.GlueSweep.Tate

import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCurve

/-!
# Theorem 5.3, Lane RC36: quadratic descent for `E_t` at a signed parameter

The sum-and-difference step of the manuscript (`diophantine_zq.tex` lines 2616–2626, used in the
calibration's Selmer input, tex 4020–4021, and in the base-zero lemma, tex 4341–4352) compares the
full two-primary Selmer group over `K = ℚ(√k)` with the two rational Selmer groups. The RC53
group's quadratic descent (`selmerDescent`, `selmerAscent`) is constructed for any curve over `ℚ`
with `a₁ = a₃ = 0`; its specializations `SelK ℓ k`, `quadraticDescent ℓ hk` and the hypothesis
`SelmerCorankOneOverK ℓ k` are stated for `Ecurve ℓ` with `ℓ : ℕ`. This file restates them for the
family curve `E_t = curve t` with `t : ℚ` of either sign, over the same genuine objects:

* `SelKSigned t k`: `Sel_{2^∞}(E_t/ℚ(√k))`, the classes of `H¹(G_K, E_t[2^∞])` locally trivial at
  every place of `K` (the RC53 group's `selmerK`); `selKSigned_natCast`: at `t = ℓ` it is
  `SelK ℓ k`;
* `quadraticDescentSigned` (`f`, corestriction and twisted corestriction) and
  `quadraticAscentSigned` (`g`, restriction and twisted restriction) with
  `g f = [2]`, `f g = [2]` (`quadraticAscentSigned_descent`, `quadraticDescentSigned_ascent`), hence
  bounded defects (`quadraticDescentSigned_boundedDefects`);
* corank additivity in rational Tate modules: `ratTateSelKSignedEquiv` and
  `finrank_ratTate_selKSigned`, `dim V₂ Sel_{2^∞}(E_t/K) = r₁ + r₂` for coranks `r₁` of
  `Sel_{2^∞}(E_t/ℚ)` and `r₂` of `Sel_{2^∞}(E_t^{(k)}/ℚ)`;
* `SelmerCorankOneOverKSigned t k`: corank one for `E_t` and corank zero for `E_t^{(k)}`;
  `selmerCorankOneOverKSigned_natCast` (at `t = ℓ` it is `SelmerCorankOneOverK ℓ k`, by `Iff.rfl`)
  and `selmerCorankOneOverKSigned_address` (at `t = ℓ h` it is the address's own statement for
  `E^{(h)}` and `E^{(hk)}`, for `h` of either sign);
  `finrank_ratTate_selKSigned_eq_one`.

Every theorem below is PROVED and the other declarations are definitions; nothing is assumed.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.QuadraticDescent ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC.BaseZeroLimit TauCeti TauCeti.ContCohomology

/-- `a₁(E_t) = 0`. Kind: PROVED. -/
theorem curve_a₁_eq_zero (t : ℚ) : (curve t).a₁ = 0 := rfl

/-- `a₃(E_t) = 0`. Kind: PROVED. -/
theorem curve_a₃_eq_zero (t : ℚ) : (curve t).a₃ = 0 := rfl

/-- **`Sel_{2^∞}(E_t/ℚ(√k))`** for a rational parameter `t` of either sign (tex 2616–2626,
4006–4021): the classes of `H¹(G_K, E_t[2^∞])`, `K = ℚ(√k)`, whose image in `H¹(G_K, E_t)` is
locally trivial at every place of `K` (the RC53 group's genuine `selmerK`, along decomposition
groups). Kind: definition. -/
abbrev SelKSigned (t : ℚ) (k : ℤ) :
    AddSubgroup (H1 (galK (sqrtK k)) (TwoPowerCoeff (curve t))) :=
  selmerK (sqrtK k) (curve t)

/-- At a natural parameter the signed Selmer group is the RC53 group's `SelK ℓ k`, literally.
Kind: PROVED. -/
theorem selKSigned_natCast (ℓ : ℕ) (k : ℤ) : SelKSigned (ℓ : ℚ) k = SelK ℓ k := rfl

/-- **The quadratic descent map for `E_t`** (tex 2616–2626): `f : Sel_{2^∞}(E_t/K) →
Sel_{2^∞}(E_t/ℚ) × Sel_{2^∞}(E_t^{(k)}/ℚ)`, corestriction and corestriction after the twist
`E_t ≃ E_t^{(k)}` over `K` (the RC53 group's `selmerDescent` at `E = E_t`). Kind: definition. -/
def quadraticDescentSigned (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    SelKSigned t k →+ selmerTwoPower (curve t) × selmerTwoPower (qtwist (curve t) (k : ℚ)) :=
  selmerDescent (curve_a₁_eq_zero t) (curve_a₃_eq_zero t) (sqrtK_sq k) (sigmaK_not_mem hk)

/-- **The quadratic ascent map for `E_t`**: `g`, restriction and restriction followed by the
inverse twist (the RC53 group's `selmerAscent` at `E = E_t`). Kind: definition. -/
def quadraticAscentSigned (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    selmerTwoPower (curve t) × selmerTwoPower (qtwist (curve t) (k : ℚ)) →+ SelKSigned t k :=
  selmerAscent (curve_a₁_eq_zero t) (curve_a₃_eq_zero t) (sqrtK_sq k) (sigmaK_not_mem hk)

/-- **`g f = [2]`** on `Sel_{2^∞}(E_t/K)`. Kind: PROVED. -/
theorem quadraticAscentSigned_descent (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (x : SelKSigned t k) :
    quadraticAscentSigned t hk (quadraticDescentSigned t hk x) = 2 • x :=
  selmerAscent_selmerDescent (curve_a₁_eq_zero t) (curve_a₃_eq_zero t) (sqrtK_sq k)
    (sigmaK_not_mem hk) x

/-- **`f g = [2]`** on `Sel_{2^∞}(E_t/ℚ) × Sel_{2^∞}(E_t^{(k)}/ℚ)`. Kind: PROVED. -/
theorem quadraticDescentSigned_ascent (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (y : selmerTwoPower (curve t) × selmerTwoPower (qtwist (curve t) (k : ℚ))) :
    quadraticDescentSigned t hk (quadraticAscentSigned t hk y) = 2 • y :=
  selmerDescent_selmerAscent (curve_a₁_eq_zero t) (curve_a₃_eq_zero t) (sqrtK_sq k)
    (sigmaK_not_mem hk) y

/-- **The descent map has kernel and cokernel killed by `2`** (from `g f = f g = [2]`).
Kind: PROVED. -/
theorem quadraticDescentSigned_boundedDefects (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    BoundedDefects (quadraticDescentSigned t hk) :=
  boundedDefects_of_scaledInverse _ (quadraticAscentSigned t hk) 2 two_ne_zero
    (quadraticAscentSigned_descent t hk) (quadraticDescentSigned_ascent t hk)

/-- **`V₂ Sel_{2^∞}(E_t/K) ≅ V₂ Sel_{2^∞}(E_t/ℚ) × V₂ Sel_{2^∞}(E_t^{(k)}/ℚ)`**, the isomorphism
induced by the descent map itself (rational Tate modules invert maps with bounded defects).
Kind: definition. -/
def ratTateSelKSignedEquiv (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    RatTate (SelKSigned t k) ≃ₗ[ℚ_[2]]
      RatTate (selmerTwoPower (curve t)) × RatTate (selmerTwoPower (qtwist (curve t) (k : ℚ))) :=
  (ratTateEquivOfBoundedDefects _ (quadraticDescentSigned_boundedDefects t hk)).trans
    RatTate.prodEquiv

/-- **Corank additivity under the quadratic descent** (`s₂(E_t/K) = s₂(E_t/ℚ) + s₂(E_t^{(k)}/ℚ)`,
tex 2616–2626): if `Sel_{2^∞}(E_t/ℚ)` has corank `r₁` and `Sel_{2^∞}(E_t^{(k)}/ℚ)` has corank `r₂`,
the rational Tate module of `Sel_{2^∞}(E_t/ℚ(√k))` has dimension `r₁ + r₂`. Kind: PROVED. -/
theorem finrank_ratTate_selKSigned (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) {r₁ r₂ : ℕ}
    (h₁ : Z2Corank (selmerTwoPower (curve t)) r₁)
    (h₂ : Z2Corank (selmerTwoPower (qtwist (curve t) (k : ℚ))) r₂) :
    Module.finrank ℚ_[2] (RatTate (SelKSigned t k)) = r₁ + r₂ := by
  have := finiteDimensional_ratTate_prod_of_Z2Corank h₁ h₂
  rw [(ratTateSelKSignedEquiv t hk).finrank_eq, finrank_ratTate_prod_of_Z2Corank h₁ h₂]

/-- **`s₂(E_t/K) = 1`, stated over the twist, for a signed parameter** (tex 2616–2626): corank one
for `Sel_{2^∞}(E_t/ℚ)` and corank zero for `Sel_{2^∞}(E_t^{(k)}/ℚ)`. It is `SelmerCorankOneOverK`
with the curve `Ecurve ℓ` replaced by `curve t`; the Selmer group over `K` enters through the
descent (`finrank_ratTate_selKSigned_eq_one`). Kind: definition. -/
def SelmerCorankOneOverKSigned (t : ℚ) (k : ℤ) : Prop :=
  SelmerCorankOne (curve t) ∧ Z2Corank (selmerTwoPower (qtwist (curve t) (k : ℚ))) 0

/-- At a natural parameter the signed hypothesis is the original `SelmerCorankOneOverK ℓ k`,
literally. Kind: PROVED. -/
theorem selmerCorankOneOverKSigned_natCast (ℓ : ℕ) (k : ℤ) :
    SelmerCorankOneOverKSigned (ℓ : ℚ) k ↔ SelmerCorankOneOverK ℓ k :=
  Iff.rfl

/-- **The signed Selmer input is the address's own statement, for `h` of either sign**
(tex 2616–2626 for `E^{(h)}`, with the calibration's hypotheses, tex 3988–3991, and the forward
theorems at known simple zeros, tex 4020–4021): `SelmerCorankOneOverKSigned (ℓ h) k` holds exactly
when `E^{(h)}` has `2^∞`-Selmer corank one and `E^{(hk)}` has corank zero over `ℚ`. Unlike
`selmerCorankOneOverK_of_pos` there is no sign condition. Kind: PROVED. -/
theorem selmerCorankOneOverKSigned_address (ℓ : ℕ) (h k : ℤ) :
    SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k ↔
      SelmerCorankOne (Etw ℓ h) ∧ Z2Corank (selmerTwoPower (Etw ℓ (h * k))) 0 :=
  and_congr
    (ZInQ.Manuscript.RC.Wiring.z2Corank_selmerTwoPower_congr (etw_eq_curve_mul ℓ h).symm 1)
    (ZInQ.Manuscript.RC.Wiring.z2Corank_selmerTwoPower_congr (qtwist_curve_mul_eq_etw ℓ h k) 0)

/-- **Under the signed Selmer input the full Selmer group over `K = ℚ(√k)` has rational corank
one** (`finrank_ratTate_selKSigned` with `r₁ = 1`, `r₂ = 0`). Kind: PROVED. -/
theorem finrank_ratTate_selKSigned_eq_one (t : ℚ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (hSel : SelmerCorankOneOverKSigned t k) :
    Module.finrank ℚ_[2] (RatTate (SelKSigned t k)) = 1 :=
  finrank_ratTate_selKSigned t hk hSel.1 hSel.2

end ZInQ.Manuscript.RC

import ZInQKernel.Contrib.OneProof.RC.Rings.GroupRing
import ZInQKernel.Contrib.OneProof.RC.Central.EulerFactors

/-!
# Lane RC22 (glue sweep, central share): the point factor is a unit of the genuine `𝒪[G]`

Lemma `ex:arith-common-coordinate` of the 11/5 manuscript (`diophantine_zq.tex`, lines 4142–4317),
tex 4194–4205: "`𝒪[G]` is local with maximal ideal `(2, I_G)` and residue field `𝔽₂((t))` [...]
Reduction modulo `(2, I_G)` gives `ē_q = t²/(1+t)` [...] so `e_q` is a unit".

Lane RC15's `ZInQ.Manuscript.RC.Central.isUnit_pointFactor` proves that `e_q = a_q − z − z⁻¹` is a
unit over an abstract local ring `R` with a residue map `ρ` to a field of characteristic two killing
the maximal ideal: the setting of tex 4194–4197 is "carried here as the hypotheses on `R` and `ρ`"
(lane RC15's docstring). Lane RC20 has since proved that setting for the genuine ring
(`ZInQ.Manuscript.RC.Rings.isLocalRing_B`, `residueFieldBEquiv`: `𝒪[G]` is local with residue field
`𝔽₂((t))`, for the manuscript's `G = 𝔽₂^b`, lane RC7's `SignGroup b`). This file instantiates lane
RC15's lemma there, removing the hypotheses `[IsLocalRing R]` and `hρ`.

* `rhoB`: the residue map `𝒪[G] → 𝔽₂((t))`.
* `rhoB_maximalIdeal`: it kills the maximal ideal.
* `isUnit_pointFactor_genuine`: lane RC15's `isUnit_pointFactor` over the genuine `𝒪[G]`.

Every theorem in this file is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Central

open ZInQ.Manuscript.RC.Rings ZInQ.Manuscript.RC.Determinant

/-- **The residue map `ρ : 𝒪[G] → 𝔽₂((t))`** modulo the maximal ideal `(2, I_G)` (tex 4194–4197),
for the manuscript's `G = 𝔽₂^b` (lane RC7's `SignGroup b`): Mathlib's residue map of the local ring
`𝒪[G]` followed by lane RC20's identification `residueFieldBEquiv` of its residue field with
`𝔽₂((t))`. -/
def rhoB (b : ℕ) : MonoidAlgebra OO (SignGroup b) →+* LaurentSeries (ZMod 2) :=
  (residueFieldBEquiv (G := SignGroup b) signGroup_mul_self).toRingHom.comp
    (IsLocalRing.residue (MonoidAlgebra OO (SignGroup b)))

/-- **`ρ` kills the maximal ideal `(2, I_G)` of `𝒪[G]`** (tex 4194–4197; the hypothesis `hρ` of lane
RC15's `isUnit_pointFactor`). Discharger: lane RC20's `residueFieldBEquiv` (with Mathlib's residue
map). PROVED. -/
theorem rhoB_maximalIdeal (b : ℕ) :
    ∀ x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra OO (SignGroup b)), rhoB b x = 0 := by
  intro x hx
  simp only [rhoB, RingHom.coe_comp, Function.comp_apply, (IsLocalRing.residue_eq_zero_iff x).2 hx,
    map_zero]

/-- **The point factor `e_q` is a unit of the genuine `𝒪[G]`** (tex 4197–4205).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.isUnit_pointFactor`, whose setting hypotheses
`[IsLocalRing R]` and `hρ` (the setting of tex 4194–4197) are removed: here `R = 𝒪[G]` with lane
RC20's instance `instIsLocalRingBSignGroup`, the residue field `𝔽₂((t))` (characteristic two: lane
RC20's `instCharPLaurentSeriesZModTwo`) and `ρ = rhoB b`. Dischargers: lane RC20's
`isLocalRing_B`, `residueFieldBEquiv` (through `rhoB_maximalIdeal`).

PROVED, from the remaining inputs of lane RC15's lemma: `z z⁻¹ = 1`, `ρ(a_q) = 0` (`a_q` even, tex
4200–4201), `ρ(z) = 1 + t` with `t ≠ 0`, `1 + t ≠ 0` (tex 4197–4204). -/
theorem isUnit_pointFactor_genuine (b : ℕ) {a z zi : MonoidAlgebra OO (SignGroup b)}
    {t : LaurentSeries (ZMod 2)} (hz : z * zi = 1) (ha : rhoB b a = 0)
    (hzt : rhoB b z = 1 + t) (ht : 1 + t ≠ 0) (ht0 : t ≠ 0) :
    IsUnit (ZInQ.Manuscript.RC.Central.pointFactor a z zi) :=
  ZInQ.Manuscript.RC.Central.isUnit_pointFactor (rhoB b) (rhoB_maximalIdeal b) hz ha hzt ht ht0

end ZInQ.Manuscript.RC.GlueSweep.Central

import ZInQKernel.Contrib.OneProof.RC.Height.Transfer
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.Height.NumberField

/-!
# Lane RC19 (height): `ĥ = 0 ⇔ torsion` over number fields, in the forms used

The manuscript (`diophantine_zq.tex`, 11/5 version) uses the vanishing criterion of the
Néron–Tate height in both directions:

* base-zero lemma, tex 4345–4346: "The conductor-one height formula makes the specified point
  torsion when `L'(E/K,1) = 0`" (`ĥ = 0 ⇒` torsion; this needs Northcott finiteness);
* tex 2464, 8268–8272, 9439–9440: "The explicit height formula makes `P` nontorsion" (`ĥ ≠ 0 ⇒`
  nontorsion, i.e. torsion `⇒ ĥ = 0`).

The vendored canonical height proves `ĥ(P) = 0 ↔ P` torsion under a `Northcott` hypothesis for the
canonical height; over a number field that hypothesis is supplied by instances (Mathlib's
Northcott property of `logHeight₁` on a number field, transferred to the naïve and then to the
canonical height). This file states the criterion over number fields with no further hypothesis,
together with the corollaries the applications use.

Every declaration in this file is PROVED.

* `canonicalHeight_eq_zero_iff_isOfFinAddOrder'`: over a number field, `ĥ(P) = 0 ↔ P` is torsion.
* `canonicalHeight_pos_iff`: `0 < ĥ(P) ↔ P` is not torsion.
* `isOfFinAddOrder_of_canonicalHeight_eq_zero'`, `not_isOfFinAddOrder_of_canonicalHeight_ne_zero`:
  the two directions in the form of the citations above.
* `isOfFinAddOrder_of_map_isOfFinAddOrder`: torsion descends along an injective additive map
  (used to pass from a point over the Hilbert class field to the specified point over `K`).
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine

section NumberField

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K)
  [W.IsElliptic]

/-- **`ĥ = 0 ⇔ torsion` over a number field** (no hypothesis beyond ellipticity: Northcott
finiteness on a number field is an instance). PROVED. -/
theorem canonicalHeight_eq_zero_iff_isOfFinAddOrder' (P : W.toAffine.Point) :
    P.canonicalHeight = 0 ↔ IsOfFinAddOrder P :=
  Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder P

/-- **A point of height zero is torsion** (tex 4345–4346). PROVED. -/
theorem isOfFinAddOrder_of_canonicalHeight_eq_zero' {P : W.toAffine.Point}
    (h : P.canonicalHeight = 0) : IsOfFinAddOrder P :=
  (canonicalHeight_eq_zero_iff_isOfFinAddOrder' W P).mp h

/-- **A point of nonzero height is not torsion** (tex 2464, 8268–8272). PROVED. -/
theorem not_isOfFinAddOrder_of_canonicalHeight_ne_zero {P : W.toAffine.Point}
    (h : P.canonicalHeight ≠ 0) : ¬IsOfFinAddOrder P :=
  fun hP => h (Point.canonicalHeight_eq_zero_of_isOfFinAddOrder hP)

/-- **Positivity off torsion**: `0 < ĥ(P) ↔ P` is not torsion. PROVED. -/
theorem canonicalHeight_pos_iff (P : W.toAffine.Point) :
    0 < P.canonicalHeight ↔ ¬IsOfFinAddOrder P := by
  rw [← canonicalHeight_eq_zero_iff_isOfFinAddOrder' W P]
  exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Point.canonicalHeight_nonneg P) (Ne.symm h)⟩

end NumberField

/-- **Torsion descends along an injective additive map**: if `f P` is torsion and `f` is injective,
then `P` is torsion. PROVED. -/
theorem isOfFinAddOrder_of_map_isOfFinAddOrder {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Injective f) {P : G} (h : IsOfFinAddOrder (f P)) :
    IsOfFinAddOrder P := by
  obtain ⟨n, hn, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hf ?_⟩
  rw [map_nsmul, hnP, map_zero]

end ZInQ.Manuscript.RC.Height

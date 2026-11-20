import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Isogeny
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction

/-!
# The base-changed Frobenius acts on points by raising coordinates to the `q`-th power

For a Weierstrass curve `W` over a finite field `F` with `q` elements and a field homomorphism
`f : F →+* K`, the base change `π_K` of the Frobenius isogeny (`frobeniusMap W f`, Tau Ceti's
`Isogeny.map`) pulls the generic point `(x, y)` of `W_K` back to `(x^q, y^q)`
(`frobeniusMap_fieldPullback_genericX/Y`). Hence it sends a point `(a, b)` of `W_K` to
`(a^q, b^q)` (`pointMap_frobeniusMap_some`): by Tau Ceti's description of the action of a morphism
on points (`Hom.pointMap_eq_iff`), it suffices that `x^q − a^q = (x − a)^q` and `y^q − b^q` vanish
at the place of `(a, b)`, which they do since `x − a` and `y − b` do.

Classification: PROVED.
-/

noncomputable section

open Polynomial WeierstrassCurve.Affine

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)
  {K : Type*} [Field K] (f : F →+* K)

/-- **The Frobenius of `W` base-changed along `f`**, an isogeny of `W_K = W.map f`. -/
def frobeniusMap : Isogeny (W.map f) (W.map f) := (frobeniusIsogeny W).map f

/-- The base-changed Frobenius pulls `x` back to `x^q`. PROVED. -/
theorem frobeniusMap_fieldPullback_genericX :
    (frobeniusMap W f).fieldPullback (W.map f).genericX =
      (W.map f).genericX ^ Fintype.card F := by
  rw [← FunctionField.map_genericX, frobeniusMap, Isogeny.map_fieldPullback_map,
    frobeniusIsogeny_fieldPullback, map_pow]

/-- The base-changed Frobenius pulls `y` back to `y^q`. PROVED. -/
theorem frobeniusMap_fieldPullback_genericY :
    (frobeniusMap W f).fieldPullback (W.map f).genericY =
      (W.map f).genericY ^ Fintype.card F := by
  rw [← FunctionField.map_genericY, frobeniusMap, Isogeny.map_fieldPullback_map,
    frobeniusIsogeny_fieldPullback, map_pow]

/-- The `q`-power map of `K` as a ring homomorphism (Mathlib's `FiniteField.frobeniusAlgHom` for the
`F`-algebra structure given by `f`). -/
def powHom : K →+* K :=
  letI := f.toAlgebra
  (FiniteField.frobeniusAlgHom F K).toRingHom

theorem powHom_apply (a : K) : powHom f a = a ^ Fintype.card F := by
  let _ := f.toAlgebra
  exact FiniteField.frobeniusAlgHom_apply F K a

/-- The `q`-power map fixes the image of `F`. PROVED. -/
theorem powHom_comp : (powHom f).comp f = f := by
  let _ := f.toAlgebra
  ext c
  exact (FiniteField.frobeniusAlgHom F K).commutes c

/-- `W_K` is fixed by the `q`-power map (its coefficients come from `F`). PROVED. -/
theorem map_powHom : (W.map f).map (powHom f) = W.map f := by
  change WeierstrassCurve.map (WeierstrassCurve.map W f) (powHom f) = WeierstrassCurve.map W f
  rw [WeierstrassCurve.map_map, powHom_comp]

/-- **Raising the coordinates of a point of `W_K` to the `q`-th power gives a point.** PROVED. -/
theorem nonsingular_pow {a b : K} (h : (W.map f).Nonsingular a b) :
    (W.map f).Nonsingular (a ^ Fintype.card F) (b ^ Fintype.card F) := by
  have := (WeierstrassCurve.Affine.map_nonsingular (W := W.map f) (powHom f).injective a b).mpr h
  rwa [map_powHom, powHom_apply, powHom_apply] at this

/-- **The base-changed Frobenius sends `(a, b)` to `(a^q, b^q)`** (PROVED). -/
theorem pointMap_frobeniusMap_some [W.IsElliptic] [DecidableEq K] {a b : K}
    (h : (W.map f).Nonsingular a b) :
    (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap (.some a b h) =
      .some (a ^ Fintype.card F) (b ^ Fintype.card F) (nonsingular_pow W f h) := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  let _ := f.toAlgebra
  have : CharP (W.map f).FunctionField p := by
    have : CharP K p := charP_of_injective_algebraMap' F p
    exact charP_of_injective_algebraMap' K p
  have : ExpChar (W.map f).FunctionField p := ExpChar.prime hp
  rw [Isogeny.Hom.pointMap_eq_iff, Isogeny.Hom.tautologicalPoint_ofIsogeny,
    Isogeny.tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some, Point.map_some,
    Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some]
  rw [frobeniusMap_fieldPullback_genericX, frobeniusMap_fieldPullback_genericY, map_pow, map_pow,
    hcard, ← sub_pow_expChar_pow, ← sub_pow_expChar_pow, map_pow, map_pow]
  have hq : p ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  exact ⟨pow_lt_one₀ zero_le (valuation_pointPlace_genericX_sub_lt_one _ h.1) hq,
    pow_lt_one₀ zero_le (valuation_pointPlace_genericY_sub_lt_one _ h.1) hq⟩

end ZInQ.Contrib.CloudB3RC53.Frobenius

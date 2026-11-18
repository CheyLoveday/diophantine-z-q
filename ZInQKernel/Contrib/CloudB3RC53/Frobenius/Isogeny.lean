import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.AdjoinTower
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Finite.Basic

/-!
# The `q`-power Frobenius of a Weierstrass curve over a finite field, and its degree

For a Weierstrass curve `W` over a finite field `F` with `q` elements, the `q`-power map is an
`F`-algebra endomorphism of the coordinate ring (Mathlib's `FiniteField.frobeniusAlgHom`; the
coefficients of `W` lie in `F`, so `W^{(q)} = W`). Composed with the embedding into the function
field it is the pullback of an isogeny `π : W → W` in Tau Ceti's sense (`frobeniusIsogeny`): the
point at infinity goes to infinity because every coordinate function has its `q`-th power pulled
back (`CoordinatePullback.mapsInfinity_of_pow`).

* `frobeniusIsogeny`: the Frobenius isogeny, with `frobeniusIsogeny_pullback`.
* `degree_frobeniusIsogeny`: `deg π = q` (Silverman II.2.11(b)): the pullback sends the affine
  coordinate `x` to `x^q`, so `[K(W) : π^* K(W)] = [K(x) : K(x^q)]` (Tau Ceti's
  `finrank_fieldRange_of_apply_X_eq`), which is `q` by Lüroth's degree formula (Mathlib's
  `RatFunc.finrank_eq_max_natDegree`).
* `isPurelyInseparable_frobenius`, `inseparableDegree_frobeniusIsogeny`,
  `separableDegree_frobeniusIsogeny`: the extension is purely inseparable (every `z` has `z^q` in
  the image), so the separable degree is `1` and the inseparable degree is `q`.

These are the first steps towards the Frobenius characteristic polynomial (`π² − a π + q = 0`),
which `LocalFactorInert` needs at an inert prime of good reduction. Classification: PROVED.
-/

noncomputable section

open Polynomial IntermediateField

open scoped RatFunc

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)

/-- The pullback of the `q`-power Frobenius: `w ↦ w^q` followed by the embedding of the coordinate
ring into the function field. -/
def frobeniusPullback : CoordinatePullback W W :=
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    (FiniteField.frobeniusAlgHom F W.CoordinateRing)

theorem frobeniusPullback_apply (w : W.CoordinateRing) :
    frobeniusPullback W w = algebraMap W.CoordinateRing W.FunctionField w ^ Fintype.card F := by
  simp [frobeniusPullback, FiniteField.frobeniusAlgHom_apply]

/-- **The `q`-power Frobenius isogeny** `π : W → W` over a finite field with `q` elements. -/
def frobeniusIsogeny : Isogeny W W where
  pullback := frobeniusPullback W
  mapsInfinity := (frobeniusPullback W).mapsInfinity_of_pow Fintype.card_pos fun z =>
    ⟨z, frobeniusPullback_apply W z⟩

/-- The pullback of the Frobenius isogeny is the `q`-power map. PROVED. -/
theorem frobeniusIsogeny_pullback (w : W.CoordinateRing) :
    (frobeniusIsogeny W).pullback w =
      algebraMap W.CoordinateRing W.FunctionField w ^ Fintype.card F :=
  frobeniusPullback_apply W w

/-- On the function field, the Frobenius pullback is the `q`-power map. PROVED. -/
theorem frobeniusIsogeny_fieldPullback (z : W.FunctionField) :
    (frobeniusIsogeny W).fieldPullback z = z ^ Fintype.card F := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [map_div₀, Isogeny.fieldPullback_algebraMap, Isogeny.fieldPullback_algebraMap,
    frobeniusIsogeny_pullback, frobeniusIsogeny_pullback, div_pow]

/-- **`deg π = q`** (Silverman II.2.11(b)). PROVED. -/
theorem degree_frobeniusIsogeny : (frobeniusIsogeny W).degree = Fintype.card F := by
  have hX : (frobeniusIsogeny W).fieldPullback (algebraMap F[X] W.FunctionField X) =
      algebraMap (RatFunc F) W.FunctionField (RatFunc.X ^ Fintype.card F) := by
    rw [frobeniusIsogeny_fieldPullback, map_pow, ← RatFunc.algebraMap_X,
      ← IsScalarTower.algebraMap_apply]
  rw [Isogeny.degree_def, WeierstrassCurve.Affine.finrank_fieldRange_of_apply_X_eq W _ hX]
  have h := RatFunc.finrank_eq_max_natDegree (K := F) (f := RatFunc.X ^ Fintype.card F)
  rw [h]
  have hn : (RatFunc.X ^ Fintype.card F : RatFunc F).num = X ^ Fintype.card F := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.num_algebraMap]
  have hd : (RatFunc.X ^ Fintype.card F : RatFunc F).denom = 1 := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.denom_algebraMap]
  rw [hn, hd, natDegree_X_pow, natDegree_one, Nat.max_zero]

/-- **The Frobenius extension is purely inseparable**: every element of the function field has its
`q`-th power in the pulled-back copy. PROVED. -/
theorem isPurelyInseparable_frobenius :
    IsPurelyInseparable (frobeniusIsogeny W).fieldPullback.fieldRange W.FunctionField := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP W.FunctionField p := charP_of_injective_algebraMap' F p
  have : CharP (frobeniusIsogeny W).fieldPullback.fieldRange p :=
    charP_of_injective_algebraMap' F p
  have : ExpChar (frobeniusIsogeny W).fieldPullback.fieldRange p := ExpChar.prime hp
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  refine ⟨n, ⟨⟨x ^ p ^ (n : ℕ), ⟨x, ?_⟩⟩, rfl⟩⟩
  change (frobeniusIsogeny W).fieldPullback x = _
  rw [frobeniusIsogeny_fieldPullback, hcard]

/-- **The Frobenius isogeny has separable degree `1`.** PROVED. -/
theorem separableDegree_frobeniusIsogeny : (frobeniusIsogeny W).separableDegree = 1 := by
  have := isPurelyInseparable_frobenius W
  exact Isogeny.separableDegree_eq_one_of_isPurelyInseparable _

/-- **The Frobenius isogeny has inseparable degree `q`.** PROVED. -/
theorem inseparableDegree_frobeniusIsogeny :
    (frobeniusIsogeny W).inseparableDegree = Fintype.card F := by
  have := isPurelyInseparable_frobenius W
  rw [Isogeny.inseparableDegree_eq_degree_of_isPurelyInseparable, degree_frobeniusIsogeny]

end ZInQ.Contrib.CloudB3RC53.Frobenius

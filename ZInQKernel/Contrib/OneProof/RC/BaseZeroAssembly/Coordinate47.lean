import ZInQKernel.Contrib.OneProof.RC.Wiring.Uniform
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaHalfCoeff
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaT

/-!
# Lane RC25 (base zero), part 1: (4.7) at the base, and the corrected coordinate at the base

Lemma `ex:arith-base-zero` (`diophantine_zq.tex`, 11/5 version, tex 4330–4376), last step
(tex 4369–4373):

> Finally `ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ Λ^×` by Lemma `ex:arith-common-coordinate`, so the
> corrected coordinate is also regular and zero at the center.

and the identification used by the final contradiction (Proposition
`ex:limits-coefficient-transfer`, tex 5703–5706):

> Both `ũ_x` and `ũ₀` lie in `Λ[1/2]` by the height-one argument above, so neither has negative
> powers of `t`.

The base-zero model of lane RC0 (`Wiring.BaseZeroModelCST`) carries, besides the two-term model
over `A = Λ_(t)` and its generic coordinate `u_{prim,0} ∈ F = Frac Λ`, six further fields for this
step: the unit `ε₀ ∈ A`, the corrected coordinate `ũ₀ ∈ F`, the identity (4.7) at the base
`ũ₀ = ε₀ u_{prim,0}`, an element `w ∈ Λ[1/2]` with `w = ũ₀` in `F`, and the identification of the
package's datum `ũ₀(0)` with `w(0)`. This file derives all six from:

* (4.7) at the base character `x = 0` as the wiring already proves it, `CommonCoordinateTarget D`
  (lane RC15's `corrected_eq`, the inputs `CommonCoordinateInputs D` with batch 3's support-triangle
  models): `ũ₀ = ε u_{prim,0}` in `ℚ₂[[t]]` with `ε ∈ Λ^×` — exactly the text's appeal to Lemma
  `ex:arith-common-coordinate`;
* height-one regularity at the base as the wiring already proves it, `HeightOneTarget D` (lane RC16,
  tex 5703–5704): `ũ₀ ∈ Λ[1/2]`;
* the interface identification `IsTExpansion u_{prim,0} (D.uPrim F 0)` (lane RC0's definition, the
  same as the first conjunct of `PrimRegularityInputs`): the interface's power series `u_{prim,0}`
  is the `t`-expansion of the generic coordinate of the base model.

Kinds: every declaration here is `PROVED`.

* `IsTExpansion.mul`, `isTExpansion_lambdaHalfToFrac`, `isTExpansion_algebraMap_lambdaT`: products,
  `Λ[1/2]` and `Λ` under `t`-expansion.
* `isUnit_algebraMap_lambdaT`: a unit of `Λ` stays a unit in `Λ_(t)` (`ε₀ ∈ Λ^× ⊂ A^×`).
* `coord_regular`: the primitive coordinate at the base is regular at `(t)` (tex 4335–4336, by
  lane RC15's `coord_specializes`; no vanishing hypothesis is needed).
* `baseTail_of_targets`: the six fields of the corrected coordinate at the base.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings
  ZInQ.Manuscript.RC.Wiring
open Matrix

/-! ## `t`-expansions -/

/-- **`t`-expansions multiply** (PROVED): if `U` is the `t`-expansion of `u` and `V` that of `v`,
then `U V` is the `t`-expansion of `u v`. -/
theorem IsTExpansion.mul {u v : FractionRing Lambda} {U V : PowerSeries ℚ_[2]}
    (hu : IsTExpansion u U) (hv : IsTExpansion v V) : IsTExpansion (u * v) (U * V) := by
  obtain ⟨a, b, hb, hub, hUb⟩ := hu
  obtain ⟨c, d, hd, hvd, hVd⟩ := hv
  refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
  · rw [map_mul, map_mul, ← hub, ← hvd]
    ring
  · rw [map_mul, map_mul, ← hUb, ← hVd]
    ring

/-- **The `t`-expansion of an element of `Λ[1/2]`** is its power series (PROVED; tex 5703–5704,
"neither has negative powers of `t`"): `halfToPowerSeries w` is the `t`-expansion of the image of
`w` in `Frac Λ`. -/
theorem isTExpansion_lambdaHalfToFrac (w : LambdaHalf) :
    IsTExpansion (lambdaHalfToFrac w) (halfToPowerSeries w) := by
  obtain ⟨f, m, hf⟩ := exists_mul_two_pow_eq w
  refine ⟨f, 2 ^ m, pow_ne_zero _ prime_two_lambda.ne_zero, ?_, ?_⟩
  · have := congrArg lambdaHalfToFrac hf
    rwa [map_mul, AlgHom.commutes, AlgHom.commutes] at this
  · have := congrArg halfToPowerSeries hf
    rwa [map_mul, halfToPowerSeries_algebraMap, halfToPowerSeries_algebraMap] at this

/-- `Λ → Λ_(t) → Frac Λ` is the canonical map (PROVED). -/
theorem algebraMap_lambdaT_lambda (f : Lambda) :
    algebraMap LambdaT (FractionRing Lambda) (algebraMap Lambda LambdaT f) =
      algebraMap Lambda (FractionRing Lambda) f :=
  (IsScalarTower.algebraMap_apply Lambda LambdaT (FractionRing Lambda) f).symm

/-- **The `t`-expansion of an element of `Λ ⊂ Λ_(t)`** is its image in `ℚ₂[[t]]` (PROVED). -/
theorem isTExpansion_algebraMap_lambdaT (f : Lambda) :
    IsTExpansion (algebraMap LambdaT (FractionRing Lambda) (algebraMap Lambda LambdaT f))
      (lamIncl f) := by
  rw [algebraMap_lambdaT_lambda]
  exact isTExpansion_algebraMap f

/-- **`Λ^× ⊂ Λ_(t)^×`** (PROVED): the image in `A = Λ_(t)` of a unit of `Λ` is a unit, so the
`ε₀` of (4.7) at the base is a unit of `A` (the text's `ε₀ ∈ Λ^×`, tex 4370–4371). -/
theorem isUnit_algebraMap_lambdaT (e : Lambdaˣ) : IsUnit (algebraMap Lambda LambdaT (e : Lambda)) :=
  e.isUnit.map _

/-- `InLamHalf U` gives a genuine element of `Λ[1/2]` with power series `U` (PROVED; lane RC20's
`mem_range_halfToPowerSeries_iff`). -/
theorem exists_lambdaHalf_of_inLamHalf {U : PowerSeries ℚ_[2]} (hU : InLamHalf U) :
    ∃ w : LambdaHalf, halfToPowerSeries w = U := by
  obtain ⟨e, g, hg⟩ := hU
  exact (mem_range_halfToPowerSeries_iff U).mpr ⟨e, InLamHalf.norm_coeff_le hg⟩

/-! ## Regularity of the primitive coordinate at the base -/

/-- **The primitive coordinate at the base is regular at `(t)`** (tex 4335–4336: "The primitive
coordinate is regular at `(t)` by the local argument below"; the argument is tex 4362–4369). Over a
DVR `A` with fraction field `F` and a residue map `ρ` killing the maximal ideal, a two-term model
`[A^{m+1} --D--> A^{m+1}]` with central dimensions `(1,1)` (`rank D̄ = m`), an integral cycle `z`
and an integral functional `w`: the generic coordinate `u_prim` lies in `A`, and its residue is
the coordinate of the central tensor. No vanishing of the central cycle is used. PROVED (lane
RC15's `coord_specializes` with `adjugate_ne_zero_of_rank`). -/
theorem coord_regular {A F k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field k] (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (uprim : F)
    (hu : Central.IsClassFunctionalCoord (D.map (algebraMap A F)) (fun i => algebraMap A F (z i))
      (fun i => algebraMap A F (w i)) uprim) :
    ∃ u₀ : A, algebraMap A F u₀ = uprim ∧
      Central.IsClassFunctionalCoord (D.map ρ) (fun i => ρ (z i)) (fun i => ρ (w i)) (ρ u₀) :=
  Central.coord_specializes (algebraMap A F) (IsFractionRing.injective A F) ρ hρ D z w uprim hu
    (Central.adjugate_ne_zero_of_rank _ hcentral)

/-! ## (4.7) at the base and the corrected coordinate -/

/-- **(4.7) at the base, and the corrected coordinate at the base** (tex 4369–4373 and
5703–5706). Let `u_{prim,0} ∈ F = Frac Λ` be the generic coordinate of the base model, whose
`t`-expansion is the interface's `D.uPrim F 0` (`hT`, definition). Suppose (4.7) holds at the base
character, `ũ₀ = ε u_{prim,0}` with `ε ∈ Λ^×` in `ℚ₂[[t]]` (`h47`, Lemma
`ex:arith-common-coordinate` at `x = 0`), and `ũ₀ ∈ Λ[1/2]` (`hhalf`, height-one regularity at the
base, tex 5703–5704). Then there are `ε₀ ∈ Λ_(t)` and `w ∈ Λ[1/2]` with

* `ε₀` a unit of `Λ_(t)` (it comes from `Λ^×`);
* `w = ε₀ u_{prim,0}` in `F`: the corrected coordinate `ũ₀ := ε₀ u_{prim,0}` of the base model lies
  in `Λ[1/2]` (the fields `eps0`, `utilde0`, `h47`, `wHalf`, `hwHalf` of `BaseZeroModelCST`);
* `ũ₀(0) = w(0)`: the package's datum is the central value of `w` (the field `hC`);
* the `t`-expansion of `ε₀ u_{prim,0}` is the interface's `D.uTilde F 0`.

PROVED. -/
theorem baseTail_of_targets {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} (uprim : FractionRing Lambda)
    (hT : IsTExpansion uprim (D.uPrim Fam 0))
    (h47 : ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde Fam 0 = ε * D.uPrim Fam 0)
    (hhalf : InLamHalf (D.uTilde Fam 0)) :
    ∃ (eps0 : LambdaT) (wHalf : LambdaHalf), IsUnit eps0 ∧
      lambdaHalfToFrac wHalf = algebraMap LambdaT (FractionRing Lambda) eps0 * uprim ∧
      central (D.uTilde Fam 0) = centralSpecialization wHalf ∧
      IsTExpansion (algebraMap LambdaT (FractionRing Lambda) eps0 * uprim) (D.uTilde Fam 0) := by
  obtain ⟨ε, ⟨e, rfl⟩, hε⟩ := h47
  obtain ⟨w, hw⟩ := exists_lambdaHalf_of_inLamHalf hhalf
  have hTε : IsTExpansion
      (algebraMap LambdaT (FractionRing Lambda) (algebraMap Lambda LambdaT (e : Lambda)) * uprim)
      (D.uTilde Fam 0) := by
    rw [hε]
    exact IsTExpansion.mul (isTExpansion_algebraMap_lambdaT (e : Lambda)) hT
  have hTw : IsTExpansion (lambdaHalfToFrac w) (D.uTilde Fam 0) := by
    rw [← hw]
    exact isTExpansion_lambdaHalfToFrac w
  exact ⟨algebraMap Lambda LambdaT (e : Lambda), w, isUnit_algebraMap_lambdaT e,
    IsTExpansion.unique_left hTw hTε, hTw.central_eq, hTε⟩

end ZInQ.Manuscript.RC.BaseZeroAssembly

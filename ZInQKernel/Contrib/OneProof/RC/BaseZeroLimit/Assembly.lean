import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Boundary
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Central
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly

/-!
# Lane RC30 (base zero), part 4: the base-zero leaf with `hlim` and `hcentral` replaced

Lane RC25's leaf `BaseZeroAssembly.BaseZeroLeafInputs D` (`RC/BaseZeroAssembly/Assembly.lean`)
asks, under the hypotheses of Lemma `ex:arith-base-zero` (tex 4330–4376), for a
`BaseZeroLeafModel D F` at every final family; its core `BaseZeroCore D F P` has two ELLIOT fields
that lane RC30 replaces:

| field of `BaseZeroCore` | before (kind) | after | tex |
|---|---|---|---|
| `boundary : Boundary45Base P (m+1) z̄` (its field `hlim : z̄ = lim_i L κ(W_i)`) | ELLIOT `hlim` | `limit : InnerLimit45Base P (m+1) z̄`: the retained stage boundaries (4.5), PROVED per stage from lane RC25's `boundary45_finite` (`InnerLimit45Base.ofStages`), the inner limit (PROVED, lane RC6), and the central comparison (definition); `hlim` is the theorem `InnerLimit45Base.hlim`, the field the bridge `InnerLimit45Base.toBoundary45Base` | 3912–3921, 3952–3968, 4401–4406, 4444–4450 |
| `hcentral : rank ρ(Dm) = m` | ELLIOT | `central : CentralSelmerComparison (Sel_{2^∞}(E/ℚ)) (Sel_{2^∞}(E^{(k)}/ℚ)) Dm` (the central degree-one cohomology is `V₂Sel(E/ℚ) × V₂Sel(E^{(k)}/ℚ)`; ELLIOT + GLUE) with the lemma's own hypothesis `SelmerCorankOneOverK ℓ k`; `hcentral` is the theorem `hcentral_of_selmer` (the corank count PROVED, `RationalTate.lean`) | 4350–4352, 3952–3962, 5305–5311 |

All other fields are verbatim. PROVED:

* `BaseZeroCoreLimit.toCore`: `SelmerCorankOneOverK ℓ D.kfin → BaseZeroCoreLimit D F P →
  BaseZeroCore D F P` (the two bridges);
* `BaseZeroLeafModelLimit.toLeafModel`, `baseZeroLeafInputs_of_limit :
  BaseZeroLeafInputsLimit D → BaseZeroLeafInputs D` (lane RC25's leaf, consumed unchanged by
  `baseZeroInputsCST_of_leaves` and `baseZeroTarget_of_leaves`);
* `baseZeroTarget_of_limit_leaves : Prints → CommonCoordinateInputs D → PrimRegularityInputs D →
  BaseZeroLeafInputsLimit D → BaseZeroTarget D`.

The hypothesis `SelmerCorankOneOverK ℓ D.kfin` used by `toCore` is the first premise of
`BaseZeroLeafInputs` itself, so the leaf bridge needs nothing new.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings
  ZInQ.Manuscript.RC.BaseZeroAssembly
open Matrix

/-- **The base-zero core with the inner limit and the central comparison** (tex 4330–4376), for a
specified point `P : G`. Fields, with tex lines and kinds:

* `m`, `Dm`, `z`, `hz`, `CU`, `e1`, `e2`, `hd`, `lam`, `hlam`, `uprim`, `hu`, `hprimId`: verbatim
  from lane RC25's `BaseZeroCore` (the two-term model of the primitive complex at the base over
  `A = Λ_(t)`, its retained cycle, the closed paired functional, the generic coordinate and its
  `t`-expansion; tex 3877–3892, 4341–4369; ELLIOT + GLUE + definition, unchanged);
* `central` (replaces `hcentral`): the central degree-one cohomology `ker ρ(Dm)` is
  `V₂ Sel_{2^∞}(E/ℚ) × V₂ Sel_{2^∞}(E^{(k)}/ℚ)` (`CentralSelmerComparison`; tex 4350–4352 with
  3952–3962 and 5305–5311; ELLIOT + GLUE);
* `limit` (replaces `boundary`): the retained inner-limit data of (4.5) for the central cycle
  `z̄ = ρ(z)` (`InnerLimit45Base`; tex 3912–3921, 3952–3968; the stage boundaries ELLIOT and
  PROVED per stage from `boundary45_finite`, the limit PROVED, the comparison definitions). -/
structure BaseZeroCoreLimit {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) : Type 1 where
  /-- the rank of the two-term model -/
  m : ℕ
  /-- the differential of the two-term model, over `A = Λ_(t)` -/
  Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT
  /-- the central degree-one cohomology is the rational full Selmer group -/
  central : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ D.kfin)) Dm
  /-- the retained integral cycle -/
  z : Fin (m + 1) → Rings.LambdaT
  /-- it is a cycle -/
  hz : Dm *ᵥ z = 0
  /-- the complex of the model -/
  CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  /-- degree one is `A^{m+1}` -/
  e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- degree two is `A^{m+1}` -/
  e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- in these coordinates the differential is `Dm` -/
  hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y
  /-- the paired functional -/
  lam : CU.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT
  /-- it is closed -/
  hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0
  /-- the generic class-functional coordinate, in `F = Frac Λ` -/
  uprim : FractionRing Uniform.Lambda
  /-- it is the coordinate of `[z] ⊗ [λ_z]` -/
  hu : ∀ w : Fin (m + 1) → Rings.LambdaT, w ᵥ* Dm = 0 →
    (∀ y, lam (e2.symm y) = w ⬝ᵥ y) →
    Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (z i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (w i)) uprim
  /-- the retained inner-limit data of (4.5) at the base -/
  limit : InnerLimit45Base P (m + 1) (fun i => Rings.rhoT (z i))
  /-- the interface's `u_{prim,0}` is the `t`-expansion of the generic coordinate -/
  hprimId : IsTExpansion uprim (D.uPrim Fam 0)

/-- **Bridge to lane RC25's `BaseZeroCore`** (tex 4330–4376): under full two-primary Selmer
corank one for `E/K` (`SelmerCorankOneOverK ℓ D.kfin`, the lemma's hypothesis), `hcentral` is
`hcentral_of_selmer` and `boundary` is `InnerLimit45Base.toBoundary45Base`; every other field is
copied. PROVED. -/
def BaseZeroCoreLimit.toCore {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {G : Type} [AddCommGroup G]
    {P : G} (M : BaseZeroCoreLimit D Fam P) (hSel : SelmerCorankOneOverK ℓ D.kfin) :
    BaseZeroCore D Fam P where
  m := M.m
  Dm := M.Dm
  hcentral := hcentral_of_selmer hSel M.central
  z := M.z
  hz := M.hz
  CU := M.CU
  e1 := M.e1
  e2 := M.e2
  hd := M.hd
  lam := M.lam
  hlam := M.hlam
  uprim := M.uprim
  hu := M.hu
  boundary := M.limit.toBoundary45Base
  hprimId := M.hprimId

/-- The bridged core keeps the model and the central cycle. PROVED. -/
theorem BaseZeroCoreLimit.toCore_z {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {G : Type}
    [AddCommGroup G] {P : G} (M : BaseZeroCoreLimit D Fam P)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) :
    (M.toCore hSel).m = M.m ∧ (M.toCore hSel).uprim = M.uprim :=
  ⟨rfl, rfl⟩

/-- **The base-zero leaf model with the inner limit and the central comparison** (tex
4330–4376): the conductor-one Heegner data of lane RC25's `BaseZeroLeafModel` (verbatim:
definition + GLUE) and a `BaseZeroCoreLimit` for the specified point. -/
structure BaseZeroLeafModelLimit {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
  /-- `E_ℓ` is elliptic (`ℓ ≠ 0`) -/
  hE : (Ecurve ℓ).IsElliptic
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  /-- the conductor-one Heegner point -/
  P : ((Ecurve ℓ).baseChange K).toAffine.Point
  /-- its Heegner data -/
  heegner : HeegnerData (Ecurve ℓ) hE (D.kfin : ℚ) K P
  /-- the model at the base -/
  core : BaseZeroCoreLimit D Fam P

attribute [instance] BaseZeroLeafModelLimit.fieldK BaseZeroLeafModelLimit.nfK
  BaseZeroLeafModelLimit.decK

/-- **Bridge to lane RC25's `BaseZeroLeafModel`** (PROVED). -/
def BaseZeroLeafModelLimit.toLeafModel {ℓ : ℕ} {D : RCData ℓ} {Fam : Family}
    (M : BaseZeroLeafModelLimit D Fam) (hSel : SelmerCorankOneOverK ℓ D.kfin) :
    BaseZeroLeafModel D Fam where
  hE := M.hE
  K := M.K
  P := M.P
  heegner := M.heegner
  core := M.core.toCore hSel

/-- **The base-zero leaf inputs with the inner limit and the central comparison** (Lemma
`ex:arith-base-zero`, tex 4330–4376): lane RC25's `BaseZeroLeafInputs` with
`BaseZeroLeafModelLimit` in place of `BaseZeroLeafModel`. -/
def BaseZeroLeafInputsLimit {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroLeafModelLimit D F)

/-- **Bridge to lane RC25's leaf: `BaseZeroLeafInputs D` from `BaseZeroLeafInputsLimit D`**
(tex 4330–4376). The Selmer hypothesis used by the bridge is the leaf's own first premise.
PROVED. -/
theorem baseZeroLeafInputs_of_limit {ℓ : ℕ} {D : RCData ℓ} (h : BaseZeroLeafInputsLimit D) :
    BaseZeroLeafInputs D := fun hSel hk Co Ce F hF =>
  (h hSel hk Co Ce F hF).map fun M => M.toLeafModel hSel

/-- **`RCSteps.base_zero` from the leaves, with `hlim` and `hcentral` replaced** (tex 4330–4376):
`Prints`, the existing leaves `CommonCoordinateInputs D`, `PrimRegularityInputs D`, and
`BaseZeroLeafInputsLimit D`. PROVED (lane RC25's `baseZeroTarget_of_leaves`). -/
theorem baseZeroTarget_of_limit_leaves {ℓ : ℕ} {D : RCData ℓ} (P : Prints)
    (hcc : CommonCoordinateInputs D) (hpr : PrimRegularityInputs D)
    (h : BaseZeroLeafInputsLimit D) : BaseZeroTarget D :=
  baseZeroTarget_of_leaves P hcc hpr (baseZeroLeafInputs_of_limit h)

/-- **`BaseZeroInputsCST D` from the base-character inputs and the new leaf** (lane RC25's
`baseZeroInputsCST_of_base`). PROVED. -/
theorem baseZeroInputsCST_of_limit {ℓ : ℕ} {D : RCData ℓ} (hb : BaseCharacterInputs D)
    (h : BaseZeroLeafInputsLimit D) : BaseZeroInputsCST D :=
  baseZeroInputsCST_of_base hb (baseZeroLeafInputs_of_limit h)

end ZInQ.Manuscript.RC.BaseZeroLimit

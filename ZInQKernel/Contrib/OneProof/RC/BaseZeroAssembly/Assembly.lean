import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Coordinate47
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Boundary45
import ZInQKernel.Contrib.OneProof.RC.Wiring.Height

/-!
# Lane RC25 (base zero), part 3: `BaseZeroInputsCST D` from smaller inputs

Lane RC0's base-zero input (`Wiring.BaseZeroInputsCST D`, `RC/Wiring/Height.lean`) asks, under the
hypotheses of Lemma `ex:arith-base-zero` on the companion (tex 4330–4376), for a
`Wiring.BaseZeroModelCST D F` at every final family. Its fields are:

* the conductor-one Heegner data (`hE`, `K`, `P`, `heegner`);
* the two-term model over `A = Λ_(t)` (`m`, `Dm`, `hcentral`, `z`, `hz`, `CU`, `e1`, `e2`, `hd`),
  the closed functional (`lam`, `hlam`) and the generic coordinate (`uprim`, `hu`);
* (4.5) at the base (`kappa`, `Lm`, `h45`);
* (4.7) at the base (`eps0`, `utilde0`, `h47`), height-one regularity at the base (`wHalf`,
  `hwHalf`) and the identification of the package's datum (`hC`).

`BaseZeroLeafModel D F` keeps the first two groups unchanged and replaces the last two:

| field of `BaseZeroModelCST` | replaced by | tex | kind of what remains |
|---|---|---|---|
| `kappa`, `Lm`, `h45` | `core.boundary : Boundary45Base P (m+1) z̄` (finite stages with (4.1), the fixed `L`, the central Kummer comparison, the limit at the centre); `h45` is `Boundary45Base.h45` | 3895–3921, 3961–3968, 4345–4348 | PRINT (4.1) per stage + definitions + ELLIOT (the limit, `hlim`) |
| `eps0`, `utilde0`, `h47` | **nothing**: (4.7) at `x = 0` is the wiring's `CommonCoordinateTarget D` (`baseTail_of_targets`) | 4369–4373 | PROVED (from the existing leaf `common_coordinate`) |
| `wHalf`, `hwHalf` | **nothing**: `HeightOneTarget D` at `x = 0` | 5703–5704 | PROVED (from the existing leaves `prim_regular`, `common_coordinate`) |
| `hC` | **nothing** (`IsTExpansion.central_eq`) | 5703–5706 | PROVED |
| — | `core.hprimId : IsTExpansion uprim (D.uPrim F 0)` | 3877–3892 | definition (lane RC0's interface identification, as in `PrimRegularityInputs`) |

`BaseZeroLeafInputs D` is `BaseZeroInputsCST D` with `BaseZeroLeafModel` in place of
`BaseZeroModelCST`. PROVED:

* `BaseZeroLeafModel.nonempty_modelCST`: a leaf model, (4.7) at the base and `ũ₀ ∈ Λ[1/2]` give a
  `BaseZeroModelCST`;
* `baseZeroInputsCST_of_leaf : CommonCoordinateTarget D → HeightOneTarget D →
  BaseZeroLeafInputs D → BaseZeroInputsCST D`;
* `baseZeroInputsCST_of_leaves`: the same from the leaves `CommonCoordinateInputs D` and
  `PrimRegularityInputs D` that `Wiring.PostLeaves` already contains;
* `baseZeroTarget_of_leaves : Prints → CommonCoordinateInputs D → PrimRegularityInputs D →
  BaseZeroLeafInputs D → BaseZeroTarget D` (through lane RC0's `baseZeroTarget_of_inputs` and
  `baseZeroInputs_of_CST`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings
open Matrix

/-- **The base-zero model without the Heegner data** (tex 4330–4376), for a specified point
`P : G`. Fields, with tex lines and kinds:

* `m`, `Dm`, `hcentral`, `z`, `hz`, `CU`, `e1`, `e2`, `hd`, `lam`, `hlam`, `uprim`, `hu`: as in
  `Wiring.BaseZeroModelCST` (the two-term model of the primitive complex at the base over
  `A = Λ_(t)` with central dimensions `(1,1)`, its retained cycle, the closed paired functional and
  the generic coordinate; tex 3877–3892, 4341–4369; ELLIOT + GLUE + definition, lanes RC15 / RC7 /
  batch 3, unchanged);
* `boundary`: the inputs of (4.5) at the base for the central cycle `z̄ = ρ(z)`
  (`Boundary45Base`; tex 3895–3921, 3961–3968; PRINT (4.1) per stage, definitions, ELLIOT `hlim`);
* `hprimId`: the interface's `u_{prim,0} ∈ ℚ₂[[t]]` is the `t`-expansion of the generic
  coordinate (tex 3877–3892; definition: lane RC0's `IsTExpansion`, the identification already
  used by `PrimRegularityInputs`). -/
structure BaseZeroCore {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) : Type 1 where
  /-- the rank of the two-term model -/
  m : ℕ
  /-- the differential of the two-term model, over `A = Λ_(t)` -/
  Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT
  /-- central dimensions `(1,1)` -/
  hcentral : (Dm.map Rings.rhoT).rank = m
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
  /-- the inputs of the retained boundary (4.5) at the base -/
  boundary : Boundary45Base P (m + 1) (fun i => Rings.rhoT (z i))
  /-- the interface's `u_{prim,0}` is the `t`-expansion of the generic coordinate -/
  hprimId : IsTExpansion uprim (D.uPrim Fam 0)

/-- **The base-zero leaf model** (tex 4330–4376): the conductor-one Heegner data of
`Wiring.BaseZeroModelCST` (`hE`, `K`, `P`, `heegner`; definition + GLUE, lanes RC19 / batch 3) and a
`BaseZeroCore` for the specified point `P`. -/
structure BaseZeroLeafModel {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
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
  core : BaseZeroCore D Fam P

attribute [instance] BaseZeroLeafModel.fieldK BaseZeroLeafModel.nfK BaseZeroLeafModel.decK

/-- **A `BaseZeroModelCST` from a leaf model, (4.7) at the base and `ũ₀ ∈ Λ[1/2]`** (tex
4330–4376, 5703–5706). The fields `kappa`, `Lm`, `h45` come from `Boundary45Base.h45`; `eps0`,
`utilde0`, `h47`, `wHalf`, `hwHalf`, `hC` from `baseTail_of_targets`. PROVED. -/
theorem BaseZeroLeafModel.nonempty_modelCST {ℓ : ℕ} {D : RCData ℓ} {Fam : Family}
    (M : BaseZeroLeafModel D Fam)
    (h47 : ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde Fam 0 = ε * D.uPrim Fam 0)
    (hhalf : InLamHalf (D.uTilde Fam 0)) : Nonempty (BaseZeroModelCST D Fam) := by
  obtain ⟨eps0, wHalf, -, hw, hC, -⟩ := baseTail_of_targets M.core.uprim M.core.hprimId h47 hhalf
  obtain ⟨kappa, h45⟩ := M.core.boundary.h45
  exact ⟨{
    hE := M.hE
    K := M.K
    P := M.P
    heegner := M.heegner
    m := M.core.m
    Dm := M.core.Dm
    hcentral := M.core.hcentral
    z := M.core.z
    hz := M.core.hz
    CU := M.core.CU
    e1 := M.core.e1
    e2 := M.core.e2
    hd := M.core.hd
    lam := M.core.lam
    hlam := M.core.hlam
    uprim := M.core.uprim
    hu := M.core.hu
    kappa := kappa
    Lm := M.core.boundary.L
    h45 := h45
    eps0 := eps0
    utilde0 := algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) eps0 * M.core.uprim
    h47 := rfl
    wHalf := wHalf
    hwHalf := hw
    hC := hC }⟩

/-- **The base-zero leaf inputs** (Lemma `ex:arith-base-zero`, tex 4330–4376): under the lemma's
hypotheses on the companion (`s₂(E/K) = 1` and `L(E^{(k)},1) ≠ 0`), every final family has a
`BaseZeroLeafModel`. As for `BaseZeroInputsCST`, the model may depend on these two hypotheses but
not on `L'(E/K,1) = 0`, which enters only through the Heegner data (the height formula). -/
def BaseZeroLeafInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroLeafModel D F)

/-- **`BaseZeroInputsCST D` from the leaf inputs, (4.7) and height-one regularity** (tex
4330–4376, 4369–4373, 5703–5706). PROVED. -/
theorem baseZeroInputsCST_of_leaf {ℓ : ℕ} {D : RCData ℓ} (h47 : CommonCoordinateTarget D)
    (hheight : HeightOneTarget D) (h : BaseZeroLeafInputs D) : BaseZeroInputsCST D := by
  intro hSel hk Co Ce F hF
  obtain ⟨M⟩ := h hSel hk Co Ce F hF
  exact M.nonempty_modelCST (h47 Co Ce F hF 0) (hheight Co Ce F hF 0)

/-- **`BaseZeroInputsCST D` from leaves already in `Wiring.PostLeaves`** (`common_coordinate`,
`prim_regular`) and the base-zero leaf inputs: lane RC15's `corrected_eq`
(`commonCoordinateTarget_of_inputs`) and lane RC16's height-one regularity
(`heightOneTarget_of_inputs`). PROVED. -/
theorem baseZeroInputsCST_of_leaves {ℓ : ℕ} {D : RCData ℓ} (hcc : CommonCoordinateInputs D)
    (hpr : PrimRegularityInputs D) (h : BaseZeroLeafInputs D) : BaseZeroInputsCST D :=
  baseZeroInputsCST_of_leaf (commonCoordinateTarget_of_inputs hcc)
    (heightOneTarget_of_inputs D hpr (commonCoordinateTarget_of_inputs hcc)) h

/-- **`RCSteps.base_zero` from the leaves** (tex 4330–4376): `Prints` (Cai–Shu–Tian Thm 1.1, for
the height formula), the existing leaves `CommonCoordinateInputs D`, `PrimRegularityInputs D` and
the base-zero leaf inputs. PROVED (lane RC0's `baseZeroTarget_of_inputs` and
`baseZeroInputs_of_CST`). -/
theorem baseZeroTarget_of_leaves {ℓ : ℕ} {D : RCData ℓ} (P : Prints)
    (hcc : CommonCoordinateInputs D) (hpr : PrimRegularityInputs D) (h : BaseZeroLeafInputs D) :
    BaseZeroTarget D :=
  baseZeroTarget_of_inputs P (baseZeroInputs_of_CST (baseZeroInputsCST_of_leaves hcc hpr h))

/-! ## Only the base character of the other leaves is used -/

/-- **(4.7) at one address from its `CommonCoordinateModel`** (Lemma
`ex:arith-common-coordinate`, tex 4142–4152, 4219–4226): `ũ_x = (∏_{q ∈ U} ε_q) u_{prim,x}` with
`∏ ε_q ∈ Λ^×`. The one-address form of lane RC0's `commonCoordinateTarget_of_inputs` (lane RC15's
`corrected_eq`); at `x = 0` it is the text's "`ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ Λ^×` by Lemma
`ex:arith-common-coordinate`" (tex 4369–4373). The model itself is what batch 3's
`CommonCoordinate.commonCoordinateModel_of_models` builds from the support-triangle models.
PROVED. -/
theorem common47_of_model {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
    (M : CommonCoordinateModel D Fam x) :
    ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde Fam x = ε * D.uPrim Fam x := by
  classical
  have hfilter : (M.Q.filter fun q => M.chi (M.g q) = 1) = M.U := by
    ext q
    rw [Finset.mem_filter, ← M.hU q]
  have h47 : (∏ q ∈ M.Q with M.chi (M.g q) = 1, M.chi (M.l q)) * M.urel =
      (∏ q ∈ M.Q with M.chi (M.g q) = 1, M.chi (M.e q) ^ 2 * M.eps q) * D.uPrim Fam x := by
    rw [hfilter]
    exact M.h47
  have hcorr := Central.corrected_eq M.chi M.Q M.v M.g M.l M.e M.ei M.eps M.urel (D.uPrim Fam x)
    M.hsign M.hratio M.hinv h47
  refine ⟨∏ q ∈ M.U, M.eps q, lamUnit_prod _ _ M.hunit, ?_⟩
  rw [M.hutilde, hcorr, hfilter]

/-- **The base-character parts of the leaves `common_coordinate` and `prim_regular`** (tex
4142–4328 and 4976–5200 at `x = 0`; tex 5196–5200, 5703–5704): at every final family, a
`CommonCoordinateModel` at the base address and lane RC16's regularity inputs for the primitive
coordinate at the base (`∃ u, IsTExpansion u (D.uPrim F 0) ∧ RegularityInputs u`). Kinds: those of
`CommonCoordinateInputs` and `PrimRegularityInputs` at `x = 0`. -/
def BaseCharacterInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    Nonempty (CommonCoordinateModel D F 0) ∧
      ∃ u : FractionRing Uniform.Lambda, IsTExpansion u (D.uPrim F 0) ∧ RegularityInputs u

/-- The leaves `common_coordinate` and `prim_regular` contain the base-character inputs
(PROVED: specialize to `x = 0`). -/
theorem baseCharacterInputs_of_leaves {ℓ : ℕ} {D : RCData ℓ} (hcc : CommonCoordinateInputs D)
    (hpr : PrimRegularityInputs D) : BaseCharacterInputs D :=
  fun Co Ce F hF => ⟨hcc Co Ce F hF 0, hpr Co Ce F hF 0⟩

/-- **`BaseZeroInputsCST D` from the base-character inputs and the leaf inputs** (tex 4330–4376,
4369–4373, 5703–5706): the base-zero lemma uses the other leaves only at the base character.
PROVED. -/
theorem baseZeroInputsCST_of_base {ℓ : ℕ} {D : RCData ℓ} (hb : BaseCharacterInputs D)
    (h : BaseZeroLeafInputs D) : BaseZeroInputsCST D := by
  intro hSel hk Co Ce F hF
  obtain ⟨M⟩ := h hSel hk Co Ce F hF
  obtain ⟨⟨M47⟩, u, hTu, hreg⟩ := hb Co Ce F hF
  obtain ⟨ε, hε, h47⟩ := common47_of_model M47
  have hprim : InLamHalf (D.uPrim F 0) := inLamHalf_of_isTExpansion hTu hreg.mem_lambdaHalf
  have htilde : InLamHalf (D.uTilde F 0) := by
    rw [h47]
    exact inLamHalf_lamUnit_mul hε hprim
  exact M.nonempty_modelCST ⟨ε, hε, h47⟩ htilde

end ZInQ.Manuscript.RC.BaseZeroAssembly

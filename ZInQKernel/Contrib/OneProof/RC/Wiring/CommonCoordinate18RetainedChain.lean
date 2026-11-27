import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18Retained
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Unit

/-!
# The end coordinate of the chain read in a retained basis

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): the relaxed
coordinate `u_rel` is read in the retained integral bases (tex 3886–3888), and "replacing them by
the retained homotopy equivalent free models contributes only determinants of unit disks"
(tex 4189–4193); with Lemma `ex:limits-inner-limit` (tex 4401–4405, 4444–4450).

The chain of the leaf reads its end coordinate `chainV n` in the iterated cone basis. Here the
cone model of the full support `C_{U_x}` (the model of the last state, `(cmState cd n le_rfl).R`)
is compared with a second, retained, finite free model of the same complex, and the comparison is
passed through the limit.

* (a) At a stage. `RetainedModel X B₀ B₁ B₂ B₃`: a retract of `X` onto a finite free model with
  bases of the given index types (lane RC31's graded models, or any retract with `FourFree`
  bases); `coneFree`: the bases of the cone model of the last state; `stageComparison`: the
  homotopy-equivalence data `modelEquiv_of_retracts` between the two models, with
  `stageComparison_holds` and `stageComparison_dA0`, `stageComparison_dA1`, `stageComparison_dA2`
  (its first model is the cone model). Over the stages: `retainedSeq`, **`retained_limit_holds`**
  (the limit data over `Λ` are exact, `limit_holds_of_stagesOn`); **`retained_dA0_eq`**,
  **`retained_dA1_eq`**, **`retained_dA2_eq`**: the first model of the limit data is the cone model
  of the limit chain at the full support.
* (b) The end coordinate in the retained basis. `retainedF`: the limit data over `Frac Λ`;
  `retainedKm`: the Knudsen–Mumford coordinate of the second model at the transported class
  `f₁ z` and functional `λ g₂`; `retainedEndCoord`: at the cone class and functional of the full
  support. **`retainedEndCoord_iso`** (PROVED): when the comparison is invertible over `Λ`,
  `u_ret = ε · chainV n` with `ε = det f₁ det f₃ det g₀ det g₂ ∈ Λ^×`. In general:
  `KmCoordComparisonLamUnit` (a statement, NOT proved) and **`retainedEndCoord_of_lamUnit`**.
  **`htildeE_of_retained`**, **`htildeE_of_retained_iso`**: from the retained-basis
  identification `ũ_x ≐ η_x u_ret` (and `ũ_x ≐ η_x v₀` when `U_x = ∅`), the relaxed end field
  `∃ ε ∈ Λ^×, ũ_x ≐ ε η_x chainV n` of `CommonCoordinateLimitSTE`.

Why the general statement is over `Λ` with values in `Frac Λ`: `KmCoordComparisonUnit` over
`Frac Λ` gives units of `Frac Λ`, which every nonzero scalar is; over `Λ` the coordinate of a
complex without a contraction over `Λ` is `0` by definition of the torsion. The text's unit is a
`Λ`-unit for data over `Λ` read over `Frac Λ`, which is `KmCoordComparisonLamUnit`.

* (c) What the chain does not carry. The second retract at the stages, with index types fixed along
  the ultrafilter, is not part of the chain data: `RetainedModelsExist` states it (NOT proved; lane
  RC31's `exists_gradedModel` gives a graded model at each stage, ELLIOT's bounded ranks fix its
  index types on a set of the ultrafilter).

Kinds: definitions and PROVED; `KmCoordComparisonLamUnit` and `RetainedModelsExist` are statements
(definitions of propositions), not proved.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (ulimHom stageIdeal GRetract SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.Torsion (FourCx kmCoord)
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (BlockComplex σBlock)
open scoped PowerSeries.WithPiTopology

/-! ### (a) The comparison at a stage -/

section Stage

variable {A : Type} [CommRing A]

/-- **A retained finite free model of a complex** (tex 4391–4399, 4189–4193): a retract of `X`
onto a complex `Y` with bases of the index types `B₀, …, B₃` in degrees `0, …, 3`.
Kind: definition (data). -/
structure RetainedModel (X : GCx A) (B0 B1 B2 B3 : Type) where
  /-- the model -/
  Y : GCx A
  /-- the retract of `X` onto it -/
  R : GRetract X Y
  /-- its bases -/
  b : FourFree Y B0 B1 B2 B3

variable {ι : Type} [DecidableEq ι] {C : Finset ι → GCx A}
  {E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T))} {m0 m1 m2 : ℕ}
  {ps : ℕ → ι} {n : ℕ}

/-- The matrix of `Matrix.toLin' M` in the standard bases is `M` (tex 4444–4448).
Kind: PROVED. -/
theorem matIn_refl_toLin' {ι κ : Type} [Fintype ι] [DecidableEq ι] (M : Matrix κ ι A) :
    matIn (LinearEquiv.refl A (ι → A)) (LinearEquiv.refl A (κ → A)) (Matrix.toLin' M) = M := by
  have e : (LinearEquiv.refl A (κ → A)).toLinearMap ∘ₗ Matrix.toLin' M ∘ₗ
      (LinearEquiv.refl A (ι → A)).symm.toLinearMap = Matrix.toLin' M :=
    LinearMap.ext fun _ => rfl
  rw [matIn, e, LinearMap.toMatrix'_toLin']

/-- **The bases of the cone model of the full support** (tex 4185–4193): the standard bases of the
block-complex model of the last state of the chain. Kind: definition. -/
def coneFree (cd : CMChainData C E m0 m1 m2 ps n) :
    FourFree (cmState cd n le_rfl).D.toGCx (Fin m0) (cD1 m0 m1 n) (cD2 m1 m2 n) (Fin m2) :=
  FourFree.ofBlock _

variable {B0 B1 B2 B3 : Type} [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]

/-- **The comparison of the cone model of the full support with a retained model** (tex 4189–4193,
4437–4441): `modelEquiv_of_retracts` between the retract of the last state and the retained
retract. Kind: definition. -/
def stageComparison (cd : CMChainData C E m0 m1 m2 ps n)
    (RM : RetainedModel (C (chainT ps n)) B0 B1 B2 B3) :
    HEMat A (Fin m0) (cD1 m0 m1 n) (cD2 m1 m2 n) (Fin m2) B0 B1 B2 B3 :=
  modelEquiv_of_retracts (cmState cd n le_rfl).R RM.R (coneFree cd) RM.b

/-- The comparison satisfies the identities exactly (tex 4189–4193, 4437–4441). Kind: PROVED. -/
theorem stageComparison_holds (cd : CMChainData C E m0 m1 m2 ps n)
    (RM : RetainedModel (C (chainT ps n)) B0 B1 B2 B3) :
    (stageComparison cd RM).Holds ⊥ :=
  modelEquiv_of_retracts_holds _ _ _ _

/-- The first model of the comparison is the cone model, degrees `0 → 1` (tex 4185–4193).
Kind: PROVED. -/
theorem stageComparison_dA0 (cd : CMChainData C E m0 m1 m2 ps n)
    (RM : RetainedModel (C (chainT ps n)) B0 B1 B2 B3) :
    (stageComparison cd RM).dA0 = (cmState cd n le_rfl).d0 :=
  matIn_refl_toLin' _

/-- The first model of the comparison is the cone model, degrees `1 → 2` (tex 4185–4193).
Kind: PROVED. -/
theorem stageComparison_dA1 (cd : CMChainData C E m0 m1 m2 ps n)
    (RM : RetainedModel (C (chainT ps n)) B0 B1 B2 B3) :
    (stageComparison cd RM).dA1 = (cmState cd n le_rfl).d1 :=
  matIn_refl_toLin' _

/-- The first model of the comparison is the cone model, degrees `2 → 3` (tex 4185–4193).
Kind: PROVED. -/
theorem stageComparison_dA2 (cd : CMChainData C E m0 m1 m2 ps n)
    (RM : RetainedModel (C (chainT ps n)) B0 B1 B2 B3) :
    (stageComparison cd RM).dA2 = (cmState cd n le_rfl).d2 :=
  matIn_refl_toLin' _

end Stage

/-! ### (a) Through the stages -/

/-- Two sequences agreeing modulo the stage ideals at `U`-many stages have the same ultralimit
(tex 4446–4448). Kind: PROVED. -/
theorem ulimHom_eq_of_stage {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    {x y : ℕ → LamI} (h : ∀ᶠ s in (U : Filter ℕ), x s - y s ∈ stageIdeal s) :
    ulimHom U x = ulimHom U y := by
  have e := ulimHom_ultraIdeal hU (x := x - y) h
  rwa [map_sub, sub_eq_zero] at e

section Stages

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
  {B0 B1 B2 B3 : Type} [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]

/-- **The lifted comparisons on the retained stages** (tex 4401–4406), zero elsewhere.
Kind: definition. -/
def retainedSeq (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3) :
    ℕ → HEMat LamI (Fin m0) (cD1 m0 m1 n) (cD2 m1 m2 n) (Fin m2) B0 B1 B2 B3 :=
  heStagesOn G fun s h => stageComparison (cd s h) (RM s h)

/-- **The limit comparison over `Λ` is exact** (tex 4401–4405, 4447–4450: "Retained homotopy
inverses remain homotopy inverses"), for retained models with index types fixed on a `U`-large set
of stages. Kind: PROVED. -/
theorem retained_limit_holds (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    (limitHE (retainedSeq G cd RM) U).Holds ⊥ :=
  limit_holds_of_stagesOn G _ hU hG fun s h => stageComparison_holds (cd s h) (RM s h)

omit [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3] in
/-- The stage chain data lifted by `stageMatsOn` reduce to the last state, degrees `0 → 1`
(tex 4385–4451). Kind: PROVED. -/
theorem mk_stageMatsOn_blk0 (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) {s : ℕ} (hs : s ∈ G)
    (a b) : Ideal.Quotient.mk (stageIdeal s) ((stageMatsOn G cd bw μ s).blk0 n a b) =
      (cmState (cd s hs) n le_rfl).d0 a b := by
  have e : stageMatsOn G cd bw μ s = stageLift s ((cd s hs).toChainMat (bw s) (μ s)) :=
    dite_eq_left hs
  rw [e]
  have h1 : ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s))).blk0 n a b = Ideal.Quotient.mk (stageIdeal s)
        ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).blk0 n a b) := by
    rw [ChainMat.blk0_map]
    rfl
  have h2 : (stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s)) = (cd s hs).toChainMat (bw s) (μ s) :=
    ChainMat.liftAlong_map _ _ _
  rw [← h1, h2, blk0_eq (cd s hs) (bw s) (μ s) n le_rfl]

omit [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3] in
/-- The stage chain data lifted by `stageMatsOn` reduce to the last state, degrees `1 → 2`
(tex 4385–4451). Kind: PROVED. -/
theorem mk_stageMatsOn_blk1 (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) {s : ℕ} (hs : s ∈ G)
    (a b) : Ideal.Quotient.mk (stageIdeal s) ((stageMatsOn G cd bw μ s).blk1 n a b) =
      (cmState (cd s hs) n le_rfl).d1 a b := by
  have e : stageMatsOn G cd bw μ s = stageLift s ((cd s hs).toChainMat (bw s) (μ s)) :=
    dite_eq_left hs
  rw [e]
  have h1 : ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s))).blk1 n a b = Ideal.Quotient.mk (stageIdeal s)
        ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).blk1 n a b) := by
    rw [ChainMat.blk1_map]
    rfl
  have h2 : (stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s)) = (cd s hs).toChainMat (bw s) (μ s) :=
    ChainMat.liftAlong_map _ _ _
  rw [← h1, h2, blk1_eq (cd s hs) (bw s) (μ s) n le_rfl]

omit [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3] in
/-- The stage chain data lifted by `stageMatsOn` reduce to the last state, degrees `2 → 3`
(tex 4385–4451). Kind: PROVED. -/
theorem mk_stageMatsOn_blk2 (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s) {s : ℕ} (hs : s ∈ G)
    (a b) : Ideal.Quotient.mk (stageIdeal s) ((stageMatsOn G cd bw μ s).blk2 n a b) =
      (cmState (cd s hs) n le_rfl).d2 a b := by
  have e : stageMatsOn G cd bw μ s = stageLift s ((cd s hs).toChainMat (bw s) (μ s)) :=
    dite_eq_left hs
  rw [e]
  have h1 : ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s))).blk2 n a b = Ideal.Quotient.mk (stageIdeal s)
        ((stageLift s ((cd s hs).toChainMat (bw s) (μ s))).blk2 n a b) := by
    rw [ChainMat.blk2_map]
    rfl
  have h2 : (stageLift s ((cd s hs).toChainMat (bw s) (μ s))).map
      (Ideal.Quotient.mk (stageIdeal s)) = (cd s hs).toChainMat (bw s) (μ s) :=
    ChainMat.liftAlong_map _ _ _
  rw [← h1, h2, blk2_eq (cd s hs) (bw s) (μ s) n le_rfl]

/-- The entries of the limit chain are the ultralimits of the stage entries, degrees `0 → 1`
(tex 4444–4448). Kind: PROVED. -/
theorem limitChain_blk0_apply {m0' m1' m2' : ℕ} (c : ℕ → ChainMat LamI m0' m1' m2')
    (U : Ultrafilter ℕ) (i : ℕ) (a b) :
    (limitChain c U).blk0 i a b = ulimHom U (fun s => (c s).blk0 i a b) := by
  change ((prodChain c).map (ulimHom U)).blk0 i a b = _
  rw [ChainMat.blk0_map]
  change ulimHom U ((prodChain c).blk0 i a b) = _
  congr 1
  funext s
  rw [← prodChain_eval c s, ChainMat.blk0_map]
  rfl

/-- The entries of the limit chain are the ultralimits of the stage entries, degrees `1 → 2`
(tex 4444–4448). Kind: PROVED. -/
theorem limitChain_blk1_apply {m0' m1' m2' : ℕ} (c : ℕ → ChainMat LamI m0' m1' m2')
    (U : Ultrafilter ℕ) (i : ℕ) (a b) :
    (limitChain c U).blk1 i a b = ulimHom U (fun s => (c s).blk1 i a b) := by
  change ((prodChain c).map (ulimHom U)).blk1 i a b = _
  rw [ChainMat.blk1_map]
  change ulimHom U ((prodChain c).blk1 i a b) = _
  congr 1
  funext s
  exact prodChain_blk1 c i a b s

/-- The entries of the limit chain are the ultralimits of the stage entries, degrees `2 → 3`
(tex 4444–4448). Kind: PROVED. -/
theorem limitChain_blk2_apply {m0' m1' m2' : ℕ} (c : ℕ → ChainMat LamI m0' m1' m2')
    (U : Ultrafilter ℕ) (i : ℕ) (a b) :
    (limitChain c U).blk2 i a b = ulimHom U (fun s => (c s).blk2 i a b) := by
  change ((prodChain c).map (ulimHom U)).blk2 i a b = _
  rw [ChainMat.blk2_map]
  change ulimHom U ((prodChain c).blk2 i a b) = _
  congr 1
  funext s
  rw [← prodChain_eval c s, ChainMat.blk2_map]
  rfl

/-- **The first model of the limit comparison is the limit cone model**, degrees `0 → 1`
(tex 4185–4193, 4444–4448). Kind: PROVED. -/
theorem retained_dA0_eq (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    (limitHE (retainedSeq G cd RM) U).dA0 = (limitChain (stageMatsOn G cd bw μ) U).blk0 n := by
  refine Matrix.ext fun a b => ?_
  rw [limitChain_blk0_apply]
  refine ulimHom_eq_of_stage hU ?_
  filter_upwards [hG] with s hs
  have e : retainedSeq G cd RM s = stageLiftHE s (stageComparison (cd s hs) (RM s hs)) :=
    dite_eq_left hs
  have h1 : Ideal.Quotient.mk (stageIdeal s) ((retainedSeq G cd RM s).dA0 a b) =
      (cmState (cd s hs) n le_rfl).d0 a b := by
    rw [e, ← stageComparison_dA0 (cd s hs) (RM s hs)]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  rw [← Ideal.Quotient.eq]
  exact h1.trans (mk_stageMatsOn_blk0 G cd bw μ hs a b).symm

/-- **The first model of the limit comparison is the limit cone model**, degrees `1 → 2`
(tex 4185–4193, 4444–4448). Kind: PROVED. -/
theorem retained_dA1_eq (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    (limitHE (retainedSeq G cd RM) U).dA1 = (limitChain (stageMatsOn G cd bw μ) U).blk1 n := by
  refine Matrix.ext fun a b => ?_
  rw [limitChain_blk1_apply]
  refine ulimHom_eq_of_stage hU ?_
  filter_upwards [hG] with s hs
  have e : retainedSeq G cd RM s = stageLiftHE s (stageComparison (cd s hs) (RM s hs)) :=
    dite_eq_left hs
  have h1 : Ideal.Quotient.mk (stageIdeal s) ((retainedSeq G cd RM s).dA1 a b) =
      (cmState (cd s hs) n le_rfl).d1 a b := by
    rw [e, ← stageComparison_dA1 (cd s hs) (RM s hs)]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  rw [← Ideal.Quotient.eq]
  exact h1.trans (mk_stageMatsOn_blk1 G cd bw μ hs a b).symm

/-- **The first model of the limit comparison is the limit cone model**, degrees `2 → 3`
(tex 4185–4193, 4444–4448). Kind: PROVED. -/
theorem retained_dA2_eq (G : Set ℕ)
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3)
    (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
    (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    (limitHE (retainedSeq G cd RM) U).dA2 = (limitChain (stageMatsOn G cd bw μ) U).blk2 n := by
  refine Matrix.ext fun a b => ?_
  rw [limitChain_blk2_apply]
  refine ulimHom_eq_of_stage hU ?_
  filter_upwards [hG] with s hs
  have e : retainedSeq G cd RM s = stageLiftHE s (stageComparison (cd s hs) (RM s hs)) :=
    dite_eq_left hs
  have h1 : Ideal.Quotient.mk (stageIdeal s) ((retainedSeq G cd RM s).dA2 a b) =
      (cmState (cd s hs) n le_rfl).d2 a b := by
    rw [e, ← stageComparison_dA2 (cd s hs) (RM s hs)]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  rw [← Ideal.Quotient.eq]
  exact h1.trans (mk_stageMatsOn_blk2 G cd bw μ hs a b).symm

end Stages


/-! ### (b) The coordinate of the transported class and functional -/

section Transported

variable {R : Type} [CommRing R] {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1]
  [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0]
  [DecidableEq A1] [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3]

/-- The transported class `f₁ z` of a cycle is a cycle of the second model (tex 4189–4193,
4437–4441). Kind: PROVED. -/
theorem HEMat.transport_cycle (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥)
    {z : A1 → R} (hz : E.dA1 *ᵥ z = 0) : (E.cxB hE).d1 *ᵥ (E.f1 *ᵥ z) = 0 := by
  have c1 : E.dB1 * E.f1 = E.f2 * E.dA1 := (sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf1)).symm
  change E.dB1 *ᵥ (E.f1 *ᵥ z) = 0
  rw [mulVec_mulVec, c1, ← mulVec_mulVec, hz, mulVec_zero]

/-- The transported functional `λ g₂` of a closed functional is closed on the second model
(tex 4189–4193, 4437–4441). Kind: PROVED. -/
theorem HEMat.transport_closed (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥)
    {lam : A2 → R} (hlam : lam ᵥ* E.dA1 = 0) : (lam ᵥ* E.g2) ᵥ* (E.cxB hE).d1 = 0 := by
  have c1 : E.g2 * E.dB1 = E.dA1 * E.g1 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hg1)
  change (lam ᵥ* E.g2) ᵥ* E.dB1 = 0
  rw [vecMul_vecMul, c1, ← vecMul_vecMul, hlam, zero_vecMul]

/-- **The coordinate in the second (retained) model** (tex 3886–3888, 4189–4193): the
Knudsen–Mumford coordinate of the second model at the transported class `f₁ z` and functional
`λ g₂`, oriented by `σ_B`. Kind: definition. -/
def HEMat.retainedKm (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥) {z : A1 → R}
    {lam : A2 → R} (hz : E.dA1 *ᵥ z = 0) (hlam : lam ᵥ* E.dA1 = 0)
    (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)) : R :=
  kmCoord (E.cxB hE) (E.f1 *ᵥ z) (lam ᵥ* E.g2) (E.transport_cycle hE hz)
    (E.transport_closed hE hlam) σB

end Transported

/-- Equal four-term complexes have equal coordinates (tex 4185–4193). Kind: PROVED. -/
theorem kmCoord_congr_cx {R : Type} [CommRing R] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1]
    [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    {C C' : FourCx R ι0 ι1 ι2 ι3} (h : C = C') (z : ι1 → R)
    (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (hz' : C'.d1 *ᵥ z = 0)
    (hlam' : lam ᵥ* C'.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ = kmCoord C' z lam hz' hlam' σ := by
  subst h
  rfl

/-- **The general change of model with a `Λ`-unit, NOT proved here** (tex 4189–4193: "replacing
them by the retained homotopy equivalent free models contributes only determinants of unit disks.
These are `A_i`-units. Their limits and inverse limits are `Λ`-units"): for exact
homotopy-equivalence data `E` over `Λ` between two four-term models of possibly different ranks,
read over `Frac Λ`, the coordinate of the second model at the transported class and functional is
a `Λ`-unit times the coordinate of the first, for any orientations. (Over `Frac Λ`, a unit of
`Frac Λ` would be no information; over `Λ`, the coordinate of a complex without a contraction over
`Λ` is `0`.) Kind: definition (a statement, not proved). -/
def KmCoordComparisonLamUnit : Prop :=
  ∀ (A0 A1 A2 A3 B0 B1 B2 B3 : Type) [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3]
    [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1]
    [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1] [DecidableEq B2]
    [DecidableEq B3] (E : HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3), E.Holds ⊥ →
    ∀ (hEF : (E.map lamToF).Holds ⊥) (z : A1 → FracLam) (lam : A2 → FracLam)
      (hz : (E.map lamToF).dA1 *ᵥ z = 0) (hlam : lam ᵥ* (E.map lamToF).dA1 = 0)
      (σA : (A0 ⊕ Unit) ⊕ A2 ≃ A1 ⊕ (A3 ⊕ Unit)) (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)),
      ∃ ε : Lambdaˣ, (E.map lamToF).retainedKm hEF hz hlam σB =
        lamToF (ε : Lambda) * kmCoord ((E.map lamToF).cxA hEF) z lam hz hlam σA

/-! ### (b) The end coordinate of the chain in the retained basis -/

section EndRetained

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
  {B0 B1 B2 B3 : Type} [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]
  (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
  (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx n)) B0 B1 B2 B3)
  (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
  (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
  (f : FrobSeq LamI)
  (hs : ∀ᶠ s in (U : Filter ℕ), (stageMatsOn G cd bw μ s).Holds (stageIdeal s) f n)

/-- **The limit comparison read over `Frac Λ`** (tex 4189–4193, 4444–4450). Kind: definition. -/
abbrev retainedF (U : Ultrafilter ℕ) :
    HEMat FracLam (Fin m0) (cD1 m0 m1 n) (cD2 m1 m2 n) (Fin m2) B0 B1 B2 B3 :=
  (limitHE (retainedSeq G cd RM) U).map lamToF

include hU hG in
/-- The limit comparison over `Frac Λ` is exact (tex 4447–4450). Kind: PROVED. -/
theorem retainedF_holds : (retainedF G cd RM U).Holds ⊥ :=
  ((limitHE (retainedSeq G cd RM) U).holds_map_iff lamToF ⊥).2
    ((retained_limit_holds G cd RM hU hG).mono bot_le)

include hU hG in
/-- The first model over `Frac Λ` is the cone model of the full support, degrees `0 → 1`
(tex 4185–4193). Kind: PROVED. -/
theorem retainedF_dA0 :
    (retainedF G cd RM U).dA0 = (fracChain (stageMatsOn G cd bw μ) U).blk0 n := by
  change (limitHE (retainedSeq G cd RM) U).dA0.map lamToF =
    ((limitChain (stageMatsOn G cd bw μ) U).map lamToF).blk0 n
  rw [ChainMat.blk0_map, retained_dA0_eq G cd RM bw μ hU hG]

include hU hG in
/-- The first model over `Frac Λ` is the cone model of the full support, degrees `1 → 2`
(tex 4185–4193). Kind: PROVED. -/
theorem retainedF_dA1 :
    (retainedF G cd RM U).dA1 = (fracChain (stageMatsOn G cd bw μ) U).blk1 n := by
  change (limitHE (retainedSeq G cd RM) U).dA1.map lamToF =
    ((limitChain (stageMatsOn G cd bw μ) U).map lamToF).blk1 n
  rw [ChainMat.blk1_map, retained_dA1_eq G cd RM bw μ hU hG]

include hU hG in
/-- The first model over `Frac Λ` is the cone model of the full support, degrees `2 → 3`
(tex 4185–4193). Kind: PROVED. -/
theorem retainedF_dA2 :
    (retainedF G cd RM U).dA2 = (fracChain (stageMatsOn G cd bw μ) U).blk2 n := by
  change (limitHE (retainedSeq G cd RM) U).dA2.map lamToF =
    ((limitChain (stageMatsOn G cd bw μ) U).map lamToF).blk2 n
  rw [ChainMat.blk2_map, retained_dA2_eq G cd RM bw μ hU hG]

/-- **The first model of the limit comparison is the cone model of the full support**
(tex 4185–4193, 4444–4448): as four-term complexes over `Frac Λ`. Kind: PROVED. -/
theorem retainedF_cxA :
    (retainedF G cd RM U).cxA (retainedF_holds G cd RM hU hG) =
      ((fracChain (stageMatsOn G cd bw μ) U).blockAt (fracChain_holds _ hU f n hs) n
        le_rfl).toFour :=
  fourCx_eq (retainedF_dA0 G cd RM bw μ hU hG) (retainedF_dA1 G cd RM bw μ hU hG)
    (retainedF_dA2 G cd RM bw μ hU hG)

include hU hG hs in
/-- The cone class of the full support is a cycle of the first model (tex 4185–4193).
Kind: PROVED. -/
theorem retainedF_cycle :
    (retainedF G cd RM U).dA1 *ᵥ (fracChain (stageMatsOn G cd bw μ) U).zP n = 0 := by
  rw [retainedF_dA1 G cd RM bw μ hU hG]
  exact (fracChain (stageMatsOn G cd bw μ) U).blockAt_cycle (fracChain_holds _ hU f n hs) n
    le_rfl

include hU hG hs in
/-- The cone functional of the full support is closed on the first model (tex 4185–4193).
Kind: PROVED. -/
theorem retainedF_closed :
    (fracChain (stageMatsOn G cd bw μ) U).lP n ᵥ* (retainedF G cd RM U).dA1 = 0 := by
  rw [retainedF_dA1 G cd RM bw μ hU hG]
  exact (fracChain (stageMatsOn G cd bw μ) U).blockAt_closed (fracChain_holds _ hU f n hs) n
    le_rfl

/-- **The end coordinate in the retained basis** (tex 3886–3888, 4189–4193: the text's `u_rel`):
the Knudsen–Mumford coordinate, over `Frac Λ`, of the retained model of the full support at the
cone class and functional of the limit chain transported by the limit comparison, oriented by
`σ_B`. Kind: definition. -/
def retainedEndCoord (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)) : FracLam :=
  (retainedF G cd RM U).retainedKm (retainedF_holds G cd RM hU hG)
    (retainedF_cycle G cd RM bw μ hU hG f hs) (retainedF_closed G cd RM bw μ hU hG f hs) σB

/-- **The cone coordinate of the first model is the chain's end value** (tex 4185–4193): the
coordinate of the first model of the limit comparison at the cone class and functional is
`chainV n` (the cone sign is one, `fracChain_v_end_one`). Kind: PROVED. -/
theorem retainedF_kmCoord_cxA :
    kmCoord ((retainedF G cd RM U).cxA (retainedF_holds G cd RM hU hG))
        ((fracChain (stageMatsOn G cd bw μ) U).zP n) ((fracChain (stageMatsOn G cd bw μ) U).lP n)
        (retainedF_cycle G cd RM bw μ hU hG f hs) (retainedF_closed G cd RM bw μ hU hG f hs)
        (σBlock m0 (m1 + 4 * n) m2) =
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f n hs) n :=
  (kmCoord_congr_cx (retainedF_cxA G cd RM bw μ hU hG f hs) _ _ _ _
    ((fracChain (stageMatsOn G cd bw μ) U).blockAt_cycle (fracChain_holds _ hU f n hs) n le_rfl)
    ((fracChain (stageMatsOn G cd bw μ) U).blockAt_closed (fracChain_holds _ hU f n hs) n le_rfl)
    _).trans (fracChain_v_end_one _ hU f n hs).symm

/-- **The end coordinate in the retained basis is a `Λ`-unit times the cone value, given the
general change of model** (tex 4189–4193). Kind: PROVED (from `KmCoordComparisonLamUnit`). -/
theorem retainedEndCoord_of_lamUnit (hK : KmCoordComparisonLamUnit)
    (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)) :
    ∃ ε : Lambdaˣ, retainedEndCoord G cd RM bw μ hU hG f hs σB =
      lamToF (ε : Lambda) *
        (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f n hs) n := by
  obtain ⟨ε, hε⟩ := hK _ _ _ _ _ _ _ _ (limitHE (retainedSeq G cd RM) U)
    (retained_limit_holds G cd RM hU hG) (retainedF_holds G cd RM hU hG)
    ((fracChain (stageMatsOn G cd bw μ) U).zP n) ((fracChain (stageMatsOn G cd bw μ) U).lP n)
    (retainedF_cycle G cd RM bw μ hU hG f hs) (retainedF_closed G cd RM bw μ hU hG f hs)
    (σBlock m0 (m1 + 4 * n) m2) σB
  exact ⟨ε, hε.trans (by rw [retainedF_kmCoord_cxA G cd RM bw μ hU hG f hs])⟩

end EndRetained

/-! ### (b) The isomorphism case -/

section EndIso

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ}
  (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
  (RM : ∀ s (_ : s ∈ G),
    RetainedModel (Cx s (chainT pidx n)) (Fin m0) (cD1 m0 m1 n) (cD2 m1 m2 n) (Fin m2))
  (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
  (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
  (f : FrobSeq LamI)
  (hs : ∀ᶠ s in (U : Filter ℕ), (stageMatsOn G cd bw μ s).Holds (stageIdeal s) f n)

/-- **The end coordinate in a retained basis with an invertible comparison** (tex 4189–4193):
when the limit comparison over `Λ` is an isomorphism (`f g = 1` in every degree; retained model of
the cone shape), the end coordinate in the retained basis, with the cone orientation, is
`ε · chainV n` with `ε = det f₁ det f₃ det g₀ det g₂ ∈ Λ^×` (`HEMat.kmCoord_comparison_iso`,
`HEMat.comparison_det_isUnit`). Kind: PROVED. -/
theorem retainedEndCoord_iso
    (h0 : (limitHE (retainedSeq G cd RM) U).f0 * (limitHE (retainedSeq G cd RM) U).g0 = 1)
    (h1 : (limitHE (retainedSeq G cd RM) U).f1 * (limitHE (retainedSeq G cd RM) U).g1 = 1)
    (h2 : (limitHE (retainedSeq G cd RM) U).f2 * (limitHE (retainedSeq G cd RM) U).g2 = 1)
    (h3 : (limitHE (retainedSeq G cd RM) U).f3 * (limitHE (retainedSeq G cd RM) U).g3 = 1) :
    ∃ ε : Lambdaˣ, retainedEndCoord G cd RM bw μ hU hG f hs (σBlock m0 (m1 + 4 * n) m2) =
      lamToF (ε : Lambda) *
        (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f n hs) n := by
  set L := limitHE (retainedSeq G cd RM) U with hL
  have hF : ∀ {α β : Type} [Fintype β] [DecidableEq α] {P : Matrix α β LamI}
      {Q : Matrix β α LamI}, P * Q = 1 → P.map lamToF * Q.map lamToF = 1 := fun h => by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨(L.comparison_det_isUnit h0 h1 h2 h3).unit, ?_⟩
  have e1 := HEMat.kmCoord_comparison_iso (L.map lamToF) (retainedF_holds G cd RM hU hG)
    (hF h0) (hF h1) (hF h2) (hF h3) (retainedF_cycle G cd RM bw μ hU hG f hs)
    (retainedF_closed G cd RM bw μ hU hG f hs)
    ((L.map lamToF).transport_cycle (retainedF_holds G cd RM hU hG)
      (retainedF_cycle G cd RM bw μ hU hG f hs))
    ((L.map lamToF).transport_closed (retainedF_holds G cd RM hU hG)
      (retainedF_closed G cd RM bw μ hU hG f hs)) (σBlock m0 (m1 + 4 * n) m2)
  refine e1.trans ?_
  rw [retainedF_kmCoord_cxA G cd RM bw μ hU hG f hs, IsUnit.unit_spec, map_mul, map_mul, map_mul,
    RingHom.map_det, RingHom.map_det, RingHom.map_det, RingHom.map_det]
  rfl

end EndIso

/-! ### (b) The relaxed end field from the retained-basis identification -/

section HTilde

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
  (x : Addr Fam.b) (ps : List ℕ)
  (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx ps.length)
  (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
  (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
  (f : FrobSeq LamI)
  (hs : ∀ᶠ s in (U : Filter ℕ), (stageMatsOn G cd bw μ s).Holds (stageIdeal s) f ps.length)

/-- **The relaxed end field from the retained-basis identification** (tex 4147, 4150–4152,
4189–4193): if `η_x u_ret` has `t`-expansion `ũ_x` (the text's `ũ_x = η_x u_rel` with `u_rel` in
the retained basis) when `U_x ≠ ∅`, and `η_x v₀ ≐ ũ_x` when `U_x = ∅` (tex 4150), then, given the
general change of model, `∃ ε ∈ Λ^×` with `ε = 1` if `U_x = ∅` and `ε η_x chainV n ≐ ũ_x`: the
field `htildeE` of `CommonCoordinateLimitSTE`. Kind: PROVED (from `KmCoordComparisonLamUnit`). -/
theorem htildeE_of_retained (hK : KmCoordComparisonLamUnit) {B0 B1 B2 B3 : Type} [Fintype B0]
    [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq B0] [DecidableEq B1] [DecidableEq B2]
    [DecidableEq B3]
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx ps.length)) B0 B1 B2 B3)
    (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit))
    (hret : ps ≠ [] → IsTExpansion (etaF ℓ Fam x * retainedEndCoord G cd RM bw μ hU hG f hs σB)
      (D.uTilde Fam x))
    (hnil : ps = [] → IsTExpansion (etaF ℓ Fam x *
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
        ps.length) (D.uTilde Fam x)) :
    ∃ ε : Lambdaˣ, (ps = [] → ε = 1) ∧ IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x *
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
        ps.length)) (D.uTilde Fam x) := by
  by_cases h0 : ps = []
  · exact ⟨1, fun _ => rfl, by rw [Units.val_one, map_one, one_mul]; exact hnil h0⟩
  · obtain ⟨ε, hε⟩ := retainedEndCoord_of_lamUnit G cd RM bw μ hU hG f hs hK σB
    refine ⟨ε, fun h => absurd h h0, ?_⟩
    have e : lamToF (ε : Lambda) * (etaF ℓ Fam x *
        (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
          ps.length) = etaF ℓ Fam x * retainedEndCoord G cd RM bw μ hU hG f hs σB := by
      rw [hε]
      ring
    rw [e]
    exact hret h0

/-- **The relaxed end field from a retained basis with an invertible comparison** (tex 4147,
4150–4152, 4189–4193): as `htildeE_of_retained`, with the comparison over `Λ` an isomorphism in
place of the general change of model; the unit is `det f₁ det f₃ det g₀ det g₂`. Kind: PROVED. -/
theorem htildeE_of_retained_iso
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx ps.length)) (Fin m0)
      (cD1 m0 m1 ps.length) (cD2 m1 m2 ps.length) (Fin m2))
    (h0 : (limitHE (retainedSeq G cd RM) U).f0 * (limitHE (retainedSeq G cd RM) U).g0 = 1)
    (h1 : (limitHE (retainedSeq G cd RM) U).f1 * (limitHE (retainedSeq G cd RM) U).g1 = 1)
    (h2 : (limitHE (retainedSeq G cd RM) U).f2 * (limitHE (retainedSeq G cd RM) U).g2 = 1)
    (h3 : (limitHE (retainedSeq G cd RM) U).f3 * (limitHE (retainedSeq G cd RM) U).g3 = 1)
    (hret : ps ≠ [] → IsTExpansion (etaF ℓ Fam x *
      retainedEndCoord G cd RM bw μ hU hG f hs (σBlock m0 (m1 + 4 * ps.length) m2))
      (D.uTilde Fam x))
    (hnil : ps = [] → IsTExpansion (etaF ℓ Fam x *
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
        ps.length) (D.uTilde Fam x)) :
    ∃ ε : Lambdaˣ, (ps = [] → ε = 1) ∧ IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x *
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
        ps.length)) (D.uTilde Fam x) := by
  by_cases hp : ps = []
  · exact ⟨1, fun _ => rfl, by rw [Units.val_one, map_one, one_mul]; exact hnil hp⟩
  · obtain ⟨ε, hε⟩ := retainedEndCoord_iso G cd RM bw μ hU hG f hs h0 h1 h2 h3
    refine ⟨ε, fun h => absurd h hp, ?_⟩
    have e : lamToF (ε : Lambda) * (etaF ℓ Fam x *
        (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
          ps.length) = etaF ℓ Fam x *
          retainedEndCoord G cd RM bw μ hU hG f hs (σBlock m0 (m1 + 4 * ps.length) m2) := by
      rw [hε]
      ring
    rw [e]
    exact hret hp

end HTilde

/-! ### (c) The retained models the chain does not carry -/

/-- **Retained models of the full support at the stages, NOT proved here** (tex 4391–4406): on a
`U`-large subset `G'` of the retained stages `G`, the complexes `Cx s (chainT pidx n)` of the full
support have retracts onto finite free models with bases of FIXED index types `Fin (r 0), …,
Fin (r 3)`. Lane RC31's `exists_gradedModel` gives a graded model at each stage (flat terms,
finite residual cohomology); ELLIOT's bounded ranks fix the ranks on a set of the ultrafilter
(`bounded_rank_tuples_fixed`); the vanishing in degrees `−1` and `4` is the concentration of the
residual cohomology in degrees `0, …, 3`. Kind: definition (a statement, not proved). -/
def RetainedModelsExist {ι : Type} [DecidableEq ι] (Cx : ∀ s, Finset ι → GCx (StageRing s))
    (pidx : ℕ → ι) (n : ℕ) (G : Set ℕ) (U : Ultrafilter ℕ) : Prop :=
  ∃ (r : Fin 4 → ℕ) (G' : Set ℕ), G' ⊆ G ∧ (∀ᶠ s in (U : Filter ℕ), s ∈ G') ∧
    Nonempty (∀ s (_ : s ∈ G'),
      RetainedModel (Cx s (chainT pidx n)) (Fin (r 0)) (Fin (r 1)) (Fin (r 2)) (Fin (r 3)))

end ZInQ.Manuscript.RC.Wiring

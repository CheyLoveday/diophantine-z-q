import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Model

/-!
# The relaxation step from the actual support triangle, in torsion coordinates

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194):

> Let `i : C_P → C_R` be the primitive-to-relaxed map […] The actual norm identity is
> `z_R = e_q i(z_P)`, with its retained boundary. […] Consequently `λ_R ∘ i = e_q λ_P`. […]
> The two quotient determinants satisfy `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`.
> In the original integral determinant bases, the support triangle therefore gives
> `l_q u_rel = e_q² ε_q u_prim` (4.7).

A `SupportTriangle F` packages the actual objects over a field `F` (e.g. the fraction field of
the coefficient domain): the primitive and relaxed complexes `C_P`, `C_R` (any `GCx`, e.g. the
Selmer cones `selCx` after base change), the primitive-to-relaxed map as a split inclusion, a
block-complex model `D` of `C_P` with its retract (for cohomology of dimensions `(0, 1, 1, 0)`
the minimal model, `CommonCoordinate10Block.lean`), a retract of the quotient complex onto a model
`Q'` living in degrees one and two (e.g. the tame local model `twoSingCx` of (4.4)) with bases,
and the actual cycles and closed functionals. Its coordinates are the Knudsen–Mumford coordinates
of the models at the transported classes:

* `primCoord`: `kmCoord` of `D` at `p z_P` and `λ_P ∘ i_D` (`u_prim` of the step);
* `relCoord`: `kmCoord` of the full-condition model of `C_R` (`relModel`, the matrices of the
  two-piece triangular model `D ⊕ Q'`) at `p z_R` and `λ_R ∘ i_R` (`u_rel` of the step).

**`kmStep_of_supportTriangle`** (PROVED): under three explicit arithmetic hypotheses,
* `hBe` (the new block): the matrix of the model quotient differential `d_{Q'} : Q'¹ → Q'²` in
  the bases is the two-place block `diag(z Fr_q − q, z⁻¹ Fr_q − q)` up to a relabelling (the
  shape of `kmCoord_step_47`'s `hBe`; for `Q' = twoSingCx` it is lane RC31's `twoSing_matrix`);
* `hzR` (the norm identity with its retained boundary): `z_R = e_q i(z_P) + d b`;
* `hlamR` (the functional relation): `λ_R ∘ i = e_q λ_P`;
and the unit condition `l_q ≠ 0`, the step is a `KmStep` at `(relCoord, primCoord)`; hence
`l_q u_rel = e_q² q⁻⁴ u_prim` (`h47_of_supportTriangle`). The model-shape variant
`kmStep_of_supportTriangle_model` takes `hlamR` literally in `KmStep`'s shape on the model
vectors. `isUnit_relModel_det`: the unit `hB` from `hBe` and `l_q ≠ 0` (`det B = q⁴ l_q`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock det_twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor quotientDet quotientDet_eq)

/-- **The actual support triangle at one unused prime** (tex 4157–4194, 5398–5424): the
primitive complex `C_P` (support `T`) and the relaxed complex `C_R` (support `T ∪ {q}`) over a
field, the primitive-to-relaxed map `i` split with quotient complex `Q` (the local quotient at
`q`), a block-complex model `D` of `C_P` with its retract, a retract of `Q` onto a model `Q'`
vanishing outside degrees one and two with bases of `Q'¹, Q'²` indexed by `N`, and the actual
cycles `z_R, z_P` and closed functionals `λ_R, λ_P`. Kind: definition (data). -/
structure SupportTriangle (F : Type) [Field F] where
  /-- the primitive complex `C_P` -/
  CP : GCx F
  /-- the relaxed complex `C_R` -/
  CR : GCx F
  /-- the primitive-to-relaxed map, degreewise split -/
  E : SplitInclusion CP CR
  /-- the block-complex model of `C_P` -/
  D : BlockComplex F
  /-- the retract of `C_P` onto its model -/
  R : GRetract CP D.toGCx
  /-- the model of the quotient complex (the local quotient at `q`) -/
  Q' : GCx F
  /-- the retract of the quotient complex onto its model -/
  RQ : GRetract E.quotientCx Q'
  /-- the model of the quotient lives in degrees one and two -/
  hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n)
  /-- the index set of the new summands -/
  N : Type
  /-- `N` is finite -/
  [fintypeN : Fintype N]
  /-- `N` has decidable equality -/
  [decEqN : DecidableEq N]
  /-- a basis of `Q'¹` -/
  b1 : Basis N F (Q'.X 1)
  /-- a basis of `Q'²` -/
  b2 : Basis N F (Q'.X 2)
  /-- the relaxed cycle `z_R` -/
  zR : CR.X 1
  /-- `d z_R = 0` -/
  hzR : CR.d 1 2 rfl zR = 0
  /-- the primitive cycle `z_P` -/
  zP : CP.X 1
  /-- `d z_P = 0` -/
  hzP : CP.d 1 2 rfl zP = 0
  /-- the relaxed functional `λ_R` -/
  lamR : CR.X 2 →ₗ[F] F
  /-- `λ_R ∘ d = 0` -/
  hlamR : lamR ∘ₗ CR.d 1 2 rfl = 0
  /-- the primitive functional `λ_P` -/
  lamP : CP.X 2 →ₗ[F] F
  /-- `λ_P ∘ d = 0` -/
  hlamP : lamP ∘ₗ CP.d 1 2 rfl = 0

attribute [instance] SupportTriangle.fintypeN SupportTriangle.decEqN

namespace SupportTriangle

variable {F : Type} [Field F] (S : SupportTriangle F)

/-- The full-condition model of the relaxed complex (tex 5398–5424). Kind: definition. -/
abbrev model : FullPreComplex F := relModel S.E S.R S.RQ S.b1 S.b2

/-- The retract of the relaxed complex onto its model (tex 5398–5424). Kind: definition. -/
abbrev retract : GRetract S.CR S.model.toGCx := relRetract S.E S.R S.RQ S.b1 S.b2 S.hQ'

/-- The model of the relaxed cycle, `p z_R` (tex 4166–4170). Kind: definition. -/
def zRv : S.model.D1 ⊕ S.model.N → F := S.retract.p.f 1 1 rfl S.zR

/-- The model of the relaxed functional, `λ_R ∘ i_R` (tex 4166–4172). Kind: definition. -/
def lamRv : S.model.D2 ⊕ S.model.N → F :=
  funVec (ι := S.model.D2 ⊕ S.model.N) (S.lamR ∘ₗ S.retract.i.f 2 2 rfl)

/-- The model of the primitive cycle, `p z_P` (tex 4166–4170). Kind: definition. -/
def zPv : Fin S.D.m0 ⊕ Unit ⊕ Fin S.D.m1 → F := S.R.p.f 1 1 rfl S.zP

/-- The model of the primitive functional, `λ_P ∘ i_D` (tex 4166–4172). Kind: definition. -/
def lamPv : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2 → F :=
  funVec (ι := Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2) (S.lamP ∘ₗ S.R.i.f 2 2 rfl)

/-- The model relaxed cycle is a cycle. (tex 4166–4170) Kind: PROVED. -/
theorem zRv_cycle : S.model.toFour.d1 *ᵥ S.zRv = 0 :=
  retract_p_cycle S.retract (rfl : (1 : ℤ) + 1 = 2) S.hzR

/-- The model relaxed functional is closed. (tex 4166–4172) Kind: PROVED. -/
theorem lamRv_closed : S.lamRv ᵥ* S.model.toFour.d1 = 0 :=
  funVec_vecMul_eq_zero _ S.model.toFour.d1
    (retract_closed_comp_i S.retract (rfl : (1 : ℤ) + 1 = 2) S.lamR S.hlamR)

/-- The model primitive cycle is a cycle. (tex 4166–4170) Kind: PROVED. -/
theorem zPv_cycle : S.D.toFour.d1 *ᵥ S.zPv = 0 :=
  retract_p_cycle S.R (rfl : (1 : ℤ) + 1 = 2) S.hzP

/-- The model primitive functional is closed. (tex 4166–4172) Kind: PROVED. -/
theorem lamPv_closed : S.lamPv ᵥ* S.D.toFour.d1 = 0 :=
  funVec_vecMul_eq_zero _ S.D.toFour.d1
    (retract_closed_comp_i S.R (rfl : (1 : ℤ) + 1 = 2) S.lamP S.hlamP)

/-- **The primitive coordinate** `u_prim`: the Knudsen–Mumford coordinate of the model `D` of
`C_P` at the transported cycle and functional (tex 3877–3892, 4159–4188). Kind: definition. -/
def primCoord : F :=
  kmCoord S.D.toFour S.zPv S.lamPv S.zPv_cycle S.lamPv_closed (σBlock S.D.m0 S.D.m1 S.D.m2)

/-- **The relaxed coordinate** `u_rel`: the Knudsen–Mumford coordinate of the full-condition
model of `C_R` at the transported cycle and functional (tex 3877–3892, 4159–4188).
Kind: definition. -/
def relCoord : F :=
  kmCoord S.model.toFour S.zRv S.lamRv S.zRv_cycle S.lamRv_closed
    (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N)

/-- **The unit condition of the step** (tex 4178–4182): if the new block is the two-place block
and `l_q ≠ 0`, then `det B = q⁴ l_q` is a unit. Kind: PROVED. -/
theorem isUnit_relModel_det {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0) (e : S.N ≃ Fin 2 ⊕ Fin 2)
    (he : LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e) :
    IsUnit S.model.B.det := by
  have h1 : S.model.B.det = ((twoPlaceBlock Fr q zq zqi).submatrix e e).det :=
    congrArg Matrix.det ((relModel_B S.E S.R S.RQ S.b1 S.b2).trans he)
  have h2 : ((twoPlaceBlock Fr q zq zqi).submatrix e e).det =
      q ^ 4 * quotientFactor Fr qi zq zqi := by
    rw [det_submatrix_equiv_self, det_twoPlaceBlock, quotientDet_eq zq zqi hq ha hd]
  rw [h1, h2]
  exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero 4 (left_ne_zero_of_mul_eq_one hq)) hl)

/-- The old cycle `(p z_P, 0)` in the coordinates of the model (tex 4166–4170).
Kind: definition. -/
def zPext : S.model.D1 ⊕ S.model.N → F := Sum.elim S.zPv 0

/-- **The norm identity in model coordinates** (tex 4169–4170): if `z_R = c i(z_P) + d b`, the
model relaxed cycle is `c (p z_P, 0)` plus a model boundary. Kind: PROVED. -/
theorem zRv_eq (c : F) (b : S.CR.X 0)
    (hb : S.zR = c • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b) :
    S.zRv = c • S.zPext + S.model.toFour.d0 *ᵥ (S.retract.p.f 0 0 rfl b) := by
  have h1 : S.retract.p.f 1 1 rfl (S.E.i.f 1 1 rfl S.zP) = S.zPext :=
    relRetract_p_i_one S.E S.R S.RQ S.b1 S.b2 S.hQ' S.zP
  have h2 : S.retract.p.f 1 1 rfl (S.CR.d 0 1 rfl b) =
      S.model.toGCx.d 0 1 rfl (S.retract.p.f 0 0 rfl b) :=
    GRetract.p_d S.retract 0 1 rfl b
  have h3 : S.retract.p.f 1 1 rfl S.zR = S.retract.p.f 1 1 rfl
      (c • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b) := congrArg _ hb
  rw [map_add, map_smul, h1, h2] at h3
  exact h3

/-- The old cycle `(p z_P, 0)` is a cycle of the model (`T = 0`). (tex 4166–4170)
Kind: PROVED. -/
theorem zPext_cycle : S.model.toFour.d1 *ᵥ S.zPext = 0 := by
  have hi : S.CR.d 1 2 rfl (S.E.i.f 1 1 rfl S.zP) = 0 := by
    rw [← S.E.i_d 1 2 rfl, S.hzP, map_zero]
  have h := retract_p_cycle S.retract (rfl : (1 : ℤ) + 1 = 2) hi
  have h1 : S.retract.p.f 1 1 rfl (S.E.i.f 1 1 rfl S.zP) = S.zPext :=
    relRetract_p_i_one S.E S.R S.RQ S.b1 S.b2 S.hQ' S.zP
  rw [h1] at h
  exact h

/-- Multiples of the old cycle are cycles of the model. (tex 4166–4170) Kind: PROVED. -/
theorem cycle_smul_zPext (c : F) : S.model.toFour.d1 *ᵥ (c • S.zPext) = 0 := by
  rw [mulVec_smul, S.zPext_cycle, smul_zero]

/-- **The functional relation in model coordinates** (tex 4166–4172): if `λ_R ∘ i = c λ_P`, the
model relaxed functional restricts to `c` times the model primitive functional. Kind: PROVED. -/
theorem lamRv_inl (c : F) (h : S.lamR ∘ₗ S.E.i.f 2 2 rfl = c • S.lamP) :
    S.lamRv ∘ Sum.inl = c • S.lamPv := by
  have e := funVec_relRetract_inl S.E S.R S.RQ S.b1 S.b2 S.hQ' S.lamR
  funext j
  refine (congrFun e j).trans ?_
  change (S.lamR ∘ₗ S.E.i.f 2 2 rfl)
      (S.R.i.f 2 2 rfl (Pi.single j 1 : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2 → F)) =
    c * S.lamP (S.R.i.f 2 2 rfl (Pi.single j 1 : Fin S.D.m1 ⊕ Unit ⊕ Fin S.D.m2 → F))
  rw [h]
  rfl

/-- The primitive coordinate is the coordinate of the cancelled model. (tex 5424–5425)
Kind: PROVED. -/
theorem primCoord_eq_cancel (hB : IsUnit S.model.B.det)
    (hzP' : (S.model.cancel hB).toFour.d1 *ᵥ S.zPv = 0)
    (hlamP' : S.lamPv ᵥ* (S.model.cancel hB).toFour.d1 = 0) :
    S.primCoord = kmCoord (S.model.cancel hB).toFour S.zPv S.lamPv hzP' hlamP'
      (σBlock S.model.m0 S.model.m1 S.model.m2) := by
  have h4 : (S.model.cancel hB).toFour = S.D.toFour :=
    cancel_relModel_toFour S.E S.R S.RQ S.b1 S.b2 hB
  unfold primCoord
  revert hzP' hlamP'
  rw [h4]
  intro hzP' hlamP'
  rfl

/-- **The relaxation step from the actual support triangle, model shape** (tex 4157–4194,
5398–5424): with the new block the two-place block (`hBe`), `l_q ≠ 0`, the norm identity with its
retained boundary (`hzR`), and the functional relation in `KmStep`'s shape on the model vectors
(`hlamRv`), the step is a `KmStep` at the coordinates of the models. Kind: PROVED. -/
theorem kmStep_of_supportTriangle_model {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = pointFactor a zq zqi • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamRv : S.lamRv ∘ Sum.inl = pointFactor a zq zqi • S.lamPv) :
    KmStep Fr q a zq zqi S.relCoord S.primCoord := by
  obtain ⟨e, he⟩ := hBe
  obtain ⟨b, hb⟩ := hzR
  have hB : IsUnit S.model.B.det := S.isUnit_relModel_det hq ha hd hl e he
  set c := pointFactor a zq zqi with hc
  have hz' := S.cycle_smul_zPext c
  have hzRv := S.zRv_eq c b hb
  have hcoordR : S.relCoord = kmCoord S.model.toFour (c • S.zPext) S.lamRv hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) := by
    unfold relCoord
    rw [kmCoord_congr S.model.toFour S.zRv_cycle
      (cycle_add_boundary S.model.toFour hz' (S.retract.p.f 0 0 rfl b)) S.lamRv_closed
      S.lamRv_closed hzRv rfl]
    exact kmCoord_add_boundary S.model.toFour hz' S.lamRv_closed
      (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) _
  have h4 : (S.model.cancel hB).toFour = S.D.toFour :=
    cancel_relModel_toFour S.E S.R S.RQ S.b1 S.b2 hB
  have hzP' : (S.model.cancel hB).toFour.d1 *ᵥ S.zPv = 0 := by
    rw [h4]
    exact S.zPv_cycle
  have hlamP' : S.lamPv ᵥ* (S.model.cancel hB).toFour.d1 = 0 := by
    rw [h4]
    exact S.lamPv_closed
  exact ⟨S.model, hB, ⟨e, (relModel_B S.E S.R S.RQ S.b1 S.b2).trans he⟩, c • S.zPext, S.lamRv,
    hz', S.lamRv_closed, S.zPv, S.lamPv, hzP', hlamP', rfl, hlamRv, hcoordR,
    S.primCoord_eq_cancel hB hzP' hlamP'⟩

/-- **The relaxation step from the actual support triangle** (tex 4157–4194, 5398–5424): with the
new block the two-place block (`hBe`), `l_q ≠ 0`, the norm identity with its retained boundary
(`hzR`) and the functional relation `λ_R ∘ i = e_q λ_P` (`hlamR`), the step is a `KmStep` at the
torsion coordinates of the models of `C_R` and `C_P`. Kind: PROVED. -/
theorem kmStep_of_supportTriangle {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = pointFactor a zq zqi • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : S.lamR ∘ₗ S.E.i.f 2 2 rfl = pointFactor a zq zqi • S.lamP) :
    KmStep Fr q a zq zqi S.relCoord S.primCoord :=
  S.kmStep_of_supportTriangle_model hq ha hd hl hBe hzR (S.lamRv_inl _ hlamR)

/-- **(4.7) at one unused prime for the actual support triangle** (tex 4185–4188):
`l_q u_rel = e_q² q⁻⁴ u_prim` for the torsion coordinates of the models. Kind: PROVED. -/
theorem h47_of_supportTriangle {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q)
    (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hBe : ∃ e : S.N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ b : S.CR.X 0, S.zR = pointFactor a zq zqi • S.E.i.f 1 1 rfl S.zP + S.CR.d 0 1 rfl b)
    (hlamR : S.lamR ∘ₗ S.E.i.f 2 2 rfl = pointFactor a zq zqi • S.lamP) :
    quotientFactor Fr qi zq zqi * S.relCoord =
      pointFactor a zq zqi ^ 2 * qi ^ 4 * S.primCoord :=
  (S.kmStep_of_supportTriangle hq ha hd hl hBe hzR hlamR).h47 hq ha hd

end SupportTriangle

end ZInQ.Manuscript.RC.Wiring

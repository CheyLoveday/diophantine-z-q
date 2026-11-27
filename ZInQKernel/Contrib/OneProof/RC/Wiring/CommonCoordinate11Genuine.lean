import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Selmer
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Block

/-!
# The genuine support triangle: `C_P ⊂ C_R` are the Selmer complexes of the stage

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4194), with
the support comparisons (tex 3470–3496) and the unramified condition (tex 3471–3487).

`supportTriangle_iff_h47` (round six) showed that a `SupportTriangle` has content only once its
complexes are the genuine ones. This file pins them.

* `SupportTriangle.ofSelmer D EU …`: for Selmer data `D` and a split inclusion of local
  conditions `EU : U' ⊂ U`, the support triangle with `C_P = selCx (selRestrict D EU.i)`,
  `C_R = selCx D` and inclusion `changeMap D EU.i` (`ofSelmer_CP`, `ofSelmer_CR`,
  `ofSelmer_E_i`, all definitional), whose quotient retraction is a retraction of the LOCAL
  quotient `U / U'` (`selQuotRetract`).
* `SupportTriangle.atPlace Dold res_q EUq …`: the support triangle at one new place `q`: the
  relaxed data `relaxedAt Dold res_q` (full condition `L_q` at `q`), the primitive data
  `addPlace Dold res_q ι_q` (`atPlace_CP`: the condition `U_q` at `q`, by
  `selRestrict_relaxedAt`), and the quotient the local quotient `L_q / U_q`.
* **`genuineSupportTriangle`**: the genuine instance — old Selmer data `selData` of the
  stage (global continuous cochains of `G_{K,S}`, the old genuine conditions at the old places),
  the new place `w ∈ S` with `L_w = C^•_cont(G_{K_w}, M)` (`genuineLq`), the genuine restriction,
  and the genuine unramified condition `ι_w : [X --Φ_w−1--> X] → L_w` (`genuineUq`,
  `genuineιq`, lane RC30): `genuineSupportTriangle_CP`, `_CR`, `_E_i`.
* `hzR_of_components`: the norm identity `z_R = e i(z_P) + d b` in the Selmer complex from its
  three components (global cochains — the shape of the cochain-level norm identity on global
  cochains —, local conditions, local homotopies).
* `kmStep_ofSelmer_retention`: lane RC30's `hlamR_of_retention` applies verbatim, with
  `changeMap D EU.i = S.E.i` (`ofSelmer_E_i`) and `ψ = id` (coefficients a field), giving the
  step with only `hBe`, `hzR` and the units left.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (changeMap idGHom)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (RetainedPairing pairedFun twoPlaceBlock)
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor)
open ZInQ.Manuscript.RC.SelmerComplex (prodCx)

/-! ### The support triangle of Selmer complexes -/

section OfSelmer

variable {F : Type} [Field F]

/-- **The support triangle of Selmer complexes** (tex 4157–4194, 3489–3494): `C_P =
selCx (selRestrict D EU.i)`, `C_R = selCx D`, the inclusion `changeMap D EU.i`, a block model of
`C_P`, a retraction of the local quotient `U / U'` onto a model `Q'` with bases, and the actual
cycles and closed functionals. Kind: definition. -/
def SupportTriangle.ofSelmer (D : SelData F) {U' : GCx F} (EU : SplitInclusion U' D.U)
    (Dm : BlockComplex F) (R : GRetract (selCx (selRestrict D EU.i)) Dm.toGCx) {Q' : GCx F}
    (RW : GRetract EU.quotientCx Q') (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
    (zR : (selCx D).X 1) (hzR : (selCx D).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict D EU.i)).X 1) (hzP : (selCx (selRestrict D EU.i)).d 1 2 rfl zP = 0)
    (lamR : (selCx D).X 2 →ₗ[F] F) (hlamR : lamR ∘ₗ (selCx D).d 1 2 rfl = 0)
    (lamP : (selCx (selRestrict D EU.i)).X 2 →ₗ[F] F)
    (hlamP : lamP ∘ₗ (selCx (selRestrict D EU.i)).d 1 2 rfl = 0) : SupportTriangle F where
  CP := selCx (selRestrict D EU.i)
  CR := selCx D
  E := selSplit D EU
  D := Dm
  R := R
  Q' := Q'
  RQ := selQuotRetract D EU RW
  hQ' := hQ'
  N := N
  b1 := b1
  b2 := b2
  zR := zR
  hzR := hzR
  zP := zP
  hzP := hzP
  lamR := lamR
  hlamR := hlamR
  lamP := lamP
  hlamP := hlamP

variable (D : SelData F) {U' : GCx F} (EU : SplitInclusion U' D.U) (Dm : BlockComplex F)
  (R : GRetract (selCx (selRestrict D EU.i)) Dm.toGCx) {Q' : GCx F}
  (RW : GRetract EU.quotientCx Q') (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
  {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
  (zR : (selCx D).X 1) (hzR : (selCx D).d 1 2 rfl zR = 0)
  (zP : (selCx (selRestrict D EU.i)).X 1) (hzP : (selCx (selRestrict D EU.i)).d 1 2 rfl zP = 0)
  (lamR : (selCx D).X 2 →ₗ[F] F) (hlamR : lamR ∘ₗ (selCx D).d 1 2 rfl = 0)
  (lamP : (selCx (selRestrict D EU.i)).X 2 →ₗ[F] F)
  (hlamP : lamP ∘ₗ (selCx (selRestrict D EU.i)).d 1 2 rfl = 0)

/-- **The primitive complex is the Selmer complex with the condition `U'`** (tex 4157–4166).
Kind: PROVED (definitional). -/
theorem ofSelmer_CP : (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR zP hzP lamR hlamR
    lamP hlamP).CP = selCx (selRestrict D EU.i) :=
  rfl

/-- **The relaxed complex is the Selmer complex with the condition `U`** (tex 4157–4166).
Kind: PROVED (definitional). -/
theorem ofSelmer_CR : (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR zP hzP lamR hlamR
    lamP hlamP).CR = selCx D :=
  rfl

/-- **The inclusion of the triangle is the primitive-to-relaxed map** `changeMap D EU.i`
(tex 4157–4166). Kind: PROVED (definitional). -/
theorem ofSelmer_E_i : (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR zP hzP lamR hlamR
    lamP hlamP).E.i = changeMap D EU.i :=
  rfl

/-- **The quotient retraction of the triangle is the retraction of the local quotient**,
transported along `U / U' ≃ C_R / C_P` (tex 3489–3494). Kind: PROVED (definitional). -/
theorem ofSelmer_RQ : (SupportTriangle.ofSelmer D EU Dm R RW hQ' b1 b2 zR hzR zP hzP lamR hlamR
    lamP hlamP).RQ = selQuotRetract D EU RW :=
  rfl

end OfSelmer

/-! ### The norm identity from its components -/

section Components

variable {S : Type} [CommRing S] (D : SelData S) {U' : GCx S} (f : GHom U' D.U)

/-- The global component `a` of a cochain `(a, u, x)` of the primitive Selmer complex
(tex 4169–4170). Kind: definition. -/
def primG (n : ℤ) (c : (selCx (selRestrict D f)).X n) : D.G.X n := c.1

/-- The local-homotopy component `x` of a cochain `(a, u, x)` of the primitive Selmer complex
(tex 4169–4170). Kind: definition. -/
def primL (n : ℤ) (c : (selCx (selRestrict D f)).X n) : D.L.X (n - 1) := c.2.2

/-- The local-condition component `u` of a cochain `(a, u, x)` of the primitive Selmer complex
(tex 4169–4170). Kind: definition. -/
def primU (n : ℤ) (c : (selCx (selRestrict D f)).X n) : U'.X n := c.2.1

/-- **The norm identity in the Selmer complex from its three components** (tex 4169–4170: "the
actual norm identity is `z_R = e_q i(z_P)`, with its retained boundary"). A degree-one element of
`C = G ⊕ U ⊕ L[−1]` is a triple; the identity `z_R = e i(z_P) + d(b_G, b_U, b_L)` holds as soon as
it holds on the global cochains (`hG`: the cochain-level norm identity with retained boundary
`b_G`), on the local conditions (`hU`) and on the local homotopies (`hL`). Kind: PROVED. -/
theorem hzR_of_components (zR : (selCx D).X 1) (zP : (selCx (selRestrict D f)).X 1) (e : S)
    (bG : D.G.X 0) (bU : D.U.X 0) (bL : D.L.X (0 - 1))
    (hG : zR.1 = e • primG D f 1 zP + D.G.d 0 1 rfl bG)
    (hU : zR.2.1 = e • f.f 1 1 rfl (primU D f 1 zP) + D.U.d 0 1 rfl bU)
    (hL : zR.2.2 = e • primL D f 1 zP + (D.res.f 0 (1 - 1) (by omega) bG -
      D.ι.f 0 (1 - 1) (by omega) bU - D.L.d (0 - 1) (1 - 1) (by omega) bL)) :
    zR = e • (changeMap D f).f 1 1 rfl zP + (selCx D).d 0 1 rfl ((bG, bU, bL) : selT D 0) := by
  change zR = ((e • primG D f 1 zP, e • f.f 1 1 rfl (primU D f 1 zP), e • primL D f 1 zP) :
      selT D 1) +
    ((D.G.d 0 1 rfl bG, D.U.d 0 1 rfl bU, D.res.f 0 (1 - 1) (by omega) bG -
      D.ι.f 0 (1 - 1) (by omega) bU - D.L.d (0 - 1) (1 - 1) (by omega) bL) : selT D 1)
  exact Prod.ext hG (Prod.ext hU hL)

/-- **The global component of the primitive-to-relaxed map is the identity** (tex 4157–4166):
`i(a, u, x) = (a, f u, x)`, so the global component of `e i(z_P)` is `e a_P`; a cochain-level
norm identity `a_R = e a_P + d b` on global cochains is the global component of `hzR`.
Kind: PROVED (definitional). -/
theorem changeMap_global (zP : (selCx (selRestrict D f)).X 1) :
    ((changeMap D f).f 1 1 rfl zP).1 = primG D f 1 zP :=
  rfl

end Components

/-! ### Lane RC30's functional relation applies verbatim -/

section Retention

variable {F : Type} [Field F]

/-- The image under a retract inclusion of a basis vector of the minimal model is a cocycle
(tex 4166–4172). Kind: PROVED. -/
theorem retract_i_minBlock_cocycle {X : GCx F} (R : GRetract X (minBlock F).toGCx)
    (v : (minBlock F).toGCx.X 2) : X.d 2 3 rfl (R.i.f 2 2 rfl v) = 0 := by
  rw [← GRetract.i_d R 2 3 rfl v, minBlock_toGCx_d, map_zero]

/-- **The paired functional is closed** (tex 4170–4177): for a cocycle `z` and a trace killing
coboundaries, `λ = β(z, ·)` kills `d(C¹)`. Kind: PROVED. -/
theorem pairedFun_closed {D D' : SelData F} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[F] F) (htr : ∀ x, tr ((coneCx Q.resE).d 2 3 rfl x) = 0)
    (z : (selCx D).X 1) (hz : (selCx D).d 1 2 rfl z = 0) :
    pairedFun Q tr z ∘ₗ (selCx D').d 1 2 rfl = 0 := by
  apply LinearMap.ext
  intro c
  have h := pairedFun_add_coboundary Q tr htr z hz 0 c
  rw [zero_add, map_zero] at h
  exact h

/-- **The functional relation of lane RC30 in the model coordinates of the support triangle**
(tex 4163–4177): for the support triangle of Selmer complexes with the minimal primitive model,
the relaxed and primitive functionals `λ_R = β_R(z_S, ·)`, `λ_P = β_P(z_{P⊥}, ·)` of genuine
retention data with the paired strict lift `j z_S = e z_{P⊥} + d b` satisfy KmStep's relation
`λ_R^mod ∘ inl = e λ_P^mod`: lane RC30's `hlamR_of_retention`, applied verbatim with
`φ_R j = i_R(e_j)`, `φ_P i = i_D(e_i)` (cocycles, the model being minimal), `changeMap D EU.i =
i` and `ψ = id`. Kind: PROVED. -/
theorem lamRv_inl_of_retention (D : SelData F) {U' : GCx F} (EU : SplitInclusion U' D.U)
    {DPp : SelData F} {US : GCx F} {fS : GHom US DPp.U} {Lq Uq : GCx F} {ιq : GHom Uq Lq}
    (PR : PlaceRetentionG D DPp EU.i fS Lq Uq ιq)
    (tr : (coneCx PR.toRetainedPairing.QP.resE).X 3 →ₗ[F] F)
    (htr : ∀ x, tr ((coneCx PR.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0)
    (zPp : (selCx DPp).X 1) (hzPp : (selCx DPp).d 1 2 rfl zPp = 0) (e : F) (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b)
    (R : GRetract (selCx (selRestrict D EU.i)) (minBlock F).toGCx) {Q' : GCx F}
    (RW : GRetract EU.quotientCx Q') (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
    (zR : (selCx D).X 1) (hzR : (selCx D).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict D EU.i)).X 1)
    (hzP : (selCx (selRestrict D EU.i)).d 1 2 rfl zP = 0) :
    (SupportTriangle.ofSelmer D EU (minBlock F) R RW hQ' b1 b2 zR hzR zP hzP
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).lamRv ∘ Sum.inl =
      e • (SupportTriangle.ofSelmer D EU (minBlock F) R RW hQ' b1 b2 zR hzR zP hzP
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).lamPv := by
  set T := SupportTriangle.ofSelmer D EU (minBlock F) R RW hQ' b1 b2 zR hzR zP hzP
    (pairedFun PR.toRetainedPairing.QR tr zS)
    (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
    (pairedFun PR.toRetainedPairing.QP tr zPp)
    (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp) with hT
  have h := hlamR_of_retention (K := F) (α := T.model.D2) (κ := T.model.N) PR tr htr zS zPp e b
    hlift (fun i => R.i.f 2 2 rfl
      ((Pi.single i (1 : F) : Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2 → F) :
        (minBlock F).toGCx.X 2))
    (fun i => retract_i_minBlock_cocycle R _)
    (fun j => T.retract.i.f 2 2 rfl
      ((Pi.single j (1 : F) : T.model.D2 ⊕ T.model.N → F) : T.model.toGCx.X 2))
    (fun i => by
      change T.retract.i.f 2 2 rfl
        ((Pi.single (Sum.inl i) (1 : F) : T.model.D2 ⊕ T.model.N → F) : T.model.toGCx.X 2) =
        T.E.i.f 2 2 rfl _
      rw [single_inl_eq]
      exact relRetract_i_two_inl T.E T.R T.RQ T.b1 T.b2 T.hQ' _)
    (RingHom.id F) T.lamRv T.lamPv (fun j => rfl) (fun i => rfl)
  exact h

/-- **The relaxation step of the support triangle of Selmer complexes with genuine retention
data** (tex 4157–4194): with the minimal primitive model, the functionals of lane RC30's retention
data, the paired strict lift `hlift` with `e = e_q`, the new block `hBe`, the norm identity
`hzR` and `l_q ≠ 0`, the step is a `KmStep` at the coordinates of the models. Only `hBe`,
`hzR`, `hlift` and the units remain as hypotheses; the functional relation is lane RC30's
theorem. Kind: PROVED. -/
theorem kmStep_ofSelmer_retention (D : SelData F) {U' : GCx F} (EU : SplitInclusion U' D.U)
    {DPp : SelData F} {US : GCx F} {fS : GHom US DPp.U} {Lq Uq : GCx F} {ιq : GHom Uq Lq}
    (PR : PlaceRetentionG D DPp EU.i fS Lq Uq ιq)
    (tr : (coneCx PR.toRetainedPairing.QP.resE).X 3 →ₗ[F] F)
    (htr : ∀ x, tr ((coneCx PR.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0)
    (zPp : (selCx DPp).X 1) (hzPp : (selCx DPp).d 1 2 rfl zPp = 0) (b : (selCx DPp).X 0)
    (R : GRetract (selCx (selRestrict D EU.i)) (minBlock F).toGCx) {Q' : GCx F}
    (RW : GRetract EU.quotientCx Q') (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
    (zR : (selCx D).X 1) (hzR0 : (selCx D).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict D EU.i)).X 1)
    (hzP0 : (selCx (selRestrict D EU.i)).d 1 2 rfl zP = 0)
    {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F} (hq : q * qi = 1) (ha : Fr.trace = a)
    (hd : Fr.det = q) (hl : quotientFactor Fr qi zq zqi ≠ 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS =
      pointFactor a zq zqi • zPp + (selCx DPp).d 0 1 rfl b)
    (hBe : ∃ e : N ≃ Fin 2 ⊕ Fin 2, LinearMap.toMatrix b1 b2 (Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (hzR : ∃ c : (selCx D).X 0,
      zR = pointFactor a zq zqi • (changeMap D EU.i).f 1 1 rfl zP + (selCx D).d 0 1 rfl c) :
    KmStep Fr q a zq zqi
      (SupportTriangle.ofSelmer D EU (minBlock F) R RW hQ' b1 b2 zR hzR0 zP hzP0
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).relCoord
      (SupportTriangle.ofSelmer D EU (minBlock F) R RW hQ' b1 b2 zR hzR0 zP hzP0
        (pairedFun PR.toRetainedPairing.QR tr zS)
        (pairedFun_closed PR.toRetainedPairing.QR tr htr zS hzS)
        (pairedFun PR.toRetainedPairing.QP tr zPp)
        (pairedFun_closed PR.toRetainedPairing.QP tr htr zPp hzPp)).primCoord :=
  SupportTriangle.kmStep_of_supportTriangle_model _ hq ha hd hl hBe hzR
    (lamRv_inl_of_retention D EU PR tr htr zS hzS zPp hzPp (pointFactor a zq zqi) b hlift R RW
      hQ' b1 b2 zR hzR0 zP hzP0)

end Retention

/-! ### The support triangle at one new place -/

section AtPlace

variable {F : Type} [Field F] (Dold : SelData F) {Lq : GCx F} (resq : GHom Dold.G Lq)
  {Uq : GCx F} (EUq : SplitInclusion Uq Lq)

/-- **The support triangle at one new place `q`** (tex 4157–4194, 3480–3496): the relaxed data
`relaxedAt Dold res_q` (the full condition `L_q` at `q`), the primitive data with the condition
`U_q` (through the split inclusion `EUq : U_q ⊂ L_q`), a block model of `C_P`, a retraction of
the LOCAL quotient `L_q / U_q` onto a model `Q'` with bases, and the actual classes.
Kind: definition. -/
def SupportTriangle.atPlace (Dm : BlockComplex F)
    (R : GRetract (selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i)))
      Dm.toGCx) {Q' : GCx F} (RWq : GRetract EUq.quotientCx Q')
    (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
    (zR : (selCx (relaxedAt Dold resq)).X 1) (hzR : (selCx (relaxedAt Dold resq)).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i))).X 1)
    (hzP : (selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i))).d 1 2 rfl zP =
      0)
    (lamR : (selCx (relaxedAt Dold resq)).X 2 →ₗ[F] F)
    (hlamR : lamR ∘ₗ (selCx (relaxedAt Dold resq)).d 1 2 rfl = 0)
    (lamP : (selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i))).X 2 →ₗ[F] F)
    (hlamP : lamP ∘ₗ
      (selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i))).d 1 2 rfl = 0) :
    SupportTriangle F :=
  SupportTriangle.ofSelmer (relaxedAt Dold resq) (newSplit Dold resq EUq) Dm R
    (newQuotRetract Dold resq EUq RWq) hQ' b1 b2 zR hzR zP hzP lamR hlamR lamP hlamP

/-- **The primitive complex of the triangle at `q` is the Selmer complex with the condition
`U_q` at `q`** (tex 4157–4166, 3483–3487): `C_P = selCx (addPlace Dold res_q i_q)`.
Kind: PROVED. -/
theorem atPlace_CP_eq :
    selCx (selRestrict (relaxedAt Dold resq) (primToRel Dold resq EUq.i)) =
      selCx (addPlace Dold resq EUq.i) :=
  congrArg selCx (selRestrict_relaxedAt Dold resq EUq.i)

/-- **The global quotient of the triangle at `q` is the local quotient at `q`**, degreewise
(tex 3489–3494: "replacing the unramified condition by the full condition then gives the singular
quotient"): `L_q / U_q ≃ C_R / C_P`, through the quotient of the local conditions.
Kind: definition. -/
def atPlaceQEquiv (n : ℤ) :
    EUq.quotientCx.X n ≃ₗ[F] (selSplit (relaxedAt Dold resq) (newSplit Dold resq EUq)).Qc n :=
  (newQEquiv Dold resq EUq n).trans (selQEquiv (relaxedAt Dold resq) (newSplit Dold resq EUq) n)

/-- The global-to-local identification of the quotient commutes with the differentials
(tex 3489–3494). Kind: PROVED. -/
theorem atPlaceQEquiv_comm (a b : ℤ) (h : a + 1 = b) (w : EUq.quotientCx.X a) :
    (selSplit (relaxedAt Dold resq) (newSplit Dold resq EUq)).quotientCx.d a b h
        (atPlaceQEquiv Dold resq EUq a w) =
      atPlaceQEquiv Dold resq EUq b (EUq.quotientCx.d a b h w) :=
  (selQEquiv_comm (relaxedAt Dold resq) (newSplit Dold resq EUq) a b h
    (newQEquiv Dold resq EUq a w)).trans
    (congrArg (selQEquiv (relaxedAt Dold resq) (newSplit Dold resq EUq) b)
      (newQEquiv_comm Dold resq EUq a b h w))

end AtPlace

/-! ### The genuine support triangle -/

section Genuine

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The genuine old Selmer data of the stage** (tex 3455–3463, 4385–4388; the convention of the
stage family `ActualStageFamily.datum`): global continuous cochains of `G_{K,S}` on the enlarged
support `S`, the old places `S₀` with their local groups `G_{K_v}` and genuine local conditions
`Δ`. Kind: definition. -/
abbrev genuineOld (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) : SelData k :=
  selData k (GKS K S) (fun v : Places K S₀ => Gloc K v.1) (fun v => locMap K S v.1) M Δ

/-- **The genuine restriction to the new place** `w`: restriction of continuous cochains along
the localization `p_w : G_{K_w} → G_{K,S}` (Nekovář 5.1; tex 3455–3463). Kind: definition. -/
abbrev genuineRes (w : Places K S) : GHom (globalCx k (GKS K S) M) (genuineLq K S k M w) :=
  natHom (resCochains (k := k) (M := M) (locMap K S w.1))

/-- **The genuine relaxed Selmer data at `w`**: the full condition `C^•_cont(G_{K_w}, M)` at
the new place (tex 4157–4166). Kind: definition. -/
abbrev genuineRelaxed (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) (w : Places K S) : SelData k :=
  relaxedAt (genuineOld K S₀ S k M Δ) (genuineRes K S k M w)

/-- **The genuine primitive Selmer data at `w`**: the genuine unramified condition
`[X --Φ_w−1--> X] → C^•_cont(G_{K_w}, M)` (`genuineιq`, lane RC30) at the new place
(tex 3471–3487, 4157–4166). Kind: definition. -/
abbrev genuinePrimitive (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    SelData k :=
  addPlace (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) (genuineιq K S k M w X f hf)

variable (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M) (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
  (EUq : SplitInclusion (genuineUq K S k w X) (genuineLq K S k M w))

/-- **The genuine support triangle at the new place `w`** (tex 4157–4194): `C_R` the genuine
relaxed Selmer complex (full condition at `w`), `C_P` the genuine primitive Selmer complex
(through a split inclusion `EUq` of the genuine unramified condition into the genuine local
complex at `w`), `i` the genuine primitive-to-relaxed map, a block model of `C_P`, a retraction
of the genuine local quotient `C^•_cont(G_{K_w}, M) / [X → X]` onto a model `Q'` (for the two
places above a split prime, the two singular blocks; lane RC31's tame local quotient), and the
actual classes as inputs. Kind: definition. -/
def genuineSupportTriangle (Dm : BlockComplex k)
    (R : GRetract (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i))) Dm.toGCx)
    {Q' : GCx k} (RWq : GRetract EUq.quotientCx Q')
    (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))
    {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N k (Q'.X 1)) (b2 : Basis N k (Q'.X 2))
    (zR : (selCx (genuineRelaxed K S₀ S k M Δ w)).X 1)
    (hzR : (selCx (genuineRelaxed K S₀ S k M Δ w)).d 1 2 rfl zR = 0)
    (zP : (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i))).X 1)
    (hzP : (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i))).d 1 2 rfl zP = 0)
    (lamR : (selCx (genuineRelaxed K S₀ S k M Δ w)).X 2 →ₗ[k] k)
    (hlamR : lamR ∘ₗ (selCx (genuineRelaxed K S₀ S k M Δ w)).d 1 2 rfl = 0)
    (lamP : (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i))).X 2 →ₗ[k] k)
    (hlamP : lamP ∘ₗ (selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
      (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i))).d 1 2 rfl = 0) :
    SupportTriangle k :=
  SupportTriangle.atPlace (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq Dm R RWq hQ' b1
    b2 zR hzR zP hzP lamR hlamR lamP hlamP

omit [TopologicalSpace k] in
/-- **Pinning, the relaxed complex**: `C_R` of the genuine triangle is the genuine Selmer complex
with the full condition at `w` (tex 4157–4166). Kind: PROVED (definitional). -/
theorem genuine_CR_eq :
    selCx (genuineRelaxed K S₀ S k M Δ w) =
      selCx (addPlace (genuineOld K S₀ S k M Δ) (genuineRes K S k M w)
        (idGHom (genuineLq K S k M w))) :=
  rfl

/-- **Pinning, the primitive complex**: when the split inclusion is the genuine inflation,
`C_P` of the genuine triangle is the genuine Selmer complex with the unramified condition at `w`
(tex 3471–3487, 4157–4166). Kind: PROVED. -/
theorem genuine_CP_eq [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hEU : EUq.i = genuineιq K S k M w X f hf) :
    selCx (selRestrict (genuineRelaxed K S₀ S k M Δ w)
        (primToRel (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq.i)) =
      selCx (genuinePrimitive K S₀ S k M Δ w X f hf) := by
  refine (atPlace_CP_eq (genuineOld K S₀ S k M Δ) (genuineRes K S k M w) EUq).trans ?_
  rw [hEU]

end Genuine

end ZInQ.Manuscript.RC.Wiring

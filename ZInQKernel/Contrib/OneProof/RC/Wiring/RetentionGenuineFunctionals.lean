import ZInQKernel.Contrib.OneProof.RC.Wiring.RetentionGenuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmCoordBilinear

/-!
# Theorem 5.3, lane RC30: `λ_R ∘ i = e_q λ_P` over genuine local cochains, and its consumers

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4157–4177): naturality of the cup
pairing (Nekovář, *Selmer complexes*, 6.4.1–6.4.3) gives `β_R(v, i w) = β_P(j v, w)`; the paired
strict lift `j z_S = e_q z_{P⊥}` then gives `λ_R ∘ i = e_q λ_P`. With the retention datum
`PlaceRetentionG` (`RetentionGenuine.lean`) the new place is arbitrary, so all statements below hold
for the genuine local cochains `L_q = C^•_cont(G_{K_q}, M)`, with no tame model.

* `PlaceRetentionG.pairedFunctional_natural`, `pairedFunctional_natural_genuine` (PROVED):
  `λ_R(i w) = e λ_P(w)` on cocycles `w` of `C_P`, for any new place and for the genuine one.
* Homotopy invariance on cohomology (PROVED): `pairedFun_add_coboundary` (`λ(w + d c) = λ(w)` for a
  cocycle `z`, from the Leibniz rule of the Selmer cup product), `homotopy_apply_cocycle` (homotopic
  chain maps differ on a cocycle by a coboundary), `PlaceRetentionG.pairedFun_model_eq` and
  `PlaceRetentionG.pairedFunctional_natural_model`: the relation in model coordinates, for chain
  maps `Φ_R : C_R^{mod} → C_R`, `Φ_P : C_P^{mod} → C_P` and a model map `i^{mod}` with
  `i^{mod} ≫ Φ_R ∼ Φ_P ≫ i` only up to homotopy, when `z_S` is a cocycle.
* `SelmerFunctionalsG` (definition; the RC53 group's `SelmerFunctionals` with the retention datum
  `PlaceRetentionG`, any index types): `SelmerFunctionalsG.restrict` (`w_R|old = e_q w_P`, PROVED),
  `SelmerFunctionals.toG` (PROVED), `selmerFunctionalsG_of_model` (PROVED: model coordinates).
* `NaturalStepG` (definition), `NaturalStepG.toActualStep`, `NaturalStep.toG` and
  `commonCoordinate_h47_of_naturalG` (RC0's field `h47`) (PROVED).
* The torsion-form relation of lane RC31's `KmStep` (PROVED): `hlamR_of_selmerFunctionalsG`,
  `hlamR_of_retention`, `hlamR_of_genuine` (no tame model; the genuine new place), and
  `kmStep_of_genuine` (`KmStep` with its relation `lam ∘ Sum.inl = e_q • lam_P` supplied by genuine
  retention data).
* Non-vacuity (PROVED): `selmerFunctionalsG_example`, `naturalStepG_example`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (FullPreComplex σFull σBlock)
open ZInQ.Contrib.CloudB3RC53.Torsion (kmCoord)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor IsClassFunctionalCoord)

universe u

/-- **The change of local condition** `D ↦ (G, U', L, res, ι ∘ f)` (definition; the RC53 group's
`restrictData` of `CloudB3RC53/SelmerDuality/SupportChange.lean`, by `rfl`; named here because in
this namespace `restrictData` is the skeleton's restriction of coordinate data). -/
abbrev selRestrict {S : Type u} [CommRing S] (D : SelData S) {U' : GCx S} (f : GHom U' D.U) :
    SelData S :=
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData D f

/-! ### Homotopy invariance of the paired functional on cohomology -/

section Invariance

variable {S : Type u} [CommRing S]

/-- **The paired functional of a cocycle kills coboundaries** (tex 3742–3749, 4170–4177; the
Leibniz rule of the Selmer cup product, the RC53 group's `selmerCupLeibniz_proof`): for a cocycle
`z ∈ C^1` and a trace killing coboundaries, `λ(w + d c) = λ(w)`. PROVED. -/
theorem pairedFun_add_coboundary {D D' : SelData S} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[S] S) (htr : ∀ x, tr ((coneCx Q.resE).d 2 3 rfl x) = 0)
    (z : (selCx D).X 1) (hz : (selCx D).d 1 2 rfl z = 0) (w : (selCx D').X 2)
    (c : (selCx D').X 1) :
    pairedFun Q tr z (w + (selCx D').d 1 2 rfl c) = pairedFun Q tr z w := by
  have hl := selmerCupLeibniz_proof S D D' Q 1 2 1 2 2 3 rfl rfl rfl rfl z c
  rw [hz] at hl
  erw [map_zero, LinearMap.zero_apply, zero_add] at hl
  have h0 := htr (selCup Q 1 1 2 rfl z c)
  erw [hl, map_zsmul, sgn_one, neg_one_smul, neg_eq_zero] at h0
  show tr (selCup Q 1 2 3 rfl z (w + (selCx D').d 1 2 rfl c)) = tr (selCup Q 1 2 3 rfl z w)
  erw [map_add, map_add, h0, add_zero]

/-- **Homotopic chain maps differ on a cocycle by a coboundary**: for a homotopy `h : f ∼ g` and a
cocycle `w` of degree `n`, `f w = g w + d (h w)`. PROVED. -/
theorem homotopy_apply_cocycle {A B : GCx S} {f g : A.toCC ⟶ B.toCC} (h : Homotopy f g)
    (m n n₁ : ℤ) (hmn : m + 1 = n) (hn : n + 1 = n₁) (w : A.X n) (hw : A.d n n₁ hn w = 0) :
    (f.f n).hom w = (g.f n).hom w + (B.toCC.d m n).hom ((h.hom n m).hom w) := by
  have e : (f.f n).hom w = (dNext n h.hom + prevD n h.hom + g.f n).hom w :=
    congrArg (fun φ => φ.hom w) (h.comm n)
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel n n₁ from hn),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel m n from hmn)] at e
  rw [e]
  have e3 : (A.toCC.d n n₁).hom w = 0 := (GCx.toCC_d_hom A n n₁ hn w).trans hw
  change (h.hom n₁ n).hom ((A.toCC.d n n₁).hom w) + (B.toCC.d m n).hom ((h.hom n m).hom w) +
    (g.f n).hom w = _
  rw [e3, map_zero, zero_add]
  exact add_comm _ _

/-- A chain map sends cocycles to cocycles. PROVED. -/
theorem chainMap_cocycle {A B : GCx S} (φ : A.toCC ⟶ B.toCC) (n n₁ : ℤ) (hn : n + 1 = n₁)
    (w : A.X n) (hw : A.d n n₁ hn w = 0) : B.d n n₁ hn ((φ.f n).hom w) = 0 := by
  have e : (B.toCC.d n n₁).hom ((φ.f n).hom w) = (φ.f n₁).hom ((A.toCC.d n n₁).hom w) :=
    congrArg (fun ψ => ψ.hom w) (φ.comm n n₁)
  have e1 := GCx.toCC_d_hom B n n₁ hn ((φ.f n).hom w)
  have e2 := GCx.toCC_d_hom A n n₁ hn w
  rw [← e1, e, e2, hw]
  exact map_zero _

end Invariance

/-! ### The functional relation for retention data with a genuine new place -/

section Natural

variable {S : Type u} [CommRing S] {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U}
  {fS : GHom US DPp.U} {Lq Uq : GCx S} {ιq : GHom Uq Lq}

/-- **`λ_R ∘ i = e_q λ_P` for retention data with an arbitrary new place** (tex 4157–4177): for
every cocycle `w ∈ C_P^2`, `λ_R(i w) = e · λ_P(w)`, given the paired strict lift
`j z_S = e z_{P⊥} + d b`. No tame model enters. PROVED (the RC53 group's
`pairedFunctional_natural` for `PlaceRetentionG.toRetainedPairing`). -/
theorem PlaceRetentionG.pairedFunctional_natural (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (w : (selCx (selRestrict DR fP)).X 2)
    (hw : (selCx (selRestrict DR fP)).d 2 3 rfl w = 0) :
    pairedFun R.toRetainedPairing.QR (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS
        ((changeMap DR fP).f 2 2 rfl w) =
      e * pairedFun R.toRetainedPairing.QP tr zP w :=
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.pairedFunctional_natural R.toRetainedPairing tr htr zS
    zP e b hlift w hw

/-- **Model coordinates do not depend on the homotopy** (tex 4170–4177): for chain maps
`Φ_R : C_R^{mod} → C_R`, `Φ_P : C_P^{mod} → C_P` and a model map `i^{mod}` with
`i^{mod} ≫ Φ_R ∼ Φ_P ≫ i`, and a cocycle `z_S`, `λ_R(Φ_R(i^{mod} w)) = λ_R(i(Φ_P w))` on model
cocycles `w`. PROVED (`homotopy_apply_cocycle`, `pairedFun_add_coboundary`). -/
theorem PlaceRetentionG.pairedFun_model_eq (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1)
    (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0)
    {CR CP : GCx S} (ΦR : CR.toCC ⟶ (selCx DR).toCC)
    (ΦP : CP.toCC ⟶ (selCx (selRestrict DR fP)).toCC) (im : CP.toCC ⟶ CR.toCC)
    (H : Homotopy (im ≫ ΦR) (ΦP ≫ GHom.toCC (changeMap DR fP))) (w : CP.X 2)
    (hw : CP.d 2 3 rfl w = 0) :
    pairedFun R.toRetainedPairing.QR (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS
        ((ΦR.f 2).hom ((im.f 2).hom w)) =
      pairedFun R.toRetainedPairing.QR (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS
        ((changeMap DR fP).f 2 2 rfl ((ΦP.f 2).hom w)) := by
  have h1 := homotopy_apply_cocycle H 1 2 3 rfl rfl w hw
  have key : (ΦR.f 2).hom ((im.f 2).hom w) =
      (changeMap DR fP).f 2 2 rfl ((ΦP.f 2).hom w) + (selCx DR).d 1 2 rfl ((H.hom 2 1).hom w) :=
    h1.trans (congrArg (fun x => ((ΦP ≫ GHom.toCC (changeMap DR fP)).f 2).hom w + x)
      (GCx.toCC_d_hom (selCx DR) 1 2 rfl ((H.hom 2 1).hom w)))
  exact (congrArg (pairedFun R.toRetainedPairing.QR
    (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS) key).trans
    (pairedFun_add_coboundary R.toRetainedPairing.QR tr htr zS hzS _ _)

/-- **`λ_R ∘ i = e_q λ_P` in model coordinates** (tex 4157–4177): the relation for the functionals
read on model cocycles through chain maps compatible with `i` up to homotopy, for a cocycle `z_S`.
PROVED. -/
theorem PlaceRetentionG.pairedFunctional_natural_model
    (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1)
    (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    {CR CP : GCx S} (ΦR : CR.toCC ⟶ (selCx DR).toCC)
    (ΦP : CP.toCC ⟶ (selCx (selRestrict DR fP)).toCC) (im : CP.toCC ⟶ CR.toCC)
    (H : Homotopy (im ≫ ΦR) (ΦP ≫ GHom.toCC (changeMap DR fP))) (w : CP.X 2)
    (hw : CP.d 2 3 rfl w = 0) :
    pairedFun R.toRetainedPairing.QR (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS
        ((ΦR.f 2).hom ((im.f 2).hom w)) =
      e * pairedFun R.toRetainedPairing.QP tr zP ((ΦP.f 2).hom w) := by
  rw [R.pairedFun_model_eq tr htr zS hzS ΦR ΦP im H w hw]
  exact R.pairedFunctional_natural tr htr zS zP e b hlift _
    (chainMap_cocycle ΦP 2 3 rfl w hw)

end Natural

/-! ### The genuine new place -/

section Genuine

open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **`λ_R ∘ i = e_q λ_P` at the genuine new place** (tex 4157–4177): the retention datum with
`L_q = C^•_cont(G_{K_w}, M)`, `U_q = [W --(Φ_w − 1)--> W]` and `ι_q` the inflation; no tame model
and no `UnramifiedNewPlace`. PROVED. -/
theorem pairedFunctional_natural_genuine (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    {DR DPp : SelData k} {UP US : GCx k} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    (R : PlaceRetentionG DR DPp fP fS (genuineLq K S k M w) (genuineUq K S k w X)
      (genuineιq K S k M w X f hf))
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (v : (selCx (selRestrict DR fP)).X 2)
    (hv : (selCx (selRestrict DR fP)).d 2 3 rfl v = 0) :
    pairedFun R.toRetainedPairing.QR (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS
        ((changeMap DR fP).f 2 2 rfl v) =
      e * pairedFun R.toRetainedPairing.QP tr zP v :=
  R.pairedFunctional_natural tr htr zS zP e b hlift v hv

/-- **Retention data exist at every genuine new place** (PROVED, non-vacuity): the datum
`examplePlaceRetentionG` at `L_q = C^•_cont(G_{K_w}, M)`, `U_q = [W --(Φ_w − 1)--> W]` and the
inflation. -/
theorem nonempty_placeRetentionG_genuine (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    Nonempty (PlaceRetentionG (relSel k) (constSel k) (constId k) (constId k)
      (genuineLq K S k M w) (genuineUq K S k w X) (genuineιq K S k M w X f hf)) :=
  ⟨examplePlaceRetentionG k _ _ _⟩

end Genuine

/-! ### Triangular-basis functionals from retention data with a genuine new place -/

section Functionals

/-- **The triangular-basis functionals are paired functionals of retention data with a genuine
new place** (tex 4157–4177): the RC53 group's `SelmerFunctionals`, with the retention datum
`PlaceRetentionG` (any new place `L_q`, `U_q`, `ι_q`, in particular the genuine local cochains) and
arbitrary index types `α` (the old basis) and `κ` (the basis at `q`). -/
def SelmerFunctionalsG {K : Type} [CommRing K] {α κ : Type} (wR : α ⊕ κ → K) (wP : α → K)
    (eK : K) : Prop :=
  ∃ (S : Type) (_ : CommRing S) (DR DPp : SelData S) (UP US : GCx S) (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) (Lq Uq : GCx S) (ιq : GHom Uq Lq)
    (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (_ : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (_ : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (φP : α → (selCx (selRestrict DR fP)).X 2)
    (_ : ∀ i, (selCx (selRestrict DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : α ⊕ κ → (selCx DR).X 2)
    (_ : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i))
    (ψ : S →+* K),
    ψ e = eK ∧
      (∀ j, wR j = ψ (pairedFun R.toRetainedPairing.QR
        (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS (φR j))) ∧
      (∀ i, wP i = ψ (pairedFun R.toRetainedPairing.QP tr zP (φP i)))

/-- **`w_R|old = e_q w_P`** (tex 4170–4177), PROVED from the naturality of the cup pairing for the
retention data with a genuine new place. -/
theorem SelmerFunctionalsG.restrict {K : Type} [CommRing K] {α κ : Type} {wR : α ⊕ κ → K}
    {wP : α → K} {eK : K} (h : SelmerFunctionalsG wR wP eK) (i : α) :
    wR (Sum.inl i) = eK * wP i := by
  obtain ⟨S, _, DR, DPp, UP, US, fP, fS, Lq, Uq, ιq, R, tr, htr, zS, zP, e, b, hlift, φP, hφP,
    φR, hφR, ψ, he, hwR, hwP⟩ := h
  rw [hwR, hwP, hφR, R.pairedFunctional_natural tr htr zS zP e b hlift (φP i) (hφP i), map_mul,
    he]

/-- **The RC53 group's `SelmerFunctionals` gives `SelmerFunctionalsG`** (PROVED: its retention
datum through `PlaceRetention.toG`). -/
theorem SelmerFunctionals.toG {K : Type} [CommRing K] {n : ℕ} {κ : Type} {wR : Fin n ⊕ κ → K}
    {wP : Fin n → K} {eK : K} (h : SelmerFunctionals wR wP eK) : SelmerFunctionalsG wR wP eK := by
  obtain ⟨S, DR, DPp, UP, US, fP, fS, R, tr, htr, zS, zP, e, b, hlift, φP, hφP, φR, hφR, ψ, he,
    hwR, hwP⟩ := h
  exact ⟨S, inferInstance, DR, DPp, UP, US, fP, fS, R.NP.Lq, R.NP.Uq, R.NP.ιq, R.toG, tr, htr, zS,
    zP, e, b, hlift, φP, hφP, φR, hφR, ψ, he, hwR, hwP⟩

/-- **The functionals in model coordinates are `SelmerFunctionalsG`** (tex 4157–4177): for retention
data with any new place, a cocycle `z_S`, chain maps `Φ_R : C_R^{mod} → C_R`,
`Φ_P : C_P^{mod} → C_P`, a model map `i^{mod}` with `i^{mod} ≫ Φ_R ∼ Φ_P ≫ i`, model cocycles
`b_P i` and a relaxed model basis `b_R` whose old part is `i^{mod} ∘ b_P`, the functionals read in
the model bases form `SelmerFunctionalsG`. PROVED (`PlaceRetentionG.pairedFun_model_eq`). -/
theorem selmerFunctionalsG_of_model {K : Type} [CommRing K] {α κ : Type} {S : Type} [CommRing S]
    {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    {Lq Uq : GCx S} {ιq : GHom Uq Lq} (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1)
    (hzS : (selCx (selRestrict DPp fS)).d 1 2 rfl zS = 0) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    {CR CP : GCx S} (ΦR : CR.toCC ⟶ (selCx DR).toCC)
    (ΦP : CP.toCC ⟶ (selCx (selRestrict DR fP)).toCC) (im : CP.toCC ⟶ CR.toCC)
    (H : Homotopy (im ≫ ΦR) (ΦP ≫ GHom.toCC (changeMap DR fP)))
    (bP : α → CP.X 2) (hbP : ∀ i, CP.d 2 3 rfl (bP i) = 0) (bR : α ⊕ κ → CR.X 2)
    (hbR : ∀ i, bR (Sum.inl i) = (im.f 2).hom (bP i)) (ψ : S →+* K) :
    SelmerFunctionalsG
      (fun j => ψ (pairedFun R.toRetainedPairing.QR
        (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS ((ΦR.f 2).hom (bR j))))
      (fun i => ψ (pairedFun R.toRetainedPairing.QP tr zP ((ΦP.f 2).hom (bP i)))) (ψ e) := by
  refine ⟨S, inferInstance, DR, DPp, UP, US, fP, fS, Lq, Uq, ιq, R, tr, htr, zS, zP, e, b, hlift,
    fun i => (ΦP.f 2).hom (bP i), fun i => chainMap_cocycle ΦP 2 3 rfl (bP i) (hbP i),
    Sum.elim (fun i => (changeMap DR fP).f 2 2 rfl ((ΦP.f 2).hom (bP i)))
      (fun j => (ΦR.f 2).hom (bR (Sum.inr j))), fun _ => rfl, ψ, rfl, ?_, fun _ => rfl⟩
  rintro (i | j)
  · have h := R.pairedFun_model_eq tr htr zS hzS ΦR ΦP im H (bP i) (hbP i)
    have hb : (ΦR.f 2).hom (bR (Sum.inl i)) = (ΦR.f 2).hom ((im.f 2).hom (bP i)) := by
      rw [hbR i]
    exact congrArg ψ ((congrArg (pairedFun R.toRetainedPairing.QR
      (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS) hb).trans h)
  · rfl

/-- **Non-vacuity of `SelmerFunctionalsG`** (PROVED): the RC53 group's retention example
`selmerFunctionals_example`, through `SelmerFunctionals.toG`. -/
theorem selmerFunctionalsG_example :
    SelmerFunctionalsG (κ := Fin 2 ⊕ Fin 2) (Sum.elim (fun _ => (-2 : KPS)) (fun _ => 0))
      (fun _ : Fin 1 => (1 : KPS)) (pointFactor 2 2 2) :=
  SelmerFunctionals.toG selmerFunctionals_example

end Functionals

/-! ### One relaxation step with genuine retention -/

section Step

/-- **One relaxation step from retention data with a genuine new place** (tex 4159–4193): the RC53
group's `NaturalStep` with `SelmerFunctionals` replaced by `SelmerFunctionalsG`. -/
def NaturalStepG {K : Type} [CommRing K] (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (uprim urel ε : K) (unitR unitP : K → Prop) : Prop :=
  ∃ (n : ℕ) (DPa PP QP : Matrix (Fin n) (Fin n) K)
    (DRa PR QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (zPa wPa : Fin n → K)
    (zRa wRa : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K),
    IsUnit PP.det ∧ IsUnit QP.det ∧ IsUnit PR.det ∧ IsUnit QR.det ∧
    PR * DRa * QR = fromBlocks (PP * DPa * QP) X 0 (twoPlaceBlock F q z zi) ∧
    (∀ i, (QR⁻¹ *ᵥ zRa) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zPa) i) ∧
    SelmerFunctionalsG (wRa ᵥ* PR⁻¹) (wPa ᵥ* PP⁻¹) (pointFactor a z zi) ∧
    IsCoordOn DRa zRa wRa urel ∧ IsClassFunctionalCoord DPa zPa wPa uprim ∧
    (PP * DPa * QP).adjugate ≠ 0 ∧
    unitR (PR.det * QR.det) ∧ unitP (PP.det * QP.det) ∧
    ε = qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)

/-- `NaturalStepG` gives the RC53 group's `ActualStep` (PROVED: the functional relation by
`SelmerFunctionalsG.restrict`). -/
theorem NaturalStepG.toActualStep {K : Type} [CommRing K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop}
    (h : NaturalStepG F q qi a z zi uprim urel ε unitR unitP) :
    ActualStep F q qi a z zi uprim urel ε unitR unitP := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS, h8, h9,
    h10, h11, h12, h13⟩ := h
  exact ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6,
    SelmerFunctionalsG.restrict hS, h8, h9, h10, h11, h12, h13⟩

/-- The RC53 group's `NaturalStep` gives `NaturalStepG` (PROVED). -/
theorem NaturalStep.toG {K : Type} [CommRing K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop}
    (h : NaturalStep F q qi a z zi uprim urel ε unitR unitP) :
    NaturalStepG F q qi a z zi uprim urel ε unitR unitP := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS, h8, h9,
    h10, h11, h12, h13⟩ := h
  exact ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6,
    SelmerFunctionals.toG hS, h8, h9, h10, h11, h12, h13⟩

/-- **RC0's field `h47` from relaxation steps with genuine retention** (tex 4166–4193): the
multi-prime (4.7) `(∏_U l_q) u_rel = (∏_U e_q² ε_q) u_prim` when each relaxation step is a
`NaturalStepG`. PROVED (the RC53 group's `commonCoordinate_h47_of_models_full`). -/
theorem commonCoordinate_h47_of_naturalG {R : Type*} [CommRing R]
    (chi : R →+* PowerSeries ℚ_[2]) (U : Finset ℕ) (l e : ℕ → R) (urel uprim : PowerSeries ℚ_[2])
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2]))
    (q qi a z zi eps : ℕ → PowerSeries ℚ_[2]) (u : Finset ℕ → PowerSeries ℚ_[2])
    (hl : ∀ p ∈ U, chi (l p) = quotientFactor (F p) (qi p) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (hrel : u U = urel) (hprim : u ∅ = uprim)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      NaturalStepG (F p) (q p) (qi p) (a p) (z p) (zi p) (u T) (u (insert p T)) (eps p)
        LamUnit LamUnit) :
    (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * eps q) * uprim :=
  commonCoordinate_h47_of_models_full chi U l e urel uprim F q qi a z zi eps u hl he hrel hprim hq
    ha hd fun T hT p hp hpT => NaturalStepG.toActualStep (hstep T hT p hp hpT)

/-- **Non-vacuity of `NaturalStepG`** (PROVED): the RC53 group's `naturalStep_example`. -/
theorem naturalStepG_example :
    NaturalStepG (1 : Matrix (Fin 2) (Fin 2) KPS) 1 1 2 2 2 1 4 1 LamUnit LamUnit :=
  NaturalStep.toG naturalStep_example

end Step

/-! ### The torsion-form relation of `KmStep` from genuine retention -/

section KmStep

/-- **The relation `lam ∘ Sum.inl = e • lam_P` from `SelmerFunctionalsG`** (tex 4170–4177).
PROVED. -/
theorem hlamR_of_selmerFunctionalsG {K : Type} [CommRing K] {α κ : Type} {lam : α ⊕ κ → K}
    {lamP : α → K} {e : K} (h : SelmerFunctionalsG lam lamP e) : lam ∘ Sum.inl = e • lamP :=
  funext fun i => by
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, SelmerFunctionalsG.restrict h i]

/-- **The relation `lam ∘ Sum.inl = e • lam_P` from retention data with any new place**
(tex 4157–4177), as direct hypotheses: the functionals `lam j = ψ(λ_R(φ_R j))`,
`lam_P i = ψ(λ_P(φ_P i))` on bases with `φ_R (inl i) = i (φ_P i)`. No tame model. PROVED. -/
theorem hlamR_of_retention {K : Type} [CommRing K] {α κ : Type} {S : Type u} [CommRing S]
    {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    {Lq Uq : GCx S} {ιq : GHom Uq Lq} (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zPp : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b)
    (φP : α → (selCx (selRestrict DR fP)).X 2)
    (hφP : ∀ i, (selCx (selRestrict DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : α ⊕ κ → (selCx DR).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i)) (ψ : S →+* K)
    (lam : α ⊕ κ → K) (lamP : α → K)
    (hlam : ∀ j, lam j = ψ (pairedFun R.toRetainedPairing.QR
      (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS (φR j)))
    (hlamP : ∀ i, lamP i = ψ (pairedFun R.toRetainedPairing.QP tr zPp (φP i))) :
    lam ∘ Sum.inl = ψ e • lamP :=
  funext fun i => by
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hlam, hlamP, hφR,
      R.pairedFunctional_natural tr htr zS zPp e b hlift (φP i) (hφP i), map_mul]

section Genuine

open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The relation `lam ∘ Sum.inl = e_q • lam_P` at the genuine new place** (tex 4157–4177): the
retention datum with `L_q = C^•_cont(G_{K_w}, M)`, `U_q = [W --(Φ_w − 1)--> W]`, `ι_q` the
inflation; no tame model. The input `hlamR` of lane RC31's `KmStep`. PROVED. -/
theorem hlamR_of_genuine {F : Type} [CommRing F] {α κ : Type} (w : Places K S)
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    {DR DPp : SelData k} {UP US : GCx k} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    (R : PlaceRetentionG DR DPp fP fS (genuineLq K S k M w) (genuineUq K S k w X)
      (genuineιq K S k M w X f hf))
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zPp : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b)
    (φP : α → (selCx (selRestrict DR fP)).X 2)
    (hφP : ∀ i, (selCx (selRestrict DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : α ⊕ κ → (selCx DR).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i)) (ψ : k →+* F)
    (lam : α ⊕ κ → F) (lamP : α → F)
    (hlam : ∀ j, lam j = ψ (pairedFun R.toRetainedPairing.QR
      (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS (φR j)))
    (hlamP : ∀ i, lamP i = ψ (pairedFun R.toRetainedPairing.QP tr zPp (φP i))) :
    lam ∘ Sum.inl = ψ e • lamP :=
  hlamR_of_retention R tr htr zS zPp e b hlift φP hφP φR hφR ψ lam lamP hlam hlamP

/-- **`SelmerFunctionalsG` from retention data at the genuine new place** (tex 4157–4177): the
retention datum with `L_q = C^•_cont(G_{K_w}, M)`, `U_q = [W --(Φ_w − 1)--> W]` and the inflation,
over the coefficient ring `k`, no tame model. PROVED. -/
theorem selmerFunctionalsG_of_genuine {F : Type} [CommRing F] {α κ : Type} (w : Places K S)
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    {DR DPp : SelData k} {UP US : GCx k} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    (R : PlaceRetentionG DR DPp fP fS (genuineLq K S k M w) (genuineUq K S k w X)
      (genuineιq K S k M w X f hf))
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zPp : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b)
    (φP : α → (selCx (selRestrict DR fP)).X 2)
    (hφP : ∀ i, (selCx (selRestrict DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : α ⊕ κ → (selCx DR).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i)) (ψ : k →+* F) :
    SelmerFunctionalsG
      (fun j => ψ (pairedFun R.toRetainedPairing.QR
        (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS (φR j)))
      (fun i => ψ (pairedFun R.toRetainedPairing.QP tr zPp (φP i))) (ψ e) :=
  ⟨k, inferInstance, DR, DPp, UP, US, fP, fS, _, _, _, R, tr, htr, zS, zPp, e, b, hlift, φP, hφP,
    φR, hφR, ψ, rfl, fun _ => rfl, fun _ => rfl⟩

/-- **Lane RC31's `KmStep` with its functional relation from genuine retention** (tex 4157–4194):
the torsion-level step, all of whose data are given except the relation
`lam ∘ Sum.inl = e_q • lam_P`, which is supplied by retention data at the genuine new place (no
tame model) with `ψ(e) = e_q`. PROVED. -/
theorem kmStep_of_genuine {F : Type} [Field F] (w : Places K S)
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    {Fr : Matrix (Fin 2) (Fin 2) F} {q a zq zqi uR uP : F} (C : FullPreComplex F)
    (hB : IsUnit C.B.det)
    (hBe : ∃ e : C.N ≃ Fin 2 ⊕ Fin 2, C.B = (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (z : C.D1 ⊕ C.N → F) (lam : C.D2 ⊕ C.N → F) (hz : C.toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.toFour.d1 = 0) (zP : C.D1 → F) (lamP : C.D2 → F)
    (hzP : (C.cancel hB).toFour.d1 *ᵥ zP = 0) (hlamP : lamP ᵥ* (C.cancel hB).toFour.d1 = 0)
    (hzR : z ∘ Sum.inl = pointFactor a zq zqi • zP)
    {DR DPp : SelData k} {UP US : GCx k} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
    (R : PlaceRetentionG DR DPp fP fS (genuineLq K S k M w) (genuineUq K S k w X)
      (genuineιq K S k M w X f hf))
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[k] k)
    (htr : ∀ x, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl x) = 0)
    (zS : (selCx (selRestrict DPp fS)).X 1) (zPp : (selCx DPp).X 1) (e : k)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zPp + (selCx DPp).d 0 1 rfl b)
    (φP : C.D2 → (selCx (selRestrict DR fP)).X 2)
    (hφP : ∀ i, (selCx (selRestrict DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : C.D2 ⊕ C.N → (selCx DR).X 2)
    (hφR : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i)) (ψ : k →+* F)
    (he : ψ e = pointFactor a zq zqi)
    (hlamE : ∀ j, lam j = ψ (pairedFun R.toRetainedPairing.QR
      (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[k] k) zS (φR j)))
    (hlamPE : ∀ i, lamP i = ψ (pairedFun R.toRetainedPairing.QP tr zPp (φP i)))
    (hR : uR = kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N))
    (hP : uP = kmCoord (C.cancel hB).toFour zP lamP hzP hlamP (σBlock C.m0 C.m1 C.m2)) :
    KmStep Fr q a zq zqi uR uP := by
  have hlamR := hlamR_of_genuine K S k M w X f hf R tr htr zS zPp e b hlift φP hφP φR hφR ψ lam
    lamP hlamE hlamPE
  rw [he] at hlamR
  exact ⟨C, hB, hBe, z, lam, hz, hlam, zP, lamP, hzP, hlamP, hzR, hlamR, hR, hP⟩

end Genuine

end KmStep

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition

/-!
# Theorem 5.3, lane RC30: the common-coordinate retention over genuine local cochains

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4142–4328), proof at tex 4157–4170:
the primitive-to-relaxed map `i : C_P → C_R` and the paired strict-to-primitive map
`j : C_S → C_{P⊥}` retain all old orthogonal conditions and their homotopies; at the new place `q`
they are the maps from the unramified condition to the full condition and from zero to the
unramified condition; naturality of the cup pairing (Nekovář, *Selmer complexes*, 6.4.1–6.4.3)
gives `λ_R ∘ i = e_q λ_P`.

The RC53 group's retention datum `PlaceRetention` (`CloudB3RC53/CommonCoordinate/Retention.lean`)
takes its new place as an `UnramifiedNewPlace` (`CloudB3RC53/SelmerDuality/SupportChange.lean`):
the full local complex at `q` and the unramified condition DEGREEWISE isomorphic to the tame model
(4.4) at `g = 1`. Genuine continuous cochains `C^•_cont(G_{K_q}, M)` are nonzero in every degree, so
they are never such a place. This file re-points the retention to genuine local cochains.

* `PlaceRetentionG DR DPp fP fS Lq Uq ιq`: the retention datum with the new place given by ANY
  complexes `L_q`, `U_q` and map `ι_q : U_q → L_q`. `PlaceRetentionG.retained` and
  `PlaceRetentionG.toRetainedPairing` (PROVED): the place-by-place argument uses at `q` only that
  the strict condition there is zero (`q_S`), never an identification of `L_q` with a model.
  `PlaceRetention.toG` (definition): the RC53 group's datum is the case `L_q = NP.Lq`.
* `TameLocalModel Lq Uq ιq` (hypothesis shape; GLUE, the tame local model (4.4) at finite level, tex
  3471–3481; Nekovář, *Selmer complexes*, 7.8.8(ii)): the tame model `T` at `g = 1` (an
  `UnramifiedNewPlace`: `M --(Φ−1, 0)--> M ⊕ M --(0, Φ−q)--> M` and `[Φ − 1]`), homotopy
  equivalences `L_q ≃ T.Lq` and `U_q ≃ T.Uq` over the coefficient ring, and a homotopy between the
  two composites `U_q → T.Lq` (through `ι_q` and through `T.ιq`).
* `genuineLq`, `genuineUq`, `genuineιq` (definitions): the genuine new place at `w ∈ S` — the local
  continuous cochains `C^•_cont(G_{K_w}, M)` of the Galois Selmer data (lane RC26's `localCx`; at
  the coefficient stage this is the complex `actualStageLocalCx` of the inner-limit files), the
  unramified complex `[W --(Φ_w − 1)--> W]` (`urCx`) and the inflation map `urToLocal_galois`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Manuscript.RC.SelmerComplex

universe u

section Retention

variable {S : Type u} [CommRing S]

/-- **Place-by-place retention data with a genuine new place** (tex 4157–4166). The fields are
those of the RC53 group's `PlaceRetention`, except that the full local complex `L_q`, the unramified
condition `U_q` and their map `ι_q` are arbitrary (parameters), in place of the degreewise tame
model of an `UnramifiedNewPlace`: for the text, `L_q = C^•_cont(G_{K_q}, M)`, `U_q` the unramified
complex and `ι_q` the inflation (`genuineLq`, `genuineUq`, `genuineιq`). Kinds: the retained
conditions and homotopies are ELLIOT (tex 4159–4166); the cup products and their compatibility are
GLUE (Nekovář 6.4.1–6.4.3). -/
structure PlaceRetentionG (DR DPp : SelData S) {UP US : GCx S} (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) (Lq Uq : GCx S) (ιq : GHom Uq Lq) where
  /-- Global target. -/
  E : GCx S
  /-- Local target. -/
  EL : GCx S
  /-- Restriction on the target. -/
  resE : GHom E EL
  /-- Global cup product (shared by both pairings). -/
  cupG : GPair DPp.G DR.G E
  /-- Local cup product (shared by both pairings). -/
  cupL : GPair DPp.L DR.L EL
  /-- Restriction commutes with the cup products. -/
  compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
    (hk : k = k') (a : DPp.G.X i) (b : DR.G.X j),
    resE.f k k' hk (cupG.P i j k h a b) =
      cupL.P i' j' k' h' (DPp.res.f i i' hi a) (DR.res.f j j' hj b)
  /-- The index type of places. -/
  ι : Type
  /-- The old places. -/
  old : Finset ι
  /-- The old local condition at `v` (primitive/relaxed side). -/
  Uo : ι → GCx S
  /-- The old orthogonal local condition at `v` (strict/orthogonal side). -/
  Uo' : ι → GCx S
  /-- The old isotropy homotopy at `v`. -/
  hv : ∀ (v : ι) (i j k : ℤ), i + j = k + 1 → (Uo' v).X i →ₗ[S] (Uo v).X j →ₗ[S] EL.X k
  /-- The orthogonal of the unramified condition at `q`. -/
  Uq' : GCx S
  /-- The isotropy homotopy at `q` for the primitive pairing. -/
  hq : ∀ i j k : ℤ, i + j = k + 1 → Uq'.X i →ₗ[S] Uq.X j →ₗ[S] EL.X k
  /-- Old components of `U_R`. -/
  pR : ∀ (v : ι) (j : ℤ), DR.U.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_P`. -/
  pP : ∀ (v : ι) (j : ℤ), UP.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_S`. -/
  pS : ∀ (v : ι) (i : ℤ), US.X i →ₗ[S] (Uo' v).X i
  /-- Old components of `U_{P⊥}`. -/
  pPp : ∀ (v : ι) (i : ℤ), DPp.U.X i →ₗ[S] (Uo' v).X i
  /-- The `q`-component of `U_R` (the full local complex at `q`). -/
  qR : ∀ j : ℤ, DR.U.X j →ₗ[S] Lq.X j
  /-- The `q`-component of `U_P` (the unramified condition). -/
  qP : ∀ j : ℤ, UP.X j →ₗ[S] Uq.X j
  /-- The `q`-component of `U_{P⊥}`. -/
  qPp : ∀ i : ℤ, DPp.U.X i →ₗ[S] Uq'.X i
  /-- The relaxed homotopy on `U_S × U_R`. -/
  hR : ∀ i j k : ℤ, i + j = k + 1 → US.X i →ₗ[S] DR.U.X j →ₗ[S] EL.X k
  /-- … is the sum of the old per-place homotopies (the strict condition at `q` is zero). -/
  hR_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : US.X i) (y : DR.U.X j),
    hR i j k h x y = ∑ v ∈ old, hv v i j k h (pS v i x) (pR v j y)
  /-- The isotropy identity of the relaxed homotopy. -/
  isoR : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : US.X i) (y : DR.U.X j),
    EL.d k k₁ hk (hR i j k h x y) + hR i₁ j k₁ (by omega) (US.d i i₁ hi x) y +
        sgn i • hR i j₁ k₁ (by omega) x (DR.U.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) ((ghomComp fS DPp.ι).f i i rfl x) (DR.ι.f j j rfl y)
  /-- The primitive homotopy on `U_{P⊥} × U_P`. -/
  hP : ∀ i j k : ℤ, i + j = k + 1 → DPp.U.X i →ₗ[S] UP.X j →ₗ[S] EL.X k
  /-- … is the sum of the same old per-place homotopies and the homotopy at `q`. -/
  hP_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : DPp.U.X i) (y : UP.X j),
    hP i j k h x y = ∑ v ∈ old, hv v i j k h (pPp v i x) (pP v j y) + hq i j k h (qPp i x) (qP j y)
  /-- The isotropy identity of the primitive homotopy. -/
  isoP : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : DPp.U.X i) (y : UP.X j),
    EL.d k k₁ hk (hP i j k h x y) + hP i₁ j k₁ (by omega) (DPp.U.d i i₁ hi x) y +
        sgn i • hP i j₁ k₁ (by omega) x (UP.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) (DPp.ι.f i i rfl x) ((ghomComp fP DR.ι).f j j rfl y)
  /-- Every old condition is retained by `f_P`: it is the identity on each old summand. -/
  ret_P : ∀ (v : ι) (j : ℤ) (y : UP.X j), pR v j (fP.f j j rfl y) = pP v j y
  /-- Every old orthogonal condition is retained by `f_S`. -/
  ret_S : ∀ (v : ι) (i : ℤ) (x : US.X i), pPp v i (fS.f i i rfl x) = pS v i x
  /-- At `q`, `f_P` is the map from the unramified condition to the full local complex. -/
  q_P : ∀ (j : ℤ) (y : UP.X j), qR j (fP.f j j rfl y) = ιq.f j j rfl (qP j y)
  /-- At `q`, `f_S` is `0 → U_q`: the strict condition at `q` is zero. -/
  q_S : ∀ (i : ℤ) (x : US.X i), qPp i (fS.f i i rfl x) = 0

variable {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U} {fS : GHom US DPp.U}
  {Lq Uq : GCx S} {ιq : GHom Uq Lq}

/-- **The retained homotopies** (tex 4163–4165), PROVED from the place-by-place retention with a
genuine new place: `h_R(u, f_P v) = h_P(f_S u, v)`. Only `q_S` is used at `q`. -/
theorem PlaceRetentionG.retained (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq) (i j k : ℤ)
    (h : i + j = k + 1) (x : US.X i) (y : UP.X j) :
    R.hR i j k h x (fP.f j j rfl y) = R.hP i j k h (fS.f i i rfl x) y := by
  rw [R.hR_eq, R.hP_eq, R.q_S, map_zero, LinearMap.zero_apply, add_zero]
  exact Finset.sum_congr rfl fun v _ => by rw [R.ret_P, R.ret_S]

/-- **The retained pairing of the retention data with a genuine new place** (definition), the
input of the RC53 group's `cup_naturality` and `pairedFunctional_natural`. -/
def PlaceRetentionG.toRetainedPairing (R : PlaceRetentionG DR DPp fP fS Lq Uq ιq) :
    RetainedPairing DR DPp fP fS where
  E := R.E
  EL := R.EL
  resE := R.resE
  cupG := R.cupG
  cupL := R.cupL
  compat := R.compat
  hR := R.hR
  isoR := R.isoR
  hP := R.hP
  isoP := R.isoP
  retained := R.retained

/-- **The RC53 group's retention datum is the special case `L_q = NP.Lq`** (definition): forget the
degreewise identification of its new place with the tame model. -/
def _root_.ZInQ.Contrib.CloudB3RC53.CommonCoordinate.PlaceRetention.toG
    (R : PlaceRetention DR DPp fP fS) : PlaceRetentionG DR DPp fP fS R.NP.Lq R.NP.Uq R.NP.ιq where
  E := R.E
  EL := R.EL
  resE := R.resE
  cupG := R.cupG
  cupL := R.cupL
  compat := R.compat
  ι := R.ι
  old := R.old
  Uo := R.Uo
  Uo' := R.Uo'
  hv := R.hv
  Uq' := R.Uq'
  hq := R.hq
  pR := R.pR
  pP := R.pP
  pS := R.pS
  pPp := R.pPp
  qR := R.qR
  qP := R.qP
  qPp := R.qPp
  hR := R.hR
  hR_eq := R.hR_eq
  isoR := R.isoR
  hP := R.hP
  hP_eq := R.hP_eq
  isoP := R.isoP
  ret_P := R.ret_P
  ret_S := R.ret_S
  q_P := R.q_P
  q_S := R.q_S

/-- The two retained pairings agree (PROVED, by definition). -/
theorem PlaceRetention.toG_toRetainedPairing (R : PlaceRetention DR DPp fP fS) :
    R.toG.toRetainedPairing = R.toRetainedPairing :=
  rfl

/-- **Non-vacuity of `PlaceRetentionG` at every new place** (definition): for ANY `L_q`, `U_q`,
`ι_q` (in particular the genuine ones), the relaxed data `relSel` (`ι_R = id`), the orthogonal data
`constSel`, identity condition maps, one old place with zero homotopy and zero components at `q`. -/
def examplePlaceRetentionG (S : Type u) [CommRing S] (Lq Uq : GCx S) (ιq : GHom Uq Lq) :
    PlaceRetentionG (relSel S) (constSel S) (constId S) (constId S) Lq Uq ιq where
  E := constCx S
  EL := constCx S
  resE := constId S
  cupG := constMul S
  cupL := constMul S
  compat _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  ι := Unit
  old := {()}
  Uo _ := constCx S
  Uo' _ := constCx S
  hv _ _ _ _ _ := 0
  Uq' := constCx S
  hq _ _ _ _ := 0
  pR _ _ := LinearMap.id
  pP _ _ := LinearMap.id
  pS _ _ := LinearMap.id
  pPp _ _ := LinearMap.id
  qR _ := 0
  qP _ := 0
  qPp _ := 0
  hR _ _ _ _ := 0
  hR_eq _ _ _ _ _ _ := by simp
  isoR i _ _ _ _ _ _ _ _ _ x y := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (show S from y)
    rw [smul_zero, add_zero, add_zero, zero_mul]
  hP _ _ _ _ := 0
  hP_eq _ _ _ _ _ _ := by simp
  isoP i _ _ _ _ _ _ _ _ _ x y := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (show S from y)
    rw [smul_zero, add_zero, add_zero, zero_mul]
  ret_P _ _ _ := rfl
  ret_S _ _ _ := rfl
  q_P _ _ := by simp
  q_S _ _ := rfl

end Retention

/-! ### The tame local model at the new place -/

section Tame

variable {S : Type u} [CommRing S]

/-- **The tame local model (4.4) at the new place, at augmentation `g = 1`** (hypothesis shape;
GLUE: tex 3471–3481; Nekovář, *Selmer complexes*, 7.8.8(ii)). For a full local complex `L_q`, an
unramified condition `U_q` and `ι_q : U_q → L_q`:
* `T`: the tame model, an `UnramifiedNewPlace` — `M --(Φ−1, 0)--> M ⊕ M --(0, Φ−q)--> M` in degrees
  `0, 1, 2`, the unramified complex `[Φ − 1]` in degrees `0, 1` and the inclusion of the
  unramified summand;
* `eL`, `eU`: homotopy equivalences `L_q ≃ T.Lq`, `U_q ≃ T.Uq` over the coefficient ring;
* `comm`: a homotopy `ι_q ≫ eL ∼ eU ≫ T.ιq`.
For the text: `L_q = C^•_cont(G_{K_q}, M_i)` at a finite coefficient stage, `U_q` the unramified
complex and `ι_q` the inflation (`genuineLq`, `genuineUq`, `genuineιq`). -/
structure TameLocalModel (Lq Uq : GCx S) (ιq : GHom Uq Lq) where
  /-- The tame model at `g = 1`. -/
  T : UnramifiedNewPlace S
  /-- `L_q ≃ T.Lq` up to homotopy. -/
  eL : HomotopyEquiv Lq.toCC T.Lq.toCC
  /-- `U_q ≃ T.Uq` up to homotopy. -/
  eU : HomotopyEquiv Uq.toCC T.Uq.toCC
  /-- `ι_q` corresponds to the inclusion of the unramified summand, up to homotopy. -/
  comm : Homotopy (GHom.toCC ιq ≫ eL.hom) (eU.hom ≫ GHom.toCC T.ιq)

/-- **A degreewise tame place is its own tame model** (definition): identity equivalences. -/
def TameLocalModel.refl (T : UnramifiedNewPlace S) : TameLocalModel T.Lq T.Uq T.ιq where
  T := T
  eL := HomotopyEquiv.refl _
  eU := HomotopyEquiv.refl _
  comm := Homotopy.ofEq (by
    change GHom.toCC T.ιq ≫ 𝟙 _ = 𝟙 _ ≫ GHom.toCC T.ιq
    rw [Category.comp_id, Category.id_comp])

/-- **Non-vacuity of `TameLocalModel`** (PROVED): the zero new place. -/
theorem nonempty_tameLocalModel_zero :
    Nonempty (TameLocalModel (zeroNewPlace S).Lq (zeroNewPlace S).Uq (zeroNewPlace S).ιq) :=
  ⟨TameLocalModel.refl _⟩

variable {Lq Uq : GCx S} {ιq : GHom Uq Lq}

/-- **The model-to-genuine maps of a tame local model** (definition): the homotopy inverses
`T.Lq → L_q`, `T.Uq → U_q`, which transport model coordinates at `q` to the genuine complexes. -/
def TameLocalModel.toGenuineL (H : TameLocalModel Lq Uq ιq) : H.T.Lq.toCC ⟶ Lq.toCC := H.eL.inv

/-- The model-to-genuine map on the unramified condition (definition). -/
def TameLocalModel.toGenuineU (H : TameLocalModel Lq Uq ιq) : H.T.Uq.toCC ⟶ Uq.toCC := H.eU.inv

/-- **The model-to-genuine maps are compatible with `ι_q` up to homotopy** (PROVED, from `comm`
and the two homotopy equivalences): `T.ιq ≫ eL⁻¹ ∼ eU⁻¹ ≫ ι_q`. -/
def TameLocalModel.invComm (H : TameLocalModel Lq Uq ιq) :
    Homotopy (GHom.toCC H.T.ιq ≫ H.toGenuineL) (H.toGenuineU ≫ GHom.toCC ιq) := by
  have h1 : Homotopy (H.eU.inv ≫ GHom.toCC ιq ≫ H.eL.hom ≫ H.eL.inv)
      (H.eU.inv ≫ GHom.toCC ιq) :=
    (H.eL.homotopyHomInvId.compLeftId (GHom.toCC ιq)).compLeft H.eU.inv
  have h2 : Homotopy (H.eU.inv ≫ (GHom.toCC ιq ≫ H.eL.hom) ≫ H.eL.inv)
      (H.eU.inv ≫ (H.eU.hom ≫ GHom.toCC H.T.ιq) ≫ H.eL.inv) :=
    (H.comm.compRight H.eL.inv).compLeft H.eU.inv
  have h3 : Homotopy ((H.eU.inv ≫ H.eU.hom) ≫ GHom.toCC H.T.ιq ≫ H.eL.inv)
      (GHom.toCC H.T.ιq ≫ H.eL.inv) :=
    H.eU.homotopyInvHomId.compRightId _
  refine ((h3.symm.trans (Homotopy.ofEq ?_)).trans h2.symm).trans
    ((Homotopy.ofEq ?_).trans h1)
  · simp only [Category.assoc]
  · simp only [Category.assoc]

end Tame

/-! ### The genuine new place -/

section Genuine

open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The genuine full local complex at a place `w ∈ S`** (definition): the continuous cochains
`C^•_cont(G_{K_w}, M)` of the Galois Selmer data (lane RC26's `localCx`, tex 3455–3463). -/
abbrev genuineLq (w : Places K S) : GCx k :=
  localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w

/-- **The genuine unramified condition at `w`** (definition): the unramified complex
`[W --(Φ_w − 1)--> W]` of a finite discrete representation `W` of `Gal(K_w^{ur}/K_w)` (tex
3471–3487). -/
abbrev genuineUq (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) : GCx k :=
  ofCC (urCx K w.1 X)

/-- **The genuine map `ι_q`** (definition): inflation along `G_{K_w} → Gal(K_w^{ur}/K_w)`,
composed with a `G_{K_w}`-equivariant `f : W → M` (lane RC26's `urToLocal_galois`). -/
abbrev genuineιq (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    GHom (genuineUq K S k w X) (genuineLq K S k M w) :=
  ofCCHom (urToLocal_galois K S w X f hf)

end Genuine

end ZInQ.Manuscript.RC.Wiring

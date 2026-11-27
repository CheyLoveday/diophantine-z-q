import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalReduction
import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModelCochains
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition

/-!
# Lane RC31, round 6: the unramified square of the tame local model

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4) at augmentation: "the direct sum of the
unramified complex `[Φ − 1]` in degrees zero and one and the singular quotient"), tex 3478–3481
(the unramified condition `U^ur = [W --Φ−1--> W]`).

Setting (generic, as for the unramified condition `urToLocal`): a topological group `G` (the
decomposition group), `H ≃ₜ* ℤ̂` (`Gal(K_w^ur/K_w)`), `π : G → H`, a finite discrete unramified
representation `X` of `H` with Frobenius `Φ_X = frob e X`, and a `G`-equivariant linear
equivalence `f : X ≃ M` onto the coefficients. For `φ, σ ∈ G` with `π φ = Frob`, `π σ = 1` and the
exact relation `φ σ φ⁻¹ = σ^q`:

* `unrModelMap`: the model map `tameFreeModel(Φ_M, 1) → tameFreeModel(Φ_X, 1)` induced by `f⁻¹`,
  an isomorphism of complexes (`isIso_toCC_unrModelMap`);
* `frobToUnr`: the identification `[W --Φ−1--> W] ≅ unrCx Φ_X` of the two forms of the unramified
  complex, an isomorphism (`isIso_frobToUnr`);
* **`unr_square`** (PROVED): the inflation `urToLocal` followed by the comparison `tameCochainMap`
  and `f⁻¹` is, strictly, the identification followed by the inclusion `unrIncl` of the unramified
  summand. On inflated cochains the comparison reads `c(φ) = x`, `c(σ) = 0`;
* **`tameLocalModelAt_of_cochainQuasiIso`** (PROVED): over a field, if `tameCochainMap` is a
  quasi-isomorphism, the genuine local complex, the genuine unramified condition and the inflation
  form a `TameLocalModelAt` for `tameNewPlace X Φ_X q`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The two forms of a Mathlib complex -/

section OfCC

variable {k : Type} [CommRing k]

/-- The relation-indexed form of a Mathlib complex has the same Mathlib complex back
(tex 3478–3481). Kind: definition. -/
def ofCCToCCIso (C : CochainComplex (ModuleCat.{0} k) ℤ) : (ofCC C).toCC ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have h : i + 1 = j := hij
    ext x
    change (C.d i j).hom x = ((ofCC C).toCC.d i j).hom x
    exact (GCx.toCC_d_hom (ofCC C) i j h x).symm)

/-- The components of `ofCCToCCIso` are identities. Kind: PROVED (definitional). -/
theorem ofCCToCCIso_hom_f (C : CochainComplex (ModuleCat.{0} k) ℤ) (n : ℤ) :
    (ofCCToCCIso C).hom.f n = 𝟙 _ :=
  rfl

end OfCC

/-! ### The identification of the unramified complexes -/

section Unr

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Φ : W →ₗ[k] W)

/-- **The two forms of the unramified complex agree** (tex 3478–3481): the identity in degrees
zero and one, `[W --Φ−1--> W] ⟶ unrCx Φ`. Kind: definition (PROVED chain property). -/
def frobToUnr : frobCx Φ ⟶ (unrCx Φ).toCC :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (LinearMap.id : W →ₗ[k] W)) (ModuleCat.ofHom (LinearMap.id : W →ₗ[k] W))
    (by
      ext x
      exact GCx.toCC_d_hom (unrCx Φ) 0 1 rfl x)
    (by
      intro j hj
      obtain rfl : j = 2 := by simpa using hj.symm
      have : Subsingleton ((unrCx Φ).toCC.X 2) := inferInstanceAs (Subsingleton PUnit)
      ext x
      exact Subsingleton.elim _ _)

/-- Degree zero of `frobToUnr`. Kind: PROVED. -/
theorem frobToUnr_f₀ :
    (frobToUnr Φ).f 0 =
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).hom ≫
        ModuleCat.ofHom (LinearMap.id : W →ₗ[k] W) :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- Degree one of `frobToUnr`. Kind: PROVED. -/
theorem frobToUnr_f₁ :
    (frobToUnr Φ).f 1 =
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01 (by decide)).hom ≫
        ModuleCat.ofHom (LinearMap.id : W →ₗ[k] W) :=
  HomologicalComplex.mkHomFromDouble_f₁ _ _ _ _ _ _

/-- The identification of the unramified complexes is an isomorphism (tex 3478–3481). Kind:
PROVED. -/
theorem isIso_frobToUnr : IsIso (frobToUnr Φ) := by
  have : ∀ n, IsIso ((frobToUnr Φ).f n) := by
    intro n
    by_cases h0 : n = 0
    · subst h0
      rw [frobToUnr_f₀, ModuleCat.ofHom_id, Category.comp_id]
      exact (HomologicalComplex.doubleXIso₀ _ rel01).isIso_hom
    · by_cases h1 : n = 1
      · subst h1
        rw [frobToUnr_f₁, ModuleCat.ofHom_id, Category.comp_id]
        exact (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).isIso_hom
      · have hz : Limits.IsZero ((frobCx Φ).X n) :=
          HomologicalComplex.isZero_double_X _ _ n h0 h1
        have : Subsingleton ((unrCx Φ).toCC.X n) := by
          by_cases h2 : n = 2
          · subst h2
            exact inferInstanceAs (Subsingleton PUnit)
          · exact cx3X_subsingleton n h0 h1 h2
        exact Limits.isIso_of_source_target_iso_zero _ hz.isoZero
          (ModuleCat.isZero_of_subsingleton _).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

end Unr

/-! ### The model map along the coefficient equivalence -/

section ModelMap

variable {k : Type} [CommRing k] {M V : Type} [AddCommGroup M] [Module k M] [AddCommGroup V]
  [Module k V] (ΦM : M →ₗ[k] M) (ΦV : V →ₗ[k] V) (q : ℕ) (hq : Odd q) (f : V ≃ₗ[k] M)
  (hfΦ : ∀ v, f (ΦV v) = ΦM (f v))

include hfΦ in
/-- `f⁻¹` intertwines the Frobenius maps. Kind: PROVED. -/
theorem symm_comp_frob : f.symm.toLinearMap ∘ₗ ΦM = ΦV ∘ₗ f.symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  change f.symm (ΦM m) = ΦV (f.symm m)
  rw [LinearEquiv.symm_apply_eq, hfΦ, LinearEquiv.apply_symm_apply]

/-- **The model map along `f⁻¹`** at `g = 1` (tex 3470–3480). Kind: definition. -/
def unrModelMap : GHom (tameFreeModel1 ΦM q hq) (tameFreeModel1 ΦV q hq) :=
  tameFreeModelMap ΦM LinearMap.id ΦV LinearMap.id q hq (comm_id ΦM) id_invol (comm_id ΦV)
    id_invol f.symm.toLinearMap (symm_comp_frob ΦM ΦV f hfΦ)
    (by rw [LinearMap.comp_id, LinearMap.id_comp])

/-- The model map along a linear equivalence is an isomorphism of complexes (tex 3470–3480).
Kind: PROVED. -/
theorem isIso_toCC_unrModelMap : IsIso (GHom.toCC (unrModelMap ΦM ΦV q hq f hfΦ)) := by
  have : ∀ n, IsIso ((GHom.toCC (unrModelMap ΦM ΦV q hq f hfΦ)).f n) := by
    intro n
    rcases n with (_ | _ | _ | n) | n
    · exact inferInstanceAs (IsIso f.symm.toModuleIso.hom)
    · exact inferInstanceAs (IsIso (LinearEquiv.prodCongr f.symm f.symm).toModuleIso.hom)
    · exact inferInstanceAs (IsIso f.symm.toModuleIso.hom)
    · have : Subsingleton ((tameFreeModel1 ΦM q hq).toCC.X (Int.ofNat (n + 3))) :=
        inferInstanceAs (Subsingleton PUnit)
      have : Subsingleton ((tameFreeModel1 ΦV q hq).toCC.X (Int.ofNat (n + 3))) :=
        inferInstanceAs (Subsingleton PUnit)
      exact Limits.isIso_of_source_target_iso_zero _
        (ModuleCat.isZero_of_subsingleton _).isoZero (ModuleCat.isZero_of_subsingleton _).isoZero
    · have : Subsingleton ((tameFreeModel1 ΦM q hq).toCC.X (Int.negSucc n)) :=
        inferInstanceAs (Subsingleton PUnit)
      have : Subsingleton ((tameFreeModel1 ΦV q hq).toCC.X (Int.negSucc n)) :=
        inferInstanceAs (Subsingleton PUnit)
      exact Limits.isIso_of_source_target_iso_zero _
        (ModuleCat.isZero_of_subsingleton _).isoZero (ModuleCat.isZero_of_subsingleton _).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

end ModelMap

/-! ### From quasi-isomorphisms to a tame local model over any ring -/

/-- **A tame local model from two quasi-isomorphisms between K-injective complexes**
(tex 3470–3480; over any coefficient ring): if the four complexes are K-injective (for instance
bounded below with injective terms, as over a field or a self-injective Noetherian stage ring),
quasi-isomorphisms `φL`, `φU` strictly compatible with the inclusions give a
`TameLocalModelAt` with `eL.hom = φL`, `eU.hom = φU`. Kind: PROVED. -/
theorem tameLocalModelAt_of_quasiIso_kInj {k : Type} [CommRing k] {Lq Uq : GCx k}
    {ιq : GHom Uq Lq} {T : UnramifiedNewPlace k} [Lq.toCC.IsKInjective] [Uq.toCC.IsKInjective]
    [T.Lq.toCC.IsKInjective] [T.Uq.toCC.IsKInjective]
    (φL : Lq.toCC ⟶ T.Lq.toCC) (φU : Uq.toCC ⟶ T.Uq.toCC) [QuasiIso φL] [QuasiIso φU]
    (hsq : GHom.toCC ιq ≫ φL = φU ≫ GHom.toCC T.ιq) :
    ∃ m : TameLocalModelAt Lq Uq ιq T, m.eL.hom = φL ∧ m.eU.hom = φU := by
  obtain ⟨eL, heL⟩ := (CochainComplex.IsKInjective.quasiIso_iff φL).1 inferInstance
  obtain ⟨eU, heU⟩ := (CochainComplex.IsKInjective.quasiIso_iff φU).1 inferInstance
  refine ⟨⟨eL, eU, Homotopy.ofEq ?_⟩, heL, heU⟩
  rw [heL, heU]
  exact hsq

/-! ### The unramified square -/

section Square

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- The inflated cocycle vanishes at the identity. Kind: PROVED. -/
theorem urCocycle_one (x : X.V) : urCocycle e X x 1 = 0 := by
  have h := urCocycle_cocycle e X x 1 1
  rw [mul_one, one_smul] at h
  exact (add_eq_left.1 h.symm)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [ContinuousSMul H X.V] [DiscreteTopology X.V]
  [Finite X.V] [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] in
include hf hbij in
/-- An element `σ` with `π σ = 1` acts trivially on the coefficients. Kind: PROVED. -/
theorem smul_eq_of_res_one (hσ : π σ = 1) (m : M) : (LinearMap.id : M →ₗ[k] M) m = σ • m := by
  obtain ⟨x, rfl⟩ := hbij.2 m
  rw [LinearMap.id_apply, ← hf, hσ, one_smul]

omit [IsTopologicalGroup G] [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] in
include hf hΦ in
/-- `f` intertwines the Frobenius of `X` with the action of `φ` when `π φ = Frob`. Kind:
PROVED. -/
theorem frob_intertwine (hφ : π φ = frobElt e) (v : X.V) : f (frob e X v) = Φ (f v) := by
  rw [frob_apply, ← hφ, hf, hΦ]

/-- **The comparison of the genuine local complex with the model over `X`** at `g = 1`
(tex 3470–3480): `tameCochainMap` followed by the model map along `f⁻¹`. Kind: definition. -/
def unrL (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    (natCx (contCochains k G M)).toCC ⟶ (tameFreeModel1 (frob e X) q hq).toCC :=
  GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ (smul_eq_of_res_one π X f hbij hf σ hσ)
      id_invol (comm_id Φ) hrel) ≫
    GHom.toCC (unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ))

/-- **The identification of the genuine unramified condition with `[Φ − 1]`** (tex 3478–3481).
Kind: definition. -/
def unrU : (ofCC (frobCx (frob e X))).toCC ⟶ (unrCx (frob e X)).toCC :=
  (ofCCToCCIso (frobCx (frob e X))).hom ≫ frobToUnr (frob e X)

/-- **The unramified square commutes strictly** (tex 3470–3481): the inflation `urToLocal`
followed by the comparison with the model equals the identification of the unramified complexes
followed by the inclusion `unrIncl` of the unramified summand. On inflated cochains the comparison
reads `c(φ) = x` (`π φ = Frob`) and `c(σ) = 0` (`π σ = 1`). Kind: PROVED. -/
theorem unr_square (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    GHom.toCC (ofCCHom (urToLocal e π X f hf)) ≫
        unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel =
      unrU e X ≫ GHom.toCC (unrIncl (frob e X) q hq) := by
  ext n x
  by_cases h0 : n = 0
  · subst h0
    change (LinearEquiv.ofBijective f hbij).symm
        (evalZero k M (((urToLocal e π X f hf).f 0).hom x)) = ((frobToUnr (frob e X)).f 0).hom x
    rw [urToLocal_f₀, frobToUnr_f₀]
    exact (LinearEquiv.ofBijective f hbij).symm_apply_apply _
  · by_cases h1 : n = 1
    · subst h1
      change ((LinearEquiv.ofBijective f hbij).symm
            (evalOne k M φ (((urToLocal e π X f hf).f 1).hom x)),
          (LinearEquiv.ofBijective f hbij).symm
            (evalOne k M σ (((urToLocal e π X f hf).f 1).hom x))) =
        ((((frobToUnr (frob e X)).f 1).hom x, 0) : X.V × X.V)
      rw [urToLocal_f₁, frobToUnr_f₁]
      change ((LinearEquiv.ofBijective f hbij).symm
          ((LinearEquiv.ofBijective f hbij) (urCocycle e X _ (π φ))),
        (LinearEquiv.ofBijective f hbij).symm
          ((LinearEquiv.ofBijective f hbij) (urCocycle e X _ (π σ)))) = _
      rw [hφ, hσ, urCocycle_frob, urCocycle_one, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply]
      rfl
    · have hz : Limits.IsZero ((frobCx (frob e X)).X n) :=
        HomologicalComplex.isZero_double_X _ _ n h0 h1
      have : Subsingleton ((ofCC (frobCx (frob e X))).toCC.X n) :=
        ModuleCat.isZero_iff_subsingleton.1 hz
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, map_zero]

omit [TopologicalSpace k] in
/-- The genuine unramified condition vanishes in negative degrees (tex 3478–3481). Kind:
PROVED. -/
theorem ofCC_frobCx_isStrictlyGE {W : Type} [AddCommGroup W] [Module k W] (Ψ : W →ₗ[k] W) :
    (ofCC (frobCx Ψ)).toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X (ModuleCat.ofHom (Ψ - 1)) rel01 i (by omega) (by omega)

/-- **A tame local model from the quasi-isomorphism of the comparison, over any coefficient
ring with K-injective complexes** (tex 3470–3481): if `tameCochainMap` (at `g = 1`, for `φ`, `σ`
with `π φ = Frob`, `π σ = 1` and `φ σ φ⁻¹ = σ^q`) is a quasi-isomorphism and the genuine local
complex, the genuine unramified condition and the two model complexes are K-injective, then
they form a `TameLocalModelAt` for the tame model `tameNewPlace X Φ_X q`, with `eL.hom = unrL`
and `eU.hom = unrU`. Kind: PROVED. -/
theorem tameLocalModelAt_of_cochainQuasiIso_kInj (hφ : π φ = frobElt e) (hσ : π σ = 1)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    [(natCx (contCochains k G M)).toCC.IsKInjective]
    [(ofCC (frobCx (frob e X))).toCC.IsKInjective]
    [(tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Lq.toCC.IsKInjective]
    [(tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Uq.toCC.IsKInjective]
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel))) :
    ∃ m : TameLocalModelAt (natCx (contCochains k G M)) (ofCC (frobCx (frob e X)))
        (ofCCHom (urToLocal e π X f hf))
        (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq),
      m.eL.hom = unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel ∧ m.eU.hom = unrU e X := by
  have : IsIso (GHom.toCC (unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ))) := isIso_toCC_unrModelMap _ _ q hq _ _
  have hM : QuasiIso (GHom.toCC (unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ))) := quasiIso_of_isIso _
  have hL : QuasiIso (unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel) := by
    unfold unrL
    exact quasiIso_comp _ _
  have hL' : QuasiIso (K := (natCx (contCochains k G M)).toCC)
      (L := (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Lq.toCC)
      (unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel) := hL
  have : IsIso (frobToUnr (frob e X)) := isIso_frobToUnr _
  have hF : QuasiIso (frobToUnr (frob e X)) := quasiIso_of_isIso _
  have : IsIso (ofCCToCCIso (frobCx (frob e X))).hom := (ofCCToCCIso _).isIso_hom
  have hI : QuasiIso (ofCCToCCIso (frobCx (frob e X))).hom := quasiIso_of_isIso _
  have hU : QuasiIso (unrU e X) := by
    unfold unrU
    exact quasiIso_comp _ _
  have hU' : QuasiIso (K := (ofCC (frobCx (frob e X))).toCC)
      (L := (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Uq.toCC) (unrU e X) := hU
  exact tameLocalModelAt_of_quasiIso_kInj (T := tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq)
    (unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel) (unrU e X)
    (unr_square e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel)

end Square

section SquareField

variable {k : Type} [Field k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- **A tame local model from the quasi-isomorphism of the comparison, over a field**
(tex 3470–3481): if `tameCochainMap` (at `g = 1`, for `φ`, `σ` with `π φ = Frob`, `π σ = 1` and
`φ σ φ⁻¹ = σ^q`) is a quasi-isomorphism, then the genuine local complex `C^•_cont(G, M)`, the
genuine unramified condition `[X --Φ−1--> X]` and the inflation `urToLocal` form a
`TameLocalModelAt` for the tame model `tameNewPlace X Φ_X q`, with `eL.hom = unrL` and
`eU.hom = unrU` (over a field all four complexes are K-injective). Kind: PROVED. -/
theorem tameLocalModelAt_of_cochainQuasiIso (hφ : π φ = frobElt e) (hσ : π σ = 1)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel))) :
    ∃ m : TameLocalModelAt (natCx (contCochains k G M)) (ofCC (frobCx (frob e X)))
        (ofCCHom (urToLocal e π X f hf))
        (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq),
      m.eL.hom = unrL e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel ∧ m.eU.hom = unrU e X := by
  have : (natCx (contCochains k G M)).toCC.IsStrictlyGE 0 :=
    ZInQ.Manuscript.RC.Limits.natCx_toCC_isStrictlyGE _
  have : (ofCC (frobCx (frob e X))).toCC.IsStrictlyGE 0 := ofCC_frobCx_isStrictlyGE _
  have : (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Lq.toCC.IsStrictlyGE 0 :=
    tameNewPlace_Lq_isStrictlyGE _ _ q hq
  have : (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Uq.toCC.IsStrictlyGE 0 :=
    tameNewPlace_Uq_isStrictlyGE _ _ q hq
  have := ZInQ.Manuscript.RC.Limits.isKInjective_field (natCx (contCochains k G M)).toCC 0
  have := ZInQ.Manuscript.RC.Limits.isKInjective_field (ofCC (frobCx (frob e X))).toCC 0
  have := ZInQ.Manuscript.RC.Limits.isKInjective_field
    (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Lq.toCC 0
  have := ZInQ.Manuscript.RC.Limits.isKInjective_field
    (tameNewPlace (ModuleCat.of k X.V) (frob e X) q hq).Uq.toCC 0
  exact tameLocalModelAt_of_cochainQuasiIso_kInj e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel hQ

end SquareField

end ZInQ.Manuscript.RC.Local

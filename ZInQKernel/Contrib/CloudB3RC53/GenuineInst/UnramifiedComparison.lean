import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.CdOne

/-!
# Genuine instantiations, part 3: the unramified condition on `H⁰`, `H¹` and in degrees `≥ 2`

Manuscript `diophantine_zq.tex`, tex 3478–3487 (the unramified complex `[Φ−1]` as the condition at
the new places) and tex 4699–4701 (it has the degree-zero invariants of the full local complex and
injects in degree one).

The other team's `urToLocal e π X f hf : [W --(Φ−1)--> W] ⟶ C^•_cont(G, M)` (degree `0`:
constants; degree `1`: `x ↦ (g ↦ f (c_x (π g)))` with the `ℤ̂`-cocycle `c_x = urCocycle e X x`) and
its place form `urToLocal_galois` are compared with `urH0Equiv`, `urH1Equiv` and inflation:

* `homologyπ_h1Iso_hom`, `h1Iso_homologyπ`: `h1Iso` sends the class of a `1`-cycle to its value in
  `W ⧸ (Φ − 1)W`;
* `h1Equiv_homologyπ`: `urH1Equiv` sends it to the class of `c_x` (Tau Ceti's explicit model);
* `urToLocal_one_apply`, **`urToLocal_H1`**: the `H¹` map induced by `urToLocal` is `urH1Equiv`
  followed by inflation along `π` and `f` (`explicitMap1 π f`);
* `explicitMap1_injective`, **`urToLocal_H1_injective_range`**: for `π` surjective and `f`
  bijective it is injective, with image the inflated classes — the unramified part `H¹_ur`;
* `homologyπ_h0Iso_hom`, `h0Iso_homologyπ`, `h0Equiv_homologyπ`: `h0Iso` and `urH0Equiv` on classes
  (a `0`-cycle with value `x` goes to `x ∈ ker (Φ − 1)`, resp. the invariant `x`);
* `urToLocal_zero_apply`, `urToLocal_zero_invariant`: in degree `0`, `x ∈ ker (Φ − 1) = W^H` goes
  to the invariant `f x`;
* on the other team's genuine continuous cohomology (`ℕ`-indexed `contCochains`, through their
  `contH0AddEquiv`, `contH1AddEquiv`): `urClass0`, `urClass1` (the classes of the images under
  `urToLocal`), **`urClass0_contH0`** (`H⁰`: the class of the image of a `0`-cycle is `f` of its
  `urH0Equiv`-value) and **`urClass1_contH1`** (`H¹`: inflation-pushforward of `urH1Equiv`). The
  statement on the homology of the `ℤ`-indexed local complex `(natCx …).toCC` awaits the
  continuous-cochain bridge;
* node `UrToLocalOntoUnramified` at a place of a number field (`π = resUr`, surjective): the
  `H¹` statement above, together with the vanishing in degrees `≥ 2` of the cohomology of the
  two-term complex and of `Gal(K_w^ur/K_w)` with coefficients in `W` (`CdOne`). This is **not** a
  quasi-isomorphism statement: it says nothing about `H⁰` beyond `urToLocal_zero_invariant`, nothing
  about `Hⁿ(G_{K_w}, M)` for `n ≥ 2`, and no unramified subcomplex of the local complex is defined.
  The quasi-isomorphism `[W --(Φ−1)--> W] ⟶ C^•_cont(Gal(K_w^ur/K_w), W)` is the clearing lane's
  `urSelf_galois_quasiIso` (TameModel/UnramifiedQIso); see `UrToLocalFactorization`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory Limits TauCeti.ContCohomology ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Manuscript.RC.SelmerComplex

section H1Iso

variable {k : Type} [Ring k] {W : Type} [AddCommGroup W] [Module k W] (Φ : W →ₗ[k] W)

/-- **`h1Iso` on classes**: the class of a `1`-cycle `c` of `[W --(Φ−1)--> W]` goes to the class
of its value in `W ⧸ (Φ − 1)W`. -/
theorem homologyπ_h1Iso_hom : (frobCx Φ).homologyπ 1 ≫ (h1Iso Φ).hom =
    (frobCx Φ).iCycles 1 ≫ (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01
      (by decide)).hom ≫ ModuleCat.ofHom (LinearMap.range (Φ - 1)).mkQ := by
  have e : (h1Iso Φ).hom = (frobCx Φ).homologyι 1 ≫
      ((frobCx Φ).opcyclesIsoSc' 0 1 2 prev1 next1).hom ≫
      (ShortComplex.opcyclesIsoCokernel _).hom ≫ (cokernelIsoOfEq ((frobCx_d01 Φ).trans
        (Category.assoc _ _ _).symm)).hom ≫
      (cokernelCompIsIso ((HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom (Φ - 1))
        (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01 (by decide)).inv).hom ≫
      (cokernelEpiComp (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).hom
        (ModuleCat.ofHom (Φ - 1))).hom ≫
      (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (Φ - 1))).hom := rfl
  rw [e, HomologicalComplex.homology_π_ι_assoc,
    HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  simp [ShortComplex.opcyclesIsoCokernel_hom, cokernelCompIsIso_hom, cokernelEpiComp_hom]
  erw [π_comp_cokernelIsoOfEq_hom_assoc, cokernel.π_desc_assoc]
  erw [Category.assoc, cokernel.π_desc_assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

/-- The value in `W` of a `1`-cycle of `[W --(Φ−1)--> W]`. -/
abbrev cycVal1 (c : (frobCx Φ).cycles 1) : W :=
  (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01 (by decide)).hom.hom
    (((frobCx Φ).iCycles 1).hom c)

theorem h1Iso_homologyπ (c : (frobCx Φ).cycles 1) :
    (h1Iso Φ).hom (((frobCx Φ).homologyπ 1).hom c) = Submodule.Quotient.mk (cycVal1 Φ c) :=
  congrArg (fun g => g.hom c) (homologyπ_h1Iso_hom Φ)

/-- **`h0Iso` on classes**: the class of a `0`-cycle `c` of `[W --(Φ−1)--> W]` goes to its value
in `ker (Φ − 1)`. -/
theorem homologyπ_h0Iso_hom : (frobCx Φ).homologyπ 0 ≫ (h0Iso Φ).hom ≫
    ModuleCat.ofHom (LinearMap.ker (Φ - 1)).subtype =
    (frobCx Φ).iCycles 0 ≫ (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).hom := by
  have e : (h0Iso Φ).hom = ((frobCx Φ).isoHomologyπ (-1) 0 prev0 (frobCx_d_prev Φ)).inv ≫
      ((frobCx Φ).cyclesIsoSc' (-1) 0 1 prev0 next0).hom ≫ (ShortComplex.cyclesIsoKernel _).hom ≫
      (kernelIsoOfEq (frobCx_d01 Φ)).hom ≫
      (kernelIsIsoComp (HomologicalComplex.doubleXIso₀ _ rel01).hom
        (ModuleCat.ofHom (Φ - 1) ≫ (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv)).hom ≫
      (kernelCompMono (ModuleCat.ofHom (Φ - 1))
        (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv).hom ≫
      (ModuleCat.kernelIsoKer _).hom := rfl
  rw [e]
  have h1 : (frobCx Φ).homologyπ 0 ≫ ((frobCx Φ).isoHomologyπ (-1) 0 prev0 (frobCx_d_prev Φ)).inv = 𝟙 _ := by
    have := ((frobCx Φ).isoHomologyπ (-1) 0 prev0 (frobCx_d_prev Φ)).hom_inv_id
    rwa [HomologicalComplex.isoHomologyπ_hom] at this
  simp only [Category.assoc]
  rw [reassoc_of% h1]
  unfold frobCx at *
  simp [kernelCompMono_hom, kernelIsIsoComp_hom, ModuleCat.kernelIsoKer_hom_ker_subtype,
    ShortComplex.cyclesIsoKernel_hom]
  rw [show ModuleCat.ofHom (LinearMap.ker (Φ - 1)).subtype =
    ModuleCat.ofHom (LinearMap.ker (ModuleCat.ofHom (Φ - 1)).hom).subtype from rfl,
    ModuleCat.kernelIsoKer_hom_ker_subtype]
  simp only [kernel.lift_ι, Category.assoc]
  erw [kernelIsoOfEq_hom_comp_ι_assoc, kernel.lift_ι_assoc,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]

/-- The value in `W` of a `0`-cycle of `[W --(Φ−1)--> W]`. -/
abbrev cycVal0 (c : (frobCx Φ).cycles 0) : W :=
  (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).hom.hom
    (((frobCx Φ).iCycles 0).hom c)

theorem h0Iso_homologyπ (c : (frobCx Φ).cycles 0) :
    (((h0Iso Φ).hom (((frobCx Φ).homologyπ 0).hom c) : LinearMap.ker (Φ - 1)) : W) =
      cycVal0 Φ c :=
  congrArg (fun g => g.hom c) (homologyπ_h0Iso_hom Φ)

end H1Iso

section Agree

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]

/-- **`urH1Equiv` on classes** (read through Tau Ceti's explicit comparison): the class of a
`1`-cycle with value `x` goes to the class of the cocycle `c_x` (`urCocycle`). -/
theorem h1Equiv_homologyπ (c : (frobCx (frob e X)).cycles 1) :
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
        (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c)) =
      H1pi H X.V ⟨urCocycle e X (cycVal1 (frob e X) c), urCocycle_mem e X _⟩ := by
  have h0 : X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
      (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c)) =
      (h1CoinvEquiv e X).symm ((h1Iso (frob e X)).hom (((frobCx (frob e X)).homologyπ 1).hom c)) := by
    simp only [h1Equiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rfl
  rw [h0, h1Iso_homologyπ, AddEquiv.symm_apply_eq]
  change _ = h1ToCoinv e X (QuotientAddGroup.mk _)
  rw [h1ToCoinv_mk]
  exact congrArg _ (urCocycle_frob e X _).symm

/-- **`urH0Equiv` on classes**: the class of a `0`-cycle with value `x` goes to the invariant `x`
(`ContinuousCohomology.zeroIso`). PROVED. -/
theorem h0Equiv_homologyπ (c : (frobCx (frob e X)).cycles 0) :
    (((ContinuousCohomology.zeroIso X).hom
        (h0Equiv e X (((frobCx (frob e X)).homologyπ 0).hom c)) : X.ρ.invariants) : X.V) =
      cycVal0 (frob e X) c := by
  have h := h0Iso_homologyπ (frob e X) c
  simp only [h0Equiv, LinearEquiv.trans_apply]
  rw [← h]
  erw [Iso.inv_hom_id_apply]
  rfl

variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- The degree-`1` image under `urToLocal` of a `1`-cycle with value `x` is the cocycle
`g ↦ f (c_x (π g))`, the inflation of `c_x` along `π` pushed by `f`. -/
theorem urToLocal_one_apply (c : (frobCx (frob e X)).cycles 1) (g : G) :
    contFun (k := k) (G := G) (M := M)
        (((urToLocal e π X f hf).f 1).hom (((frobCx (frob e X)).iCycles 1).hom c)) (fun _ => g) =
      f (urCocycle e X (cycVal1 (frob e X) c) (π g)) := by
  rw [urToLocal_f₁]
  rfl

/-- **The `H¹` map induced by `urToLocal` is `urH1Equiv` followed by inflation along `π` and
`f`** (explicit classes, Tau Ceti's model): for every `1`-cycle `c` of `[W --(Φ−1)--> W]`, the
explicit class of its image cocycle in `C¹_cont(G, M)` is
`explicitMap1 π f (urH1Equiv [c])`. PROVED. -/
theorem urToLocal_H1 (c : (frobCx (frob e X)).cycles 1)
    (hz : (fun g : G => contFun (k := k) (G := G) (M := M)
      (((urToLocal e π X f hf).f 1).hom (((frobCx (frob e X)).iCycles 1).hom c)) (fun _ => g)) ∈
        Z1 G M) :
    H1pi G M ⟨_, hz⟩ =
      explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
          (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c))) := by
  rw [h1Equiv_homologyπ]
  erw [explicitMap1_mk]
  change H1pi G M _ = H1pi G M _
  congr 1
  apply Subtype.ext
  funext g
  erw [cocyclesMap1_apply]
  exact urToLocal_one_apply e π X f hf c g

include hf in
/-- `urLin₁ x` is a `1`-cocycle of the (`ℕ`-indexed) genuine complex `C^•_cont(G, M)`. -/
theorem urLin₁_d (x : X.V) : ((contCochains k G M).d 1 2).hom (urLin₁ e π X f x) = 0 := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (urToLocal_cocycle e π X f hf 2 (by simp))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    ModuleCat.hom_ofHom] at h
  exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom (natCx (contCochains k G M)) 1 2 rfl (urLin₁ e π X f x)).symm.trans h

include π hf in
/-- `urLin₀ y` is a `0`-cocycle for `y ∈ ker (Φ − 1)`. -/
theorem urLin₀_d (y : X.V) (hy : y ∈ LinearMap.ker (frob e X - 1)) :
    ((contCochains k G M).d 0 1).hom (urLin₀ (G := G) X f y) = 0 := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) (urToLocal_comm e π X f hf)
  change ((locCC (k := k) (G := G) (M := M)).d 0 1).hom (urLin₀ (G := G) X f y) =
    urLin₁ e π X f ((frob e X - 1) y) at h
  rw [LinearMap.mem_ker.mp hy, map_zero] at h
  exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom (natCx (contCochains k G M)) 0 1 rfl (urLin₀ (G := G) X f y)).symm.trans h

/-- The degree-`1` map `W → H¹_cont(G, M)` on the genuine continuous cohomology, `x ↦ [urLin₁ x]`
(the class of the image of `x` under `urToLocal`). -/
def urClass1 : ModuleCat.of k X.V ⟶ contCohomology k G M 1 :=
  (contCochains k G M).liftCycles (ModuleCat.ofHom (urLin₁ e π X f)) 2 (by simp)
    (by ext x; exact urLin₁_d e π X f hf x) ≫ (contCochains k G M).homologyπ 1

/-- The degree-`0` map `ker (Φ − 1) → H⁰_cont(G, M)`, `y ↦ [urLin₀ y]`. -/
def urClass0 : ModuleCat.of k (LinearMap.ker (frob e X - 1)) ⟶ contCohomology k G M 0 :=
  (contCochains k G M).liftCycles
    (ModuleCat.ofHom ((urLin₀ (G := G) X f).comp (LinearMap.ker (frob e X - 1)).subtype)) 1
    (by simp) (by ext y; exact urLin₀_d e π X f hf y.1 y.2) ≫ (contCochains k G M).homologyπ 0

/-- **On the genuine `H⁰_cont`**: the class of the image of a `0`-cycle with value `x` is the
invariant `f x`, i.e. `urToLocal` on `H⁰` is `urH0Equiv` (`h0Equiv_homologyπ`) followed by `f`,
read through the other team's `contH0AddEquiv`. PROVED. -/
theorem urClass0_contH0 (c : (frobCx (frob e X)).cycles 0) :
    ((contH0AddEquiv k G M ((urClass0 e π X f hf).hom
      ⟨cycVal0 (frob e X) c, by
        rw [← h0Iso_homologyπ]; exact ((h0Iso (frob e X)).hom _).2⟩)) : M) =
      f (cycVal0 (frob e X) c) := by
  rw [urClass0, ModuleCat.hom_comp, LinearMap.comp_apply, contH0AddEquiv_homologyπ]
  have := congrArg (fun φ => ModuleCat.Hom.hom φ (⟨cycVal0 (frob e X) c, by
        rw [← h0Iso_homologyπ]; exact ((h0Iso (frob e X)).hom _).2⟩ :
          LinearMap.ker (frob e X - 1)))
    (HomologicalComplex.liftCycles_i (contCochains k G M)
      (ModuleCat.ofHom ((urLin₀ (G := G) X f).comp (LinearMap.ker (frob e X - 1)).subtype)) 1
      (by simp) (by ext y; exact urLin₀_d e π X f hf y.1 y.2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact (congrArg (fun y => asFun k G M ((contSubCx k G M).el y :
    (groupCohomology.inhomogeneousCochains (rep k G M)).X 0) Fin.elim0) this).trans rfl

/-- **On the genuine `H¹_cont`**: the class of the image of a `1`-cycle `c` under `urToLocal` is
`explicitMap1 π f (urH1Equiv [c])` through the other team's `contH1AddEquiv`: the `H¹` map induced by
`urToLocal` on genuine continuous cohomology is `urH1Equiv` followed by inflation and `f`. PROVED. -/
theorem urClass1_contH1 (c : (frobCx (frob e X)).cycles 1) :
    contH1AddEquiv k G M ((urClass1 e π X f hf).hom (cycVal1 (frob e X) c)) =
      explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
          (h1Equiv e X (((frobCx (frob e X)).homologyπ 1).hom c))) := by
  rw [h1Equiv_homologyπ, urClass1, ModuleCat.hom_comp, LinearMap.comp_apply,
    contH1AddEquiv_homologyπ]
  erw [explicitMap1_mk]
  change H1pi G M _ = H1pi G M _
  congr 1
  apply Subtype.ext
  funext g
  erw [cocyclesMap1_apply]
  have := congrArg (fun φ => ModuleCat.Hom.hom φ (cycVal1 (frob e X) c))
    (HomologicalComplex.liftCycles_i (contCochains k G M) (ModuleCat.ofHom (urLin₁ e π X f)) 2
      (by simp) (by ext x; exact urLin₁_d e π X f hf x))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact (congrArg (fun y => asFun k G M ((contSubCx k G M).el y :
    (groupCohomology.inhomogeneousCochains (rep k G M)).X 1) (fun _ => g)) this).trans rfl

/-- Inflation-pushforward `explicitMap1 π f` is injective for `π` surjective and `f` bijective. PROVED. -/
theorem explicitMap1_injective (hπ : Function.Surjective π) (hfb : Function.Bijective f) :
    Function.Injective (explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    erw [explicitMap1_mk] at hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨m', rfl⟩ := hfb.2 m
    refine AddMonoidHom.mem_range.2 ⟨m', funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := hπ h
    apply hfb.1
    have := congrFun hm g
    rw [d0_apply] at this ⊢
    rw [map_sub, hf]
    exact this

/-- **On `H¹`, `urToLocal` is injective onto the unramified part** (`π` surjective, `f` bijective):
the map `H¹([W --(Φ−1)--> W]) → H¹(G, M)` induced by `urToLocal` (`urToLocal_H1`), i.e.
`y ↦ explicitMap1 π f (urH1Equiv y)`, is injective, and its image is the image of
inflation-pushforward `explicitMap1 π f`: the unramified classes. PROVED. -/
theorem urToLocal_H1_injective_range (hπ : Function.Surjective π) (hfb : Function.Bijective f) :
    Function.Injective (fun y => explicitMap1 H X.V G M π f.toAddMonoidHom
        continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (h1Equiv e X y))) ∧
      Set.range (fun y => explicitMap1 H X.V G M π f.toAddMonoidHom
        continuous_of_discreteTopology hf
        (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (h1Equiv e X y))) =
      Set.range (explicitMap1 H X.V G M π f.toAddMonoidHom continuous_of_discreteTopology hf) := by
  refine ⟨fun a b hab => (h1Equiv e X).injective
    (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.injective
      (explicitMap1_injective π X f hf hπ hfb hab)), ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(h1Equiv e X).symm (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x), ?_⟩
    simp only [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

/-- The degree-`0` image under `urToLocal` of `x ∈ W` is the constant `0`-cochain `f x`; for
`x ∈ ker (Φ − 1) = W^H` (`ker_frob_sub_one`) it is invariant, `f x ∈ M^G`. PROVED. -/
theorem urToLocal_zero_apply (x : X.V) (v : Fin 0 → G) :
    contFun (k := k) (G := G) (M := M) (((urToLocal e π X f hf).f 0).hom
      ((HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).inv.hom x)) v =
      f x := by
  rw [urToLocal_f₀]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply]
  rfl

include hf in
/-- The degree-`0` image of an invariant is invariant. -/
theorem urToLocal_zero_invariant (x : X.V) (hx : x ∈ LinearMap.ker (frob e X - 1)) (g : G) :
    g • f x = f x := by
  rw [← hf]
  have hinv : x ∈ X.ρ.invariants := ker_frob_sub_one e X ▸ hx
  exact congrArg f (hinv (π g))

end Agree

section Galois

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **(PROVED) The unramified condition `urToLocal_galois` on `H¹`, and vanishing in degrees `≥ 2`
of its source** (tex 3478–3487, 4699–4701), at a place `w ∈ S` of a number field, for a finite
discrete `Gal(K_w^ur/K_w)`-module `W` identified with the coefficients `M` by a `G_{K_w}`-equivariant
bijection `f`. Exactly:
* on `H¹`, the induced map `y ↦ inflation∘f (urH1Equiv y)` (`urToLocal_H1`) is injective, with image
  the inflated (unramified) classes `explicitMap1 (resUr) f`;
* for every `n ≥ 2`, `Hⁿ` of the two-term complex `[W --(Φ−1)--> W]` is zero and
  `Hⁿ(Gal(K_w^ur/K_w), W)` (Mathlib's continuous cohomology) is zero (`CdOne`).
This is not a quasi-isomorphism statement: nothing is asserted on `H⁰` (where `urToLocal` sends
`ker (Φ − 1)` to `G_{K_w}`-invariants: `urToLocal_zero_apply`, `urToLocal_zero_invariant`), nothing
about `Hⁿ(G_{K_w}, M)`, `n ≥ 2`, and no unramified subcomplex of the local complex is defined. The
quasi-isomorphism onto `C^•_cont(Gal(K_w^ur/K_w), W)` is `urSelf_galois_quasiIso`, and
`urToLocal_galois` factors through it followed by inflation (`UrToLocalFactorization`). -/
def UrToLocalOntoUnramified : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (w : Places K S)
    (k : Type) [CommRing k] [TopologicalSpace k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x),
    Function.Bijective f →
      (Function.Injective (fun y => explicitMap1 (GUr K w.1) X.V (Gloc K w.1)
          (ResMod (locMap K S w.1) M) (resUr K w.1) f.toAddMonoidHom
          continuous_of_discreteTopology hf
          (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (urH1Equiv K w.1 X y))) ∧
        Set.range (fun y => explicitMap1 (GUr K w.1) X.V (Gloc K w.1)
          (ResMod (locMap K S w.1) M) (resUr K w.1) f.toAddMonoidHom
          continuous_of_discreteTopology hf
          (X.explicitH1AddEquivContinuousCohomologyOfDiscrete.symm (urH1Equiv K w.1 X y))) =
        Set.range (explicitMap1 (GUr K w.1) X.V (Gloc K w.1) (ResMod (locMap K S w.1) M)
          (resUr K w.1) f.toAddMonoidHom continuous_of_discreteTopology hf)) ∧
      ∀ n : ℕ, 2 ≤ n → IsZero ((urCx K w.1 X).homology (n : ℤ)) ∧
        Subsingleton (continuousCohomology n X)

theorem urToLocalOntoUnramified_proof : UrToLocalOntoUnramified := by
  intro K _ _ S w k _ _ M _ _ _ _ _ _ _ X _ _ _ f hf hfb
  have hsc := instSMulCommClassResMod (k := k) (locMap K S w.1) M
  exact ⟨@urToLocal_H1_injective_range k _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1)
        (resUr K w.1) X _ _ _ (ResMod (locMap K S w.1) M) _ _ _ hsc _ _ _ f hf
        (resUr_surjective K w.1) hfb,
      fun n hn => ⟨isZero_homology _ (n : ℤ) (by omega) (by omega),
        ur_subsingleton_continuousCohomology_ge_two K w.1 X n hn⟩⟩

end Galois

end ZInQ.Contrib.CloudB3RC53.GenuineInst

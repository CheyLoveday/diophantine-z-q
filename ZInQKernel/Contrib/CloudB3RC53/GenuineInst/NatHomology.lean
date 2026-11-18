import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.UnramifiedComparison
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.ClassFormula

open CategoryTheory Limits ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-!
# Genuine instantiations, part 7: `urClass0/1` through the homology of the `ℤ`-indexed local complex

The genuine local complex of the other team's Selmer data is the extension by zero
`(natCx (contCochains k G M)).toCC` of the `ℕ`-indexed continuous cochains, and `urToLocal` maps
into it. Here:

* `natH0Iso`, `natH1Iso`: `H⁰`, `H¹` of `(natCx K).toCC` are `H⁰`, `H¹` of `K` (with
  `π_natH0Iso_hom`, `π_natH1Iso_hom`: classes of cycles go to classes of the same cochain);
* `natH0ToMathlib`, `natH1ToMathlib`: composed with the merged continuous-cochain bridge
  `contCohomologyLinearEquiv`, they are Mathlib's `continuousCohomology n (ofDiscreteModule k G M)`;
* **`natH0Iso_homologyMap_urToLocal`**, **`natH1Iso_homologyMap_urToLocal`**: the maps induced by
  `urToLocal` on `H⁰`, `H¹` of the `ℤ`-indexed local complex are `urClass0`, `urClass1`; with
  `urClass0_contH0`, `urClass1_contH1`, `h0Equiv_homologyπ`, `h1Equiv_homologyπ` they are
  `urH0Equiv`, resp. `urH1Equiv`, followed by inflation and `f`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

variable {k : Type} [CommRing k] (K : CochainComplex (ModuleCat.{0} k) ℕ)

/-- The degree-`1` short complexes of `(natCx K).toCC` and of `K` agree. -/
def natSc1Iso : (natCx K).toCC.sc' 0 1 2 ≅ K.sc' 0 1 2 :=
  ShortComplex.isoMk (Iso.refl (K.X 0)) (Iso.refl (K.X 1)) (Iso.refl (K.X 2))
    (by ext x; exact (GCx.toCC_d_hom (natCx K) 0 1 rfl x).trans rfl)
    (by ext x; exact (GCx.toCC_d_hom (natCx K) 1 2 rfl x).trans rfl)

/-- **`H¹` of the extension by zero is `H¹` of the `ℕ`-indexed complex.** -/
def natH1Iso : (natCx K).toCC.homology 1 ≅ K.homology 1 :=
  (natCx K).toCC.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (natSc1Iso K) ≪≫ (K.homologyIsoSc' 0 1 2 (by simp) (by simp)).symm

/-- The comparison of `1`-cycles. -/
def natCyc1 : (natCx K).toCC.cycles 1 ⟶ K.cycles 1 :=
  ((natCx K).toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (natSc1Iso K).hom ≫ (K.cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv

theorem natCyc1_i : natCyc1 K ≫ K.iCycles 1 = (natCx K).toCC.iCycles 1 := by
  simp [natCyc1]
  exact Category.comp_id _

theorem π_natH1Iso_hom :
    (natCx K).toCC.homologyπ 1 ≫ (natH1Iso K).hom = natCyc1 K ≫ K.homologyπ 1 := by
  simp [natH1Iso, natCyc1, ShortComplex.homologyπ_naturality_assoc]

/-- The degree-`0` short complexes: identity on `X₂ = K⁰`, `X₃ = K¹`; zero on `X₁`. -/
def natSc0Hom : (natCx K).toCC.sc' (-1) 0 1 ⟶ K.sc' 0 0 1 where
  τ₁ := 0
  τ₂ := 𝟙 (K.X 0)
  τ₃ := 𝟙 (K.X 1)
  comm₁₂ := by
    rw [zero_comp]
    change 0 = (natCx K).toCC.d (-1) 0 ≫ 𝟙 _
    rw [Category.comp_id]
    ext x
    exact ((GCx.toCC_d_hom (natCx K) (-1) 0 (by omega) x).trans rfl).symm
  comm₂₃ := by
    ext x
    exact (GCx.toCC_d_hom (natCx K) 0 1 rfl x).trans rfl

/-- The comparison of degree-`0` short complexes is an isomorphism on cycles. -/
instance : IsIso (ShortComplex.cyclesMap (natSc0Hom K)) :=
  ShortComplex.isIso_cyclesMap_of_isIso_of_mono' _ (by change IsIso (𝟙 _); infer_instance)
    (by change Mono (𝟙 _); infer_instance)

/-- The comparison of `0`-cycles. -/
def natCyc0 : (natCx K).toCC.cycles 0 ⟶ K.cycles 0 :=
  ((natCx K).toCC.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (natSc0Hom K) ≫ (K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).inv

/-- The comparison of `0`-cycles is an isomorphism. -/
instance : IsIso (natCyc0 K) := by unfold natCyc0; infer_instance

theorem natCyc0_i : natCyc0 K ≫ K.iCycles 0 = (natCx K).toCC.iCycles 0 := by
  simp [natCyc0]
  exact Category.comp_id _

/-- The differential into degree `0` of the extension by zero vanishes. -/
theorem natCx_d_neg (K : CochainComplex (ModuleCat.{0} k) ℕ) : (natCx K).toCC.d (-1) 0 = 0 := by
  ext x
  exact GCx.toCC_d_hom (natCx K) (-1) 0 (by omega) x

/-- **`H⁰` of the extension by zero is `H⁰` of the `ℕ`-indexed complex.** -/
def natH0Iso : (natCx K).toCC.homology 0 ≅ K.homology 0 :=
  ((natCx K).toCC.isoHomologyπ (-1) 0 (by simp) (natCx_d_neg K)).symm ≪≫ asIso (natCyc0 K) ≪≫
    K.isoHomologyπ 0 0 (by simp) (K.shape 0 0 (by simp))

theorem π_natH0Iso_hom :
    (natCx K).toCC.homologyπ 0 ≫ (natH0Iso K).hom = natCyc0 K ≫ K.homologyπ 0 := by
  have := ((natCx K).toCC.isoHomologyπ (-1) 0 (by simp) (natCx_d_neg K)).hom_inv_id
  rw [HomologicalComplex.isoHomologyπ_hom] at this
  simp only [natH0Iso, Iso.trans_hom, Iso.symm_hom, asIso_hom, HomologicalComplex.isoHomologyπ_hom]
  rw [reassoc_of% this]

section Bridge

variable (k G M : Type) [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousSMul k M] [ContinuousSMul G M]

/-- **Degrees `0`, `1` of the `ℤ`-indexed genuine local/global complex against Mathlib's continuous
cohomology** (through the merged continuous-cochain bridge `contCohomologyLinearEquiv`). -/
def natH0ToMathlib : (natCx (contCochains k G M)).toCC.homology 0 ≃ₗ[k]
    continuousCohomology 0 (TauCeti.ofDiscreteModule k G M) :=
  (natH0Iso (contCochains k G M)).toLinearEquiv.trans
    (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv k G M 0).symm

/-- Degree `1` of the same. -/
def natH1ToMathlib : (natCx (contCochains k G M)).toCC.homology 1 ≃ₗ[k]
    continuousCohomology 1 (TauCeti.ofDiscreteModule k G M) :=
  (natH1Iso (contCochains k G M)).toLinearEquiv.trans
    (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv k G M 1).symm

end Bridge

section Ur

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

open TauCeti.ContCohomology ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {k' : Type} [CommRing k'] [TopologicalSpace k']
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k' H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k' M] [DistribMulAction G M] [SMulCommClass G k' M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k'] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- **`urClass1` through the homology of the `ℤ`-indexed local complex**: the map induced by
`urToLocal` on `H¹((natCx C^•_cont(G, M)).toCC)`, read in `H¹_cont(G, M)` by `natH1Iso`, sends the
class of a `1`-cycle `c` to `urClass1 (value of c)`. Combined with `urClass1_contH1`, the `H¹` map
of `urToLocal` on the homology of the other team's local complex is `urH1Equiv` followed by
inflation and `f`. PROVED. -/
theorem natH1Iso_homologyMap_urToLocal (c : (frobCx (frob e X)).cycles 1) :
    (natH1Iso (contCochains k' G M)).hom ((HomologicalComplex.homologyMap
      (urToLocal e π X f hf) 1).hom (((frobCx (frob e X)).homologyπ 1).hom c)) =
      (urClass1 e π X f hf).hom (cycVal1 (frob e X) c) := by
  have h1 := congrArg (fun φ => φ.hom c)
    (HomologicalComplex.homologyπ_naturality (urToLocal e π X f hf) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1]
  have h2 := congrArg (fun φ => φ.hom (HomologicalComplex.cyclesMap (urToLocal e π X f hf) 1 |>.hom c))
    (π_natH1Iso_hom (contCochains k' G M))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2, urClass1, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((contCochains k' G M).iCycles 1)).1 inferInstance
  have h3 := congrArg (fun φ => φ.hom (HomologicalComplex.cyclesMap (urToLocal e π X f hf) 1 |>.hom c))
    (natCyc1_i (contCochains k' G M))
  have h4 := congrArg (fun φ => φ.hom c) (HomologicalComplex.cyclesMap_i (urToLocal e π X f hf) 1)
  have h5 := congrArg (fun φ => φ.hom (cycVal1 (frob e X) c))
    (HomologicalComplex.liftCycles_i (contCochains k' G M) (ModuleCat.ofHom (urLin₁ e π X f)) 2
      (by simp) (by ext x; exact urLin₁_d e π X f hf x))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3 h4 h5
  rw [h5]
  erw [h3, h4, urToLocal_f₁]
  rfl

/-- **`urClass0` through the homology of the `ℤ`-indexed local complex**: the map induced by
`urToLocal` on `H⁰((natCx C^•_cont(G, M)).toCC)`, read in `H⁰_cont(G, M)` by `natH0Iso`, sends the
class of a `0`-cycle `c` to `urClass0` of its value. With `urClass0_contH0` and
`h0Equiv_homologyπ`, on `H⁰` it is `urH0Equiv` followed by `f`. PROVED. -/
theorem natH0Iso_homologyMap_urToLocal (c : (frobCx (frob e X)).cycles 0) :
    (natH0Iso (contCochains k' G M)).hom ((HomologicalComplex.homologyMap
      (urToLocal e π X f hf) 0).hom (((frobCx (frob e X)).homologyπ 0).hom c)) =
      (urClass0 e π X f hf).hom ⟨cycVal0 (frob e X) c, by
        rw [← h0Iso_homologyπ]; exact ((h0Iso (frob e X)).hom _).2⟩ := by
  have h1 := congrArg (fun φ => φ.hom c)
    (HomologicalComplex.homologyπ_naturality (urToLocal e π X f hf) 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1]
  have h2 := congrArg (fun φ => φ.hom (HomologicalComplex.cyclesMap (urToLocal e π X f hf) 0 |>.hom c))
    (π_natH0Iso_hom (contCochains k' G M))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2, urClass0, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((contCochains k' G M).iCycles 0)).1 inferInstance
  have h3 := congrArg (fun φ => φ.hom (HomologicalComplex.cyclesMap (urToLocal e π X f hf) 0 |>.hom c))
    (natCyc0_i (contCochains k' G M))
  have h4 := congrArg (fun φ => φ.hom c) (HomologicalComplex.cyclesMap_i (urToLocal e π X f hf) 0)
  have h5 := congrArg (fun φ => φ.hom (⟨cycVal0 (frob e X) c, by
        rw [← h0Iso_homologyπ]; exact ((h0Iso (frob e X)).hom _).2⟩ :
          LinearMap.ker (frob e X - 1)))
    (HomologicalComplex.liftCycles_i (contCochains k' G M)
      (ModuleCat.ofHom ((urLin₀ (G := G) X f).comp (LinearMap.ker (frob e X - 1)).subtype)) 1
      (by simp) (by ext y; exact urLin₀_d e π X f hf y.1 y.2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3 h4 h5
  rw [h5]
  erw [h3, h4, urToLocal_f₀]
  rfl

end Ur

end ZInQ.Contrib.CloudB3RC53.GenuineInst

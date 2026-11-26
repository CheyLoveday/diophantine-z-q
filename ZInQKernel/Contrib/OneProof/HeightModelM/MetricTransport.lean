import ZInQKernel.Contrib.OneProof.HeightModelM.SemiAbelianModel

/-!
# Transport of the Hodge line, its lattice and the archimedean metric along `𝒢₀ → 𝒩`

Let `f : 𝒢 → 𝒩` be an open immersion homomorphism of group models of `A_L` (for instance
`𝒩⁰ → 𝒩`). It is an isomorphism on generic fibres (`ZInQ.H5Glue.genericIso_of_openImmersion`), so:

* the pull-back `Φ = hodgeMap 𝒢 𝒩 f g : 𝒩.hodgeSpace g → 𝒢.hodgeSpace g` is an `L`-linear
  bijection (`ZInQ.H5Glue.hodgeMapBijective`) carrying `⋀^g ω_𝒩` onto `⋀^g ω_𝒢`
  (`hodgeMap_detLattice`, `detLattice_le_hodgeMap`), so it preserves the index of a section
  (`secIndex_hodgeMap`);
* `p ↦ p ≫ f` is a homeomorphism `𝒢(ℂ)_τ ≃ₜ 𝒩(ℂ)_τ` for the analytic topologies
  (`continuous_ptsE`, `continuous_ptsE_symm`), compatible with the regular functions in both
  directions (`coord_pull`, `coord_push`), hence with the holomorphic charts
  (`isHolChart_pull`, `isHolChart_push`) and the measures `(i/2)^g η̃ ∧ η̄̃`
  (`hasAnFormDensityAt_pull`, `hasAnFormDensityAt_push`);
* `isAnMetricSq_hodgeMap`: `IsAnMetricSq 𝒩 τ η r → IsAnMetricSq 𝒢 τ (Φ η) r`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj MeasureTheory
open MonoidalCategory CartesianMonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.H5Glue
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.HeightModelM

section Transport

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsOpenImmersion f.left] [IsMonHom f]

/-! ## Lattice and index -/

/-- The pull-back of Hodge lines is injective. -/
theorem hodgeMap_injective (g : ℕ) : Function.Injective (hodgeMap 𝒢 𝒩 f g) :=
  (hodgeMapBijective K A L 𝒢 𝒩 f (genericIso_of_openImmersion 𝒢 𝒩 f) g).1

/-- The pull-back carries `⋀^g ω_𝒩` onto `⋀^g ω_𝒢`. -/
theorem map_detLattice (g : ℕ) :
    (𝒩.detLattice g).toAddSubgroup.map (hodgeMap 𝒢 𝒩 f g).toAddMonoidHom =
      (𝒢.detLattice g).toAddSubgroup := by
  haveI := genericIso_of_openImmersion 𝒢 𝒩 f
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hodgeMap_detLattice 𝒢 𝒩 f g y hy
  · intro hx
    obtain ⟨y, hy, rfl⟩ := detLattice_le_hodgeMap 𝒢 𝒩 f g x hx
    exact ⟨y, hy, rfl⟩

/-- Membership in the printed lattice is preserved. -/
theorem hodgeMap_mem_printedDetLattice (g : ℕ) {eta : 𝒩.hodgeSpace g}
    (h : eta ∈ printedDetLattice 𝒩 g) : hodgeMap 𝒢 𝒩 f g eta ∈ printedDetLattice 𝒢 g := by
  rw [printedDetLattice_eq] at h ⊢
  exact hodgeMap_detLattice 𝒢 𝒩 f g eta h

/-- **The index of a section is preserved.** -/
theorem secIndex_hodgeMap (g : ℕ) (eta : 𝒩.hodgeSpace g) :
    secIndex (printedDetLattice 𝒢 g) (hodgeMap 𝒢 𝒩 f g eta) =
      secIndex (printedDetLattice 𝒩 g) eta := by
  rw [printedDetLattice_eq, printedDetLattice_eq]
  have hinj : Function.Injective (hodgeMap 𝒢 𝒩 f g).toAddMonoidHom :=
    hodgeMap_injective 𝒢 𝒩 f g
  show (Submodule.span (𝓞 L) {hodgeMap 𝒢 𝒩 f g eta}).toAddSubgroup.relIndex
      (𝒢.detLattice g).toAddSubgroup =
    (Submodule.span (𝓞 L) {eta}).toAddSubgroup.relIndex (𝒩.detLattice g).toAddSubgroup
  rw [← map_detLattice 𝒢 𝒩 f g,
    ← map_span_singleton_toAddSubgroup (hodgeMap 𝒢 𝒩 f g) eta,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

/-! ## Complex points -/

/-- `p ↦ p ≫ f` on complex points. -/
def ptsE (τ : L →+* ℂ) : 𝒢.Pts τ ≃ 𝒩.Pts τ :=
  haveI := genericIso_of_openImmersion 𝒢 𝒩 f
  Equiv.ofBijective (fun p => p ≫ f) (pts_comp_bijective 𝒢 𝒩 f τ)

theorem ptsE_apply (τ : L →+* ℂ) (p : 𝒢.Pts τ) : ptsE 𝒢 𝒩 f τ p = p ≫ f := rfl

theorem comp_mul {τ : L →+* ℂ} (p q : 𝒢.Pts τ) : (p * q) ≫ f = (p ≫ f) * (q ≫ f) :=
  MonObj.mul_comp p q f

theorem comp_inv {τ : L →+* ℂ} (p : 𝒢.Pts τ) : p⁻¹ ≫ f = (p ≫ f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← comp_mul, inv_mul_cancel]
  exact MonObj.one_comp f

/-- Values of regular functions of `𝒢` along `f`, pushed to `𝒩`. -/
theorem evalAt_push {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (t : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V t = 𝒩.evalAt (p ≫ f) (f.left ''ᵁ V) ((f.left.appIso V).inv t) := by
  rw [evalAt_comp]
  by_cases hp : ⊤ ≤ p.left ⁻¹ᵁ V
  · rw [evalAt_res 𝒢 p (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge) hp]
    congr 1
    have hh : f.left.app (f.left ''ᵁ V) ≫
        𝒢.G.left.presheaf.map (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge).op =
        (f.left.appIso V).hom := by
      rw [Scheme.Hom.appIso_hom]
      rfl
    symm
    rw [← CommRingCat.comp_apply, hh, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  · have hp' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ (f.left ''ᵁ V)) := by
      rwa [Scheme.Hom.preimage_image_eq]
    unfold GroupModel.evalAt
    rw [dif_neg hp, dif_neg hp']

/-- The restriction identity behind `evalAt_push`, for germs. -/
theorem res_app_appIso_inv (V : 𝒢.G.left.Opens) (t : Γ(𝒢.G.left, V)) :
    𝒢.G.left.presheaf.map (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge).op
      (f.left.app (f.left ''ᵁ V) ((f.left.appIso V).inv t)) = t := by
  have hh : f.left.app (f.left ''ᵁ V) ≫
      𝒢.G.left.presheaf.map (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge).op =
      (f.left.appIso V).hom := by
    rw [Scheme.Hom.appIso_hom]
    rfl
  rw [← CommRingCat.comp_apply, hh, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]

/-! ## Regular coordinates in both directions -/

/-- **Coordinates of `𝒩` pulled back to `𝒢`.** -/
theorem coord_pull {g : ℕ} (U : Fin g → 𝒩.G.left.Opens) (hU : ∀ i, 𝒩.genericUnit ∈ U i)
    (s : ∀ i, Γ(𝒩.G.left, U i))
    (hm : ∀ i, 𝒩.G.left.presheaf.germ (U i) 𝒩.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒩.genStalk) :
    ∃ (U₀ : Fin g → 𝒢.G.left.Opens) (hU₀ : ∀ i, 𝒢.genericUnit ∈ U₀ i)
      (s₀ : ∀ i, Γ(𝒢.G.left, U₀ i))
      (hm₀ : ∀ i, 𝒢.G.left.presheaf.germ (U₀ i) 𝒢.genericUnit (hU₀ i) (s₀ i) ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk),
      (∀ (τ : L →+* ℂ) (p : 𝒢.Pts τ) (i : Fin g),
        𝒩.evalAt (p ≫ f) (U i) (s i) = 𝒢.evalAt p (U₀ i) (s₀ i)) ∧
      𝒢.wedge (fun i => ⟨_, hm₀ i⟩) = hodgeMap 𝒢 𝒩 f g (𝒩.wedge (fun i => ⟨_, hm i⟩)) := by
  have hU₀ : ∀ i, 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U i := fun i => by
    show f.left 𝒢.genericUnit ∈ U i
    rw [map_genericUnit' 𝒢 𝒩 f]
    exact hU i
  have hgerm : ∀ i, genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.germ (U i) 𝒩.genericUnit (hU i) (s i)) =
      𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U i) 𝒢.genericUnit (hU₀ i) (f.left.app (U i) (s i)) :=
    fun i => genMap_germ 𝒢 𝒩 f (U i) (hU i) (hU₀ i) (s i)
  have hm₀ : ∀ i, 𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U i) 𝒢.genericUnit (hU₀ i)
      (f.left.app (U i) (s i)) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := fun i => by
    rw [← hgerm i]
    exact genMap_mem_maximalIdeal 𝒢 𝒩 f _ (hm i)
  refine ⟨fun i => f.left ⁻¹ᵁ U i, hU₀, fun i => f.left.app (U i) (s i), hm₀,
    fun τ p i => evalAt_comp 𝒢 𝒩 f p (U i) (s i), ?_⟩
  rw [hodgeMap_wedgeGerm]
  congr 1
  funext i
  exact Subtype.ext (hgerm i).symm

/-- **Coordinates of `𝒢` pushed to `𝒩`.** -/
theorem coord_push {g : ℕ} (U₀ : Fin g → 𝒢.G.left.Opens) (hU₀ : ∀ i, 𝒢.genericUnit ∈ U₀ i)
    (s₀ : ∀ i, Γ(𝒢.G.left, U₀ i))
    (hm₀ : ∀ i, 𝒢.G.left.presheaf.germ (U₀ i) 𝒢.genericUnit (hU₀ i) (s₀ i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk) :
    ∃ (U : Fin g → 𝒩.G.left.Opens) (hU : ∀ i, 𝒩.genericUnit ∈ U i)
      (s : ∀ i, Γ(𝒩.G.left, U i))
      (hm : ∀ i, 𝒩.G.left.presheaf.germ (U i) 𝒩.genericUnit (hU i) (s i) ∈
        IsLocalRing.maximalIdeal 𝒩.genStalk),
      (∀ (τ : L →+* ℂ) (p : 𝒢.Pts τ) (i : Fin g),
        𝒩.evalAt (p ≫ f) (U i) (s i) = 𝒢.evalAt p (U₀ i) (s₀ i)) ∧
      𝒢.wedge (fun i => ⟨_, hm₀ i⟩) = hodgeMap 𝒢 𝒩 f g (𝒩.wedge (fun i => ⟨_, hm i⟩)) := by
  haveI := genericIso_of_openImmersion 𝒢 𝒩 f
  have hU : ∀ i, 𝒩.genericUnit ∈ f.left ''ᵁ U₀ i := fun i => by
    rw [← map_genericUnit' 𝒢 𝒩 f, ← SetLike.mem_coe, Scheme.Hom.coe_image]
    exact Set.mem_image_of_mem _ (hU₀ i)
  have hU' : ∀ i, 𝒢.genericUnit ∈ f.left ⁻¹ᵁ (f.left ''ᵁ U₀ i) := fun i => by
    rw [Scheme.Hom.preimage_image_eq]
    exact hU₀ i
  have hgerm : ∀ i, genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.germ (f.left ''ᵁ U₀ i) 𝒩.genericUnit (hU i)
      ((f.left.appIso (U₀ i)).inv (s₀ i))) =
      𝒢.G.left.presheaf.germ (U₀ i) 𝒢.genericUnit (hU₀ i) (s₀ i) := fun i => by
    rw [genMap_germ 𝒢 𝒩 f _ (hU i) (hU' i),
      ← TopCat.Presheaf.germ_res_apply 𝒢.G.left.presheaf
        (homOfLE (Scheme.Hom.preimage_image_eq f.left (U₀ i)).ge) _ (hU₀ i),
      res_app_appIso_inv 𝒢 𝒩 f]
  have hm : ∀ i, 𝒩.G.left.presheaf.germ (f.left ''ᵁ U₀ i) 𝒩.genericUnit (hU i)
      ((f.left.appIso (U₀ i)).inv (s₀ i)) ∈ IsLocalRing.maximalIdeal 𝒩.genStalk := fun i => by
    rw [← genMap_mem_maximalIdeal_iff 𝒢 𝒩 f, hgerm i]
    exact hm₀ i
  refine ⟨fun i => f.left ''ᵁ U₀ i, hU, fun i => (f.left.appIso (U₀ i)).inv (s₀ i), hm,
    fun τ p i => (evalAt_push 𝒢 𝒩 f p (U₀ i) (s₀ i)).symm, ?_⟩
  rw [hodgeMap_wedgeGerm]
  congr 1
  funext i
  exact Subtype.ext (hgerm i).symm

/-- Charts in matching coordinates agree along `f`. -/
theorem chartAt_comp {g : ℕ} {τ : L →+* ℂ} {U : Fin g → 𝒩.G.left.Opens}
    {s : ∀ i, Γ(𝒩.G.left, U i)} {U₀ : Fin g → 𝒢.G.left.Opens} {s₀ : ∀ i, Γ(𝒢.G.left, U₀ i)}
    (h : ∀ (p : 𝒢.Pts τ) (i : Fin g), 𝒩.evalAt (p ≫ f) (U i) (s i) = 𝒢.evalAt p (U₀ i) (s₀ i))
    (q q' : 𝒢.Pts τ) : chartAt 𝒩 τ U s (q ≫ f) (q' ≫ f) = chartAt 𝒢 τ U₀ s₀ q q' := by
  funext i
  show 𝒩.evalAt ((q ≫ f)⁻¹ * (q' ≫ f)) (U i) (s i) = 𝒢.evalAt (q⁻¹ * q') (U₀ i) (s₀ i)
  rw [← h, comp_mul, comp_inv]

/-! ## The analytic topologies -/

/-- `p ↦ p ≫ f` is continuous for the analytic topologies. -/
theorem continuous_ptsE (τ : L →+* ℂ) :
    @Continuous _ _ (anTop 𝒢 τ) (anTop 𝒩 τ) (ptsE 𝒢 𝒩 f τ) := by
  letI := anTop 𝒢 τ
  show Continuous[_, TopologicalSpace.generateFrom _] _
  rw [continuous_generateFrom_iff]
  rintro S ⟨U, s, V, hV, rfl⟩
  show IsOpen[TopologicalSpace.generateFrom _] _
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨f.left ⁻¹ᵁ U, f.left.app U s, V, hV, ?_⟩
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ptsE_apply]
  rw [evalAt_comp]
  exact Iff.rfl

/-- The inverse is continuous. -/
theorem continuous_ptsE_symm (τ : L →+* ℂ) :
    @Continuous _ _ (anTop 𝒩 τ) (anTop 𝒢 τ) (ptsE 𝒢 𝒩 f τ).symm := by
  letI := anTop 𝒩 τ
  show Continuous[_, TopologicalSpace.generateFrom _] _
  rw [continuous_generateFrom_iff]
  rintro S ⟨V, t, W, hW, rfl⟩
  show IsOpen[TopologicalSpace.generateFrom _] _
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨f.left ''ᵁ V, (f.left.appIso V).inv t, W, hW, ?_⟩
  ext q
  obtain ⟨p, rfl⟩ := (ptsE 𝒢 𝒩 f τ).surjective q
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Equiv.symm_apply_apply, ptsE_apply]
  rw [← evalAt_push]
  have hpre : (p ≫ f).left ⁻¹ᵁ (f.left ''ᵁ V) = p.left ⁻¹ᵁ V := by
    show p.left ⁻¹ᵁ (f.left ⁻¹ᵁ (f.left ''ᵁ V)) = _
    rw [Scheme.Hom.preimage_image_eq]
  rw [hpre]

/-! ## Holomorphic charts -/

/-- A holomorphic chart of `𝒩(ℂ)_τ` gives one of `𝒢(ℂ)_τ`. -/
theorem isHolChart_pull {g : ℕ} (τ : L →+* ℂ) :
    letI := anTop 𝒢 τ
    letI := anTop 𝒩 τ
    ∀ (h : 𝒢.Pts τ ≃ₜ 𝒩.Pts τ), (∀ p, h p = p ≫ f) →
    ∀ φ : OpenPartialHomeomorph (𝒩.Pts τ) (Fin g → ℂ), IsHolChart 𝒩 τ φ →
      IsHolChart 𝒢 τ (h.transOpenPartialHomeomorph φ) := by
  letI := anTop 𝒢 τ
  letI := anTop 𝒩 τ
  intro h hh φ hφ q hq U₀ hU₀ s₀ hm₀ hw
  obtain ⟨U, hU, s, hm, hev, hwe⟩ := coord_push 𝒢 𝒩 f U₀ hU₀ s₀ hm₀
  have hw' : 𝒩.wedge (fun i => ⟨_, hm i⟩) ≠ 0 := fun h0 => hw (by rw [hwe, h0, map_zero])
  have hq' : h q ∈ φ.source := by
    rw [Homeomorph.transOpenPartialHomeomorph_source] at hq
    exact hq
  obtain ⟨V, hVo, hV, hd, hdet⟩ := hφ (h q) hq' U hU s hm hw'
  have hfun : chartAt 𝒢 τ U₀ s₀ q ∘ (h.transOpenPartialHomeomorph φ).symm =
      chartAt 𝒩 τ U s (h q) ∘ φ.symm := by
    rw [Homeomorph.transOpenPartialHomeomorph_symm_apply]
    funext z
    simp only [Function.comp_apply]
    rw [← chartAt_comp 𝒢 𝒩 f (hev τ) q (h.symm (φ.symm z)), ← hh, ← hh, h.apply_symm_apply]
  have hpt : (h.transOpenPartialHomeomorph φ) q = φ (h q) := by
    rw [Homeomorph.transOpenPartialHomeomorph_apply]
    rfl
  refine ⟨V, hVo, by rw [hpt]; exact hV, by rw [hfun]; exact hd, ?_⟩
  rw [hfun, hpt]
  exact hdet

/-- A holomorphic chart of `𝒢(ℂ)_τ` gives one of `𝒩(ℂ)_τ`. -/
theorem isHolChart_push {g : ℕ} (τ : L →+* ℂ) :
    letI := anTop 𝒢 τ
    letI := anTop 𝒩 τ
    ∀ (h : 𝒢.Pts τ ≃ₜ 𝒩.Pts τ), (∀ p, h p = p ≫ f) →
    ∀ φ₀ : OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ), IsHolChart 𝒢 τ φ₀ →
      IsHolChart 𝒩 τ (h.symm.transOpenPartialHomeomorph φ₀) := by
  letI := anTop 𝒢 τ
  letI := anTop 𝒩 τ
  intro h hh φ₀ hφ₀ q hq U hU s hm hw
  obtain ⟨U₀, hU₀, s₀, hm₀, hev, hwe⟩ := coord_pull 𝒢 𝒩 f U hU s hm
  have hw' : 𝒢.wedge (fun i => ⟨_, hm₀ i⟩) ≠ 0 := by
    rw [hwe]
    intro h0
    exact hw (hodgeMap_injective 𝒢 𝒩 f g (h0.trans (map_zero _).symm))
  have hq' : h.symm q ∈ φ₀.source := by
    rw [Homeomorph.transOpenPartialHomeomorph_source] at hq
    exact hq
  obtain ⟨V, hVo, hV, hd, hdet⟩ := hφ₀ (h.symm q) hq' U₀ hU₀ s₀ hm₀ hw'
  have hfun : chartAt 𝒩 τ U s q ∘ (h.symm.transOpenPartialHomeomorph φ₀).symm =
      chartAt 𝒢 τ U₀ s₀ (h.symm q) ∘ φ₀.symm := by
    rw [Homeomorph.transOpenPartialHomeomorph_symm_apply]
    funext z
    simp only [Function.comp_apply, Homeomorph.symm_symm]
    rw [← chartAt_comp 𝒢 𝒩 f (hev τ) (h.symm q) (φ₀.symm z), ← hh, ← hh, h.apply_symm_apply]
  have hpt : (h.symm.transOpenPartialHomeomorph φ₀) q = φ₀ (h.symm q) := by
    rw [Homeomorph.transOpenPartialHomeomorph_apply]
    rfl
  refine ⟨V, hVo, by rw [hpt]; exact hV, by rw [hfun]; exact hd, ?_⟩
  rw [hfun, hpt]
  exact hdet

/-! ## The measures `(i/2)^g η̃ ∧ η̄̃` -/

/-- **Densities pull back.** If `nu` has the density of `(i/2)^g η̃ ∧ η̄̃` at `h p₀` on `𝒩(ℂ)_τ`
and `nu₀ E = nu (h(E))`, then `nu₀` has the density of `(i/2)^g (Φη)~ ∧ (Φη)~‾` at `p₀`. -/
theorem hasAnFormDensityAt_pull {g : ℕ} (τ : L →+* ℂ) (eta : 𝒩.hodgeSpace g) :
    letI := anTop 𝒢 τ
    letI := anTop 𝒩 τ
    letI := anBorel 𝒢 τ
    letI := anBorel 𝒩 τ
    ∀ (h : 𝒢.Pts τ ≃ₜ 𝒩.Pts τ), (∀ p, h p = p ≫ f) →
    ∀ (nu : Measure (𝒩.Pts τ)) (nu₀ : Measure (𝒢.Pts τ)),
      (∀ E, MeasurableSet E → nu₀ E = nu (h.symm ⁻¹' E)) →
    ∀ p₀ : 𝒢.Pts τ, HasAnFormDensityAt 𝒩 τ nu eta (h p₀) →
      HasAnFormDensityAt 𝒢 τ nu₀ (hodgeMap 𝒢 𝒩 f g eta) p₀ := by
  letI := anTop 𝒢 τ
  letI := anTop 𝒩 τ
  letI := anBorel 𝒢 τ
  letI := anBorel 𝒩 τ
  haveI : BorelSpace (𝒢.Pts τ) := ⟨rfl⟩
  haveI : BorelSpace (𝒩.Pts τ) := ⟨rfl⟩
  intro h hh nu nu₀ hmeas p₀ hnu φ₀ hφ₀ hp₀ U₀ hU₀ s₀ hm₀ l hrep ε hε
  set φ := h.symm.transOpenPartialHomeomorph φ₀ with hφdef
  have hφ : IsHolChart 𝒩 τ φ := isHolChart_push 𝒢 𝒩 f τ h hh φ₀ hφ₀
  have hpφ : h p₀ ∈ φ.source := by
    rw [hφdef, Homeomorph.transOpenPartialHomeomorph_source]
    show h.symm (h p₀) ∈ φ₀.source
    rw [h.symm_apply_apply]
    exact hp₀
  obtain ⟨U, hU, s, hm, hev, hwe⟩ := coord_push 𝒢 𝒩 f U₀ hU₀ s₀ hm₀
  have hrep' : eta = l • 𝒩.wedge (fun i => ⟨_, hm i⟩) := by
    apply hodgeMap_injective 𝒢 𝒩 f g
    rw [hrep, hwe, LinearMap.map_smul]
  obtain ⟨W, hW, hWb⟩ := hnu φ hφ hpφ U hU s hm l hrep' ε hε
  refine ⟨h ⁻¹' W, h.continuous.continuousAt.preimage_mem_nhds hW, fun E hE hEm => ?_⟩
  have hE' : MeasurableSet (h.symm ⁻¹' E) := h.symm.continuous.measurable hEm
  have hEW : h.symm ⁻¹' E ⊆ W := fun y hy => by
    have := hE hy
    rwa [Set.mem_preimage, h.apply_symm_apply] at this
  have hb := hWb _ hEW hE'
  have himg : φ '' (h.symm ⁻¹' E) = φ₀ '' E := by
    rw [hφdef, Homeomorph.transOpenPartialHomeomorph_apply, Set.image_comp,
      h.symm.image_preimage]
  have hfun : chartAt 𝒩 τ U s (h p₀) ∘ φ.symm = chartAt 𝒢 τ U₀ s₀ p₀ ∘ φ₀.symm := by
    rw [hφdef, Homeomorph.transOpenPartialHomeomorph_symm_apply]
    funext z
    simp only [Function.comp_apply, Homeomorph.symm_symm]
    rw [hh, hh, chartAt_comp 𝒢 𝒩 f (hev τ)]
  have hpt : φ (h p₀) = φ₀ p₀ := by
    rw [hφdef, Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply,
      h.symm_apply_apply]
  rw [himg, hfun, hpt] at hb
  rw [hmeas E hEm]
  exact hb

/-- **Densities push forward.** -/
theorem hasAnFormDensityAt_push {g : ℕ} (τ : L →+* ℂ) (eta : 𝒩.hodgeSpace g) :
    letI := anTop 𝒢 τ
    letI := anTop 𝒩 τ
    letI := anBorel 𝒢 τ
    letI := anBorel 𝒩 τ
    ∀ (h : 𝒢.Pts τ ≃ₜ 𝒩.Pts τ), (∀ p, h p = p ≫ f) →
    ∀ (nu₀ : Measure (𝒢.Pts τ)) (nu : Measure (𝒩.Pts τ)),
      (∀ E, MeasurableSet E → nu E = nu₀ (h ⁻¹' E)) →
    ∀ q₀ : 𝒩.Pts τ, HasAnFormDensityAt 𝒢 τ nu₀ (hodgeMap 𝒢 𝒩 f g eta) (h.symm q₀) →
      HasAnFormDensityAt 𝒩 τ nu eta q₀ := by
  letI := anTop 𝒢 τ
  letI := anTop 𝒩 τ
  letI := anBorel 𝒢 τ
  letI := anBorel 𝒩 τ
  haveI : BorelSpace (𝒢.Pts τ) := ⟨rfl⟩
  haveI : BorelSpace (𝒩.Pts τ) := ⟨rfl⟩
  intro h hh nu₀ nu hmeas q₀ hnu₀ φ hφ hq₀ U hU s hm l hrep ε hε
  set φ₀ := h.transOpenPartialHomeomorph φ with hφ₀def
  have hφ₀ : IsHolChart 𝒢 τ φ₀ := isHolChart_pull 𝒢 𝒩 f τ h hh φ hφ
  have hp : h.symm q₀ ∈ φ₀.source := by
    rw [hφ₀def, Homeomorph.transOpenPartialHomeomorph_source]
    show h (h.symm q₀) ∈ φ.source
    rw [h.apply_symm_apply]
    exact hq₀
  obtain ⟨U₀, hU₀, s₀, hm₀, hev, hwe⟩ := coord_pull 𝒢 𝒩 f U hU s hm
  have hrep₀ : hodgeMap 𝒢 𝒩 f g eta = l • 𝒢.wedge (fun i => ⟨_, hm₀ i⟩) := by
    rw [hrep, hwe, LinearMap.map_smul]
  obtain ⟨W, hW, hWb⟩ := hnu₀ φ₀ hφ₀ hp U₀ hU₀ s₀ hm₀ l hrep₀ ε hε
  refine ⟨h.symm ⁻¹' W, h.symm.continuous.continuousAt.preimage_mem_nhds hW,
    fun E hE hEm => ?_⟩
  have hE' : MeasurableSet (h ⁻¹' E) := h.continuous.measurable hEm
  have hEW : h ⁻¹' E ⊆ W := fun y hy => by
    have := hE hy
    rwa [Set.mem_preimage, h.symm_apply_apply] at this
  have hb := hWb _ hEW hE'
  have himg : φ₀ '' (h ⁻¹' E) = φ '' E := by
    rw [hφ₀def, Homeomorph.transOpenPartialHomeomorph_apply, Set.image_comp, h.image_preimage]
  have hfun : chartAt 𝒢 τ U₀ s₀ (h.symm q₀) ∘ φ₀.symm = chartAt 𝒩 τ U s q₀ ∘ φ.symm := by
    rw [hφ₀def, Homeomorph.transOpenPartialHomeomorph_symm_apply]
    funext z
    simp only [Function.comp_apply]
    rw [← chartAt_comp 𝒢 𝒩 f (hev τ), ← hh, ← hh, h.apply_symm_apply, h.apply_symm_apply]
  have hpt : φ₀ (h.symm q₀) = φ q₀ := by
    rw [hφ₀def, Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply,
      h.apply_symm_apply]
  rw [himg, hfun, hpt] at hb
  rw [hmeas E hEm]
  exact hb

/-! ## The metric -/

/-- **The archimedean metric is unchanged:** `IsAnMetricSq 𝒩 τ η r → IsAnMetricSq 𝒢 τ (Φ η) r`. -/
theorem isAnMetricSq_hodgeMap {g : ℕ} (τ : L →+* ℂ) (eta : 𝒩.hodgeSpace g) (r : ℝ)
    (hr : IsAnMetricSq 𝒩 τ eta r) : IsAnMetricSq 𝒢 τ (hodgeMap 𝒢 𝒩 f g eta) r := by
  letI := anTop 𝒢 τ
  letI := anTop 𝒩 τ
  letI := anBorel 𝒢 τ
  letI := anBorel 𝒩 τ
  haveI : BorelSpace (𝒢.Pts τ) := ⟨rfl⟩
  haveI : BorelSpace (𝒩.Pts τ) := ⟨rfl⟩
  let h : 𝒢.Pts τ ≃ₜ 𝒩.Pts τ :=
    { toEquiv := ptsE 𝒢 𝒩 f τ
      continuous_toFun := continuous_ptsE 𝒢 𝒩 f τ
      continuous_invFun := continuous_ptsE_symm 𝒢 𝒩 f τ }
  have hh : ∀ p, h p = p ≫ f := fun p => rfl
  let hm : 𝒢.Pts τ ≃ᵐ 𝒩.Pts τ := h.toMeasurableEquiv
  obtain ⟨⟨nu, hnu⟩, huniq⟩ := hr
  refine And.intro (Exists.intro (nu.map hm.symm) (And.intro ?_ fun p₀ => ?_))
    fun nu₀ hnu₀ => ?_
  · constructor
    rw [MeasurableEquiv.map_apply, Set.preimage_univ]
    exact hnu.1.measure_univ_lt_top
  · refine hasAnFormDensityAt_pull 𝒢 𝒩 f τ eta h hh nu (nu.map hm.symm) (fun E _ => ?_) p₀
      (hnu.2 (h p₀))
    rw [MeasurableEquiv.map_apply]
    rfl
  · have hpush : IsAnFormMeasure 𝒩 τ (nu₀.map hm) eta := by
      refine And.intro ⟨?_⟩ fun q₀ => ?_
      · rw [MeasurableEquiv.map_apply, Set.preimage_univ]
        exact hnu₀.1.measure_univ_lt_top
      · refine hasAnFormDensityAt_push 𝒢 𝒩 f τ eta h hh nu₀ (nu₀.map hm) (fun E _ => ?_) q₀
          (hnu₀.2 (h.symm q₀))
        rw [MeasurableEquiv.map_apply]
        rfl
    have := huniq _ hpush
    rwa [MeasurableEquiv.map_apply, Set.preimage_univ] at this

end Transport

end ZInQ.HeightModelM

import ZInQKernel.Contrib.OneProof.QMLattice
import ZInQKernel.Contrib.OneProof.GRCountX6

/-!
# gr56-prove: CM points on `X₆` inject into optimal embeddings (the lattice model)

Work in progress.
-/

set_option linter.all false

noncomputable section

namespace GR56

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open HDec.QMSplit.CNO (act act_add act_mul act_one act_smul act_eq_zero act_sub act_zero act_neg
  mem_qmOrbit_iff)

/-! ## §1 Lattice data of a QM pair over `ℂ` -/

/-- The orbit lattice `ι(𝒪)v`. -/
abbrev L (v : Fin 2 → ℂ) : Submodule ℤ (Fin 2 → ℂ) := HDec.FibreQMNorm.qmOrbit v

/-- **Lattice data of a QM abelian surface over `ℂ`** (all fields come from T35, T11(a) and the chain's
`QMLatticeAlgebra`): a uniformization `Φ : ℂ² → A(ℂ)` with kernel `Λ`, the analytic representation `ρ`, and a
`ℂ`-linear change of coordinates `Fl` carrying `Λ` onto `ι(𝒪)(τ, 1)ᵀ` and `ρ(ι(a))` to `ι(a)`. -/
structure LatData (A : PkgI3.AbVar ℂ) (q : QMStr A) where
  Λ : Submodule ℤ (Fin 2 → ℂ)
  disc : DiscreteTopology Λ
  Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ)
  hΦ : ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) Λ Φ
  ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)
  hρ : ∀ e z, Φ (ρ e z) = Φ z ≫ e.hom
  hρΛ : ∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ
  Fl : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)
  τ : ℂ
  hτ : 0 < τ.im
  hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ L ![τ, 1]
  hFρ : ∀ (a : O) z, Fl (ρ (q.iota a) z) = act (a : B) (Fl z)

theorem exists_latData (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : QMStr A) : Nonempty (LatData A q) := by
  have hE : HDec.HSyn.G0Split.FibreQM.UniformizationExistsT35 := AvSplit.Final.h38 hU hM
  have hR : HDec.HSyn.G0Split.FibreQM.T11aRiemannEnd :=
    ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hU hG)
  have hL : HDec.HSyn.G0Split.FibreQM.QMLatticeAlgebra :=
    HDec.HSyn.G0Split.FibreQM.qmLatticeAlgebra_of_free
      (HDec.HSyn.G0Split.FibreQM.qmLatticeFree_of HDec.HSyn.G0Split.FibreQM.qmSkolemNoetherC_proof
        HDec.QMSplit.CNO.qmClassNumberOne_proof)
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ A (RingHom.id ℂ) 2 hA
  haveI := hd
  obtain ⟨ρ, hρ, hpres⟩ := HDec.HSyn.G0Split.FibreQM.unif_ring_hom hR A hA Λ Φu hΦ
  obtain ⟨τ, hτ, Fl, hF, hFρ⟩ := hL Λ hlat (ρ.comp q.iota) (fun a z hz => hpres (q.iota a) z hz)
  have hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ L ![τ, 1] := by
    intro z
    rw [L, ← HDec.FibreQMNorm.qmLattice_eq_orbit hτ.ne', ← hF]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have : w = z := Fl.injective he
      rw [← this]; exact hw
  exact ⟨⟨Λ, hd, Φu, hΦ, ρ, hρ, hpres, Fl, τ, hτ, hΛ, fun a z => hFρ a z⟩⟩

namespace LatData

variable {A : PkgI3.AbVar ℂ} {q : QMStr A} (D : LatData A q)

/-- The base vector `v = (τ, 1)ᵀ`. -/
abbrev v : Fin 2 → ℂ := ![D.τ, 1]

theorem v_ne : D.v ≠ 0 := fun h => by simpa using congrFun h 1

/-- The normalized analytic representation `ρ' = Fl ∘ ρ ∘ Fl⁻¹`. -/
def ρn : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) where
  toFun e := D.Fl.toLinearMap ∘ₗ D.ρ e ∘ₗ D.Fl.symm.toLinearMap
  map_one' := LinearMap.ext fun z => by simp
  map_mul' e e' := LinearMap.ext fun z => by simp [map_mul]
  map_zero' := LinearMap.ext fun z => by simp
  map_add' e e' := LinearMap.ext fun z => by simp [map_add]

theorem ρn_apply (e : PkgI3.AbVar.End A) (z : Fin 2 → ℂ) : D.ρn e z = D.Fl (D.ρ e (D.Fl.symm z)) := rfl

theorem ρn_iota (a : O) (z : Fin 2 → ℂ) : D.ρn (q.iota a) z = act (a : B) z := by
  rw [ρn_apply, D.hFρ, LinearEquiv.apply_symm_apply]

theorem hT11 (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) :
    ∀ M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ), (∀ z ∈ D.Λ, M z ∈ D.Λ) →
      ∃! f : PkgI3.AbVar.End A, ∀ z, D.Φ (M z) = D.Φ z ≫ f.hom :=
  fun M hM => hC.2 A A 2 2 D.Λ D.Λ D.Φ D.Φ hA hA D.hΦ D.hΦ M hM

theorem ρ_injective (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) : Function.Injective D.ρ :=
  fun e e' h => (D.hT11 hC hA (D.ρ e) (D.hρΛ e)).unique (D.hρ e) (fun z => by rw [h]; exact D.hρ e' z)

theorem ρn_injective (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) : Function.Injective D.ρn := by
  intro e e' h
  apply D.ρ_injective hC hA
  refine LinearMap.ext fun w => ?_
  have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => D.Fl.symm (T (D.Fl w))) h
  simpa [ρn_apply] using this

theorem ρn_range (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (N : Module.End ℂ (Fin 2 → ℂ)) :
    (∀ z ∈ L D.v, N z ∈ L D.v) ↔ ∃ e, D.ρn e = N := by
  haveI := D.disc
  constructor
  · intro hN
    have hN' : ∀ z ∈ D.Λ, (D.Fl.symm.toLinearMap ∘ₗ N ∘ₗ D.Fl.toLinearMap) z ∈ D.Λ := by
      intro z hz
      rw [D.hΛ]
      simpa using hN _ ((D.hΛ z).1 hz)
    obtain ⟨f, hf, -⟩ := D.hT11 hC hA _ hN'
    have hfe : D.ρ f = D.Fl.symm.toLinearMap ∘ₗ N ∘ₗ D.Fl.toLinearMap :=
      HDec.HSyn.G0Split.FibreQM.lift_unique D.hΦ (fun z => by rw [D.hρ, hf])
    refine ⟨f, LinearMap.ext fun z => ?_⟩
    rw [ρn_apply, hfe]
    simp
  · rintro ⟨e, rfl⟩ z hz
    rw [ρn_apply, ← D.hΛ]
    apply D.hρΛ
    rw [D.hΛ]
    simpa using hz

end LatData

/-! ## §2 Isomorphisms of QM pairs over `ℂ` from scalars between the normalized lattices -/

theorem realize (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) (hM : ∀ z ∈ D.Λ, M z ∈ D'.Λ) :
    ∃! f : PkgI3.AbVar.Hom A A', ∀ z, D'.Φ (M z) = D.Φ z ≫ f.hom :=
  hC.2 A A' 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA' D.hΦ D'.hΦ M hM

/-- The scalar change of normalized coordinates as a map of raw coordinates. -/
def scalM {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (μ : ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  D'.Fl.symm.toLinearMap ∘ₗ (μ • LinearMap.id) ∘ₗ D.Fl.toLinearMap

theorem scalM_apply {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q)
    (D' : LatData A' q') (μ : ℂ) (z : Fin 2 → ℂ) : scalM D D' μ z = D'.Fl.symm (μ • D.Fl z) := rfl

theorem scalM_mem {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q)
    (D' : LatData A' q') (μ : ℂ) (h : ∀ w ∈ L D.v, μ • w ∈ L D'.v) : ∀ z ∈ D.Λ, scalM D D' μ z ∈ D'.Λ := by
  intro z hz
  rw [D'.hΛ, scalM_apply, LinearEquiv.apply_symm_apply]
  exact h _ ((D.hΛ z).1 hz)

/-- **An isomorphism of QM pairs over `ℂ` from a scalar `μ` with `μ·ι(𝒪)v = ι(𝒪)v'`.** -/
theorem qmIso_of_scalar (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (μ : ℂ) (hμ : μ ≠ 0) (h1 : ∀ w ∈ L D.v, μ • w ∈ L D'.v) (h2 : ∀ w ∈ L D'.v, μ⁻¹ • w ∈ L D.v) :
    Nonempty (QMIso q q') := by
  obtain ⟨f, hf, hfu⟩ := realize hC hA hA' D D' (scalM D D' μ) (scalM_mem D D' μ h1)
  obtain ⟨g, hg, -⟩ := realize hC hA' hA D' D (scalM D' D μ⁻¹) (scalM_mem D' D μ⁻¹ h2)
  have hgf : ∀ z, scalM D' D μ⁻¹ (scalM D D' μ z) = z := fun z => by
    simp [scalM_apply, smul_smul, mul_inv_cancel₀ hμ]
  have hfg : ∀ z, scalM D D' μ (scalM D' D μ⁻¹ z) = z := fun z => by
    simp [scalM_apply, smul_smul, inv_mul_cancel₀ hμ]
  have left : f.hom ≫ g.hom = 𝟙 _ := by
    obtain ⟨e, -, he⟩ := D.hT11 hC hA LinearMap.id (fun z hz => hz)
    have e1 := he (PkgI3.AbVar.Hom.mk' (f.hom ≫ g.hom)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hf, ← hg, hgf]; rfl)
    have e2 := he (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)
  have right : g.hom ≫ f.hom = 𝟙 _ := by
    obtain ⟨e, -, he⟩ := D'.hT11 hC hA' LinearMap.id (fun z hz => hz)
    have e1 := he (PkgI3.AbVar.Hom.mk' (g.hom ≫ f.hom)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hg, ← hf, hfg]; rfl)
    have e2 := he (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)
  refine ⟨⟨f, g, left, right, fun a => ?_⟩⟩
  -- both sides realize `scalM ∘ ρ(ι a) = ρ'(ι a) ∘ scalM`
  have hcomm : ∀ z, scalM D D' μ (D.ρ (q.iota a) z) = D'.ρ (q'.iota a) (scalM D D' μ z) := by
    intro z
    apply D'.Fl.injective
    rw [D'.hFρ, scalM_apply, scalM_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      D.hFρ]
    simp [act, Matrix.mulVec_smul]
  let N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := scalM D D' μ ∘ₗ D.ρ (q.iota a)
  have hN : ∀ z ∈ D.Λ, N z ∈ D'.Λ := fun z hz =>
    scalM_mem D D' μ h1 _ (D.hρΛ _ z hz)
  obtain ⟨e, -, he⟩ := realize hC hA hA' D D' N hN
  have e1 := he (PkgI3.AbVar.Hom.mk' ((q.iota a).hom ≫ f.hom)) (fun z => by
    rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← D.hρ, ← hf]; rfl)
  have e2 := he (PkgI3.AbVar.Hom.mk' (f.hom ≫ (q'.iota a).hom)) (fun z => by
    rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hf, ← D'.hρ]
    show D'.Φ (scalM D D' μ (D.ρ (q.iota a) z)) = _
    rw [hcomm])
  exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)

end GR56

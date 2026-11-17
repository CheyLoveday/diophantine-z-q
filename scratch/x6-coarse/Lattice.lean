import ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal

/-! Draft: `iso_of_quotient` from the textbook fields via the lattice model (no `IsogenyQuotient`). -/

set_option linter.style.longLine false

noncomputable section

namespace X6ALIdeal

open CategoryTheory AlgebraicGeometry Limits MonObj MonoidalCategory
open LeafQM LeafQM.AV
open HDec.LeafQM.AV.Pin.Exact (rep)
open scoped CategoryTheory.Obj

attribute [local instance] GR56.algQC

/-- `Spec ℂ → Spec ℚ̄` along `σQ`. -/
abbrev fC : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ))

/-- Base change of a homomorphism along `σQ`. -/
def bcHom {A A' : PkgI3.AbVar Qbar} (φ : PkgI3.AbVar.Hom A A') :
    PkgI3.AbVar.Hom (A.baseChange ℂ) (A'.baseChange ℂ) :=
  @PkgI3.AbVar.Hom.mk' ℂ _ (A.baseChange ℂ) (A'.baseChange ℂ) ((Over.pullback fC).map φ.hom)
    (Functor.map.instIsMonHom (F := Over.pullback fC) (f := φ.hom))

theorem bcHom_hom {A A' : PkgI3.AbVar Qbar} (φ : PkgI3.AbVar.Hom A A') :
    (bcHom φ).hom = (Over.pullback fC).map φ.hom := rfl

/-- The adjunction bijection `Hom(T ×_σ ℚ̄-side, A) ≃ Hom(T, A_ℂ)`, typed with `A_ℂ = A.baseChange ℂ`. -/
def hE (A : PkgI3.AbVar Qbar) (X : Over (Spec (CommRingCat.of ℂ))) :
    ((Over.map fC).obj X ⟶ A.X) ≃ (X ⟶ (A.baseChange ℂ).X) :=
  (Over.mapPullbackAdj fC).homEquiv X A.X

theorem hE_mul (A : PkgI3.AbVar Qbar) (X : Over (Spec (CommRingCat.of ℂ)))
    (p q : (Over.map fC).obj X ⟶ A.X) : hE A X (p * q) = hE A X p * hE A X q := by
  have key : ∀ r, hE A X r = (Over.mapPullbackAdj fC).unit.app X ≫ (Over.pullback fC).map r :=
    fun r => Adjunction.homEquiv_unit _ _ _ _
  rw [key, key, key]
  exact (congrArg _ (Functor.map_mul _ _ _)).trans (MonObj.comp_mul _ _ _)

theorem hE_one (A : PkgI3.AbVar Qbar) (X : Over (Spec (CommRingCat.of ℂ))) : hE A X 1 = 1 := by
  have h := hE_mul A X 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h

theorem hE_comp {A A' : PkgI3.AbVar Qbar} (φ : PkgI3.AbVar.Hom A A') (X : Over (Spec (CommRingCat.of ℂ)))
    (p : (Over.map fC).obj X ⟶ A.X) : hE A' X (p ≫ φ.hom) = hE A X p ≫ (bcHom φ).hom := by
  exact Adjunction.homEquiv_naturality_right _ _ _

/-- **Kernels commute with base change** on `T`-points of `A_ℂ`. -/
theorem ker_bc {A A' : PkgI3.AbVar Qbar} (φ : PkgI3.AbVar.Hom A A') (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (A.baseChange ℂ).X) :
    x ≫ (bcHom φ).hom = 1 ↔ (hE A T).symm x ≫ φ.hom = 1 := by
  have hn : x ≫ (bcHom φ).hom = hE A' T ((hE A T).symm x ≫ φ.hom) := by
    rw [hE_comp, Equiv.apply_symm_apply]
  rw [hn]
  constructor
  · intro h
    apply (hE A' T).injective
    rw [h, hE_one]
  · intro h
    rw [h, hE_one]

/-- `bcHom` between the base changes `bcQ P`, `bcQ P'` (typed with `GR56.bcQ`). -/
def bcHomQ {P P' : QMPair Qbar} (φ : PkgI3.AbVar.Hom P.A P'.A) :
    PkgI3.AbVar.Hom (GR56.bcQ P).A (GR56.bcQ P').A := bcHom φ

theorem bcHomQ_hom {P P' : QMPair Qbar} (φ : PkgI3.AbVar.Hom P.A P'.A) :
    (bcHomQ φ).hom = (Over.pullback fC).map φ.hom := rfl

theorem bcQ_iota (P : QMPair Qbar) (a : O) :
    ((GR56.bcQ P).q.iota a).hom = (Over.pullback fC).map (P.q.iota a).hom := rfl

theorem ker_bcQ {P P' : QMPair Qbar} (φ : PkgI3.AbVar.Hom P.A P'.A) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GR56.bcQ P).A.X) :
    x ≫ (bcHomQ φ).hom = 1 ↔ (hE P.A T).symm x ≫ φ.hom = 1 :=
  ker_bc φ T x

theorem ker_bcQ_iota (P : QMPair Qbar) (a : O) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GR56.bcQ P).A.X) :
    x ≫ ((GR56.bcQ P).q.iota a).hom = 1 ↔ (hE P.A T).symm x ≫ (P.q.iota a).hom = 1 :=
  ker_bc (P.q.iota a) T x

theorem bcQ_isog {P P' : QMPair Qbar} (φ : PkgI3.AbVar.Hom P.A P'.A) (ψ : PkgI3.AbVar.Hom P'.A P.A) (n : ℤ)
    (h : φ.hom ≫ ψ.hom = ((n : PkgI3.AbVar.End P.A)).hom) :
    (bcHomQ φ).hom ≫ (bcHomQ ψ).hom = ((n : PkgI3.AbVar.End (GR56.bcQ P).A)).hom := by
  have e : (Over.pullback fC).map φ.hom ≫ (Over.pullback fC).map ψ.hom =
      (Over.pullback fC).map ((n : PkgI3.AbVar.End P.A)).hom := by rw [← Functor.map_comp, h]
  exact e.trans (congrArg PkgI3.AbVar.Hom.hom (map_intCast (HDec.G0ModField.KernelField.endBC P.A ℂ) n))

theorem bcQ_equiv {P P' : QMPair Qbar} (φ : PkgI3.AbVar.Hom P.A P'.A) (a : O)
    (h : (P.q.iota a).hom ≫ φ.hom = φ.hom ≫ (P'.q.iota a).hom) :
    ((GR56.bcQ P).q.iota a).hom ≫ (bcHomQ φ).hom = (bcHomQ φ).hom ≫ ((GR56.bcQ P').q.iota a).hom := by
  have e : (Over.pullback fC).map (P.q.iota a).hom ≫ (Over.pullback fC).map φ.hom =
      (Over.pullback fC).map φ.hom ≫ (Over.pullback fC).map (P'.q.iota a).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  exact e

section Lat

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

set_option maxHeartbeats 1000000 in
include hU hG hM in
/-- **Every quotient of `(A, ι)` by `A[I_m]` is the twist `(A, ι ∘ Ad μ_m)`**, from the textbook fields
(uniformization, GAGA, torsion) through the lattice model: the lifts `F` of `φ` and `M` of `ι(μ_m)` have the same
lattice preimage (the kernel hypothesis on `ℂ`-points, `ker_bc`), so `M F⁻¹` and `F M⁻¹` are mutually inverse
lattice maps; they are realized over `ℂ` (`HomLatticeCorr`) and descend to `ℚ̄` (`GR56.qmIso_descend`). -/
theorem iso_of_quotient_lat (P P' : QMPair Qbar) (k : Fin 4) (φ : PkgI3.AbVar.Hom P.A P'.A)
    (hφ : IsIdealQuotient P (idealI k) P' φ) : Nonempty (QMIso (P.twist (rep k)).q P'.q) := by
  obtain ⟨hφe, ⟨ψ, n, hn, hφψ, -⟩, hφk⟩ := hφ
  have hC : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hU hG
  set D := GR56.datQ hU hG hM P with hD
  set D' := GR56.datQ hU hG hM P' with hD'
  have := D.disc
  have := D'.disc
  have hA : (GR56.bcQ P).A.dim = 2 := (GR56.bcQ P).surface
  have hA' : (GR56.bcQ P').A.dim = 2 := (GR56.bcQ P').surface
  obtain ⟨F, hF⟩ := hC.1 ℂ (GR56.bcQ P).A (GR56.bcQ P').A (RingHom.id ℂ) 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA'
    D.hΦ D'.hΦ (bcHomQ φ)
  obtain ⟨G, hGl⟩ := hC.1 ℂ (GR56.bcQ P').A (GR56.bcQ P).A (RingHom.id ℂ) 2 2 D'.Λ D.Λ D'.Φ D.Φ hA' hA
    D'.hΦ D.hΦ (bcHomQ ψ)
  set M := D.ρ ((GR56.bcQ P).q.iota (mu k)) with hMdef
  have hMΦ : ∀ z, D.Φ (M z) = D.Φ z ≫ ((GR56.bcQ P).q.iota (mu k)).hom := fun z => D.hρ _ z
  -- the kernel hypothesis on complex points
  have hker : ∀ z, F z ∈ D'.Λ ↔ M z ∈ D.Λ := by
    intro z
    rw [← D'.hΦ.2.1, ← D.hΦ.2.1, hF z, hMΦ z, ker_bcQ φ _ (D.Φ z), ker_bcQ_iota P (mu k) _ (D.Φ z)]
    exact (hφk _ _).trans (ker_mu P k _ _).symm
  -- `G F = n` and `M M = s_m`: both are injective
  have hGF : G ∘ₗ F = D.ρ (n : PkgI3.AbVar.End (GR56.bcQ P).A) := by
    apply HDec.HSyn.G0Split.FibreQM.lift_unique D.hΦ
    intro z
    rw [LinearMap.comp_apply, hGl, hF, D.hρ, Category.assoc, bcQ_isog φ ψ n hφψ]
  have hFinj : Function.Injective F := by
    intro z w h
    have h2 : (G ∘ₗ F) z = (G ∘ₗ F) w := by rw [LinearMap.comp_apply, LinearMap.comp_apply, h]
    rw [hGF, map_intCast, Module.End.intCast_apply, Module.End.intCast_apply] at h2
    exact smul_right_injective _ hn h2
  have hMM : M * M = D.ρ (sq k : PkgI3.AbVar.End (GR56.bcQ P).A) := by
    rw [hMdef, ← map_mul, ← map_mul, mu_mul_mu, map_intCast]
  have hMinj : Function.Injective M := by
    intro z w h
    have h2 : (M * M) z = (M * M) w := by rw [Module.End.mul_apply, Module.End.mul_apply, h]
    rw [hMM, map_intCast, Module.End.intCast_apply, Module.End.intCast_apply] at h2
    exact smul_right_injective _ (sq_ne_zero k) h2
  set eF := LinearEquiv.ofInjectiveEndo F hFinj
  set eM := LinearEquiv.ofInjectiveEndo M hMinj
  have hFe : ∀ w, F (eF.symm w) = w := fun w => eF.apply_symm_apply w
  have hFe' : ∀ z, eF.symm (F z) = z := fun z => eF.symm_apply_apply z
  have hMe : ∀ w, M (eM.symm w) = w := fun w => eM.apply_symm_apply w
  have hMe' : ∀ z, eM.symm (M z) = z := fun z => eM.symm_apply_apply z
  -- the two lattice maps
  set N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := M ∘ₗ (eF.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
  set N' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := F ∘ₗ (eM.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
  have hN : ∀ w ∈ D'.Λ, N w ∈ D.Λ := fun w hw => (hker (eF.symm w)).1 (by rw [hFe]; exact hw)
  have hN' : ∀ z ∈ D.Λ, N' z ∈ D'.Λ := fun z hz => (hker (eM.symm z)).2 (by rw [hMe]; exact hz)
  obtain ⟨χ, hχ, -⟩ := hC.2 (GR56.bcQ P').A (GR56.bcQ P).A 2 2 D'.Λ D.Λ D'.Φ D.Φ hA' hA D'.hΦ D.hΦ N hN
  obtain ⟨χ', hχ', -⟩ := hC.2 (GR56.bcQ P).A (GR56.bcQ P').A 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA' D.hΦ D'.hΦ N' hN'
  have hNN' : ∀ z, N (N' z) = z := fun z => by
    change M (eF.symm (F (eM.symm z))) = z
    rw [hFe', hMe]
  have hN'N : ∀ w, N' (N w) = w := fun w => by
    change F (eM.symm (M (eF.symm w))) = w
    rw [hMe', hFe]
  have e21 : χ'.hom ≫ χ.hom = 𝟙 _ := by
    obtain ⟨f0, -, hu⟩ := hC.2 (GR56.bcQ P).A (GR56.bcQ P).A 2 2 D.Λ D.Λ D.Φ D.Φ hA hA D.hΦ D.hΦ
      LinearMap.id (fun z hz => hz)
    have h1 := hu (PkgI3.AbVar.Hom.mk' (χ'.hom ≫ χ.hom)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hχ', ← hχ, hNN']; rfl)
    have h2 := hu (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
  have e12 : χ.hom ≫ χ'.hom = 𝟙 _ := by
    obtain ⟨f0, -, hu⟩ := hC.2 (GR56.bcQ P').A (GR56.bcQ P').A 2 2 D'.Λ D'.Λ D'.Φ D'.Φ hA' hA' D'.hΦ D'.hΦ
      LinearMap.id (fun z hz => hz)
    have h1 := hu (PkgI3.AbVar.Hom.mk' (χ.hom ≫ χ'.hom)) (fun w => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hχ, ← hχ', hN'N]; rfl)
    have h2 := hu (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun w => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
  -- equivariance
  have L1 : ∀ a : O, D'.ρ ((GR56.bcQ P').q.iota a) ∘ₗ F = F ∘ₗ D.ρ ((GR56.bcQ P).q.iota a) := by
    intro a
    apply HDec.HSyn.G0Split.FibreQM.lift_unique D'.hΦ
    intro z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, D'.hρ, hF, hF, D.hρ, Category.assoc, Category.assoc,
      bcQ_equiv φ a (hφe a)]
  have L2 : ∀ a : O, M * D.ρ ((GR56.bcQ P).q.iota a) = D.ρ ((GR56.bcQ P).q.iota (rep k a)) * M := by
    intro a
    rw [hMdef, ← map_mul, ← map_mul, ← map_mul, ← map_mul, rep_mul_mu]
  have hcomm : ∀ (a : O) z, N' (D.ρ ((GR56.bcQ P).q.iota (rep k a)) z) =
      D'.ρ ((GR56.bcQ P').q.iota a) (N' z) := by
    intro a z
    have h2 := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T (eM.symm z)) (L2 a)
    simp only [Module.End.mul_apply, hMe] at h2
    have h3 : eM.symm (D.ρ ((GR56.bcQ P).q.iota (rep k a)) z) = D.ρ ((GR56.bcQ P).q.iota a) (eM.symm z) := by
      rw [← h2, hMe']
    change F (eM.symm _) = _
    rw [h3]
    have h4 := congrArg (fun T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) => T (eM.symm z)) (L1 a)
    simp only [LinearMap.comp_apply] at h4
    rw [← h4]
    rfl
  refine GR56.qmIso_descend (P.twist (rep k)) P' ⟨χ', χ, e21, e12, fun a => ?_⟩
  have hpres : ∀ z ∈ D.Λ, (N' ∘ₗ D.ρ ((GR56.bcQ P).q.iota (rep k a))) z ∈ D'.Λ := by
    intro z hz
    rw [LinearMap.comp_apply]
    exact hN' _ (D.hρΛ _ z hz)
  have hex := hC.2 (GR56.bcQ P).A (GR56.bcQ P').A 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA' D.hΦ D'.hΦ _ hpres
  refine congrArg PkgI3.AbVar.Hom.hom (hex.unique (y₁ := PkgI3.AbVar.Hom.mk' (((GR56.bcQ P).q.iota (rep k a)).hom ≫ χ'.hom))
    (y₂ := PkgI3.AbVar.Hom.mk' (χ'.hom ≫ ((GR56.bcQ P').q.iota a).hom)) (fun z => ?_) (fun z => ?_))
  · rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, hχ', D.hρ, Category.assoc]
  · rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, hcomm, D'.hρ, hχ', Category.assoc]

end Lat

end X6ALIdeal

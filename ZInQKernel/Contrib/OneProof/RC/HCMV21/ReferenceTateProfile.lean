import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorReference
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RationalTateCoordinates
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CyclicTateChain

/-! Translate a geometric Tate chain to the split matrix profile of the
level order. Tex 8462–8468 and 9136–9146. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj Matrix TensorProduct

variable {k : Type} [Field k] {A : PkgI3.AbVar k} {a b : ℚ}

private theorem tateMatrix_baseChange (p : Prime)
    (c : Module.Basis (Fin 2) ℤ_[p.val] (A.T p.val)) (f : Module.End ℤ_[p.val] (A.T p.val)) :
    LinearMap.toMatrixAlgEquiv (c.baseChange ℚ_[p.val]) (f.baseChange ℚ_[p.val]) =
      matrixCast p.val (LinearMap.toMatrixAlgEquiv c f) := by
  ext i j
  change (LinearMap.toMatrixAlgEquiv (c.baseChange ℚ_[p.val])) (f.baseChange ℚ_[p.val]) i j =
    ((LinearMap.toMatrixAlgEquiv c f i j : ℤ_[p.val]) : ℚ_[p.val])
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply]
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one, PadicInt.algebraMap_apply]

private theorem tateMatrix_mulVec (p : Prime)
    (c : Module.Basis (Fin 2) ℤ_[p.val] (A.T p.val)) (f : Module.End ℤ_[p.val] (A.T p.val))
    (x : A.T p.val) :
    (LinearMap.toMatrixAlgEquiv c f).mulVec (c.equivFun x) = c.equivFun (f x) :=
  LinearMap.toMatrix_mulVec_repr c c f x

/-- A local basis carrying the Tate chain to the standard lattice gives
the matrix profile in the very same rational frame. The span hypothesis
uses the action of the geometric endomorphisms preserving the level. -/
theorem splitProfile_of_referenceTateChain (p : Prime) (n : ℕ)
    (R : Order a b) (embed : A.End →+* B a b) (C : Subgroup (A.Pt k))
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (B a b)))
    (e : Bp p.val a b ≃ₐ[ℚ_[p.val]] Module.End ℚ_[p.val] (A.V p.val))
    (he : ∀ x : A.End, e (toLocal p.val (embed x)) =
      (homT (ℓ := p.val) x).baseChange ℚ_[p.val])
    (c : Module.Basis (Fin 2) ℤ_[p.val] (A.T p.val))
    (hspan : (Submodule.span ℤ_[p.val]
      (tateHom p.val A A '' (levelEnd A C : Set A.End)) : Set (Module.End ℤ_[p.val] (A.T p.val))) =
      {f : Module.End ℤ_[p.val] (A.T p.val) | Set.MapsTo (⇑f) (c.equivFun ⁻¹' splitLevelLattice p.val 0 n)
        (c.equivFun ⁻¹' splitLevelLattice p.val 0 n)}) :
    ∃ d : Bp p.val a b ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val],
      d '' (R.completion p.val : Set _) = standardLevel p.val n := by
  let d := e.trans (LinearMap.toMatrixAlgEquiv (c.baseChange ℚ_[p.val]))
  let τ := Module.End.baseChangeHom ℤ_[p.val] ℚ_[p.val] (A.T p.val)
  let m := LinearMap.toMatrixAlgEquiv (c.baseChange ℚ_[p.val])
  refine ⟨d, ?_⟩
  let ρ : Bp p.val a b →ₗ[ℤ_[p.val]] Module.End ℚ_[p.val] (A.V p.val) :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r x => by
        change e ((r : ℚ_[p.val]) • x) = (r : ℚ_[p.val]) • e x
        exact map_smul e _ _ }
  have hι : ρ '' (R.completion p.val : Set (Bp p.val a b)) =
      τ '' (Submodule.span ℤ_[p.val] (tateHom p.val A A '' (levelEnd A C : Set A.End)) :
        Set (Module.End ℤ_[p.val] (A.T p.val))) := by
    change ρ '' (((R.completion p.val).toSubmodule : Submodule ℤ_[p.val] (Bp p.val a b)) :
      Set (Bp p.val a b)) = _
    rw [R.completion_toSubmodule, localLattice]
    erw [← Submodule.map_coe, Submodule.map_span]
    change (Submodule.span ℤ_[p.val] (ρ '' (toLocal p.val '' (R.ring : Set (B a b)))) :
      Set (Module.End ℚ_[p.val] (A.V p.val))) = _
    rw [← hR]
    rw [Set.image_image, Set.image_image]
    have hh : (fun x : A.End => ρ (toLocal p.val (embed x))) =
        (fun x => τ (tateHom p.val A A x)) := funext he
    rw [hh, ← Set.image_image]
    exact (congrArg SetLike.coe (Submodule.map_span τ.toLinearMap _)).symm.trans
      (Submodule.map_coe τ.toLinearMap _)
  have htrans : d '' (R.completion p.val : Set (Bp p.val a b)) =
      m '' (ρ '' (R.completion p.val : Set (Bp p.val a b))) :=
    (Set.image_image m ρ _).symm
  rw [htrans, hι, hspan, Set.image_image]
  have hm : (fun f : Module.End ℤ_[p.val] (A.T p.val) => m (τ f)) = fun f => matrixCast p.val (LinearMap.toMatrixAlgEquiv c f) :=
    funext (tateMatrix_baseChange p c)
  rw [hm, ← Set.image_image, standardLevel]
  congr 1
  ext M
  change _ ↔ M ∈ LocalWeights.eichler p.val n
  rw [Set.mem_image, (mapsTo_splitLevelLattice_iff M).symm]
  let f := (LinearMap.toMatrixAlgEquiv c).symm M
  have hf : LinearMap.toMatrixAlgEquiv c f = M := AlgEquiv.apply_symm_apply _ _
  have htest : Set.MapsTo (⇑f) (c.equivFun ⁻¹' splitLevelLattice p.val 0 n)
      (c.equivFun ⁻¹' splitLevelLattice p.val 0 n) ↔
      Set.MapsTo M.mulVec (splitLevelLattice p.val 0 n) (splitLevelLattice p.val 0 n) := by
    constructor
    · intro h x hx
      have hx' : c.equivFun (c.equivFun.symm x) = x := c.equivFun.apply_symm_apply x
      have hh := h (show c.equivFun (c.equivFun.symm x) ∈ splitLevelLattice p.val 0 n from hx'.symm ▸ hx)
      change c.equivFun (f (c.equivFun.symm x)) ∈ splitLevelLattice p.val 0 n at hh
      rw [← tateMatrix_mulVec p c f, hf, hx'] at hh
      exact hh
    · intro h x hx
      change c.equivFun (f x) ∈ splitLevelLattice p.val 0 n
      rw [← tateMatrix_mulVec p c f, hf]
      exact h hx
  change (∃ g, _ ∧ LinearMap.toMatrixAlgEquiv c g = M) ↔ _
  exact ⟨fun ⟨g, hg, hgM⟩ => htest.mp
      (((LinearMap.toMatrixAlgEquiv c).injective (hgM.trans hf.symm)) ▸ hg),
    fun h => ⟨f, htest.mpr h, hf⟩⟩

end ZInQ.Manuscript.RC.HCMV21

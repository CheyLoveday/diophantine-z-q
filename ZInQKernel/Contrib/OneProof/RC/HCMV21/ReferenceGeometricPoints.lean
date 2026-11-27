import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain

/-! Translate the reference subgroup to the geometric point type used in
the Tate module. Tex 9136–9146. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open scoped CategoryTheory.MonObj

noncomputable section

variable {k : Type} [Field k] [IsAlgClosed k] {A : PkgI3.AbVar k}

/-- The two test objects for points agree over an algebraically closed
base. The hom is the usual base-change map on the test schemes. -/
def geometricPointSourceIso (k : Type) [Field k] [IsAlgClosed k] :
    ptObj (K := k) (AlgebraicClosure k) ≅ ptObj (K := k) k := by
  let e := RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine Over.isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  rw [Algebra.algebraMap_self]
  change _ ≫ Spec.map (𝟙 (CommRingCat.of k)) = _
  rw [Spec.map_id, Category.comp_id]

/-- Transport rational points to the test field in the definition of
the geometric Tate module. -/
def levelPointsToClosure (A : PkgI3.AbVar k) : A.Pt k →* A.Pt (AlgebraicClosure k) where
  toFun P := (geometricPointSourceIso k).hom ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem levelPointsToClosure_injective (A : PkgI3.AbVar k) :
    Function.Injective (levelPointsToClosure A) := fun _ _ h =>
  (cancel_epi (geometricPointSourceIso k).hom).mp h

/-- The rational preservation test is the same test after transporting
the subgroup to the geometric point type. -/
theorem levelEnd_iff_levelHom_closure (C : Subgroup (A.Pt k)) (f : A.End) :
    f ∈ levelEnd A C ↔
      f ∈ levelHom (C.map (levelPointsToClosure A)) (C.map (levelPointsToClosure A)) := by
  have he (P : A.Pt k) : levelPointsToClosure A (P ≫ f.hom) =
      levelPointsToClosure A P ≫ f.hom := by
    change (geometricPointSourceIso k).hom ≫ (P ≫ f.hom) =
      ((geometricPointSourceIso k).hom ≫ P) ≫ f.hom
    exact (Category.assoc _ _ _).symm
  constructor
  · intro h P hP
    obtain ⟨Q, hQ, rfl⟩ := hP
    exact ⟨Q ≫ f.hom, h Q hQ, he Q⟩
  · intro h P hP
    obtain ⟨Q, hQ, heQ⟩ := h _ ⟨P, hP, rfl⟩
    exact (levelPointsToClosure_injective A (heQ.trans (he P).symm)) ▸ hQ

end

end ZInQ.Manuscript.RC.HCMV21

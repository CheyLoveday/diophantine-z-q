import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel

/-! The enhanced Hom group is the intersection of the two integral Hom
conditions at the ends of the level isogenies (tex 8462–8476, 9136–9148).
The second integrality condition is geometric descent through the source
level isogeny. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry
open PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k]
  {A A' B B' : PkgI3.AbVar k}

/-- A map of source curves preserves the given level kernels if and only
if it has an integral map of the quotient curves making the square commute. -/
theorem mem_levelHom_iff_exists_levelQuotientMap
    (u : Hom A A') (v : Hom B B') (f : Hom A B)
    [IsFinite u.hom.left] [Etale u.hom.left] [Surjective u.hom.left] :
    f ∈ levelHom (geometricKernel (L := AlgebraicClosure k) u)
        (geometricKernel (L := AlgebraicClosure k) v) ↔
      ∃! g : Hom A' B', u.hom ≫ g.hom = f.hom ≫ v.hom := by
  constructor
  · intro hf
    let fv : Hom A B' := Hom.mk' (f.hom ≫ v.hom)
    have h : ∀ P : A.Pt (AlgebraicClosure k), P ≫ u.hom = 1 → P ≫ fv.hom = 1 := by
      intro P hP
      change P ≫ (f.hom ≫ v.hom) = 1
      rw [← Category.assoc]
      exact hf P hP
    exact existsUnique_factor_of_etale_kernel u fv h
  · rintro ⟨g, hg, -⟩ P hP
    change P ≫ u.hom = 1 at hP
    change (P ≫ f.hom) ≫ v.hom = 1
    rw [Category.assoc, ← hg, ← Category.assoc, hP, MonObj.one_comp]

/-- In endomorphism coordinates the second maximal order is read by
intertwining with the same labelled level quotient. -/
theorem levelEnd_eq_intersection_of_levelQuotient
    (u : Hom A A') [IsFinite u.hom.left] [Etale u.hom.left] [Surjective u.hom.left] :
    {f : A.End | ∀ P ∈ geometricKernel (L := AlgebraicClosure k) u,
        P ≫ f.hom ∈ geometricKernel (L := AlgebraicClosure k) u} =
      {f : A.End | ∃ g : A'.End, u.hom ≫ g.hom = f.hom ≫ u.hom} := by
  ext f
  exact (mem_levelHom_iff_exists_levelQuotientMap u u f).trans
    ⟨fun ⟨g, hg, _⟩ => ⟨g, hg⟩,
      fun ⟨g, hg⟩ => by
        obtain ⟨d, hd, hu⟩ := existsUnique_factor_of_etale_kernel u
          (Hom.mk' (f.hom ≫ u.hom)) (fun P hP => by
            change P ≫ (f.hom ≫ u.hom) = 1
            rw [← hg, ← Category.assoc, hP, MonObj.one_comp])
        exact ⟨d, hd, hu⟩⟩

end ZInQ.Manuscript.RC.HCMV21

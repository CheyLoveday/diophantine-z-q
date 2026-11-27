import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceAdelic
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricRightIdeal

/-! The local read test for one actual prime-to-level quotient.
Tex 9265–9279. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {a b : ℚ} {R S : Order a b}
  {k : Type} [Field k] {A B : PkgI3.AbVar k}

/-- Away from the degree the geometric quotient lattice is the reference
order. Hence the corresponding part of the local comparison is the
ordinary unit test on the proposed relative factor. -/
theorem quotientReferenceRead_away {z : Adelic.FiniteUnits R}
    (hz : ReferenceOrderCoordinates R S z) {D : Type*} [DecidableEq D]
    (x₀ x : D) (I : D → LPIdeal S) (h₀ : I x₀ = fromAdelic (1 : Adelic.FiniteUnits S))
    (embed : A.End →+* Eichler.B a b)
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hS : embed '' (levelEnd A C : Set A.End) = (S.ring : Set (Eichler.B a b)))
    (hI : (I x).val = quotientRightIdeal S embed u v m hm hu hv C hC hS)
    (p : Prime) (hpm : IsUnit (m : ℤ_[p.val])) (w : (Bp p.val a b)ˣ) :
    (localRight R p (w * z.val p) =
      localRight R p ((geometricReferenceRead z x₀ I x).val p)) ↔
      w ∈ Adelic.localUnits S p := by
  rw [geometricReferenceRead_local hz x₀ I h₀ x p w, hI,
    localLattice_quotientRightIdeal_eq_completion S embed u v m hm hu hv C hC hS p.val hpm]
  have he : localRight S p 1 = (S.completion p.val).toSubmodule :=
    (localRight_one (R := S) p).trans (S.completion_toSubmodule p.val).symm
  calc
    _ ↔ localRight S p w = localRight S p 1 := ⟨fun h => h.trans he.symm, fun h => h.trans he⟩
    _ ↔ w⁻¹ * 1 ∈ Adelic.localUnits S p := localRight_eq_iff p w 1
    _ ↔ _ := by simp only [mul_one, Subgroup.inv_mem_iff]

/-- The identity quotient yields the reference right lattice in the
relative frame. -/
theorem identity_quotientRightIdeal_eq (S : Order a b) (embed : A.End →+* Eichler.B a b)
    (C : Subgroup (A.Pt k))
    (hS : embed '' (levelEnd A C : Set A.End) = (S.ring : Set (Eichler.B a b))) :
    quotientRightIdeal S embed 1 1 1 (by simp) (by simp only [Nat.cast_one, Int.cast_one]; exact Category.id_comp (𝟙 A.X))
      (by simp only [Nat.cast_one, Int.cast_one]; exact Category.id_comp (𝟙 A.X)) C (Nat.coprime_one_right _) hS =
      (fromAdelic (1 : Adelic.FiniteUnits S)).val := by
  apply rightIdeal_eq_fromAdelic_of_completions
  intro p
  have hC : (Nat.card C).Coprime 1 := Nat.coprime_one_right _
  have h : (1 : A.End).hom ≫ (1 : A.End).hom = ((1 : ℤ) : A.End).hom := by
    simp only [Int.cast_one]
    exact Category.id_comp (𝟙 A.X)
  have hm : IsUnit ((1 : ℕ) : ℤ_[p.val]) := by simp
  refine (localLattice_quotientRightIdeal_eq_completion S embed 1 1 1
    (by simp) h h C hC hS p.val hm).trans ?_
  exact (S.completion_toSubmodule p.val).trans (localRight_one (R := S) p).symm

end ZInQ.Manuscript.RC.HCMV21

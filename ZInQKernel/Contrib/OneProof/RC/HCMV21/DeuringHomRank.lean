import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeToGeometry
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Extract the rank-four geometric Hom lattice from the level-one
endomorphism theorem, using the actual isogeny in both directions. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry
open PkgI3.AbVar
open ZInQ.Contrib.MilneQuasiInverse ZInQ.DefFaltings
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A B D : PkgI3.AbVar k}

private noncomputable def precomposeHom (u : Hom A B) : Hom B D →+ Hom A D where
  toFun f := Hom.mk' (u.hom ≫ f.hom)
  map_zero' := Hom.ext' (by rw [Hom.hom_mk', Hom.hom_zero, MonObj.comp_one, Hom.hom_zero])
  map_add' f g := Hom.ext' (by simp only [Hom.hom_mk', Hom.hom_add, MonObj.comp_mul])

private theorem precomposeHom_injective (u : Hom A B) [Epi u.hom] :
    Function.Injective (precomposeHom (D := D) u) := by
  intro f g h
  apply Hom.ext'
  apply (cancel_epi u.hom).mp
  exact congrArg Hom.hom h

/-- The two precomposition maps into and out of the level-one
endomorphism lattice give a full-rank Hom group. -/
theorem hom_basis_of_epi_both_ways (u : Hom A B) (v : Hom B A) [Epi u.hom] [Epi v.hom]
    (b : Module.Basis (Fin 4) ℤ B.End) : Nonempty (Module.Basis (Fin 4) ℤ (Hom A B)) := by
  let F := (precomposeHom (D := B) u).toIntLinearMap
  let G := (precomposeHom (D := B) v).toIntLinearMap
  have hF : Function.Injective F := precomposeHom_injective u
  have hG : Function.Injective G := precomposeHom_injective v
  obtain ⟨n, c⟩ := (LinearMap.range G).basisOfPid b
  let e := c.map (LinearEquiv.ofInjective G hG).symm
  have : Module.Finite ℤ (Hom A B) := Module.Finite.of_basis e
  have : Module.Finite ℤ B.End := Module.Finite.of_basis b
  have hr := Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hG)
    (LinearMap.finrank_le_finrank_of_injective hF)
  have hn : n = 4 := by
    simpa only [Module.finrank_eq_card_basis e, Module.finrank_eq_card_basis b, Fintype.card_fin]
      using hr
  subst n
  exact ⟨e⟩

/-- The level-one Deuring candidate supplies the free integral
endomorphism basis of each actual supersingular curve. -/
theorem end_basis_of_deuring (h : DeuringSupersingularEndOrder)
    (q : ℕ) [Fact q.Prime] [IsAlgClosed k] [CharP k q]
    (hB : B.dim = 1) (hss : ∀ P : B.Pt k, P ^ q = 1 → P = 1) :
    Nonempty (Module.Basis (Fin 4) ℤ B.End) := by
  obtain ⟨a, b, _, R, ⟨e⟩, _⟩ := h q k B hB hss
  exact ⟨R.basis.map e.symm.toAddEquiv.toIntLinearEquiv⟩

/-- A prime-to-characteristic finite étale quotient has a reverse
homomorphism with both composites equal to multiplication by an
integer killing the original kernel. -/
theorem exists_reverse_of_etale_quotient (u : Hom A B)
    [IsFinite u.hom.left] [Etale u.hom.left] [Surjective u.hom.left]
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hk : ∀ P : A.Pt (AlgebraicClosure k), P ≫ u.hom = 1 → P ^ m = 1) :
    ∃ v : Hom B A, Epi u.hom ∧ Epi v.hom ∧
      u.hom ≫ v.hom = (((m : ℤ) : A.End)).hom ∧
      v.hom ≫ u.hom = (((m : ℤ) : B.End)).hom := by
  have : EffectiveEpi u.hom :=
    Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc u.hom
  obtain ⟨hf, he, hs⟩ := finiteEtale_mul_of_ne_zero A m hm
  let := hf
  let := he
  let := hs
  have : EffectiveEpi (((m : ℤ) : A.End)).hom :=
    Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc (((m : ℤ) : A.End)).hom
  obtain ⟨v, hv, -⟩ := existsUnique_factor_of_etale_kernel u (((m : ℤ) : A.End))
    (fun P hP => by rw [AvSplit.comp_natCast_hom']; exact hk P hP)
  refine ⟨v, inferInstance, epi_of_epi_fac hv, hv, ?_⟩
  apply (cancel_epi u.hom).mp
  rw [← Category.assoc, hv, AvSplit.comp_natCast_hom']
  have hid := AvSplit.comp_natCast_hom' A (𝟙 A.X) m
  rw [Category.id_comp] at hid
  rw [hid, MonObj.pow_comp, Category.id_comp]

end ZInQ.Manuscript.RC.HCMV21

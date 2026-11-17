import ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal

/-! Draft: base change of a QM pair along `σ ∈ Aut(ℚ̄/ℚ)`, to make `clause_of_galoisNatural` unconditional. -/

set_option linter.style.longLine false

noncomputable section

namespace X6ALIdeal

open CategoryTheory AlgebraicGeometry Limits MonObj
open LeafQM LeafQM.AV

/-- The base change of a QM pair along `σ : ℚ̄ → ℚ̄` (`AbVar.baseChange` along `σ`, with `ι_σ = endBC ∘ ι`). -/
def bcAut (σ : Qbar →+* Qbar) (P : QMPair Qbar) : QMPair Qbar :=
  letI : Algebra Qbar Qbar := σ.toAlgebra
  ⟨P.A.baseChange Qbar, by rw [PkgI3.AbVar.dim_baseChange]; exact P.surface,
   ⟨(HDec.G0ModField.KernelField.endBC P.A Qbar).comp P.q.iota,
    (HDec.G0ModField.KernelField.endBC_injective P.A Qbar).comp P.q.injective⟩⟩

theorem isBaseChange_bcAut (σ : Qbar →+* Qbar) (P : QMPair Qbar) :
    IsBaseChangeOfPair σ P (bcAut σ P) := by
  refine ⟨pullback.fst P.A.X.hom (Spec.map (CommRingCat.ofHom σ)), IsPullback.of_hasPullback _ _,
    fun a => ?_, ?_⟩
  · change ((Over.pullback (Spec.map (CommRingCat.ofHom σ))).map (P.q.iota a).hom).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (P.q.iota a).hom.left
    simp
  · rw [ShimuraSplit.pt_one_left, ShimuraSplit.pt_one_left]
    change (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom σ))) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map η[P.A.X]).left ≫ pullback.fst _ _ = _
    rw [Over.comp_left, Category.assoc]
    simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc]
    congr 1
    have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom σ))))
    have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom)
      (g := Spec.map (CommRingCat.ofHom σ))
    sorry

theorem exists_bc_aut (σ : Qbar ≃ₐ[ℚ] Qbar) (P : QMPair Qbar) :
    ∃ Q : QMPair Qbar, IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q :=
  ⟨bcAut σ P, isBaseChange_bcAut σ P⟩

end X6ALIdeal

import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain
import ZInQKernel.Contrib.OneProof.RC.Adelic.FullPatch
import ZInQKernel.Contrib.OneProof.CharPolyIndepOfEllAlgClosed

/-! The rational Tate chart of a given quaternion frame is forced by
its action on reference endomorphisms. This construction does not
choose a different reference at each prime. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler PkgI3.AbVar ZInQ.Contrib.OneProof.CharPolyEll
open scoped CategoryTheory.MonObj TensorProduct

variable {k : Type} [Field k] {A : PkgI3.AbVar k} {a b : ℚ}

private theorem algHom_liftEquiv_surjective {K E D : Type*}
    [Field K] [Ring E] [Ring D] [Algebra K D]
    (f : E →ₐ[ℤ] D) (hf : Submodule.span K (Set.range f) = ⊤) :
    Function.Surjective (AlgHom.liftEquiv ℤ K E D f) := by
  let g := AlgHom.liftEquiv ℤ K E D f
  change Function.Surjective g.toLinearMap
  apply LinearMap.range_eq_top.mp
  rw [← top_le_iff, ← hf]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact ⟨1 ⊗ₜ[ℤ] x, by simp [g]⟩

private theorem baseChangeEnd_span (p : ℕ) [Fact p.Prime]
    (c : Module.Basis (Fin 2) ℤ_[p] (A.T p)) :
    Submodule.span ℚ_[p] (Set.range fun f : Module.End ℤ_[p] (A.T p) => f.baseChange ℚ_[p]) =
      ⊤ := by
  let d := c.baseChange ℚ_[p]
  apply top_unique
  rw [← (d.linearMap d).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨c.linearMap c i, ?_⟩
  apply d.ext
  intro j
  calc
    ((c.linearMap c i).baseChange ℚ_[p]) (d j) =
        1 ⊗ₜ[ℤ_[p]] (c.linearMap c i) (c j) := by
      rw [show d j = 1 ⊗ₜ[ℤ_[p]] c j from Module.Basis.baseChange_apply ..,
        LinearMap.baseChange_tmul]
    _ = (d.linearMap d i) (d j) := by
      rw [Module.Basis.linearMap_apply_apply, Module.Basis.linearMap_apply_apply]
      split_ifs <;> simp [d]

/-- From one rational framing of the reference order, geometric Tate
rank and the full span of level-one endomorphisms give the compatible
rational chart at a split prime. -/
theorem exists_rationalTate_coordinates_of_endOrder
    (R : Order a b) (embed : A.End →+* Eichler.B a b) (C : Subgroup (A.Pt k))
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (p : Adelic.Prime)
    (bE : Module.Basis (Fin 4) ℤ A.End) (bT : Module.Basis (Fin 2) ℤ_[p.val] (A.T p.val))
    (hfull : Submodule.span ℤ_[p.val] (Set.range (tateHom p.val A A)) = ⊤) :
    ∃ e : Bp p.val a b ≃ₐ[ℚ_[p.val]] Module.End ℚ_[p.val] (A.V p.val),
      ∀ x : A.End, e (toLocal p.val (embed x)) =
        (homT (ℓ := p.val) x).baseChange ℚ_[p.val] := by
  let Q := ℚ_[p.val]
  let L := Q ⊗[ℤ] A.End
  let f := ((toLocal p.val).comp embed).toIntAlgHom
  let τ := Module.End.baseChangeHom ℤ_[p.val] Q (A.T p.val)
  let g := τ.toRingHom.comp (homTRingHom A p.val)
  have hf : Submodule.span Q (Set.range f) = ⊤ := by
    have hl := Adelic.localLattice_full p R.full
    have hs : Submodule.span Q (toLocal p.val '' (R.ring : Set (Eichler.B a b))) = ⊤ := by
      have hs' := hl.span_eq_top
      rw [localLattice, Submodule.span_span_of_tower] at hs'
      exact hs'
    rw [← hR, Set.image_image] at hs
    apply top_unique
    rw [← hs]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hg : Submodule.span Q (Set.range g.toIntAlgHom) = ⊤ := by
    have hh : τ '' Set.range (tateHom p.val A A) = Set.range g.toIntAlgHom := by
      rw [← Set.range_comp]
      rfl
    rw [← hh, ← Submodule.span_span_of_tower ℤ_[p.val]]
    change Submodule.span Q ((Submodule.span ℤ_[p.val] (τ.toLinearMap ''
      Set.range (tateHom p.val A A))) : Set (Module.End Q (A.V p.val))) = ⊤
    rw [← Submodule.map_span, hfull, Submodule.map_top]
    exact baseChangeEnd_span p.val bT
  let fQ := AlgHom.liftEquiv ℤ Q A.End (Bp p.val a b) f
  let gQ := AlgHom.liftEquiv ℤ Q A.End (Module.End Q (A.V p.val)) g.toIntAlgHom
  let : Module.Finite Q L := Module.Finite.of_basis (bE.baseChange Q)
  have hL : Module.finrank Q L = 4 := by
    rw [Module.finrank_eq_card_basis (bE.baseChange Q), Fintype.card_fin]
  let d := bT.baseChange Q
  let : Module.Finite Q (Module.End Q (A.V p.val)) := Module.Finite.of_basis (d.linearMap d)
  have hA : Module.finrank Q (Module.End Q (A.V p.val)) = 4 := by
    rw [Module.finrank_eq_card_basis (d.linearMap d)]
    decide
  have hB : Module.finrank Q (Bp p.val a b) = 4 := by
    rw [Module.finrank_eq_card_basis (QuaternionAlgebra.basisOneIJK (a : Q) 0 (b : Q)),
      Fintype.card_fin]
  have fs := algHom_liftEquiv_surjective f hf
  have gs := algHom_liftEquiv_surjective g.toIntAlgHom hg
  let eF := AlgEquiv.ofBijective fQ
    ⟨(fQ.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank (hL.trans hB.symm)).mpr fs, fs⟩
  let eG := AlgEquiv.ofBijective gQ
    ⟨(gQ.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank (hL.trans hA.symm)).mpr gs, gs⟩
  refine ⟨eF.symm.trans eG, fun x => ?_⟩
  have hF : eF (1 ⊗ₜ[ℤ] x) = toLocal p.val (embed x) := by
    change fQ (1 ⊗ₜ[ℤ] x) = _
    simp [fQ, f]
  have hG : eG (1 ⊗ₜ[ℤ] x) = (homT (ℓ := p.val) x).baseChange ℚ_[p.val] := by
    change gQ (1 ⊗ₜ[ℤ] x) = _
    rw [show gQ (1 ⊗ₜ[ℤ] x) = (1 : Q) • g.toIntAlgHom x from AlgHom.liftEquiv_tmul .., one_smul]
    rfl
  rw [← hF, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, hG]

/-- Use the existing geometric Tate theorem to obtain the compatible
split chart directly from the level-one maximal-order candidate. -/
theorem exists_rationalTate_coordinates_of_deuring (h : DeuringSupersingularEndOrder)
    (hT : PkgI3.TateModuleFree)
    (q : ℕ) [Fact q.Prime] [IsAlgClosed k] [CharP k q] (hA : A.dim = 1)
    (hss : ∀ P : A.Pt k, P ^ q = 1 → P = 1)
    (R : Order a b) (embed : A.End →+* Eichler.B a b) (C : Subgroup (A.Pt k))
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (p : Adelic.Prime) (hp : (p.val : k) ≠ 0) :
    ∃ e : Bp p.val a b ≃ₐ[ℚ_[p.val]] Module.End ℚ_[p.val] (A.V p.val),
      ∀ x : A.End, e (toLocal p.val (embed x)) =
        (homT (ℓ := p.val) x).baseChange ℚ_[p.val] := by
  obtain ⟨bE⟩ := end_basis_of_deuring h q hA hss
  obtain ⟨hFree, hFinite, hRank⟩ := hT k A p.val hp
  have hRank' : ((Module.finrank ℤ_[p.val] (A.T p.val) : ℕ∞) : WithBot ℕ∞) = 2 := by
    simpa only [hA, mul_one] using hRank
  let bT := Module.finBasisOfFinrankEq ℤ_[p.val] (A.T p.val)
    (WithTop.coe_inj.mp (WithBot.coe_inj.mp hRank'))
  exact exists_rationalTate_coordinates_of_endOrder R embed C hR p bE bT
    (span_homT_eq_top_of_basis p.val 4 hp bE ((bT.linearMap bT).reindex finProdFinEquiv))

end ZInQ.Manuscript.RC.HCMV21

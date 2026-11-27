import ZInQKernel.Contrib.OneProof.ColmezTorsionIso.Basic

/-!
# The shape of the row `colmez1992DeRhamAbVar`, transported along `V_p(A) ≅ V_p(A_{ℂ_p})`

`ColmezShape p F Q ρ` is the conclusion of the row `Colmez1992DeRhamAbVar` for a
`G_F`-representation `ρ` on a `ℚ_p`-space `V`, with the condition "values in `B_dR⁺`" abstracted
as a predicate `Q` on `B_dR` (the row takes `Q b = (b ∈ filB p 0)`). It is invariant under a
`G_F`-equivariant linear isomorphism (`colmezShape_transfer`). With `vCp`, the row's statement on
the `F̄`-points and the same statement on the `ℂ_p`-points are equivalent (`colmezShape_iff_cp`).
-/

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.ColmezTorsionIso

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

variable (p F) in
/-- The conclusion of the row `Colmez1992DeRhamAbVar` for a representation `ρ` (Colmez,
Théorème 5.2 (i)-(ii), in the row's Lean form), with `B_dR⁺` abstracted as `Q`. -/
def ColmezShape (Q : BdR p → Prop) {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) : Prop :=
  ∃ (H : Type) (P : H → (V →ₗ[ℚ_[p]] BdR p)),
    (∀ ω u, Q (P ω u)) ∧
    (∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (ρ σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
    (∀ x : BdR p ⊗[ℚ_[p]] V, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

theorem liftBaseChange_comp_apply {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [AddCommGroup W] [Module ℚ_[p] W] (f : V →ₗ[ℚ_[p]] BdR p) (g : W →ₗ[ℚ_[p]] V)
    (y : BdR p ⊗[ℚ_[p]] W) :
    (f ∘ₗ g).liftBaseChange (BdR p) y = f.liftBaseChange (BdR p) (g.baseChange (BdR p) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a w =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      LinearMap.comp_apply]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]

/-- **Transport** along a `G_F`-equivariant linear isomorphism `e : V ≃ W`. -/
theorem colmezShape_transfer (Q : BdR p → Prop) {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [AddCommGroup W] [Module ℚ_[p] W]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρ' : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) (e : V ≃ₗ[ℚ_[p]] W)
    (he : ∀ σ v, e (ρ σ v) = ρ' σ (e v)) :
    ColmezShape p F Q ρ → ColmezShape p F Q ρ' := by
  rintro ⟨H, P, h0, hgal, hnd⟩
  have he' : ∀ σ w, e.symm (ρ' σ w) = ρ σ (e.symm w) := by
    intro σ w
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  refine ⟨H, fun ω => P ω ∘ₗ e.symm.toLinearMap, fun ω u => h0 ω _, fun ω σ u => ?_,
    fun x hx => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he', hgal]
  · have hinj : Function.Injective (e.symm.toLinearMap.baseChange (BdR p)) := by
      intro a b hab
      have key : ∀ c, e.toLinearMap.baseChange (BdR p) (e.symm.toLinearMap.baseChange (BdR p) c)
          = c := by
        intro c
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
        have hid : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
          ext w
          simp
        rw [hid, LinearMap.baseChange_id, LinearMap.id_apply]
      rw [← key a, ← key b, hab]
    apply hinj
    rw [map_zero]
    apply hnd
    intro ω
    rw [← liftBaseChange_comp_apply]
    exact hx ω

/-- **The row's statement for `V_p(A)` (from `F̄`-points) is equivalent to the same statement
for `V_p` of the `ℂ_p`-points**, through `vCp`. -/
theorem colmezShape_iff_cp (Q : BdR p → Prop) (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    ColmezShape p F Q (A.galRep p) ↔ ColmezShape p F Q (galRepCp p A) :=
  ⟨colmezShape_transfer Q _ _ (vCp p A) (vCp_galRep A),
    colmezShape_transfer Q _ _ (vCp p A).symm (fun σ w => by
      apply (vCp p A).injective
      rw [LinearEquiv.apply_symm_apply, vCp_galRep, LinearEquiv.apply_symm_apply])⟩

end ZInQ.Contrib.ColmezTorsionIso

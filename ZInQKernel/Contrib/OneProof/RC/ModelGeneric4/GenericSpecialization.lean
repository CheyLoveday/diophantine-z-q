import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.LatticeQuotient
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.PairCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientInvariant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

/-! # The pinned pair at a parameter with transcendental j-value

The rational pair reading and the actual Vélu quotient invariant commute with every embedding of
algebraically closed fields. At a parameter τ whose j-value is transcendental, the complex point of
the pinned rational open at τ is the image of a geometric point over the generic j-line under an
embedding of the algebraic closure of `ℚ(j)` sending `j` to `j(τ)`. The descended Vélu invariant
then gives the quotient invariant `j(Nτ)` of the pinned pair, and the actual pair classes agree. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open LeafModCurves ModelGeneric ModelGeneric2 ModelTorsion RC.ModelInvariants UpperHalfPlane
open WeierstrassCurve.Affine
open ZInQ.Manuscript.RC

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

section Naturality

variable {K₁ K₂ : Type} [Field K₁] [Algebra ℚ K₁] [DecidableEq K₁] [IsAlgClosed K₁] [CharZero K₁]
  [Field K₂] [Algebra ℚ K₂] [DecidableEq K₂] [IsAlgClosed K₂] [CharZero K₂]

omit [IsAlgClosed K₂] [CharZero K₁] [CharZero K₂] in
/-- The actual Vélu quotient invariant of a specialized short curve with a marked cyclic subgroup
commutes with an embedding of the specialization fields. -/
private theorem shortQuotientJ_comp (c : ShortBase ℚ →ₐ[ℚ] K₁) (σ : K₁ →ₐ[ℚ] K₂) {x y : K₁}
    (h : ((shortFamily ℚ).map c.toRingHom).toAffine.Nonsingular x y)
    (h' : ((shortFamily ℚ).map (σ.comp c).toRingHom).toAffine.Nonsingular (σ x) (σ y)) (N : ℕ) :
    ((shortFamily ℚ).map (σ.comp c).toRingHom).cyclicQuotientJ
        (AddSubgroup.zmultiples (Point.some (σ x) (σ y) h')) N =
      σ (((shortFamily ℚ).map c.toRingHom).cyclicQuotientJ
        (AddSubgroup.zmultiples (Point.some x y h)) N) := by
  letI : Algebra (ShortBase ℚ) K₁ := c.toRingHom.toAlgebra
  letI : Algebra (ShortBase ℚ) K₂ := (σ.comp c).toRingHom.toAlgebra
  let σ' : K₁ →ₐ[ShortBase ℚ] K₂ := { toRingHom := σ.toRingHom, commutes' := fun _ => rfl }
  have key := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed (shortFamily ℚ) σ'
    (AddSubgroup.zmultiples (Point.some x y h :
      ((shortFamily ℚ).baseChange K₁).toAffine.Point)) N
  rw [AddMonoidHom.map_zmultiples, Point.map_some] at key
  exact key

/-- **Naturality of the pinned pair reading.** The quotient invariant of the rational pair reading
commutes with every embedding of algebraically closed fields of characteristic zero. -/
theorem pairQuotientJ_rationalPoints_comp {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (σ : K₁ →ₐ[ℚ] K₂)
    (y : Y0RationalAlgebra h₂ →ₐ[ℚ] K₁) :
    pairQuotientJ (rationalPoints h₂ (σ.comp y)) = σ (pairQuotientJ (rationalPoints h₂ y)) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let hn := rationalLevel_isUnit (N := n + 2)
  let gr := rationalGrading h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  have hδ : (↑(shortExactOrderDiscriminantUnit (R := ℚ) hn) : rationalCover (n + 2)) ∈
      gr 12 := shortExactOrderDiscriminantUnit_mem (R := ℚ) hn
  obtain ⟨f, rfl⟩ := degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ)
    (k := K₁) gr (by decide) hδ y
  change pairQuotientJ ((rationalPointReading h₂).val ((σ.comp f).comp (Y0RationalInclusion h₂))) =
    σ (pairQuotientJ ((rationalPointReading h₂).val (f.comp (Y0RationalInclusion h₂))))
  rw [(rationalPointReading h₂).property, (rationalPointReading h₂).property, pairQuotientJ_mk,
    pairQuotientJ_mk]
  obtain ⟨hf, hfP⟩ := shortExactOrderPoints_affine hn f
  obtain ⟨hg, hgP⟩ := shortExactOrderPoints_affine hn (σ.comp f)
  change ((shortFamily ℚ).map (shortExactOrderPoints hn (σ.comp f)).1.toRingHom).cyclicQuotientJ
      (AddSubgroup.zmultiples (shortExactOrderPoints hn (σ.comp f)).2.1) (n + 2) =
    σ (((shortFamily ℚ).map (shortExactOrderPoints hn f).1.toRingHom).cyclicQuotientJ
      (AddSubgroup.zmultiples (shortExactOrderPoints hn f).2.1) (n + 2))
  rw [hgP, hfP]
  exact shortQuotientJ_comp (shortExactOrderPoints hn f).1 σ hf hg (n + 2)

end Naturality

end WeierstrassCurve.ModelLevels.ModelGeneric4

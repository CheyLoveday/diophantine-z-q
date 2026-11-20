import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Projective
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Splitting

/-! A genuine spherical action of the integral group at a good prime,
by normalizing the projective representatives. This implements tex
8944–8946 on the rectangular lattice, on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Visibility
open scoped MatrixGroups

variable (p : Place)

def includeIntegral : SL(2, ℤ_[p.val]) →* SL(2, ℚ_[p.val]) :=
  Matrix.SpecialLinearGroup.map PadicInt.Coe.ringHom

private theorem include_upper (b : ℤ_[p.val]) :
    includeIntegral p (upperMatrix b) = upperMatrix (b : ℚ_[p.val]) := by
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.map PadicInt.Coe.ringHom (upperMatrix b)) :
    Matrix (Fin 2) (Fin 2) ℚ_[p.val]) = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix, RingHom.mapMatrix_apply]

private theorem include_diagonal (t : ℤ_[p.val]ˣ) :
    includeIntegral p (diagonalMatrix t) =
      diagonalMatrix (Units.map (PadicInt.Coe.ringHom (p := p.val)) t) := by
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.map PadicInt.Coe.ringHom (diagonalMatrix t)) :
    Matrix (Fin 2) (Fin 2) ℚ_[p.val]) = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, RingHom.mapMatrix_apply, ← map_inv]

private theorem include_weyl :
    includeIntegral p weylMatrix = weylMatrix := by
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.map PadicInt.Coe.ringHom (weylMatrix (A := ℤ_[p.val]))) :
    Matrix (Fin 2) (Fin 2) ℚ_[p.val]) = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMatrix, RingHom.mapMatrix_apply]

private def Representatives (ρ : SL(2, ℚ_[p.val]) →* ProjectiveOperators p) :
    Subgroup (SL(2, ℤ_[p.val]) × (LocalEnd p)ˣ) :=
  MonoidHom.eqLocus (ρ.comp ((includeIntegral p).comp (MonoidHom.fst _ _)))
    ((project p).comp (MonoidHom.snd _ _))

/-- At good primes the projective representatives normalized to fix
the spherical vector define an actual action of SL₂ of the integers. -/
theorem local_integral_action (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]
    (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a)) :
    ∃ R : SL(2, ℤ_[p.val]) →* (LocalEnd p)ˣ,
      (∀ b, R (upperMatrix b) = upperUnit p a (b : ℚ_[p.val])) ∧
      (∀ t, R (diagonalMatrix t) =
        diagonalUnit p a (Units.map (PadicInt.Coe.ringHom (p := p.val)) t)) ∧
      R weylMatrix = weylUnit p a ∧
      ∀ k, (R k : LocalEnd p) (spherical p) = spherical p := by
  obtain ⟨ρ, hρU, hρM, hρW⟩ := local_projective_representation p a
  let H := Representatives p ρ
  let π : H →* SL(2, ℤ_[p.val]) := (MonoidHom.fst _ _).comp H.subtype
  let V : H →* (LocalEnd p)ˣ := (MonoidHom.snd _ _).comp H.subtype
  let V' : H →* LocalEnd p :=
    { toFun := fun h => (V h : LocalEnd p)
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl }
  let u (b : ℤ_[p.val]) : H := ⟨(upperMatrix b, upperUnit p a (b : ℚ_[p.val])), by
    change ρ (includeIntegral p (upperMatrix b)) = _
    rw [include_upper, hρU]; rfl⟩
  let m (t : ℤ_[p.val]ˣ) : H := ⟨(diagonalMatrix t,
      diagonalUnit p a (Units.map (PadicInt.Coe.ringHom (p := p.val)) t)), by
    change ρ (includeIntegral p (diagonalMatrix t)) = _
    rw [include_diagonal, hρM]; rfl⟩
  let w : H := ⟨(weylMatrix, weylUnit p a), by
    change ρ (includeIntegral p weylMatrix) = _
    rw [include_weyl, hρW]; rfl⟩
  have hU (b : ℤ_[p.val]) : V' (u b) = upperUnipotent a p (b : ℚ_[p.val]) :=
    coe_upperUnit p a _
  have hM (t : ℤ_[p.val]ˣ) :
      V' (m t) = diagonal a p (Units.map (PadicInt.Coe.ringHom (p := p.val)) t) :=
    coe_diagonalUnit p a _
  have hW : V' w = Metaplectic.weyl a p := coe_weylUnit p a
  have hker (g : H) (hg : π g = 1) (hne : g ≠ 1) :
      ∃ z : ℂ, z ≠ 1 ∧ V' g = z • (1 : LocalEnd p) := by
    have hq := g.property
    change ρ (includeIntegral p g.1.1) = project p g.1.2 at hq
    change g.1.1 = 1 at hg
    rw [hg, map_one, map_one] at hq
    have hh : g.1.2 ∈ scalarSubgroup p := (QuotientGroup.eq_one_iff _).mp hq.symm
    obtain ⟨c, hc⟩ := hh
    have hcone : c ≠ 1 := by
      intro h
      subst c
      have he : g.1.2 = 1 := by simpa using hc.symm
      exact hne (Subtype.ext (Prod.ext hg he))
    refine ⟨(c : ℂ), fun he => hcone (Units.ext he), ?_⟩
    change (g.1.2 : LocalEnd p) = _
    rw [← hc, coe_scalarOp]
    exact Algebra.algebraMap_eq_smul_one _
  obtain ⟨s, _, hs, huniq⟩ :=
    integral_spherical_section p a hp₂ hp π V' u m w (fun _ => rfl) (fun _ => rfl) rfl hU hM hW hker
  have hu (b : ℤ_[p.val]) : u b = s (upperMatrix b) :=
    huniq _ _ rfl ((hU b).symm ▸ upper_spherical a p b.property)
  have hm (t : ℤ_[p.val]ˣ) : m t = s (diagonalMatrix t) := by
    apply huniq _ _ rfl
    rw [hM]
    apply diagonal_spherical a p hp₂ hp
    change ‖((t : ℤ_[p.val]) : ℚ_[p.val])‖ = 1
    rw [PadicInt.norm_coe, PadicInt.norm_units]
  have hw : w = s weylMatrix :=
    huniq _ _ rfl (hW.symm ▸ weyl_spherical a p hp₂ hp)
  refine ⟨V.comp s, fun b => ?_, fun t => ?_, ?_, hs⟩
  · change V (s (upperMatrix b)) = _
    rw [← hu]
    rfl
  · change V (s (diagonalMatrix t)) = _
    rw [← hm]
    rfl
  · change V (s weylMatrix) = _
    rw [← hw]
    rfl


end ZInQ.Manuscript.RC.Metaplectic2

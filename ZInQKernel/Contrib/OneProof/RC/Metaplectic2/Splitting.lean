import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Spherical
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Matrices

/-! Spherical splitting of a genuine cover above the integral subgroup,
tex 8884–8886 and 8944–8946. The stabilizer argument is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex
open scoped MatrixGroups

variable {G : Type*} [Group G] (p : Place)

def sphericalStabilizer (R : G →* Module.End ℂ (SchwartzBruhat p)) : Subgroup G where
  carrier := {g | R g (spherical p) = spherical p}
  one_mem' := by change R 1 (spherical p) = _; rw [map_one]; rfl
  mul_mem' {g h} hg hh := by
    change R g (spherical p) = _ at hg
    change R h (spherical p) = _ at hh
    change R (g * h) (spherical p) = _
    rw [map_mul]
    change R g (R h (spherical p)) = _
    rw [hh, hg]
  inv_mem' {g} hg := by
    change R g (spherical p) = _ at hg
    have h : R g⁻¹ (R g (spherical p)) = spherical p := by
      change (R g⁻¹ * R g) (spherical p) = _
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    change R g⁻¹ (spherical p) = spherical p
    simpa only [hg] using h

/-- Given local lifts of the three generators and a genuine kernel,
every integral matrix has a unique lift fixing the spherical vector.
The section is multiplicative because the fixes form a subgroup. -/
theorem integral_spherical_section (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]
    (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a))
    (π : G →* SL(2, ℤ_[p.val])) (R : G →* Module.End ℂ (SchwartzBruhat p))
    (u : ℤ_[p.val] → G) (m : ℤ_[p.val]ˣ → G) (w : G)
    (hu : ∀ b, π (u b) = upperMatrix b)
    (hm : ∀ t, π (m t) = diagonalMatrix t)
    (hw : π w = weylMatrix)
    (hU : ∀ b, R (u b) = upperUnipotent a p (b : ℚ_[p.val]))
    (hM : ∀ t, R (m t) = diagonal a p (Units.map (PadicInt.Coe.ringHom (p := p.val)) t))
    (hW : R w = Metaplectic.weyl a p)
    (hker : ∀ g : G, π g = 1 → g ≠ 1 → R g = -1) :
    ∃ s : SL(2, ℤ_[p.val]) →* G,
      (∀ k, π (s k) = k) ∧ (∀ k, R (s k) (spherical p) = spherical p) ∧
        ∀ k g, π g = k → R g (spherical p) = spherical p → g = s k := by
  let H := sphericalStabilizer p R
  let q : H →* SL(2, ℤ_[p.val]) := π.comp H.subtype
  have huu (b : ℤ_[p.val]) : u b ∈ H := by
    change R (u b) (spherical p) = _
    rw [hU]
    exact upper_spherical a p b.property
  have hmm (t : ℤ_[p.val]ˣ) : m t ∈ H := by
    change R (m t) (spherical p) = _
    rw [hM]
    apply diagonal_spherical a p hp₂ hp
    change ‖((t : ℤ_[p.val]) : ℚ_[p.val])‖ = 1
    rw [PadicInt.norm_coe, PadicInt.norm_units]
  have hww : w ∈ H := by
    change R w (spherical p) = _
    rw [hW]
    exact weyl_spherical a p hp₂ hp
  have hsurj : Function.Surjective q := by
    intro k
    have hk := integral_generators (H.map π) (fun b => ⟨u b, huu b, hu b⟩)
      (fun t => ⟨m t, hmm t, hm t⟩) ⟨w, hww, hw⟩ k
    obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hk
    exact ⟨⟨g, hg⟩, he⟩
  have hinj : Function.Injective q := (injective_iff_map_eq_one q).2 fun g hg => by
    apply Subtype.ext
    change (g : G) = 1
    by_contra hn
    have hh : R (g : G) (spherical p) = spherical p := g.property
    have hg' : π (g : G) = 1 := hg
    rw [hker _ hg' hn] at hh
    have he := congrArg (fun f : SchwartzBruhat p => f.1 0) hh
    have hz : (0 : LocalVectors p) ∈ localLattice p := by simp [localLattice]
    change -(spherical p).1 0 = (spherical p).1 0 at he
    rw [spherical_apply, ite_eq_left hz] at he
    norm_num at he
  let e : H ≃* SL(2, ℤ_[p.val]) := MulEquiv.ofBijective q ⟨hinj, hsurj⟩
  let s := H.subtype.comp e.symm.toMonoidHom
  refine ⟨s, e.apply_symm_apply, fun k => (e.symm k).property, ?_⟩
  intro k g hg hf
  have h := hinj (show q (⟨g, hf⟩ : H) = q (e.symm k) from hg.trans (e.apply_symm_apply k).symm)
  exact congrArg Subtype.val h

#print axioms integral_spherical_section

end ZInQ.Manuscript.RC.Metaplectic2

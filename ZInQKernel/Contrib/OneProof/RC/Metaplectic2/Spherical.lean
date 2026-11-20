import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Relations

/-! The standard lattice at a good prime, tex 8938–8946.
This is the rectangular form calculation, on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex GaussSign Set
open scoped BigOperators

variable (a : Fin 3 → ℕ) (p : Place)

/-- The reference factor in the finite restricted tensor product. -/
def spherical : SchwartzBruhat p := elementaryCoset p 0

open Classical in
theorem spherical_apply (x : LocalVectors p) :
    (spherical p).1 x = if x ∈ localLattice p then 1 else 0 := by
  classical
  simp [spherical, elementaryCoset, localCoset, Set.indicator_apply]

theorem spherical_ne_zero : spherical p ≠ 0 := by
  intro h
  have hh := congrArg (fun f : SchwartzBruhat p => f.1 0) h
  have hz : (0 : LocalVectors p) ∈ localLattice p := by simp [localLattice]
  simp [spherical_apply, hz] at hh

private theorem mem_lattice (x : LocalVectors p) :
    x ∈ localLattice p ↔ ∀ i, x i ∈ PadicInt.subring p.val := by
  simp [localLattice]

theorem upper_spherical {b : ℚ_[p.val]} (hb : b ∈ PadicInt.subring p.val) :
    upperUnipotent a p b (spherical p) = spherical p := by
  apply Subtype.ext
  funext x
  change localPhase p (b * quad a x) * (spherical p).1 x = (spherical p).1 x
  classical
  rw [spherical_apply]
  split_ifs with hx
  · have hq : quad a x ∈ PadicInt.subring p.val := by
      apply (PadicInt.subring p.val).sum_mem
      intro i _
      exact (PadicInt.subring p.val).mul_mem (natCast_mem _ _) <|
        (PadicInt.subring p.val).pow_mem ((mem_lattice p x).1 hx i) 2
    rw [(localPhase_eq_one p _).2 ((PadicInt.subring p.val).mul_mem hb hq), one_mul]
  · rw [mul_zero]

variable [∀ i, NeZero (2 * a i)]

private theorem determinant_ne_zero : determinant a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (2 * a i))

private theorem not_dvd_determinant (hp : p ∉ badPlaces (determinant a)) :
    ¬ p.val ∣ determinant a := by
  intro h
  have hmem := Nat.mem_primeFactors.mpr ⟨p.property, h, determinant_ne_zero a⟩
  exact hp (Finset.mem_map.mpr ⟨⟨p.val, hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)

private theorem gram_norm_one (hp : p ∉ badPlaces (determinant a)) (i : Fin 3) :
    ‖((2 * a i : ℕ) : ℚ_[p.val])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply p.property.coprime_iff_not_dvd.mpr
  intro h
  exact not_dvd_determinant a p hp (h.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

private theorem coefficient_norm_one (hp : p ∉ badPlaces (determinant a)) (i : Fin 3) :
    ‖(localCoefficient a p i : ℚ_[p.val])‖ = 1 := by
  rw [localCoefficient_val]
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply p.property.coprime_iff_not_dvd.mpr
  intro h
  exact not_dvd_determinant a p hp ((h.trans (dvd_mul_left _ _)).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

private theorem val_zero_of_norm_one (t : ℚ_[p.val]ˣ)
    (ht : ‖(t : ℚ_[p.val])‖ = 1) : valAt p t = 0 := by
  change (t : ℚ_[p.val]).valuation = 0
  have hn : 0 ≤ (t : ℚ_[p.val]).valuation :=
    (Padic.norm_le_one_iff_val_nonneg _).mp ht.le
  have hi : 0 ≤ ((t : ℚ_[p.val])⁻¹).valuation := by
    apply (Padic.norm_le_one_iff_val_nonneg _).mp
    rw [norm_inv, ht, inv_one]
  rw [Padic.valuation_inv] at hi
  omega

theorem self_dual_lattice (hp : p ∉ badPlaces (determinant a)) (x : LocalVectors p) :
    localDual a p x ↔ x ∈ localLattice p := by
  rw [mem_lattice]
  unfold localDual
  simp only [PadicInt.mem_subring_iff, norm_mul, gram_norm_one a p hp, one_mul]

theorem scaledIndex_spherical (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a))
    (t : ℚ_[p.val]ˣ) (ht : ‖(t : ℚ_[p.val])‖ = 1) : scaledIndex a p t = 1 := by
  unfold scaledIndex
  apply Finset.prod_eq_one
  intro i _
  rw [gaussGamma_eq_finiteGamma]
  apply finiteGamma_even_odd_place p hp₂
  rw [valAt_mul, val_zero_of_norm_one p t ht,
    val_zero_of_norm_one p _ (coefficient_norm_one a p hp i)]
  decide

theorem index_spherical (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a)) :
    gaussIndex a p = 1 := by
  rw [← scaledIndex_one]
  exact scaledIndex_spherical a p hp₂ hp 1 (by simp)

theorem fourier_spherical (hp : p ∉ badPlaces (determinant a)) :
    fourier a p (spherical p) = spherical p := by
  classical
  apply Subtype.ext
  funext y
  rw [show (fourier a p (spherical p)).1 y = localFourier a p (localCoset p 0) y from rfl,
    localFourier_coset, self_dual_lattice a p hp, spherical_apply,
    localNorm_good (determinant_ne_zero a) hp, Real.sqrt_one]
  have hz : polar a (0 : LocalVectors p) y = 0 := by simp [polar]
  simp [hz, (localPhase_eq_one p 0).2 (zero_mem (PadicInt.subring p.val))]

theorem weyl_spherical (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a)) :
    Metaplectic.weyl a p (spherical p) = spherical p := by
  rw [Metaplectic.weyl, index_spherical a p hp₂ hp, Units.val_one, one_smul, fourier_spherical a p hp]

theorem diagonal_spherical (hp₂ : p ≠ dyadicPlace) (hp : p ∉ badPlaces (determinant a))
    (t : ℚ_[p.val]ˣ) (ht : ‖(t : ℚ_[p.val])‖ = 1) :
    diagonal a p t (spherical p) = spherical p := by
  classical
  have hm (x : LocalVectors p) : (t : ℚ_[p.val]) • x ∈ localLattice p ↔ x ∈ localLattice p := by
    simp only [mem_lattice, Pi.smul_apply, smul_eq_mul, PadicInt.mem_subring_iff, norm_mul, ht, one_mul]
  unfold diagonal diagonalRatio
  rw [scaledIndex_spherical a p hp₂ hp t ht, index_spherical a p hp₂ hp, div_one,
    Units.val_one, one_smul]
  apply Subtype.ext
  funext x
  rw [dilation_apply, spherical_apply, spherical_apply, hm]
  simp [dilationFactor, ht]

#print axioms spherical_apply
#print axioms spherical_ne_zero
#print axioms mem_lattice
#print axioms upper_spherical
#print axioms determinant_ne_zero
#print axioms not_dvd_determinant
#print axioms gram_norm_one
#print axioms coefficient_norm_one
#print axioms val_zero_of_norm_one
#print axioms self_dual_lattice
#print axioms scaledIndex_spherical
#print axioms index_spherical
#print axioms fourier_spherical
#print axioms weyl_spherical
#print axioms diagonal_spherical

end ZInQ.Manuscript.RC.Metaplectic2

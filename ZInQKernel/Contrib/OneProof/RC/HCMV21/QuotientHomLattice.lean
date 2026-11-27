import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeToGeometry

/-! For a finite étale quotient of the reference, the covariant Hom
lattice pulled back by the isogeny has an integral description. At
primes away from the degree the same quotient identifies the
completed enhanced Hom lattice with the reference order. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry
open PkgI3.AbVar ZInQ.DefFaltings ZInQ.Contrib.MilneQuasiInverse
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A B : PkgI3.AbVar k}

/-- A reverse isogeny identifies each covariant Hom with an actual
endomorphism of the source after clearing the degree. -/
noncomputable def postcomposeToEnd (v : Hom B A) : Hom A B →+ A.End where
  toFun f := Hom.mk' (f.hom ≫ v.hom)
  map_zero' := Hom.ext' (by rw [Hom.hom_mk', Hom.hom_zero, MonObj.one_comp, Hom.hom_zero])
  map_add' f g := Hom.ext' (by simp only [Hom.hom_mk', Hom.hom_add, MonObj.mul_comp])

private theorem postcomposeToEnd_mem_level
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (C : Subgroup (A.Pt k)) (f : Hom A B)
    (hf : f ∈ levelHom C (C.map (ptMap u))) : postcomposeToEnd v f ∈ levelEnd A C := by
  intro P hP
  obtain ⟨Q, hQ, h⟩ := hf P hP
  change P ≫ (f.hom ≫ v.hom) ∈ C
  rw [← Category.assoc, ← h, show ptMap u Q = Q ≫ u.hom from rfl, Category.assoc, hu,
    AvSplit.comp_natCast_hom']
  exact C.pow_mem hQ m

/-- At a prime where the kernel exponent of a level-transporting
quotient is a unit, pulling back the enhanced Hom lattice gives
the completed source level order. The chosen quasi-inverse is
`v/m`, so the unscaled image used here has the same local span. -/
theorem span_quotient_levelHom_eq_source_order {S M : Type*}
    [CommRing S] [AddCommGroup M] [Module S M]
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : IsUnit (m : S))
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (C : Subgroup (A.Pt k)) (φ : A.End →+ M) :
    Submodule.span S ((φ.comp (postcomposeToEnd v)) ''
        (levelHom C (C.map (ptMap u)) : Set (Hom A B))) =
      Submodule.span S (φ '' (levelEnd A C : Set A.End)) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, postcomposeToEnd_mem_level u v m hu C f hf, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    let g : Hom A B := Hom.mk' (f.hom ≫ u.hom)
    have hg : g ∈ levelHom C (C.map (ptMap u)) := by
      intro P hP
      refine ⟨P ≫ f.hom, hf P hP, ?_⟩
      change (P ≫ f.hom) ≫ u.hom = P ≫ (f.hom ≫ u.hom)
      rw [Category.assoc]
    have hvg : postcomposeToEnd v g = m • f := by
      apply Hom.ext'
      change (f.hom ≫ u.hom) ≫ v.hom = f.hom ^ m
      rw [Category.assoc, hu, AvSplit.comp_natCast_hom']
    let L := Submodule.span S ((φ.comp (postcomposeToEnd v)) ''
      (levelHom C (C.map (ptMap u)) : Set (Hom A B)))
    have h : φ (m • f) ∈ L := hvg ▸ Submodule.subset_span ⟨_, hg, rfl⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul S] at h
    have he : (↑hm.unit⁻¹ : S) * (m : S) = 1 := by
      exact (congrArg ((↑hm.unit⁻¹ : S) * ·) hm.unit_spec.symm).trans (Units.inv_mul hm.unit)
    change φ f ∈ L
    simpa only [smul_smul, he, one_smul] using L.smul_mem (↑hm.unit⁻¹ : S) h

/-- Before dividing by `m`, a covariant enhanced Hom lattice in
reverse-isogeny coordinates is cut out inside the reference level order
by one condition on the geometric `m`-torsion. This is the actual
individual kernel of the quotient, so the criterion distinguishes
different labelled quotients of the same degree. -/
theorem mem_postcomposeToEnd_levelHom_image_iff
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m) (a : A.End) :
    a ∈ postcomposeToEnd v '' (levelHom C (C.map (ptMap u)) : Set (Hom A B)) ↔
      a ∈ levelEnd A C ∧
        ∀ P : A.Pt (AlgebraicClosure k), P ^ m = 1 → (P ≫ a.hom) ≫ u.hom = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨postcomposeToEnd_mem_level u v m hu C g hg, ?_⟩
    intro P hP
    change (P ≫ (g.hom ≫ v.hom)) ≫ u.hom = 1
    rw [← Category.assoc P, Category.assoc, hv, AvSplit.comp_natCast_hom',
      ← MonObj.pow_comp, hP, MonObj.one_comp]
  · rintro ⟨ha, hker⟩
    let mult : Hom A A := ((m : ℤ) : A.End)
    obtain ⟨hf, he, hs⟩ := finiteEtale_mul_of_ne_zero A m hm
    let : IsFinite mult.hom.left := hf
    let : Etale mult.hom.left := he
    let : Surjective mult.hom.left := hs
    have : EffectiveEpi mult.hom :=
      Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc mult.hom
    have ⟨g, hg, _⟩ := existsUnique_factor_of_etale_kernel mult
      (Hom.mk' (a.hom ≫ u.hom)) (fun P hP => by
        change P ≫ ((m : ℤ) : A.End).hom = 1 at hP
        rw [AvSplit.comp_natCast_hom'] at hP
        change P ≫ (a.hom ≫ u.hom) = 1
        rw [← Category.assoc]
        exact hker P hP)
    have hg' : mult.hom ≫ g.hom = a.hom ≫ u.hom := hg
    refine ⟨g, ?_, Hom.ext' ?_⟩
    · intro P hP
      obtain ⟨Q, hQ⟩ := (powCoprime hC).surjective ⟨P, hP⟩
      have hQ' : (Q : A.Pt k) ^ m = P := congrArg Subtype.val hQ
      refine ⟨(Q : A.Pt k) ≫ a.hom, ha _ Q.prop, ?_⟩
      change ((Q : A.Pt k) ≫ a.hom) ≫ u.hom = P ≫ g.hom
      rw [Category.assoc, ← hg', ← Category.assoc, ← hQ']
      rw [show (Q : A.Pt k) ≫ mult.hom = (Q : A.Pt k) ^ m from
        AvSplit.comp_natCast_hom' A _ m]
    · change g.hom ≫ v.hom = a.hom
      apply (cancel_epi mult.hom).mp
      rw [← Category.assoc, hg', Category.assoc, hu, AvSplit.comp_natCast_hom']
      have hmul : mult.hom = (𝟙 A.X : A.X ⟶ A.X) ^ m := by
        simpa only [Category.id_comp] using AvSplit.comp_natCast_hom' A (𝟙 A.X) m
      rw [hmul, MonObj.pow_comp, Category.id_comp]

end ZInQ.Manuscript.RC.HCMV21

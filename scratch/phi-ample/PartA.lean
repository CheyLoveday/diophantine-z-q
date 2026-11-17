import ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Endomorphism

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory

namespace PhiAmple

open Scheme.Modules

section ZeroLocus

variable {X : Scheme.{0}}

/-- `D(ψ ≫ φ) ⊇ D(ψ) ∩ D(φ)`. -/
theorem notMem_support_comp {L M N : X.Modules} [L.IsInvertible] [M.IsInvertible] [N.IsInvertible]
    (ψ : L ⟶ M) (φ : M ⟶ N) {x : X} (h1 : x ∉ (Hom.zeroLocus ψ).support)
    (h2 : x ∉ (Hom.zeroLocus φ).support) : x ∉ (Hom.zeroLocus (ψ ≫ φ)).support := by
  obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
    exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
  obtain ⟨V, hxV, hVU, eL, hL⟩ := exists_isFreeGenerator L hxU
  obtain ⟨b, hb⟩ := (hM.map hVU).exists_smul_eq (ψ.app V.1 eL)
  obtain ⟨c, hc⟩ := (hN.map hVU).exists_smul_eq
    (φ.app V.1 (M.presheaf.map (homOfLE hVU).op eM))
  have i1 := Hom.ideal_zeroLocus ψ V hL (hM.map hVU) hb.symm
  have i2 := Hom.ideal_zeroLocus φ V (hM.map hVU) (hN.map hVU) hc.symm
  have i3 := Hom.ideal_zeroLocus (ψ ≫ φ) V hL (hN.map hVU) (b := b * c) (by
    change φ.app V.1 (ψ.app V.1 eL) = _
    rw [← hb, Hom.app_smul, ← hc, mul_smul])
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i1, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton] at h1
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i2, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton] at h2
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i3, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Scheme.basicOpen_mul]
  simp only [Set.mem_compl_iff, not_not] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- An isomorphism vanishes nowhere. -/
theorem notMem_support_iso {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (e : M ≅ N) (x : X) :
    x ∉ (Hom.zeroLocus e.hom).support := by
  have h : Hom.zeroLocus e.hom = Hom.zeroLocus (𝟙 M) :=
    Hom.zeroLocus_eq_of_arrowIso _ _ (Arrow.isoMk (Iso.refl M) e.symm (by simp))
  rw [h]
  obtain ⟨U, hxU, -, eM, hM⟩ := exists_isFreeGenerator M (TopologicalSpace.Opens.mem_top x)
  have i1 := Hom.ideal_zeroLocus (𝟙 M) U hM hM (b := 1) (by simp)
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, i1, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Scheme.basicOpen_of_isUnit _ isUnit_one]
  simpa using hxU

/-- The zero scheme of `Q ◁ φ` is that of `φ`. -/
theorem zeroLocus_whiskerLeft {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (Q : X.Modules)
    [Q.IsInvertible] (φ : M ⟶ N) : Hom.zeroLocus (Q ◁ φ) = Hom.zeroLocus φ := by
  rw [← Hom.zeroLocus_whiskerRight φ Q]
  exact Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (β_ Q M) (β_ Q N) (BraidedCategory.braiding_naturality_right Q φ).symm)

/-- On a scheme whose global functions form a field, an endomorphism of `𝒪` that is nonzero at one point
vanishes nowhere. -/
theorem notMem_support_of_isField (hF : IsField Γ(X, ⊤)) (f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) {x : X}
    (hx : x ∉ (Hom.zeroLocus f).support) (y : X) : y ∉ (Hom.zeroLocus f).support := by
  obtain ⟨g, rfl⟩ := exists_eq_smulHom (𝟙_ X.Modules) f
  by_cases hg : g = 0
  · subst hg
    exfalso
    apply hx
    rw [smulHom_zero, (Hom.zeroLocus_eq_bot_iff 0).2 rfl, Scheme.IdealSheafData.support_bot]
    trivial
  · obtain ⟨g', hg'⟩ := hF.mul_inv_cancel hg
    let e : 𝟙_ X.Modules ≅ 𝟙_ X.Modules :=
      ⟨smulHom _ g, smulHom _ g', by rw [← smulHom_mul, mul_comm, hg', smulHom_one],
        by rw [← smulHom_mul, hg', smulHom_one]⟩
    exact notMem_support_iso e y

end ZeroLocus

end PhiAmple

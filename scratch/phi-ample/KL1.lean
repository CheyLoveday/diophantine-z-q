import ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Endomorphism

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

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

section Affine

variable {X : Scheme.{0}}

/-- Composing with an isomorphism does not change the zero scheme (any source). -/
theorem zeroLocus_comp_iso' {L M N : X.Modules} [L.IsInvertible] [M.IsInvertible] [N.IsInvertible]
    (s : L ⟶ M) (e : M ≅ N) : Hom.zeroLocus (s ≫ e.hom) = Hom.zeroLocus s :=
  (Hom.zeroLocus_eq_of_arrowIso s (s ≫ e.hom) (Arrow.isoMk (Iso.refl _) e (by simp))).symm

/-- **A scheme whose global functions form a field and which carries two ample classes with trivial
product is affine.** For `x`, sections `s` of `c^n` and `t` of `d^m` nonvanishing at `x`, with `D(s)` affine,
give the global function `u = s^{⊗m} ⊗ t^{⊗n}` (a section of `(cd)^{nm} = 𝒪`) nonvanishing at `x`, hence a unit;
so `D(s) ⊇ D(u) = X`. -/
theorem isAffine_of_ample_mul_eq_one [Nonempty X] (hF : IsField Γ(X, ⊤)) (c d : X.Pic)
    (hc : T09Pic.IsAmple X c) (hd : T09Pic.IsAmple X d) (hcd : c * d = 1) : IsAffine X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, s, hxs, haff⟩ := hc.2 x
  obtain ⟨m, hm, t, hxt, -⟩ := hd.2 x
  let Mc := (fromSkeleton X.Modules).obj c.val
  let Md := (fromSkeleton X.Modules).obj d.val
  let P := (Mc.tensorPow n).tensorPow m
  let Q := (Md.tensorPow m).tensorPow n
  let S : 𝟙_ X.Modules ⟶ P := Scheme.Modules.tensorPowSection s m
  let T : 𝟙_ X.Modules ⟶ Q := Scheme.Modules.tensorPowSection t n
  have hPQ : Scheme.Pic.mk (P ⊗ Q) = Scheme.Pic.mk (𝟙_ X.Modules) := by
    rw [Scheme.Pic.mk_tensorObj, PicFix.mk_tensorPow, PicFix.mk_tensorPow, PicFix.mk_tensorPow,
      PicFix.mk_tensorPow, Scheme.Pic.mk_fromSkeleton, Scheme.Pic.mk_fromSkeleton, ← pow_mul, ← pow_mul,
      mul_comm m n, ← mul_pow, hcd, one_pow]
    exact Scheme.Pic.one_eq_mk_unit
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).1 hPQ
  let u : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
    ((λ_ (𝟙_ X.Modules)).inv ≫ (𝟙_ X.Modules ◁ T)) ≫ ((S ▷ Q) ≫ e.hom)
  have hS : (Hom.zeroLocus ((S ▷ Q) ≫ e.hom)).support = (Hom.zeroLocus s).support := by
    rw [zeroLocus_comp_iso', Hom.zeroLocus_whiskerRight, PicFix.support_tensorPowSection _ hm]
  have hxs' : x ∉ (Hom.zeroLocus s).support := hxs
  have hxt' : x ∉ (Hom.zeroLocus t).support := hxt
  have hxu : x ∉ (Hom.zeroLocus u).support := by
    apply notMem_support_comp
    · apply notMem_support_comp
      · exact notMem_support_iso (λ_ (𝟙_ X.Modules)).symm x
      · rw [zeroLocus_whiskerLeft, PicFix.support_tensorPowSection _ hn]; exact hxt'
    · rw [hS]; exact hxs'
  have hsupp : (Hom.zeroLocus s).support = ⊥ := by
    rw [← hS]
    refine le_antisymm ?_ bot_le
    refine (Scheme.IdealSheafData.support_antitone (Hom.zeroLocus_comp_le
      ((λ_ (𝟙_ X.Modules)).inv ≫ (𝟙_ X.Modules ◁ T)) ((S ▷ Q) ≫ e.hom))).trans ?_
    intro y hy
    exact absurd hy (notMem_support_of_isField hF u hxu y)
  rw [hsupp] at haff
  have htop : (⊥ : TopologicalSpace.Closeds X).compl = ⊤ := by
    ext y; simp [TopologicalSpace.Closeds.compl]
  rw [htop] at haff
  have : IsAffine (⊤ : X.Opens).toScheme := haff
  exact IsAffine.of_isIso X.topIso.inv

/-- An affine scheme whose global functions form a field has one point. -/
theorem subsingleton_of_isAffine_of_isField [IsAffine X] (hF : IsField Γ(X, ⊤)) : Subsingleton X := by
  let _ := hF.toField
  have : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := inferInstance
  refine ⟨fun a b => ?_⟩
  have h : X.isoSpec.hom a = X.isoSpec.hom b := Subsingleton.elim (α := PrimeSpectrum Γ(X, ⊤)) _ _
  simpa using congrArg X.isoSpec.inv h

end Affine

end PhiAmple

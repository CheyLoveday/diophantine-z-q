import ZInQKernel.Contrib.OneProof.DelignePrintShapedMilne.Prints
import ZInQKernel.Contrib.OneProof.GAGAMorphism

/-! # The row `deligneCanonicalModelY3EveryPrint` from Milne's existence argument: bridges and assembly

Proved here (standard axioms, no GLUE):

* `compare_iso_P`: two witnesses of the printed fine-moduli clause list `Y3Fix.R1fpPropsAbP` are isomorphic over `ℚ`,
  compatibly with their moduli bijections (the argument of `Y3Fix.compare_iso_np`, for the printed level structure).
* `mk_eq_of_isBaseChangeOf`: two base changes of one object along one field map are isomorphic (both are isomorphic to
  the base change of the abelian variety, `RayClassCFT.bcIso`, by isomorphisms that are homomorphisms by rigidity and
  carry the `𝒪`-actions and level points to each other).
* `holFamily_of_prints` (holomorphy): from M1 and T2c″, the moduli map `Ψ` of every witness is holomorphic in
  `τ ∈ ℍ`: the classifying map `F : T → S` of M1's family composed with M1's holomorphic `ψ` is `S`'s moduli map, and
  the witness's moduli map is that, followed by the isomorphism `S ≅ Y` of `compare_iso_P`.
* `agree_of_witness`: on every witness, the moduli map satisfies M2's hypothesis on the action of `Aut(ℂ)` (the
  naturality clause of `Y3Fix.R1fpPropsAbP` with `mk_eq_of_isBaseChangeOf`).
* `deligneCanonicalModelY3EveryPrint_of_milne`: T2a, T2c′, T2c″, M1 and M2 give
  `Y3Hodge.DeligneCanonicalModelY3EveryPrint` (with the proved `ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof`).
-/

set_option autoImplicit false

noncomputable section

namespace DelignePSMilne

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraCFT RayClassCFT
open Y3Hodge (HPM DCRelPM toPM)
open DelignePS

/-! ## 1. Two witnesses are isomorphic -/

/-- A witness `(Y, Φ)` receives a morphism from any other witness `(Y', Φ')`, compatible with the moduli bijections
(the universal property of `Y` applied to the universal object of `Y'`). -/
theorem phi_part_P {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : Y3Fix.R1univAbPropsP Y Φ) (h1' : Y3Fix.R1fpPropsAbP Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

/-- **Two witnesses of `Y3Fix.R1fpPropsAbP` are isomorphic over `ℚ`, compatibly with the moduli bijections.** -/
theorem compare_iso_P {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : Y3Fix.R1fpPropsAbP Y Φ) (h' : Y3Fix.R1fpPropsAbP Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := phi_part_P h.2.2.2.2 h'
  obtain ⟨g', hg'⟩ := phi_part_P h'.2.2.2.2 h
  have e1 : g' ≫ g = 𝟙 Y := HDec.QMSplit.Moduli.eq_id_of_fieldPts h.1 h.2.1 _ fun K _ _ y =>
    (Φ K).injective (by rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y])
  have e2 : g ≫ g' = 𝟙 Y' := HDec.QMSplit.Moduli.eq_id_of_fieldPts h'.1 h'.2.1 _ fun K _ _ y =>
    (Φ' K).injective (by rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y])
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

/-! ## 2. Base change is unique up to isomorphism -/

/-- **Two base changes of one object along one field map are isomorphic.** Both are isomorphic over `L` to the base
change of `P.A` (`RayClassCFT.bcIso`); these isomorphisms preserve the identity (the level clause at `a = 0`), hence are
homomorphisms (the kernel's rigidity, through `RayClassCFT.bcIso_isMonHom`), and they carry the `𝒪`-actions
(`RayClassCFT.bc_iota`) and the level points (both project to those of `P`) to each other. -/
theorem mk_eq_of_isBaseChangeOf {K L : Type} [Field K] [Field L] {f : K →+* L} {P : QML3 K}
    {Q Q' : QML3 L} (h : IsBaseChangeOf f P Q) (h' : IsBaseChangeOf f P Q') :
    M3.mk Q = M3.mk Q' := by
  let _ : Algebra K L := f.toAlgebra
  obtain ⟨g, hpb, hι, hη⟩ := h
  obtain ⟨g', hpb', hι', hη'⟩ := h'
  have hpb₁ : IsPullback g Q.A.X.hom P.A.X.hom (RayClassCFT.fS K L) := hpb
  have hpb₁' : IsPullback g' Q'.A.X.hom P.A.X.hom (RayClassCFT.fS K L) := hpb'
  have hη₀ := RayClassCFT.eta_compat (P := P) (Q := Q) (g := g) hη
  have hη₀' := RayClassCFT.eta_compat (P := P) (Q := Q') (g := g') hη'
  have := RayClassCFT.bcIso_isMonHom hpb₁ hη₀
  have := RayClassCFT.bcIso_inv_isMonHom hpb₁ hη₀
  have := RayClassCFT.bcIso_isMonHom hpb₁' hη₀'
  have := RayClassCFT.bcIso_inv_isMonHom hpb₁' hη₀'
  refine Quotient.sound (Nonempty.intro
    ⟨PkgI3.AbVar.Hom.mk' ((RayClassCFT.bcIso hpb₁).hom ≫ (RayClassCFT.bcIso hpb₁').inv),
      PkgI3.AbVar.Hom.mk' ((RayClassCFT.bcIso hpb₁').hom ≫ (RayClassCFT.bcIso hpb₁).inv),
      ?_, ?_, ?_, ?_⟩)
  · show ((RayClassCFT.bcIso hpb₁).hom ≫ (RayClassCFT.bcIso hpb₁').inv) ≫
      ((RayClassCFT.bcIso hpb₁').hom ≫ (RayClassCFT.bcIso hpb₁).inv) = 𝟙 _
    simp
  · show ((RayClassCFT.bcIso hpb₁').hom ≫ (RayClassCFT.bcIso hpb₁).inv) ≫
      ((RayClassCFT.bcIso hpb₁).hom ≫ (RayClassCFT.bcIso hpb₁').inv) = 𝟙 _
    simp
  · intro a
    have h1 := RayClassCFT.bc_iota hpb₁ hι a
    have h2 := RayClassCFT.bc_iota hpb₁' hι' a
    have h2' : (HDec.G0ModField.KernelField.endBC P.A L (P.q.iota a)).hom ≫ (RayClassCFT.bcIso hpb₁').inv =
        (RayClassCFT.bcIso hpb₁').inv ≫ (Q'.q.iota a).hom := by
      rw [Iso.comp_inv_eq, Category.assoc, ← h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    show (Q.q.iota a).hom ≫ (RayClassCFT.bcIso hpb₁).hom ≫ (RayClassCFT.bcIso hpb₁').inv =
      ((RayClassCFT.bcIso hpb₁).hom ≫ (RayClassCFT.bcIso hpb₁').inv) ≫ (Q'.q.iota a).hom
    rw [← Category.assoc, ← h1, Category.assoc, h2', ← Category.assoc]
  · intro a
    have key : Additive.toMul (Q.e.eta a) ≫ (RayClassCFT.bcIso hpb₁).hom =
        Additive.toMul (Q'.e.eta a) ≫ (RayClassCFT.bcIso hpb₁').hom := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Over.comp_left]
      apply pullback.hom_ext
      · calc ((Additive.toMul (Q.e.eta a)).left ≫ (RayClassCFT.bcIso hpb₁).hom.left) ≫
              pullback.fst P.A.X.hom (RayClassCFT.fS K L)
            = (Additive.toMul (Q.e.eta a)).left ≫
                ((RayClassCFT.bcIso hpb₁).hom.left ≫ pullback.fst P.A.X.hom (RayClassCFT.fS K L)) :=
              Category.assoc _ _ _
          _ = (Additive.toMul (Q.e.eta a)).left ≫ g := by rw [RayClassCFT.bcIso_fst]
          _ = (Additive.toMul (Q'.e.eta a)).left ≫ g' := (hη a).trans (hη' a).symm
          _ = (Additive.toMul (Q'.e.eta a)).left ≫
                ((RayClassCFT.bcIso hpb₁').hom.left ≫ pullback.fst P.A.X.hom (RayClassCFT.fS K L)) := by
              rw [RayClassCFT.bcIso_fst]
          _ = _ := (Category.assoc _ _ _).symm
      · calc ((Additive.toMul (Q.e.eta a)).left ≫ (RayClassCFT.bcIso hpb₁).hom.left) ≫
              pullback.snd P.A.X.hom (RayClassCFT.fS K L)
            = (Additive.toMul (Q.e.eta a)).left ≫
                ((RayClassCFT.bcIso hpb₁).hom.left ≫ pullback.snd P.A.X.hom (RayClassCFT.fS K L)) :=
              Category.assoc _ _ _
          _ = (Additive.toMul (Q.e.eta a)).left ≫ Q.A.X.hom := by rw [RayClassCFT.bcIso_snd]
          _ = (Additive.toMul (Q'.e.eta a)).left ≫ Q'.A.X.hom := (Over.w _).trans (Over.w _).symm
          _ = (Additive.toMul (Q'.e.eta a)).left ≫
                ((RayClassCFT.bcIso hpb₁').hom.left ≫ pullback.snd P.A.X.hom (RayClassCFT.fS K L)) := by
              rw [RayClassCFT.bcIso_snd]
          _ = _ := (Category.assoc _ _ _).symm
    show Additive.ofMul (Additive.toMul (Q.e.eta a) ≫ (RayClassCFT.bcIso hpb₁).hom ≫
      (RayClassCFT.bcIso hpb₁').inv) = Q'.e.eta a
    rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id, ofMul_toMul]

/-! ## 3. Holomorphy of the moduli map (M1 and T2c″) -/

/-- **The moduli map of every witness is holomorphic.** Let `F : T → S` classify M1's family (T2c″). For every
`(z, g)`, `F ∘ ψ_T(z, g)` is a `ℂ`-point of `S` whose class is that of the fibre of M1's family at `ψ_T(z, g)`, a moduli
object of `[z, g]`; with the isomorphism `k : S ≅ Y` of `compare_iso_P`, `F ∘ ψ_T(z, g) ≫ k` and `Ψ(z, g)` have the
same class, so they are equal, and `Ψ(·, g) = (F ≫ k) ∘ ψ_T(·, g)` is holomorphic (`Y3ABUPrint.isHolFamily_comp`). -/
theorem holFamily_of_prints (hR : BoutotCarayolRepresentabilityPrint) (hF : MilneShimuraFamilyPrint)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hY : Y3Fix.R1fpPropsAbP Y Φ)
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hΨ : ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (Ψ z g) = M3.mk P) (g : BAQˣ) :
    ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ (toPM τ) g).left) := by
  obtain ⟨S, ΦS, hS, hU⟩ := hR
  obtain ⟨T, hTp, hTs, 𝒜, ψ, hψT, hψon, hψhol, hψfib⟩ := hF
  obtain ⟨F, hFS, hFΦ⟩ := hU T hTp hTs 𝒜 (fun s hs => by
    obtain ⟨z, g, rfl⟩ := hψon s hs
    obtain ⟨P, -, hP⟩ := hψfib z g
    exact ⟨P, hP⟩)
  obtain ⟨k, hk⟩ := compare_iso_P hY hS
  have hw : ∀ (z : HPM) (g : BAQˣ), (ψ z g ≫ F) ≫ S.hom = (fieldPt ℂ).hom := by
    intro z g
    show (ψ z g ≫ F) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
    rw [Category.assoc, hFS, ← Category.assoc, hψT z g, Category.id_comp]
  have key : ∀ (z : HPM) (g : BAQˣ), (Ψ z g).left = ψ z g ≫ (F ≫ k.hom.left) := by
    intro z g
    obtain ⟨P, hPl, hPf⟩ := hψfib z g
    have h1 : (Over.homMk (ψ z g ≫ F) (hw z g) : fieldPt ℂ ⟶ S) ≫ k.hom = Ψ z g := by
      apply (Φ ℂ).injective
      rw [← hk ℂ, hΨ z g P hPl]
      exact hFΦ (ψ z g) (hψT z g) _ rfl P hPf
    rw [← h1, Over.comp_left]
    exact Category.assoc (ψ z g) F k.hom.left
  have hfun : (fun τ : UpperHalfPlane => (Ψ (toPM τ) g).left) =
      fun τ => ψ (toPM τ) g ≫ (F ≫ k.hom.left) := by
    funext τ
    exact key _ _
  rw [hfun]
  exact Y3ABUPrint.isHolFamily_comp (F ≫ k.hom.left) (hψhol g)

/-! ## 4. The action of `Aut(ℂ)` on a witness (M2's hypothesis) -/

/-- **On every witness the moduli map satisfies M2's hypothesis on `Aut(ℂ)`.** If `P` is a moduli object of `[z, g]`
and its base change `Q` along `σ` is a moduli object of `[z', g']`, the naturality clause of `Y3Fix.R1fpPropsAbP` gives
`Φ(σ Ψ(z, g)) = [Q₁]` for a base change `Q₁` of `P` along `σ`, and `[Q₁] = [Q]` (`mk_eq_of_isBaseChangeOf`)
`= Φ(Ψ(z', g'))`. -/
theorem agree_of_witness {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hY : Y3Fix.R1fpPropsAbP Y Φ)
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hΨ : ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (Ψ z g) = M3.mk P)
    (σ : ℂ ≃+* ℂ) (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) (P Q : QML3 ℂ)
    (hP : IsLevelPoint P z g) (hQ : IsLevelPoint Q z' g') (hPQ : IsBaseChangeOf (σ : ℂ →+* ℂ) P Q) :
    galPt σ (Ψ z g) = Ψ z' g' := by
  obtain ⟨Q₁, hQ₁, hbc⟩ := hY.2.2.1 ℂ ℂ (σ : ℂ →+* ℂ).toRatAlgHom (Ψ z g) P (hΨ z g P hP)
  apply (Φ ℂ).injective
  rw [hΨ z' g' Q hQ]
  show Φ ℂ (fieldMap (σ : ℂ →+* ℂ).toRatAlgHom ≫ Ψ z g) = M3.mk Q
  rw [hQ₁]
  exact mk_eq_of_isBaseChangeOf hbc hPQ

/-! ## 5. The discharge -/

/-- **The discharge, with no GLUE.** T2a (Voight), T2c′ (Boutot–Carayol 1.5), T2c″ (Boutot–Carayol 1.4), M1 (Milne,
Theorem 14.8 as applied in §14) and M2 (Milne, §14 PEL case with Definition 12.8) give
`Y3Hodge.DeligneCanonicalModelY3EveryPrint`; the analytic representation of homomorphisms enters through the proved
`ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof`. On a witness `(Y, Φ)`, `Ψ` is the moduli map of B2.1
(`DelignePS.moduli_clauses_of_prints`: onto, the double-coset fibres, the moduli clause in the print's `H₁` form at
`g = 1` and at every `u ∈ 𝒪̂^×`); it is holomorphic (`holFamily_of_prints`), so `(Y, Ψ)` is a model
(`DelignePS.UnifK3`) on which `Aut(ℂ)` acts as on the moduli objects (`agree_of_witness`); M2 gives the reciprocity law
in the geometric normalization, and B2.4 (`DelignePS.recip_kernel_of_cv`) the row's clause, with `−ε`. -/
theorem deligneCanonicalModelY3EveryPrint_of_milne (hV : VoightQMComplexModuliPrint)
    (hP : BoutotCarayolPolarizationPrint) (hR : BoutotCarayolRepresentabilityPrint)
    (hF : MilneShimuraFamilyPrint) (hM : MilneCanonicalModelPrint) :
    Y3Hodge.DeligneCanonicalModelY3EveryPrint := by
  intro Y Φ hY
  obtain ⟨Ψ, hon, hfib, hmod, hH1, hunits⟩ :=
    moduli_clauses_of_prints hV hP ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof Y Φ
  have hhol : ∀ g : BAQˣ, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ (toPM τ) g).left) :=
    fun g => holFamily_of_prints hR hF hY hmod g
  obtain ⟨ε, δ, hrec⟩ := hM Y Ψ hY.1 hY.2.1 ⟨hon, hfib, hhol⟩
    (fun σ z g z' g' P Q hPl hQl hPQ => agree_of_witness hY hmod σ z g z' g' P Q hPl hQl hPQ)
  exact ⟨Ψ, ⟨hon, hfib, hhol, ⟨hH1, hhol 1⟩, -ε, δ, recip_kernel_of_cv hrec⟩, hunits⟩

end DelignePSMilne

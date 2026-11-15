import ZInQKernel.Contrib.OneProof.SGRDirectNV
import ZInQKernel.Contrib.OneProof.ElkiesX6Star

set_option linter.style.haveILetI false

noncomputable section

open Polynomial GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed LeafQM.AV

namespace SGRDirect

/-- **Density of `ℚ̄`-points**: in a domain of finite type over `ℚ`, an element killed by every ring map to `ℚ̄`
is zero (Hilbert's Nullstellensatz: the Jacobson radical of `0` is `0`, and every residue field at a maximal ideal
is finite over `ℚ`). -/
theorem eq_zero_of_forall_ringHom_qbar {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.FiniteType ℚ B] (x : B) (h : ∀ ψ : B →+* Qbar, ψ x = 0) : x = 0 := by
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := ℚ)
  by_contra hx
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out ‹_› (Ideal.isRadical_bot)
  have hxj : x ∉ (⊥ : Ideal B).jacobson := by rw [hj, Ideal.mem_bot]; exact hx
  rw [Ideal.jacobson, Submodule.mem_sInf] at hxj
  push Not at hxj
  obtain ⟨P, ⟨-, hPmax⟩, hxP⟩ := hxj
  haveI := hPmax
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite ℚ (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ P)
  haveI : Algebra.IsAlgebraic ℚ (B ⧸ P) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (B ⧸ P) →ₐ[ℚ] Qbar := IsAlgClosed.lift
  apply hxP
  have h1 := h ((φ : B ⧸ P →+* Qbar).comp (Ideal.Quotient.mk P))
  rw [RingHom.comp_apply] at h1
  have h0 : Ideal.Quotient.mk P x = 0 := (map_eq_zero_iff _ (φ : B ⧸ P →+* Qbar).injective).mp h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

open scoped Classical in
open CategoryTheory AlgebraicGeometry QMSplit.Moduli.ElkiesX6Star in
/-- **The coordinate comparison on every triple** (from `elkiesX6StarPrinted`, `R1R2fp`, T5): for a triple with R1fp
and R2fp there are a morphism `G : Y → Y_E` to Elkies' witness, its forgetful map `fY_E : Y_E → X_E` and Elkies'
coordinate `t_E` on `X_E` (with its charts), such that `16 (t_E − 1)/27 = π` on `ℚ̄`-points of `Y`. -/
theorem elkies_coordinate (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure) (hEl : ElkiesX6StarPrinted)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) :
    ∃ (XE : Over (Spec (CommRingCat.of ℚ))) (tE : ToP1 XE.left) (m : Y.left ⟶ XE.left),
      X6Glue.ElkiesCharts XE tE ∧
      ∀ y : fieldPt Qbar ⟶ Y,
        Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar)
            (ShimuraGlue.Mob.gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)) •
          tE.val (K := Qbar) (y.left ≫ m) = π.val (K := Qbar) y.left := by
  obtain ⟨YE, ΦE, XE, ΨE, fYE, tE, hAb, hX6, hfib, hcm, hch⟩ := hEl
  obtain ⟨hpE, hsE, -, -, hfamAb, -⟩ := hAb
  obtain ⟨𝒜, h𝒜⟩ := R1UnivRigid.r1famProps_of_r1famAbProps hfamAb
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ YE), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P :=
    fun K _ _ s => ⟨Quotient.out (ΦE K s), h𝒜 K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g', hg'⟩ := Pin.R1fpProps.univ h1 YE hpE hsE 𝒜 hall
  have hΦg : ∀ (s : fieldPt Qbar ⟶ YE), ΦE Qbar s = Φ Qbar (s ≫ g') := fun s => by
    rw [hg' Qbar s _ (h𝒜 Qbar s _ (Quotient.out_eq _).symm)]
    exact (Quotient.out_eq _).symm
  have hbij : Function.Bijective (fun s : fieldPt Qbar ⟶ YE => s ≫ g') := by
    have e : (fun s : fieldPt Qbar ⟶ YE => s ≫ g') = (Φ Qbar).symm ∘ (ΦE Qbar) := by
      funext s
      simp [hΦg]
    rw [e]
    exact (Φ Qbar).symm.bijective.comp (ΦE Qbar).bijective
  haveI : IsIso g' := CurveSplit.curveBijIso YE Y hpE hsE h1.1 h1.2.1 g' hbij
  set G : Y ⟶ YE := inv g' with hGdef
  have hΦG : ∀ y : fieldPt Qbar ⟶ Y, ΦE Qbar (y ≫ G) = Φ Qbar y := fun y => by
    rw [hΦg, Category.assoc, hGdef, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨jE, hjE⟩ := ShimuraGlue.Mob.good_all
    (ShimuraGlue.Mob.gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)) XE tE
  have hR2 : R2X6Props XE ΨE jE := by
    intro x x' P Q hP hQ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hjE x, hjE x', smul_left_cancel_iff, hfib x x']
      exact orbit_iff_twist hX6 x x' P Q hP hQ
    · intro hc
      rw [hjE x, (hcm x P hP).2.1 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
    · intro hc
      rw [hjE x, (hcm x P hP).2.2 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
    · intro hc
      rw [hjE x, (hcm x P hP).1 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
  have hX6' := hX6.2.2.2.2.2
  set π'' : ToP1 Y.left := (jE.comp fYE.left).comp G.left with hπ''
  have hval'' : ∀ y : fieldPt Qbar ⟶ Y, π''.val (K := Qbar) y.left =
      jE.val (K := Qbar) (y ≫ G ≫ fYE).left := by
    intro y
    have ea : π''.val (K := Qbar) y.left = (ToP1.comp fYE.left jE).val (K := Qbar) (y ≫ G).left :=
      ToP1.val_comp_right (ToP1.comp fYE.left jE) G.left y.left
    have eb : (ToP1.comp fYE.left jE).val (K := Qbar) (y ≫ G).left =
        jE.val (K := Qbar) ((y ≫ G) ≫ fYE).left :=
      ToP1.val_comp_right jE fYE.left (y ≫ G).left
    rw [ea, eb, Category.assoc]
  have h2'' : R2fpProps Y Φ π'' := by
    intro y y' P Q hP hQ
    have hPE : ΨE ((y ≫ G) ≫ fYE) = Quotient.mk _ P.forget := hX6' (y ≫ G) P (by rw [hΦG]; exact hP)
    have hQE : ΨE ((y' ≫ G) ≫ fYE) = Quotient.mk _ Q.forget :=
      hX6' (y' ≫ G) Q (by rw [hΦG]; exact hQ)
    rw [Category.assoc] at hPE hQE
    have h := hR2 (y ≫ G ≫ fYE) (y' ≫ G ≫ fYE) P.forget Q.forget hPE hQE
    rw [hval'' y, hval'' y']
    exact h
  have hM := CurveGlue.mobiusGlue_of_T5 hT
  have hCM := Pin.cm_objects_of_R1R2fp hRR
  have hmob := hM Y Y Φ Φ π π'' (𝟙 Y) h1 h2 h1 h2'' hCM (fun K _ _ y => by rw [Category.comp_id])
  refine ⟨XE, tE, G.left ≫ fYE.left, hch, fun y => ?_⟩
  have e1 := hmob y
  rw [Category.comp_id, hval'', hjE] at e1
  have e2 : (y ≫ G ≫ fYE).left = y.left ≫ G.left ≫ fYE.left := by simp [Over.comp_left]
  rw [e2] at e1
  exact e1

end SGRDirect

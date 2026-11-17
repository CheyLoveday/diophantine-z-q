import ZInQKernel.Contrib.OneProof.CMBranch.Localize
import ZInQKernel.OneProof.H.TailF

/-! # cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex L581-586) reduced

Step 1 (this file): the reduction `cmFibreSplit_of` of the glue `CMFibreSplit` to
* `CMHomFieldModel` (A8's Hom field at a fibre, L540-561, without the conjugacy maps),
* `CMMatrixUnitSplit` (L582-586: matrix units of `End⁰(A_ℚ̄) = M₂(k)` over `L`),
with the case `End⁰(P.A) ≅ M₂(ℚ(√d))` read off from Yu's dichotomy (the chain's leaf `YuB6Alg`).
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace HDec
namespace CMBranch
namespace FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch
open scoped Quaternion TensorProduct

/-- `ℚ(√d)`, as in the chain's form of Yu's dichotomy (`QMLattice.YuB6Alg`). -/
abbrev Kd (d : ℚ) : Type := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)

/-- **Glue (manuscript L540-561, A8, the Hom field; no conjugacy maps).** At every fibre context
(moduli data with R1-R2's clauses, `u ∉ 𝒞`, a `ℚ̄`-point carrying `P` over `J(u)`) there is a number
field `L ⊆ ℚ̄` with `[L:ℚ] ≤ D` and a model `A/L` of `P.A` (an isomorphism of abelian varieties
`A_ℚ̄ ≅ P.A`) over which every geometric endomorphism is defined (`End(A) → End(A_ℚ̄)` onto):
`L = EK`, `E` the kernel field of `G_ℚ` on the endomorphism lattice of `W₀ = Res_{K/ℚ} A`. -/
def CMHomFieldModel : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), G0ModField.FibreCtx Y Φ π u P →
    ∃ (L : G0ModField.IF) (_ : FiniteDimensional ℚ L), Module.finrank ℚ L ≤ heightD ∧
      ∃ (A : PkgI3.AbVar L) (θ : PkgI3.AbVar.Hom (A.baseChange Qbar) P.A)
        (θ' : PkgI3.AbVar.Hom P.A (A.baseChange Qbar)),
        θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
        Function.Surjective (G0ModField.KernelField.endBC A Qbar)

/-- **Glue (manuscript L582-586: matrix units).** An abelian surface `A` over a number field `L`
all of whose geometric endomorphisms are defined over `L` (`End(A) → End(A_Ω)` onto, `Ω` an
algebraic closure), with `End⁰(A_Ω) ≅ M₂(ℚ(√d))`, `d < 0`: multiples of matrix units give an
elliptic curve `E/L` (the image of a multiple of `e₁₁`) whose geometric endomorphism ring is an order
`R` of an imaginary quadratic field `k`, the product `E² = E × E`, and an `L`-isogeny `E² → A`
(`(x, y) ↦ x + m e₂₁ y`). -/
def CMMatrixUnitSplit : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L), A.dim = 2 →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω],
      Function.Surjective (G0ModField.KernelField.endBC A Ω) →
      ∀ d : ℚ, d < 0 →
        Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
        ∃ (E Pr : ZInQ.DefFaltings.AbVar L) (k : Type) (_ : Field k) (_ : NumberField k)
          (R : Subring k),
          E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧
          (∃ φ : Pr.X ⟶ ((LeafAdopt.abVarEquiv L).symm A).X, IsIsogeny φ) ∧
          IsImagQuadOrder k R ∧ IsCMBy E k R


/-! ## 1. The CM case of Yu's dichotomy -/

/-- **`End⁰ ≅ B` forces `End = ι(𝒪)`** (the chain's `G0ModField.KernelField.endEqOFibre_of_hf`, lines
after its case analysis copied verbatim: `B → End⁰` is onto by dimension, `End` is an order of
`ι(B)` containing the maximal order `ι(𝒪)`). -/
theorem end_eq_iota_of_B (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (P : QML3 Qbar) (hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]))
    (f : PkgI3.AbVar.End P.A) : ∃ a : LeafQM.O, f = P.q.iota a := by
  have hmax := G0ModField.KernelField.oMaximal
  obtain ⟨e⟩ := hB
  let φ : LeafQM.B →ₐ[ℚ] PkgI3.AbVar.End0 P.A := (G0FibreSimple.qmBasis P.q).liftHom
  haveI : Nontrivial (PkgI3.AbVar.End0 P.A) := e.toEquiv.nontrivial
  have hinj : Function.Injective φ := φ.toRingHom.injective
  haveI : FiniteDimensional ℚ (PkgI3.AbVar.End0 P.A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hrank : Module.finrank ℚ LeafQM.B = Module.finrank ℚ (PkgI3.AbVar.End0 P.A) :=
    e.toLinearEquiv.finrank_eq.symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  let j : PkgI3.AbVar.End P.A →ₐ[ℤ] PkgI3.AbVar.End0 P.A := Algebra.TensorProduct.includeRight
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar _root_.HFReroute.sigmaQbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar _root_.HFReroute.sigmaQbar P.A P.A).2.1
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End P.A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End P.A) (S := ℚ))
  have hjinj : Function.Injective j := by
    intro x y hxy
    have hm : (1 : ℚ) ⊗ₜ[ℤ] (x - y) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s'))
  -- `φ` agrees with `j ∘ ι` on `𝒪`
  have hagree : ∀ a : LeafQM.O, φ (a : LeafQM.B) = j (P.q.iota a) := by
    let ψ1 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := φ.toRingHom.comp (Subring.subtype _)
    let ψ2 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := j.toRingHom.comp P.q.iota
    have hi : ψ1 G0FibreSimple.oi = ψ2 G0FibreSimple.oi := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oi : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oi, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    have hj : ψ1 G0FibreSimple.oj = ψ2 G0FibreSimple.oj := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oj : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oj, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    intro a
    obtain ⟨n, hn⟩ := a.2
    have h2 : (2 : LeafQM.O) * a = ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
        ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * G0FibreSimple.oi +
        ((n 2 : ℤ) : LeafQM.O) * G0FibreSimple.oj +
        ((n 3 : ℤ) : LeafQM.O) * (G0FibreSimple.oi * G0FibreSimple.oj) := by
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      rw [show ((2 : LeafQM.O) : LeafQM.B) = 2 from rfl, hn]
      ext <;> simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat,
        QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;>
        ring
    have key : ∀ ψ : LeafQM.O →+* PkgI3.AbVar.End0 P.A, ψ ((2 : LeafQM.O) * a) =
        ((2 * n 0 + n 2 : ℤ) : PkgI3.AbVar.End0 P.A) +
        ((2 * n 1 + n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oi +
        ((n 2 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oj +
        ((n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * (ψ G0FibreSimple.oi * ψ G0FibreSimple.oj) := by
      intro ψ
      rw [h2]; simp only [map_add, map_mul, map_intCast]
    have e1 : (2 : PkgI3.AbVar.End0 P.A) * ψ1 a = (2 : PkgI3.AbVar.End0 P.A) * ψ2 a := by
      have := key ψ1
      rw [map_mul, map_ofNat] at this
      rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
    have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
      rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e1
    exact smul_right_injective (PkgI3.AbVar.End0 P.A) (two_ne_zero : (2 : ℚ) ≠ 0) e2
  -- the order `R = φ⁻¹(End)`
  let R : Subring LeafQM.B := (j.toRingHom.range).comap φ.toRingHom
  have hOR : LeafQM.O ≤ R := fun x hx => ⟨P.q.iota ⟨x, hx⟩, (hagree ⟨x, hx⟩).symm⟩
  have hint : ∀ x ∈ R, IsIntegral ℤ x := by
    rintro x ⟨g, hg⟩
    have h1 : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    have h2 : IsIntegral ℤ (φ x) := by
      have := h1.map j
      rwa [show j g = φ x from hg] at this
    exact (isIntegral_algHom_iff (φ.restrictScalars ℤ) hinj).mp h2
  obtain ⟨x, hx⟩ := hsurj (j f)
  have hxO : x ∈ LeafQM.O := hmax R hOR hint ⟨f, hx.symm⟩
  refine ⟨⟨x, hxO⟩, hjinj ?_⟩
  rw [← hagree, ← hx]

/-- The centre of `𝒪` is `ℤ`: an element commuting with `i` and `j` is an integer. -/
theorem central_O (a : LeafQM.O) (hi : a * G0FibreSimple.oi = G0FibreSimple.oi * a)
    (hj : a * G0FibreSimple.oj = G0FibreSimple.oj * a) : ∃ n : ℤ, a = n := by
  obtain ⟨v, hv⟩ := a.2
  have hi' := congrArg Subtype.val hi
  have hj' := congrArg Subtype.val hj
  simp only [Subring.coe_mul] at hi' hj'
  rw [hv] at hi' hj'
  have e1 := congrArg QuaternionAlgebra.imJ hi'
  have e2 := congrArg QuaternionAlgebra.imK hi'
  have e3 := congrArg QuaternionAlgebra.imI hj'
  have e4 := congrArg QuaternionAlgebra.imK hj'
  simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt] at e1 e2 e3 e4
  refine ⟨v 0, Subtype.ext ?_⟩
  rw [hv]
  have h2 : (v 2 : ℚ) = 0 := by linarith
  have h3 : (v 3 : ℚ) = 0 := by linarith
  have h1 : (v 1 : ℚ) = 0 := by linarith
  ext <;> simp [LeafQM.ofInt, h1, h2, h3]

/-- **The CM case (manuscript L572-581, through Yu's dichotomy).** If the `𝒪`-centralizer of a QM
surface over `ℚ̄` contains a non-integer, then `End⁰ ≅ M₂(ℚ(√d))` with `d < 0`. -/
theorem end0Matrix_of_noncentral (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (P : QML3 Qbar)
    (φ : PkgI3.AbVar.End P.A) (hφ : φ ∈ com P.q) (hne : ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End P.A)) :
    ∃ d : ℚ, d < 0 ∧ Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) := by
  rcases hYu Qbar P.A P.surface P.q with hB | h
  · exfalso
    obtain ⟨a, ha⟩ := end_eq_iota_of_B hHF P hB φ
    have hc : ∀ b : LeafQM.O, a * b = b * a := by
      intro b
      apply P.q.injective
      have := hφ (P.q.iota b) ⟨b, rfl⟩
      rw [map_mul, map_mul, ← ha]
      exact this.symm
    obtain ⟨n, hn⟩ := central_O a (hc _) (hc _)
    apply hne n
    rw [ha, hn, map_intCast]
  · exact h

/-! ## 2. Transport of `End` along an isomorphism of abelian varieties -/

/-- `End A ≅ End B` for inverse homomorphisms `θ : A → B`, `θ' : B → A`. -/
def endEquivOfIso {K : Type} [Field K] {A B : PkgI3.AbVar K} (θ : PkgI3.AbVar.Hom A B)
    (θ' : PkgI3.AbVar.Hom B A) (h1 : θ.hom ≫ θ'.hom = 𝟙 _) (h2 : θ'.hom ≫ θ.hom = 𝟙 _) :
    PkgI3.AbVar.End A ≃+* PkgI3.AbVar.End B where
  toFun f := PkgI3.AbVar.Hom.mk' (θ'.hom ≫ f.hom ≫ θ.hom)
  invFun g := PkgI3.AbVar.Hom.mk' (θ.hom ≫ g.hom ≫ θ'.hom)
  left_inv f := PkgI3.AbVar.Hom.ext' (by
    simp only [PkgI3.AbVar.Hom.hom_mk']
    rw [reassoc_of% h1, Category.assoc, h1, Category.comp_id])
  right_inv g := PkgI3.AbVar.Hom.ext' (by
    simp only [PkgI3.AbVar.Hom.hom_mk']
    rw [reassoc_of% h2, Category.assoc, h2, Category.comp_id])
  map_mul' f g := PkgI3.AbVar.Hom.ext' (by
    change θ'.hom ≫ (g.hom ≫ f.hom) ≫ θ.hom =
      (θ'.hom ≫ g.hom ≫ θ.hom) ≫ θ'.hom ≫ f.hom ≫ θ.hom
    simp only [Category.assoc]
    rw [reassoc_of% h1])
  map_add' f g := PkgI3.AbVar.Hom.ext' (by
    change θ'.hom ≫ (f.hom * g.hom) ≫ θ.hom =
      (θ'.hom ≫ f.hom ≫ θ.hom) * (θ'.hom ≫ g.hom ≫ θ.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, Category.assoc])

/-- `End⁰ A ≅ End⁰ B` as `ℚ`-algebras, for inverse homomorphisms. -/
def end0EquivOfIso {K : Type} [Field K] {A B : PkgI3.AbVar K} (θ : PkgI3.AbVar.Hom A B)
    (θ' : PkgI3.AbVar.Hom B A) (h1 : θ.hom ≫ θ'.hom = 𝟙 _) (h2 : θ'.hom ≫ θ.hom = 𝟙 _) :
    PkgI3.AbVar.End0 A ≃ₐ[ℚ] PkgI3.AbVar.End0 B :=
  Algebra.TensorProduct.congr AlgEquiv.refl (endEquivOfIso θ θ' h1 h2).toIntAlgEquiv

/-! ## 3. The reduction of `CMFibreSplit` -/

/-- **`CMFibreSplit` from A8's Hom field and the matrix units** (with the chain's leaves T27 = Yu,
`YuB6Alg`, and T6, `HomFreeFiniteC`). A fibre with CM has a `ℚ̄`-point `P` whose `𝒪`-centralizer
contains a non-integer; then `End⁰(P.A) ≅ M₂(ℚ(√d))` (Yu, `end0Matrix_of_noncentral`), A8 gives
`A/L` with `[L:ℚ] ≤ D`, `A_ℚ̄ ≅ P.A` and every geometric endomorphism defined over `L`, and the
matrix units give `E`, `E²`, the isogeny and the order. -/
theorem cmFibreSplit_of (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hA8 : CMHomFieldModel) (hMU : CMMatrixUnitSplit) : CMFibreSplit := by
  intro Y Φ π hR1 hR2 u hu hCM
  simp only [NoCMAt, not_forall, not_exists] at hCM
  obtain ⟨y, P, hP, hπ, φ, hφ, hne⟩ := hCM
  obtain ⟨L, hfin, hdeg, A, θ, θ', h1, h2, hsurj⟩ := hA8 Y Φ π u P ⟨hR1, hR2, hu, y, hP, hπ⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := end0Matrix_of_noncentral hYu hHF P φ hφ hne
  letI : NumberField L := G0ModField.numberField_of_fd L
  have hiso : letI : Algebra L Qbar := (algebraMap L Qbar).toAlgebra;
      Nonempty ((((LeafAdopt.abVarEquiv L).symm A).baseChange Qbar).X ≅ P.A.X) :=
    ⟨⟨θ.hom, θ'.hom, h1, h2⟩⟩
  have hA2 : A.dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L Qbar) ((LeafAdopt.abVarEquiv L).symm A)
      P.A hiso P.surface
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨E, Pr, k, i1, i2, R, hE, hPr, hprod, hisog, hR, hcm⟩ :=
    hMU L A hA2 Qbar hsurj d hd ⟨(end0EquivOfIso θ θ' h1 h2).trans e⟩
  exact ⟨⟨L⟩, (LeafAdopt.abVarEquiv L).symm A, E, Pr, k, i1, i2, R,
    ⟨algebraMap L Qbar, y, P, hP, hπ, hiso⟩, hdeg, hE, hPr, hprod, hisog, hR, hcm⟩

end FibreSplit
end CMBranch
end HDec

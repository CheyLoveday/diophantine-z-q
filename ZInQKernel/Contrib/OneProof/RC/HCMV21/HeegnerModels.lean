import ZInQKernel.Contrib.OneProof.RC.HCMV21.ConductorOne
import ZInQKernel.Contrib.OneProof.RC.HCMV21.IdealLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.Reciprocity
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrientedIdeals
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimeComparison
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusLower
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! The two lattices of the actual Heegner argument, using the CMField2 ideal
calculation. The chosen point on the normalization is specified by its
upper half-plane argument, even where the pair of plane coordinates is
insufficient to specify a branch. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField Module FractionalIdeal TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve nonZeroDivisors Classical

variable {F : Type} [Field F] [NumberField F]

/-- The scaled period basis `[a, aτ]` used in the ideal presentation. -/
def formPeriod (a B d : ℤ) (ha : 0 < a) : PeriodPair :=
  (PeriodPair.ofTau (cmPoint a B d)).scale
    (Units.mk0 (a : ℂ) (by exact_mod_cast ha.ne'))

/-- The exact lattice of the form, in the specified CM embedding. -/
theorem formPeriod_lattice (O : NumberFieldOrder F) (κ : F →+* ℂ)
    {a B C d : ℤ} (ha : 0 < a) (hd : d < 0) (ω : F)
    (hgen : ∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : F) = (u : F) + (v : F) * ω)
    (hω : ω ^ 2 + (B : F) * ω + (a : F) * (C : F) = 0)
    (he : κ ω = (-(B : ℂ) + Complex.I * (Real.sqrt (-(d : ℝ)) : ℂ)) / 2) :
    ((formPeriod a B d ha).lattice : Set ℂ) = κ '' (CMField2.formIdeal O a ω : Set F) := by
  let k := κ.toRatAlgHom.toLinearMap.restrictScalars ℤ
  have hJ : (CMField2.formIdeal O a ω : Set F) = (CMField2.pairLattice a ω : Set F) :=
    congrArg (fun U : Submodule ℤ F => (U : Set F))
      (CMField2.formIdeal_restrictScalars O a B C ω hgen hω)
  rw [hJ]
  change ((formPeriod a B d ha).lattice : Set ℂ) = ((CMField2.pairLattice a ω).map k : Set ℂ)
  rw [CMField2.pairLattice, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
  have hw : (a : ℂ) * (cmPoint a B d : ℂ) = κ ω := by
    rw [CMField2.coe_cmPoint_of_neg ha hd, he]
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
  change (Submodule.span ℤ {((a : ℂ) * (cmPoint a B d : ℂ)), (a : ℂ) * 1} : Set ℂ) =
    (Submodule.span ℤ {κ (a : F), κ ω} : Set ℂ)
  rw [hw, mul_one, map_intCast]
  congr 2
  exact Set.pair_comm _ _

/-- At conductor one the actual `Γ₀(N)` lattice pair is the quotient
by the torsion for the one level ideal. `a = A/N` and the two periods
use scales `A` and `a` respectively, so the inclusion uses the same
ambient complex line. -/
theorem heegnerForm_ideal_pair
    (hk : finrank ℚ F = 2) (hc : IsTotallyComplex F) (κ : F →+* ℂ)
    {N : ℕ} [NeZero N] {A B C : ℤ}
    (hd : discr F < 0) (hcop : IsCoprime (discr F) (N : ℤ))
    (hf : IsHeegnerForm N (discr F) A B C) :
    ∃ (a : ℤ) (ha : 0 < a) (_ : A = (N : ℤ) * a)
      (I : FractionalIdeal (𝓞 F)⁰ F) (n : Ideal (𝓞 F)),
        I ≠ 0 ∧ n ≠ ⊥ ∧
        IsIdealPeriod κ I (formPeriod A B (discr F) hf.1) ∧
        IsIdealPeriod κ (idealTranslate n I) (formPeriod a B (discr F) ha) ∧
        X0Model.dilate N (cmPoint A B (discr F)) = cmPoint a B (discr F) ∧
        ∃ w : 𝓞 F, n = Ideal.span {(N : 𝓞 F), w} ∧
          κ (w : F) = (-(B : ℂ) + Complex.I * (Real.sqrt (-(discr F : ℝ)) : ℂ)) / 2 := by
  let O := maximalNumberFieldOrder F
  have hD : O.discr = discr F := NumberFieldOrder.discr_maximal
  obtain ⟨ω, hw, hgen, hp, he⟩ :=
    CMField2.exists_heegner_generator_in_embedding O hk hc κ hD hd hf.2.2.1
  obtain ⟨a, ha, hfa⟩ := CMField2.heegner_scaled_form hcop hf
  have hAB : IsCoprime (N : ℤ) B := (CMField2.heegner_middle_coprime hcop hf).symm
  let I : FractionalIdeal (𝓞 F)⁰ F := CMField2.formIdeal O A ω
  have hI : I ≠ 0 := (CMField2.formIdeal_isUnit O A B C ω hw hf.1.ne' hf.2.2.2 hp).ne_zero
  have hw' : ω ∈ integralClosure ℤ F := hw
  let w : 𝓞 F := ⟨ω, hw'⟩
  let n : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F), w}
  have hn₀ : (N : 𝓞 F) ∈ n := Ideal.subset_span (by simp)
  have hn : n ≠ ⊥ := by
    intro h
    have hh : (N : 𝓞 F) = 0 := by simpa only [h, Ideal.mem_bot] using hn₀
    exact (Nat.cast_ne_zero.mpr (NeZero.ne N)) hh
  let JN : FractionalIdeal (𝓞 F)⁰ F := CMField2.formIdeal O (N : ℤ) ω
  let Ja : FractionalIdeal (𝓞 F)⁰ F := CMField2.formIdeal O a ω
  have hnI : (n : FractionalIdeal (𝓞 F)⁰ F) = JN := by
    apply coeToSubmodule_injective
    change ((n : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = (JN : Submodule (𝓞 F) F)
    have hspan : (JN : Submodule (𝓞 F) F) = Submodule.span (𝓞 F) {(N : F), ω} := by
      have h := CMField2.formIdeal_coe O (N : ℤ) ω
      push_cast at h
      exact h
    rw [hspan, coe_coeIdeal]
    change IsLocalization.coeSubmodule F (Ideal.span {(N : 𝓞 F), w}) = _
    rw [IsLocalization.coeSubmodule_span, Set.image_insert_eq, Set.image_singleton]
    simp [w]
  have hmul : JN * Ja = I := CMField2.formIdeal_mul_scaled O ω ha hAB hgen hp
  have hp' : ω ^ 2 + (B : F) * ω + (a : F) * (((N : ℤ) * C : ℤ) : F) = 0 := by
    rw [ha] at hp
    push_cast at hp ⊢
    linear_combination hp
  refine ⟨a, hfa.1, ha, I, n, hI, hn, formPeriod_lattice O κ hf.1 hd ω hgen hp he, ?_,
    CMField2.dilate_cmPoint_eq hf.1 ha hd, ⟨w, rfl, he⟩⟩
  have ht : idealTranslate n I = Ja := by
    unfold idealTranslate
    apply (div_eq_iff (coeIdeal_eq_zero.not.mpr hn)).mpr
    rw [hnI, mul_comm]
    exact hmul.symm
  unfold IsIdealPeriod
  rw [ht]
  exact formPeriod_lattice O κ hfa.1 hd ω hgen hp' he

/-- Use the actual argument from the conductor-one datum rather than
selecting a point from the fibre of the two plane functions. -/
def heegnerBranchPoint {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2} {L : PeriodPair} {s : ℂ} {d t : ℤ}
    (dat : HeegnerDatum E f L s d 1 t) [NeZero (newformLevel E)] :=
  (X0Branch.model (newformLevel E)).complexPoint (cmPoint dat.A dat.B (d * (1 : ℤ) ^ 2))

/-- Reuse the integral CM singular moduli and their membership in one
embedding of the Hilbert class field. No field-generation claim is needed
to build Weierstrass curves with those invariants. -/
theorem hilbert_j_integral_values (hk : finrank ℚ F = 2) (hc : IsTotallyComplex F)
    (κ : F →+* ℂ) :
    ∃ i : hilbertClassField F →+* ℂ,
      i.comp (algebraMap F _) = κ ∧
      ∀ (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (P : PeriodPair), IsIdealPeriod κ I.val P →
        ∃ x : hilbertClassField F, IsIntegral ℤ x ∧ i x = P.jLattice := by
  let O := maximalNumberFieldOrder F
  obtain ⟨i, hi, h⟩ := CMField2.singularModulusMemRingClass F O hk hc κ
  have hH : ringClassField O = hilbertClassField F := ringClassField_maximal_eq_hilbertClassField F
  rw [← hH]
  refine ⟨i, hi, ?_⟩
  intro I P hP
  obtain ⟨x, hx⟩ := h I
  have hJ : CMField2.singularModulus O hk hc κ I = P.jLattice := by
    apply CMField2.jLattice_eq_of_lattice_eq
    exact SetLike.coe_injective ((CMField2.idealPeriod_lattice O hk hc κ I).trans hP.symm)
  refine ⟨x, ?_, hx.trans hJ⟩
  let iZ : ringClassField O →ₐ[ℤ] ℂ :=
    { toRingHom := i, commutes' := map_intCast i }
  apply (isIntegral_algHom_iff iZ i.injective).mp
  change IsIntegral ℤ (i x)
  rw [hx]
  exact CMField2.singularModulus_isIntegral O hk hc κ I

/-- The canonical equation with the descended j-value is a geometric
model of the analytic elliptic curve. Transporting the order action
and cyclic subgroup still requires choosing their fields of definition. -/
theorem exists_variableChange_ofJ_of_lattice {H : Type*} [Field H] (i : H →+* ℂ)
    (x : H) (P : PeriodPair) [P.weierstrassCurve.IsElliptic] (hx : i x = P.jLattice) :
    ∃ C : WeierstrassCurve.VariableChange ℂ,
      C • (WeierstrassCurve.ofJ x).map i = P.weierstrassCurve := by
  apply WeierstrassCurve.exists_variableChange_of_j_eq
  rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j, hx, P.jLattice_eq_c₄_pow_three_div_Δ]
  rw [WeierstrassCurve.j_eq, div_eq_mul_inv, mul_comm]

end ZInQ.Manuscript.RC.HCMV21

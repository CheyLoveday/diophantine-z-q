import ZInQKernel.Contrib.OneProof.RC.HCMV21.ClassFieldGeneration
import ZInQKernel.Contrib.OneProof.RC.HCMV21.AnalyticTorsor
import ZInQKernel.Contrib.OneProof.RC.CMField2.ScalarWitness
import ZInQKernel.Contrib.OneProof.RC.CMField2.Kronecker

/-! The reverse class-field degree calculation when the Hilbert-class Artin
action is matched with the inverse-ideal action. Also record the off-diagonal
split-prime test needed for an independent proof of that calculation. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open scoped nonZeroDivisors

/-- Distinct ideal classes have distinct j-values. The complex scaling
coming from a j-equality already belongs to the quadratic field. -/
theorem idealClass_eq_of_jLattice_eq {F : Type} [Field F] [NumberField F]
    (κ : F →+* ℂ) (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (P Q : PeriodPair)
    (hP : IsIdealPeriod κ I.val P) (hQ : IsIdealPeriod κ J.val Q)
    (h : P.jLattice = Q.jLattice) :
    ClassGroup.mk F I = ClassGroup.mk F J := by
  obtain ⟨u, hu⟩ := CMField2.exists_homothetic_of_jLattice_eq P Q h
  have hE : (fun x : F => (u : ℂ) * κ x) '' (I.val : Set F) = κ '' (J.val : Set F) := by
    have hh := congrArg (fun L : Submodule ℤ ℂ => (L : Set ℂ)) hu
    rw [CMField2.lattice_scale, hP, hQ, Set.image_image] at hh
    exact hh
  have ht := (idealClass_eq_iff_complexHomothety κ I J).mpr ⟨u, u.ne_zero, hE⟩
  apply (ClassGroup.equiv F).injective
  rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self]
  convert ht using 1 <;> rfl

/-- A descended singular modulus generates the Hilbert class field once the
Artin formula on j is available. This proves the reverse degree inequality
without using a class-polynomial degree or generation print. -/
theorem hilbertField_eq_adjoin_of_artinActsOnJ
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (hk : Module.finrank ℚ F = 2) (hArtin : ArtinActsOnJ)
    (e : SeparableClosure F →+* ℂ) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (P : PeriodPair) (hP : IsIdealPeriod (e.comp (algebraMap F (SeparableClosure F))) I.val P)
    (x : hilbertClassField F) (hx : e x = P.jLattice) :
    IntermediateField.adjoin F {(x : SeparableClosure F)} = hilbertClassField F := by
  let κ := e.comp (algebraMap F (SeparableClosure F))
  apply hilbertField_eq_adjoin_of_freeArtinOrbit x
  intro c h
  obtain ⟨a, rfl⟩ := ClassGroup.mk0_surjective (R := 𝓞 F) c
  let J := I / FractionalIdeal.mk0 F a
  let Q := CMField2.idealPeriod (maximalNumberFieldOrder F) hk inferInstance κ J
  have hQ : IsIdealPeriod κ J.val Q :=
    CMField2.idealPeriod_lattice (maximalNumberFieldOrder F) hk inferInstance κ J
  have hQa : IsIdealPeriod κ
      (I.val / ((a : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) Q := by
    simpa only [J, Units.val_div_eq_div_val, FractionalIdeal.coe_mk0] using hQ
  have hj := hArtin F hk e I.val a P Q hP hQa x hx
  rw [h, hx] at hj
  have hIJ := idealClass_eq_of_jLattice_eq κ I J P Q hP hQ hj
  rw [show J = I / FractionalIdeal.mk0 F a from rfl, map_div, ClassGroup.mk_mk0, eq_comm,
    div_eq_self] at hIJ
  exact hIJ

open Polynomial ModularCurve in
/-- The off-diagonal part of the split-prime test. If the first residue
value already lies in the prime field, a prime-degree modular equation
forces the second residue value to be the same. -/
theorem eq_of_kronecker_root_of_fixed (p : ℕ) [Fact p.Prime]
    (D : ModularPolynomialData p) {k : Type*} [Field k] [CharP k p]
    (x y : k) (hx : x ^ p = x)
    (hxy : (D.Φ.map (eval₂RingHom (Int.castRingHom k) x)).eval y = 0) :
    y = x := by
  let f := ZMod.castHom (dvd_refl p) k
  let g := eval₂RingHom f x
  have hg : g.comp (mapRingHom (Int.castRingHom (ZMod p))) =
      eval₂RingHom (Int.castRingHom k) x := by
    apply Polynomial.ringHom_ext' (Subsingleton.elim _ _)
    simp [g]
  have h := congrArg (fun P : (ZMod p)[X][X] => P.eval₂ g y)
    (CMField2.kroneckerCongruence_of_prime p D)
  change (reduceModBivar p D.Φ).eval₂ g y =
    (((C X : (ZMod p)[X][X]) ^ p - X) * (C X - X ^ p)).eval₂ g y at h
  rw [reduceModBivar, coe_mapRingHom, eval₂_map, hg, ← eval_map, hxy] at h
  have h' : (x ^ p - y) * (x - y ^ p) = 0 := by
    simpa [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, g] using h.symm
  rcases mul_eq_zero.mp h' with h₁ | h₂
  · exact (sub_eq_zero.mp h₁).symm.trans hx
  · apply (frobenius k p).injective
    change y ^ p = x ^ p
    exact (sub_eq_zero.mp h₂).symm.trans hx.symm

end ZInQ.Manuscript.RC.HCMV21

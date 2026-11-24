import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization

/-! Printed inputs for conductor-one reciprocity. The `j` here is the classical
complex lattice invariant, and the Artin map is the existing class-field map. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField TauCeti TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- A period basis for the image of `I` under the fixed complex embedding. -/
def IsIdealPeriod (ι : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) (P : PeriodPair) : Prop :=
  (P.lattice : Set ℂ) = ι '' (I : Set K)

/-- Candidate printed input, UNVERIFIED locator: Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, Thm. II.6.1 (integrality of singular moduli). This uses
only integrality of each root of the monic integral class polynomial. -/
def IntegralSingularModuli : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (ι : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) (P : PeriodPair),
      IsIdealPeriod ι I P → IsIntegral ℤ P.jLattice

/-- Candidate printed input, UNVERIFIED locator: Silverman, *Advanced Topics*, Ch. II
(main theorem of CM for the maximal order); *AEC*, Appendix C §11. A single singular
modulus generates the Hilbert class field with the given embedding of `K`. -/
def HilbertClassFieldGeneratedByJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (e : SeparableClosure K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) (P : PeriodPair),
      IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K))) I P →
      ∃ x : SeparableClosure K, e x = P.jLattice ∧
        IntermediateField.adjoin K {x} = hilbertClassField K

/-- Candidate printed input, UNVERIFIED locator: Silverman, *Advanced Topics*, Ch. II
(main theorem of CM); Shimura, *Introduction*, Thm. 5.4 specialized to `j`. In the
arithmetic Artin convention an integral ideal `a` sends the lattice invariant to
that of `a⁻¹ I`. At a prime the Artin automorphism is arithmetic Frobenius. -/
def ArtinActsOnJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (e : SeparableClosure K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K)
      (a : (Ideal (𝓞 K))⁰) (P Q : PeriodPair),
      IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K))) I P →
      IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K)))
        (I / ((a : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) Q →
      ∀ x : hilbertClassField K, e x = P.jLattice →
        e (hilbertClassArtinEquiv K (ClassGroup.mk0 a) x) = Q.jLattice

/-- The generation statement supplies an element of the actual class field with
this complex lattice invariant, which the reciprocity statement can then act on. -/
theorem exists_artin_conjugate_j [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (hgen : HilbertClassFieldGeneratedByJ) (hart : ArtinActsOnJ)
    (e : SeparableClosure K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K)
    (a : (Ideal (𝓞 K))⁰) (P Q : PeriodPair)
    (hP : IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K))) I P)
    (hQ : IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K)))
      (I / ((a : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) Q) :
    ∃ x : hilbertClassField K, e x = P.jLattice ∧
      e (hilbertClassArtinEquiv K (ClassGroup.mk0 a) x) = Q.jLattice := by
  obtain ⟨x, hx, hH⟩ := hgen K hK e I P hP
  let xH : hilbertClassField K := ⟨x, hH ▸ IntermediateField.mem_adjoin_simple_self K x⟩
  exact ⟨xH, hx, hart K hK e I a P Q hP hQ xH hx⟩

/-- The ideal-class action at a prime uses arithmetic, rather than geometric,
Frobenius. This is the existing splitting law at the trivial modulus. -/
theorem hilbert_artin_is_arithmetic_frobenius
    (a : (Ideal (𝓞 K))⁰) [(a : Ideal (𝓞 K)).IsMaximal]
    (Q : Ideal (𝓞 (hilbertClassField K))) [Q.IsPrime] [Q.LiesOver (a : Ideal (𝓞 K))] :
    IsArithFrobAt (𝓞 K) (hilbertClassArtinEquiv K (ClassGroup.mk0 a)) Q := by
  let I : integralIdealsPrimeTo (Modulus.one K) := ⟨a, Modulus.mem_integralIdealsPrimeTo.mpr
    (Modulus.isCoprimeTo_iff_sup_eq_top.mpr
      ⟨mem_nonZeroDivisors_iff_ne_zero.mp a.2, by simp⟩)⟩
  have hI : ClassGroup.mk0 a = oneEquivClassGroup (idealClass (Modulus.one K) I) := by
    rw [idealClass_apply, oneEquivClassGroup_rayClassMk, ← ClassGroup.mk_mk0 K a]
    congr 1
  rw [hI, hilbertClassArtinEquiv_oneEquivClassGroup, rayClassArtinEquiv_apply]
  exact isArithFrobAt_rayClassArtinMap_idealClass _ I Q

/-- At a nonzero prime the translated singular modulus is the image under
arithmetic Frobenius at the chosen prime of the Hilbert class field. -/
theorem exists_frobenius_conjugate_j [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (hgen : HilbertClassFieldGeneratedByJ) (hart : ArtinActsOnJ)
    (e : SeparableClosure K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K)
    (a : (Ideal (𝓞 K))⁰) [(a : Ideal (𝓞 K)).IsMaximal] (P Q : PeriodPair)
    (hP : IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K))) I P)
    (hQ : IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K)))
      (I / ((a : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) Q)
    (v : Ideal (𝓞 (hilbertClassField K))) [v.IsPrime] [v.LiesOver (a : Ideal (𝓞 K))] :
    ∃ (σ : hilbertClassField K ≃ₐ[K] hilbertClassField K) (x : hilbertClassField K),
      IsArithFrobAt (𝓞 K) σ v ∧ e x = P.jLattice ∧ e (σ x) = Q.jLattice := by
  obtain ⟨x, hx, hσ⟩ := exists_artin_conjugate_j hK hgen hart e I a P Q hP hQ
  exact ⟨hilbertClassArtinEquiv K (ClassGroup.mk0 a), x,
    hilbert_artin_is_arithmetic_frobenius a v, hx, hσ⟩

/-- An element of the Hilbert class field representing the complex singular
modulus is integral there as well. This can be transported to a completion. -/
theorem isIntegral_hilbert_j [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (hint : IntegralSingularModuli) (e : SeparableClosure K →+* ℂ)
    (I : FractionalIdeal (𝓞 K)⁰ K) (P : PeriodPair)
    (hP : IsIdealPeriod (e.comp (algebraMap K (SeparableClosure K))) I P)
    (x : hilbertClassField K) (hx : e x = P.jLattice) : IsIntegral ℤ x := by
  let eZ : hilbertClassField K →ₐ[ℤ] ℂ :=
    { toRingHom := e.comp (hilbertClassField K).val.toRingHom
      commutes' := map_intCast _ }
  apply (isIntegral_algHom_iff eZ eZ.toRingHom.injective).mp
  change IsIntegral ℤ (e x)
  rw [hx]
  exact hint K hK (e.comp (algebraMap K (SeparableClosure K))) I P hP

end ZInQ.Manuscript.RC.HCMV21

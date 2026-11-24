import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.Reciprocity

/-! Extract the (j)-invariant consequence of the existing Weierstrass
form of Shimura 5.4. The Artin and inverse-lattice identifications in
the second lemma are purely idelic inputs. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 500000

namespace ZInQ.Manuscript.RC.HCMV21

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.Shimura ZInQ.RouteK.Rank5b
open ZInQ.Contrib.TYZGenus.CM (ιC)
open T5Glue NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors

/-- At the trivial modulus the Artin symbol reads the ideal of the finite
components, with no inverse in the class-field symbol. -/
theorem hilbertArtin_of_idele {F : Type} [Field F] [NumberField F]
    (s : IdeleGroup (𝓞 F) F) :
    ideleClassArtinMap F (hilbertClassField F) (s : IdeleClassGroup (𝓞 F) F) =
      hilbertClassArtinEquiv F
        (ClassGroup.mk F (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 F) F s))) := by
  have hs : s ∈ ideleCongrOneSubgroup (Modulus.one F) := by simp
  let I : idealsPrimeTo (Modulus.one F) :=
    ⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 F) F s),
      toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo hs⟩
  have hI : rayClassQuotient (Modulus.one F) (s : IdeleClassGroup (𝓞 F) F) =
      rayClassMk (Modulus.one F) I := rayClassQuotient_mk_of_mem hs
  change _ = hilbertClassArtinEquiv F (ClassGroup.mk F (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
  rw [hilbertClassArtinEquiv_mk, rayClassArtinEquiv_apply, ← hI, rayClassArtinMap_rayClassQuotient]

/-- The existing reciprocity input already implies the Artin formula on
the lattice invariant of the idelic translate. -/
theorem idelic_j_reciprocity_of_shimura (hCM : ShimuraMainCM)
    (m : ℕ) [NeZero m] (hm : Squarefree m)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (hs : ArtinCond m e σ s)
    (I : Set (QNeg m)) (P Q : PeriodPair)
    (hP : (P.lattice : Set ℂ) = kappa m '' I)
    (hQ : (Q.lattice : Set ℂ) = kappa m '' sInvLat m s I)
    (x : hilbertClassField (QNeg m)) (hx : ιC (e x) = P.jLattice) :
    ιC (e (ideleClassArtinMap (QNeg m) (hilbertClassField (QNeg m)) (icl s) x)) =
      Q.jLattice := by
  obtain ⟨μ, hμ, -⟩ := hCM m hm e he σ s hs I P Q hP hQ
  calc
    _ = σ (ιC (e x)) := (hs (hilbertClassField (QNeg m)) x).symm
    _ = Q.jLattice := by rw [hx]; exact hμ.jL

/-- The specialized arithmetic-ideal formula, once the chosen idele
represents the ideal both in the class-field map and on the lattice. -/
theorem ideal_j_reciprocity_of_shimura (hCM : ShimuraMainCM)
    (m : ℕ) [NeZero m] (hm : Squarefree m)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (hs : ArtinCond m e σ s)
    (I : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))
    (a : (Ideal (𝓞 (QNeg m)))⁰)
    (hsIdeal : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s) =
      FractionalIdeal.mk0 (QNeg m) a)
    (hI : sInvLat m s (I : Set (QNeg m)) =
      ((I / ((a : Ideal (𝓞 (QNeg m))) : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))) :
        Set (QNeg m)))
    (P Q : PeriodPair) (hP : (P.lattice : Set ℂ) = kappa m '' (I : Set (QNeg m)))
    (hQ : (Q.lattice : Set ℂ) =
      kappa m '' ((I / ((a : Ideal (𝓞 (QNeg m))) : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))) :
        Set (QNeg m)))
    (x : hilbertClassField (QNeg m)) (hx : ιC (e x) = P.jLattice) :
    ιC (e (hilbertClassArtinEquiv (QNeg m) (ClassGroup.mk0 a) x)) = Q.jLattice := by
  have hA := hilbertArtin_of_idele s
  rw [hsIdeal, ClassGroup.mk_mk0] at hA
  rw [← hA]
  exact idelic_j_reciprocity_of_shimura hCM m hm e he σ s hs (I : Set (QNeg m)) P Q hP
    (hI.symm ▸ hQ) x hx

end ZInQ.Manuscript.RC.HCMV21

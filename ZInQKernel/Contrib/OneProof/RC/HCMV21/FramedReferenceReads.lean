import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal

/-! Plug the actual single-reference torus into the completed-reads
assembly. Tex 9150–9169 and 9273–9279. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open Eichler Adelic
open scoped CategoryTheory.MonObj NumberField nonZeroDivisors

variable {k F : Type} [Field k] [Field F] [NumberField F]
  {A : PkgI3.AbVar k} {a b : ℚ}

/-- A normalized comparison in the geometric frame suffices. The
single-reference unit test and the change to detector coordinates are
automatic. The quotient family and its local generators are inputs. -/
theorem orientedCorrespondence_of_framedReferenceReads
    (R S : Order a b) (j : A.End ≃+* S.ring) (action : 𝓞 F →+* A.End)
    (C : Subgroup (A.Pt k)) (N : ℕ) (hN : N ≠ 0)
    (hC : ∀ x ∈ C, x ^ N = 1) (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C)
    (z : Adelic.FiniteUnits R)
    (hz : ReferenceOrderCoordinates R (levelOrderOfEndOrder S j C N hN hC) z)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) [DecidableEq (IdealLatticeClass (𝓞 F) F)]
    (I : IdealLatticeClass (𝓞 F) F → LPIdeal (levelOrderOfEndOrder S j C N hN hC))
    (h₀ : I (referenceAnalyticClass L) = fromAdelic 1) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hfactors :
      let J := referenceCMAdeles R S j action C N hN hC hact
      ∀ d : (Ideal (𝓞 F))⁰, IsCoprime (d : Ideal (𝓞 F)) m →
        ∃ (s : 𝔸ᶠ[𝓞 F, F]ˣ) (r : Adelic.FiniteUnits R),
          toFractionalIdeal s = FractionalIdeal.mk0 F d ∧
          r ∈ rationalTorusUnits J ∧
          ∀ p : Prime, localRight (levelOrderOfEndOrder S j C N hN hC) p
              ((r * J s⁻¹).val p) =
            localLattice p.val (I (ClassGroup.mk0 d • referenceAnalyticClass L)).val.lattice) :
    let J := referenceCMAdeles R S j action C N hN hC hact
    let U := Adelic.integralUnits R
    let read := geometricReferenceRead z (referenceAnalyticClass L) I
    letI := inverseAdelicOrbitAction J U (read (referenceAnalyticClass L))
      (by simpa only [read, geometricReferenceRead_base] using
        reference_geometry_hunit j action C N hN hC hact z hz)
    ∃ red : IdealLatticeClass (𝓞 F) F → Set.range (torusOrbitMap J U (read (referenceAnalyticClass L))),
      (∀ x, (red x).val = DoubleCoset.mk (rationalTorusUnits J) U
        (geometricReferenceRead z (referenceAnalyticClass L) I x)) ∧
      OrientedCorrespondence (C := ClassGroup (𝓞 F)) red := by
  dsimp only at hfactors ⊢
  let J := referenceCMAdeles R S j action C N hN hC hact
  let read := geometricReferenceRead z (referenceAnalyticClass L) I
  have hbase : read (referenceAnalyticClass L) = z := geometricReferenceRead_base _ _ _
  have hunit : ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ, (read (referenceAnalyticClass L))⁻¹ * J s *
      read (referenceAnalyticClass L) ∈ Adelic.integralUnits R ↔
        s ∈ FiniteAdeleRing.integralUnits (𝓞 F) F := by
    rw [hbase]
    exact reference_geometry_hunit j action C N hN hC hact z hz
  exact orientedCorrespondence_of_completedReferenceReads J read
    (referenceAnalyticClass L) hunit m hm (by
      intro d hd
      obtain ⟨s, r, hs, hr, hl⟩ := hfactors d hd
      refine ⟨s, r, hs, hr, fun p => ?_⟩
      rw [hbase, ← mul_assoc]
      exact (geometricReferenceRead_local hz (referenceAnalyticClass L) I h₀ _ p _).mpr (hl p))

end ZInQ.Manuscript.RC.HCMV21

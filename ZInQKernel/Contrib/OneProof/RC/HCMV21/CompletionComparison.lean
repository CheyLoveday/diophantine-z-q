import ZInQKernel.Contrib.OneProof.RC.HCMV21.InverseOrbit
import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal

/-! Completed right-ideal comparisons at the reference imply the
labelled adelic comparison. Equality of the completed lattices
recovers precisely the ambiguity by right order units. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField nonZeroDivisors

variable {a b : ℚ} {R : Order a b}

/-- Equal local spans determine the actual rational Hom lattice whenever
both rational lattices are full. -/
theorem rightIdeal_eq_fromAdelic_of_completions (I : RightIdeal R) (z : FiniteUnits R)
    (h : ∀ p : Prime, localLattice p.val I.lattice = localRight R p (z.val p)) :
    I = (fromAdelic z).val := by
  apply RightIdeal.ext
  ext x
  rw [mem_fromAdelic, mem_iff_all_local I.full]
  simp only [h]

/-- Clearing the degree multiplies all completions by one rational
torus element. The labelled class still agrees, since the only other
ambiguity is by right order units. -/
theorem torusOrbitMap_eq_of_scaledLocalRight
    {F : Type*} [Field F] [NumberField F]
    (j : 𝔸ᶠ[𝓞 F, F]ˣ →* FiniteUnits R) (z w : FiniteUnits R)
    (s : 𝔸ᶠ[𝓞 F, F]ˣ) (r : FiniteUnits R) (hr : r ∈ rationalTorusUnits j)
    (h : ∀ p : Prime, localRight R p ((r * (j s * z)).val p) = localRight R p (w.val p)) :
    DoubleCoset.mk (rationalTorusUnits j) (Adelic.integralUnits R) w =
      torusOrbitMap j (Adelic.integralUnits R) z s := by
  unfold torusOrbitMap
  apply DoubleCoset.eq.mpr
  have hu : (r * (j s * z))⁻¹ * w ∈ Adelic.integralUnits R :=
    fun p => (localRight_eq_iff p _ _).mp (h p)
  refine ⟨r⁻¹, (rationalTorusUnits j).inv_mem hr, _, (Adelic.integralUnits R).inv_mem hu, ?_⟩
  group

/-- Given the adelic generators of the completed Hom lattices of the
reduced curves, local equality for the individual coprime quotients
puts every generator in the selected orbit and gives the inverse
oriented correspondence there. The reference is the generator of the
actual reduced base curve. -/
theorem orientedCorrespondence_of_completedReferenceReads
    {F : Type*} [Field F] [NumberField F]
    (j : 𝔸ᶠ[𝓞 F, F]ˣ →* FiniteUnits R)
    (read : IdealLatticeClass (𝓞 F) F → FiniteUnits R) (x₀ : IdealLatticeClass (𝓞 F) F)
    (hunit : ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ, (read x₀)⁻¹ * j s * read x₀ ∈ Adelic.integralUnits R ↔
      s ∈ IsDedekindDomain.FiniteAdeleRing.integralUnits (𝓞 F) F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hlocal : ∀ a : (Ideal (𝓞 F))⁰, IsCoprime (a : Ideal (𝓞 F)) m →
      ∃ (s : 𝔸ᶠ[𝓞 F, F]ˣ) (r : FiniteUnits R), toFractionalIdeal s = FractionalIdeal.mk0 F a ∧
        r ∈ rationalTorusUnits j ∧ ∀ p : Prime,
          localRight R p ((r * (j s⁻¹ * read x₀)).val p) =
            localRight R p ((read (ClassGroup.mk0 a • x₀)).val p)) :
    let U := Adelic.integralUnits R
    let z := read x₀
    letI := inverseAdelicOrbitAction j U z hunit
    ∃ red : IdealLatticeClass (𝓞 F) F → Set.range (torusOrbitMap j U z),
      (∀ x, (red x).val = DoubleCoset.mk (rationalTorusUnits j) U (read x)) ∧
        OrientedCorrespondence (C := ClassGroup (𝓞 F)) red := by
  dsimp only
  have horbit (x : IdealLatticeClass (𝓞 F) F) :
      DoubleCoset.mk (rationalTorusUnits j) (Adelic.integralUnits R) (read x) ∈
        Set.range (torusOrbitMap j (Adelic.integralUnits R) (read x₀)) := by
    obtain ⟨c, rfl⟩ := (analytic_orbit_bijective x₀).surjective x
    obtain ⟨a, ha, rfl⟩ := exists_integral_class_prime_to m hm c
    obtain ⟨s, r, _, hr, hs⟩ := hlocal a ha
    exact ⟨s⁻¹, (torusOrbitMap_eq_of_scaledLocalRight j _ _ _ r hr hs).symm⟩
  let red : IdealLatticeClass (𝓞 F) F →
      Set.range (torusOrbitMap j (Adelic.integralUnits R) (read x₀)) :=
    fun x => ⟨DoubleCoset.mk (rationalTorusUnits j) (Adelic.integralUnits R) (read x), horbit x⟩
  refine ⟨red, fun _ => rfl, ?_⟩
  apply orientedCorrespondence_of_inverseReferenceReads j _ (read x₀) hunit red x₀ ?_ m hm
  · intro a ha
    obtain ⟨s, r, hs, hr, hsp⟩ := hlocal a ha
    exact ⟨s, hs, torusOrbitMap_eq_of_scaledLocalRight j _ _ _ r hr hsp⟩
  · simp [red, torusOrbitMap]

end ZInQ.Manuscript.RC.HCMV21

import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Grouped
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.BasedFiber

/-! The placewise comparison needed for tex 9161–9166 and its passage
to the restricted product. -/

noncomputable section

set_option maxHeartbeats 800000

open IsDedekindDomain
open scoped NumberField RestrictedProduct

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler Adelic O7Actual O7Orbits

section PrimeBlocks

variable (F : Type*) [Field F] [NumberField F]

/-- The prime under a finite place, in the index convention of the
quaternion restricted product. -/
def primeBelow (v : HeightOneSpectrum (𝓞 F)) : Prime :=
  rationalPrimeEquiv.symm (rationalPrimeUnder F v)

private theorem primeBelow_finite (p : Prime) : (primeBelow F ⁻¹' ({p} : Set Prime)).Finite := by
  refine (rationalPrimeUnder_finite F (rationalPrimeEquiv p)).subset ?_
  intro v hv
  change primeBelow F v = p at hv
  change rationalPrimeUnder F v = rationalPrimeEquiv p
  exact (rationalPrimeEquiv.apply_symm_apply _).symm.trans (congrArg rationalPrimeEquiv hv)

abbrev PrimeBlock (p : Prime) :=
  ∀ v : {v : HeightOneSpectrum (𝓞 F) // primeBelow F v = p}, (v.val.adicCompletion F)ˣ

/-- Integral units in all of the factors over one rational prime. -/
def primeBlockIntegral (p : Prime) : Submonoid (PrimeBlock F p) :=
  blockIntegral (primeBelow F) (fun v => (v.adicCompletion F)ˣ)
    (fun v => (Submonoid.ofClass (v.adicCompletionIntegers F)).units.toSubmonoid) p

abbrev PrimeBlocks :=
  Πʳ p : Prime, [PrimeBlock F p, primeBlockIntegral F p]

/-- The regrouping in the quaternion order's prime convention. -/
def idelePrimeBlocks : (FiniteAdeleRing (𝓞 F) F)ˣ ≃* PrimeBlocks F :=
  (RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)).trans
    (regroup (primeBelow F) _ _ (primeBelow_finite F))

private theorem idelePrimeBlocks_apply (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (p : Prime)
    (v : {v : HeightOneSpectrum (𝓞 F) // primeBelow F v = p}) :
    ((idelePrimeBlocks F a p v : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) =
      a.val v.val := rfl

set_option maxHeartbeats 800000 in
private theorem idele_kernel_primeBlocks (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    a ∈ (ideleToIdeal (R := 𝓞 F) (K := F)).ker ↔
      ∀ p : Prime, idelePrimeBlocks F a p ∈ primeBlockIntegral F p := by
  rw [mem_ker_ideleToIdeal]
  constructor
  · intro h p v
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [idelePrimeBlocks_apply]
    exact h v.val
  · intro h v
    let w : {w : HeightOneSpectrum (𝓞 F) // primeBelow F w = primeBelow F v} := ⟨v, rfl⟩
    have hv : idelePrimeBlocks F a (primeBelow F v) w ∈ (v.adicCompletionIntegers F).units :=
      h (primeBelow F v) w
    have he := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hv
    rw [idelePrimeBlocks_apply] at he
    exact he

end PrimeBlocks

section Comparison

variable {a b : ℚ} {F : Type*} [Field F] [NumberField F]

/-- Tex 9161–9165: the open local arithmetic comparison. The chart
identifies only local units, carries the diagonal field units to their
embedded values, and tests their completed integral order. -/
structure LocalTorusChart (R : Order a b) (ι : F →ₐ[ℚ] B a b)
    (x₀ : (B a b)ˣ) (α : B a b) (p : Prime) where
  units : PrimeBlock F p ≃* Subgroup.centralizer
    ({Units.map (toLocal p.val).toMonoidHom x₀} : Set (Bp p.val a b)ˣ)
  diagonal_eq : ∀ k : Fˣ,
    (units (idelePrimeBlocks F (FiniteAdeleRing.unitEmbedding (𝓞 F) F k) p)).val =
      Units.map (toLocal p.val).toMonoidHom (Units.map ι.toMonoidHom k)
  integral_iff : ∀ z : (Bp p.val a b)ˣ,
    unitConjRing z⁻¹ (toLocal p.val α) ∈ R.completion p.val →
      ∀ u : PrimeBlock F p, z⁻¹ * (units u).val * z ∈ localUnits R p ↔
        u ∈ primeBlockIntegral F p

private theorem conjugate_mem_iff {G : Type*} [Group G] (U : Subgroup G) {z : G} (hz : z ∈ U)
    (g : G) : z⁻¹ * g * z ∈ U ↔ g ∈ U := by
  constructor
  · intro h
    have he : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
    rw [← he]
    exact U.mul_mem (U.mul_mem hz h) (U.inv_mem hz)
  · intro h
    exact U.mul_mem (U.mul_mem (U.inv_mem hz) h) hz

variable (R : Order a b) (ι : F →ₐ[ℚ] B a b) (x₀ : (B a b)ˣ) (α : B a b)
  (E : ∀ p, LocalTorusChart R ι x₀ α p)

private def blockToLocalFamily (c : PrimeBlocks F) : LocalFamily a b :=
  fun p => ((E p).units (c p)).val

private def localToBlockFamily (g : adelicCentralizer R (diagonal R x₀).val) (p : Prime) :
    PrimeBlock F p :=
  (E p).units.symm ⟨g.val.val p, Subgroup.mem_centralizer_singleton_iff.mpr (g.prop p)⟩

set_option maxHeartbeats 1200000 in
/-- The local comparison gives the adelic centralizer. Restrictedness
can be read relative to any admissible representative: the two tests
agree outside the finite set where that representative is not integral. -/
def blocksCentralizerEquiv (z : FiniteUnits R) (hz : AdelicAdmissible α z) :
    PrimeBlocks F ≃* adelicCentralizer R (diagonal R x₀).val where
  toFun c := ⟨⟨blockToLocalFamily R ι x₀ α E c, by
    have hf : {p | c p ∉ primeBlockIntegral F p}.Finite :=
      Filter.eventually_cofinite.mp c.prop
    refine (hf.union z.prop).subset ?_
    intro p hp
    by_contra hn
    have h₁ : c p ∈ primeBlockIntegral F p := by
      by_contra h
      exact hn (Or.inl h)
    have h₂ : z.val p ∈ localUnits R p := by
      by_contra h
      exact hn (Or.inr h)
    exact hp ((conjugate_mem_iff _ h₂ _).mp (((E p).integral_iff _ (hz p) _).mpr h₁))⟩,
      fun p => Subgroup.mem_centralizer_singleton_iff.mp ((E p).units (c p)).prop⟩
  invFun g := ⟨localToBlockFamily R ι x₀ α E g, by
    rw [Filter.eventually_cofinite]
    refine (g.val.prop.union z.prop).subset ?_
    intro p hp
    by_contra hn
    have h₁ : g.val.val p ∈ localUnits R p := by
      by_contra h
      exact hn (Or.inl h)
    have h₂ : z.val p ∈ localUnits R p := by
      by_contra h
      exact hn (Or.inr h)
    apply hp
    apply ((E p).integral_iff _ (hz p) _).mp
    change (z.val p)⁻¹ * (((E p).units ((E p).units.symm
      ⟨g.val.val p, _⟩)).val) * z.val p ∈ localUnits R p
    rw [MulEquiv.apply_symm_apply]
    exact (conjugate_mem_iff _ h₂ _).mpr h₁⟩
  left_inv c := by
    apply Subtype.ext
    funext p
    exact (E p).units.symm_apply_apply (c p)
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact congrArg Subtype.val ((E p).units.apply_symm_apply ⟨g.val.val p, _⟩)
  map_mul' c d := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact congrArg Subtype.val ((E p).units.map_mul (c p) (d p))

/-- Compose the placewise comparison with the regrouping of finite ideles. -/
def ideleCentralizerEquiv (z : FiniteUnits R) (hz : AdelicAdmissible α z) :
    (FiniteAdeleRing (𝓞 F) F)ˣ ≃* adelicCentralizer R (diagonal R x₀).val :=
  (idelePrimeBlocks F).trans (blocksCentralizerEquiv R ι x₀ α E z hz)

theorem ideleCentralizerEquiv_diagonal (z : FiniteUnits R) (hz : AdelicAdmissible α z) (k : Fˣ) :
    (ideleCentralizerEquiv R ι x₀ α E z hz (FiniteAdeleRing.unitEmbedding (𝓞 F) F k)).val =
      diagonal R (Units.map ι.toMonoidHom k) :=
  Subtype.ext (funext fun p => (E p).diagonal_eq k)

theorem ideleCentralizerEquiv_integral (z : FiniteUnits R) (hz : AdelicAdmissible α z)
    (w : FiniteUnits R) (hw : AdelicAdmissible α w) (c : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    w⁻¹ * (ideleCentralizerEquiv R ι x₀ α E z hz c).val * w ∈ integralUnits R ↔
      c ∈ (ideleToIdeal (R := 𝓞 F) (K := F)).ker := by
  rw [idele_kernel_primeBlocks]
  exact forall_congr' fun p => (E p).integral_iff _ (hw p) (idelePrimeBlocks F c p)

theorem ideleCentralizerEquiv_rational (z : FiniteUnits R) (hz : AdelicAdmissible α z)
    {d : ℤ} (Q : QuadraticBasis F d) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : x₀.val.re = 0) (hroot : x₀.val = ι (Q.model QuadraticAlgebra.omega))
    (c : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (ideleCentralizerEquiv R ι x₀ α E z hz c).val ∈ diagonalCentralizer R x₀ ↔
      c ∈ (FiniteAdeleRing.unitEmbedding (𝓞 F) F).range := by
  have hR := rationalCentralizer_eq_range ha hb Q ι x₀ hx hroot
  constructor
  · rintro ⟨v, hv, he⟩
    rw [hR] at hv
    obtain ⟨k, rfl⟩ := hv
    refine ⟨k, (ideleCentralizerEquiv R ι x₀ α E z hz).injective (Subtype.ext ?_)⟩
    exact (ideleCentralizerEquiv_diagonal R ι x₀ α E z hz k).trans he
  · rintro ⟨k, rfl⟩
    rw [ideleCentralizerEquiv_diagonal]
    exact ⟨Units.map ι.toMonoidHom k, hR.symm ▸ ⟨k, rfl⟩, rfl⟩

end Comparison

end ZInQ.Manuscript.RC.PicardFibers

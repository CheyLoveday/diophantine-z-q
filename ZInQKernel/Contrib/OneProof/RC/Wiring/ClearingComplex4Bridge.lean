import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.RelCore

/-!
# Theorem 5.3, Lane RC0 round 4: what remains of the coordinate input after batch 3's Bridge47

Batch 3's `correctedIsEta_of_triangles` (CoordLink, Bridge47) proves `CorrectedIsEta` outright for
a universal correction `η_Λ ∈ Λ[G]` whose sign evaluations are units, with the relaxed coordinate
pinned to `urelK = η_x⁻¹ ũ_x` (read off any representation `ũ = g₀/2^{e₀}`). So the only content
left in `OrigCoordLink` is batch 3's `RelIsKM` at that pinned coordinate:

* `origCoordLink_of_relIsKMG_urelK` (PROVED): from a representation of `ũ` (which height-one
  regularity provides), `η_Λ` with unit sign evaluations and `RelIsKMG M (urelK …) z λ`,
  `OrigCoordLink D F M z λ (φO η_Λ)` holds.

* `integralCore_coord_ne_zero` (PROVED): an integral two-term core with exact augmentation never
  has class-functional coordinate `0`. Consequence for batch 3's further reduction of `RelIsKM`
  (`relIsKM_of_core`, RelCore), which takes such a core at EVERY address with coordinate the
  relaxed coordinate `η_x⁻¹ ũ_x`: its hypotheses fail at any address with `ũ_x = 0`, in particular
  at a generically acyclic constituent (the text's convention `u = 0`, tex 3889–3890, and the
  acyclic pattern, tex 5612–5615). That route therefore applies only to families with `ũ_x ≠ 0`
  at every address (`uTilde_ne_zero_of_core`, PROVED); `OrigCoordLink` and `RelIsKMG` hold at
  acyclic constituents (both sides vanish), so they are not replaced by it here.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink (urelK correctedIsEta_of_triangles IntegralCore ιQ ψO
  ιQ_injective)
open ZInQ.Contrib.CloudB3RC53.Torsion (twoTerm FourCx.aug)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- **`OrigCoordLink` from `RelIsKM` at the pinned relaxed coordinate** (PROVED; batch 3's
`correctedIsEta_of_triangles` discharges `CorrectedIsEta`). -/
theorem origCoordLink_of_relIsKMG_urelK {ℓ : ℕ} (D : RCData ℓ) (F : Family) {K : Type} [Field K]
    [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
    [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {dK hK cE tK : ℕ}
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep D F e₀ g₀)
    (hrel : RelIsKMG M (urelK ηΛ hunit e₀ g₀) z lam hz hlam) :
    OrigCoordLink D F M z lam hz hlam (φO F.b ηΛ) :=
  origCoordLink_of_eta_rel (correctedIsEta_of_triangles D F ηΛ hunit e₀ g₀ h₀) hrel

/-- **An integral two-term core with exact augmentation has nonzero coordinate** (PROVED): exactness
forces the class and the functional to be nonzero, and `z ⊗ w = 0 · adj D = 0` would force one of
them to vanish (`ℚ₂[[t]]` is a domain and `Λ → ℚ₂[[t]]` is injective). -/
theorem integralCore_coord_ne_zero (c : IntegralCore) :
    ¬ Central.IsClassFunctionalCoord (c.D.map ιQ) (ιQ ∘ c.zc) (ιQ ∘ c.wc) 0 := by
  intro h
  obtain ⟨h0, -, -, h3⟩ := c.exact
  have h10 : (1 : FractionRing OO) ≠ 0 := by
    have := (map_ne_zero_iff (algebraMap OO (FractionRing OO))
      (IsFractionRing.injective OO (FractionRing OO))).mpr (one_ne_zero (α := OO))
    rwa [map_one] at this
  have hz : ∃ i, ψO (c.zc i) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ i, ψO (c.zc i) = 0 := fun i => not_not.mp (not_exists.mp hcon i)
    have hx := h0 (Pi.single (Sum.inr ()) 1) (by
      rw [Matrix.mulVec_single_one]
      funext i
      exact hcon' i)
    apply h10
    have := congrFun hx (Sum.inr ())
    rwa [Pi.single_eq_same, Pi.zero_apply] at this
  have hw : ∃ j, ψO (c.wc j) ≠ 0 := by
    obtain ⟨x, hx⟩ := h3 (Pi.single (Sum.inr ()) 1)
    by_contra hcon
    have hcon' : ∀ j, ψO (c.wc j) = 0 := fun j => not_not.mp (not_exists.mp hcon j)
    have h1 := congrFun hx (Sum.inr ())
    rw [Pi.single_eq_same] at h1
    apply h10
    rw [← h1]
    change ∑ j, ψO (c.wc j) * x j = 0
    simp only [hcon', zero_mul, Finset.sum_const_zero]
  obtain ⟨i, hi⟩ := hz
  obtain ⟨j, hj⟩ := hw
  have hij := congrFun (congrFun h i) j
  simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, zero_smul] at hij
  rcases mul_eq_zero.mp hij with h1 | h1
  · exact hi (by rw [(map_eq_zero_iff ιQ ιQ_injective).mp h1, map_zero])
  · exact hj (by rw [(map_eq_zero_iff ιQ ιQ_injective).mp h1, map_zero])

/-- **Batch 3's core route forces `ũ_x ≠ 0`** (PROVED): at an address where the (4.7) data `T`
(`hutilde : ũ_x = χ(η) u_rel`, `χ(η)` a unit, as `hcompat` and `hunit` give) and an integral core
with exact augmentation carrying the coordinate `u_rel` (the hypotheses `hcore` of batch 3's
`relIsKM_of_core`) are given, the corrected coordinate is nonzero. -/
theorem uTilde_ne_zero_of_core {ℓ : ℕ} (D : RCData ℓ) (F : Family) (x : Addr F.b)
    (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN D F x)
    (hχ : IsUnit (T.chi (Central.eta T.Q T.v T.g))) (c : IntegralCore)
    (hcore : Central.IsClassFunctionalCoord (c.D.map ιQ) (ιQ ∘ c.zc) (ιQ ∘ c.wc) T.urel) :
    D.uTilde F x ≠ 0 := by
  intro h0
  have hut := T.hutilde
  rw [h0] at hut
  have hu : T.urel = 0 := hχ.mul_right_eq_zero.mp hut.symm
  rw [hu] at hcore
  exact integralCore_coord_ne_zero c hcore

end ZInQ.Manuscript.RC.Wiring

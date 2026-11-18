import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.NonVacuity

/-!
# Theorem 5.3, Lane RC0 round 4: consistency of the coordinate input of `ClearingInputsG`

The coordinate identification of `ClearingInputsG` (`OrigCoordLink`, and batch 3's pair
`CorrectedIsEta`, `RelIsKMG` that implies it) adds no obstruction beyond the genuine identification
`Identification2G` itself (non-vacuity, as for batch 3's `coordLinkInputs_example`, now for every
genuine identification):

* `correctedIsEta_of_zero`: for interface data whose corrected coordinates vanish on `F`,
  `CorrectedIsEta D F η 0` holds for every `η`;
* `relIsKMG_zero`: for EVERY `M : Identification2G …`, the zero class and functional satisfy
  `RelIsKMG M 0 0 0` (the Knudsen–Mumford coordinate of the zero class vanishes);
* `origCoordLink_zero`: hence `OrigCoordLink D F M 0 0 _ _ η` for such data, every `M` and `η`;
* `clearingInputsG_of_zero`: for such data, `ClearingInputsG D` follows from the existence of
  genuine identifications alone.

The instance is degenerate (`ũ = 0`, zero class); it shows joint satisfiability of the coordinate
input with any genuine identification, not that it holds for the genuine coordinate. A witness of
`Identification2G` with a nonempty set of new places needs genuine local cochains quasi-isomorphic
to a nonzero tame model (local Galois cohomology), which no lane provides (as for batch 3's non-vacuity examples).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink (CorrectedIsEta hlamev kmCoord_congr kmCoord_zero_class
  uK_eq_zero_of_rep_zero)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- **`ũ = η u_rel` for vanishing corrected coordinates** (`u_rel = 0`, any `η`; PROVED). -/
theorem correctedIsEta_of_zero {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (h0 : ∀ x, D.uTilde F x = 0) (η : MonoidAlgebra OO (SignGroup F.b)) :
    CorrectedIsEta D F η 0 := fun e g hrep x => by
  rw [uK_eq_zero_of_rep_zero D F h0 e g hrep x]
  simp

/-- **The zero class and functional satisfy `RelIsKMG` for every genuine identification**
(`u_rel = 0`; PROVED: the Knudsen–Mumford coordinate of the zero class vanishes). -/
theorem relIsKMG_zero {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
    {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    {b dK hK cE tK : ℕ} (M : Identification2G K S S' hS b dK hK cE tK) :
    RelIsKMG M 0 0 0 (mulVec_zero _) (zero_vecMul _) := fun x _ => by
  have hz' : (evK (sgnChar x) ∘
      (0 : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))) = 0 := by
    funext i; simp
  exact ((kmCoord_congr rfl hz' rfl _ _ (mulVec_zero _) (hlamev (zero_vecMul _) x) _).trans
    (kmCoord_zero_class _ _ _ _ _)).symm

/-- **`OrigCoordLink` for vanishing corrected coordinates** with the zero class and functional, for
every genuine identification and every `η` (PROVED). -/
theorem origCoordLink_zero {ℓ : ℕ} (D : RCData ℓ) (F : Family) (h0 : ∀ x, D.uTilde F x = 0)
    {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
    [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {dK hK cE tK : ℕ}
    (M : Identification2G K S S' hS F.b dK hK cE tK) (η : MonoidAlgebra OO (SignGroup F.b)) :
    OrigCoordLink D F M 0 0 (mulVec_zero _) (zero_vecMul _) η :=
  origCoordLink_of_eta_rel (correctedIsEta_of_zero D F h0 η) (relIsKMG_zero M)

/-- **For vanishing corrected coordinates, `ClearingInputsG` is the existence of genuine
identifications** (PROVED; the coordinate input holds with `z = 0`, `λ = 0`, `η = 1`). -/
theorem clearingInputsG_of_zero {ℓ : ℕ} (D : RCData ℓ) (h0 : ∀ F x, D.uTilde F x = 0)
    (h : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
      ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
        ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
          (_ : DecidableEq (NewPlaces K S S')),
          Nonempty (Identification2G K S S' hS F.b dK hK cE tK)) :
    ClearingInputsG D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  refine ⟨K, inferInstance, inferInstance, dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, ⟨M⟩⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, inferInstance, inferInstance, M, 0, 0, mulVec_zero _, zero_vecMul _, 1,
    origCoordLink_zero D F (h0 F) M 1⟩

end ZInQ.Manuscript.RC.Wiring

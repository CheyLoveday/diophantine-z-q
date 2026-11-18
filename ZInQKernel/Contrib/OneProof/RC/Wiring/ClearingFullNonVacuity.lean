import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionNonVacuity
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingFull
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4NonVacuity

/-!
# Theorem 5.3, Lane RC0: consistency of the coordinate input of `ClearingInputsG3`

The leaf `PostLeaves.clearing_model` is `ClearingInputsG3Q` (`ClearingFull.lean`): at every final
family a full-condition identification (the triangle (5.6), tex 5234–5238, 5398–5403) with its new
places the primes of the family (`Identification3Q`), and one coordinate identification
`OrigCoordLink3`. The coordinate input adds no obstruction
beyond the identification itself:

* `origCoordLink3_zero`: for interface data whose corrected coordinates vanish on `F`, the zero
  class and functional satisfy `OrigCoordLink3` for every `Identification3` and every `η`;
* `clearingInputsG3_of_zero`, `clearingInputsG3Q_of_zero`: for such data, `ClearingInputsG3 D`
  (resp. the leaf `ClearingInputsG3Q D`) follows from the existence of full-condition
  identifications (resp. with the new places the primes of the family) alone.

The instance is degenerate (`ũ = 0`, zero class); it shows joint satisfiability of the coordinate
input with any full-condition identification, not that it holds for the genuine coordinate. The
cancellation core of `Identification3` is inhabited for every finite set of new places, the empty
one included (the RC53 group's `fullCore_nonempty_empty`, `fullCore_nonempty_unit`); a witness of
the whole `Identification3` needs its genuine continuous-cochain comparisons (the family Selmer
complex, the full-condition and unramified support complexes, the tame models), which no lane
provides.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink (kmCoord_congr kmCoord_zero_class uK_eq_zero_of_rep_zero)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- **`OrigCoordLink3` for vanishing corrected coordinates** with the zero class and functional,
for every full-condition identification and every `η` (PROVED: the corrected coordinate vanishes,
and so does the Knudsen–Mumford coordinate of the zero class). -/
theorem origCoordLink3_zero {ℓ : ℕ} (D : RCData ℓ) (F : Family) (h0 : ∀ x, D.uTilde F x = 0)
    {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
    [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')] {dK hK cE tK : ℕ}
    (M : Identification3 K S S' hS F.b dK hK cE tK) (η : MonoidAlgebra OO (SignGroup F.b)) :
    OrigCoordLink3 D F M 0 0 (mulVec_zero _) (zero_vecMul _) η := by
  intro e g hrep x _
  rw [uK_eq_zero_of_rep_zero D F h0 e g hrep x]
  have hz' : (evK (sgnChar x) ∘
      (0 : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))) =
      0 := by
    funext i; simp
  refine (mul_eq_zero_of_right _ ?_).symm
  exact (kmCoord_congr rfl hz' rfl _ _ (mulVec_zero _) (hlamev3 (zero_vecMul _) x) _).trans
    (kmCoord_zero_class _ _ _ _ _)

/-- **For vanishing corrected coordinates, `ClearingInputsG3` is the existence of full-condition
identifications** (PROVED; the coordinate input holds with `z = 0`, `λ = 0`, `η = 1`). -/
theorem clearingInputsG3_of_zero {ℓ : ℕ} (D : RCData ℓ) (h0 : ∀ F x, D.uTilde F x = 0)
    (h : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
      ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
        ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
          (_ : DecidableEq (NewPlaces K S S')),
          Nonempty (Identification3 K S S' hS F.b dK hK cE tK)) :
    ClearingInputsG3 D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  refine ⟨K, inferInstance, inferInstance, dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, ⟨M⟩⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, inferInstance, inferInstance, M, 0, 0, mulVec_zero _, zero_vecMul _, 1,
    origCoordLink3_zero D F (h0 F) M 1⟩

/-- **For vanishing corrected coordinates, the leaf `ClearingInputsG3Q` is the existence of
full-condition identifications with the new places the primes of the family** (PROVED; the
coordinate input holds with `z = 0`, `λ = 0`, `η = 1`). -/
theorem clearingInputsG3Q_of_zero {ℓ : ℕ} (D : RCData ℓ) (h0 : ∀ F x, D.uTilde F x = 0)
    (h : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
      ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
        ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
          (_ : DecidableEq (NewPlaces K S S')),
          Nonempty (Identification3Q K S S' hS F dK hK cE tK)) :
    ClearingInputsG3Q D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  refine ⟨K, inferInstance, inferInstance, dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, ⟨M⟩⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, inferInstance, inferInstance, M, 0, 0, mulVec_zero _, zero_vecMul _, 1,
    origCoordLink3_zero D F (h0 F) M.toIdentification3 1⟩

end ZInQ.Manuscript.RC.Wiring

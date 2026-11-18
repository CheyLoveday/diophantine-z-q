import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionFamily

/-!
# Theorem 5.3, Lane RC0: the clearing leaf over the full-condition triangle (5.6)

Proposition `ex:arith-clearing`, (5.9) (tex 5355–5645), over the triangle (5.6) (tex 5234–5238,
5398–5403). The leaf `PostLeaves.clearing_model` is `ClearingInputsG3Q`: the RC53 group's
`ClearingInputsG3` (`CloudB3RC53/ClearingComplex/FullConditionE1a.lean`) with its full-condition
identification in the form `Identification3Q` (`FullConditionFamily.lean`), whose new places are
the primes of the family: `eQ : NewPlaces K S S' ≃ F.Q`, each new place over its prime, and the
residue cardinality of its tame model equal to that prime.

* `ClearingInputsG3Q` (the leaf);
* `clearingInputsG3_of_G3Q` (PROVED): the RC53 group's `ClearingInputsG3` from it;
* `clearingTarget_of_G3Q` (PROVED): `RCSteps.clearing` from it and height-one regularity, through
  the RC53 group's `clearingTarget_of_G3` (`κ = det(B)⁻¹`, E1a, lane RC7's (5.9)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- **The inputs of (5.9) over the full-condition triangle (5.6), with the new places the primes of
the family** (tex 5234–5238, 5355–5645, 3470–3499, 3877–3892): a number field `K` and the
constants, and at every final family `F` a full-condition identification `Identification3Q`
(GLUE: the model with the new singular summands in degrees one and two, the family conditions full
at the new places, the comparisons with the genuine family Selmer complex and, modulo `ρ`, with the
genuine full-condition and unramified support complexes, the tame models; the new places
identified with `F.Q`), the actual cycle, the closed functional and the correction `η` over `𝒪[G]`
(data), and the coordinate identification `OrigCoordLink3` (GLUE). -/
def ClearingInputsG3Q {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification3Q K S S' hS F dK hK cE tK)
        (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
        (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
        (η : MonoidAlgebra OO (SignGroup F.b)),
        OrigCoordLink3 D F M.toIdentification3 z lam hz hlam η

/-- **The RC53 group's `ClearingInputsG3` from the leaf** (PROVED: forget the identification of the
new places with `F.Q`). -/
theorem clearingInputsG3_of_G3Q {ℓ : ℕ} {D : RCData ℓ} (h : ClearingInputsG3Q D) :
    ClearingInputsG3 D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  refine ⟨K, inferInstance, inferInstance, dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, M, z, lam, hz, hlam, η, hlink⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, inferInstance, inferInstance, M.toIdentification3, z, lam, hz, hlam, η, hlink⟩

/-- **`RCSteps.clearing` from the leaf and height-one regularity** (PROVED: the RC53 group's
`clearingTarget_of_G3`). -/
theorem clearingTarget_of_G3Q {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h : ClearingInputsG3Q D) : ClearingTarget D :=
  clearingTarget_of_G3 D h1 (clearingInputsG3_of_G3Q h)

end ZInQ.Manuscript.RC.Wiring

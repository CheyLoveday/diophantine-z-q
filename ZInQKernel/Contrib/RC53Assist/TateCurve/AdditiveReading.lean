import ZInQKernel.Contrib.RC53Assist.TateCurve.InertiaLinearAlgebra
import ZInQKernel.Contrib.RC53Assist.TateCurve.WeilInertia

/-!
# Additive reduction has zero inertia coinvariants

The reduction to literature uses the semistable-reduction criterion rather
than assuming the additive coinvariant conclusion. Grothendieck's criterion
says that inertia is unipotent exactly at semistable reduction. For elliptic
curves semistable means good or multiplicative reduction.

In dimension two, determinant one and a singular inertia defect force that
defect to have square zero. Therefore any nonunipotent inertia element has
an invertible defect. At an additive prime such an element exists by the
criterion, so the augmentation subspace is the whole Tate space.

The determinant-one statement is separately derived from Silverman III.8.1(d)
and the proved prime-to-`p` root-of-unity argument. No vanishing assertion is
used as an input. Both printed inputs remain theorem parameters, not axioms.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **PRINT INPUT, ELLIPTIC-CURVE SPECIALIZATION**: an elliptic curve has
semistable reduction if and only if inertia acts unipotently on its rational
`ℓ`-adic Tate module, for `ℓ` different from the residue characteristic.

Locator: Silverberg and Zarhin, *Reduction of Abelian Varieties*,
arXiv:alg-geom/9602014v2 (29 August 1998), Theorem 4.1(i)-(ii), PDF page 4;
text body read. Its proof cites SGA 7 I, Exposé IX, Proposition 3.5 and
Corollaire 3.8; those original pages have not been checked. This is the
elliptic-curve specialization of that literal criterion. For elliptic
curves semistable means good or multiplicative reduction, and unipotent
means `ρ(i)-1` is nilpotent for every inertia element. The representation
is the actual rational Tate representation, not a supplied replacement. This source is not
one of the manuscript's bibliography entries (the manuscript cites a different
Silverberg-Zarhin paper, Theorem 3.5). -/
def GrothendieckSemistableReductionPrint : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime), p ≠ ℓ → ∀ D : LocalArithmeticFrobenius p,
    (GoodReductionAt E (primeIdealQ p hp) ∨
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
          ((primeIdealQ p hp).adicCompletionIntegers ℚ)) ↔
      ∀ i ∈ inertiaAt D, IsNilpotent (rationalTateRep E ℓ i -
        (1 : Module.End ℚ_[ℓ] (rationalTate E ℓ)))

end ZInQ.Contrib.RC53Assist.TateCurve

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open ZInQ.Contrib.RC53Assist.TateCurve
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **PROVED FROM TWO PRINTED RESULTS**: the exact retained additive
coinvariant proposition. The inputs are the semistable-reduction criterion
(SGA 7 I, IX, Proposition 3.5 and Corollaire 3.8; Silverberg-Zarhin,
Theorem 4.1) and Galois equivariance of the Weil pairing (Silverman,
AEC, III.8.1(d)); neither input states a coinvariant conclusion.
Locators: `augmentation_eq_top_of_nonunipotent` and
`rational_tate_det_inertia`. -/
theorem additiveReductionCoinvariantsVanish_of_prints
    (hS : GrothendieckSemistableReductionPrint)
    (hW : SilvermanIII81GaloisWeilPairingPrint) :
    AdditiveReductionCoinvariantsVanish := by
  classical
  intro E _ ℓ _ p hp hpℓ hgood hmult D
  have hnot : ¬∀ i ∈ inertiaAt D,
      IsNilpotent (rationalTateRep E ℓ i -
        (1 : Module.End ℚ_[ℓ] (rationalTate E ℓ))) := by
    intro h
    exact (hS E ℓ p hp hpℓ D).mpr h |>.elim hgood hmult
  push Not at hnot
  obtain ⟨i, hi, hni⟩ := hnot
  exact augmentation_eq_top_of_nonunipotent (rationalTateRep E ℓ) (inertiaAt D)
    (rationalTateBasis E ℓ) i hi
    (rational_tate_det_inertia hW E ℓ p hp hpℓ D i hi) hni

/-- **PROVED FROM TWO PRINTED RESULTS**: the corrected local polynomial
at an additive prime is the classical constant factor one.
Locator: `additiveReductionCoinvariantsVanish_of_prints` and the retained
additive-polynomial computation. -/
theorem localTatePolynomialCoinv_of_additive_prints
    (hS : GrothendieckSemistableReductionPrint)
    (hW : SilvermanIII81GaloisWeilPairingPrint)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hgood : ¬GoodReductionAt E (primeIdealQ p hp))
    (hmult : ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ))
    (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) :=
  localTatePolynomialCoinv_of_additive E ℓ p hp hgood hmult D
    (additiveReductionCoinvariantsVanish_of_prints hS hW E ℓ p hp hpℓ hgood hmult D)

end ZInQ.Contrib.RC53Assist.GlobalTrace

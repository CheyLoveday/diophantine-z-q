import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.CoordParam

/-!
# Theorem 5.3, Lane RC0 round 3: determinant clearing (5.9) from the remaining complex

Batch 3's ClearingComplex builds this lane's `ClearingModel` (`clearingModel_of_coord`) from:
* one identification of the remaining complex (`SelmerIdentification`; ELLIOT, its Selmer clause is
  vacuous: `G := D` meets it): a block-form complex over `𝒪[G]` whose augmentation is the old complex
  over `Λ`, with sign-evaluated differentials given by one new-local Schur family, the (5.7) counts
  of its central complex, and a quasi-isomorphism to a Selmer complex (tex 5355–5392, 5437–5454,
  5509–5519, 5537–5538); the Smith model, the entry poles and the budget are PROVED from it, and the
  generic patterns (E2) are PROVED;
* the coordinate link (E1a, ELLIOT; with E1b it is Elliot's E1) for every representation of `ũ`,
  and Elliot's determinant computation (E1b, ELLIOT) for the genuine generic patterns.

None of these objects is tied to `E`, `K`, the graph primes of the family or a Selmer complex, so
they do not constrain the genuine objects: `ClearingInputsCx` follows from a bare common-denominator
statement (lane RV2's review probe `clearingInputsCx_of_commonDenominator`), and as a leaf it is
Proposition `ex:limits-fixed-field-clearing` in the form of its proof (ELLIOT, conclusion-shaped).

`clearingTarget_of_complex` (PROVED) gives `RCSteps.clearing` from these inputs (`ClearingInputsCx`)
and height-one regularity.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup ScalarData)

/-- **The inputs of (5.9) from the remaining complex** (tex 5207–5645): constants
`d_K, h_K, c_E, t_K` fixed before the family (tex 5641–5643) and, at every final family, the
identification of the remaining complex with its Selmer comparison (ELLIOT; the Selmer clause is
vacuous), scalar data, the elements `κ, ε, η` of `𝒪[G]`, a coordinate `c`, Elliot's computation
(E1b, tex 5586–5617; with `c` a free parameter it only defines `c`) and the link (E1a, ELLIOT, tex
5605–5611; together with E1b it is Elliot's E1) for every representation `ũ_x = g_x/2^{e_x}`.
Conclusion-shaped (see the module docstring). Owners: RC7, batch 3 ClearingComplex / RankCounts. -/
def ClearingInputsCx {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
      (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
      CoordComputation I.B sd ε c I.D.RankOnePattern I.D.AcyclicPattern ∧
      ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g → CoordLink I.B κ η 0 e g c

/-- **`RCSteps.clearing` from the remaining complex** (PROVED: batch 3's `clearingModel_of_coord`
and lane RC7's `clearing_nodes` through `clearingTarget_of_model`). -/
theorem clearingTarget_of_complex {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h : ClearingInputsCx D) : ClearingTarget D :=
  clearingTarget_of_model D h1 (clearingModel_of_coord D h)

end ZInQ.Manuscript.RC.Wiring

# CCL consumer inventory at the base

VERIFIED by `git grep -n -E 'CCL|Thm2_15|NormRelations'` on Lean files, followed by searches
for the names of the direct users and the `E2ChainInputs` and `E2ChainInputsS` providers.
Paths below are relative to `ZInQKernel/Contrib/`.

| Module and use | Existing premises relevant to the factor |
| --- | --- |
| `CloudB3E2Norm/H20HeegnerNorm.lean`: `hnorm_of_normRelations`, `hnorm_of_print` | Arbitrary `d`, admissibility, split Jacobi value and additive transport. The print wrapper has an arbitrary anchor with no unit, level or split-at-two condition. |
| `CloudB3E2Norm/H20Transport.lean`: `hnorm_of_normRelations_on`, `hnorm_of_print_on` | Same conditions, with transport on an additive subgroup. |
| `CloudB3E2Norm/H20Dictionary.lean`: `hnorm_of_fields` | Admissibility, splitting of the new prime, realization in the field, lifts and Frobenius. It calls `hnorm_of_normRelations_on`. |
| `CloudB3E2Norm/H20Anchor.lean`: `CCLGenuine`, `hnorm_of_genuine_print` | The anchor pins the discriminant, the newform level and a Heegner form at conductor one. The field, curve and level are generic; no `4 ∣ N` or split-at-two premise. |
| `CloudB3E2Norm/H20DictFields.lean`: `hnorm_of_full_anchor` | Full anchor adds the field and Galois dictionaries, with `[NeZero d]`, which allows `d = 1`. It calls `hnorm_of_fields`. |
| `CloudB3E2Norm/H20PresClass.lean`: `gx_step_anchored` | Calls `hnorm_of_full_anchor` at generic positive `d`; extra assumptions concern coefficient support, points and transfer. |
| `CloudB3E2Norm/H20PresClassOf.lean`: `gx_step_heegner` | Calls `gx_step_anchored`; adds the realized points and character data. The conductor is still generic and can be one. |
| `CloudB3E2Norm/H20PresClassMatch.lean`: `gx_step_heegner_at` | Calls `gx_step_heegner`; adds the matching of the two places and Frobenius. No explicit level or unit premise. |
| `OneProof/RC/Wiring/CommonCoordinate18E2.lean`: `E2ChainInputs.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | The older presentation has `hd : 0 < d`, `f ∣ d` and `[NeZero f]`; none of these is a lower bound greater than one. The curve is explicit, but no `4 ∣ newformLevel (Ecurve ℓ)` theorem was found. |
| `OneProof/RC/Wiring/CommonCoordinate19E2.lean`: `E2ChainInputsS.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | `G.r_prime (t+1)`, `dvd_thetaCond_r`, `I.hfd`, `dvd_chainCond`, and `I.chainCond_pos` give `1 < chainCond I.d P.ps i`. |
| `CloudB3E2Norm/E2ChainActual.lean`: `e2ChainInputsS_of_actual` | Passes the print through; sets `d = thetaCond …`. Also has the companion data excluding the exceptional discriminants via `discr_of_sqrt`. |
| `CloudB3E2Norm/E2ChainGood.lean`: `e2ChainInputsS_of_actual'` | Passes the print and the same companion data to the constructor. |
| `CloudB3E1RingClass/SupportReq.lean`: `e2ChainInputsS_of_support` | Passes the print and the same companion data to the good reduction wrapper. |
| `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean`, `OneProof/RC/Wiring/CommonCoordinate19Leaf.lean` | Downstream packages use `e2Provider` and `e2ProviderS`, respectively; they do not apply the print. |
| `CloudB3E2Norm/CochainNorm.lean`, `GlobalChar.lean`, `GlobalCochain.lean`, `H20PresAssembly.lean`, `H20FrobArtin.lean`, `OneProof/RC/BaseZeroAssembly/Boundary45.lean`, `OneProof/RC/HeegnerAlgebra/Interfaces.lean` | References are in explanations. The cochain core takes the explicit point equality (4.1); no CCL application occurs in its proof. |
| `OneProof/RC/PrintsArith/Bundle.lean` | Direct import and comment; does not package a CCL witness. |

The two direct module importers of `Heegner.lean` are `H20HeegnerNorm.lean` and `Bundle.lean`.
The reverse import closure calculated from tracked Lean imports contains neither
`ZInQKernel/OneProof/Main.lean` nor `ZInQKernel.lean` at this base.

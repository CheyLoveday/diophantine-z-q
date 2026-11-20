# rc-metaplectic-2 results

- Base: `de7285815455bd82c7b9a7d805d4f7c6db714c95`.
- Source checkpoint: `8ca793de7afe0900f21fe8ff1a057997f25d15e0`; no earlier task log in the checkout.
- Local scalar defects: `r(s) r(t) / r(st)`, `γ(Q)^2 / r(-1)`, and `γ(Q)^2 γ(bQ) / γ(-b⁻¹ Q)`. Cubic defect: `γ(Q)^4`, equal to `-1` at two and `1` away from two.
- Good primes: self-duality, mass one, index one, three fixed generators, integral action fixing the reference.
- Finite tensor: coordinatewise multilinear quotient; full-space cylinder tests for each form's separate operator group.
- Common cover construction: `cover_of_relations` takes relations in the quotient and makes the prescribed generator lifts; `coverProjection_surjective` and `cover_kernel` compute the surjection and kernel; `cover_kernel_pair` and `cover_kernel_central` give the exact two-element central kernel for a scalar sign subgroup.
- Stop: actual common signs, finite restricted product of the covers modulo product-one signs, invariant rectangular images. No new print.

| Module | `lake env lean` | Audits returned or first missing import |
| --- | --- | --- |
| CentralCover | pass | 5 |
| Covariance | import blocked | Metaplectic2.Relations |
| Gaussian | import blocked | Metaplectic2.Relations |
| IntegralAction | import blocked | Metaplectic2.Projective |
| Matrices | pass | 3 |
| NormalForm | pass | 7 |
| Presentation | pass | 2 |
| Projective | import blocked | Metaplectic2.WeylRelations |
| Relations | import blocked | Metaplectic.Generators |
| Restricted | import blocked | Metaplectic2.Spherical |
| Sandwich | import blocked | Metaplectic2.Gaussian |
| Spherical | import blocked | Metaplectic2.Relations |
| Splitting | import blocked | Metaplectic2.Spherical |
| TensorComparison | import blocked | Metaplectic2.Projective |
| WeylRelations | import blocked | Metaplectic2.Sandwich |

- 109 audit commands cover all theorem declarations; 17 audits returned, all within `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `axiom` declaration, local notation, or direct import of `ZInQKernel.OneProof.Main`.
- Load/memory gates passed. Verification incident: the first matrix check briefly overlapped the dependency build. Older build terminated. Table: serial rerun with exclusive lock and load/available memory gate before each invocation.

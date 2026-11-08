# Source application and incorporation record

This record connects the actual arithmetic objects to the new conditional
Lean interface. It does not claim that those arithmetic constructions already
exist in Lean. The ordinary proof is incorporated in the versioned
[LaTeX insertion source](manuscript-insertion.tex), the sole editable
publication authority for this addendum. The earlier `DERIVATION.md` and its
`REVIEW.md` are preserved as the reviewed research record.

## Exact insertion and source

Base: `e653d6ff295ae4e0535710a7d64aa255d294d211`.
Target: `manuscripts/quartic_v13.tex`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
Inside `ex:limits-derivative-switch`, replace the paragraph beginning
`The determinant comparison is exact even if $v$ is divisible.` and ending
`Requiring $x$ integral would be wrong when $v$ is divisible.` (lines 5086–5092).
Do not replace the following `\end{proof}`. The insertion is an expansion of
that comparison, not a change to the polynomial or theorem statement.

The canonical V13 file remains unchanged while the old cloud/review snapshot
is frozen. This is addendum incorporation, **not canonical manuscript
incorporation or an update of its acceptance registry**. A later manuscript
integration must bind the changed complete source and obtain its own review.

The consumer is `ex:limits-uniform-lower-bound`, its inner valuation
preservation step (5095–5145), and the primitive height-one continuation
(including the exceptional localizations, 5160–5374). Outer rank-reducing
objects are not asserted to be isomorphic or rank preserving.

## Formal interface crosswalk

| New formal item | Required arithmetic realization and evidence |
| --- | --- |
| `cocycle_conjugation` | `rho` is the coefficient representation as a monoid homomorphism to linear endomorphisms; `p` is an actual crossed cocycle. The theorem derives the coboundary term without any trivial-action assumption. |
| `cocycle_transport_shared_unit` | On the retained local group the action is trivial. For `a=d*tau`, H12 gives the Tate factor identity, leaving one character unit. The source/review checks both classes use that same transporter. No global quadraticity is assumed. |
| `rawCup` and `coefficient_pairing_symmetric` | The actual coefficient pairing is `epsilon * area(f,J*s)` with J once. Involution and determinant -1 derive symmetry; no division by two. |
| `coneProductThird` / `cone_pure_boundary` | Explicit degree-(2,1), parameter-zero third component. The degree-one mixed cup and degree-two/degree-zero cup have separate types. Bilinear homotopies vanish for a pure boundary. This is the elementary source formula, not a constructed cochain complex. |
| `PairedBoundaryData.comparison` | The localized orthogonal-to-conjugate map on degree-one classes, with inverse. Its derivative-place identity gives `comparison_local`. Separate data are supplied for F and S; no F-to-S equivalence exists in this interface. |
| `conjugate_local` | Local compatibility of the actual conjugate transport, with shared coefficient scalar and tame minus. The cocycle theorem and the retained Frobenius/tame computation justify this source application. The Lean bridge requires its realization on the supplied carriers. |
| `partner` / `partner_local` | The partner is defined as the inverse comparison applied to the conjugate of the actual class. Its localization is derived, not assumed separately. |
| `boundary_adjoint` | General Poitou–Tate boundary adjunction for all local directions and orthogonal partners, with the same trace convention. The new module proves its elementary pure-boundary product calculation but inherits the identification with actual global duality. |
| `hA`, `hB` | Actual H19–H22 old/derivative local coordinates, with the same fixed L. The new module does not construct Heegner classes. |
| `hboundaryF`, `hboundaryS` | The opposite boundary representatives realize AS/AF in the actual common-strict matrix model. This is an explicit model-identification requirement. |
| `hrowF`, `hrowS` | The stored rows are evaluations of the actual paired functionals on every target vector. Independent primitive-row rescaling is not allowed. |
| `hclassF`, `hclassS` | The specified realization of each actual class equals the stored cycle vector. The `HasCoordinate` premises are about the realized actual classes and are rewritten using these equalities. Local-coordinate agreement alone is not substituted for class identity. |
| `transported_boundary_cup` | Derives all-vector `BoundaryCupIdentity` with cF=-(kappa*transport), cS=kappa*transport. Neither these normalized identities nor the unit conclusion is an input field. |
| `arithmetic_unit_comparison` | Uses the actual subring and explicit -1 unit witnesses to call the unchanged integral adapter, preserving zero and common nonunit factors. |

## Nine application obligations

| Obligation | Required, constructed and checked scope |
| --- | --- |
| Source hypotheses | Actual paired cones, perfect coefficient pairing and retained isotropy/localization homotopies are inherited from V13. Nekovář's explicit pure-boundary formula is evaluated in the addendum; the whole arithmetic duality theorem is not reproved. |
| Objects | H19–H22 A/B, their actual PD-defined functionals, two distinct local conditions and the common strict determinant factor. The formal interface exposes class and row identities. |
| Domain/index coverage | Every local f/s, every eligible inner rank-one constituent and every finite switched list. Generic nonzero localization remains required. No bounded test substitutes for these quantifiers. |
| Maps | Actual inverse orthogonal comparison, conjugate transport, local restriction, opposite boundaries and trace. The local rational-Frobenius choice and shared character unit are checked in the ordinary review; the formal cocycle identity records the algebra. |
| Consumed object | The ordinary proof compares the actual determinant tensors. The Lean consumer compares their specified common-strict matrix realizations; the model realization is explicit inherited work. |
| Coefficients/normalization | The coefficient ring is fixed under conjugation. J is inserted once; fixed L stays in the classes; the common trace factor may be nonunit. The relative normalizer is an actual integral -1 unit. |
| Local conditions | D0 is retained. The derivative orthogonal comparison is identity. Completed two-adic and primitive height-one functional representatives are separate source constructions. |
| Exceptions | Divisible vectors, no integral eigenbasis at two, nonquadratic global character, common zero/nonunit factors in the formal bridge, and (t)/(t+2) are distinguished. Actual rank claims use nonzero local pairing/trace. |
| Downstream | Supplies the normalization and tensor-comparison inference relative to the retained inputs. No restricted converse, full arithmetic construction, formal determinant functor or cloud acceptance follows. |

Exact versions and native evidence are bound in `evidence/native/RESULT.json`.
The three focused read-only reviews bind the final new source and application
bytes. The old 63/65/99 manifests and generated 39-project remain unchanged.

# Application: actual local conjugation and its integral unit

Application ID: `CLT-20261108`. Author: Codex `/root` (model).
Base: `3a7dce59e3d0601a3758cf924810563a6e5f0a98` on the separate research
branch `codex/derivative-switch-boundary-v13`. This is a scoped research
follow-up, not a manuscript edition, release, or promotion of the arithmetic
switch. The canonical manuscript, prior research packets and foundation PR
are unchanged. Publication-generation duties do not apply to these new
ordinary GitHub Markdown research records.

The actual finite calculation derives the common conjugation unit from the
twisted representation and H12. Previously, the Lean bridge's
`cocycle_transport_shared_unit` took the scalar action as a hypothesis and was
stated over a field. Its `PairedBoundaryData` still assumed `conjugate_local`.
The earlier source derivation already discussed the cocycle identity and the
shared factor; the present contribution is its precise ring-level derivation,
descent to actual Mathlib H¹, common-quotient application, and explicit retention
of the unit/inverse pair. No historical claim of a new mathematical discovery
is intended.

## Sources and proof authority

The authoritative source under review is `manuscripts/quartic_v13.tex`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
`evidence/source-bindings.json` records the relevant source/consumer excerpt
hashes as well as whole-file hashes. Source line ranges are locators at this
revision, not substitutes for the actual text.

| Input | Exact source and mathematical status |
| --- | --- |
| Finite rings and actual coefficient character | V13 2859–2866 and 2898–2967: $A_i=(\mathbf Z/2^i)[t]/t^i$, or $A_i[G]$; the twist is $\alpha_i T$, and raw pullback fixes the coefficient ring. Internal source construction, not formalized here. |
| H12 and local basis | V13 3225–3233: $T(\varphi)=T(\tau)$ and $2^{a+1}\mid\ell+1$. Internal retained arithmetic input. |
| Actual A/B classes and their common module | H20–H21, V13 3339–3417: both classes use the same coefficient character/push, with character trivial at the derivative place. The derivative relation changes the class, not this module. |
| Local action and coordinates | V13 3431–3456: good odd derivative primes, good-reduction unramified Tate action, inert Frobenius square and retained tame coordinates. |
| Continuous representatives and witnesses | H22, V13 3509–3542: continuous finite-coefficient cocycles and local boundary witnesses in the actual cone. |
| Tame group and Frobenius orientation | Jan Nekovář, *Selmer complexes*, Astérisque **310** (2006), §7.1.1 p.155 and §7.2.1 p.156, [published Numdam source](https://www.numdam.org/item/AST_2006__310__R1_0/). Read PDF SHA-256 `61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`. No extra arithmetic duality theorem is imported from these sections. |
| Retained inner diagram | V13 4456–4464 and `ex:limits-inner-limit`, 4577–4634: one fixed ultrafilter, actual contractions and comparison homotopies, bounded model ranks for fixed support. An internal source lemma used explicitly, not a Lean-proved consequence of this packet. |
| Genuine H¹ implementation | Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, `RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`: `cocycles₁`, `H1`, `H1π`, `H1π_eq_zero_iff`, `H1_induction_on`. The new maps descend through the cohomology of that actual cochain complex. |

The mathematical proof of this application is [DERIVATION.md](DERIVATION.md).
The new Lean files are proof sources for its finite ring/H¹ assertions, not
generated reading copies. The manuscript's existing addendum authority in
`research/arithmetic-boundary-cup/manuscript-insertion.tex` is unchanged;
this packet neither edits it nor claims to incorporate a new manuscript repair.

## Nine application obligations

| Obligation | Constructed input, check and status |
| --- | --- |
| Source hypotheses | **Addressed for this local calculation, relative to the named source constructions.** Set $\Gamma=G_{\mathbf Q}$, $H=G_K$ through the common finite quotient, $T$ the retained Tate representation, and $\alpha$ the actual coefficient character. The inert rational Frobenius and actual complex conjugation have the same nontrivial coset, so $d=\varphi\tau^{-1}\in H$. H12 yields $T(d)=1$, not an assumed arbitrary scalar action. |
| Constructed objects | **Addressed at finite precision.** Use the actual H20–H22 old and derivative cocycles, same character and transported local coordinates. The common affine-kernel/normal-core construction in the derivation makes the tame relation exact while retaining both cocycles and coefficient systems. Full arithmetic definitions are not constructed in Lean. |
| Domain and index coverage | **Addressed for every cocycle on fixed data and fixed finite family/support.** No nonzero or primitivity assumptions; finite Artin rings, group rings, divisible vectors and zero classes are included. Both classes use the same explicitly defined unit. The inner argument uses fixed support/bounded ranks, and claims no uniform rank bound over all supports. |
| Transition and comparison maps | **Addressed locally; later global comparisons remain open.** Pullback is into conjugate coefficients; coboundaries vanish at the relevant local elements. The unit and its inverse join the same fixed-ultrafilter tuple. For arbitrary limiting cycles, use reduced retained contractions and the finite theorem at each precision, not a claim that H¹ commutes with nonflat base change. |
| Identity of the consumed object | **Addressed for local conjugation in the specified retained diagram.** No independent rescaling is made: the factor is $\alpha(d)^{-1}$. Extending the tuple preserves the existing coordinate-map limits. Matching this diagram to every later common-strict matrix and stored functional is a separate, unresolved consumer obligation. |
| Coefficients and normalization | **Addressed.** Original and conjugate representations stay distinct, even for a nonquadratic moving character. The coefficient $J$ belongs to $e_2(x,Jy)$, not raw pullback. Forward tame conjugation gives $\ell$, inverse gives $\ell^{-1}$; both reduce to $-1$. No fixed prime equals $-1$ in characteristic zero. Unit/inverse retention supplies integral units. |
| Local conditions | **Addressed for the derivative place.** Good reduction gives trivial inertia; H12 gives trivial Frobenius-square action; character triviality is supplied separately by H21. Wild inertia vanishes in the common quotient. Kummer conditions at other places and global orthogonal comparisons are not proved by this local result. |
| Exceptional cases | **Addressed in scope.** Characteristic two and 2-primary torsion are allowed; there is no division by two or by a class. The derivative prime is odd and good as required by the arithmetic source. Rank changes, vanished coordinates and divisible local vectors are harmless to this identity. Actual localization inverses and exceptional occurrence for the determinant comparison remain separate. |
| Downstream consumption | **Partial, explicitly bounded.** The result supplies the local shared-unit equation used by `PairedBoundaryData.conjugate_local`, relative to the specified retained-model identification. It does not instantiate the whole structure, prove `boundary_adjoint`, identify its stored functional rows, or prove the final tensor relation. The foundation's 39 targets remain exactly unchanged. |

## Findings and disposition

| Finding | Historical classification and current disposition |
| --- | --- |
| Scalar transporter was an input in the field lemma | Prior components located in the old cocycle derivation. Now derived over a ring from the actual twist and H12; source and code reviewed separately. |
| Raw conjugate may not be a cocycle for the original module | Correct coefficient distinction already present in V13. Preserved explicitly in `rawConjugate_isCrossed` and `h1Pullback`; no quadraticity is added. |
| Tame relation need not hold for arbitrary global lifts | Additional connecting argument supplied in the derivation: common finite quotient killing wild inertia for both actual cocycles and the actions. |
| Finite H12 cannot be instantiated at a fixed prime in characteristic zero | Direct field specialization rejected. The actual fixed-ultrafilter source route retains the unit and inverse instead. |
| Moving characters need not be compatible between stages | Source explicitly permits this. The finite-residue ultrafilter proof retains the shared unit without inventing a global character. |
| Stagewise H¹ identities do not automatically apply to every limiting class | Addressed by the per-precision cycle argument using retained contraction maps after coefficient reduction. No surjectivity of cohomology base change is asserted. |
| Global determinant normalization | Still open here: boundary–cup/duality identity on actual objects, orthogonal inverse, common-strict realization, actual functional rows, determinant comparisons and localization occurrence. |

## Verification, review and scope of delivery

Native Lean 4.35 verification and transitive axiom results are recorded in
`evidence/native/`. Only the two new modules are freshly compiled by this
packet's runner. Its imported Mathlib artifacts are pinned official master
cache dependencies. This is development verification, without paranoid mode,
external kernels or protected comparison; the older six-checker evidence does
not cover these new files.

The non-author review is recorded separately in `REVIEW.md`, tied to the
exact final hashes. It is a model review, not independent specialist acceptance.
Full arithmetic formalization and manuscript acceptance remain open.

Preservation is measured by direct hashes of all entries in the frozen 63/65/99
manifests and comparison of the seven frozen modules against `e653d6f`. The
foundational branch is not a destination for these research changes. No V13
publication, historical approval, or Open Math receipt is rewritten.

# Independent review of the orthogonal comparison packet

Date: 2026-11-09. Reviewer: Codex `/root/determinant_attack`, not the author
`/root/orthogonal_attack`. This is an internal model review of the bounded
source-interface argument, not independent human acceptance of the paper.

### 1) Verification target

The actual same-global-component Selmer-cone comparison, its homotopy inverse,
and preservation of global/derivative local cohomology; the strict-H² dictionary
for actual boundary matrices and pulled-back PD-functional rows. The assumptions
are the packet's specified actual local comparison maps/inclusion homotopies,
localized integral homotopy inverse, same global carrier and localization, and
its generic rank/nonzero-localization guards. Independence of opposite columns
uses either the actual relaxed-image input or nonzero actual cross evaluations.

Source lookup read V13's H22 at 3509–3542, actual paired functional and localized
contractions 3842–4012, derivative triangles 5021–5093, singular comparison
5351–5373, the complete new Lean source, and actual prior declaration
`Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1_local_transport`
in `ConjugateLocalH1.lean`. This is a bounded source check; it does not reprove
old Kummer duality, existence/uniform bounds of all retained models, or all
Poitou–Tate hypotheses. Those remain source premises, visibly stated.

### 2) Independent re-derivation (outline)

With H22 differential third coordinate loc(g)-i(u)-dq, an inclusion square
`i-i'a=dh+hd` gives j(g,u,q)=(g,au,q+hu). Its two third-coordinate expressions
differ by exactly i(u)-i'au-dhu-hdu; hence it is a chain map. Global projection
is literally unchanged. In categorical composition order, j:C→D, k:D→C,
p:C→G,q:D→G satisfy j≫q=p and k≫j~id_D. Postcomposing that homotopy by q
gives k≫p~q. This establishes equality of the induced homology maps and remains
true after postcomposing the actual localization chain map. On an actual H22
cycle, global localization and the local-condition representative differ by a
boundary; thus the conclusion is about actual local H¹, not literal equality of
cochain entries. No extra scalar can appear.

For the separate strict dictionary, the finite LES and v≠0 imply H¹(Cstr)=0
and the short exact sequence F/Kv→H²(Cstr)→H²(CF), so dim W=2. Rows are first
defined intrinsically as λ_U∘π_U, and closedness follows from π_U∂_U=0. If
opposite columns are independent, singular rank one follows from ∂_S(Jv)=0
and ∂_S(Jx)≠0. This reasoning does not assume singular rank one when defining
λ_B and does not identify CF with CS. Integral strict torsion is explicitly
left to the common strict determinant factor, not removed by this field model.

### 3) Checks

- Independently reran `python3 -B research/orthogonal-comparison/check_comparison.py`.
  PASS: 6400 degreewise cone cases; 4680 two-term homotopy congruence cases;
  2043 wrong-sign instances detected; arbitrary-map and nilpotent-inverse
  controls rejected. These are exact finite-ring algebra checks, not arithmetic
  Galois instances. Degreewise checks do not assert that every random tuple is
  a full cochain complex; the separate Mathlib statement uses actual complexes.
- Rechecked the sign conversion l=-q and the required inverse direction k then
  j. Both are consistent with H22 and the displayed homotopy proof.
- Checked degenerate guards: v=0 invalidates strict-H¹ vanishing; zero trace
  cannot prove column independence through Route B; arbitrary cohomological
  equivalence without the same projection/homotopy square is insufficient.
- Checked the actual prior local transport theorem's carrier, conjugate
  representation, retained ell=-1 premise and common transport unit. The new
  packet does not silently identify a conjugate representation with an ordinary
  dual or insert a second J.
- Reviewed the new Lean theorem statements and proof bodies. Native Lean4.35
  compilation/axiom receipts are supplied separately by the root integration
  harness; no new independent kernel replay, paranoid run or external-checker
  result is claimed by this review.

### 4) Discrepancy report

One exact source locator was corrected by the author before this acceptance:
`ConjugateLocalH1.LocalData.h1_local_transport` was a filename-like shorthand,
not the actual declaration namespace. The final derivation now names the full
`Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1_local_transport`
and its owning file. The correction changes no mathematical assertion or Lean
source. The reviewer reread the corrected application sentence and actual
source declaration. No remaining mathematical discrepancy was found within
this bounded contract.

### 5) Certification result

**CERTIFIED under the explicitly retained source premises for the bounded cone,
homotopy/localization and generic strict-H² dictionary lemmas.** This independently
supports the claim that an actual justified inverse introduces no new derivative
local normalization factor. **The complete arithmetic determinant-switch theorem
is NOT CERTIFIED by this review.** Actual global cup/trace descent, source-to-limit
coherence, nonzero actual trace where used for rank, and universal group-ring
integral descent remain separate obligations. The source's existence of the
local a/h diagrams and localized inverse is not newly constructed by a generic
homotopy theorem.

Reviewed exact-byte SHA-256 bindings:

```json
{
  "research/orthogonal-comparison/DERIVATION.md": "eac267d42dafa465de5c96c8754446e07b86c2a5802aaf54cae7103f09e80cd2",
  "research/orthogonal-comparison/README.md": "e9c250a06f896e4b713edd87e88207a3d212c83149d0c279d7d5eab6ad757d19",
  "research/orthogonal-comparison/check_comparison.py": "5b071db8be64a86dba569f12527ef1e3bd7bf2463927586d8cda5fe9d5643fc9",
  "research/orthogonal-comparison/evidence/comparison-checks.json": "f746d85905fa687dada152bc7b6a4c8ad980d051079c631a63db4d6622e8f6d3",
  "lean/Research/DerivativeSwitch/OrthogonalComparison.lean": "bfec996b869e44c6a42fc058fbc24cc7288b1f61d0f0e7eef1f4f58f41dca1ba",
  "manuscripts/quartic_v13.tex": "9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd",
  "lean/Research/DerivativeSwitch/ConjugateLocalH1.lean": "078ac50ae0c90c8e609a57c51c5884a25646ad7305531f1cf531617485b9078f"
}
```

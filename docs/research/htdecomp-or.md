# htdecomp-or: `hodgeTateDecompExists` from an or-form leaf (tensor form OR Hom form)

Task htdecomp-or, 2026-11-17. Base `origin/wip/leaf-fold33b` at d911d55cf (8ba86099 is an ancestor), with
`origin/main` (ee33f2143) merged. Log: `scratch/htdecomp-or/log.md`.

## Verdict

The research field `hodgeTateDecompExists` (`ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists`,
`ZInQKernel/Contrib/OneProof/HodgeTatePairingDecomp.lean` l. 44; strict leaf review 2026-11-17, queue10: GLUE/GLUE,
"Fontaine 1982's form is unread. A Hom-form print needs a `C_p`-dualization Lean does not prove") is **proved in Lean
from one new leaf**, the disjunction of the two printed shapes of the Hodge–Tate decomposition:

```
def HodgeTateDecompOr : Prop := HodgeTateDecompExists ∨ HodgeTateDecompHom

theorem ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or (h : HodgeTateDecompOr) : HodgeTateDecompExists
theorem ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_hom (h : HodgeTateDecompHom) : HodgeTateDecompExists
```

The **`ℂ_p`-dualization the review asked for is proved** (`dualEquiv`, `dualEquiv_map`, §2): an equivariant
`Hom_{ℚ_p}(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` gives an equivariant `ℂ_p ⊗ V ≅ ℂ_p(1)^b ⊕ ℂ_p^a`, for any
`ℚ_p`-representation `V` of `G_F`, with no finiteness assumption on `V` (the Hom form forces it). No new glue: the
proof uses only Mathlib and pkg-I4/TailS definitions and lemmas (`cpAct_inv_apply`, `cpAct_algebraMap`).
`#print axioms`: `[propext, Classical.choice, Quot.sound]` for both theorems (VERIFIED, §5).

Result for the fold (`autofold.py --dry-run`, §6): `hodgeTateDecompExists` (GLUE, pending reading) replaced by
`hodgeTateDecompOr` (LEAF, unread, locator UNVERIFIED): **GLUE −1 in both columns, no new glue.**

(The remaining sections are filled in below.)

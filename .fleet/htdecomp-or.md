# htdecomp-or (2026-11-17)

**Result.** The research field `hodgeTateDecompExists` (`HodgeTateFromPairing.HodgeTateDecompExists`, rated GLUE/GLUE
by the queue10 review) is proved from one new leaf, `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
HodgeTateDecompExists ∨ HodgeTateDecompHom`. Its disjuncts are the tensor form `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b` and
the Hom form `Hom_{ℚ_p}(V_p(A), ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b` (Tate 1967 §4 / Fontaine 1982 shape, bases chosen,
exponents unnamed). **The `ℂ_p`-dualization the review said Lean did not prove is proved**
(`hodgeTateDecompExists_of_hom`), for any `ℚ_p`-representation, with finite-dimensionality derived from the Hom form
itself. A helper file also proves that the `H¹_ét` shape (Faltings 1988) implies the Hom form, and that tensor ⇒ Hom,
so the or-leaf is equivalent to the field (`or_iff_field`). Each print shape implies the leaf by a Lean proof, so the
leaf is never stronger than any of them. Rated LEAF (published, unread, locator UNVERIFIED).

**Compiles (VERIFIED).** `ZInQKernel/Contrib/OneProof/HodgeTateDecompOr.lean` (imports `HodgeTatePairingDecomp`) and
the helper `HodgeTateDecompOrH1.lean` both build with `lake build`. All axioms are standard. `#discharges`:
`hodgeTateDecompExists_of_or` discharges `OpenResearchLeaves41.hodgeTateDecompExists` and still assumes only
`HodgeTateDecompOr` (`scratch/htdecomp-or/Discharges-output.txt`). The autofold spec is
`scratch/htdecomp-or/autofold.json`. The dry run printed `strict 12/23 -> 13/22; strictest 11/24 -> 12/23` (GLUE −1 in
both columns, no new glue). The dry-run module `AutofoldDry.lean` compiles on TailZ66, and `sixContactMin_of_open60`
has standard axioms.

**Remains.** A reading of Fontaine 1982 and Tate 1967 §4 to record which disjunct is the literal print. It cannot
change the rating. Also the integrator's fold and a `locators.md` row (the text is proposed in the report). Report:
`docs/research/htdecomp-or.md`.

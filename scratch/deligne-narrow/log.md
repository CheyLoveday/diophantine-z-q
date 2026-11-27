# Results

- VERIFIED: source census follows the Deligne input through one assembly
  slot to three readers: the holomorphic family, ray class descent and
  connectedness. See [census.md](census.md) for the clause and object uses.
- VERIFIED: the copied cache initially lacked the archived `ZInQ` modules
  and the current headline modules. The archived sources match the cache's
  source tree. Missing project artifacts are supplied from local cache or
  compiled one module at a time; the current `Main.lean` is rebuilt.
- VERIFIED: `lake env lean` compiled `DeligneNarrow.lean` with no diagnostics
  after correcting an `open` scope and disambiguating `K4`. It proves
  `narrow_of_print` and replacement proofs of the three outputs.
- VERIFIED: the proposed kinds row passes the production validator.
  Both scores are 5 LEAF / 28 GLUE on 33 H inputs, unchanged; on the whole
  headline both are 5 LEAF / 32 GLUE on 37.
- UNVERIFIED: the inherited Shimura, Deligne and Milne locators were not
  checked against the publications.


- VERIFIED: the initial dry run found the `OpenResearchLeaves34EBCFSFU_y3c`
  carrier in the preceding module; the generator now copies it along with
  the other carriers. The final dry run declares 19 copied structures,
  32 copied theorems and a scratch headline.
- VERIFIED: `lake env lean scratch/deligne-narrow/Census.lean` compiled
  and passed the live/dead controls (80 listed declarations).
- VERIFIED: `lake env lean scratch/deligne-narrow/Discharges.lean` ran the
  three old-to-new reader examples, printed the standard axioms for all
  eleven new theorems, and found no new provider of an old field
  (`#discharges`: 37 hypotheses, 13,861 candidate theorems).
- VERIFIED: `lake env lean scratch/deligne-narrow/DryRun.lean` compiled.
  The old Deligne proposition is present under the original H and headline
  roots and absent under both replacement roots. The narrowed proposition
  and only it replaces the old type in the 30-field research bundle; the
  other headline argument types and conclusion match. The generated
  theorems report only the standard axioms.
- VERIFIED: the tail-only generator output compiled with `lake env lean`
  using only the two proposed tail imports. Its top has the standard axioms.

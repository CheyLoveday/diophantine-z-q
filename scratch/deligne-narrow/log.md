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

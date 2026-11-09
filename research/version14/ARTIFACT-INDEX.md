# Version 14 artifact index

These are the selected current artifact identities. They do not certify the unassembled cumulative archive or supply missing release approval.

| Artifact | Repository path | Scope |
| --- | --- | --- |
| Main TeX | `manuscripts/quartic_v14.tex` | Current main003 source |
| Main PDF | `manuscripts/quartic_v14.pdf` | 323 pages |
| Merged GI PDF | `research/version14/proofs/local-gi-v1/GI-SUPPLEMENT.pdf` | 103 pages, one guide and sixteen modules |
| GI PDF alias | `manuscripts/quartic-local-gi-supplement.pdf` | Same bytes as the merged GI PDF |
| Standalone GI archive | `research/version14/proofs/GI-PROOF-ONLY.zip` | Separate proof-only delivery, not nested in the cumulative archive |
| Research annex | `research/version14/z-in-q-version14-research-annex.zip` | 1,939 logical records, 1,643 distinct content objects; 10,265,610 bytes |

SHA-256 identities:

```text
main TeX       1f7bf748843d67c6a67d9863931ff0a15ca2548ae171ec1c1ce34b9002eb70a8
main PDF       b8844030a29a9b582911a7a3dbf711bed9e9e1b14d77c29ed56e40951827fe91
GI PDF/alias   1a553926eccf7540d43589554c737c8b3c6b0d9e049f1ee71d02dfea4fc01220
GI archive     d4aa92224ff373410a8e63073d0f829f80f55ad81be5dda357872a88822c0ae0
GI manifest    6bd2c5a0f632d908f94540622fe96ec378a6f79c983d3aca3e9ba26d350a8201
research annex 54e7aec54df9c1bd9bed0b02cd22a9a41ae3fb7717d12107ff72dd0700a2cd51
```

The GI manifest is `PROOF-ONLY-MANIFEST.json` inside the standalone package. Its membership describes that package, not a smaller cumulative selection.

The coefficient tables below are in `quartics/quartic-299-314/`.

| Table | Variables | Monomials | Bytes | Input coordinate |
| --- | ---: | ---: | ---: | --- |
| `quartic-299-symbolic-coefficients.txt` | 299 | 6,630 | 228,028 | `x1` |
| `quartic-314-ordinary-coefficients.txt` | 314 | 6,672 | 264,430 | `x1` |
| `quartic-314-source-id-coefficients.txt` | 314 | 6,672 | 222,890 | `x0`, preserved source IDs |

```text
299 text       e7f00ae1c0643cb31b93c28ea88e30c3b1790ace718625bb5e223b91e2b101ba
314 text       57d44e10a92cda1ffac29f46a54282f855882bcf21760c3419df62dc8c673822
314 source IDs efb34a9664a3a2c5b0abe548463e646ba18d6f7e5ab5d9eff9e80bb8b461291e
package        5369f80f69742958ea31f3a32b62b43e6b23b284063e6870af2dc2f0073977fb
```

The package identity is its `PACKAGE-MANIFEST.json`. See `ARTIFACTS.json`, `ACCEPTANCE.json` and the coordinate maps for the JSON tables, exact maxima, and distinctions between accepted and rejected history. Finite checks verify these constructions and serializations; they do not replace the retained arithmetic premises.

Final cumulative archive, selected source commit and authenticated gate bindings are pending. See [CUMULATIVE-HANDOFF.md](CUMULATIVE-HANDOFF.md) for their explicit binding slots.

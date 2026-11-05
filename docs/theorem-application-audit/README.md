# Theorem application inventory — November 5, 2026

This inventory records the external inputs used by the **11/4 manuscript**, the objects and maps to which they are applied, required hypotheses, convention changes, and the proposed justification for each translation. It is tied to one exact TeX file; it is not an endorsement of every recorded application.

**One source-strength mismatch has been found:** the Faltings 1988 comparison cited at the de Rham step gives Hodge–Tate decomposition. A stronger comparison theorem and finite-extension descent are needed. A replacement chain is described in [the findings](FINDINGS.md#f001-the-de-rham-step-needs-a-different-comparison-reference). It has not been inserted into the frozen manuscript or independently accepted.

## Read the audit

| File | Purpose |
| --- | --- |
| [INVENTORY.md](INVENTORY.md) | 82 application families, with maps, hypotheses, conventions, translations and prior review evidence |
| [SOURCES.md](SOURCES.md) | Exact file hashes, version differences, retrieval URLs and missing source pins |
| [FINDINGS.md](FINDINGS.md) | Concrete mismatch, proposed repair, and scope of new source checks |
| [OPEN_ITEMS.md](OPEN_ITEMS.md) | 39 unresolved source or application-review obligations |
| [coverage.json](coverage.json) | Counts, frozen manuscript identity, and explicit limitations |
| [validate.py](validate.py) | Checks bindings, references, coverage and hashes; does not check proofs |

The machine-readable files are [applications](applications.json), [348 anchored application contexts](application-sites.json), [all citation occurrences](citations.json), [sources](sources.json), [prior evidence](evidence.json), [internal references](internal-references.json), and a [named-input search index](named-input-index.json). A context anchor is not necessarily a separate theorem application. Nearby and repeated anchors are deliberately preserved.

## Coverage and verification are separate

| Item | Recorded coverage |
| --- | --- |
| Frozen manuscript | 10,734 lines; SHA256 `c59598ba474a1512dd03787c2bc9ff093a3c3a8a0604f96d5f8bcfa140c61693` |
| Explicit citation occurrences | All 99 classified: 87 applications, 10 summary citations, 1 provenance citation, 1 source-scope declaration |
| Citation keys | 119 occurrences across 44 cited works; bibliography contains 46 works |
| Application families | 82, including 28 identified uncited input families |
| Source records | 57, of which 55 have file hashes; 60 individual files checked |
| New source-interface inspections | 19 application families; each has an explicit bounded result |
| Internal references | All 223 resolve to a unique label |
| Outstanding obligations | 39 application records have specific open items |

The two source records without a file pin are Serre's *Local Fields* and the OpenAI provenance citation. The latter is not an imported theorem in this inventory. Five application families still have no identified external source: four squares, cusp torsion/Hecke equivariance, the optional Schreier route, compactness, and tame-cover geometry. These gaps are explicit rather than filled by guessed references.

The citation list is mechanically exhaustive for the frozen manuscript's `\cite` commands. **Semantic exhaustiveness is not certified:** implicit theorem uses may remain, and a resolved internal cross-reference does not establish that its theorem is applicable. The 82 families are a review organization, not 82 independently verified applications. Their 348 anchors retain the individual consumption contexts; where several uses share an interface, each still requires its own hypothesis check.

Likewise, a source hash identifies bytes, not publication status or equivalence to a journal edition. Several records distinguish an author version, an erratum, and a journal citation. Prior AI reviews are copied with their hashes and original scope; they are not relabelled as fresh reviews of this entire snapshot.

## Reproduce the structural check

From the repository root, using Python 3.10 or later:

```console
python docs/theorem-application-audit/validate.py
```

To check the primary files in a restored research workspace as well:

```console
python docs/theorem-application-audit/validate.py --workspace /path/to/research-workspace
```

`workspace_relative_path` values in `sources.json` identify their locations. New source PDFs retrieved for this audit have retrieval URLs and hashes; they are not automatically present in the older research handoff. The default repository-only check does not claim to have re-downloaded or checked those primary PDFs.

A successful run checks the manuscript hash, citation extraction and classification, excerpt hashes, application/source/evidence links, all internal reference targets, and prior-review file hashes. The optional workspace pass additionally hashes the available primary source files. **PASS means the audit data are internally consistent with the frozen inputs. It does not mean the mathematical applications pass.**

## Closing an item

For each application, the reviewer must compare the exact source statement (and any relevant proof/erratum) with the exact consumer, check every hypothesis, identify the actual map rather than only the names of its source and target, and justify every change of coefficients, lattice, dual, normalization, local condition or quantifier order. An exact sequence is not an isomorphism unless its other terms are proved to vanish; a rational theorem is not an integral theorem merely because both sides have lattices.

The open-items register must be updated with that evidence before an application is marked accepted. If the TeX changes, this snapshot must be regenerated or explicitly superseded; the validator intentionally rejects a changed manuscript hash.

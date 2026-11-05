# Inventory authoring files

`FROZEN_APPLICATIONS.json` contains the reviewed interfaces, current citation IDs and line anchors. `CITATION_ROLES.json` supplies the individually reviewed citation classifications. These files supersede the original `application_specs.py`, `fresh_checks.py` and `closure_checks.py`, which are preserved as the earlier authoring history and are not executed by the generator.

`source_map.py` supplies the original source/evidence paths. `SOURCE_ADDITIONS.json` and `EVIDENCE_ADDITIONS.json` add the final pinned records and explicitly replace corrected identities. `DOWNLOADS.json` and `CLOSURE_DOWNLOADS.json` retain original retrieval metadata. Primary files are obtained separately; the generator never downloads them.

From the repository root, with the listed source and evidence paths restored:

```console
python docs/theorem-application-audit/authoring/build_inventory.py --workspace /path/to/research-workspace --repo .
python docs/theorem-application-audit/validate.py --workspace /path/to/research-workspace
```

The generator refuses another manuscript hash. Review changed interfaces, anchors and classifications before updating its frozen inputs. `ANCHOR_REBIND.json` records the current rebind, and `MANUSCRIPT_EDITS.json` records the applied text repairs. The generator rebuilds the inventories, not the hand-written overview, findings or dependency discussion. It does not check mathematical proofs.

# Inventory authoring files

`application_specs.py` contains the hand-written application interfaces. `fresh_checks.py` records the bounded new source inspections and their changes to those interfaces. `source_map.py` maps source and historical-review IDs to files in the research workspace. `DOWNLOADS.json` records the primary sources retrieved for this audit.

The generator requires a restored research workspace containing those files. From the repository root:

```console
python docs/theorem-application-audit/authoring/build_inventory.py --workspace /path/to/research-workspace --repo .
python docs/theorem-application-audit/validate.py --workspace /path/to/research-workspace
```

The generator deliberately refuses a manuscript with a different hash. To audit a revision, first review and update the hand-written interfaces, line anchors, citation classifications, findings and overview; changing the expected hash alone is insufficient.

The generator rebuilds the inventory, source register, open-items list and JSON indexes. `README.md` and `FINDINGS.md` are hand-written reports and are not generated. It does not download files, inspect mathematical statements, or establish correctness. Exact source locations that have not yet been verified remain labelled as open obligations.

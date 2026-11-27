"""Dry run of the kinds.tsv row replacement; uses the actual scorer and validator."""
import csv
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "scripts/one_proof")
import autofold
import render_open

old = "deligneCanonicalModelY3EveryPrint"
new = "deligneCanonicalModelY3Narrow"
before, columns = autofold.load_kinds()
row, = [r for r in before if r["field"] == old]
flag = ("pending review: narrowed to live readers. Drops the lower half-plane, reverse fibre implication, "
        "regular-function analyticity away from g = 1, and duplicate body moduli and holomorphy hypotheses; "
        "restricts forward fibres, unit moduli and CM reciprocity. Locators UNVERIFIED.")
replacement = dict(row, field=new, kind="consequence", flag=flag, strict="GLUE", strictest="GLUE",
                   rated_by="pending review", flag_class="pending-review",
                   source="Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne, Travaux de Shimura, "
                          "Sem. Bourbaki 389 (1971), sections 4–5 (Cor. 5.7, Ex. 5.8); Milne, Introduction "
                          "to Shimura varieties (2005), sections 5–8, 12–14; locators UNVERIFIED.")
assert not render_open.kinds_row_problems(replacement, {new}, {})
assert render_open.must_be_glue(flag)
after = [replacement if r["field"] == old else r for r in before]
assert autofold.counts(before) == autofold.counts(after)
for stage, rows in [("before", before), ("after", after)]:
    n, l, g, ls, gs = autofold.counts(rows)
    hl = sum(r["strict"] == "LEAF" for r in rows)
    hs = sum(r["strictest"] == "LEAF" for r in rows)
    print(f"{stage}: H {n}, strict {l} LEAF / {g} GLUE, strictest {ls} LEAF / {gs} GLUE; "
          f"headline {len(rows)}, strict {hl} LEAF / {len(rows)-hl} GLUE, "
          f"strictest {hs} LEAF / {len(rows)-hs} GLUE")
print("Replacement passes kinds_row_problems and must_be_glue.")
with Path("scratch/deligne-narrow/kinds-row.tsv").open("w") as f:
    out = csv.DictWriter(f, columns, delimiter="\t", lineterminator="\n")
    out.writeheader()
    out.writerow(replacement)

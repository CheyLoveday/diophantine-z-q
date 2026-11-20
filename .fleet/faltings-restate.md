# Faltings’ height and the Néron comparison

**Verified.** Faltings’ printed height invariance for a semiabelian scheme
and its base change is proved from the existing height base change theorem.
The separately stated Néron comparison, with both Néron models semistable,
follows from the printed DVR instance of Faltings’ Lemma 1 (p. 350, read by
the reading desk). The local proof identifies the identity components;
localization gives the common open subgroup needed globally.

With Raynaud’s criterion and Néron model existence, the comparison gives
the old `faltingsSemistableHeightBC` field. Height minimality over a
common larger field handles an arbitrary intermediate Néron model.
There is no remaining need for a separate Corollary 3.3 input in this
discharge. Lemma 1 remains a literature input.

Both Lean files compile. All 14 new theorems use only the three standard
axioms. The live `#discharges` check matched the old field; the autofold
dry run gives **5 LEAF / 24 GLUE → 6 LEAF / 23 GLUE** on the 29 H fields,
in both ratings. The fold was not applied.

The previous report’s locator and citation attribution were incorrect:
the invariance sentence is on p. 354 in §3, without a proof or an SGA 7
citation. The old field still needed the Néron comparison. See
[the report](../docs/research/faltings-restate.md) and
[the check outputs](../scratch/faltings-restate/).

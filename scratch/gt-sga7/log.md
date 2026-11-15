# gt-sga7 results log

Base ef2f6915 (wip/leaf-fold18, top TailZ29).

## Findings (reading)
- VERIFIED (read TailZ19 L249, L1595-1650): the field `CToPrinted.SGA7_IX_3_3` is SGA 7 IX 3.3 **second** assertion
  (N0 x R' -> N'0 open immersion with image N'0). Its one use (`identityComponentBaseChangeDVRRange_of`, inside
  `semistableNeronBaseChange_of_printed_full`) is at L number field, O = O' ∩ L, L'/L finite number fields; only the
  open-immersion half is used (`obtain ⟨hWo, -⟩`).
- VERIFIED (read TailZ23 L311-330): the chain's leaf `ReductB.SemistablePersistsSHcp` is the **first** assertion of
  SGA 7 IX 3.3 (semistable reduction persists). It does not imply the second assertion: a strictly henselian form of
  the second assertion is needed as a leaf.
- VERIFIED (git show origin/wip/sh-printed2): task sh-printed2 (11-14, base b5ff0474, not folded) proved
  `SGA7_IX_3_3_0` (char 0, perfect residue field) from `SGA7_IX_3_3_SH` + sh-route's `NeronBaseChangeSH` + SGA 3 VI_B
  3.10 + Stacks 04KV, by fpqc descent. Plan: port onto the current chain with GapSHPair (every characteristic).

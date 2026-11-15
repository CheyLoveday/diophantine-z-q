# gap-triage results log

Base e38375b3 (w62). Started 2026-11-14 17:46 PST. Deadline 11-15 06:00 PST.

## Setup facts
- No .lake/build in the worktree; ~/dzq (main checkout, e38375b3) was mid-build of `lake build` (build-main.log, 10912/12302 at 17:51). Probes wait for it, then use `lean` with LEAN_PATH over ~/dzq's build dirs (read-only).
- Field list (base e38375b3, VERIFIED by grep of TailZ15/TailZ11/TailZ13/TailX): research 28, textbook 16, added 14, glue 1 = 59.
- w63 (origin/wip/w63 b5ff0474, leaf-fold11.md, VERIFIED read): removes genusX1Field (genus-fold), igusaCMValue24 (cm24-value), neronLocalizesDVR, faltingsLemma5BC, semistableNeronBaseChange (c-to-printed → six printed leaves blr_1_2_4, faltingsLemma5Printed, raynaudKernelBound, sga3_VIB_3_10, sga7_IX_3_3, egaIV_8_10_5_openImm); restates r1r2, shimuraFamily, gonzalezRotgerCountX6, deligneComponentsY3Printed on abelian schemes (…Ab) and adds mumfordRigidityCore. 61 fields, strict 50/11.
- Branches seen (for-each-ref, 17:50): x6-fold, x6-glue, shimura-cft, c-to-printed2, sh-route, theta-glue, t09-pic, unipotent-b, t5-glue2 — active, not in the brief's in-flight list.
- Upstream issue numbers: no mapping in tree. Partial evidence: CloudW02 BUILD_REPORT (H-67 under #80), CloudW06 NOTICE (H-72 under #81; T11bExists.lean says H-75 under #82), CloudW07 README (H-36, H-80 under #83), CloudW08 (H-33 under #83). Not reliable: issue column marked UNVERIFIED.

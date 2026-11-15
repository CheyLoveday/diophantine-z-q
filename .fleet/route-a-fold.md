# route-a-fold (fleet note)

**Result.** r1univ-rigid is folded into the single proof (route A for `R1univProps`). `ZInQ.OneProof.frozenTarget`
now goes through `HDec.HSyn.sixContactMin_of_open13` (`ZInQKernel/OneProof/H/TailZ17.lean`). Its bundles are
`OpenResearchLeaves11` (29 fields), `OpenTextbookLeaves10` (16, unchanged), `OpenAddedLeaves10` (14) and
`OpenGlue7` (1). Four fields change to their printed forms on abelian schemes:
- `r1r2` → `r1r2Ab`;
- `shimuraFamily` → `shimuraFamilyAb`;
- `gonzalezRotgerCountX6` → `gonzalezRotgerCountX6Ab`;
- `deligneComponentsY3Printed` → `deligneComponentsY3PrintedAb`.

Each new form is `L` with `R1fpProps ↦ R1fpPropsAb`. One leaf is added: `mumfordRigidityCore` (GIT Thm 6.14 +
Cor. 6.4, numbers UNVERIFIED). Each old field is filled by `(L_iff_ab (mumfordRigidity_of_core _)).mpr`. None of
r1univ-rigid's 18 leaves is a textbook field, and the other 14 are not `frozenTarget` fields.

**Counts.** 59 → 60 fields. Strict LEAF/GLUE: 44/15 → 45/15. Lenient: 52/7 → 53/7. The four restated fields keep
their kinds: `r1r2Ab` comp, `shimuraFamilyAb` c, the other two LEAF. If `MumfordRigidityCore` is read as a
consequence (per-component use of Thm 6.14), strict is 44/16 (SPECULATIVE, report §1.1).

**What compiles (VERIFIED).**
- `TailZ16` (32.6 KB): r1univ-rigid's `R1UnivRigid.lean`, verbatim.
- `TailZ17` (15.7 KB).
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- DumpCompact/cmp_hashes: 0 removed, 1 changed (`frozenTarget`), 129 new.
- `CheckRAF.lean`: field types and standard axioms of all new theorems.

No existing module was edited, and no HDec copy was added or deleted.

**What remains.**
- The polarization caveat (Lemma QP in families) is unchanged.
- The human check of Deligne's PEL model against this functor is still open.
- A future fold of the other moduli leaves (e.g. the split of `r1r2`) should use their `LAb` forms from
  `scratch/r1univ-rigid/R1UnivLeaves.lean`.

Report: docs/research/route-a-fold.md.

# hcm-lattice (fleet note)

**Result.** `hCM` is now a direct instance of Shimura 1971 Thm 5.4. The new leaf
`ZInQ.Contrib.HCMLattice.ShimuraThm54Local` uses three things from the print:

* the print's hypothesis: `IsAnalyticIso`, an analytic isomorphism ℂ/𝔞 → E(ℂ) over ℙ² coordinates;
* the print's `s⁻¹𝔞`, given by p-components (𝔟_p = s_p⁻¹𝔞_p in K_p = ∏_{v∣p} K_v);
* the print's `s⁻¹u`.

The old leaf is kept, and both uses are proved in Lean:
`shimuraMainCM_of_local : ShimuraThm54Local → T5Glue.ShimuraMainCM` and
`shimuraThm54_of_local : ShimuraThm54Local → HCMDict.ShimuraThm54`.

The steps between the print and the use are all proved:

* The Weierstrass map is an analytic isomorphism (`toPoint_isAnalyticIso`).
* The Weierstrass-map step is proved (`eq_toPoint_of_holo`, by Liouville on x'/2y), so no Silverman leaf is needed.
* `(sInvLat s 𝔞)_p = s_p⁻¹𝔞_p` holds for every lattice (`locLat_sInvLat`), and `sInvLat s 𝔞` is a lattice.
* The local–global principle holds: a lattice is determined by its p-components, and s⁻¹u is well defined
  (`mem_of_forall_locLat`, `lattice_eq_of_locLat_eq`, `rep_sub_mem`).

**What compiles** (only the standard axioms, no sorry):

* `scratch/hcm-lattice/HCMLattice.lean`, about 1.8k lines (proposed `ZInQKernel/Contrib/OneProof/HCMLattice.lean`).
* `FoldCheck.lean`. `#discharges` gives `DISCHARGES [hCM] by HCMLattice.shimuraThm54_of_local`, which still assumes
  `[ShimuraThm54Local]`. It also checks two theorems: the folded Main body, and frozenTarget with hCM filled.
* `MainFolded.lean`. `frozenTarget` compiles with standard axioms.

**Count.** hCM goes from consequence/GLUE/GLUE to the proposed published (unread)/LEAF/LEAF, pending review.
Strict GLUE among the TYZ/GZ hypotheses falls from 4 to 3; over all hypotheses the split goes from 17/22 to 18/21.
No other count rises.

**What remains.**

* The theorem numbers (Shimura Thm 5.4, Lang Ch. 10 Thm 3) are UNVERIFIED. The statement needs a check against the
  print: whether "analytic isomorphism" includes the group law (the leaf covers both readings), and the p-component
  definitions of s𝔞 and su.
* A reviewer still has to rate the new leaf.

Report: docs/research/hcm-lattice.md.

# hcm-lattice (fleet note)

**Result.** `hCM` is now a direct instance of Shimura 1971 Thm 5.4. The new leaf
`ZInQ.Contrib.HCMLattice.ShimuraThm54Local` uses three things from the print:

* the print's hypothesis: `IsAnalyticIso`, an analytic isomorphism ℂ/𝔞 → E(ℂ) over ℙ² coordinates;
* the print's `s⁻¹𝔞`, given by p-components (𝔟_p = s_p⁻¹𝔞_p in K_p = ∏_{v∣p} K_v);
* the print's `s⁻¹u`.

The old leaf is kept, and both uses are proved in Lean:
`shimuraMainCM_of_local : ShimuraThm54Local → T5Glue.ShimuraMainCM` and
`shimuraThm54_of_local : ShimuraThm54Local → HCMDict.ShimuraThm54`.

The Weierstrass-map step is proved (`eq_toPoint_of_holo`, by Liouville on x'/2y), so no Silverman leaf is needed.
The lattice lemma `(sInvLat s 𝔞)_p = s_p⁻¹𝔞_p` holds for every lattice (`locLat_sInvLat`), and `sInvLat s 𝔞` is a
lattice (`exists_periodPair_sInvLat`).

**What compiles** (only the standard axioms, no sorry):

* `scratch/hcm-lattice/HCMLattice.lean` (proposed `ZInQKernel/Contrib/OneProof/HCMLattice.lean`).
* `FoldCheck.lean`. `#discharges` gives `DISCHARGES [hCM] by HCMLattice.shimuraThm54_of_local`, which still assumes
  `[ShimuraThm54Local]`. It also checks two theorems: the folded Main body, and frozenTarget with hCM filled.
* `MainFolded.lean`. `frozenTarget` compiles with standard axioms.

**Count.** hCM goes from consequence/GLUE/GLUE to the proposed published (unread)/LEAF/LEAF, pending review.
Strict GLUE among the TYZ/GZ hypotheses falls from 4 to 3; over all hypotheses the split goes from 17/22 to 18/21.
No other count rises.

**What remains.**

* The local–global principle for lattices (𝔟 = K ∩ ⋂_p 𝔟_p) is used only informally, to read "every 𝔟 / every v
  with these p-components" as the print's single s⁻¹𝔞 / s⁻¹u. Formalizing it is a possible follow-up.
* The theorem numbers (Shimura Thm 5.4, Lang Ch. 10 Thm 3) are UNVERIFIED. The statement needs a check against the
  print.

Report: docs/research/hcm-lattice.md.

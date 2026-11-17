# derham-range results log

- 03:41 Berger download (arXiv math/0210184v1): FAILED, `curl: (6) Could not resolve host: arxiv.org` (sandbox and unsandboxed). No local copy found (find ~, docs/). Reading item (3) BLOCKED; flag stays pending reading.
- 03:44 scratch/derham-range/DeRhamRange.lean: VERIFIED compiles (lake env lean, no errors/warnings): range_iotaF_eq_bdrFix, bdrFixAlg, bdrFixEquiv, isField_bdrFixAlg, ddrFix, finrank_ddrFix, IsDeRhamAdm, DeRhamVpAbVarAdm, deRhamVpAbVarDirect_iff_adm. Copied to ZInQKernel/Contrib/OneProof/DeRhamRange.lean.
- 03:50 autofold.json (optional swap deRhamVpAbVarDirect -> leaf deRhamVpAbVarAdm, flag "pending reading: ..."): dry run rc=0, strict 9/25 on 34 -> 9/25 (unchanged). With a "pending review" flag autofold.py:196 would rate LEAF (count rise without a reading), so the flag was not used.
- 04:40 lake build +Main +Discharges +DeRhamRange: OK. #discharges (Discharges-output.txt): `DISCHARGES [OpenResearchLeaves45.deRhamVpAbVarDirect] by DeRhamPrint.Range.deRhamVpAbVarDirect_of_adm, still assumes: [DeRhamPrint.Range.DeRhamVpAbVarAdm], axioms: [propext, Classical.choice, Quot.sound]`; range_iotaF_eq_bdrFix and deRhamVpAbVarDirect_iff_adm: standard axioms only. VERIFIED.
- 04:45 dry-run fold (FoldDryRun.lean.txt, line 1 stripped) compiles: sixContactMin_of_open65 standard axioms. VERIFIED.

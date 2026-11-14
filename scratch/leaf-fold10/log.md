# leaf-fold10 log

- 12:57 start (fresh). Base 28b41fb3. dimjac-glue done (.fleet present); reduct-glue, shimura-glue not done; no CloudW1* on origin/main.
- merged origin/wip/dimjac-glue (scratch only). `dimJacobianEqGenus` is strict GLUE (comp) in leaf-fold9 §2 => fold lowers strict GLUE 21 -> 20.
- TailZ10 = DimJacGlue.lean verbatim after imports (+ import TailZ9; #print/example dropped); TailZ11 = OpenTextbookLeaves10 (17), textbookLeaves9_of_open10, sixContactMin_of_open10. Main switched.
- 13:20 build1 (lake build +Main) stopped by the harness's 10-min background limit at ~[12723/12900], no errors so far; restarted as build2 (long timeout).
- mk_fields10.py: counts leaf-fold9 63 (42/21 strict) -> dimjac 62 (42/20 strict, 53/9 lenient). Four reduct-split DVR leaves marked "pending the base review".
- verbatim_check10.py: TailZ10 = DimJacGlue.lean body (only #print x2 and example dropped). VERIFIED.
- 13:23 build2: `lake build +ZInQKernel.OneProof.Main` EXIT 0 (12900 jobs); frozenTarget axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- DumpCompact after: 11215 constants. Base Main restored temporarily, `lake build ZInQKernel.OneProof.Main` EXIT 0, DumpCompact before: 11123 constants, byte-identical to scratch/leaf-fold9/hashes_after.txt. New Main restored and rebuilt (EXIT 0).
- cmp_hashes: 0 removed, 1 changed (frozenTarget), 92 new, all in TailZ10/TailZ11. VERIFIED.
- Check10: sixContactMin_of_open10 standard axioms; closure 212325 constants, no sorryAx; 62 fields (30+17+14+1), 16 kernel heads; dimJacobianEqGenus, h0DifferentialsEqHolo, textbookLeaves9_of_open10 standard axioms; type of dimJacobianEqGenus is ZInQ.Contrib.CurvesG.DimJacobianEqGenus. VERIFIED.
- Note: build1.txt/build2.txt (partial build logs, no absolute paths) were committed by mistake in the first two commits; removed from the index, .gitignore added for build*/dump* logs.

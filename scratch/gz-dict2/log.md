# gz-dict2 log

Base wip/leaf-fold33b 943f1775 (origin/main c1e4ed1b already an ancestor: no merge needed). Build tree copied
from ~/dzq-wt/leaf-fold33b (.lake/build, lean/.lake).

## Compile log
- D2a.lean (HasQExp algebra: add, const, mul via Cauchy product over ℤ×ℤ, eq_zero): compiles, no errors (VERIFIED).
- D2a.lean +§2 (HasQExp.exists_ne_zero: no zeros high up), §3 (jFun, pt2, ptQ, polyFn, polyQ, ratFn, IsRatRep, hasQExp_polyFn, exists_isRatRep): compiles (VERIFIED).
- D2a.lean +§4 (HoloH, holoH_jFun, holoH_polyFn, identity theorem on ℍ: eventuallyEq_zero_transfer/_of_im_gt, eventually_ne_zero_of_im_gt), §5 (eventuallyEq_ratFn = D2, modPt_congr, modPt_eq_ratFn, isOptimalParam_congr): compiles (VERIFIED).
- D2a.lean +§6: leaf GrossZagierPlaneOptAt/Cd, bridges grossZagierAlgOptAt_of_plane, grossZagierAlgOptCd_of_plane, grossZagierFormulaCd_of_plane: compiles (VERIFIED).
- ZInQKernel/Contrib/OneProof/GrossZagierPlane.lean (= D2a.lean + module doc): `lake build ZInQKernel.Contrib.OneProof.GrossZagierPlane` succeeded (11397 jobs, file 8.0 s) (VERIFIED).
- scratch/gz-dict2/FoldCheck.lean (frozenTarget_gzdict2: Main's frozenTarget with hGZ : GZDict2.GrossZagierPlaneOptCd): compiles; axioms [propext, Classical.choice, Quot.sound] for frozenTarget_gzdict2, grossZagierAlgOptCd_of_plane, grossZagierFormulaCd_of_plane, modPt_eq_ratFn (FoldCheck-output.txt) (VERIFIED).
- scratch/gz-dict2/Discharges.lean: "DISCHARGES [hGZ] by ZInQ.GZDict2.grossZagierAlgOptCd_of_plane, still assumes [ZInQ.GZDict2.GrossZagierPlaneOptCd], axioms standard"; 37 open hypotheses, 9524 theorems checked, 39 discharge one (Discharges-output.txt) (VERIFIED).
- D1a.lean (WEqK, center_of_wEq: valuative criterion for E ⊂ P² in valuation form; center_of_wEq_subring for ValuationSubring ⊇ ℚ): compiles (VERIFIED).

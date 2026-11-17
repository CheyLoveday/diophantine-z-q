# gz-dict2 log

Base wip/leaf-fold33b 943f1775 (origin/main c1e4ed1b already an ancestor: no merge needed). Build tree copied
from ~/dzq-wt/leaf-fold33b (.lake/build, lean/.lake).

## Compile log
- D2a.lean (HasQExp algebra: add, const, mul via Cauchy product over ℤ×ℤ, eq_zero): compiles, no errors (VERIFIED).
- D2a.lean +§2 (HasQExp.exists_ne_zero: no zeros high up), §3 (jFun, pt2, ptQ, polyFn, polyQ, ratFn, IsRatRep, hasQExp_polyFn, exists_isRatRep): compiles (VERIFIED).
- D2a.lean +§4 (HoloH, holoH_jFun, holoH_polyFn, identity theorem on ℍ: eventuallyEq_zero_transfer/_of_im_gt, eventually_ne_zero_of_im_gt), §5 (eventuallyEq_ratFn = D2, modPt_congr, modPt_eq_ratFn, isOptimalParam_congr): compiles (VERIFIED).
- D2a.lean +§6: leaf GrossZagierPlaneOptAt/Cd, bridges grossZagierAlgOptAt_of_plane, grossZagierAlgOptCd_of_plane, grossZagierFormulaCd_of_plane: compiles (VERIFIED).

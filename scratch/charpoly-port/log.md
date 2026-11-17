# charpoly-port results log

Base: main bf737bfe7; merged origin/wip/degpoly-proof (0a9e6698) for `DegDet.DegHomogPoly`
(`ZInQKernel/Contrib/OneProof/DegEqDetTate/Reduction.lean`).

## Sources found (VERIFIED, read)
- No original FLT checkout on the host. The target theorem exists, ported to Lean 4.35 in a
  namespace-wrapped form (`namespace ZInQ.Contrib.CloudW03NeronSurj.FLT`), on
  `origin/cloud-b3/w13-recovery` (3360b4789) under `ZInQKernel/Contrib/CloudB3W13/Source/`
  (FLT @ 6e837e75, Apache-2.0). That branch is not merged into main.
- main already vendors 1,315 FLT modules (+48 reused) unwrapped under
  `ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT` (SOURCE_MANIFEST.json).

## Closure (COUNTED, tools/closure_w13.py, tools/missing_w13.py)
- closure of the theorem on w13-recovery: 1,586 ZInQKernel modules.
- not in the W16 vendor (descent stopped at W16 modules): 63 = 58 FLT modules + 1 FLT P2M.Util-
  dependent... + 4 W13 port shims (Compat.MvPolynomialCoeff, Compat.PresheafOfModulesMonoidal,
  Compat.TensorProductInduction, PortUtilExt), the shims dropped. 59 modules written by
  tools/convert.py to `ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/`
  (LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md copied; per-file "Modified for the Z-in-Q
  kernel" notice).

## Conversion rules (tools/convert.py)
- strip the W13 namespace wrapper / `open` of it / `r2nos_*` shim lines; `w03_*` -> `p2m_*`;
  `_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.` -> `_root_.`;
- imports: W13 module -> W16 local (manifest) or the new vendor dir; CloudW03NeronSurj.PortUtil ->
  CloudW02 P2M.Util;
- W16 NOTICE renames (tensorPow*, pullbackSection*, preserves*_opensMap, isInvertible_unit/top,
  monoidalCategory/symmetricCategory, IdealSheafData.IsInvertible -> IsCartierFLT, Module.depth, ...);
- `respectTransparency.types false` -> W16's `respectTransparency false`.

## Manual repairs (compile errors, build1/build2)
- S_IsLocalRing_flat_of_isScalarTower_...: lines 559-568 `simp only ...; exact map_zero _` ->
  `<;>`, `exact (map_add ..).trans ..` -> `first | exact congrArg₂ .. | ..` (simp closes more in 4.35).
- S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_...: line 122 `rfl` -> `try rfl`.
- S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle:
  line 508 `rfl` -> `try rfl`.
- S_MvPolynomial_isHomogeneous_..., S_AddCommGroup_exists_mvPolynomial_...: W16's global
  `respectTransparency false` makes `Module ℚ≥0 (MvPolynomial ι R)` synthesis time out; restored
  W13's `respectTransparency.types false` + `.instanceSearchTypes false`.
No statement changed.
- VERIFIED: lake build of Thm_..._exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle (new vendor) OK, 10647 jobs (build3.log).
- VERIFIED: lake build ZInQKernel.Contrib.OneProof.DegHomogPolyFLT OK (10796 jobs, build5.log); #print axioms of degHomogPolyEndDegree, degHomogPoly_of_degEndEq, degEndEqEndDegree_of_glue, degHomogPoly_of_glue: [propext, Classical.choice, Quot.sound] (Axioms-output.txt).
- VERIFIED (build6): flat_of_isFinite (finite endomorphism of PkgI3.AbVar is flat; miracle flatness, FLT's [n] argument generalized) and finiteEndSurjective : FiniteEndSurjective proved; degHomogPoly_of_finrankGeneric (h1 : FinrankGenericEqDegEnd) : DegDet.DegHomogPoly.
- VERIFIED: scratch/charpoly-port/FinrankAlg.lean compiles: CharPolyPortFinrank.finrank_genericPoint (FinrankGenericPoint in universe u; rank of finite flat surjective map of integral schemes at the generic point = function-field degree), axioms [propext, Classical.choice, Quot.sound].
- VERIFIED (build8, Axioms-output.txt): FinrankGeneric.lean moved to ZInQKernel/Contrib/OneProof/CharPolyPort/FinrankGeneric.lean; DegPolyFLT.degHomogPoly : DegDet.DegHomogPoly proved with no hypothesis; all standard axioms.
- VERIFIED: lake build +Main +Discharges +DegHomogPolyFLT +CharPolyCharP OK (16118 jobs, build9.log).
- VERIFIED #discharges (Discharges-output.txt): `DISCHARGES [OpenTextbookLeaves17.charPolyIndepOfEllAlgClosed] by
  charPolyIndepOfEllAlgClosed_proof, still assumes: [], axioms: [propext, Classical.choice, Quot.sound]`
  (scratch composition `CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly' DegPolyFLT.degHomogPoly`);
  summary line `#discharges: 36 open hypotheses, 13237 theorems checked, 37 discharge one`.
- autofold.py --dry-run (autofold-dryrun.txt): strict 15/16 on 31 -> 14/16 on 30; strictest 15/16 -> 14/16;
  OpenTextbookLeaves18 has no fields.
- VERIFIED: autofold dry-run module (AutofoldDryRun.lean = dry-run output minus line 1) compiles; HDec.HSyn.sixContactMin_of_open59 axioms [propext, Classical.choice, Quot.sound] (AutofoldDryRun-output.txt).

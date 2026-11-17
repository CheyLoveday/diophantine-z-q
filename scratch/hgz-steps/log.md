# hgz-steps log

Base: wip/hgz-steps at 222c98bf (main); merged origin/wip/leaf-fold33b (db99b5b4) and origin/wip/gz-dict2 (4fd8ddd2).

Targets: hGZ = ZInQ.GZAlg.GrossZagierAlgOptCd (binder of ZInQ.OneProof.frozenTarget).
- D1 scheme-level (phi^* -> morphism X0(N) -> E of schemes over Q), route exists_hom_of_valuationRing_stalk + NormalModelOfFunctionFieldQ_proof.
- D2 scheme-level (Heegner points as C-points of X, values through q-expansions).
- jacobiSym(n, |D|) = epsilon_D (Kronecker symbol) for D < 0, D = 1 mod 4.

## Entries
- EpsD.lean: epsD (Kronecker symbol) and epsD_eq_jacobiSym (D<0, D%4=1) compiled, axioms standard. VERIFIED
- SchCore.lean: ESch E = Proj (Tau Ceti grading), toSpecQ proper, chartZ, chartHom (+naturality), exists_extension (D1), mem_range_of_mem_chart, fromSpecStalk_comp_eq (separatedness), mem_chart_of_factor, comp_eq_of_factor, ptOf + ptOf_chart/ptOf_eq_zero: compiled, no sorry. VERIFIED. Copied to Contrib/OneProof/GrossZagierScheme/Core.lean

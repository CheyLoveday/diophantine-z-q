# sgr-split results log

Target: `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` (ZInQKernel/OneProof/H/TailW.lean:739).

## Statements
- Verbatim copy: `scratch/sgr-split/StatementCopy.lean` (namespace `HDec.SGRCopy`), `Iff.rfl` with the chain's. VERIFIED (compiled).
- New printed leaf `ShimuraIntegralModelRep` (representability over ℤ_(p), p > 324, on `QMAbScheme`; Kottwitz 1992 §5, Buzzard 1997, Morita 1981; locators UNVERIFIED). Flag: pending reading (level at 3 | D; PEL vs polarization-free).
- New textbook leaf `AbVarSurfaceRelDim` (AbVar of Krull dim 2 is SmoothOfRelativeDimension 2; locators UNVERIFIED).
- Glue `QMAbFieldFibre` (G1, not proved), `QML3AsQMAb` (G2, proved from AbVarSurfaceRelDim), `FibreClassUnique` (G3, proved).

## Compile outcomes (lake env lean / lake build; all standard axioms)
- 02:30 `SGR.lean`: `shimuraGoodReductionNoGuard_of_rep` compiled. VERIFIED.
- 02:32 `fibreClassUnique` compiled. VERIFIED.
- 02:35 `qml3AsQMAb_of` compiled. VERIFIED.
- 02:40 `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` built (86 s). VERIFIED.
- 02:41 `#discharges`: field discharged by `SGRSplit.shimuraGoodReductionNoGuard_of_printed`, still assumes [ShimuraIntegralModelRep, AbVarSurfaceRelDim, QMAbFieldFibre]; output `discharges.out`. VERIFIED.
- 02:43 autofold dry-run (`--allow-rise`): strict 46/13 on 59 -> 47/14 on 61; strictest 45/14 -> 46/15; generated module compiles (`sixContactMin_of_open26`, standard axioms). VERIFIED.

## Findings
- curve-split §3.6 "not statable": superseded; QMAbScheme supplies abelian schemes over a base with O-action and level 3.
- NOS (r7a) / Néron / BLR leaves concern models of abelian varieties; they do not produce a model of the curve. (Statements VERIFIED by reading; conclusion SPECULATIVE-free mathematical observation, STANDARD.)
- 02:48 `abVarSurfaceRelDim` proved (Smooth.exists_isStandardSmooth chart + ZInQ.Contrib.Dim stalk dimensions). VERIFIED.
- 02:57 G1 `qmAbFieldFibre_of : SmoothGeomConnIntegral → AbVarEndTorsionFree → QMAbFieldFibre` compiled (`G1.lean`, standard axioms). VERIFIED.
- 02:59 Contrib file rebuilt with G1; `#discharges`: still assumes [ShimuraIntegralModelRep, SmoothGeomConnIntegral, AbVarEndTorsionFree]; autofold dry-run 46/13 on 59 -> 48/13 on 61 (no rise), generated module compiles. VERIFIED.

## Current new leaves
- `ShimuraIntegralModelRep` (published, pending reading; GLUE until read).
- `SmoothGeomConnIntegral` (textbook: Stacks/EGA IV_2; locators UNVERIFIED).
- `AbVarEndTorsionFree` (textbook: Mumford AV §19; locators UNVERIFIED).

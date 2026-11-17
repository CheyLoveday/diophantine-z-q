# y3abu-print log

Base c1e4ed1b (wip/y3abu-print). Field: RayClassCFT.ShimuraMainThmIDeligneY3AbU (RayClassShimura.lean:1152).

## 16:52 contributor file compiles
- Build tree copied (reflink) from ~/dzq-wt/homfree-noemb (.lake/build, lean/.lake/build; same Main.lean, its diff vs c1e4ed1b only adds files).
- ZInQKernel/Contrib/OneProof/ShimuraY3Print.lean (namespace Y3ABUPrint): `lake env lean` OK, no errors (VERIFIED).
  - leaves: Y3FineModuliAb := ∃ Y Φ, R1fpPropsAb Y Φ; DeligneCanonicalModelY3Every := ∀ Y Φ, R1fpPropsAb Y Φ → ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ.
  - shimuraMainThmIDeligneY3AbU_of_print (discharge), y3FineModuliAb_of_field, deligneCanonicalModelY3Every_of_field
    (compare_iso_ab copied from elkies-print + body_transport; holomorphy via regVal_comp/isHolFamily_comp), print_iff_field.

## Clause read analysis (VERIFIED by reading the consumers at c1e4ed1b)
Consumers of the field: TailZ34 L81 shimuraFamilyAb_of_U, L101 rayClassCMAb_of_leaves, L148 DCY3Used.y3Connected_of_leaves
(TailZ35-45 only pass it on). Pending branch wip/grx6ab-print: x6ModuliWitness_of_coarse reads (Y, Φ, R1fpPropsAb).
- R1fpPropsAb: carried into the conclusions ShimuraFamilyAb, RayClassCMAb, Y3ConnectedAb (all ∃ Y Φ, R1fpPropsAb ∧ …); naturality read by obj_at.
- clause 1 surjectivity: read (embed_core L1377, connected_of_body).
- clause 1 fibres, direction DCRel → equal: read (embed_core L1380, L1439; connected_of_body L634).
- clause 1 fibres, direction equal → DCRel: UNREAD (only `.2` is ever applied).
- clause 2 holomorphy ∀ g: only the open-preimage half `(hhol g).1` read (connected_of_body); analytic half unread for g ≠ 1.
- clause 3 IsShimuraHolFamily at g = 1 (moduli + full holomorphy): read (shimuraFamilyAb_of_mainThmI).
- clause 4 reciprocity: read (embed_core, connected_of_body).
- ModuliAtUnits: read (obj_at).

## 17:00 build, #discharges, autofold dry-run (all VERIFIED)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3Print`:
  success, 14102 jobs; frozenTarget standard axioms (build-summary.txt).
- discharges.txt: `DISCHARGES [OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU] by Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print
  still assumes: [Y3ABUPrint.Y3FineModuliAb, Y3ABUPrint.DeligneCanonicalModelY3Every]`, axioms standard.
  `#discharges: 45 open hypotheses, 6687 theorems checked, 14 discharge one`. All four theorems: [propext, Classical.choice, Quot.sound].
- autofold.json --dry-run: strict 16/21 on 37 -> 18/20 on 38; strictest 16/21 -> 18/20 (-1 GLUE).
- FoldCheck.lean (dry-run minus line 1) compiles: sixContactMin_of_open39 standard axioms (foldcheck.txt).

## combined (VERIFIED)
- merged origin/wip/grx6ab-print (b047ce25; contains elkies-print and gr-dict). autofold-combined.json: three discharges
  (shimuraMainThmIDeligneY3AbU, gonzalezRotgerX6Ab, elkiesX6StarFunctionField), {n}.shimuraMainThmIDeligneY3AbU replaced by
  (Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print {n}.y3FineModuliAb {n}.deligneCanonicalModelY3Every).
- dry-run: strict 16/21 on 37 -> 21/18 on 39, strictest same (-3 GLUE).
- lake build GRX6AbPrint, ElkiesX6StarEvery, ShimuraY3Print: success (13023 jobs). FoldCheckCombined.lean compiles,
  sixContactMin_of_open39 standard axioms.

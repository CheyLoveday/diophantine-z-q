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

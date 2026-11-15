# gt-grcount results log

Target: `ShimuraSplit.GonzalezRotgerCountX6Ab` (ZInQKernel/OneProof/H/TailZ17.lean L31), field
`HDec.HSyn.OpenResearchLeaves16.gonzalezRotgerCountX6Ab`, strict GLUE (composite: witness + count).

## Findings (reading)
- VERIFIED (read TailZ9 L97, TailZ23 L804, grep of ZInQKernel): the field's only consumer is
  `r5count := ShimuraSplit.r5fpCount_of_points r.gonzalezRotgerCountX6` (TailZ9); i.e. the chain uses only
  `LeafQM.AV.R5fpCount` (ZInQKernel/HDecomp/QM/Leaves.lean L599); the witness (Y,Φ,X,Ψ,fY) is inert for the chain.
- VERIFIED (read): the count clause of the Ab form depends on the witness only through the bijection Ψ, so
  R5fpCount + any witness of `R1fpPropsAb ∧ X6Props` gives the Ab form (same proof as TailZ8 `points_of_r5fpCount`).
- VERIFIED (read TailZ22 L64): the open LEAF `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (GR 2006 Thm 5.12) supplies
  such a witness; so does `ShimuraGlue.DeligneComponentsX6PrintedAb` (TailZ22 L33).
- Finite computation? NO: R5fpCount quantifies over all imaginary quadratic orders R (h(R) unbounded) and its
  left side counts isomorphism classes of QM abelian surfaces over Qbar; nothing to `decide`. The only
  finite/arithmetic content is the local factor: 2^{inertCount6 k} = ∏_{p|6}(1-(k/p)) when no p|6 splits
  (Eichler's local optimal-embedding numbers), which is glue (proved below).

import ZInQKernel.Contrib.OneProof.C8Dicts
import ZInQKernel.Contrib.OneProof.C8Twist
import ZInQKernel.Contrib.OneProof.C8Poincare

/-! # c8-conrad3: step C8 from its two printed leaves

c8-conrad2's C8 reroute (`C8Poincare.C8Inputs`, five fields) had two leaves and three open glue Props. The three glue
Props are now theorems (`twistCharHTWt0_proof` in `C8Twist`, `inertiaAtPDecomp_proof` and `minkowskiInertiaQ_proof` in
`C8Dicts`), so the reroute's inputs are the two leaves of `C8Leaves`:

* `conradAppBQp` — Conrad, *Lifting global representations with local properties* (author preprint, Dec. 11, 2011),
  App. B, pp. 32-33, base field `ℚ_p`: the manuscript's citation at step C8 (diophantine_zq.tex L761,
  bibitem `conrad-local-characters` L11046-11049); unread on this host;
* `tateTwistInvariantsInertia` — Tate, *p-divisible groups* (1967), §3.3, Thm 2, for the completion of `K^{ur}`
  (locator UNVERIFIED): a source the manuscript does not cite (it proves the manuscript's uncited step L763-764).

`g12DetPZ_of_printed` is the term for the C8 swap at `g8_g12_of_leaves3_hf_pz_eb` with these two leaves only. -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

/-- **The printed leaves of the C8 reroute** (every glue input of c8-conrad2's `C8Inputs` is now proved). -/
structure C8Leaves : Prop where
  conradAppBQp : ConradAppBQp
  tateTwistInvariantsInertia : TateTwistInvariantsInertia

/-- c8-conrad2's `C8Inputs` from the two leaves (the three glue fields are theorems). -/
theorem c8Inputs_of_leaves (l : C8Leaves) : C8Inputs where
  conradAppBQp := l.conradAppBQp
  tateTwistInvariantsInertia := l.tateTwistInvariantsInertia
  twistCharHTWt0 := twistCharHTWt0_proof
  inertiaAtPDecomp := inertiaAtPDecomp_proof
  minkowskiInertiaQ := minkowskiInertiaQ_proof

/-- **C8 (the twist has finite image) from Conrad's App. B and Tate's theorem over `\hat{K^{ur}}`**, with R13 and R14
(diophantine_zq.tex L758-766). -/
theorem c8TwistFinite_of_printed (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppBQp) (hTT : TateTwistInvariantsInertia) : C8TwistFinite :=
  c8TwistFinite_of_leaves hR hHT hC hTT twistCharHTWt0_proof inertiaAtPDecomp_proof minkowskiInertiaQ_proof

/-- **C8's consumer `G12DetPZ` from the two printed leaves** (the replacement term at `g8_g12_of_leaves3_hf_pz_eb`:
`g12DetPZ_of_printed r.r14 r.r13 m.c8.conradAppBQp m.c8.tateTwistInvariantsInertia h9 r.r10`). -/
theorem g12DetPZ_of_printed (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppBQp) (hTT : TateTwistInvariantsInertia) (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) :
    G12DetPZ :=
  g12DetPZ_of_twistFinite (c8TwistFinite_of_printed hR hHT hC hTT) h9 hdR

end HDec.G0Galois.C8Conrad

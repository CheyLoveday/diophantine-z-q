# neron-ext results log

Base: origin/main 0caafe66 (w80). Build copied (reflink) from ~/dzq-wt/homfree-proof (base 0caafe66, only a new Contrib file).

## Statement (VERIFIED, read)
`ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (ZInQKernel/Contrib/NeronC/NeronGroup.lean:82): for every field K,
AbVar A/K, number field L ⊇ K: a smooth, separated, qc `N` over Spec 𝓞_L with `e : N_L ≅ A_L` such that every
L-morphism `Y_L → A_L` (Y smooth over 𝓞_L) extends to `Y → N`. = existence half of BLR §1.4 Thm 3 over 𝓞_L.

## Consumers (grep, VERIFIED)
- TailM L387 `t41_of_extension5` → T41 `ZInQ.H5Neron.NeronModelExists` (TailN L225, TailO L2875):
  feeds the stable-Faltings-height rows (TailY: r18–r22, heightAdditivity), at every finite L.
- TailZ4 L153/L173 `neronModelExists_of_extension` → N1 for R20 (heightRows_of8).
- TailZ26 L174/L182 `GapNeron.neronSchemeModelExistsNF` (N1 at L = K, then BLR 1.2/4 to DVRs O of K) →
  r6 at number fields (`raynaudCriterionNF_of14`: Raynaud's criterion, used to PROVE semistable/good reduction of
  QML3 objects and in the G15/LTLocal chain) and SS1/SS3 (`ss1_ss3_of14NF`, semistable reduction theorem).
- Field passing only: TailX L145, TailZ9 L76, TailZ11 L29, TailZ32 L25, TailZ42 L24 bundles.

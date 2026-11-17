# d2a6b results log

Base: fork main d435851d; merged origin/wip/d2a6-reroute (698c8c9e) and origin/wip/y3-route-a (6558e2ff), both clean
(merge commits f72326f9f, 41f61097c).

## Step 1: A6 on Y3FullThreeRepZ30

- Comparison (VERIFIED by reading the Lean files):
  - A6IntModel's `hasGoodReduction_of_intModel` uses ShimuraIntegralModelRep only at p: (i) the universal property at
    the one base `Spec K` (K ⊇ ℚ, a field; locally noetherian) for the object `qml3AsQMAb_of PK`; (ii) properness of
    `𝒴 → Spec ℤ_(p)` (valuative criterion); (iii) the universal family's proper/smooth/geomConn/grp/one_eq;
    (iv) uniqueness of maps to Spec ℤ_(p).
  - Y3FullThreeRepZ30 gives: 𝒴 proper smooth over ℤ[1/30], universal `QMAbSchemeP` (Mumford-form level), universal
    property on locally noetherian ℤ[1/30]-schemes for `QMAbSchemeP` objects.
  - Objects: QMAbScheme (kernel level: injective on field fibres) vs QMAbSchemeP (printed level: bijective onto A_s[3]
    at geometric points). Bridges, both already proved in the tree: `Y3Fix.toKer` (P → kernel, same QMFamily, any base)
    and `Y3Fix.ofKer hT` (kernel → P over ℚ-schemes, from the proved mumfordTorsionAlgClosed). A6 needs the bridge only
    at Spec K, a ℚ-scheme. No new bridge; nothing on the spot.
  - Polarization: both leaves are polarization-free (both carry the same relative-Lemma-P reading point).
  - Primes: ℤ[1/30] model covers every p ∤ 30 ⊇ {p > 324}; `not_dvd_thirty_of_lt`.
- New file ZInQKernel/Contrib/OneProof/A6Z30.lean: spec_to_Z30_ext, z30To, not_dvd_thirty_of_lt, z30ToLocal,
  hasGoodReduction_of_z30, qmModelG3U_of_z30, modelG3G6_of_leavesU_z30.
- D2A6Wrap.lean edited: R6U := RaynaudWildNF ∧ Y3FullThreeRepZ30; modelG3G6_of_leaves3U and good_of_QML3U use the z30
  theorems.
- `lake build ZInQKernel.Contrib.OneProof.A6Z30`: success (14376 jobs, 0 errors; build-a6z30.txt). VERIFIED axioms
  [propext, Classical.choice, Quot.sound] for spec_to_Z30_ext, z30ToLocal, hasGoodReduction_of_z30, qmModelG3U_of_z30,
  modelG3G6_of_leavesU_z30.

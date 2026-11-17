# hcm-lattice: `hCM` as a direct instance of Shimura 1971 Thm 5.4

Task hcm-lattice, 2026-11-17. Base: wip/leaf-fold33b d879bb73. Log: `scratch/hcm-lattice/log.md`. Lean:
`scratch/hcm-lattice/HCMLattice.lean` (proposed path `ZInQKernel/Contrib/OneProof/HCMLattice.lean`; it imports only
`ZInQKernel.Contrib.OneProof.ShimuraMainCM`).

## 1. Result

The reviewer's two steps between the print and hcm-dict's leaf `HCMDict.ShimuraThm54` are both closed in Lean, and
the step that the task allowed to become a Silverman leaf is proved, so no new leaf enters:

* **`ShimuraThm54Local`** (new `def`, the old one kept) states Shimura's Thm 5.4 with
  * the print's hypothesis on `ξ`: `IsAnalyticIso`, an analytic isomorphism `ℂ/𝔞 → E(ℂ)` defined over `ℙ²(ℂ)`
    coordinates (bijection `ℂ/κ𝔞 → E(ℂ)`, holomorphic lift to `ℂ³ ∖ 0` near every point, nowhere vanishing
    differential), plus the group law;
  * the print's `s⁻¹𝔞`: any lattice `𝔟` with `𝔟_p = s_p⁻¹𝔞_p` for every prime `p`, in `K_p = ∏_{v∣p} K_v`;
  * the print's `s⁻¹u`: `v` represents `s⁻¹u` when `v ≡ s_p⁻¹u (mod 𝔟_p)` for every prime `p`.
* **`shimuraMainCM_of_local : ShimuraThm54Local → T5Glue.ShimuraMainCM`** (what the consumers of `hCM` use), compiled,
  standard axioms only.
* **Manual Main fold** `scratch/hcm-lattice/FoldCheck.lean`: `frozenTarget_hCMLocal`, the `Main.lean` body with
  `hCM : HCMLattice.ShimuraThm54Local` and `HCMLattice.shimuraMainCM_of_local hCM` at both uses, compiles against the
  built `Main`; axioms `[propext, Classical.choice, Quot.sound]` (`FoldCheck-output.txt`).

**Count.** `hCM` was rated `consequence / GLUE / GLUE` (Addendum 2). With the new leaf it is proposed
`published (unread) / LEAF / LEAF`, pending a reviewer: TYZ/GZ hypotheses strict GLUE 4 → 3; H part unchanged
(16/18); over all hypotheses 17/22 → 18/21. No other count rises: the Weierstrass-map step is proved (no Silverman
leaf), and no new GLUE `def` is introduced.

(Details, proofs and open points: sections 2–5, completed below.)

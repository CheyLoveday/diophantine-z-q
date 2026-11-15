# c-to-printed2 results log

Fields: `r17 : LadicCond.CarayolR17'`, `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists`,
`eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew` (leaf-fold10 §2, all GLUE (c)).
Base e38375b3. Compile command: `lake env lean scratch/c-to-printed2/<file>.lean` (prebuilt oleans in the worktree).

## 2026-11-14

- `HTDual.lean` (imports `OneProof.H.TailT`): **VERIFIED** compiles, `#print axioms CToPrinted2.htDual_proof` =
  `[propext, Classical.choice, Quot.sound]` (about 70 s).
  - `htDual_proof : TateTwistInvariants → AxSenTate → HTDual`. `HTDual` and `dualGR` are modular-split's
    (`scratch/modular-split/EigenHT.lean`), copied verbatim into namespace `CToPrinted2`.
  - Route: pairing `Y_i(ρ) × Y_j(ρ^∨) → ℂ_ℓ(−i−j)^{G_E}` (`pair_twist`; zero by Tate, in `E` by Ax–Sen–Tate);
    hodge-split's `exists_basis_Ysp`; the dual basis lies in `Y_{−j}(ρ^∨)` (`cvec_mem`); `finrank_Ysp_dual`,
    `finrank_Ysp_dual_eq`; hodge-split's `htMult_eq_finrank_Ysp`.
  - Consequence: modular-split's glue `HTDual` is closed by two existing bundle LEAF fields (`tateTwistInvariants`,
    `axSenTate`).

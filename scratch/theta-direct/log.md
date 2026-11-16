# theta-direct results log

Task theta-direct, started 2026-11-16 00:00 PST. Base a40d5c4d (wip/theta-direct = fork main + STATUS w76).

## Step 0: merge of origin/wip/theta-fold (8e3dbdea)
* `git merge --no-edit origin/wip/theta-fold`: CONFLICTS in STATUS.md, ZInQKernel/OneProof/Main.lean,
  docs/one-proof/{CONTRIBUTING.md,OPEN.md,open-statements.json,pages-wanted.md},
  scratch/contrib-kit/DischargesTest-output.txt. Merge aborted (`git merge --abort`), as instructed. VERIFIED.
* Went the copy route: theta-fold's definitions copied verbatim into helper modules under
  ZInQKernel/Contrib/OneProof/ThetaDirect/ (each file names its source and line range):
  * UseForm.lean: theta-fold TailK.lean l.283-346 (`ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero`,
    `thetaPointOfFibre_of_qm_atQM`);
  * Kron.lean, Split.lean, Glue.lean: theta-fold's LinYangKron/LinYangSplit/LinYangGlue (import lines only changed);
  * Printed.lean: theta-fold LinYangPrinted.lean l.4-100 (siegelEis, igusaChi10E/12E, IgusaThetaExpressions) and
    l.139-210 (thetaConst_omega_analyticAt); linyang-printed LinYangPrintedFull.lean l.2993-3310 (modularity of
    siegelEis) and l.3330-3338. `LinYangEx29All` / `LinYangEx29` NOT copied.

## Plan (no Lin–Yang)
* Valence (proved in kernel: ValenceFormulaGammaStar from valenceFormulaCocompactEq_proof + shimizuCovolumeO1_proof;
  EllipticOrderDvd = ellipticOrderDvd_proof): a holomorphic weight-2m form for Γ* vanishing at r pairwise
  inequivalent points where a second weight-2m form is nonzero vanishes identically once 12r > m.
* Automorphy of ψ₆∘Ω, χ₁₂∘Ω (normalized) from siegelEis modularity + IgusaThetaExpressions + GammaStarGen.
* R1: ψ₆·Σθ⁸ = c₁·∏θ² on Ω(ℍ) (weight 20, one node τ₂₄); R2: (Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)² (weight 40,
  nodes √2+i and τ₂₄). c_i algebraic from algebraic theta ratios at the nodes (CM24 at Ω₂₄; genus one at Ω₀).
* Then e_k(θ⁸)/(Σθ⁸)^k algebraic where j_θ ∈ ℚ∖0 (IgusaAlg k, weighted homogeneity) ⇒ ThetaRatiosAtQM.

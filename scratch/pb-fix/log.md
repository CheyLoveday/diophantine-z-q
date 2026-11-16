# pb-fix results log

## 2026-11-15 22:36 start
- Base c1636db9 (pb-bypass); fast-forwarded to origin/wip/pb-sanity 9dbaabbd3 (pb-sanity reported: B_cris ≠ 0, t not
  nilpotent, etc., in ZInQKernel/Contrib/OneProof/PanBergerSanity.lean). VERIFIED (git merge --ff-only).
- Build tree: copied ~/dzq-wt/pb-sanity/.lake/build (same commit 9dbaabbd3) into .lake/build (old one moved to .lake/build.old).
- Plan: new file ZInQKernel/Contrib/OneProof/PanBergerFix.lean:
  * K0 K := ℚ_p(prime-to-p roots of unity in K) (max. absolutely unramified subextension).
  * IsSemistableOverT: tensor form (B_st ⊗ V^*)^{G_K}, normalized by finrank K0 (explicit [K_0:ℚ_p]).
  * BergerPrintedT := BergerDR LocalIsPstT.
  * PanPrintedT: ∀ ι_p : ℚ̄_p ≃+* ℂ, tr ρ(σ_arith) = ψ(σ) ι_p^{-1}(a_q(g)) (no algebraicity in the leaf).
  * glue: PanFor LocalIsPstT from PanPrintedT + DSThm965 + DSThm966 (r14Det_of_printed) + Steinitz.

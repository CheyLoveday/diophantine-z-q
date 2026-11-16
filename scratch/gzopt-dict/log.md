# gzopt-dict results log

Base: wip/period-odd 6382ef59, merged origin/main e41a7169 (merge 812b36c0). Build tree copied from ~/dzq-wt/period-odd.

## Statements (ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean, namespace ZInQ.GZAlg)
- Model of Q(X0(N)): vendored FLT `ModularCurve.modularFunctionField N` = Q(jq, jq(q^N)) ⊂ LaurentSeries Q (abbrev `X0Field`).
- `HasQExp X x`: X(τ) = Σ_{m∈ℤ} x_m q^m for Im τ > T.
- Leaf `Gamma0QExpansion`: IsRatModFnMero N g → HasQExp g x → x ∈ X0Field N (Shimura 1971 Prop 6.9, UNVERIFIED).
- Leaf `GrossZagierAlgOptAt E`: φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N, ord φ(x) < 0, X Y meromorphic with q-expansions φ(x), φ(y), IsOptimalParam, rest as GZOptimal.GrossZagierModuliOptAt.
- `GrossZagierAlgOptCd` (restriction to short models in the isogeny class of C_d).
- compile: `lake env lean` OK, no errors (VERIFIED).
- §2 algebra (aeval_ne_zero_of_order_neg, psi0, psi0_injective via Ideal.eq_bot_of_under_eq_bot, phiOf via IsFractionRing.liftAlgHom, eval₂_polynomial_of_wEq): compiles (VERIFIED). Pitfall: Algebra ℚ (LaurentSeries ℚ) diamond between IntermediateField's instance and default; bridge with Subsingleton.elim on ℚ →+* L.
- §3 analysis (le_radius, regularAt_of, hasQExp_laurentOf, tay_weq, tay_eq_zero_of_punctured, wEq_laurent, wEq_of, order_neg_of) and §4 bridge (grossZagierModuliOptAt_of_alg, grossZagierModuliOptCd_of_alg, grossZagierFormulaCd_of_alg): whole file compiles with lake env lean, no errors/warnings (VERIFIED, 11-16 ~16:40).

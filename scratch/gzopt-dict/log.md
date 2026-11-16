# gzopt-dict results log

Base: wip/period-odd 6382ef59, merged origin/main e41a7169 (merge 812b36c0). Build tree copied from ~/dzq-wt/period-odd.

## Statements (ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean, namespace ZInQ.GZAlg)
- Model of Q(X0(N)): vendored FLT `ModularCurve.modularFunctionField N` = Q(jq, jq(q^N)) ⊂ LaurentSeries Q (abbrev `X0Field`).
- `HasQExp X x`: X(τ) = Σ_{m∈ℤ} x_m q^m for Im τ > T.
- Leaf `Gamma0QExpansion`: IsRatModFnMero N g → HasQExp g x → x ∈ X0Field N (Shimura 1971 Prop 6.9, UNVERIFIED).
- Leaf `GrossZagierAlgOptAt E`: φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N, ord φ(x) < 0, X Y meromorphic with q-expansions φ(x), φ(y), IsOptimalParam, rest as GZOptimal.GrossZagierModuliOptAt.
- `GrossZagierAlgOptCd` (restriction to short models in the isogeny class of C_d).
- compile: `lake env lean` OK, no errors (VERIFIED).

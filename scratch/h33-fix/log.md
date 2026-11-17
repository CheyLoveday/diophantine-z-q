# h33-fix log

- 11-17 00:00 merged d489fc13 (h33-dict: TYZThm33.lean, scratch/h33-dict). Base 222c98bf.
- Plan: leaf `TYZThm33Alg` with i₀ an algebraic isomorphism given by i₀^* : ℚ(A) ≃ₐ[ℚ] X0Field 32 (= ℚ(j, j_32) ⊂ ℚ((q)),
  vendored FLT, as gzopt-dict's GrossZagierAlgOptCd), i₀(∞)=O as ord_q i₀^*(x) < 0, X,Y holomorphic on ℍ with
  q-expansions i₀^*(x), i₀^*(y). Dictionary in Lean: eta model gives such an i₀ (needs surjectivity:
  jq, jq(q^32) ∈ ℚ(x_eta, y_eta)), via E4/E6 in thetas (Mathlib rank one) + Landen (jacobi-lambda).

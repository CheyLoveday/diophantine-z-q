# h33-fix log

- 11-17 00:00 merged d489fc13 (h33-dict: TYZThm33.lean, scratch/h33-dict). Base 222c98bf.
- Plan: leaf `TYZThm33Alg` with i₀ an algebraic isomorphism given by i₀^* : ℚ(A) ≃ₐ[ℚ] X0Field 32 (= ℚ(j, j_32) ⊂ ℚ((q)),
  vendored FLT, as gzopt-dict's GrossZagierAlgOptCd), i₀(∞)=O as ord_q i₀^*(x) < 0, X,Y holomorphic on ℍ with
  q-expansions i₀^*(x), i₀^*(y). Dictionary in Lean: eta model gives such an i₀ (needs surjectivity:
  jq, jq(q^32) ∈ ℚ(x_eta, y_eta)), via E4/E6 in thetas (Mathlib rank one) + Landen (jacobi-lambda).
- Numerics (VERIFIED, scratch/h33-fix/py/theta_j_check.py, double precision, 3 points): E4 = ½(θ2⁸+θ3⁸+θ4⁸),
  E6 = ½(θ3⁴+θ4⁴)(θ2⁴+θ3⁴)(θ4⁴−θ2⁴), j(τ) and j(32τ) as rational functions of the eta model (x,y), rel. err ≤ 5e-7.
- ThetaE.lean COMPILES (VERIFIED): e4T_eq, e6T_eq (rank one, Mathlib), j_theta, j_eta (j(τ)·jDen(x,y) = jNum(x,y),
  jDen ≠ 0), j32_eta (j(32τ)·j32Den(x) = j32Num(x)). Needed `lake build ...JacobiLambdaDeriv` first (11342 jobs).
- 00:50 ZInQKernel/Contrib/OneProof/TYZThm33Alg.lean + TYZThm33Alg/ThetaJ.lean: lake build success (VERIFIED, build-output.txt). jq_rel/jq32_rel need maxHeartbeats 4e6 (instance defeq on LaurentSeries ℂ).
- 01:00 #discharges (VERIFIED): DISCHARGES [h33] by ZInQ.H33Fix.tyzThm33_of_alg, still assumes
  [T5Glue.ShimuraMainCM, ZInQ.H33Fix.TYZThm33Alg]; axioms standard. FoldCheck frozenTarget_h33Alg compiles, rfl-equal.
- TYZ source re-read (VERIFIED): L1173-1174 "isomorphic to (X_0(32),∞). Fix an identification i_0"; L1296-1311 display.
- Report docs/research/h33-fix.md; autofold.json; kinds-row.tsv.

# heegner-32 results log

## Setup (2026-11-16 00:00 PST)
- Base 60a3fac7 + merge origin/wip/gz-weil ad22e947 (commit 6c5f81e4). gz-heegner (58a780e4) is an ancestor.
- Build tree copied from ~/dzq-wt/gz-moduli (identical ZInQKernel/ and lean/ trees). HeegnerCd builds (VERIFIED).

## Numerics: the period lattice of f_d versus the lattice L of C_d (scratch/heegner-32/py/periods.py)
- Periods Phi_d(γτ) − Phi_d(τ), γ = (a b; 32d²·k, dd) ∈ Γ₀(32d²), computed from ellan (40 digits, ≤ 4·10⁴ terms),
  coordinates in PARI's basis (ω₁, ω₂) of L (g₂ = 4d², g₃ = 0, the lattice of `IsPeriodLattice C_d`).
- d = 5: 12 periods, all with integer coordinates, including (−1, 0) and (0, 1). So Λ_{f_5} = L and
  c = 1 satisfies `PeriodsIn f c L` (VERIFIED, computed; numerical, 6 decimals).
- d = 13: periods include (−1, 0), (0, 2), (0, 3): Λ_{f_13} = L, c = 1 admissible (VERIFIED, computed).
- Consequence: `HeegnerPointRationalCd` quantifies over odd `c` that really occur. Any route through the level-32
  parametrization of 32a1 (gz-weil's twist, `g Φ_d(τ) = Σ_a χ(a) Φ₁(τ + a/d)`, g² = d) reaches only `c ∈ 2ℤ`:
  the lattice of 32a1 is `L' = ((1+i)/2) Λ₁` (Λ₁ = gL the lattice of C₁), and `z ↦ c z` maps `ℂ/g⁻¹L'` to `ℂ/L`
  iff `c ∈ 2ℤ`.

## Lean results (2026-11-16 ~01:00 PST)
- `scratch/heegner-32/Used.lean` compiles (VERIFIED, `lake env lean`): `X0ModuliGaloisParamCd` (the used instance of
  `X0ModuliGaloisMero`: level `N` of the newform of `C_d`, functions `x∘φ, y∘φ, 1/(x∘φ − t)`, Heegner points of one odd
  fundamental discriminant), `x0ModuliGaloisParamCd_of_mero`, `heegnerPointRationalCd_of_used (hCM) (hX)`.
  Copied to `ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd/Used.lean` (builds).
- `scratch/heegner-32/Twist.lean` compiles (VERIFIED):
  * `weierPt_short_add` (additivity of `weierPt` for `y² = x³ + Ax`, from the vendored uniformization theorem
    `PeriodPair.isUniformization_toPoint`);
  * `exists_c0`: for every lattice `L'` of 32a1, `(x, y)(σ) = weierPt 32a1 L' (Φ₁(σ) + c₀)` on ℍ (℘' sign by
    differentiating with `etaModelDifferential`);
  * **`weierPt_two_eichlerCd`**: `weierPt C_d L (2Φ_d(τ)) = S_{λg}(Z(τ)) + S_{λ̄g}(Z(τ))`,
    `Z(τ) = Σ_{a mod d} (a/d)(x, y)(τ + a/d)`, `S_μ(x, y) = (μ²x, μ³y)`, `λ = (1+i)/2`, `g = gaussD d`;
  * `map_psiMap`: `σ ∘ Ψ = Ψ ∘ (±σ)`, sign `σ(g)/g`;
  * `TwistTransportCd` (GLUE Prop), `HeegnerPointRationalCdEven`, `heegnerPointRationalCdEven_of_twist`;
  * `heegner_at_even`, `grossZagierHeegnerCd_of_even`, `grossZagierHeegnerCd_of_twist`:
    `GZStatements.GrossZagierHeegnerCd` from `TwistTransportCd`, `GrossZagierFormulaCd`, `GrossConjugationCd`
    (the constant `c` of the parametrization replaced by `2·num(c)`).

## Numerical check of `TwistTransportCd` (scratch/heegner-32/py/twist_check.py)
- d = 5, D = −31 (h = 3), β = 113, level 800: the three `Z_Q ∈ 32a1(ℂ)` computed from PARI's `eta` (250 digits
  requested, ~15 digits reached at Im τ ≈ 0.0035). The polynomials `∏_Q (X − x(Z_Q))` and `∏_Q (X − √5·y(Z_Q))`
  have rational coefficients to ~15 digits (e.g. constant term of the second `3182911.1197037037… = (3182911·3375 + 404)/3375`;
  the others found by `algdep` as degree-1 or squares). Consistent with `σ(Z_Q) = (σ(√5)/√5)·Z_{πQ}` (VERIFIED, numerical).

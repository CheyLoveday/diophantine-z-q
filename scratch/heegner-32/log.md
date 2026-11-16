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

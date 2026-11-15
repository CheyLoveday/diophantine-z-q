# h33-sign results log

Task h33-sign (2026-11-15). Target: `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (ZInQKernel/OneProof/TYZSplit.lean),
pending-review flag: the sign of `[i]` in `tyzZn` (z_n for n ≡ 5 mod 8). Source: ~/tyz-src/Period7.tex (Lnnnn).

## Setup
- Build tree copied from ~/dzq-wt/r16-split (same ZInQKernel sources as base 24f97774; no diff). Probe
  `import ZInQKernel.OneProof.TYZSplit` compiles (2m10s). VERIFIED.

## Source reading (VERIFIED, read in Period7.tex)
- L1174: "Fix an identification i_0:(X_0(32),∞)→A" (arbitrary; Aut_Q(A,O) = ±1).
- L1191-1193: f_0 : X_U → X_0(32) natural projection; geometric components of X_U parametrized by Spec Q(i);
  X_U ≅ X_0(32)_{Q(i)} "easy to figure out" — no choice of the square root of −1 in Γ(X_U,O) is printed.
- L1198: f_n = f_0 − f_0∘[i] (n ≡ 5). By L1192 alone `[i]` is defined only up to `[i] ↔ [−i]`.
- L1203-1205: embedding n≡5: √−n ↦ [[−1,1/4],[−4(n+1),1]]; fixed point h: 16(n+1)h² − 8h + 1 = 0 = kernel tyzForm.
- L1245-1252: P_n = [h,1] ∈ X_U(C), h ∈ H the fixed point; z_n = f_n(P_n).
- L1379-1404: τ : C/(1+i)Z[i] → A(C) analytic (C-linear), normalized by τ(1/2)=[0], τ(i/2)=[1/4], τ(1)=[1/16],
  τ((1±i)/2)=[±1/8].
- L1408-1413 Thm 3.6(1): for n ≡ 5: z^{σ_ϖ} = z + τ((1+i)/2), z^{σ_{1+2ϖ}} = z, z̄ = −z + τ(1).
- L1484-1567 (proof of Prop 3.5 = heckeaction5): R,S,T,α,β,γ computed on the cusps [∞]=[∞,1], [0]=[∞,w]
  (w = [[0,1],[−1,0]], det 1: identity component, the component of P_n=[h,1]); equations solved with the
  C-linear τ ("τ((1−i)/2) = ατ(1/2) + τ(1/2)", L1564) give α = −i, β = 1, γ = i (L1566). So TYZ identify
  μ_4 ⊂ Aut_{Q(i)} with μ_4 ⊂ C through the identity component: there `[i]` is complex multiplication by +I.
- L1584: f_n = f_0∘[1−i]. L1636-1649: proof of z̄_n = −z_n + τ(1) via j = [[1,0],[8,−1]], P̄_n = P_n^j.

## Lean: scratch/h33-sign/Sign.lean (imports ZInQKernel.OneProof.TYZSplit) — VERIFIED compiled
- `lake env lean scratch/h33-sign/Sign.lean`: 0 errors; output in Sign.out; axioms of
  `tyzThm33With_iff_of_reading`, `basePt_reading`, `torsion_of_alt_thm36`, `tyzThm33Copy_iff`:
  [propext, Classical.choice, Quot.sound].
- `TYZThm33Copy` = verbatim copy of kernel L157–176 (diff-checked), `Iff.rfl`.
- `TYZThm33With z` (basePt replaced by z); `TYZThm33 ↔ TYZThm33With basePt` is `Iff.rfl`.
- `zAlt n = P + [i]P = iPt (tyzZn n)`; `conj_zAlt`: c(zAlt) = zAlt − τ(1) (from kernel T321.tyzThm36ConjFive_of,
  i.e. Fricke + τ↦τ+1/4, all proved; hypothesis CMAlgebraic only).
- `torsion_of_alt_thm36`: if zAlt satisfied TYZ Thm 3.6(1) (z̄ = −z + τ(1)) then f₀(P_n) is torsion.
- `tyzThm33With_imp`/`_iff`: TYZThm33With depends on z n only up to sign or "both torsion".
- MAIN `tyzThm33With_iff_of_reading (hA : CMAlgebraic) zT h5 h36 h7 : TYZThm33With zT ↔ TYZThm33`
  for any zT of TYZ's shape (±(P∓[i]P) for n≡5, ±f₀(P_n) for n≡7) satisfying TYZ Thm 3.6(1) conj part.
- `basePt_reading`: the kernel's basePt satisfies the hypotheses (non-vacuity).

# hodgetate-from-dr results log

## 2026-11-16 15:00 setup
- Merged origin/main: already up to date; origin/wip/integrate-w82 already in HEAD (5e235a40a).
- lean/.lake/build was missing (unknown module prefix 'ZInQ'); copied from ~/dzq/lean/.lake/build (lean/ZInQ identical, diff -rq empty).

## Consumers of the field (VERIFIED by grep)
- `HodgeTateDecompAbVar` (ZInQKernel/OneProof/H/TailS.lean:347) is read in exactly one place:
  TailX.lean:195, `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT`
  (all other occurrences are bundle-to-bundle copies in TailZ*).
- `deRhamComparisonHT_of_leavesT` uses it for (i) `htMultOver w = g([w=0]+[w=-1])` (via `htMultOver_of_decomp`)
  and (ii) `FiniteDimensional ℚ_p V_p(A)` (via `finiteDimensional_of_decomp`). So the consumer needs the HT
  multiplicities and finite-dimensionality, i.e. the full numerical content; nothing smaller.

## Kernel inventory (VERIFIED by reading)
- No Hodge filtration on D_dR, no H^1_dR, no gr^i B_dR = C_p(i) in the kernel (grep "Fil", "Hodge filtration").
- KerTheta: B_dR^+ DVR with uniformizer xi, theta^+ : B_dR^+ -> C_p surjective with kernel (xi). No t = log[eps].
- `deRhamH1AbVarT` gives only dim_F D_dR(V^vee) = dim V (no filtration data).
- kinds.tsv flag of hodgeTateDecompAbVar: GLUE only because the coordinate form C(1)^g + C^g needs dim t*_{A'} = g.

## 15:45 HTPairing.lean §1-§2 (import TailS only) — COMPILES (VERIFIED, lake env lean, no errors)
- §1: TailS §6 generalized from (g,g) to (a,b): `htSpaceOver_eq_map2`, `finrank_htSpaceOver_of_decomp2`, `finrank_PSub2`.
- §2: `eq_of_pairing`: given e : C_p ⊗ V ≅ C_p^a × C_p^b (G_F-equivariant, first factor twisted by χ) and a
  nondegenerate B on V with B(ρσx, ρσy) = χ(σ) B(x,y), then a = b (from Tate's two theorems).
  Proof: Hom_{G_F}(V, C_p(1)) = Ψ_B((C_p ⊗ V)^{G_F}); count the left side via e (a·[F:Q_p]) and the right side via e (b·[F:Q_p]).
  `add_eq_finrank`: a + b = dim V.
- Importing TailX instead of TailS makes the same file time out in typeclass search (Module.Free, IsTorsionFree): keep the
  linear algebra in a module importing TailS only.

# pb-pst results log

Base: wip/pb-pst = origin/wip/leaf-fold33b 4dfb7e58 (75d94fe7 + main merge).

## Plan (from task)
(a) V1: B_max for one t = log[eps0]; (b) P2: FiniteDimensional htSpaceE; (c) P1; (d) V2.

## Entries
- 02:3x VERIFIED (compiled, `lake env lean scratch/pb-pst/BmaxOne.lean`, no errors): `amax_sep` (A_max ⊆ B_dR^+
  p-adically separated: x ∈ p^k A_max ∀k ⇒ x = 0, via ⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf and the ker θ-adic
  evaluations), `log_decomp`, `exists_padic_limit`, `logTeich_eq_mul`: for a generator ε₀ (ε₀^♯=1, ε₀^{(1)}≠1) and
  any ε with ε^♯ = 1, log[ε] = a·log[ε₀] in B_dR^+ for some a ∈ ℤ_p.
- 02:5x VERIFIED (compiled): §6-7 of BmaxOne.lean: `bmaxOf_eq : BmaxOf h = Bmax`, `bstOf_eq : BstOf h = Bst`
  (bst-construct's rings, which invert every log[ε], equal B_max^+[1/t] and B_max^+[1/t][log p̃] for one
  t = log[ε₀]); `exists_isGenEps`; restated leaves `PanDict.BergerPrintedVt` (∀ generator ε₀, de Rham ⇒ pst over
  BstOf) and `PanDict.PanPrintedPt` (pst hypothesis over BstOf for a given generator); proofs of the old leaves
  `bergerPrintedV_of_t : BergerPrintedVt → BergerPrintedV`, `panPrintedP_of_t : PanPrintedPt → PanPrintedP`.
  V1 cleared (no extra hypothesis).

# pb-pst results log

Base: wip/pb-pst = origin/wip/leaf-fold33b 4dfb7e58 (75d94fe7 + main merge).

## Plan (from task)
(a) V1: B_max for one t = log[eps0]; (b) P2: FiniteDimensional htSpaceE; (c) P1; (d) V2.

## Entries
- VERIFIED (compiled, `lake env lean scratch/pb-pst/BmaxOne.lean`, no errors): `amax_sep` (A_max ⊆ B_dR^+
  p-adically separated: x ∈ p^k A_max ∀k ⇒ x = 0, via ⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf and the ker θ-adic
  evaluations), `log_decomp`, `exists_padic_limit`, `logTeich_eq_mul`: for a generator ε₀ (ε₀^♯=1, ε₀^{(1)}≠1) and
  any ε with ε^♯ = 1, log[ε] = a·log[ε₀] in B_dR^+ for some a ∈ ℤ_p.
- VERIFIED (compiled): §6-7 of BmaxOne.lean: `bmaxOf_eq : BmaxOf h = Bmax`, `bstOf_eq : BstOf h = Bst`
  (bst-construct's rings, which invert every log[ε], equal B_max^+[1/t] and B_max^+[1/t][log p̃] for one
  t = log[ε₀]); `exists_isGenEps`; restated leaves `PanDict.BergerPrintedVt` (∀ generator ε₀, de Rham ⇒ pst over
  BstOf) and `PanDict.PanPrintedPt` (pst hypothesis over BstOf for a given generator); proofs of the old leaves
  `bergerPrintedV_of_t : BergerPrintedVt → BergerPrintedV`, `panPrintedP_of_t : PanPrintedPt → PanPrintedP`.
  V1 cleared (no extra hypothesis).
- VERIFIED (compiled, `lake env lean scratch/pb-pst/HTFinite.lean`): P2. `exists_rat_relation` /
  `linearIndependent_of_invariant` (Galois descent for ℂ_p-semilinear actions, minimal-relation argument,
  ℂ_p^{G_Qp} = Q_p from `ZInQ.Contrib.CloudB3W11.axSenTate_proof` at K = ⊥), `finrank_invariants_le`,
  `finiteDimensional_htU` (dim_Qp (C_p(w) ⊗ V)^G ≤ dim_Qp V), `finiteDimensional_htSpaceE :
  FiniteDimensional E (htSpaceE ρ w)`, `htMultE_le : htMultE ρ w ≤ n`. Probe: HDec.PkgI4.cpAct and
  ZInQ.Contrib.G9.PkgI4.cpAct agree by `rfl` (VERIFIED).
- VERIFIED (compiled): V2. BmaxOne.lean §8: `IsAdmissibleT` (Fontaine's admissibility, basis form:
  B ⊗ V has a B-basis of H-invariant vectors), `inclT_injective`, `isAdmissible_of_T` (basis form ⇒ bst-construct's
  dimension form `dim_{B^H} D_B(V) = dim V` for any G-stable B ⊆ B_dR; no B^H = K_0 used), `IsPstT`,
  `isPstBOf_of_T`; new leaf `PanDict.BergerPrintedVT` (one t + basis-form admissibility),
  `bergerPrintedV_of_T : BergerPrintedVT → BergerPrintedV`. Pitfalls: `Fintype.linearIndependent_iff` on the
  submodule `dB` and on `B ⊗ V` times out (instance paths); used `Basis.repr_sum_self`,
  `LinearIndependent.restrict_scalars` + `.of_comp dB.subtype`, and span via `Submodule.map_span`.

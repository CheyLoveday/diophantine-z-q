# bst-construct results log

Base: wip/pb-fix2 401a75236, merged origin/main (0caafe661) as af12d91ef.
Build: OneProof/H closure oleans copied from ~/dzq-wt/javanpeykar-fix (349 closure files identical to this tree,
checked with cmp); PanBerger, PanBergerFix, PanBergerPrinted built here (VERIFIED, `lake build`, 13:10).

## Bst.lean (scratch/bst-construct/Bst.lean, imports ZInQKernel.Contrib.OneProof.PanBergerPrinted)

- §1 `psEval I hx : A⟦X⟧ →+* AdicCompletion I A` (x ∈ I), ring hom; `psEval_eq_of_terms`, `psEval_C`. COMPILED.
- §2 `Amax` (Σ a_n (ω/p)^n, a_n ∈ A_inf → 0 p-adically, ω = ξ = p − [p̃], image in B_dR^+), `logPlus`
  (log(1+y), y ∈ ker θ, ξ-adic series), `logTeich` (log [ε]), `tInvSet` (inverses of log [ε], ε^♯=1, ε≠1),
  `logPTilde` (log([p̃]/p)), `BmaxPlus = adjoin_ℚp Amax`, `Bmax = adjoin_ℚp (Amax ∪ tInvSet)`,
  `Bst = adjoin_ℚp (Amax ∪ tInvSet ∪ {log p̃})`, `bst_eq_adjoin` (B_st = B_max[log p̃], rfl). COMPILED.
- §3 `fixedSub B H` (B^H), `dB B H ρ` ((B ⊗ V)^H, action computed in B_dR ⊗ V, a B^H-module),
  `IsAdmissible B H ρ := finrank_{B^H} dB = dim_ℚp V`. COMPILED.
- §4 `IsSemistableB`, `IsPstB`, `LocalIsPstB`, leaves `BergerPrintedB`, `PanPrintedB`, glue
  `panBerger_of_printedB` (pb-fix2's proof verbatim). COMPILED.
- §5 `isAdmissible_trivial` (trivial rep admissible for every B ⊆ B_dR, H; unconditional), `isPstB_trivial`. COMPILED.
- §6 `bdrAct_evalB` (σ Σ a_k x^k = Σ σ(a_k) σ(x)^k), `bdrAct_amax`, `bdrAct_logTeich` (σ log[ε] = log[σε]),
  `bmaxPlus_stable`, `bmax_stable`: A_max, B_max^+, B_max are G_Qp-stable. COMPILED.

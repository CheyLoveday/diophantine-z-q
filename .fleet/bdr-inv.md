# bdr-inv (2026-11-17): done — field proved outright

**Verdict.** `DeRhamPrint.BdRInvariantsPrinted` (Fontaine `B_dR^{G_K} = K`, Lean form
`dim_{ℚ_p} B_dR^{G_F} = [F:ℚ_p]`, research field `bdRInvariantsPrinted`, pending review / strict GLUE) is **proved**,
statement unchanged (imported, not restated), no new leaf, no open field used:
`BdRInv.bdRInvariantsPrinted_proof`. Inputs: Tate (`tateTwistInvariants_proof`), Ax–Sen–Tate (`axSenTate_proof`),
bdr-kertheta (DVR, fraction field, ker θ = (ξ)), TDict (`ε`, `[ε]−1 ∉ (ξ²)`), g9-derham (θ equivariant, Hensel lift),
Mathlib's `cyclotomicCharacter.spec`.

**What compiles (VERIFIED).**
* `scratch/bdr-inv/BdRInv.lean` (~490 lines): axioms [propext, Classical.choice, Quot.sound].
* `ZInQKernel/Contrib/OneProof/BdRInvariants.lean` (new file, same content):
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.BdRInvariants`
  succeeds; `#discharges`: `OpenResearchLeaves39.bdRInvariantsPrinted`, `still assumes: []`, axioms standard.
* `scratch/bdr-inv/autofold.json`; `autofold.py --dry-run`: strict 16/15 on 31 → 16/14 on 30 (strictest the same);
  the generated `sixContactMin_of_open58` module compiles with standard axioms.

**Proof.** `T = [ε]−1` is a uniformizer of `B_dR^+` and `σ(T) = T·w` with `θ(w) = χ(σ)` (σ(ε) = ε^{a_m}ρ^{p^m} in
the tilt with ρ♯ = 1, `[ρ]−1 ∈ ξW(O♭)` bounds the error by `p^m`); an invariant `x = T^{j−k}u` gives
`θ(u) ∈ ℂ_p(j−k)^{G_K}`, so `j = k` by Tate; then θ(x) ∈ ℂ_p^{G_K} = K (Ax–Sen–Tate) and the invariant Hensel lift
`F → B_dR^+` gives `F ≅ B_dR^{G_F}`. By-products: `bdrPlus_T` (gr¹ = ℂ_p(1)), `key` (invariants are units of B_dR^+).

**Remains.** Lead: run the fold (`python3 scripts/one_proof/autofold.py scratch/bdr-inv/autofold.json`, no
`--allow-rise`) and the usual post-fold checks. Report: docs/research/bdr-inv.md.

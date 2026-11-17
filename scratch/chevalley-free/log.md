# chevalley-free log

Base: wip/chevalley-free = wip/leaf-fold33b fe2f0d4a. Build tree seeded (reflink copy) from ~/dzq-wt/bdr-inv
(Main.lean byte-identical; has SemiAbelianDescendsPerfect and CloudW07 oleans).

## 0. Consumer check (VERIFIED, grep)

- `ZInQ.SemiAbDescend.ChevalleyPerfect` is used only in `ZInQKernel/Contrib/OneProof/SemiAbelianDescendsPerfect.lean`
  (`semiAbelianDescendsPerfect_of_chevalley` and the four `*_of_printed_chevalley` wrappers that call it) and as the
  bundle field `chevalleyPerfect` (TailZ61 `OpenResearchLeaves39`, TailZ63, EichlerBoundCopy), where it is passed to
  `bostLowerBound_of_printed_chevalley`, `gaudronRemondThm14_of_printed_chevalley` and (EichlerBoundCopy:4012)
  `semiAbelianDescendsPerfect_of_chevalley` for `javanpeykarBound`.
- In `semiAbelianDescendsPerfect_of_chevalley` the leaf is used exactly twice: existence over k for `U = G⁰`
  (`(hC k U ...).1`) and uniqueness over k̄ for `(G⁰)_{k̄}` (`(hC k̄ (F.obj U) ...).2`).

## 1. What the leaf supplies (VERIFIED, read)

For `U = G⁰` over perfect `k` (smooth, qc, connected) with `φU ≫ π' : (G⁰)_{k̄} → B'` flat surjective hom with
split-torus kernel: an abelian variety `B` over `k` and a flat surjective hom `π : U → B` with
`ker(π_{k̄}) = ker(φU ≫ π')` on points of k̄-algebras. This is the descent of the quotient `(B', φU ≫ π')` from k̄
to k.

## 2. Step A: reduction to `QuotientDescendsPerfect` (VERIFIED, compiled)

`scratch/chevalley-free/Assembly.lean`: `ZInQ.ChevFree.QuotientDescendsPerfect` (descent of a semi-abelian
presentation `(B', π')` of `U_{k̄}` to `(B, π)` over perfect `k`, same kernel over k̄-algebras) and
`semiAbelianDescendsPerfect_of_qd : QuotientDescendsPerfect → SemiAbelianDescendsPerfect` (semiab-descend's proof
with step (e) replaced). `lake env lean`: OK, axioms [propext, Classical.choice, Quot.sound]. ~75 s per check
(import load dominates).

## 3. Step R: rigidity (VERIFIED, compiled)

`scratch/chevalley-free/Rig.lean`: `torus1_const` — for any field `K`, any `B : PkgI3.AbVar K` and any morphism
`g : Spec K[x^{±1}] → B` over `K`, `g(s) = g(1)` for all `s ∈ Kˣ`. Proof: `𝔾_m` = overlap of the two charts of
the vendored relative `ℙ¹` (CloudW07), extension to `ℙ¹` by the vendored valuative extension
(`exists_hom_of_valuationRing_stalk`, stalks valuation rings since `ℙ¹` is smooth of relative dimension 1, proved
here from Mathlib's `𝔸ⁿ` smoothness), constancy by vendored `RationalCurves.eq_zero_comp` with commutativity from
Mathlib `isCommMonObj_of_isProper_of_geometricallyIntegral`. Axioms standard.

## 4. Step D: descent of the quotient along a finite flat cover (VERIFIED, compiled)

`scratch/chevalley-free/Descent.lean`: for `q : S' → S` finite flat surjective lfp, `U` over `S`, `π₁ : U_{S'} → X₁`
fpqc over `S'` with the transport condition `KI q π₁`, and finite sets of `X₁` in affine opens: `exists_descent`
gives `B₀` over `S`, `d : X₁ → B₀` with `IsPullback d X₁.hom B₀.hom q`, and `π : U → B₀` with `fst ≫ π = π₁ ≫ d`.
Descent datum built as `ψ : X₁ ×_S S' → X₁` by effective-epi descent along `π₁ × id` (unit, `ψ ≫ hom = snd`,
coassociativity by epi cancellation), effectivity from vendored `isEffective_of_isFinite`. Axioms standard.

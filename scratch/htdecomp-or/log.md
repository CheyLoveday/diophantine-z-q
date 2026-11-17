# htdecomp-or results log

Base: origin/wip/leaf-fold33b d911d55cf (8ba86099 is an ancestor), origin/main ee33f2143 merged (e69290c7e).
Build tree: reflink copy of ~/dzq-wt/javanpeykar-steps/.lake/build (TailZ63) + lean/.lake/build.

## Statements
* Field (unchanged): `ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists` (HodgeTatePairingDecomp.lean L44),
  tensor form `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a × ℂ_p^b`.
* New `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom`: Hom form `Hom_{ℚ_p}(V_p(A), ℂ_p) ≅ ℂ_p^a × ℂ_p(−1)^b`,
  action `σ·f = cpLin σ ∘ f ∘ ρ(σ⁻¹)`.
* New leaf `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr := HodgeTateDecompExists ∨ HodgeTateDecompHom`.

## Findings
* VERIFIED (Lean probe): no instance `Module ℤ_[p] ℂ_[p]` in the tree, so `Hom_{ℤ_p}(T_p A, ℂ_p)` is not statable
  without an ad hoc instance; the Hom form uses `Hom_{ℚ_p}(V_p A, ℂ_p)` (canonically equal).
* VERIFIED (compiled): dualization needs no finite-dimensionality input: `C ⊗ V → Dual_C(Hom(V,C))` is injective
  for every ℚ_p-space V (basis of V); the Hom form makes the target finite-dimensional, so V is finite-dimensional.

## Compile outcomes
* 2026-11-17 ~02:10 `lake env lean ZInQKernel/Contrib/OneProof/HodgeTateDecompOr.lean`: no errors, no warnings.
  Theorems: `hodgeTateDecompExists_of_hom`, `hodgeTateDecompExists_of_or`, `or_of_tensor`, `or_of_hom`.

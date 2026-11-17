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
* `lake build ZInQKernel.Contrib.OneProof.HodgeTateDecompOr +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`:
  success, 16070 jobs (VERIFIED).
* `scratch/htdecomp-or/Discharges.lean` (output `Discharges-output.txt`): `hodgeTateDecompExists_of_or` discharges
  `OpenResearchLeaves41.hodgeTateDecompExists`, still assumes `[HodgeTateOr.HodgeTateDecompOr]`; `_of_hom` assumes
  `[HodgeTateOr.HodgeTateDecompHom]`; axioms standard for both (VERIFIED). 40 open, 13275 theorems checked, 27 discharge one.
* `scratch/htdecomp-or/Statement.lean`: verbatim copy of the field, `Iff.rfl` against the tree; compiles (VERIFIED).
* `autofold.py scratch/htdecomp-or/autofold.json --dry-run`: `strict count: 12/23 on 35 -> 13/22 on 35; strictest
  11/24 -> 12/23` (GLUE −1 in both columns). Output minus line 1 = `AutofoldDry.lean`, compiles against TailZ66:
  `HDec.HSyn.sixContactMin_of_open60` depends on `[propext, Classical.choice, Quot.sound]` (VERIFIED). No tree file written.
* `ZInQKernel/Contrib/OneProof/HodgeTateDecompOrH1.lean` (helper, imports HodgeTateDecompOr): `HodgeTateDecompH1`
  (`ℂ_p ⊗ V^∨` shape, Faltings 1988), `hom_of_h1`, `or_of_h1`, `hodgeTateDecompExists_of_h1`; converse
  `hom_of_tensor`, `hom_iff_tensor`, `or_iff_field`. `lake build` success; all axioms standard (VERIFIED,
  `Discharges-output.txt`: 40 open, 13321 theorems checked, 28 discharge one).
* No `#eval`/`run_cmd`/notation/macros/`sorry` in either new file (grep, VERIFIED).

# r16-used results log

Base 43513d87 (leaf-fold25). Field on the route: `r16CoreY : R16Split.R16CoreY` (OpenResearchLeaves22).

## Consumers (VERIFIED: grep + reading, 2026-11-15)
- Only non-pass-through use of r16 on the route: `TailA.lean:3717` `g13_g16` -> `g13` (TailA:3442) ->
  `commonConstituent_of_attached hR16 ... 5 D.ιC D.ι5 D.r5 ...` (TailA:3404).
  Reached from TailK G0 term via `afterG7_of3` (TailD) -> `newformLeaves_of3` (TailD:150) -> `NewformLeaves.r16`.
- Other `.r16` occurrences: pass-throughs between bundle generations (`r16 := r.r16`), TailN:117 copy change
  (`eichlerShimuraJ1_ofK5`), TailA:4659 `newformLeaves_of` (older generation), Leaves.lean:291 (`exists_J1_quotient`, not on route).
- Instance: ℓ = 5, emb = `embOf 5 ιC ι5 (coeffField f)`, f = newform from `newform_of_pan` (T24 twist + T25 newform of
  Pan's eigenform for r5), arbitrary level N, every J with IsJ1 N J.
- Clauses of r16 used by `commonConstituent_of_attached`: `FiniteDimensional ℚ K_f` (for embOf), A, π surjective, θ,
  `finrank (eigenFun 5 A θ emb) = 2`, trace clause at p ∤ 5N. NOT used: `A.dim = [K_f:ℚ]`, the determinant clause,
  ℓ ≠ 5, embeddings other than embOf.

## Lean (VERIFIED: compiled with `lake env lean scratch/r16-used/Used.lean`, 2026-11-15 ~07:00)
- New leaf `R16Used.AfTateCharPoly` (existence form of DS Lemma 9.5.3 + Thm 9.5.4, numbers UNVERIFIED): ∃ quotient
  π : J ↠ A over ℚ, θ : K_f → End⁰(A), for every ℓ a basis b of V_ℓ(A) over ℚ_ℓ ⊗_ℚ K_f (module via θ), and for
  p ∤ Nℓ, Frobenius σ: ∃ c ∈ K_f with c = χ(p) and charpoly_{ℚ_ℓ⊗K_f}(matrix of σ in b) = X² − (1⊗a_p)X + (1⊗cp).
- `R16Used.r16_of_afTate : AfTateCharPoly → PkgI3.TateModuleFree → R16_EichlerShimuraJ1'` (glue, proved):
  [K_f:ℚ] < ∞ by faithfully flat descent (`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`);
  ι-eigenfunctionals ≅ Ω² via the basis (rank two); frobOn conjugate to (ι_R M)ᵀ (trace, det = ι_R(tr M), ι_R(det M));
  dim A = [K_f:ℚ] from rank two (`R16Split.dim_eq_of_rank_two`).
- `R16Used.r16CoreY_of_printed : AfTateCharPoly → AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY`.
- `#print axioms R16Used.r16CoreY_of_printed`: [propext, Classical.choice, Quot.sound].

## Contribution, discharges, bypass, fold (VERIFIED, 2026-11-15 07:15-07:45)
- `lake env lean ZInQKernel/Contrib/OneProof/R16Used.lean`: no errors, no warnings.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.R16Used`:
  success, 12995 jobs, 9 min (build dir copied from wip/r17-bypass; partial rebuild). `build-output.txt`.
- `lake env lean scratch/r16-used/Discharges.lean` (`Discharges-output.txt`):
  `DISCHARGES [OpenResearchLeaves22.r16CoreY] by R16Used.r16CoreY_of_printed
     still assumes: [R16Used.AfTateCharPoly, AvSplit.MumfordTorsionAlgClosed]
     axioms: [propext, Classical.choice, Quot.sound]`; `#discharges: 63 open hypotheses, 1865 theorems checked, 8 discharge one`.
- `lake env lean scratch/r16-used/Bypass.lean`: `HDec.G0ModNewform.g13_trace` (g13 from `R16Trace`) and
  `g13_via_trace`: standard axioms (`Bypass-output.txt`).
- `python3 scripts/one_proof/autofold.py scratch/r16-used/autofold.json --dry-run`:
  `strict count: 46/10 on 56 -> 47/9 on 56; strictest 45/11 -> 46/10` (LEAF/GLUE: −1 GLUE in both columns).
  Line 1 stripped -> `FoldDryRun.lean`; `lake env lean` -> `HDec.HSyn.sixContactMin_of_open30` standard axioms.
  Not applied (Main.lean, kinds.tsv, claims.tsv unchanged).

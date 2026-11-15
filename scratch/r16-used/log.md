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

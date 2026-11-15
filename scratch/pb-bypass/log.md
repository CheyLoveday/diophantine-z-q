# pb-bypass results log

Base 9a100aa7 (leaf-fold22). Field: research `r11r12 : HDec.PkgI4.PanBerger` (LPrefix.lean l. 2250),
kinds.tsv: composite, GLUE.

## Step 1. Consumers (VERIFIED by grep of ZInQKernel/, 11-15)
- Every `.r11r12` occurrence in ZInQKernel/ is a bundle-to-bundle assignment `r11r12 := r.r11r12`, except one:
  `HDec.G0Galois.g8_g12_of_leaves3` (TailD.lean l. 139) passes `r.r11r12` to `g8_g12` (TailA l. 2255),
  which passes it to `g12` (TailA l. 2211).
- `g12` applies it once: `hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, _, h9.2⟩`
  (TailA l. 2220): **only p = 5**, ρ = `r : GaloisRep 5 2`, the 2-dim constituent r₅ of the QM abelian surface A
  over the descent field L' (Galois over ℚ, `dim A = 2`, `Intertwines (tate A 5) (r|G_{L'}) e` with
  V₅(A)⊗ℚ̄₅ ≅ r ⊕ r). Hypotheses fed: irreducible (G8), finitely ramified (G11), `LocalIsDeRham` (G9),
  odd (G10), HT weights {0,−1} (G9). A is not CM (NoCM branch), so r₅ is not induced from a Hecke character.
- `g8_g12_of_leaves3` is called once, by `HSyn.G0AssembleMod.afterG7_of3` (TailD l. 171), on the route to
  `sixContactMin_of_open28` / `ZInQ.OneProof.frozenTarget`.

# HeightModelM3: the readings of HeightModelM2 as Lean theorems

`HeightModelM2` stated three readings that were not Lean theorems. Each is proved here.

1. **`θ` is an isomorphism** (`Theta.lean`). `theta_surjective`: the comparison map
   `θ : 𝔪_ξ/𝔪_ξ² → 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]` is surjective, by the conormal sequence and
   `Ω[𝒪_{S,η}/𝓞_L] = 0`. With the tree's `theta_injective` this gives `thetaEquiv`. So `detSec`,
   which wedges sections in the image of `θ`, wedges all sections (`map_comap_secOmega`).
2. **Sections of `e*Ω¹` itself** (`StalkInjective.lean`). `stalkToGeneric_injective`: the stalk
   `𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]` of `e*Ω¹` injects into the generic fibre. The
   proof uses that `Ω` of a smooth algebra is projective, and that the local rings are
   localizations of an affine chart. `range_stalkToGeneric`: its image is `printedOmegaAt s`.
   `mem_globalOmega_iff`: `globalOmega` is the module of compatible families of germs of
   `e*Ω¹`, one in each stalk.
3. **Spans** (`Spans.lean`). `germEta_smul_mem_secOmega` and `smul_wedge_mem_detSec`: the
   `𝓞_L`-spans `secOmega` and `detSec` are `𝒪_S(V)`-modules.

`GR1Rows.lean` restates the implications from the GR1 rows over `IsGR1StableHeightGlobal` to the
bundle's fields. `Check.lean` prints the axioms.

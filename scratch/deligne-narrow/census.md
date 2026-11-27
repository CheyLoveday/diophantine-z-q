# Deligne reader census

Scope: the declaration graph of `ZInQ.OneProof.frozenTarget` at `41892618b`.
Here **reads** means uses the information to obtain a result, and **carries**
means packages or projects a proof without interpreting all its clauses. The
direct declaration scan is `Census.lean`; this table follows the clauses
through the packaging and to the terminal uses. Paths are relative to the
repository root. Lines refer to the base.

In all three terminal readers `(Y, Φ)` is the witness selected from
`Y3FineModuliAbP` (an existing consequence of `y3FullThreeRepZ30`). The
point map is the same `Ψ` supplied for this witness, restricted through
`toPM` to the upper half-plane. The printed clause list is converted to
`R1fpPropsAb` using the existing torsion theorem and the point `Ψ(i,1)`.
Nothing about this point's abelian surface is needed just to obtain a
`ℚ̄`-point.

| Base declaration / location | Onto | Fibres | Holomorphy | Body moduli | Reciprocity | Unit moduli |
|---|---|---|---|---|---|---|
| `OpenResearchLeaves63`, `openResearchLeaves60_y3x6_of_OpenResearchLeaves63`; `ZInQKernel/OneProof/H/TailZ89.lean:18,46,79,95` | Carries | Carries | Carries | Carries | Carries | Carries |
| `OpenResearchLeaves60_y3x6`, `OpenResearchLeaves59_y3x6`, `OpenResearchLeaves54SFU_y3x6`; `ZInQKernel/OneProof/H/Y3Open.lean:19,49,77,111,145,185` | Carries | Carries | Carries | Carries | Carries | Carries |
| `openResearchLeaves59_y3x6_of_60_y3x6` and `openResearchLeaves54SFU_y3x6_of_59_y3x6`; `ZInQKernel/OneProof/H/Y3Open.lean:332,350,366,390` | Carries | Carries | Carries | Carries | Carries | Carries |
| `GR9.openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6`; `ZInQKernel/OneProof/H/Y3Open.lean:413,424` | Packages | Packages | Packages | Packages | Packages | Packages |
| `Y3Hodge.deligneH_of_print`; `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean:960` | Calls body conversion | Calls body conversion | Calls body conversion | Calls body conversion | Calls body conversion | Calls unit conversion |
| `Y3Hodge.bodyH_of_PM`; `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean:939` | All complex points; old unrestricted witness then `exists_upper` | Both directions on upper pairs to build old intermediate; forward `DCRelPM → equality` also moves old lower witnesses to upper in the onto proof | Forwards all `g` and the duplicate at `1` | Converts `IsHodgeH1Print` at `g=1`, all upper `τ` | Forwards all | — |
| `Y3Hodge.unitsH_of_PM`; `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean:951` | — | — | — | — | — | Converts `IsHodgeH1Print` at all integral units and upper `τ` for the intermediate |
| `Y3Fix.shimuraMainThmIDeligneY3AbU_of_print`, `deligneP_of_H`, `body_of_H`, `units_of_H`, `field_of_printP`; `ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean:887,879,865,872,790` | Packages | Packages | Packages | Converts Hodge to lattice for all upper `τ` at `1` | Packages | Converts Hodge to lattice at all units and upper `τ` for the intermediate |
| `mainThmI_of_U`; `ZInQKernel/Contrib/OneProof/RayClassShimura.lean:1157` | Carries | Carries | Carries | Carries | Carries | Drops |
| `isShimuraHolFamily_of_body`, `shimuraFamilyAb_of_mainThmI`, `isR1bFamily_of_hol`, `shimuraFamilyAb_of_U`; `ZInQKernel/Contrib/OneProof/RayClassShimura.lean:491,498,265,3049`; invoked at `ZInQKernel/OneProof/H/Y3Copy4.lean:1417` | — | — | Full `IsHolFamily` at `1`, all upper `τ`; used for the map to `P¹` | All upper `τ` at `1`, CM or otherwise; needs the complex QM torus with its action | — | Does not project this field in the base; its `u=1` case supplies the very same moduli data in the replacement |
| `rayClassCMAb_of_leaves`, `rayClassCMAb_of`, `embed_core`, `obj_at`; `ZInQKernel/Contrib/OneProof/RayClassShimura.lean:3042,3004,1367,1642`; invoked at `ZInQKernel/OneProof/H/Y3Copy4.lean:1435` | At the complex base change of each `y : Y(ℚ̄)` with object of type CM4/3/24 | Forward only: move `(τ₀,g)` to unit representative `(τ,u)`; then at that CM `τ` compare `u` with `q̂(s)^ε u` | — | — | `K4,K3,K24`, the integral `q` and CM `τ` from the object's CM endomorphism, `g=u∈𝒪̂^×`, `s` in the ray kernel modulo three, `σ` extending a Galois element fixing the embedded ray class field | Only `(τ,u)` over those three types of algebraic points, with all choices of their unit representative |
| `y3ConnectedAb_of_U`, `y3ConnectedAb_of_mainThmI`, `connected_of_body`; `ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean:681,675,608`; invoked at `ZInQKernel/OneProof/H/Y3Copy5.lean:2142,2145` | Two arbitrary complex points chosen in opposite clopens of `Y` | Forward only from `(i,g)` to `(γ i,g')`, `γ` of positive norm, `g'=γgk`, `k∈K₃` | First projection only, all `g`: Zariski-open inverse images are open on the upper half-plane | — | `K4=ℚ(i)`, fixed `q4`, `tau0=√2+i`, `kappa0` or its conjugate, fixed `s4` or its inverse, all `g`; an Artin-compatible `σ` and then underlying point equality | — |

The higher callers in `ZInQKernel/OneProof/H/Y3Copy4.lean`, `Y3Copy5.lean`,
`Y3Copy6.lean` and `Y3Open.lean` only carry this Deligne input or relay
the resulting bundle. The copied declaration manifest gives these file:line
locations. The three terminal results feed `r1b`, the CM part of the
moduli row, and `TSHecke.Y3Connected` respectively.

The two similarly named wrappers
`Y3Hodge.shimuraMainThmIDeligneY3AbU_of_printPM`
(`ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean:967`) and
`Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print`
(`ZInQKernel/Contrib/OneProof/ShimuraY3Print.lean:102`) are not live.
The former would forward every clause through the same Hodge bridge; the
latter combines the fine witness and a different lattice-form Prop and
does not use `DeligneCanonicalModelY3EveryPrint`. The converse/equivalence
theorems in `Y3HodgePrint.lean:1632,1652,1656` and historical Tail, CM, and
X₆ assemblies are not readers of the leaf of this root.

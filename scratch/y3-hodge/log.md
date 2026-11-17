# y3-hodge results log

Base wip/leaf-fold33b 6b97a5c7. Build tree copied (reflink) from ~/dzq-wt/h21-gchar (same ZInQKernel tree plus two
unrelated TYZThm21Span files).

## Inputs located (VERIFIED, read)
- Leaf: `Y3Fix.DeligneCanonicalModelY3EveryH` (ShimuraY3PrintedLeaves.lean:861), moduli clause `Y3Fix.IsHodgeH1`
  (line 394): `H₁` = the lattice `Λ` of an arbitrary analytic uniformization (the reviewer's objection (1)).
- Reviewer verdict queue11: only the kinds.tsv summary row is on this host (crowd-kit/ckpt/... not present).
- pel-hodge (origin/wip/pel-hodge, not in base): `PELHodge.h1Form_iff`, H₁ := π₁(A(ℂ),0)ᵃᵇ, built over
  UnifPrinted (not in base). Base has the same definitions as `CloudB3W17Hodge.{CPt,XPtIn,XevalAt,basicSets,
  classicalTopology}` (Bridge.lean), with `classicalTopology_eq` to the ported manifold topology.
- y3abu-strict (origin/wip/y3abu-strict, not in base): `Y3ABUStrict.LemmaP.lemmaP_lattice_unique`, imports only
  HDecomp.QM.Polar + HDecomp.Analytic.QMLattice (both in base).

## Compile log
- Hodge.lean stage 1 (§0 UP lemmas + pel-hodge H1/H1Form/Unif/Main/h1Form_iff, rebased on CloudB3W17Hodge):
  compiles, 0 errors (2m33).
- Hodge.lean stage 2 (continuous_postcomp, pushLoop = f_* on H1, continuous_of_isAnalyticHom, IsHodgeH1Print, bOf bijective 𝒪 ≃ Λ_τ): compiles, 0 errors.
- Hodge.lean stage 3: `lattice_of_print`, `print_of_lattice`, `print_iff_hodge : IsHodgeH1Print P τ ↔
  Y3Fix.IsHodgeH1 P τ` (uses uniformizationLeafAll_proof): compiles, 0 errors. Item (1) VERIFIED (compiled).
  Key step: 𝒪-linearity on H₁ (ι_A(a)_* c(b) = c(ab)) ⇒ ι-compatibility of Φu, via monodromy of straight loops
  (Θ = IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite) + LinearMap.ext_on over the full lattice Λ_τ.
- Hodge.lean stage 4 (item 3 + sign): compiles, 0 errors.
  * `dcRelPM_iff`: on ℍ ⊂ ℍ^± the print's relation (γ ∈ B^×, any sign) is `DCRel` (γ ∈ B^×_+).
  * `exists_upper`: every (z, g), z ∈ ℍ^±, is related to some (τ, g'), τ ∈ ℍ (μ = 1+i, nrd μ = −1).
  * `Jmat_sq` (J_τ² = −1), `adjugate_Jmat` (J̄_τ = −J_τ), `iota_mul_Jmat` (ι(γ)J_τ = J_{γτ}ι(γ), nrd γ > 0),
    `F0_iff` (M J_τ = −i M ↔ M(τ,1)ᵀ = 0: F⁰ = V^{0,−1} holomorphic in τ in Deligne's convention).
  Sign verdict (VERIFIED as Lean + STANDARD convention): the leaf's `β(M J_τ) = i β(M)` is the holomorphic choice;
  the docstring's "h_τ(i) = J_τ" holds for G = B^{op×} acting on V = B by right multiplication; for Deligne's
  G = B^× acting on V = B by left multiplication (𝒪 on the right), transport by the canonical involution gives
  h_x(i) = J̄_τ = −J_τ (adjugate_Jmat). No statement change needed.
- Hodge.lean stage 5 (§7 leaf): `DeligneCanonicalModelY3EveryPrint` (Ψ on ℍ^± × G(𝔸_f), fibres DCRelPM, moduli
  IsHodgeH1Print), `deligneH_of_print : DeligneCanonicalModelY3EveryPrint → Y3Fix.DeligneCanonicalModelY3EveryH`,
  `shimuraMainThmIDeligneY3AbU_of_printPM`: compiles, 0 errors.
- Contributor module `ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean` (new file = Hodge.lean): `lake build` OK.
- autofold spec `autofold.json` (field deligneCanonicalModelY3EveryH := Y3Hodge.deligneH_of_print
  {n}.deligneCanonicalModelY3EveryPrint; leaf kind consequence, flag "pending review (new leaf, GLUE until a
  reviewer rates it) ..."): `--dry-run` strict 11/23 on 34 -> 11/23 on 34; strictest 10/24 -> 10/24 (GLUE for GLUE).
  FoldCheck.lean.txt (dry run minus line 1) compiles: `HDec.HSyn.sixContactMin_of_open61` standard axioms.
- `lake build ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.Main` OK (16073 jobs; frozenTarget standard axioms).
  Discharges.lean: DISCHARGES [OpenResearchLeaves42.deligneCanonicalModelY3EveryH] by Y3Hodge.deligneH_of_print,
  still assumes [Y3Hodge.DeligneCanonicalModelY3EveryPrint]; 39 open, 13439 theorems checked; all Y3Hodge
  #print axioms standard (discharges.txt).

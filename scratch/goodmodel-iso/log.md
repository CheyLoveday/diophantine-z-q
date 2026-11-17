# goodmodel-iso results log

## 11-16 16:10 setup
- Base wip/group-law-dvr 3ab4d8eb; merged origin/main (already ancestor, c1e4ed1b) and origin/wip/neron-ext (901a0efd), no conflicts.
- Top bundle on this tree: TailZ45 `sixContactMin_of_open38 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19)`;
  `mumfordGroupLawConn` in r (TailZ45:58 region), `neronSchemeExtensionExists` in t (TailZ44:110). VERIFIED (read).
- group-law-dvr's F2 patch generator scratch/group-law-dvr/fold/make_patch.py targets this same TailZ45 (main unchanged since). VERIFIED (read).

## Route analysis
- Suggested step (1) "F is a Néron model (BLR 1.2/8)" needs a group law on F: the tree's proof
  (NeronExt.isNeronModelOver_of_grpObj, NeronExtAb.lean) takes `[GrpObj X]`; its Weil-extension step
  `RelativeGroupLaw.exists_opens_diagonal_difference_extension` uses the target's group law. In
  NeronGoodModelIso, F has no group law (constructing it is the point of MumfordGroupLawDVR). So (1) is circular. VERIFIED (read).
- Build: copied (reflink) ~/dzq-wt/group-law-dvr/.lake/build and lean/.lake/build (same base commit 3ab4d8eb).

## Plan (purity-free route, all tools located; VERIFIED by reading statements)
NeronGoodModelIso for an arbitrary smooth separated N follows from the case where N carries a group law with
e ≫ ψ = η_N, given a Néron model over R (NeronSchemeExtensionDVR): χ : N → N' (Néron), χψ iso by the group case,
then ψ has a left inverse and ψ ∘ (χψ)⁻¹ χ = id_N by density. Group case:
 A. V ⊂ N open, v : V → F (FLT `NeronModelInfra.exists_opens_extension_of_isProper_of_smooth`, target F proper):
    V ⊇ generic fibre, V meets every irreducible component of N_k.
 B. ψ ∘ v = ι_V and v ∘ ψ = id on ψ⁻¹V (density: flat source, separated target).
 C. ψ injective on points: on ψ⁻¹V by B; on F_k by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`,
    FrobChain/Rigidity.lean: pointed map AbVar → separated lft group scheme over any field is a hom) and a
    translation argument with field-valued points (no k̄, no descent).
 D. For z ∈ N: ψ⁻¹{z} ⊆ affine Y; U' ∋ z affine with ψ⁻¹U' ⊆ Y (ψ closed).
 E. Hartogs (`existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk`, stalks normal by
    `Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`, dim ≤ 1 points in V by
    `mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing`): v|U'∩V extends to U' → Y.
 F. ψ iso over each U' ; G. iso is local on the target.
- 16:45 Part1.lean compiles: genMap_ne_closedPoint, ext_of_generic_open, exists_inverse_open (steps A-B: V, v, B1 v≫ψ=ι, B2 (ψ∣V)≫v=ι). VERIFIED (lake env lean, no errors).

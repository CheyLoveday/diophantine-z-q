# goodmodel-iso: `NeronGoodModelIso` proved; `mumfordGroupLawConn` and `neronSchemeExtensionExists` replaced by the one leaf `NeronSchemeExtensionDedekind`

Task goodmodel-iso, 2026-11-16. Base: wip/group-law-dvr 3ab4d8eb, merged with origin/main (c1e4ed1b, already an
ancestor) and origin/wip/neron-ext (901a0efd). Results log: scratch/goodmodel-iso/log.md. Model work, no human review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means published mathematics
with a reference. **SPECULATIVE** means judgement. **UNVERIFIED** marks a theorem number recalled without a source
(no network).

## 1. Verdict

**Target met (VERIFIED, no `sorry`, standard axioms only).** group-law-dvr's glue
`ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso` is proved. Its input is the DVR case of the leaf that group-law-dvr's
fold F2 already carries. No purity theorem is used, and no new leaf or glue is added:

```lean
-- ZInQKernel/Contrib/OneProof/NeronGoodModelIso.lean (namespace ZInQ.Contrib.GoodModelIso)
theorem neronGoodModelIso_of_dvr (hN : NeronSchemeExtensionDVR) : NeronGoodModelIso
theorem neronGoodModelIso_of_dedekind (hN : NeronSchemeExtensionDedekind) : NeronGoodModelIso
theorem mumfordGroupLawDVR_of_dedekind (hN : NeronSchemeExtensionDedekind) :
    ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
```

So *GIT* Thm 6.14 over a DVR, the form the chain uses, follows from BLR §1.4 Thm 3 alone. The combined fold **G** is
group-law-dvr's F2 without the glue field, plus the removal of the textbook field `neronSchemeExtensionExists`, which
follows from the same leaf (`neronSchemeExtensionExists_of_dedekind`). It replaces the two open fields
`mumfordGroupLawConn` (research) and `neronSchemeExtensionExists` (textbook) by the one printed leaf
`neronSchemeExtensionDedekind`: **net −1 open hypothesis, no new glue**. Fold G was checked in an olean overlay (§5).

On the statement: `NeronGoodModelIso` is proved exactly as group-law-dvr stated it, for an arbitrary smooth separated
`N`. The proof first treats the case where `N` has a group law, then reduces the general case to it through the
Néron model (§3).

## 2. Why the suggested route (1) is circular, and what replaces it (VERIFIED, read)

The suggested step (1) was "`F` is the Néron model of its generic fibre (BLR 1.2/8)". The tree's proof of BLR 1.2/8
over a DVR, `NeronExt.isNeronModelOver_of_grpObj` (NeronExtAb.lean), takes `[GrpObj X]`. Its extension step, the
vendored FLT lemma `RelativeGroupLaw.exists_opens_diagonal_difference_extension` (Weil's argument), uses the group
law of the **target**. In `NeronGoodModelIso`, `F` has no group law: constructing one is the whole content of
`MumfordGroupLawDVR`. So (1) cannot be used.

The replacement still uses the Néron model, but in the target `N`, which carries the Néron group law, and never in
`F`. Three facts take the place of van der Waerden purity:
* a Hartogs lemma for maps into affine schemes;
* injectivity of `ψ` on points, from rigidity on the special fibre;
* the FLT extension of a generic map into a proper target over an open that contains all points of codimension ≤ 1.

## 3. The proof (all VERIFIED: compiled)

The file is `ZInQKernel/Contrib/OneProof/NeronGoodModelIso.lean` (about 620 lines). It is also in scratch as
scratch/goodmodel-iso/GoodModel.lean. Notation: `R` is a DVR with fraction field `K` and residue field `k`; `F` is as
in the glue (proper, smooth, every field fibre an abelian variety with origin `e`); `ψ : F → N` is an isomorphism over `K`.

**Group case** (`isIso_of_grp`): `N` is smooth, separated and quasi-compact, with a `GrpObj N` whose identity is `e ≫ ψ`.

| step | Lean | content | ingredients |
| --- | --- | --- | --- |
| A–B | `exists_inverse_open` | `ψ_K⁻¹` extends to `v : V → F` on an open `V ⊆ N` that contains the generic fibre and meets every irreducible component of `N_k`. Then `v ≫ ψ = ι_V` and `(ψ ∣_ V) ≫ v = ι_{ψ⁻¹V}` | vendored FLT `NeronModelInfra.exists_opens_extension_of_isProper_of_smooth` (target `F` proper, source `N` smooth and quasi-compact); density: `NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated` with Mathlib's `IsSchemeTheoreticallyDominant.pullbackFst` |
| C (generic fibre) | inside `isIso_of_grp` | `ψ` is injective on `ψ⁻¹V ⊇ F_K` | B at points |
| C (special fibre) | `fibreMap`, `fibreMap_isMonHom`, `fibre_injective` | the base change `ψ_k : A → N_k` is a homomorphism. It is pointed (`η_N = e ≫ ψ`), and the tree's rigidity applies over any field (`MulRigidity.isMonHom_of_geometricallyIntegral`, FrobChain/Rigidity.lean). If `ψ_k x = ψ_k y` for points `x, y`, take a field point of `A ×_{N_k} A` over `(x, y)`. In `T ⊗ A`, with `T` the spectrum of that point's residue field, the opens `{w : yx⁻¹w ∈ W}` and `{w ∈ W}` are non-empty: translations are surjective, and `W` is the preimage of `ψ⁻¹V` in `A`, which contains a point. `A_T` is irreducible, so the two opens meet. At a point `q` of the intersection, `ψ` is injective on `W` (by B), so `yx⁻¹w = w` and `x = y` | Mathlib's `nonempty_preirreducible_inter` and `IrreducibleSpace (pullback f g)` for geometrically irreducible `g`; group calculus in `Hom(T, A)` (`MonObj.mul_comp`, `GrpObj.inv_comp`) |
| W ≠ ∅ | inside `isIso_of_grp` | some point of `F_k` maps into `V` | `hVs` gives `n ∈ V ∩ N_k`. Since `N → Spec R` is open, `n` is in the closure of `N_K ⊆ ψ(F)`, and `ψ(F)` is closed (`ψ` is proper) |
| D–G | `isIso_of_injective` | for `z ∈ N`, the fibre `ψ⁻¹ z` (at most one point) lies in an affine `Y`, and an affine `U' ∋ z` has `ψ⁻¹U' ⊆ Y`. `v` restricted to `U' ∩ V` extends to `φ : U' → Y` by Hartogs. `φ` lies over `Spec R` (uniqueness into the affine `Spec R`) and is a section of `ψ` (density). So `ψ ∣_ U'` is an isomorphism with inverse `φ` (density again, and `eq_of_comp_eq`). Isomorphisms are local on the target | vendored FLT `existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk` (Hartogs into affines on a locally noetherian scheme with normal stalks), `Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`, `mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing` (points of dimension ≤ 1 lie in `V`); Mathlib `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict` |

**General `N`** (`neronGoodModelIso_of_dvr`):
1. Take the Néron model `N'` of `A = F_K` from `NeronSchemeExtensionDVR`, with the group law `NeronC.grpObjOfNeron`,
   and `χ : N → N'` extending the generic identification (`N` is smooth).
2. `ψ' := ψ ≫ χ` is an isomorphism over `K`. Its identity condition `e ≫ ψ' = η_{N'}` is group-law-dvr's argument,
   copied. So `ψ'` is an isomorphism by the group case.
3. `r := χ ≫ ψ'⁻¹` satisfies `ψ ≫ r = 𝟙`. Also `r ≫ ψ = 𝟙`, because both sides agree over `K` and `N` is flat and
   separated (`NeronC.pullback_map_injective`).

`#print axioms` (VERIFIED, `lake build ZInQKernel.Contrib.OneProof.NeronGoodModelIso`, 12,803 jobs):
`neronGoodModelIso_of_dvr` and `mumfordGroupLawDVR_of_dedekind` depend on `[propext, Classical.choice, Quot.sound]`.

## 4. The fold G (manual; spec and script in scratch/goodmodel-iso/fold/)

Autofold cannot express G, for two reasons:
* As in group-law-dvr's F1/F2, no theorem proves the old field type `MumfordGroupLawConn` (connected, possibly
  non-reduced bases) from the new leaf. The field type of the older generations is narrowed in place.
* The textbook field is discharged by a research-bundle leaf, and autofold's `{n}` reaches only the field's own
  bundle.

Script: scratch/goodmodel-iso/fold/make_patch.py (`make_patch.py ROOT OUT`). Patch: fold/G.patch. Edits for the integrator:

1. **Narrowing** (group-law-dvr's, unchanged):
   * In `OpenResearchLeaves14` to `27` (structures in TailZ23, 25 to 29, 33 to 38, 41 and 44), change the field type
     `_root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` to `_root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`.
     The name `mumfordGroupLaw` is kept.
   * TailZ23: add `import ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`. At its three sites,
     `qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw` becomes `qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw`.
   * TailZ34: `y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU` becomes
     `y3Connected_of_ab_gl (qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw) (y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU)`.
2. **TailZ45, research bundle:**
   * Add `import ZInQKernel.Contrib.OneProof.NeronGoodModelIso`.
   * In `OpenResearchLeaves28`, the field `mumfordGroupLawConn : MumfordGroupLawConn` becomes
     `neronSchemeExtensionDedekind : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind`.
   * Set `mumfordGroupLaw := ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.
3. **TailZ45, textbook bundle:**
   * New `structure OpenTextbookLeaves14`: `OpenTextbookLeaves13` without `neronSchemeExtensionExists`.
   * New `openTextbookLeaves13_of_OpenTextbookLeaves14 (n) (h : NeronSchemeExtensionDedekind)`, which sets
     `neronSchemeExtensionExists := neronSchemeExtensionExists_of_dedekind h`.
   * New top theorem `sixContactMin_of_open39 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves14) (l : OpenAddedLeaves19)`.
4. **Main.lean:** `frozenTarget` takes `t : HDec.HSyn.OpenTextbookLeaves14` and calls `sixContactMin_of_open39 r t l`.

The integrator should also:
* update the docstrings of the narrowed fields (unchanged by the patch);
* give `OpenResearchLeaves28` a new name, or keep the in-place edit as group-law-dvr's F2 did;
* regenerate the kinds.tsv and OPEN.md rows. `neronSchemeExtensionDedekind` is the printed leaf; the rows
  `mumfordGroupLawConn` and `neronSchemeExtensionExists` go.

## 5. Fold check (overlay)

PENDING

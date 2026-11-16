# weil-proof results log

Base 0caafe66 (origin/main) + merge of origin/wip/pic-dict 4e95795b (PicDictionary.lean, clean merge).

## Statement
`T09Pic.WeilPairingMumford` (ZInQKernel/OneProof/H/TailZ24.lean:708), field `OpenAddedLeaves17.weilPairingMumford`.
pic-dict: `PicDict.weilPairingMumford_final` from 7 Mumford leaves over k = k̄ (MumfordSquareAC, MumfordMulNPicZeroAC,
MumfordPhiSurjectiveAC, MumfordWeilPairingAC, MumfordWeilNondegAC, MumfordWeilAltAC, MumfordKLFiniteAC).
weil-used (origin/wip/weil-used 8ea3eaf3): consumers read only left kernel, Galois, compat, e(x, λ_L x) = 0 (VERIFIED there by probe).

## 11-16 results (scratch/weil-proof/Generic.lean, imports ZInQKernel.Contrib.OneProof.PicDictionary)
- VERIFIED (compiles, standard axioms): generic lemmas on `PicDict.Transport.wf` over any scheme:
  `wf_comp` (cocycle wf(t1≫t2) = t1^*(wf t2)·wf t1), `wf_id` (wf 𝟙 = 1), `wf_isUnit`, `wf_change`
  (change of trivialization, ratio t-invariant ⇒ same value).
- VERIFIED: over any field k, X : AbVar k: translations act trivially on Γ(X,𝒪) (`tr_appTop`, from the vendored
  bijectivity of constants), `formula_indep` (part (i)), `formula_root` (part (ii)), `formula_mul` (part (iii)),
  `formula_pow`. IsAlgClosed not needed.
- VERIFIED: `mumfordWeilPairingAC_of_bilinRight : MumfordWeilBilinRightAC → MumfordWeilPairingAC`;
  `weilPairingMumford_of_bilinRight` (7 leaves: pic-dict's six other + MumfordWeilBilinRightAC); axioms standard.
- Finding: part (iv) (multiplicativity in the class) needs monoidal coherence of the vendored pullback monoidal
  structure (built by localization lifting) with Mathlib's `Scheme.Modules.pullbackComp` (adjunction-mate) and
  `pullbackObjUnitIso` vs ε. Not in the tree; out of reach today.
- VERIFIED: `wf_tensor_ratio` (from `PullbackCompMonoidal`: wf(ψ⊗ψ')·r_t = wf ψ · wf ψ', r_t = ratio of
  pullbackObjUnitIso⁻¹ and ε), `wf_unit`, `unitRatio_tr` (r_t = 1 for translations, derived: no unit-coherence
  hypothesis needed), `mumfordWeilBilinRightAC_of_pullbackCompMonoidal`,
  `mumfordWeilPairingAC_of_pullbackCompMonoidal : PullbackCompMonoidal → PicDict.MumfordWeilPairingAC`,
  `weilPairingMumford_of_pullbackCompMonoidal` (6 Mumford leaves + GLUE PullbackCompMonoidal); standard axioms.
- `PullbackCompMonoidal`: Mathlib's `Scheme.Modules.pullbackComp f g` commutes with the vendored tensorators μ
  (Modules/PullbackMonoidal.lean, built by Localization.Monoidal.functorMonoidalOfComp). Not proved: needs the
  presheaf-level pullbackComp monoidal + compatibility of `sheafificationCompPullback` with pullbackComp
  (conjugate computation). Rated GLUE (formal, STANDARD in the theory: pullback is a monoidal pseudofunctor).

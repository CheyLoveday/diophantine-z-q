# Active residual witness: verification

## Result

`Witness.lean` applies both RC53 residual-count constructors,
`ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine` and
`ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual`, to one instance in which the
derivative labels, the old Kummer labels, the local conditions, the support change and the residual
model carry content (`activeGenuineCounts`, `activeActualCounts`). The instance and the status of
every input are in `Hypotheses.md`. Summary:

* `K = ℚ(i)`, `E₁₁ : y² = x(x − 11)(x + 33)`, `N = 66`, moving prime `5`, derivative prime `7`,
  active prime `13`; `S` = places above `{2, 3, 5, 7, 11}`, `S'` adds the places above `13`;
  coefficients the actual residual module `𝔽₂ ⊗ M₁` of `E₁₁` (index `j = 0`).
* Genuine local conditions: the Kummer complex of `E₁₁(K_v)` above `2, 3, 11`, the relaxed
  derivative condition `τ≤1` above `7`, the full condition above `5`; unramified conditions at the
  active places.
* The residual model consists of the cohomology of the global complex, of the local conditions and
  of the local complexes, with the induced maps, and maps to the genuine Selmer complex by an actual
  quasi-isomorphism (`formalMap_quasiIso`, valid for arbitrary local conditions over a field).
* `hcondD` and `hfull` are used with realized premises; `hUm` holds with equality, its left side is
  at least `2`, and the old Kummer rows have exactly Mattuck's dimension with nonzero `H¹`; `hLm`
  has left side at least `2`; the support change has new places; the change of condition has a
  nonzero acyclic quotient; the minimal model is reached through the genuine support change and the
  change of condition.
* Both constructors give `2 ≤ genericRank < rankTot` and `genericRank ≤ 294`
  (`56·3 + 8·0 + 56·1 + 70`).
* Not available: the text's change from the unramified to the full condition at an active place has
  a non-acyclic quotient over `𝔽₂` (proved: `active_full_change_not_acyclic`); its acyclicity in the
  text needs the inversion of `t`. The witness uses the contractible thickening instead.

## Verification performed

* Base revision `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc` (detached worktree; the consumers'
  modules were already compiled). No existing file was edited and no prerequisite module was
  built. The only repository operations were one read-only query of the current revision and of
  the working-tree status at the start; nothing was committed, checked out or changed. Nobody was
  contacted.
* `Witness.lean` was compiled as a single file with the repository's environment, six Lean worker
  threads, CPU affinity 64–79 and niceness 10: exit status 0, no errors and no warnings, about 65
  seconds.
* Options: `maxHeartbeats 400000` (the only heartbeat setting) and
  `backward.isDefEq.respectTransparency false` (as in the earlier residual witness), the latter
  after the copied Kummer section.
* Source guard: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, notation, macro,
  syntax, `#eval`, `run_cmd`, `#check` or `#print` in `Witness.lean`. Finite facts are proved by
  `decide` and `norm_num`. No new proposition is assumed: the printed inputs are the existing
  explicit hypotheses. The only new `Prop`-valued definition is the abbreviation `Good C`
  ("finite cohomology vanishing outside degrees `0, 1, 2`"), proved for every complex it is applied
  to; `ModelMap` is a structure of data.
* Public text guard: no internal tool, platform or session names and no filesystem paths in the
  shipped files.
* Axiom audit: a separate copy of `Witness.lean` followed by `#print axioms` for each of its 367
  named declarations (all public theorems, definitions, abbreviations and named instances,
  including the copied Kummer section). Every report is a subset of
  `[propext, Classical.choice, Quot.sound]`; 359 use exactly these three. `Axioms.txt` is the
  complete list. The audit copy is not shipped.
* The section `LocalKummer` is a verbatim copy of the declarations of the module
  `ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer` (source file 60382 bytes, SHA-256
  `e16fd9b3aa8c3156a16d41f90ac8f92e40f8656edf206e127b5ad45196003cb3`), whose compiled form is not part
  of the build; only the namespace is changed. Its other dependencies are compiled modules.

## Main statements

Namespace `ZInQ.Contrib.RC53Assist.ResidualWitnessActive`. In the first group `k` is a field and
`GS, Gv, loc, M, Δ` are arbitrary Galois-type data (as in the repository's `selData`); `v` is a
finite place of `ℚ(i)`. Each statement below has axioms `[propext, Classical.choice, Quot.sound]`.

```lean
theorem homologyModelTo_quasiIso (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    QuasiIso (homologyModelTo C)

theorem exists_htpy {X Y : CochainComplex (ModuleCat.{0} k) ℤ} (f : X ⟶ Y) (n : ℤ) :
    ∃ h : X.homology n ⟶ Y.X (n - 1), h ≫ Y.d (n - 1) n =
      ((homologyModelTo X).f n ≫ f.f n : X.homology n ⟶ Y.X n) -
        HomologicalComplex.homologyMap f n ≫ (homologyModelTo Y).f n

theorem ModelMap.sel_quasiIso (F : ModelMap D₁ D₂) (hG : QuasiIso (GHom.toCC F.gG))
    (hU : QuasiIso (GHom.toCC F.gU)) (hL : QuasiIso (GHom.toCC F.gL)) :
    QuasiIso (GHom.toCC F.sel)

theorem piMap_quasiIso {ι : Type} {A B : ι → GCx k} (f : ∀ v, GHom (A v) (B v))
    (hf : ∀ v, QuasiIso (GHom.toCC (f v))) : QuasiIso (GHom.toCC (piMap f))

theorem formalMap_quasiIso :
    QuasiIso (GHom.toCC (formalMap GS Gv loc M Δ).sel)

theorem newPlaces_nonempty : Nonempty (NewPlaces SmallK SmallS SmallS')

theorem Tv_trivial (σ : Gloc SmallK v) (t : Tv v) : σ • t = t

theorem kumIota_equivariant (σ : Gloc SmallK v) (t : Tv v) :
    kumIota v (σ • t) = σ • kumIota v t

theorem kumLambda_injective : Function.Injective (kumLambda v)

theorem finrank_kum_H1_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 1) =
      Module.finrank (ZMod 2) (ModN (smallCurve (v.adicCompletion SmallK)).toAffine.Point 2)

theorem kum_dims_eq :
    Module.finrank (ZMod 2) ((kumCC v).homology 0) +
        Module.finrank (ZMod 2) ((kumCC v).homology 1) +
        Module.finrank (ZMod 2) ((kumCC v).homology 2) =
      kummerResidualDim v (smallLocalModels v)

theorem kum_H1_pos : 0 < Module.finrank (ZMod 2) ((kumCC v).homology 1)

theorem actΔ_U_oldKummer (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1)

theorem actΔ_U_derivRelaxed (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .derivRelaxed) :
    actΔ.U v = ofCC (relCC v.1)

theorem actΔ_U_full (v : Places SmallK SmallS) (hv : actCond v.1.asIdeal = .full) :
    actΔ.U v = ofCC (locCC v.1)

theorem oldKummer_places_exact (v : Places SmallK SmallS)
    (hv : actCond v.1.asIdeal = .oldKummer) :
    actΔ.U v = ofCC (kumCC v.1) ∧ 0 < Module.finrank (ZMod 2) ((kumCC v.1).homology 1) ∧
      Module.finrank (ZMod 2) ((kumCC v.1).homology 0) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 1) +
          Module.finrank (ZMod 2) ((kumCC v.1).homology 2) =
        kummerResidualDim v.1 (smallLocalModels v.1)

theorem act_hUm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ≤
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p

theorem act_hUm_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p

theorem act_hLm (h28 : MilneADT_I_2_8) :
    ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes 66 5 actD, genLocSum SmallK SmallS p

theorem actPP_quasiIso : QuasiIso actPP

theorem actPL_quasiIso (h788 : NekovarProp788ii SmallK) : QuasiIso actPL

theorem exists_derivative_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed

theorem exists_oldKummer_place :
    ∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer

theorem act_U_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n)

theorem act_L_positive (h28 : MilneADT_I_2_8) :
    2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1))

theorem actW_nontrivial : Nontrivial (actW.X 0)

theorem actP_d_ne_zero :
    ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0

theorem activeBound :
    residualBoundConstant (2 * 66).primeFactors.card 0 actD.card = 294

theorem residualRankCounts_genuine_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeGenuineCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ≤ 294

theorem residualRankCounts_actual_active (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤
        (activeActualCounts h410 h51 h28 h23 h788).rankTot ∧
      (activeActualCounts h410 h51 h28 h23 h788).genericRank ≤ 294

theorem activeGenuineCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeGenuineCounts h410 h51 h28 h23 h788).genericRank <
      (activeGenuineCounts h410 h51 h28 h23 h788).rankTot

theorem activeActualCounts_strict (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    (activeActualCounts h410 h51 h28 h23 h788).genericRank <
      (activeActualCounts h410 h51 h28 h23 h788).rankTot

theorem two_le_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    2 ≤ (activeGenuineCounts h410 h51 h28 h23 h788).genericRank ∧
      2 ≤ (activeActualCounts h410 h51 h28 h23 h788).genericRank

theorem active_instance_nondegenerate (h28 : MilneADT_I_2_8) :
    (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .derivRelaxed) ∧
      (∃ v : Places SmallK SmallS, actCond v.1.asIdeal = .oldKummer) ∧
      Nonempty (NewPlaces SmallK SmallS SmallS') ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.U.X n) ∧
      2 ≤ ∑ n ∈ actDegrees, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) ∧
      Nontrivial (actW.X 0) ∧
      ∃ x : (selCx actSel).toCC.X 0, ((selCx actSel).toCC.d 0 (0 + 1)).hom x ≠ 0

theorem active_unramified_not_full (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS')
    (φ : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM))))) :
    ¬ QuasiIso (GHom.toCC φ)

theorem active_full_change_not_acyclic (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (q : NewPlaces SmallK SmallS SmallS') {W : GCx (ZMod 2)}
    (f : GHom (natCx (contCochains (ZMod 2) (GUr SmallK q.1) (ResMod (urFactor SmallK q) SmallM)))
      (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))))
    (g : GHom (natCx (contCochains (ZMod 2) (Gloc SmallK q.1)
        (ResMod (locMap SmallK SmallS' q.1) (ResMod (inflMap SmallK smallS_sub) SmallM)))) W)
    (hfg : ∀ i u, g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl))
    (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i u, g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u) :
    ¬ W.toCC.Acyclic
```

## The target declarations

* `ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine` (source 6952 bytes, SHA-256
  `41da1457b6701d6a8b150223a7e9afe23bc4f838d50f3fea01027345477d33dd`)
* `ZInQ.Contrib.CloudB3RC53.GenuineInst.residualRankCounts_actual` (source 16216 bytes, SHA-256
  `e40818f9ec3bb06b69a37af56e9c71eaa23fb0764dd5e12b2660ddc7b3e9a657`)

## File identities

* `Witness.lean`: 204147 bytes; SHA-256 `0c36b8b49ccc1a6318dd2648d7c8565df497d6120252c954706aa7594228a18e`.
* `Hypotheses.md`: 9546 bytes; SHA-256 `7ee43b7f56a2888275739727f19aa700bd4272f89006cd6311b39c586a80d305`.
* `Axioms.txt`: 38469 bytes; SHA-256 `a4d2192bd5dbcc540c18570d0d91d0a1b60b459503c58bd6e12309f1ac228bb1`.

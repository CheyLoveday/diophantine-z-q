# weil-proof: the field `weilPairingMumford`

Task weil-proof. Base `0caafe66` (fork main 2880fef1 + STATUS w80), with `origin/wip/pic-dict` (4e95795b) and
`origin/wip/pic-fix` (be79cb5b) merged (both clean; their `PicDictionary.lean` and `PhiAmpleIsogeny.lean` are the
same blobs as in `origin/wip/leaf-fold32b`). Field `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford :
T09Pic.WeilPairingMumford` (`ZInQKernel/OneProof/H/TailZ24.lean:708`).

## 1. Verdict

**The field is not removed outright.** Its perfectness clause is Mumford's nondegeneracy of `ē_n` (§20, through
the duality of §15 and `deg n_X = n^{2g}`) and its last clause is Mumford §23 (`e^L(x, x) = 1`); neither has any
Lean infrastructure in the tree (no Cartier duality of `ker n_X` and `ker n̂`, no theorem of the cube or seesaw, no
theta groups), and neither is in reach in a day. Five of pic-dict's seven Mumford displays remain leaves.

**What is new (all VERIFIED: compiled, standard axioms):**

1. **Mumford's §20 display is a theorem, modulo one formal glue statement about the library.**
   pic-dict's leaf `PicDict.MumfordWeilPairingAC` (the formula `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` is independent of `ψ`,
   is a constant `n`-th root of unity, and is bilinear) is proved:
   * three of its four conjuncts **outright**, over any field (`formula_indep`, `formula_root`, `formula_mul`);
   * the fourth (multiplicativity in the class `M`) from `WeilProof.PullbackCompMonoidal`: Mathlib's
     `Scheme.Modules.pullbackComp f g` commutes with the tensorators of the vendored monoidal structure of
     `Scheme.Modules.pullback` (pull-back is a monoidal pseudofunctor). The unit constraint is *not* assumed
     (`unitRatio_tr` derives it on abelian varieties).
2. **The field** from five Mumford leaves, that glue, and the open field `phiAmpleIsogeny` (which replaces
   pic-dict's `MumfordKLFiniteAC`; in leaf-fold32 that field is `PicFix.phiAmpleIsogeny_of_printed` of two printed
   leaves):

   ```lean
   theorem WeilProof.weilPairingMumford_proof (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
       (h8 : MumfordPhiSurjectiveAC) (hA : PullbackCompMonoidal) (h20b : MumfordWeilNondegAC)
       (h23 : MumfordWeilAltAC) (h3 : T09Pic.PhiAmpleIsogeny) : T09Pic.WeilPairingMumford
   ```

   Variants: `weilPairingMumford_of_pullbackCompMonoidal` (with `MumfordKLFiniteAC` in place of the field) and
   `weilPairingMumford_of_bilinRight` (with the narrower §20 leaf `MumfordWeilBilinRightAC`, the fourth conjunct
   alone, in place of the glue).

**Count.** With honest flags (the two remaining `ē_n` leaves pending reading, the glue as project glue) the fold
raises GLUE: dry run `34/11 on 45 -> 37/13 on 50; strictest 34/11 -> 37/13` (needs `--allow-rise`). It is −1 or
0 only after `PullbackCompMonoidal` is proved and the §20/§23 readings clear (see §5). **Do not fold now**; fold
the file's theorem when one of those happens, or use `mumfordWeilPairingAC_of_pullbackCompMonoidal` to drop
pic-dict's §20 leaf from any fold of pic-dict's reduction.

## 2. Files

* `ZInQKernel/Contrib/OneProof/WeilFormula.lean` (namespace `WeilProof`; imports
  `ZInQKernel.OneProof.H.TailZ24`, the module that defines the statement, and
  `ZInQKernel.Contrib.OneProof.PicDictionary`). `lake build ZInQKernel.Contrib.OneProof.WeilFormula` succeeds. No
  build-time code.
* `scratch/weil-proof/Generic.lean`: the development copy (same content, compiled with `lake env lean`).
* `scratch/weil-proof/Discharges.lean`, output `scratch/weil-proof/discharges.txt`.
* `scratch/weil-proof/autofold.json`, dry-run module `scratch/weil-proof/FoldDryRun.lean` (compiles;
  `sixContactMin_of_open36` has the standard axioms).
* `scratch/weil-proof/log.md`.

## 3. The proofs

Notation: `X` a scheme, `m, t : X ⟶ X` with `t ≫ m = m`, `M` a module, `ψ : 𝒪_X ≅ m^*M`;
`wf t m h M ψ = (pOU t)⁻¹ ≫ t^*ψ ≫ θ_t ≫ ψ⁻¹ ∈ End(𝒪_X) = Γ(X, 𝒪)` (pic-dict's `Transport.wf`;
`θ_t = pullbackComp ≫ pullbackCongr`). `AC.formula x hx c ψ = wf (t_x) (n_X) _ (M_c) ψ`.

* `comp_val`: composition in `End(𝒪_X)` is multiplication of values (`Hom.app_smul`).
* `wf_comp` (**cocycle**): `wf (t₁ ≫ t₂) = t₁^*(wf t₂) · wf t₁`. Proof: `pOU_inv_comp`, naturality of
  `pullbackComp`, and `theta_comp` (`θ_{t₁t₂} = t₁^*θ_{t₂} ∘ θ_{t₁}`, from pic-dict's `pullbackComp_assoc_app`).
* `wf_id`: `wf 𝟙 = 1` (cocycle at `𝟙 ≫ 𝟙` and `wf_isUnit`).
* `wf_change`: replacing `ψ` by `ψ'` multiplies by `t^*(a)·a⁻¹`, `a = ψ' ψ⁻¹`; equal if `t^*a = a`.
* `tr_appTop`: on an abelian variety translations act trivially on `Γ(X, 𝒪)` (every global function is a
  constant: vendored `bijective_appTop_of_isProper_of_geometricallyIntegral`; `t_x` is a `k`-morphism).
* (i) `formula_indep` = `wf_change` + `tr_appTop`. (iii) `formula_mul` = `wf_comp` + `t_{xx'} = t_x ≫ t_{x'}` +
  `tr_appTop`. `formula_pow`, and (ii) `formula_root`: `ē(x)^n = ē(x^n) = ē(1) = 1`, and the value is `const u` with
  `u^n = 1` by bijectivity of constants.
* Tensor part (`alpha_tensor`, `wf_tensor_ratio`): with `ψ'' = λ⁻¹ ≫ (ψ ⊗ ψ') ≫ μ_m`,
  `α(ψ'') = r_t · λ⁻¹ (β ⊗ β') λ`, where `β = ε_t ≫ t^*ψ ≫ θ_t ≫ ψ⁻¹` and `r_t = (pOU t)⁻¹ ε_t⁻¹`; uses
  `PullbackCompMonoidal` (for `θ_t` on `M ⊗ M'`), `μ_natural`, the left unitality of `t^*` and
  Eckmann–Hilton (`unitor_tensor`). So `wf(ψ'') · r_t = wf ψ · wf ψ'`.
* `unitRatio_tr`: `r_t = 1` for translations: apply the previous line to `M = M' = 𝒪` with `ψ = ψ' = pOU_m⁻¹`
  (`wf_unit`: value 1), and compare `ψ''` with `pOU_m⁻¹` by `wf_iso` (unitor) and `wf_change`.
* `mumfordWeilBilinRightAC_of_pullbackCompMonoidal`: `formula_indep` to choose `ψ''`, `wf_iso` along
  `Scheme.Pic.mulIso`, `wf_tensor_ratio`, `unitRatio_tr`.

## 4. Consumers and narrowing

* The field is read once on the route, at `TailZ24.lean:808` (`t09SymmIsogenyExists_of_four`, in
  `addedLeaves12_of_open13`) — VERIFIED by grep on this base. weil-used (origin/wip/weil-used, probe over the
  closure of `frozenTarget`) found that below `T09_SymmIsogenyExists` only the left half of perfectness, Galois,
  compatibility and `e_n(x, λ_L x) = 0` for very ample `L` are read; clause 6 (`weilScalar` pin), the adjoint
  clause and the right half of perfectness are inert.
* A narrower form (characteristic 0, number fields, the abelian varieties used) does **not** help: the left half of
  perfectness and §23 are as deep in characteristic 0 as in general (they are the same Mumford arguments), so no
  narrowing makes the field provable today. The narrowing that would reduce trust is weil-used's read set
  (`WeilUsed.WeilPairingRead`); it requires rerouting through older bundle generations (weil-used §3) and was not
  done.

## 5. New statements and their rating

| statement | kind | printed form? | reason |
|---|---|---|---|
| `WeilProof.PullbackCompMonoidal` | **project glue** | n/a | Formal property of the library: Mathlib's `pullbackComp` (an adjunction mate) commutes with the vendored tensorators of `pullback` (built by `Localization.Monoidal.functorMonoidalOfComp`). True in the standard theory (pull-back of modules is a monoidal pseudofunctor); its truth for these Lean definitions is STANDARD in content but unproved here. Proof plan in §6. |
| `WeilProof.MumfordWeilBilinRightAC` (variant only) | published | yes, as a conjunct | Mumford §20 bilinearity, second variable, for the formula; same reading caveat as the next rows. Not used by `weilPairingMumford_proof`. |
| `PicDict.MumfordWeilNondegAC` (pic-dict's) | published | **pending reading** | Stated for the formula; it is the print only if §20 states `ē_n` by `t_x^*ψ ∘ ψ⁻¹` and not only through the duality of §15 (pic-fix's note). |
| `PicDict.MumfordWeilAltAC` (pic-dict's) | published | **pending reading** | Mumford §23, same caveat. |
| `PicDict.MumfordSquareAC`, `MumfordMulNPicZeroAC`, `MumfordPhiSurjectiveAC` (pic-dict's) | published | yes (unread) | Statements about line bundles only (no `ē_n`), Mumford §6 Cor. 4, §8 (iv), §8 Thm 1; locators UNVERIFIED. `MumfordPhiSurjectiveAC` is already a field in leaf-fold32. |

pic-dict's `MumfordWeilPairingAC` and `MumfordKLFiniteAC` are no longer assumptions of the field.

## 6. What remains

* `PullbackCompMonoidal` (see the plan in the log): reduce to sheafified objects `L A, L B`
  (`functorMonoidalOfComp_μ`), then two facts: (E) `c_{f,g}` at `L A` equals `f^*e_g ∘ e_f ∘ L(pc_{f,g}) ∘ e_{fg}⁻¹`
  (conjugate computation: every right adjoint involved is a pushforward and the comparisons are identities), and
  (P) the presheaf `pullbackComp` is oplax monoidal for the `leftAdjointOplaxMonoidal` structures (mates of the
  presheaf pushforward's `μ`, which is `m ⊗ m' ↦ m ⊗ m'`, and `pushforwardComp = Iso.refl`).
* Readings of Mumford §20 and §23 for the two pending leaves; all locators UNVERIFIED (no copy of Mumford on the
  host).

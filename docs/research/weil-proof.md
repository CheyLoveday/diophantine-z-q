# weil-proof: the field `weilPairingMumford`

Task weil-proof. Base `0caafe66` (fork main 2880fef1 + STATUS w80), with `origin/wip/pic-dict` (4e95795b) and
`origin/wip/pic-fix` (be79cb5b) merged (both clean; their `PicDictionary.lean` and `PhiAmpleIsogeny.lean` are the
same blobs as in `origin/wip/leaf-fold32b`). Field `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford :
T09Pic.WeilPairingMumford` (`ZInQKernel/OneProof/H/TailZ24.lean:708`).

## 1. Verdict

**The field is not removed outright**, but one of pic-dict's seven Mumford displays is now a Lean theorem with
no hypotheses, and the field rests on five displays plus an open field.

* Its perfectness clause is Mumford's nondegeneracy of `ē_n` (§20, through the duality of §15 and
  `deg n_X = n^{2g}`) and its alternation clause is Mumford §23 (`e^L(x, x) = 1`). Neither has Lean
  infrastructure in the tree (no Cartier duality of `ker n_X` and `ker n̂`, no theorem of the cube or seesaw), so
  nondegeneracy stays a leaf; §23 is attacked in §6.

**What is new (all VERIFIED: compiled, `#print axioms` = `[propext, Classical.choice, Quot.sound]`):**

1. **`WeilProof.mumfordWeilPairingAC_proof : PicDict.MumfordWeilPairingAC`.** Mumford's §20 display as pic-dict
   stated it: the formula `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` is independent of `ψ`, is a constant `n`-th root of unity,
   and is bilinear. Three conjuncts are proved from the cocycle relation of the formula over any field; the
   fourth (multiplicativity in `M`) from `PullbackCompMonoidal`.
2. **`WeilProof.pullbackCompMonoidal_proof : PullbackCompMonoidal`**: Mathlib's `Scheme.Modules.pullbackComp`
   commutes with the tensorators of the vendored monoidal structure of `Scheme.Modules.pullback` (pull-back of
   sheaves of modules is a monoidal pseudofunctor). New general lemma on the way: `Mates.leftAdjointCompIso_δ`
   (the left-adjoint comparison of a monoidal right-adjoint comparison is oplax monoidal).
3. **The field**:

   ```lean
   theorem WeilProof.weilPairingMumford_proof (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
       (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC)
       (h3 : T09Pic.PhiAmpleIsogeny) : T09Pic.WeilPairingMumford
   ```

   `h3` is the open field `phiAmpleIsogeny` (it replaces pic-dict's `MumfordKLFiniteAC`, whose only use was to
   produce it; in leaf-fold32 the field is `PicFix.phiAmpleIsogeny_of_printed` of two printed leaves).
   Variant `weilPairingMumford_of_six`: `MumfordKLFiniteAC` in place of `h3`.

**Count** (dry runs on this base, `scratch/weil-proof/autofold*.json`; each printed module compiles):

| flags of `mumfordWeilNondegAC`, `mumfordWeilAltAC` | dry run |
|---|---|
| pending reading (honest: they are stated for the formula, see §5) | `34/11 on 45 -> 37/12 on 49; strictest 34/11 -> 37/12` (needs `--allow-rise`) |
| unread (pic-dict's rating) | `34/11 on 45 -> 39/10 on 49; strictest 34/11 -> 39/10` |

So the fold is −1 once the §20/§23 readings confirm that Mumford states `ē_n` by the formula; with honest flags
it is +1 now. pic-dict's own reduction had seven leaves (four of them pending readings); this one has five
(two pending readings).

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
| `WeilProof.PullbackCompMonoidal` | **proved** (`pullbackCompMonoidal_proof`) | n/a | Not a leaf. |
| `WeilProof.MumfordWeilBilinRightAC` (variant only) | published | yes, as a conjunct | Mumford §20 bilinearity, second variable, for the formula; same reading caveat as the next rows. Not used by `weilPairingMumford_proof`. |
| `PicDict.MumfordWeilNondegAC` (pic-dict's) | published | **pending reading** | Stated for the formula; it is the print only if §20 states `ē_n` by `t_x^*ψ ∘ ψ⁻¹` and not only through the duality of §15 (pic-fix's note). |
| `PicDict.MumfordWeilAltAC` (pic-dict's) | published | **pending reading** | Mumford §23, same caveat. |
| `PicDict.MumfordSquareAC`, `MumfordMulNPicZeroAC`, `MumfordPhiSurjectiveAC` (pic-dict's) | published | yes (unread) | Statements about line bundles only (no `ē_n`), Mumford §6 Cor. 4, §8 (iv), §8 Thm 1; locators UNVERIFIED. `MumfordPhiSurjectiveAC` is already a field in leaf-fold32. |

pic-dict's `MumfordWeilPairingAC` is a theorem and `MumfordKLFiniteAC` is no longer an assumption of the field (it enters only through the open field `phiAmpleIsogeny`).

## 6. What remains

* `PullbackCompMonoidal` (see the plan in the log): reduce to sheafified objects `L A, L B`
  (`functorMonoidalOfComp_μ`), then two facts: (E) `c_{f,g}` at `L A` equals `f^*e_g ∘ e_f ∘ L(pc_{f,g}) ∘ e_{fg}⁻¹`
  (conjugate computation: every right adjoint involved is a pushforward and the comparisons are identities), and
  (P) the presheaf `pullbackComp` is oplax monoidal for the `leftAdjointOplaxMonoidal` structures (mates of the
  presheaf pushforward's `μ`, which is `m ⊗ m' ↦ m ⊗ m'`, and `pushforwardComp = Iso.refl`).
* Readings of Mumford §20 and §23 for the two pending leaves; all locators UNVERIFIED (no copy of Mumford on the
  host).

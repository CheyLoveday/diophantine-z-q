# gt-rigidity: `MumfordRigidityCore` reduced to two printed leaves; Cor. 6.4 proved

Task gt-rigidity, 2026-11-14/15. Base a454ad64 (leaf-fold16). Lean: `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean`
(the contribution) and `scratch/gt-rigidity/`. Results log: `scratch/gt-rigidity/log.md`. No other file under
`ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. Model work, no human review.

Marks: **VERIFIED** (compiled, computed, or read in a file), **STANDARD** (published, with a reference),
**SPECULATIVE** (a judgement), **UNVERIFIED** (a theorem number recalled without a source; no network, and
*GIT* is not in the repository).

## 1. Main result

**`MumfordRigidityCore` is proved from two printed leaves, and its clause (a) (*GIT* Cor. 6.4) is now a Lean
proof.** VERIFIED: compiled, standard axioms only.

```
theorem ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
    (hG : MumfordGroupLaw) (hR : RigidityLemma) : LeafQM.AV.R1UnivRigid.MumfordRigidityCore
```

`#discharges` (scratch/gt-rigidity/Discharges.lean, output `scratch/gt-rigidity/discharges-output.txt`):

```
DISCHARGES [OpenResearchLeaves16.mumfordRigidityCore] by ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
  still assumes: [ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, ZInQ.Contrib.MumfordRigidity.RigidityLemma]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 514 theorems checked, 1 discharge one
```

(Section 5 will be updated if the further reduction of `RigidityLemma` lands.)

## 2. The leaves

* **`MumfordGroupLaw`** (LEAF, *GIT* Thm. 6.14, number UNVERIFIED). This is the existence half of
  `MumfordRigidityCore`, verbatim: the same hypotheses, and the conclusion `∃ _ : GrpObj F, η[F].left = e`
  without clause (a). `mumfordGroupLaw_of_core : MumfordRigidityCore → MumfordGroupLaw` compiles, so it is
  strictly weaker. Its form is the one r1univ-rigid gave: Thm. 6.14 applied on each connected component.
  Lean 4.35 cannot prove it: the proof is Grothendieck's (deformations of the group law over Artinian
  thickenings, with the obstruction in `H²(A, 𝒪)` killed by rigidity, then Grothendieck existence). Mathlib
  has none of that machinery (SPECULATIVE).
* **`RigidityLemma`** (LEAF, *GIT* Prop. 6.1, number UNVERIFIED). The setup: `S` connected and locally
  noetherian; `p : X → S` proper, smooth, geometrically connected; `q : Y → S` separated and locally of finite
  type; `f : X → Y` over `S`. If `f(X_s)` is a single point for one `s`, then `f = p ≫ σ` for a section `σ`.
  *Form*: a consequence of the printed statement, never stronger. The printed hypotheses are `p` proper and
  flat with `H⁰(X_s, 𝒪) = k(s)`, `S` connected. Smooth gives flat with geometrically reduced fibres, and with
  proper and geometrically connected it gives `H⁰ = k(s)` (Stacks 0BUG, tag UNVERIFIED). The conditions on
  `Y` and the noetherian hypothesis on `S` are extra assumptions.

Both are stated over Mathlib's `Scheme`, `IsProper`, `Smooth`, `GeometricallyConnected`, `IsSeparated` and
`GrpObj`, and over the kernel's `PkgI3.AbVar` and `IsAbVarFibre`. Neither is vacuous or a disguised form of the
conclusion: `RigidityLemma` says nothing about groups.

## 3. What is proved (all VERIFIED, `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean`)

* `isOpen_connectedComponent_of_noetherianSpace`: in a noetherian space, connected components are open.
* `isOpen_connectedComponent_of_isLocallyNoetherian`: the same in a locally noetherian scheme.
* `eq_of_rigidity`: the rigidity lemma on every connected component. Let `p : X → T` be proper, smooth and
  geometrically connected over a locally noetherian `T`, with a section `j`, and let `f' : X → X` be over
  `T`. If every connected component of `T` contains a point whose fibre `f'` sends to a point, then
  `f' = p ≫ j ≫ f'`. Proof: restrict to the open component (`morphismRestrict`, `resLE`), apply
  `RigidityLemma`, glue with `Scheme.hom_ext_of_forall`.
* `isPullback_jr`: `x ↦ (x, 1)` is the base change of `η` along `snd : F ×_S F → F`.
* `fibre_value`, `eta_mem_connectedComponent`, `defect_eq_one`.
* `isMonHom_of_rigidity`: *GIT* Cor. 6.4 for endomorphisms. If a group object `F` of `Over S` is proper,
  smooth and geometrically connected over a locally noetherian `S`, then every endomorphism fixing `η` is a
  homomorphism. This is Mumford's argument with the defect `d(x, y) = f(xy)(f(x)f(y))⁻¹`.
* `mumfordGroupLaw_of_core`, `mumfordRigidityCore_of_printed`.

## 4. What remains

* `MumfordGroupLaw`: a leaf, out of reach in Lean today (deformation theory).
* `RigidityLemma`: a leaf; see section 5.

# degpoly-proof results log

Base: wip/deg-det ecf7da39 + merge origin/main (e41a7169, STATUS.md only) + merge origin/wip/homfree-proof (a0570509;
lattice representation, `HomFreeC.homFreeFiniteC`). Build dir copied (reflink) from ~/dzq-wt/deg-det (same commit ecf7da39).

## Findings (before Lean)

- F1 (VERIFIED, read): `DegHomogPoly` and the field `charPolyIndepOfEllAlgClosed` quantify over every algebraically closed
  `k`, char p included. The field reaches the proof through `HSyn.t7_of_algClosed5` (TailN L215, TailO L2865: bundle field
  `t7 : PkgI3.CharPolyIndepOfEll`, stated over EVERY field) and `R16Split.r16_of_printed` (TailZ35 L89). Same shape as
  homfree-proof's T6: a "-1, no new leaf" needs a reroute of T7's consumers, not an autofold.
- F2 (VERIFIED, math): over a field with `emb : K̄ → ℂ` the field needs NO degree theory: conj-twist's injective natural
  `α : ℤ_ℓ ⊗ Λ ↪ T_ℓ` and rank `T_ℓ = 2g` make `V_ℓ(φ)` conjugate to `φ|_Λ ⊗ ℚ_ℓ`, so
  `charpoly V_ℓ(φ) = charpoly_ℤ(φ|_Λ)`, monic in `ℤ[X]`, independent of `ℓ`.

## Lean

- VERIFIED compiled (`lake env lean scratch/degpoly-proof/CharPolyC.lean`, no errors):
  `DegPolyScratch.charpoly_V_eq` (charpoly of `toMatrix b b (V_ℓ φ)` = `(latEnd Λ M _).charpoly.map`),
  `DegPolyScratch.charPolyIndep_of_emb (HL : UniformizationLeafAll) (HT : MumfordTorsionAlgClosed) (emb : K̄ →+* ℂ) A φ`
  = the body of `PkgI3.CharPolyIndepOfEll` for this `K`, `A`, `φ`.
- VERIFIED compiled: contribution `ZInQKernel/Contrib/OneProof/CharPolyLattice.lean` (imports TailE, TailQ, AVB1.AlgClosed,
  LF4T5 only: independent of deg-det's and homfree-proof's unmerged files) `lake build ZInQKernel.Contrib.OneProof.CharPolyLattice`
  OK (11761 jobs). Theorems: `charpoly_V_eq`, `charPolyIndep_of_emb`, `charPolyIndepOfEllC` (T7 over fields with σ : k →+* ℂ),
  `charPolyIndepOfEllAlgClosedC`, `charPolyIndepOfEllAlgQ`, new leaf def `CharPolyIndepOfEllAlgClosedNoEmb`,
  `charPolyIndepOfEllAlgClosed_of_noEmb : UniformizationLeafAll → MumfordTorsionAlgClosed → CharPolyIndepOfEllAlgClosedNoEmb →
  ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed`.
- VERIFIED: `lake build +Main +Discharges +CharPolyLattice` OK (13699 jobs, frozenTarget standard axioms). #discharges
  (scratch/degpoly-proof/Discharges-output.txt): DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by
  CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb, still assumes [UniformizationLeafAll, MumfordTorsionAlgClosed,
  CharPolyIndepOfEllAlgClosedNoEmb], axioms standard. (56 open hypotheses, 2878 theorems checked, 8 discharge one.)
- VERIFIED: autofold dry run (scratch/degpoly-proof/autofold.json): `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`;
  module scratch/degpoly-proof/FoldDryRun.lean (line 1 stripped) compiles, `HDec.HSyn.sixContactMin_of_open36` standard axioms.

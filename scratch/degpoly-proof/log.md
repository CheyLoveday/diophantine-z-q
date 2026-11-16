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

## Consumers of the field / T7 (VERIFIED, `scratch/degpoly-proof/Closure.lean` over frozenTarget's closure, 259,568 constants; output closure_out.txt)

- Constants with T7/the field in their type (non-bundle): `t7_of_algClosed5`, `charPolyIndepOfEll_of_algClosed`,
  `PkgI3.trace_indep_of_ell`, `GlueC10Link.trace_endE_indep`, `GlueC10Link.trace_T_of_frobCompare`,
  `G14Trace.common_trace`, `G14Trace.g14TraceCompat_of_link`, `G0AssembleMod.linkedTateData_of_local`,
  `R16Split.trace_endV_rat`, `rank_two_of_dim`, `r16_of_coreY`, `r16_of_printed`. Call graph: `gluePieces_of_open4` uses
  `OpenTextbookLeaves4.t7` only through `linkedTateData_of_local` -> `g14TraceCompat_of_link` -> `common_trace` ->
  `trace_T_of_frobCompare` -> `trace_endE_indep` -> `trace_indep_of_ell`; `openResearchLeaves21_of_OpenResearchLeaves22` uses
  the field through `r16_of_printed` -> ... -> `trace_endV_rat` (A : AbVar ℚ).
- F3 (VERIFIED, read TailC L8718-8742 and FrobChain/LinkedStatement.lean L43-49): `common_trace` applies T7
  (`trace_T_of_frobCompare hM Ab α`) to `Ab : PkgI3.AbVar k` where `k` comes from `FrobTraceLink`:
  `∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ Ab α N, ...` — a field of CHARACTERISTIC p (the reduction of A mod p and
  its Frobenius). So the characteristic-p case of Mumford §19 Thm 4 is genuinely consumed; no narrowing to fields
  embedding into ℂ can remove the field. The R16 branch is over ℚ (covered by CharPolyIndepOfEllC).
- Consequence: the new leaf `CharPolyIndepOfEllAlgClosedNoEmb` is live (used in char p); "-1, no new leaf" is out of reach
  for this field by narrowing, and so is a proof of `DegHomogPoly` outright (char p needs cube + Riemann-Roch or similar).

## DegHomogPoly over fields embedding into ℂ (in progress)

- VERIFIED compiled (scratch/degpoly-proof/KerFibre.lean): `eq_of_closed` (two `Spec L → X` over `Spec k`, `k` alg. closed,
  through the same closed point are equal; Mathlib's `residueFieldIsoBase` + `descResidueField_stalkClosedPointTo_fromSpecResidueField`),
  `isClosed_of_mem_fibre` (points of the fibre of a locally quasi-finite map over a closed point are closed),
  `pt_eq_of_closed`, `e0`, `one_left_apply`, `isClosed_e0`, and for `ψ` with `IsFinite ψ.hom.left`:
  `card_ker_eq L : Nat.card (ptMap (L := L) ψ).ker = Nat.card (Fibre ψ)` for EVERY field `L` with `Algebra k L`
  (Fibre ψ = ψ⁻¹(e₀), finite), `finite_ker`.

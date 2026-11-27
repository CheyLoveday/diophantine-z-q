# Berger reroute: results log

## 1. Sizing (VERIFIED in the base Lean tree and manuscript)

Both rows live in `HDec.PkgI4.PanDict` in
`ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean` (below: **PF**);
`bergerSurveyF` and `panPrintedF` are fields in
`ZInQKernel/OneProof/H/CMOpen.lean`. Bare filenames in this table are
relative to `ZInQKernel/Contrib/OneProof/`. Note locators are from the
existing inventory and were not reread in this run.

| Brinon–Conrad item (preliminary CMI notes) | Berger row | Pan row | Lean |
| --- | --- | --- | --- |
| Def. 4.4.7 p. 60 and p. 131: de Rham period ring | `dR` premise; also ambient ring for the conclusion | Ambient ring for the pst hypothesis | `HDec.PkgI4.BdR` in `ZInQKernel/Contrib/G9/I4Layer.lean`, `PanBergerSplit.bdrLin` in `PanBergerPrinted.lean`; comparison with Mathlib's `BDeRham` via `DeRhamPrint.TDict` and `DeRhamPrint.BdRT` (`DeRhamPrintTDict.lean`, `BdRT.lean`) |
| Thm 4.4.13 p. 64 and §5.2 pp. 67–68: de Rham fixed field and dimension condition | `dim_{Q_p} D_dR = dim_{Q_p} V` | No separate de Rham hypothesis | `PanBergerSplit.ddrU`, `IsDeRhamU` in `PanBergerPrinted.lean`; `BdRInv.bdRInvariantsPrinted_proof` in `BdRInvariants.lean`; element form `LogPTransc.bdr_invariant_eq_algebraMap` in `LogPTranscendenceBdR.lean` |
| §5.2 pp. 67–68: fixed ring, diagonal tensor invariants, dimension form of admissibility | pst conclusion | pst premise | `BergerBst.fixedSub`, `inclT`, `dB`, `IsAdmissible` in `BergerBst.lean`; `BmaxOne.isAdmissible_of_T` in `PanBergerPst.lean`, `FontaineSt.isPstF_of_basis` in PF |
| Thm 9.3.5 p. 148: finite extension meaning of pst; “only if” direction of monodromy theorem | Definition **and** de Rham → pst theorem | Definition only; Pan assumes pst | `FontaineSt.IsPstF`, `LocalIsPstF` in PF; `PstModel.localIsPstF_iff_forall` in `PstModel.lean` (Lean model independence, no additional notes theorem) |
| pp. 128–129: completed divided power envelope and description of its image | pst coefficients | same | `FontaineSt.AcrisOf`, `dpSeries`, `acrisOf_eq` in PF; `PstModel.bcrisPlusOf_eq_printed` in `PstModel.lean` compares the series sets, not the abstract completed PD envelope |
| Def. 9.1.4 p. 131: $B_{cris}$ and the inversion of $t$ | pst coefficients | same | `FontaineSt.BcrisPlusOf`, `bcrisPlusOf_eq_set`, `BcrisOf` in PF; `BmaxOne.tOf` in `PanBergerPst.lean` |
| Def. 9.2.3 p. 138; pp. 140–142: abstract $B_{cris}[X]$, its operators and the logarithm embedding with `log$p$ = 0`; Thm 9.2.10 p. 143: injectivity | pst period ring (only Galois action enters the row) | same | `FontaineSt.BstFOf` and `bstF_stable` in PF, `BergerBst.logPTilde`, `bdrAct_logPTilde` in `BergerBst.lean`; `LogPTransc.bstFOf_eq_adjoin` and conditional `transcendental_bcrisOf`, `bcrisPolyEquiv` in `LogPTranscendence.lean` |

Sizing: the common predicate is one existential finite extension and
one rank equality. It sees the period ring and the Galois action only.
`PstModel` compares finite coefficient models, not two period rings.
The algebraic polynomial-to-image comparison is one injectivity
statement at the chosen `ξ`, with the cyclotomic generator exposed;
`BergerBst.LogPTildeTranscendental` is a stronger existing supplier,
equivalent to nonmembership in `Frac(Bmax)` by
`LogPTransc.logPTildeTranscendental_iff_notInFrac`.
`BmaxStToFontaine` (PF) is an existing unproved comparison in the
direction needed for the tree's $B_{max}[\log[\widetilde p]]$.

- VERIFIED (audit read; journal page UNVERIFIED): `docs/research/locators.md`
  R11 distinguishes arXiv v3 Thm 0.6 / Thm 5.19 from the later
  author copy Thm 0.7 / Cor. 5.22. Manuscript 739–741 and 11037–11040
  cite the theorem by name, without a number.
- VERIFIED (prior arXiv reading recorded in `docs/research/pb-p1.md`,
  §2): the paper uses basis admissibility and writes
  $B_{max}[\log[\bar\pi]]$; its §1.2 says the functor $D_{st}$ is
  the same as Fontaine's. Neither the analytic change from
  $\log[\bar\pi]$ to $\log[\widetilde p]$ nor the downstream
  $B_{max}$-to-$B_{cris}$ comparison is proved in the row's Lean
  dependencies.

## 2. Draft and scoped stop

- VERIFIED (source inspection): the new draft retains the invariant-basis
  conclusion on the normalized Fontaine image at `ξ`. The proposed bridge
  uses `FontaineSt.isAdmissible_of_pstF` and `bstFOf_eq_xi`.
- The literal mismatch is `BergerPaperStComparison p ell`, pending a
  construction of the paper's logarithm and comparison of admissibility.
  The abstract-polynomial issue is separately `FontainePolynomialEmbedding`;
  it is not a premise of the bridge for the embedded ring.
- VERIFIED (build tooling): restored existing Mathlib cache archives with
  offline `cache unpack!`. Missing project imports are being compiled with
  offline Lake; the Lean compiler invocations are serialized. The new
  proof and the headline check are pending the import build.
- Build incident: two Lake invocations briefly overlapped when a
  cancellation from the sandbox did not reach the first one. The
  compiler lock kept their Lean subprocesses serial. The first Lake
  run was stopped before any further restart.

## 3. Checks (VERIFIED)

- Offline `lake build` succeeded for `LogPTranscendence`,
  `ZInQKernel.OneProof.Discharges`, and the new contribution.
  The contribution also compiled directly with `lake env lean`.
- `lake env lean scratch/berger-reroute/Axioms.lean`: all three new
  theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean scratch/berger-reroute/Discharges.lean`: the unmodified
  matcher found `bergerSurveyF_of_thm06Print` for the exact row type;
  its only remaining assumption is `BergerThm06Print`. The harness
  checks the field in the source and matches that isolated row.
  The complete headline was not elaborated.
- `FontainePolynomialEmbedding` and `BergerPaperStComparison`
  remain open. The journal locator remains UNVERIFIED.

# y3-fix results log

## 2026-11-16 23:45 start
- Merged 579a89bb (y3abu-print) into wip/y3-fix (587c4b51f), no conflicts.
- Base top: sixContactMin_of_open48 (TailZ55); field `shimuraMainThmIDeligneY3AbU` still open (kinds.tsv: composite, GLUE).
  Textbook field `mumfordTorsionAlgClosed` (LEAF) available as `{t}.mumfordTorsionAlgClosed`. VERIFIED (kinds.tsv).

## Plan
- A1: drop `Nonempty (fieldPt Qbar ⟶ Y)` from the fine-moduli leaf; obtain the point from Ψ(i,1) ∈ Y(ℂ) of the
  Deligne leaf + Lean lemma (proper ℚ-scheme with a ℂ-point has a closed point, hence a ℚ̄-point: `exists_qbarPt`, TailL).
- A2: level structure in Mumford GIT Def 7.1 form (sections; at every geometric point s, η_s : 𝒪/3𝒪 → A_s(k)[3] bijective,
  A_s = Over.pullback s of the abelian scheme, Mathlib group law). Prove both comparisons with the kernel's `QMAbScheme`:
  print ⇒ kernel (epi Spec K̄ → Spec K); kernel ⇒ print (fibre QML3 as in SGRSplit.qmAbFieldFibre_of + Level3.onto, from
  TorsionStructure = torsionStructure_of_mumford t.mumfordTorsionAlgClosed).
- B: Deligne leaf lattice clause: analyse.

## 00:10 Part A compiled (VERIFIED, `lake env lean scratch/y3-fix/Y3Fix.lean`, standard axioms)
- `nonempty_qbar_of_cpt`: proper ℚ-scheme with a ℂ-point has a ℚ̄-point (closed point via compact T0 + exists_qbarPt).
- `QMAbSchemeNL`, `LevelPrint` (Mumford GIT Def 7.1 form: at every geometric point s, η_s : 𝒪/3𝒪 → A_s(k)[3]
  injective and onto the k-points x of the pulled-back fibre with x³ = 1), `QMAbSchemeP`.
- `toKer : QMAbSchemeP S → QMAbScheme S` (no hypotheses); `ofKer hT : QMAbScheme S.left → QMAbSchemeP S.left`
  over ℚ-schemes (TorsionStructure; fibre object via a copy of SGRSplit.qmAbFieldFibre_of + Level3.onto).
- `R1fpPropsAbP` (printed level, no ℚ̄-point clause); `np_of_P`/`P_of_np` (TorsionStructure).
- `field_of_printP : TorsionStructure → Y3FineModuliAbP → DeligneCanonicalModelY3EveryP → ShimuraMainThmIDeligneY3AbU`
  (ℚ̄-point from Ψ(i,1)); converses `y3FineModuliAbP_of_field`, `deligneP_of_field` (compare_iso without point).

## 00:20-00:50 Part B and checks (all VERIFIED)
- `IsHodgeH1` (H₁/Hodge form of the moduli clause); `lattice_of_hodge` and `hodge_of_lattice` compiled:
  `hodge_iff_lattice : IsHodgeH1 P τ ↔ (lattice-form clause)`. The converse uses `uniformizationLeafAll_proof`, the
  continuity of φ⁻¹∘Φu (BP open_map), `BPAnalytic.exists_realLinear_lift`, the local-inverse argument of
  `IsUniformization.exists_complexLinear`, injectivity (discreteness of Λ_τ), surjectivity (Λ countable).
- `DeligneCanonicalModelY3EveryH` (H₁ form, over `R1fpPropsAbP`); `deligneH_iff_P`.
- `shimuraMainThmIDeligneY3AbU_of_print : MumfordTorsionAlgClosed → Y3FineModuliAbP → DeligneCanonicalModelY3EveryH → field`;
  `print_iff_field` (both directions). All standard axioms.
- Contributor file `ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean` builds (12982 jobs).
- `lake build +Main +Discharges +ShimuraY3PrintedLeaves`: success, 14229 jobs (build1.txt).
- `#discharges` (discharges.txt): DISCHARGES [OpenResearchLeaves31.shimuraMainThmIDeligneY3AbU] by
  Y3Fix.shimuraMainThmIDeligneY3AbU_of_print, still assumes [AvSplit.MumfordTorsionAlgClosed, Y3Fix.Y3FineModuliAbP,
  Y3Fix.DeligneCanonicalModelY3EveryH]; 35 open, 9889 theorems checked, 36 discharge one.
- autofold --dry-run (autofold-dryrun.txt): strict 11/18 on 29 -> 13/17 on 30; strictest 11/18 -> 13/17.
- FoldCheck.lean (dry-run minus line 1) compiles; sixContactMin_of_open49 standard axioms (foldcheck.txt).

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

# rc-model-target results log

## Setup
- Merge of main 29bfbc3f6 into wip/rc-model-neron 64a338f49: commit 11b3db714.
- Item 6 (rc-model-neron.md same-place row): commit 8dee6dc8f.
- Build seed: copy of a prebuilt tree at a later main (3 added files only) plus the neron worktree build.

## Item 4 (generic): RC/ModelTarget/ComplexReading.lean
- IsComplexLaw g : ∀ p q : complexBase ⟶ ellipticTarget E₀, projectiveValue (p*q).left = pv p.left + pv q.left
- exists_complexLaw := J0Cusps.projectiveGroup_exists; complexLaw (choice), complexLaw_spec
- targetReading g hg : (complexBase ⟶ ellipticTarget E₀) →* Multiplicative (E₀.baseChange ℂ).toAffine.Point
- readComplex E jE g hg (hj : IsMonHom jE.hom) := targetReading ∘ IsMonHom.monoidHom jE.hom
- readComplex_eq : (readComplex .. a).toAdd = projectiveValue (a.left ≫ jE.hom.left) (rfl)
- Build OK (13472 jobs), axioms: propext, Classical.choice, Quot.sound.

# ga-rigidity (fleet summary)

**Result.** Rigidity for 𝔾_a is now proved in Lean over an algebraically closed field: no `sorry`, standard axioms
only. The file is `ZInQKernel/Contrib/OneProof/GaRigidity.lean`.
1. Every homomorphism 𝔾_a → 𝔾_m^r is trivial (`gaHom_torus_trivial`).
2. Every homomorphism 𝔾_a → B is trivial for B a proper group scheme, in particular an abelian variety
   (`gaHom_proper_trivial`, `gaHom_abVar_trivial`). The proof uses the valuative criterion at ∞ of ℙ¹, with the
   translation s ↦ s/(1+cs) on k[s]_(s).
3. If G⁰ is an extension of an abelian variety by a split torus (`HasSemiAbelianIdentityComponent`), then every
   homomorphism 𝔾_a → G is trivial and G contains no 𝔾_a (`noGaSubgroup_of_semiAbelian`). On the way: a homomorphism
   𝔾_a → G factors through every open subgroup.

**Wired into both rows.** This is in `ZInQKernel/Contrib/OneProof/GaRigiditySGA7.lean`.
- New leaves `SGA7_IX_Cor3_3_Def34` and `SGA7_IX_3_5_ForwardGeom_Def34`. Each is the old row word for word, except
  that the hypothesis is SGA 7 IX Déf. 3.4's "no 𝔾_a in the identity component of the geometric special fibre"
  (`NoGaInIdComp`).
- Both fields are proved with their statements unchanged.
- `#discharges` shows both fields discharged, with standard axioms.
- `scratch/ga-rigidity/autofold.json`: the dry run passes and its module compiles. Counts go from strict 12/22 to
  13/21, i.e. −1 GLUE in this base, where ForwardGeom is already LEAF. If queue11 re-rated ForwardGeom GLUE, it is −2.

**Remains.**
- Reading risk, unresolved: SGA 7 was not read and the queue11 file is not available locally.
- If Déf. 3.4 defines semistability as "extension of an abelian variety by a torus", the old rows are already
  literal, and the new leaves would also need Chevalley's theorem (no 𝔾_a ⇒ semi-abelian), which is not proved here.

Report: docs/research/ga-rigidity.md.

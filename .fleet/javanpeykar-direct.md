# javanpeykar-direct: summary

**Result.** The research field `javanpeykarPrintedMapHF` (`JavanpeykarRebase.JavanpeykarPrintedMap`) is proved in
Lean from one new leaf, `JavanpeykarDirect.JavanpeykarThm111`. The new leaf is Javanpeykar, ANT 8 (2014),
Thm 1.1.1, p. 90, stated over its own objects:
* any smooth proper connected integral projective curve `X` over any algebraic closure of `ℚ`;
* `g = dim H¹(X, 𝒪_X) ≥ 1`;
* `W = Pic⁰` with the tensor group law;
* `h_Fal(Jac X)`: `IsStableHeightBar W x`, height-fix's printed stable height of a model of `W` over some number
  field inside `ℚ̄`;
* `deg_B(X) = Nat.find` of the existence of a Belyi map of positive degree.

The only hypothesis added to the print is that some Belyi map exists (Belyi's theorem).

Both theorem steps of the recorded reading gap are now Lean proofs:
* (i) `deg_B ≤` the degree of the given Belyi map, and the bound is increasing (`belyiDegree_le`,
  `javanpeykarBound_mono`);
* (ii) the model `V` over `K` gives the stable height of `W` (`isStableHeightBar_of_model`, ∃-introduction).

No further printed theorem was needed. The remaining readings are definition level only: `IsStableHeightBar` is
Faltings' stable height, plus height-fix's height, `IsBelyiMap`, and "projective".

**What compiles (VERIFIED).**
* `scratch/javanpeykar-direct/JavanpeykarDirect.lean` (the contribution file):
  `javanpeykarPrintedMap_of_thm111` uses only the standard axioms.
* `lake build` of it as `ZInQKernel.Contrib.OneProof.JavanpeykarDirect` succeeds. It was placed there temporarily
  and removed; nothing under `ZInQKernel/` is changed.
* Autofold spec `scratch/javanpeykar-direct/autofold.json`: the field gets proof
  `javanpeykarPrintedMap_of_thm111 {n}.javanpeykarThm111`, and the leaf `javanpeykarThm111` is kind published,
  flag "pending review (Addendum 1 …)".
  * The dry run exits 0. The generated `sixContactMin_of_open58` compiles against a rebuilt TailZ64 with the
    standard axioms.
  * Raw count 16/15 → 17/14 on 31. Under Addendum 1 (the lead sets the new row to GLUE until it is reviewed) it
    is neutral; once a reviewer rates the leaf LEAF it is −1 strict GLUE.
* `WellPosed.lean` (supporting): `IsStableHeightBar` is invariant under isomorphism, and the printed height of a
  fixed model is single-valued given N1 and SS2.

**What remains.** A reviewer must rate `javanpeykarThm111` against the print. Independence of
`IsStableHeightBar` from the choice of model is standard (Faltings 1983) but is not proved in the tree; it is not
needed for the fold. Report: `docs/research/javanpeykar-direct.md`.

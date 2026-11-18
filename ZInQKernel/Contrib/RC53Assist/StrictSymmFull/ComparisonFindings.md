# Retained absolute cochains and the tame comparison

## Result and scope

Route B is assembled for the actual primitive height-one coefficient fibres, conditional on three explicit manuscript-cited Nekovář premises and the remaining nonprimitive local unit tests. The continuous smaller/larger-support coefficient identification is proved, not assumed. The retained absolute-local inflation map is constructed in all degrees, and the homotopy inverse is proved from the cited quasi-isomorphism. At actual primitive old primes the resulting contraction is for the actual full continuous-cochain condition, not just its proposed tame model.

The final theorem actual_reduced_switch_symmetry uses the actual coefficient character, actual localization maps, the chosen old conditions, and the original genuine isotropy datum. It constructs a contraction license from primitive-prime hypotheses and OtherPlaceInputs, then proves Hsw StrictSymmTrunc and StrictSymm for the reduced switch. actual_reduced_switch_rc26 proves the exact RC26 place-wise formula for the same continuous data. No StrictSymm input is used.

These statements are conditional results. None of the three cited premise values is constructed by this contribution. They are ordinary proposition arguments, not new Lean axioms. The precise remaining arithmetic input is stated below; it has not been silently converted into a theorem.

## Continuous coefficient identification

CoefficientComparison.levelEquiv identifies E(K_S)[2^n] and E(K_S0)[2^n] through their common actual geometric torsion. HasFullTwoTorsion is retained for both supports. The identification commutes with halving and with the actual absolute Galois action. Passing to the inverse limit gives tateContinuousEquiv, a continuous integral linear equivalence of the actual Tate modules.

The base-changed fibreContinuousEquiv is linear over k(P). It preserves the actual integral lattices in both directions and maps every basic neighbourhood 2^n latt into the same basic neighbourhood. Both directions are proved continuous for the supplied lattice topologies. No discrete topology is imposed on either fibre.

For actual inflated characters, inflated_fibreEquiv_Galois and inflated_fibreEquiv_local retain the global inflation and local restriction actions without an additional character-compatibility premise. For a primitive quadratic twist, primitive_fibreEquiv_local_action retains the quadratic sign times the smaller-support action; it does not replace that action by an unramified one. Compatible continuous coefficient maps induce actual all-degree full local cochain isomorphisms in actualLocalCoefficientCochains.

## Exact cited premises

Only one manuscript-cited source is used: J. Nekovář, Selmer complexes, Astérisque 310 (2006), https://www.numdam.org/item/AST_2006__310__R1_0.pdf. The supplied manuscript cites this book. Milne ADT is also cited, but NSW is not a bibliography entry in the supplied manuscript, so no NSW premise is introduced.

### Nekovar414Fibre

Source: Lemma 4.1.4, printed p. 96. For a profinite G, closed normal H with pro-finite order prime to the residual characteristic p, and an ind-admissible coefficient module M, the actual inflation

    C_cont(G/H, M^H) -> C_cont(G, M)

is a quasi-isomorphism. The proof reduces through Corollary 4.1.3 to discrete p-primary torsion coefficients and degenerates the Hochschild–Serre spectral sequence. Proposition 3.7.4(ii), printed p. 94, identifies the localized-coefficient derived continuous cohomology with the underlying continuous cohomology used here.

The Lean packet is the specialization p=2 to actual VP K S W P alpha, with its supplied lattice topology, actual local group Gloc K v, and actual quotient map by N. The kernel is required to be closed with every finite open-normal quotient of odd cardinality and to act trivially on that actual fibre. The conclusion is only QuasiIso of the constructed inflation morphism.

Wild inertia at residue characteristic ell is pro-ell. At an odd place this means pro-order prime to 2, not prime to ell. PrimeToTwoKernel and primeToTwoKernel_of_proOdd state that condition exactly.

### Nekovar721Structure

Source: the wild/tame notation of 7.1.1, printed p. 155, and the local quotient/generator description of 7.2.1, printed p. 156. The maximal tame quotient has procyclic tame inertia and a geometric Frobenius lift f satisfying

    t f = f t^L,    L = cardinality of the residue field.

The packet specializes this local structure to the concrete normal fixing kernel of the unramified extension together with all prime-to-residue-characteristic roots of uniformizers. It asserts that the kernel is pro-residue-characteristic and that a TameFrame exists. Closedness, inertia containment and fixation of the defining radicals are proved separately. The packet does not contain an operator-unit, contraction, cohomological comparison or symmetry conclusion.

### Nekovar723Fibre

Source: Proposition 7.2.3, printed pp. 158–160, following the small complex of 7.2.1. The full geometric norm is

    N_L(t) = sum_{i=0}^{L-1} t^i,    theta = f N_L(t).

The actual small complex is

    M --(f-1, t-1)--> M x M --(-(t-1), theta-1)--> M.

The compatible formulas for its comparison from full tame cochains are fixed, not merely existential:

    lambda_0 = identity,
    lambda_1(c) = (c(f), c(t)),
    lambda_2(z) = -z(t,f) + z(f,t^L)
      + f sum_{i=0}^{L-2} t^i z(t,t^{L-1-i}),
    lambda_i = 0 for i > 2.

The packet asserts the formula-preserving quasi-isomorphism for the actual tame quotient, actual VP lattice coefficients and an actual TameFrame at an odd place. FrameComparison records the degree-zero, degree-one and full degree-two formulas and the quasi-isomorphism. Higher target terms are zero by the defined three-term complex. The homotopy inverse is not included in this printed premise.

The literal Lean bodies of all three packets, their exact binder lists, and their axiom reports are included in ComparisonAudit.txt.

### Specialization boundary

The source statements are for ind-admissible modules and the maximal tame extension. The three specialized packets include the identification of the actual finite-type coefficient lattice and its localization with that source setting and the identification of the concrete tame-radical field with the cited maximal tame extension. Those source-to-object identifications are not independently proved in this contribution. Accepting the packets is therefore a real premise, not a claim that an arbitrary topological module is covered. They are quantified over actual coefficient fibres and actual kernels, not freely chosen complexes.

No claim is made that a general Hochschild–Serre formalism for non-discrete continuous coefficients is available: Nekovář 7.1.2 explicitly warns against that shortcut. The contribution uses the exact quasi-isomorphism of 4.1.4 and the explicit small complex of 7.2.3 instead.

## Proved all-degree retained comparison

The original local representation is descended through the actual kernel-triviality condition without changing the coefficient carrier or lattice topology. quotientCoefficient_pullback proves that pulling the descended action back gives the original actual local action. Quotient continuity is proved through the open quotient map, not assumed.

The inflation morphism is the compatible pair consisting of the actual local quotient map and the literal coefficient identity. It is defined in all nonnegative cochain degrees and extended by zero to negative integer degrees. absolute_inflation_homotopy constructs a homotopy equivalence whose forward morphism is exactly that inflation.

A quasi-isomorphism is not generally a homotopy equivalence over an arbitrary ring. The conversion here is proved over the actual coefficient field: all cochain vector spaces are injective, the complexes are bounded below, and the bounded-below injective-complex theorem gives the homotopy inverse. These homotopies are linear maps of the actual continuous-cochain modules; no finite-degree truncation is substituted for the full cochains.

geometricNorm_identity and geometric_tame_relation prove the exact full-norm small-complex relation. frame_comparison_homotopy converts the specified small-complex quasi-isomorphism to a homotopy equivalence. retained_absolute_tame_homotopy composes the two comparisons while retaining the inflation leg and the explicit small-complex formulas.

The older normQ model and its frozen source are not modified. That quadratic-reduced, arithmetic-Frobenius presentation must not be substituted for the full geometric-norm presentation at a general moving fibre without checking its actual norm and Frobenius conversion. The new contraction theorem uses the full norm directly.

## Actual primitive old-place contractions

The actual tame fixing kernel lies in inertia and fixes the retained primitive square root. Full two-power torsion over the smaller coefficient support fixes the actual Tate module there; the inflated moving character is trivial on that kernel. actual_old_primitive_kernel_trivial proves kernel triviality for the actual primitive coefficient character.

At an actual odd old prime where the radicand is a uniformizer, every topological tame inertia generator has primitive quadratic sign -1. frame_primitive_sign proves this from the dense inertia image and the genuine ramified root, not from a freely chosen operator hypothesis. frame_primitive_fibre_scalar discharges the remaining Tate and moving actions, so the specified tame-frame inertia operator on the actual fibre is -1. Its difference from one is -2, a unit at every permitted odd height-one test prime P.

actual_old_primitive_absolute_contraction and actual_old_primitive_full_condition_contraction combine the three cited packets, the proved genuine scalar identity and the displayed tame contraction to produce an all-degree contraction of the actual full absolute-local condition. There is no assumed homotopy equivalence, unit operator or strict symmetry in those theorem inputs.

## Reduction and genuine switch assembly

The existing FullReduction.reduced_strictSymmetry wrapper requires discrete coefficients. It cannot be applied unchanged to the actual VP lattice coefficients. The new ContinuousReduction namespace proves its continuous analogue in a new file only, using the same actual continuousSwitch and genuine truncated isotropy interfaces.

The licensed erasure preserves every nonremoved old condition and leaves the derivative switch place retained. The original isotropy homotopy is pulled back through the actual subtype inclusions in every bidegree. retained_condition_maps proves the actual local maps agree; retained_traced_pairing proves exact preservation of every trace of the original cup formula. condition_retractions and selmer_retractions use the specified full-cochain contractions, including the local correction in the inverse projection. reduced_data_eq identifies the reduced actual Selmer data with those restrictions, and actual_selmer_equivalences gives equivalences of the actual reduced and original Selmer complexes.

The reduced strict condition has a literally zero degree-two term. ContinuousReduction.reduced_strictSymmetry proves Hsw StrictSymmTrunc and StrictSymm for the actual reduced continuous switch. reduced_rc26_strictSymm proves the exact original RC26 place-wise formula on those same data. No DiscreteTopology hypothesis is imposed on the coefficients.

ActualSwitchAssembly.actualRetainedReduction selects the actual primitive contractions and, at every remaining removed full place, the contraction arising from OtherPlaceInputs. actual_reduced_switch_symmetry and actual_reduced_switch_rc26 are the final actual height-one switch theorems, retaining the original genuine isotropy datum. The RC26 formula is stated directly rather than claiming to inhabit the older discrete-only GenuineSwitch wrapper.

## Precisely remaining

1. Supply or approve the three specialized cited premise values. They are explicit assumptions in the final theorems; their source-to-object boundary is stated above.
2. For every nonprimitive full place to be erased, OtherPlaceInputs still requires actual wild-kernel triviality and the actual tame-frame unit tests. The unit tests are either inertia-minus-one invertible or both f-1 and f N_L(t)-1 invertible. The moving-place witnesses and their finite-stage character bindings are not constructed here.
3. At the central moving test P=(X), bind the actual central Frobenius determinants and their nonzero/unit hypotheses to the correct retained operators. These are not produced by the primitive sign theorem. No generic full local Frobenius complex at unused good primes is inverted.
4. The actual erasure set must exclude the new switch place and contain only old conditions known to be full and licensed to contract. The nonremoved old strict conditions still need the supplied literal degree-two bound. Neither acyclicity alone nor a primitive contraction at a different prime licenses their erasure.
5. If a consumer needs the previous arithmetic/quadratic normQ comparison literally, prove its operator/Frobenius identification with the full geometric-norm presentation. The new route B assembly does not require that substitution.

Route A, literal strict symmetry of the original chosen forward homotopy on unerased full absolute cochains, remains unproved. The result is route B and uses the retained reduced datum.

## Verification

CoefficientComparison.lean compiles cleanly with the supplied single-file invocation, six threads and the supplied CPU affinity. Its maxHeartbeats is 600000. It contains 76 theorems and 137 named declarations, including definitions, instances and records. ComparisonAudit.txt contains 137 complete type/axiom report pairs, covering every theorem, plus the full proposition bodies of the three cited premises. The only reported axioms are propext, Classical.choice and Quot.sound. There are zero errors, zero warnings and no elisions in the audit. The temporary audit source and reference images were removed after verification.

All previously committed StrictSymmFull files remain byte-for-byte unchanged. No commit, checkout, project build, generated import, subagent or human outreach was used. No memory write was made in this continuation.

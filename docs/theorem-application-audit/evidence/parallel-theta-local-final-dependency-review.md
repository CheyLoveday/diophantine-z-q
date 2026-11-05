# Final dependency-consistency review

Reviewed 2026-11-05. The input inventory has 82 distinct application records, A001 through A082, attached to baseline SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. I read every record's hypothesis and translation fields, the relevant closure reports, the latest parallel acceptance/repair reports, and the critical baseline consumers. No shared file was edited.

## Finding

I found no unavoidable circular argument in the reviewed source-application dependencies. I did find several coarse application-ID cycles that must not be presented as mutual discharge. The most important are A037/A075 and A045/A075. A075 contains both a general finite-model construction and later deductions using arithmetic duality. Those are different statements with different prerequisites. Calling the entire record simply a prerequisite of A037 or A045 obscures the valid order and can falsely suggest that duality proves its own perfectness hypothesis.

A complete honest inventory can record all 82 external application families without claiming that every internal lemma, every arithmetic construction, or the final theorem has an independent proof certificate. Its statuses should say which source statements and substitutions have been checked, name the internal premises consumed, and distinguish pending repair integration from the unchanged baseline. Empty `open_items` means no remaining item within the recorded scope; it must not erase these prerequisites.

## Required refinement of A075

Use named subclaims within A075. No new top-level application number is necessary.

1. **A075-F, existence of finite models.** Finite-coefficient continuous cochains are filtered colimits of free function modules and are flat; over the Artin local coefficient rings they are free. Once residual cohomology is bounded and finite, residual splitting and the explicit nilpotent perturbation formulas give a bounded finite free model and a contraction. BATCH-006 sections 1–3 check these formulas and the tensor/composition corrections. Residual boundedness for global cochains over imaginary K comes from the finite global Galois-cohomology statements in Milne/Nekovar, not from Selmer self-duality. Local Galois cohomology is bounded and finite. For a Kummer source, local point-group finite generation gives its two-term free resolution, including torsion. Cones of these finite models are perfect before applying a duality theorem. Over Q at two, the positive fiber cancels high-degree real cohomology; ordinary global cochains are not silently declared bounded.
2. **A075-T, transport and limits.** Given actual maps, products and homotopies, the pfi, pghfi and higher correction formulas transport them. Given the stated termwise-surjective compatible tower, the inverse-limit cone argument applies. The different moving-prime inner limit uses finite matrix tuples and retained finite detecting lists, not a nonexistent compatible tower of all moving representations. These algebraic operations do not create arithmetic maps, isotropy, valid stages or nonempty Frobenius classes.
3. **A075-B, arithmetic budgets.** The special formula (2,d_K,d_K,2), rank 2d_K+4, torsion length h_K+2t_K, and subsequent determinant bounds consume A037/A038/A045 and their corank inputs. They cannot be used as the original proof of A075-F's boundedness in those same applications. BATCH-006 itself keeps these scopes separate.

The valid order is A075-F, then the arithmetic duality applications, then A075-B. A075-T is a general operation on already supplied data. The broad A075 dependencies in my earlier ACCEPTANCE-UPDATES.json should be interpreted and preferably rewritten this way.

## Critical application map

| Application | Inputs actually consumed | Dependency boundary |
|---|---|---|
| A037, Kummer exact annihilator | Milne finite local duality; actual elliptic principal polarization; local point-group completion with torsion; A075-F local models | It uses no global Selmer duality and no rank budget. The integral isotropy proof and derived Nakayama precede A038. |
| A038, global Selmer duality | Perfect coefficient pairing; A037 at Kummer places; elementary zero/full and unramified diagrams; checked derivative local diagrams from A080; A075-F/T | Nekovar 6.3.4 concludes duality only after these diagrams and orthogonality are supplied. It cannot manufacture A080's custom local maps. |
| A040, isogeny ratio | Milne I.7.3 proof; dual isogenies and polarizations; rank-one and finite-Sha inputs from forward A020/A082; A069 local component calculation | It applies at already known simple zeros and known nonzero companions. It is not used to deduce their analytic nonvanishing, nor does full Selmer corank alone imply finite Sha. |
| A041, primitive/relaxed naturality | Actual maps i and j, old isotropy data, norm boundary and generic paired lift; A038 pairing; A075-T comparisons | Nekovar 6.4.1–3 supplies compatibility once the full map/homotopy data are present. It does not prove the arithmetic norm relation, existence of the chosen paired lift, or the Lambda-unit claim. The latter has its separate finite cone-basis argument. |
| A044, derivative switch | A038 and the A080 local model; old generic H1 rank one with nonzero localization; actual derivative identity; A075-T | Exact annihilator is a duality consequence. Existence/detection of the two vectors is an arithmetic input. The switch cannot serve as its own proof of that input. |
| A045, finite self-duality budget | A037/A038, A075-F; rational torsion finiteness; full Selmer corank one with the independently nonzero companion A082 | Finite duality gives the dimensions; universal coefficients give torsion and free ranks. These conclusions feed A075-B, not A075-F. The real appendix separately uses Nekovar 5.7. |
| A080, cochain functoriality/local compatibility | Standard Kummer/transfer/Shapiro/Mackey constructions; actual tower arithmetic and congruences; direct tame resolution and bar comparison | The added local proof is independent of global exact annihilators and global rank bounds. It supplies data to A038/A044. A075-T may transport those data afterward. |
| A081, fixed clearing factor | Local Iwasawa control and degree range; ordinary local duality; finite local elliptic torsion; finitely many local quadratic types | This is independent of global Selmer duality, the restricted converse and the global determinant bounds. |

### A037 and A038 in detail

The Kummer complex M[-1] has M finite over Z_2, including finite torsion; its perfect local model needs no Selmer duality. The finite Kummer exact sequence and local duality identify its annihilator. The restricted integral cup class lies in Hom(M tensor M,Z_2); vanishing at every finite precision gives integral vanishing. This proves the local input before Nekovar is applied globally. Exactness and boundedness of the local finite models precede derived Nakayama; Nakayama is not being used to conjure perfectness.

The coefficient pairing for A038 is also independent. A_i is a finite complete-intersection ring and A_i[G] is its symmetric group-ring extension. Coefficient-of-1(ab) is a permutation pairing, without 1/|G|. The actual conjugation pullback inverts the anticyclotomic character and supplies the correct dual twist. Neither statement relies on the desired global duality.

A038's active/moving contractions after the specified localization are additional local matrix facts. A075-T preserves them once supplied; it does not prove their determinants are units. The final inventory should link those local calculations explicitly rather than replace them by the phrase "A075 verified."

### A080 and A044

The derivative local repair is restricted to the actual split or new totally ramified extensions. Its arithmetic inputs include the H12 Frobenius congruence, local triviality of the moving/old ring-class data, and the specified derivative inertia index. Their construction is tracked by A033/A067/A068 and the manuscript's finite-stage arithmetic, not by global duality. The repair proves the finite/singular model, the square-zero assertion after the adapted uniformizer choice, all-degree restriction/corestriction, the shear divisibility, and compatibility homotopies. The direct small-resolution/bar comparison is local; no global contraction is assumed in order to establish it.

The transported pairing includes J. Checking its local isotropy is not an invocation of the global exact-annihilator conclusion. The latter comes only after A038. Similarly, A044 assumes the old class spans generic H1 and that v is nonzero; it uses the independently established finite/singular derivative formula (H19). Those assumptions belong to the actual Heegner class and detection arguments, with A034/A035/A067/A068/A080 interfaces. The source theorem does not prove them. Listing these internal premises is sufficient for an external-application inventory, but calling them all "discharged by Nekovar" would be false.

### A040, A045 and A081

The finite-Sha requirement in A040 is met only in its known analytic-rank-zero/one applications. A020/A082 are forward theorems, and the cited nonvanishing constructions precede them. The A045 full-corank calculation expressly allows a divisible Sha part and must remain distinct. A040 cannot be transferred to the latter setting by citation alone.

In my earlier A045 acceptance wording, A082 should be read only as the forward analytic-rank-zero input. The rational-field real-place exact-sequence construction is a separate application of Nekovar 5.7 and the displayed compact/discrete limit argument; it is not a conclusion of A082. The inventory already has the real-place anchors within A045, so this calls for a clearer dependency label, not an additional theorem family.

A081 uses local Iwasawa H2, its derived augmentation and the vanishing of local rational H2. Its Kato citation is the local finite-generation/degree-range statement (12.2.3), not global Euler-system divisibility 13.4(2). Consequently A023 may consume A081 without a cycle: A081 does not consume A023. The local torsion argument uses a sufficiently deep formal neighborhood, whose convergence inequality is checked in A071. It does not use the global nonzero clearing factor that it is proving.

## Other coarse cycles and scope traps across the 82 records

- A011 uses the elementary semisimple character/density argument recorded in A064 to identify a constituent of the modular Jacobian. A064's eventual comparison of the constructed r_3 with that modular constituent uses A011. Separate the reusable Brauer–Nesbitt/continuity lemma from the final r_3 application. The former has its own primary source and proof and does not assume the latter. Likewise, the Fricke argument uses Shimura's unconditional coefficient-conjugate existence before its conditional zeta conclusion. The geometry/A011-FRICKE-REVIEW.md checks that order.
- A013 supplies semistability after adjoining prime-to-residue-characteristic torsion. A012 consumes it to bound ramification/conductor. The local A013 theorem does not need the final A012 bound; its acceptance report explicitly says so. Do not treat A013's mention of subsequent A012 transport as a reverse prerequisite.
- A014/A015/A016 depend on the factor construction A063. A063 depends on modularity and Faltings, not on the height bound it later enables. The source height used in the bounded-isogeny application is J's height, and the initial unbounded isogeny is already constructed. There is no height-bound bootstrap.
- A027's explicit Gross–Zagier identity and A020's forward rank-one conclusion are separate uses. A027's later native free-line comparison can consume A020; the earlier nonzero height identity supplying the forward theorem's point does not assume that line comparison. The analytic derivative/nonvanishing hypotheses must remain explicit.
- A067/A068/A076 should distinguish arithmetic construction of actual finite extensions/elements from Chebotarev realization, and both from compactness. A076 cannot produce a nonempty arithmetic stage from the compactness theorem. The later finite-realization closures are the evidence; BATCH-006's earlier A076-open paragraph is historical.
- A028/A029/A030/A031/A052–A054 separate construction/modularity, nonzero lift and packet admissibility, and full-space proportionality. The inventory correctly lists a nonzero vector or packet as an input where needed; proportionality cannot prove that its own ambient space is nonzero. Characteristic-zero proportionality is not an integral lattice comparison.
- A047 and A048 are downstream conditional consequences of the claimed integer definition. Their application checks cannot count as evidence for that definition or the main theorem.

## Accounting additions and publication wording

The semantic coverage pass identified two genuine missing source subobligations. They must be carried into the final inventory: A021's Mertens product/harmonic-sum inputs, and A052's quaternion classification and rational embedding input, cross-referenced by A028. See sieve-bounds/COVERAGE-REVIEW.md and its exact replacements. These fit existing application families; there is no reason to invent A083 merely to preserve an earlier incomplete description. Include the repeated A057 and A065 consumers and the A018 source-version correction from that agent's acceptance report as well.

Record the sequence of A080 evidence honestly. forward-modularity/A080-REPORT.md identifies a genuine local-data gap in the unchanged baseline. theta-local/A080-LOCAL-REVIEW.md and the final forward-modularity/A080-LOCAL-SECOND-REVIEW.md supply and review the repair. A final acceptance refers to the integrated repair and its new anchors. It must not retroactively say that the original H19/H22 statements alone supplied all chain-level hypotheses. Similar repair dependencies apply to A032's h_p convention and A069's component-factor source.

Recommended common status text is:

> The cited source statement, hypotheses, conventions and recorded translation have been checked for this application, with the named internal premises and integrated repairs. This is not an independent verification of every upstream lemma or of the manuscript's final theorem.

Use a separate field for unresolved in-scope obligations and another for consumed internal premises. A record with no in-scope source obligation can still have nonempty premises. Preserve historical reports as historical; avoid treating superseded open-item prose as a current contradiction, and avoid deleting it in a way that conceals the repair.

## Disposition

No new mathematical assumption or additional top-level external theorem family was forced by this dependency pass. The required changes are finer dependency labels, explicit integration references, and the already identified coverage additions. The existing acceptance claims are defensible only with those limits. In particular, an undifferentiated statement that A075 proves A037/A038/A045 while simultaneously relying on all of them should not appear in the published inventory.

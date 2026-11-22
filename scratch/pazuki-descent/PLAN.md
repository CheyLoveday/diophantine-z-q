# Pazuki descent on the fork

22 November 2026 · Research plan for the arithmetic part of the theta-height comparison

**The first theorem to attempt recovers the given symmetric line-bundle class.** Fix a number field $K$, an abelian variety $A/K$, an embedding $\sigma:K\hookrightarrow\mathbb C$, and a symmetric class $L$ on $A_\sigma$. Under the two Picard hypotheses used by the fork, construct one finite extension $E/K$, an embedding $e:E\hookrightarrow\mathbb C$ extending $\sigma$, and a symmetric class $M$ on $A_E$ such that $\pi_e^*M=L$. Here $\pi_e$ is the projection in the archived consumer. The eventual arithmetic theorem also asks for ampleness and one-dimensional global sections when $L$ has those properties. It ranges over abelian varieties of every dimension. The height application uses dimension two. [Arithmetic consumer][consumer] · [Definition of symmetric principal][principal]

## What the existing proof supplies

| Source | What this attempt can use |
| --- | --- |
| Fork proof at `38dc3563f` | Eight Lean files. `fixedPicard_point_definedOver` gives $E,e,t$ for a fixed field-valued point $s$ of the represented relative Picard scheme. Its conclusion includes the original embedding, fixedness of $t$, and the equality factoring $s$ itself through $t$. [Declaration][fixed] |
| Hosted evidence at `fa21b107` | The eight files match their named input hashes in the retained receipt. The supplement records three typed examples and standard axioms for 15 declarations. Its linter warnings are recorded. The earlier project reporter covered a smaller overlay and reported a conditional CM match. [Receipt][receipt] |
| Formal project at `f0334871b` | The open field is `HDec.HSyn.OpenResearchLeaves75.pazukiCor13Upper`. A temporary Git index accepted the eight fork files and all three archived consumer files at this revision. All 11 resulting blobs matched their sources. All 26 direct project imports supplied by main, the Lean 4.35.0 pin, the Mathlib pin and the Lake configuration matched the hosted base. Git reported a trailing blank line in the archived patch. Elaboration at this revision is pending. [Board][board] · [Archive][archive] |

## 1. Compare field-valued classes and points

Start in one additive module, provisionally `ZInQKernel/Contrib/OneProof/PazukiLineBundleDescent.lean`. For a field $F$ equipped with an actual map $K\to F$, take $T=\operatorname{Spec} F$ over $K$. The natural map from $\operatorname{Pic}(A_T)$ to the relative Picard sheaf at $T$ is a bijection. The zero section and `PicDict.Θ A PicDict.pushforwardUnitUniversal` identify the sheaf with classes normalized at zero. Every class is normalized because $\operatorname{Pic}(T)$ is trivial. The fork already uses the inverse of this normalization isomorphism. This part needs neither of the two global Picard hypotheses. [Normalization in use][used-normalization] · [Field Picard group][field] · [Existing injectivity proof][injectivity]

Given a representation `rep` for **this** $A$, compose the sheaf map with `rep.homEquiv.symm` to get a classifying map $\lambda_T$. Prove two identities. For $v:T'\to T$ over $K$, write $A_v:A_{T'}\to A_T$ for `JacobianChallenge.baseChangeMap`. For inversion write $D$ for `T09Pic.dualP rep` applied to inversion on $A$.

$$
\lambda_{T'}(A_v^*L)=\lambda_T(L)\circ v,\qquad
\lambda_T(([-1]\times 1_T)^*L)=D\circ\lambda_T(L).
$$

Use naturality of the sheafification unit and `rep.homEquiv_comp` for the first identity. Use `toPicardFunctor_comp_dualSheafMap` and `comp_dualP` for the second. Identify the family map with inversion on $A_T$ by its two pullback projections. The fork has the corresponding calculation at the algebraic closure. Check both equations with an explicitly supplied base map, including the tower $\operatorname{Spec}\mathbb C\to\operatorname{Spec} E\to\operatorname{Spec} K$. [Definitions and identities][dual] · [Inversion calculation][involution]

Take $T=\mathbf P^1_K$ and $p:A_T\to T$ to test the field restriction. The class $p^*\mathcal O_T(1)$ is nontrivial because pulling it back along the zero section gives $\mathcal O_T(1)$. It becomes trivial over the two standard opens of $T$, so it has the same image as the trivial class in the relative Picard sheaf at $T$. This rules out extending the unnormalized bijection to arbitrary test schemes. [Stacks 0BXJ, AI-READ][projective-line]

## 2. Recover the same symmetric class

Apply step 1 to $L$ to obtain a fixed point $s$. Apply the fork theorem to $s$, choose $M$ from the descended $t$ by the field comparison at $E$, and use the two identities. The factorization gives $\pi_e^*M=L$. Fixedness of $t$ gives symmetry on $A_E$. Use the returned equality `hσ : e.comp (algebraMap K E) = σ` to identify the comparison map with `PazukiInputs.bcMap A σ e hσ` by its two projections. This works even when $\mathbb C/E$ has positive transcendence degree. [Exact projection][projection] · [Complex base change at the chosen embedding][bcc]

The field-class comparison uses the supplied `rep`. The fork theorem also takes `T09Pic.PicRepresentableAbVar` and `PicZeroChar0.PicZeroAbVar0`. Once $s$ is fixed, its factorization lemma needs quasi-finiteness only at the image of this $s$ in the equalizer. A proof of that pointwise assertion for the chosen representative would suffice for this step. [Pointwise factorization][pointwise] · [Fixed-locus proof][fixed]

**First milestone.** A typed scratch example must return the same $E,e,M$ with `FiniteDimensional K E`, the embedding equation, equality under the archived `bcMap`, and invariance under the actual inversion on $A_E$. Load the three archived files in the scratch overlay when first testing `bcMap`. The contribution module can state its theorem using the live project's base-change map.

Take $B/\mathbb Q$ given by $y^2=x^3-2x$ and $P_\pm=(\pm\sqrt2,0)$. The two classes $\mathcal O(P_\pm)$ in $\operatorname{Pic}^1(B_{\mathbb Q(\sqrt2)})$ have equal degree, are symmetric, and are exchanged by conjugation. A theorem returning only the degree or the polarization morphism would allow the wrong conjugate.

## 3. Transfer section dimension and ampleness

These lemmas can be worked on separately once the projection is fixed. Apply both to the $M$ returned in step 2.

| Obligation | First proof to try | Acceptance |
| --- | --- | --- |
| Section dimension | Use `finrankH_pullback` at degree zero on the cartesian square `bcMap_isPullback`. Pass through `H.zeroLinearEquiv`, the pullback isomorphism of the chosen invertible-module representatives, and the constants isomorphism for each proper geometrically integral abelian variety. | An equality of section ranks over the respective rings of global functions, as written in `PazukiDict.IsSymmPrincipal`. [Field-extension ranks][rank] · [Constants map][constants] · [Consumer][principal] |
| Ampleness | Start with global sections of the ideal of a closed complement, tensored with a power of $M$. Use the canonical section map described below to descend a section nonzero at the selected point. | For every $x\in A_E$, exhibit a positive power of $M$ and a section whose nonvanishing open is affine and contains $x$. On $B\times B$, the first projection pullback of $\mathcal O_B([O])$ is symmetric with section dimension one and restricts trivially to the second factor. This checks why rank alone cannot supply ampleness. [Exact Lean definition][ample] · [Stacks 0D2P, AI-READ][ample-stacks] |

The proof of the private `sectionsBaseChange_injective` already writes down the commutative square at the top open for a quasi-coherent module, a flat map between affine bases, and a quasi-compact, quasi-separated structure map. Two sides are equivalences. The cohomological side is bijective by `bijective_cohomologyBaseChange_of_isCompact` at degree zero. The square therefore gives **surjectivity** of the concrete `sectionsModuleBaseChange … ⊤` as well. Reuse the displayed square in a new lemma with source credit. Check its value on pure tensors and its compatibility with the coefficient map $I\otimes M^n\to M^n$. Try this before building an affine-cover argument. [Existing square and its hypotheses][square] · [Bijectivity on compact opens][compact] · [Pure-tensor formula][tensor] · [Stacks 02KH, AI-READ][flat-stacks]

For the geometric step choose an affine $U$ around $x$ trivializing $M$, its closed-complement ideal $I$, and a point above $x$. Upstairs ampleness gives an affine nonvanishing open $D(s)$ through that point. On $D(s)$ choose a section of the pulled-back ideal nonzero in the residue field there. Clear denominators and multiply once more by $s$ to obtain a positive power. Global section surjectivity expresses that section as a sum of scalar multiples of pulled-back sections of $I\otimes M^n$. Some ground section has image $b$ nonzero at $x$. Because $b$ comes from $I$, its nonvanishing open lies in $U$ and is principal there. The remaining Lean work includes the ideal map, tensor powers and comparison with the defining zero locus. [Clearing denominators][clear]

## 4. Check the arithmetic endpoint and the live premises

After steps 2 and 3, assemble `PazukiInputs.SymmPrincipalDefinedOver` under the two explicit Picard hypotheses and apply the archived `symmPrincipalDescends_of_definedOver`. Its proof handles a zero section and a nonzero section of the bundle on the same descended model. Check both named types on the archived overlay. [Assembly][assembly]

The live-premise review can start now. The C8 fold retired the old Picard rows. There is a concrete first test. In the proof behind `mu_pic_of_isTI0`, the first two lines choose a representative and its identity component from the global hypotheses. The rest of that proof uses the chosen `P, rep, B, j, hj` directly. Try stating that calculation for those witnesses in an additive module. The fixed-locus proof first passes from $K$ to its algebraic closure $k$. Its inversion calculation then uses `AKbar` over an algebraic closure of $k$. Check `fullPicardRepresentation` on those actual base changes, and identify which identity-component witnesses are still needed. [C8 decision][c8] · [Use of the two hypotheses][mumford] · [First base change][first-closure] · [Inversion calculation][involution]

For this argument to reach the board field, it needs a representative for the original $A/K$. Test each use against the locally Noetherian site. The existing comparison identifies restricted sheaves. Constructing the appropriate representative and its morphisms, or adapting the argument to that site, remains open. If that is the obstruction, the archive proposes lifting the Néron–Severi class, symmetrizing the lift and recovering the actual two-torsion difference in $\operatorname{Pic}^0$. Compare the cost of that alternative at the same line-bundle endpoint. [Restricted site][site] · [Archived alternative][consumer]

An eventual proof of the board field also needs the analytic polarization on the given complex surface and the printed height inequality in the project's coordinates and normalization. The archived assembly exposes `GAGAMorphism`, `RiemannPPAV`, `PazukiCor13UpperPP` and arithmetic descent as separate inputs. A live proof of `GAGAMorphism` is available. [Archived board theorem][height] · [GAGA theorem][gaga] · [Live target][board]

## Branch and verification

Use `research/pazuki-line-bundle-descent` on `CheyLoveday/diophantine-z-q` for this attempt. It starts at the eight-file Pazuki cut. All new commits and pushes go to Chey's fork. Jack's main, claims thread and contribution rules supply read-only coordination references. Issue #14 contained Chey's scope question and follow-up at this review, with the maintainer's choice of endpoint still pending. Fork draft #6 retains the earlier hosted evidence. Apply the fork's research rules and the DZQ working guide on fork draft #7. [Scope thread][scope] · [Fork draft #6][draft] · [Fork research rules][fork-rules] · [DZQ working guide][guide]

Use the existing odProof Modal runner for Lean. Pin the base and file digests, include the scratch overlay needed for the endpoint, and check the cache and resource bounds before dispatch. The following worker commands are planned for the first milestone, using the proposed module and scratch names. Build the archived consumer explicitly before importing it in the scratch example.

```sh
lake --offline --no-cache --fail-fast build +ZInQKernel.Contrib.OneProof.PazukiLineBundleDescent +ZInQKernel.Contrib.OneProof.PazukiInputs
lake --offline --no-cache env lean CheckPazukiBundle.lean
```

Capture the actual commands, stage results and `#print axioms` for the new declarations. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. For a board candidate, run the separate scratch `#discharges` reporter and read every remaining premise. Keep proof files additive and put `OneProof.Main` imports in scratch. [Fork runner rules][guide] · [OneProof contribution checks][checks]

Chey Loveday is the operator. OpenAI Codex used odskills for this source review and plan. The checks recorded here cover source identities, the temporary overlay and the cited arguments. The proposed Lean lemmas await a hosted build and independent review.

[consumer]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/ZInQKernel/Contrib/OneProof/PazukiInputs.lean#L105-L121
[principal]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean#L87-L94
[fixed]: https://github.com/CheyLoveday/diophantine-z-q/blob/38dc3563f70a0e286728e752f56733252464cd5e/ZInQKernel/Contrib/OneProof/PazukiPicardFixedLocus.lean#L48-L70
[receipt]: https://github.com/CheyLoveday/diophantine-z-q/blob/797f556df014b70d0748785ddb25466969a01124/scratch/height-cm-review/modal-results.json
[board]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/docs/one-proof/OPEN.md#pazukicor13upper
[archive]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/docs/research/pazuki-inputs.md
[used-normalization]: https://github.com/CheyLoveday/diophantine-z-q/blob/38dc3563f70a0e286728e752f56733252464cd5e/ZInQKernel/Contrib/OneProof/PazukiPicardBaseChange.lean#L64-L80
[field]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Picard/Field.lean#L40-L50
[injectivity]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudR2Poincare/L1/PicardKernel.lean#L43-L85
[dual]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/OneProof/H/TailZ24.lean#L169-L214
[involution]: https://github.com/CheyLoveday/diophantine-z-q/blob/38dc3563f70a0e286728e752f56733252464cd5e/ZInQKernel/Contrib/OneProof/PazukiPicardInvolution.lean#L47-L89
[projective-line]: https://stacks.math.columbia.edu/tag/0BXJ
[projection]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/ZInQKernel/Contrib/OneProof/PazukiInputs.lean#L42-L83
[bcc]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/OneProof/H/TailQ.lean#L1004-L1013
[pointwise]: https://github.com/CheyLoveday/diophantine-z-q/blob/38dc3563f70a0e286728e752f56733252464cd5e/ZInQKernel/Contrib/OneProof/PazukiSymmetricDescent.lean#L96-L108
[rank]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Cohomology/FieldExtension.lean#L30-L70
[constants]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Cohomology/GlobalFunctions.lean#L26-L37
[ample]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/OneProof/H/TailZ24.lean#L347-L355
[ample-stacks]: https://stacks.math.columbia.edu/tag/0D2P
[square]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Hilbert/SectionPencil/BaseChange.lean#L32-L85
[compact]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Cohomology/FlatBaseChange.lean#L343-L356
[tensor]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Modules/BaseChange.lean#L109-L130
[flat-stacks]: https://stacks.math.columbia.edu/tag/02KH
[clear]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Modules/ClearDenominators.lean#L235-L248
[assembly]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/ZInQKernel/Contrib/OneProof/PazukiInputs.lean#L184-L202
[c8]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/docs/research/fold-c8.md#1-result
[mumford]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/OneProof/PhiSurjCharZero.lean#L140-L182
[first-closure]: https://github.com/CheyLoveday/diophantine-z-q/blob/38dc3563f70a0e286728e752f56733252464cd5e/ZInQKernel/Contrib/OneProof/PazukiPicardFixedLocus.lean#L19-L35
[site]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/OneProof/KleimanPicZeroSite.lean#L9-L25
[height]: https://github.com/Deicyde/diophantine-z-q/blob/7f58b0149966df60ccc1008cb9ef2de12df3c66e/ZInQKernel/Contrib/OneProof/PazukiInputs.lean#L237-L243
[gaga]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/ZInQKernel/Contrib/OneProof/GAGAMorphism.lean#L58-L82
[scope]: https://github.com/Deicyde/diophantine-z-q/issues/14#issuecomment-7076116788
[draft]: https://github.com/CheyLoveday/diophantine-z-q/pull/6
[fork-rules]: https://github.com/CheyLoveday/diophantine-z-q/blob/c40d7521b2b82c122a2dd32b75fd88a70c547b9b/AGENTS.md
[guide]: https://github.com/CheyLoveday/diophantine-z-q/blob/d1b6ff042a654fa92c60c49fabcfdabe47099295/AGENTS.md#working-on-dzq-in-this-fork
[checks]: https://github.com/Deicyde/diophantine-z-q/blob/f0334871b407fb899939ab502c777668f593a491/docs/one-proof/CONTRIBUTING.md#how-to-check-it

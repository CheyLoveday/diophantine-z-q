# Prescribed fibre-class detection

## Result and scope

The nonquadratic detection producer and its retained switching consumer are proved conditionally on precise arithmetic and retained-comparison inputs. No detecting determinant, finite-plane detection, or vanishing of image first cohomology is an input to the producer.

The main declarations are:

- `produce_kernel_detection`: through a prescribed nonzero fibre class, choose an independent partner and an actual arithmetic kernel sequence with nonzero determinant at the square of its conjugation coset.
- `produce_arithmetic_detection`: extract genuine finite-stage representatives, construct their actual inert arithmetic label, prove representatives nonidentity on an ultrafilter-large set, and prove the normalized localization determinant nonzero.
- `makeArithmeticDetection`: construct the resulting witness, partner, and detection proof.
- `producedLimitNonquadStep`: pass the derived determinant to `detectedLimitNonquadStep`. The retained localization identity, duality, and side-to-stage comparisons are the standard remaining consumer inputs.

The exact statements and axiom dependencies of every named declaration and all input-record fields are recorded in the declaration audit.

## Kernel and prescribed-class argument

The selected sequence belongs to

\[
 H=\prod_i\bigl(\operatorname{derivativeKernel}_i\cap\operatorname{Fix}(B_i)\bigr).
\]

Each component therefore fixes the specified Tate precision, the constructed finite character field, and the prescribed arithmetic kernel fields. Kernel fields are separate from the cochain evaluation fields: the latter are realized on the conjugation coset, not required to be fixed by the kernel representative.

Actual finite kernel membership proves the twisted Tate congruence and exact limiting action identity. The induced coefficient dictionary then proves that this sequence kernel acts trivially on the coefficient module.

For a cocycle vanishing on this kernel, the scalar identity proves

\[
 (\mu-1)c(g)=g\,c(z)-c(z),\qquad
 c(g)=g\bigl((\mu-1)^{-1}c(z)\bigr)-(\mu-1)^{-1}c(z).
\]

Thus kernel restriction is injective; image-cohomology vanishing is proved by the scalar argument rather than assumed. The scalar is the manuscript's fixed \((1+2^n)^4\). Its difference from one is proved nonzero at characteristic-zero height-one tests away from two.

An independent partner is chosen in first cohomology when its dimension is greater than one. The global boundary-reflection comparison transfers independence to the genuine evaluated cocycles. A finite coefficient image-span witness forces their full joint kernel-value span. Polarization then selects one actual kernel element, not merely a linear combination of evaluations.

## Finite realization and normalization

Every original continuous cochain, without a cocycle hypothesis, has a finite normal rational evaluation field at each retained precision. The proof uses compactness, a finite cover by translates of finite fixing subgroups, and a normal closure. The basis-field constructor includes all original basis cochains and every original stage field in one finite compositum.

Finite Chebotarev and the constructed stage-prime theorem produce the actual inert label. Agreement on a normal finite field also retains squares. The prescribed square evaluations and selected rational Frobenius-square evaluations therefore have equal integral limits on every original basis column.

At the fixed decomposition embedding, Frobenius compatibility gives conjugacy. Projected cocycle equivariance supplies one common transport matrix for both classes. Its integral determinant is a unit. Consequently

\[
 \det[\operatorname{loc}(a),\operatorname{loc}(b)]
 =\det[\pi c_a((\tau h)^2),\pi c_b((\tau h)^2)]\det A\ne0.
\]

The fibre evaluation is

\[
 \sum_j I(a)_j\,\operatorname{specialize}
 \left(\lim_i z_{j,i}(\operatorname{Frob}_i)\right).
\]

Integral basis evaluations are limited before specialization or application of localized minimal-model coordinates. No integral stage-cocycle lift of every fibre class is postulated. In particular, original basis columns need not be cycles; the retained cochain identity makes a fibre cycle into a crossed homomorphism only after coefficient change. This is why the consumer composition uses the retained route.

## Precise remaining inputs

The following records are hypotheses to be instantiated from the arithmetic objects and retained comparison maps. They are not constructed unconditionally from an arbitrary continuous character or a bare matrix complex.

1. **`InducedCoefficientDictionary`**: conjugation exchanges the two induced summands, and restriction to sequences fixing the number field is the actual limiting twisted Tate action. These are the usual induced-coefficient identifications in transversal coordinates. The precise universal identities are printed in the audit. Kernel triviality is derived from them and finite arithmetic kernel membership.
2. **`ArithmeticCommonScalar`**: a fixed integer `n ≥ 2` and an actual rational Galois sequence `element`, acting by the fixed scalar and central modulo the particular arithmetic sequence kernel. This is the manuscript's common-kernel scalar hypothesis, lines 4766–4774, with its arithmetic construction in (H1), lines 2882–2892. Finite-stage kernel membership alone does not establish this hypothesis for the chosen character and arithmetic fields.
3. **`CoefficientSpanWitness`**: finitely many actual rational Galois sequences whose coefficient endomorphisms span the full endomorphism algebra. This is the characteristic-zero, nonquadratic finite image-span input of lines 4779–4785. No residual irreducibility or residual rank-two detection is claimed.
4. **`RetainedEvaluation`**: original integral basis cochains, localized coordinates, retained degree-one and degree-two evaluation maps satisfying the cochain identity, reflection of global principal cocycles to boundaries, and the normalized projected evaluation identity. These are the retained cochain comparison and coefficient-change inputs in lines 4651–4704 and 4809–4830. The global boundary-reflection condition is precisely first-cohomology injectivity, not kernel restriction or prime detection. A sufficient cochain-embedding criterion is proved in `boundary_of_principal_under_embedding`.

For the switching composition, `hloc` identifies the retained localization with the normalized original-basis Frobenius evaluations at the produced label. `hdual`, `φ`, and `φ'` are the existing duality and side-to-stage comparison inputs. The determinant supplied to the consumer is computed by the producer, not assumed in any of these inputs.

The global comparison assertion is for the primitive and derivative models of the manuscript. It is not asserted directly for arbitrary orthogonal zero/full models; those require the retained contraction at the chosen test ring, as explained in lines 4706–4717.

## Verification and constraints

Only new contribution files were written. No existing source was edited, and no version-control operation, whole-project build, package update, `lake exe` invocation, subagent, memory write, or human outreach was used. Verification uses single-file compilation at six threads and the prescribed processor affinity and priority.

All 75 theorem declarations compile. The complete scratch declaration audit checks 127 named declarations and 22 input/output-record fields, with no missing entries and no errors. Every recorded dependency set is contained in `{propext, Classical.choice, Quot.sound}`. The main producers and switching composition each use exactly those three standard axioms.

No proof placeholder or additional axiom is introduced. The declaration audit contains the exact declarations and the scratch axiom-dependency output; the final proof source contains no diagnostic printing commands.

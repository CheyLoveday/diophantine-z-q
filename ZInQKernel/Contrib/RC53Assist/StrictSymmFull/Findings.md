# Retained full local conditions: symmetry and contraction reduction

The formal contraction-and-compatibility mechanism is proved for the actual switch. Its arithmetic application still requires the specified retained contractions of the full local complexes. A separate, stronger result proves descent of the original traced cup formula for the literal retained continuous switch, given its genuine forward truncated isotropy datum, without any old-place contraction or degree-two bound.

## 1. The original retained switch has compatible reverse isotropy

Let the switch at q have strict and relaxed conditions S_v and U_v, with inclusion φ_v. These are the conditions of the defined derivative switch on continuous cochains, not arbitrary complexes. At q, S_q is the actual strict derivative subcomplex [Z⁰ → 0]. At every v ≠ q, both S_v and U_v are the same given old condition, including any retained full continuous-cochain condition.

Let I be the given genuine forward truncated isotropy datum for these conditions. At v ≠ q, let b_v : U_v → S_v be the retained inverse of φ_v. Define the reverse homotopy, without swapping the arguments of I, by

    hʳ_v(u,t) = h_v(b_v u, φ_v t).

At q, take the relevant reverse homotopies to be zero. The actual strict condition has no degree-one or degree-two cochains there. At an old place, the forward isotropy identity for b_v u and φ_v t is exactly the reverse isotropy identity. Its agreement with the original homotopy is literal:

    h_v(s, φ_v t) = hʳ_v(φ_v s, t).

After canonical target truncation, degree one of the local target is zero. The assembled homotopies therefore give the complete compatible reverse datum used for strict orthogonality.

The constructions `actual_reverseIsotropy` and `continuous_retainedReverseIsotropy` supply this datum. The theorems `actual_strictOrth`, `actual_exists_residuePairing`, `actual_original_residuePairing`, and `continuous_original_residuePairing` prove strict orthogonality and the descent

    tr((0,s,−ιu) ∪ (0,t,0)) = P(eR[g t], eR[g u]),

for dt = 0 and du = φs, with P a bilinear form on the retained quotient coordinates. The last theorem uses genuine global and local continuous cochains over arbitrary compatible topological groups and continuous coefficient modules; it does not assume discrete coefficients. No symmetry assumption on the coefficient pairing, old-place degree bound, or old-place contraction is required for this descent result.

This does not prove the all-cochain cup-one condition `StrictSymm` for the original chosen forward homotopy. The reverse datum above uses the retained identification, not the particular swapped cup-one construction. It is nevertheless a complete reverse datum and discharges the strict-orthogonality hypothesis of traced descent.

## 2. Route B: the authorized reduction preserves the genuine data

For the RC26 genuine switch interface, `RetainedFullReduction q old F` records precisely:

1. q is not in F;
2. at each v in F, the old condition is the full subcomplex of the actual local continuous cochains;
3. each such full condition has a specified contracting homotopy in all degrees;
4. at each v ≠ q outside F, the actual old condition has zero degree-two term.

Only the conditions in F are replaced by zero. Every other old condition and the new derivative condition are retained. The result is the defined switch family with this erased old family. The assumptions refer to its actual local complexes; they do not assume symmetry or traced descent.

The forward condition comparisons are the actual inclusions. Both local-condition inclusion squares commute exactly (`reduced_condition_maps`). The reduced isotropy datum is the pullback of the original genuine datum in every bidegree (`reducedIsotropy_h`):

    h′(s,u) = h(j_S s, j_R u).

No unrelated null-homotopy is substituted. The original cup formula and every trace of it are preserved exactly on the forward comparison (`reduction_cup_naturality`, `reduction_traced_pairing`). These statements are for arbitrary cochains, not just cohomology classes, and do not replace the pairing or trace by zero.

The contraction gives the required inverse comparison of Selmer cochains. It is not the uncorrected operation of forgetting a component. For a local deformation retract (j,p,h), the projection and lifted homotopy are

    (a,u,x) ↦ (a,p u,x + ιh u),
    (a,u,x) ↦ (0,h u,0).

The cochain-map and homotopy identities are proved. In particular,

    1 − jp = dh + hd

holds on the condition complexes and on their actual Selmer complexes. `actual_erasedSelmer_equivalences` proves that the same forward maps used by the cup formula are homotopy equivalences of the genuine reduced and original strict and relaxed Selmer complexes. Thus the exact forward traced-pairing identity is an identification under cohomology isomorphisms, not an assertion about an arbitrary smaller model.

`actual_retained_arrows` also proves that a cochain arrow f between the original genuine complexes transfers as j_S f p_R, with a homotopy-commutative inclusion square. An original homotopy between arrows transfers by the same precomposition and postcomposition.

The reduced strict family has zero degree-two term (`erased_switch_degreeTwoZero`). The theorem `reduced_strictSymmetry` consequently supplies all three required conclusions for the pullback of the original genuine datum:

- the placewise RC26 `StrictSymm`;
- the general cup-one `StrictSymmTrunc` before target truncation;
- exact general `StrictSymm` after canonical target truncation.

The RC26 normalization wrappers retain the coefficient-topology assumptions of its existing genuine-switch interface. The direct continuous descent theorem in Section 1 has no discreteness restriction. The abstract deformation-retract calculations themselves make no degreewise finiteness assumption.

## 3. The displayed contraction is tied to actual local actions

The endomorphism `localActionEnd v g` is the actual action of the local group element g on the restricted coefficient module. For chosen Frobenius and inertia elements φ and σ, `actualTameComplex` is the manuscript's model with

    A = Φ − 1,   C = g − 1,   D = Φ − N_q(g),   DC = CA.

Here Φ and g are those actual actions. The theorem `full_contraction_of_tame_comparison` transports either displayed contraction to the actual full continuous-cochain condition, provided a retained all-degree homotopy comparison with this actual tame model and the corresponding unit operators are given.

For primitive quadratic inertia, the explicit action hypothesis σm = −m gives g = −1. `primitive_inertia_isUnit` proves that C = −2 is a unit when 2 ≠ 0 in the test field. `primitive_tame_relation` proves DC = CA for these actual actions. Accordingly, `full_contraction_of_primitive_tame_comparison` needs only that action hypothesis, the indicated test-field condition, and the retained full-cochain/tame-model homotopy comparison. It makes no assertion for an unused full condition with trivial inertia.

## 4. What remains open

The formal compatibility step in route B is closed, conditional on the specified actual contractions. To apply it arithmetically, the following bindings are still needed:

- For every full place selected for removal at a manuscript-approved test localization, construct the retained all-degree homotopy comparison from the actual full continuous-cochain condition to the actual tame model, with the actual Frobenius and inertia actions.
- Bind the primitive inertia action hypothesis and the test-field condition, or the appropriate actual Frobenius-unit hypotheses at the central moving localization. The unit calculations here do not establish those arithmetic bindings from a concrete coefficient representation.
- Supply the original genuine forward truncated isotropy datum. Every result is about that given datum or its exact pullback; its arithmetic construction is not supplied here.

The relevant procyclic comparison provides a map from a two-term model for finite discrete coefficients and low-degree cohomology calculations. It does not provide the retained tame all-degree homotopy comparison required above. Vanishing of H², or abstract acyclicity, is not substituted for that input and is not used to claim literal vanishing of the full degree-two cochain term.

All-cochain `StrictSymm` for the original chosen forward homotopy remains unproved. The cyclic symmetry theorem `actual_cyclicStrictSymm` is proved using the specified contractions and applies only to closed strict cochains in both slots. The original traced descent result in Section 1 is stronger for that application and requires no such contraction.

The manuscript passages used are 5055–5061 for retention, 2813–2815 for authorized replacement, and 3731–3735 and 3776–3779 for the displayed contractions. No new external arithmetic fact or printed premise was introduced.

## 5. Verification

The contribution contains 44 theorems and the explicit homotopy constructions. Ordinary single-file checks succeed without warnings. The audit records the complete types and axiom reports of all 94 declarations and the three structure constructors, covering every theorem and every construction. Every axiom report is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

The pre-existing sources were left unchanged. No dependency module was built and no version-control operation was performed.

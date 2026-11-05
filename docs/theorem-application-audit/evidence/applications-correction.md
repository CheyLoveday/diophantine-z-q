# Additive correction to the sealed RC report, and central-functional clarification

4 November 2026. The sealed report is `work/astra-final-rc-unconditional-closure-audit-001/REPORT.md`, SHA256 `da18bc014ea500ed842950e31898cdf50ff7f9efcba68a0c66c7505e16255f72`. Its bytes remain unchanged. Root's direct source review identified the following erroneous shorthand in its section 12. This note corrects that report, not the manuscript or raw proof source.

## 1. Correct unused-prime factor

Delete the section 12 sentence defining v_q through primitive polynomials P_e and P_delta. In particular, the formula v_q=P_delta/P_e^2 in that sentence is wrong. The exact source is RD1316-1326, and current V4e03a:320-325 states it correctly:

    v_q = (l_q/e_q^2 - 1)/2,
    eta = product_q (1 + v_q(1+g_q)).

Here e_q=a_q-z-z^-1, and l_q is the product of the two local determinants in RD1290-1293. Both are units over O[G], since their reductions modulo the maximal ideal are nonzero at the nonconstant odd-exponent scalar (1+t)^m. The polynomial identity

    (1+a_q z+z^2)(1+a_q z^-1+z^-2)
       = (a_q+z+z^-1)^2 mod 2

holds before character evaluation. Thus l_q/e_q^2-1 belongs to 2 O[G], and v_q is an actual element of O[G]. There is no division by a group order and no successive loss of powers of two.

At an active character x(g_q)=-1, the q factor is 1. At an inactive character x(g_q)=+1, it is 1+2v_q=l_q/e_q^2. The support comparison in current A310-311 is

    l_q u_rel = e_q^2 epsilon_q u_prim,
    epsilon_q in Lambda^times.

Multiplying by the inactive correction therefore gives epsilon_q u_prim exactly in the generic fraction field. Taking the product over inactive q gives

    tilde_u_x = epsilon_x u_prim,x,
    epsilon_x in Lambda^times.

This is valid at every character. No evaluation at a zero of e_q or l_q is performed in forming the fractions. Such functions are nonzero as generic elements, and the displayed equality identifies their product with the regular primitive coordinate times a Lambda-unit. It supplies the unique regular continuation at any height-one zero, including t=0 when e_q(0)=0. The individual eta_x may have a pole there. Only the already-cancelled product is specialized. Acyclic constituents have both specified class-functional coordinates zero, so the same identity is harmless there.

The original report's P-polynomial formula would instead give an inactive factor 1+2P_delta/P_e^2, which does not in general cancel the actual support factor. It must not be used. The proof and manuscript use the correct difference quotient above.

## 2. Why the central functional has no compensating pole

The last paragraph of the report's section 13 compresses a necessary premise. Constant generic and central ranks do not alone show that an arbitrary rational functional is regular. The functional here is regular because of its construction from the actual duality diagram.

Put A=Lambda_(t). For the primitive constituent, the only full local conditions beyond the old exact Kummer conditions are the active ramified primes and the moving auxiliary prime. At an active ramified odd prime, the inertia differential is -2, a unit in A. At the moving prime, the limiting central Frobenius determinants are nonzero by the fixed bound on v2(a_r+/-2), with r tending to 1. Their determinants are therefore A-units. These local complexes are acyclic over A and, being bounded finite free, have A-linear contractions. For the unknown base h0=1 there are no active ramified primes; the same moving-prime argument applies directly.

Consequently the orthogonal-to-relaxed comparison has an actual homotopy inverse over A. Old Kummer conditions and any derivative plane conditions have their exact local orthogonality already built into the finite diagram. Lift the conjugate actual cycle using that A-inverse and compose with the retained integral global duality map. This constructs a closed degree-two A-functional lambda_A. After passing to the generic field it is the same functional used in the O-construction: both represent the inverse of the same comparison followed by the same duality morphism. No equality between arbitrary independently chosen cochain representatives is asserted.

This is the construction in RD439-464 and, with central specialization spelled out, RD1062-1072. Although the latter paragraph appears inside the simple-zero central-formula proof, the contraction argument uses local acyclicity and the trace bound, not nonvanishing of the point, finite Sha, or an analytic-rank hypothesis. It applies to the unknown full-corank-one base as just checked.

Now, if its generic rank is one, the central rank is also one by the full Selmer hypothesis and complementary rank zero. The equal-rank determinant base-change lemma applies to the actual A-cycle and the actual A-functional lambda_A. The central point is zero rationally if the base derivative is zero, by the conductor-one height formula and the retained torsion-killing boundary. Its tensor with the regular central lambda_A is zero. There is no compensating pole. If the generic complex is acyclic, the specified coordinate is zero by definition. In both cases the corrected coordinate also centralizes to zero by section 1's Lambda-unit comparison.

These corrections and explanations do not supply or assume a new arithmetic theorem. They identify a transcription error and restore the precise existing functional construction. The sealed RC report should always be read with this note. The external-theorem applicability audit remains in progress; neither this note nor the prior report approves the global polynomial theorem or a Lean result.

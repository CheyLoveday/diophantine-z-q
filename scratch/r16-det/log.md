# r16-det results log

- Merged d62e5b85 (r16-close) cleanly (7dd00681b).
- Reworded host path in docs/research/r16-close.md (l.16-18) and scratch/r16-close/log.md to "a local copy of the 2005 printing"; grep cloud-b4 now empty in r16-close files.

## Statement check of DS Thm 9.6.5 at k = 2 (VERIFIED, pdftotext of local copies of the 2005 printing and the 2016 fourth printing)
- DS Thm 9.6.5 (2005 p. 393; 2016 p. 404): for f in S_k(N,chi) a normalized eigenform, each lambda | l, an irreducible 2-dim rho_{f,lambda}: G_Q -> GL_2(K_{f,lambda}), unramified at p not dividing lN, and "the characteristic equation" of rho_{f,lambda}(Frob_p) is x^2 - a_p x + chi(p) p^{k-1} = 0.
- Same page, after the theorem: displayed det rho_{f,lambda} = chi chi_l^{k-1} (with Exercise 9.6.3(a)).
- Same page, identification paragraph (2005 p. 393, 2016 p. 404): Section 9.5 constructed rho_{f,lambda} for k = 2 but did not prove irreducibility or that the equation is the characteristic equation. => DS identify 9.6.5's rho_{f,lambda} at k=2 with the Section 9.5 construction (lambda-component e_lambda V_l(A_f), Exercise 9.5.2(a)), and the theorem asserts the characteristic equation for it. Same wording in both printings.
- Exercise 9.6.3 (2005 p. 397; 2016 p. 409): (a) det from charpoly for 9.6.5's rho; (b) converse.
- Consequence: AfTateLam.AfTateDSLambda (charpoly over K_{f,lambda}) is DS Thm 9.6.5 at k = 2 for the 9.5 realization; AfDetLambda is its constant term (det = constant coeff of a degree-2 charpoly).
- R16CoreYDS965.lean: lake build +ZInQKernel.Contrib.OneProof.R16CoreYDS965 -> Build completed successfully (11359 jobs) (VERIFIED). Contents: AfCharpolyDS965 (leaf, = AfTateDSLambda verbatim, afCharpolyDS965_iff Iff.rfl), det_finrank_of_charpoly, afDetLambda_of_ds965 (hM, h : AfCharpolyDS965 -> AfDetLambda), r16CoreY_of_ds965.

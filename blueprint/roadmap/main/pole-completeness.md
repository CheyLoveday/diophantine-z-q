---
article_id: af_07b61cae8c50eaaa6ef18746
declaration: def
origin: cited
statement: formalized
lean: ZInQ.PoleCompleteness, ZInQ.polePoly, ZInQ.PoleSoluble, ZInQ.poleS0
---

# Pole completeness

For $B\in\mathbb Q$ and witnesses $b_0,\ldots,b_5,e,z,r_1,r_2,w\in\mathbb Q$ put
$m=(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5)$, $A=mB$, $H=A(A-B^2)$,
$T_1=A(A-e)(A+3e)$, $T_2=A(Az^2-eH)(Az^2+3eH)$ and
$$Q_{\rm pole}=B\Bigl(\sum_{i=0}^5(b_i^2-b_i)^2+(eHzw-1)^2+(r_1^2-T_1)^2+(r_2^2-T_2)^2\Bigr).$$
Write $\Phi(B)$ when $Q_{\rm pole}$ has a rational zero with input $B$. For $B\ne0$ a zero puts
$(A,r_1)$ on the manuscript curve $y^2=x(x-e)(x+3e)$ and $(Az^2,zr_2)$ on $y^2=x(x-eH)(x+3eH)$.

Pole completeness is the assertion that every rational $B$ with square reduced
denominator, $0<B<1/2$ and $v_p(B)\ge4$ for every $p\in S_0=\{2,3,5,7,13\}$ satisfies $\Phi(B)$.

This is the manuscript's polynomial. Pole completeness (Theorem 5.2) is an explicit
hypothesis of the current headline. Its derivation from the restricted converse is not
formalized. Route K used a different polynomial and is retired from active aggregation.
The changed assembly's complete build and retained comparison are pending Open Math OS.

## Depends on

None.

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Pole predicate](../../sources/multiplication-locators.md#pole-predicate)

---
article_id: af_2f0b2ecb3bf06eff5e1da42f
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves31.fontaine1982HTAbVar
---

# The Hodge–Tate theorem of Tate and Raynaud for abelian varieties

The *Hodge–Tate statement* is the following assertion. Let $F$ be a finite extension of
$\mathbb Q_p$, $\overline F$ an algebraic closure of $F$, $G_F=\operatorname{Gal}(\overline F/F)$,
$A$ an abelian variety of dimension $g$ over $F$, and $V_pA=\mathbb Q_p\otimes_{\mathbb Z_p}T_pA$
with $T_pA=\varprojlim_nA(\overline F)[p^n]$, on which $G_F$ acts through its action on the points
of $A$. Let $G_F$ act on $\mathbb C_p$ through the restriction map $G_F\to G_{\mathbb Q_p}$ along an
embedding of $\overline{\mathbb Q}_p$ in $\overline F$, and let $F$ act on $\mathbb C_p$ through the
same embedding. For $i=0,1$ let $W_i$ be the $F$-vector space of $\mathbb Q_p$-linear maps
$\varphi:V_pA\to\mathbb C_p$ with $\varphi(\sigma v)=\chi_p(\sigma)^i\,\sigma\bigl(\varphi(v)\bigr)$
for all $\sigma\in G_F$ and $v\in V_pA$, that is, of the $G_F$-equivariant maps
$V_pA\to\mathbb C_p(i)$. Then $\dim_FW_1=\dim_FW_0=g$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
It is Théorème 2 of Fontaine, which he credits to Tate and Raynaud and proves anew, for $K=F$ finite
over $\mathbb Q_p$, in dimension form. Fontaine gives canonical $F$-linear bijections from
$H^1(A,\mathcal O_A)$ onto $\operatorname{Hom}_{\mathbb Z_p[G_F]}(T_pA,\mathbb C_p)$ and from
$H^0(A,\Omega^1_A)$ onto $\operatorname{Hom}_{\mathbb Z_p[G_F]}(T_pA,\mathbb C_p(1))$, and the
equality of both dimensions with $g$ is printed in the proof on the same page; the statement keeps
only the two dimensions. A $\mathbb Z_p$-linear map from $T_pA$ to $\mathbb C_p(i)$ extends uniquely
to $V_pA$, and a generator of $\varprojlim_n\mu_{p^n}(\overline F)$ identifies Fontaine's
$\mathbb C_p(1)$ with the twist used here. Fontaine allows any complete discretely valued field of
characteristic $0$ with perfect residue field of characteristic $p$; the statement takes only finite
extensions of $\mathbb Q_p$. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Fontaine Theorem 2](../../../sources/height-decomposition-locators.md#fontaine-theorem-2)

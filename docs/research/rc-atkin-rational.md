# Rational Atkin–Lehner action for the (O.7) input

**Scoped stop.** The new Lean result is rational field membership of
$j(q^m)$ for every positive $m\mid N$. This supplies both pullback
generators for every $Q\parallel N$. The matrix calculation below
confirms those generators in the pinned chart's convention. The
consumer uses `X0Branch.model`:
`ParamJoin.algebraicParametrizationAtScale` and
`AtkinPin.actualParametrization_transform_chart` both name it
explicitly. No `X0Model3` dependency is needed.

The rational involution, descent to `BasedAtkinOnPoints`, and generic
input of (O.7) remain open. Both declarations in `Coordinates.lean`
elaborated and passed their axiom audits during a scoped build attempt,
but that attempt failed on the accompanying matrix proof. A concurrent
Lean job on the host prevented a standalone build of the isolated file.
The unverified matrix and scheme code was left out of the commits.
No printed leaf is added.

## Statements

The declarations are in `ZInQ.Manuscript.RC.AtkinRational`.

| Declaration | Statement and use |
| --- | --- |
| `Coordinates.levelInvariant_of_dvd` (private) | For $m>0$, $m\mid N$ implies that $z\mapsto j(mz)$ is invariant under $\Gamma_0(N)$. The lower left entry condition at level $N$ implies that at level $m$. |
| `Coordinates.jqN_mem_of_dvd` | For $N,m>0$ and $m\mid N$, `jqN m ∈ modularFunctionField N`. Over $\mathbf C(j)$ the existing orbit degree bound applies to $j_m$ and each $j_N+t j_m$. The exact degree of $j_N$ bounds the compositum by $\mathbf C(j,j_N)$. The existing rational Laurent descent then gives membership over $\mathbf Q$. Apply this to $m=Q$ and $m=N/Q$. |

Both `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. They appear in the attempted
build, not in a successful build of the isolated file. See
`scratch/rc-atkin-rational/log.md` for the build outcomes.

## Construction and exact stop

**ON THE SPOT (c): check the pullbacks in the actual chart.** Put $M=N/Q$.
By `TauCeti.IsAtkinLehnerMatrix.exists_entries`, the chosen matrix $A$
has entries $Qa,b,Nc,Qd$ in row order, with $Qad-Mbc=1$. Then

$$
 A=\begin{pmatrix}a&b\\Mc&Qd\end{pmatrix}
   \begin{pmatrix}Q&0\\0&1\end{pmatrix},\qquad
 \begin{pmatrix}N&0\\0&1\end{pmatrix} A
 = Q\begin{pmatrix}Qa&Mb\\c&d\end{pmatrix}
     \begin{pmatrix}M&0\\0&1\end{pmatrix}.
$$

Both left factors of the non-scalar products are in
$\mathrm{SL}_2(\mathbf Z)$; the scalar $Q$ acts trivially on the upper
half-plane. Thus $j(A\tau)=j(Q\tau)$ and $j(NA\tau)=j(M\tau)$.
This checks the `atkinGL` convention directly. The Laurent orders at
infinity are $-Q$ and $-M$; the literal swap of the original series
is the Fricke case $Q=N$.

**ON THE SPOT (c): build the rational map.** The first missing
declaration is a ring homomorphism
$\alpha_Q:\mathbf Q(j,j_N)\to\mathbf Q(j,j_N)$ satisfying, for all
$\tau$ and $f$,

$$
 \operatorname{fieldGerm}_{\tau}(\alpha_Q f)
  = (z\mapsto Az)^*\operatorname{fieldGerm}_{A\tau}(f).
$$

The pullback on the right is precomposition of punctured meromorphic
germs. It is well defined because the Möbius map is analytic and
locally invertible. For the two generators, use
`X0Model2.exists_hasSum_meromorphicContinuation` for the elements of
the rational field and `X0Model.hasSum_jN` for the dilations.
Uniqueness of the sum gives equality on a cusp tail. The meromorphic
identity theorem identifies the germs at each interior parameter.
Both images belong to the field by `jqN_mem_of_dvd`, so field
generation extends the substitution to every element. Injectivity
of the meromorphic germ embeddings and of Möbius precomposition
ensures that a nonzero denominator remains nonzero. This needs a
local germ comparison module, using the existing continuation API.

Extend the generic map using `Scheme.exists_hom_of_valuationRing_stalk`.
The stalk condition follows from `smooth_curve_valuation_stalk` and
`ParamAtScale.model_dimension`; the target is proper by
`X0Model.proper`. For the chart condition, pull back the analytic
arc at $A\tau$ along precomposition on valuation rings of finite
germs. This arc and the analytic arc at $\tau$ followed by the
extended map agree generically by the displayed compatibility.
Uniqueness in `X0Model.existsUnique_specialization` identifies them
over the valuation ring. Precomposition preserves the finite limit,
so the closed complex points agree. This step compares branches
of the normalization even over singular points of the plane equation.

For the square, `AtkinPin.atkinInterior_involutive` gives the
identity on the chart. To show the chart is dense over $\mathbf Q$,
choose $\tau$ with $j(\tau)$ transcendental: the range of $j$ is
connected and nonconstant by its pole, so it cannot be contained in
the countable, totally disconnected set of algebraic numbers.
By `X0Model2.complexPoint_jProjection` this point lies over the
generic point of the $j$-line. The $j$-projection is finite, hence
closed, so the point on the integral curve cannot be closed. It
must be the generic point. The map $\operatorname{Spec}\mathbf C\to
X$ is therefore dominant over $\mathbf Q$. Apply
`ext_of_isDominant_of_isSeparated` on the reduced source. This
would supply the fixed `RationalAtkin (X0Branch.model N) hQ`,
with its original fields.

**ON THE SPOT (c): descend the based identity.** Let $P$ be
`projectiveValue` after the fixed $\pi$ and
$e=$ `(signUnit f hχ hQ : ℤ)`. The missing elliptic compatibility is
that the function $x\mapsto P(W_Qx)-[e]P(x)$ is represented by a
$\mathbf Q$-morphism $D:X\to\operatorname{Proj}(E)$ with that reading
after every field extension. It suffices to provide this for the
two maps at hand and $e=\pm1$. A scheme group law on the specific
projective Weierstrass curve compatible with `projectiveValue`
would give it. The group law on point types, `projectiveValue_map`,
and the comparison to a *supplied* abelian scheme in
`RC53Assist/AbelianCurve` do not give that comparison for the
fixed projective target. This is the separate scheme argument
needed to use density.

The pinned identity makes $D$ constant on the complex chart.
Over $\mathbf C$, reducedness, separatedness and Zariski density of
the interior imply that $D_{\mathbf C}$ is constant. Evaluation at
the rational cusp $b$ identifies that constant; faithful scalar
extension descends the equality of morphisms. A route that uses the
rational chart API directly is to take an affine neighborhood of
the common complex chart value. The pullback of each regular
function there has constant complex values along the chart.
By `sectionExpansion` and `ModFnField.laurent_unique_of_tail`,
its rational Laurent series is constant, with rational coefficient
at zero. Thus the pullback of the affine coordinate ring into
the function field factors through $\mathbf Q$. The generic
restriction of $D$ is a rational constant map. The separated
target and integral source extend equality to all of $X$.
In either route, comparing the complex chart points uses injectivity
of the point reading: the two affine coordinates determine the
ring map and the projective complement is the single rational identity.

Evaluating at $b=\texttt{infinityPoint}$ identifies the constant as
$P(W_Qb)-[e]P(b)$. Evaluating again after scalar extension and
subtracting gives exactly
`BasedAtkinOnPoints X W π hπ b e`. For the normalized conclusion
of `translatedAtkinAtInfinity`, one also needs $P(b)=0$ on this
same $\pi$. A direct formal proof uses the nonzero $q^{-2}$
coefficient $\kappa^{-2}$ of $x\circ\pi$. If the cusp mapped into the
affine chart $Z\ne0$, the $x$-coordinate would pull back to
$\mathbf Q[[q]]$ along `X0Model.formalQArc`, contradicting that
coefficient. Therefore the cusp maps to the projective identity.
This needs the generic-coordinate witness in
`dominant_morphism_of_classification`, or uniqueness of the map
with the given chart. The analytic cusp limit does not by itself
identify the value on the formal arc.

## Generic input and remaining hypotheses

The intended producer, at `N = newformLevel (Ecurve ℓ)`, takes
ellipticity, positive level, the fixed normalized form data
`f hχ hf`, `Lat hLat κ hκ`, a rational representative of `κ`,
and `hQ : Q ∥ N`. It returns the pinned chart's dominant $\pi$
over $\mathbf Q$, the rational involution with its chart,
`BasedAtkinOnPoints` at `infinityPoint` with
`e := (signUnit f hχ hQ : ℤ)`, and the normalized translated
identity over every field. No Atkin–Lehner hypothesis is in this
intended statement. For $Q=p^{v_p(N)}$ the sign is
`(wNew f hχ p : ℤ)` by definition. Its pointwise conclusion is
`ha` of `AtkinPin.pinned_atkin_quotient_of_specialization`.
The morphism version would supply `hgen` of
`GoodReduction.atkinQuotient_of_integralRelation` once the
generic-fibre identifications with the integral data are supplied.

| Input or proof still needed | Reduction or reason it remains |
| --- | --- |
| Ellipticity of `Ecurve ℓ` and $N>0$ | Concrete curve and stage inputs; `StageKummer.positiveLevel` is already in the tree. These are not printed inputs. |
| Normalized newform at $N$, trivial character and matching Fourier coefficients | Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises* (2001), Theorem A and the introduction as cited at tex 1779, locators **UNVERIFIED**. The conductor comparison reduces to Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert* (1986), local conductor theorem, number **UNVERIFIED**. The existing `ModularNewform` input and `AtkinPin.consumerNewform` compare with the consumer's form. |
| Period lattice for the chosen equation | Complex uniformization, e.g. Silverman, *The Arithmetic of Elliptic Curves* (2009), uniformization theorem, number **UNVERIFIED**. `IsLatticeOf` specifies the already chosen period data. |
| `IsParamScale` at `κ`, and its rational representative | Integrate the pullback of the rational invariant differential of the manuscript's based rational map. For its modular quotient, see Shimura, *On the factors of the jacobian variety of a modular function field* (1973), theorem number **UNVERIFIED**. Comparing rational differentials gives the scalar for a chosen rational map. Existence of another map does not identify the independently supplied `κ`; `ParamJoin/AtScale` takes its rationality as input. |
| Exact divisor and pinned eigenvalue | Divisibility is elementary. Atkin–Lehner, *Hecke operators on Γ₀(m)* (1970), eigenrelation locator **UNVERIFIED**, is already used via Lean and supplies only the newform step here. |
| `RationalAtkin` | Matrix calculation, rational Laurent algebra and valuative extension as above. The classical moduli operation quotients by $C_Q$ with new level $(C_N+E[Q])/C_Q$; see Deligne–Rapoport, *Les schémas de modules de courbes elliptiques* (1973), cyclic isogeny moduli and compactification, theorem number **UNVERIFIED**. The function field route needs the germ and model comparison, not a moduli leaf. |
| Represented difference, rational constancy and formal cusp normalization | Regular elliptic group law, e.g. Silverman (2009), algebraicity theorem, number **UNVERIFIED**; the gap is compatibility with evaluation on this exact `Proj`. Constancy by density and normalization by the pole are on-the-spot comparisons. |
| Specialization, multipliers and actual row | The integral model and coarse point comparisons remain separate. Good modular reduction uses Deligne–Rapoport (1973), theorem number **UNVERIFIED**; extension uses Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), Néron mapping property, locator **UNVERIFIED**. Manin–Drinfeld is cited via Elkik, *Le théorème de modularité de Wiles* (1996), manuscript p. 59 locator **UNVERIFIED**. These do not identify the independently fixed coefficient reading. CM points, cusp classes and the special-fibre object are outside this work. |

## Known issues

- Inherited: the Milne locators at tex 1784–1788 do not state the
  normalized-newform and good Hecke claims. See
  `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean`.
- Inherited: the earlier (O.7) audit flags the level-one scope of
  the cited Jetchev–Kane comparison at tex 8468–8474. The source
  locators for these inherited issues were not independently checked.
- The manuscript's based map has $\pi(\infty)=0$. The missing
  normalization here is the comparison to the constructed map at
  its formal cusp.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1779–1783: take the curve's actual conductor and newform. | OK |
| 1784–1788: the Milne locators for the normalized form and Hecke claim. | unverified (inherited citation scope above) |
| 1785–1787: base the rational map at infinity. | unverified (formal cusp comparison) |
| 1825–1828: use the same fixed period scale. | OK |
| 2937–2942: kill the image of the cuspidal classes. | unverified (outside this work) |
| 2943–2944: identify the pullback coordinates and their field. | gap filled (matrix check and Lean Laurent membership) |
| 2943–2946: descend the translated identity. | unverified (rational map and group-law comparison) |
| 8468–8474: cite Jetchev–Kane for the full-level supersingular comparison. | unverified (inherited citation scope above) |
| 8476–8479: specialize at the good prime. | unverified (outside this work) |
| 8487–8489: specialize the signed identity. | unverified (generic identity remains) |
| 9101–9113: use the eigenrelation in (O.7). | unverified (only part of the generic input proved) |
| 9331–9341: match orientation reversal with the sign on values. | unverified (generic and specialization comparisons remain) |

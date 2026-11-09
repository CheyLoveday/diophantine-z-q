# Orthogonal comparison, actual local classes and strict rows

Date: 2026-11-09. Author: Codex agent `/root/orthogonal_attack`.
This is a source-bound research derivation with a native Lean helper. It is
not an acceptance of the arithmetic determinant-switch theorem. It does not
modify the manuscript, the frozen 39-target packet or existing proof sources.

### 0) Problem restatement (brief)

At research source `fb29fe2bc6968e178a6458357c437574221b5338`, identify the
actual partner `z_perp=j_U^-1 c(z)` used in the manuscript's paired functional,
prove preservation of its derivative local cohomology class, and identify the
actual common-strict matrices and functional rows. Connect to the determinant
consumer without constructing a finite/singular quasi-isomorphism.

The authoritative manuscript is `manuscripts/quartic_v13.tex`, SHA-256
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
Bounded lookup read the actual arguments at 2898–2967 (coefficient carrier),
3431–3542 (derivative models and H22), 3842–4012 (actual paired functional,
localization contractions), 4577–4636 (retained inner diagrams), 5020–5093
(common-strict triangles), and 5351–5373 (singular orthogonal condition).
Also read the earlier arithmetic-boundary-cup functional audit and the
2026-11-09 scout. These contain prior ingredients; no novelty or exhaustive
historical-search claim is made. The earlier source audit treated the inverse's
localization compatibility as a retained square. L1–L3 below now derive that
compatibility from an explicit cone comparison and its common global projection.

### 1) Assumptions ledger

- Work at a specified ring R where the actual comparison is an integral
  homotopy equivalence. Over `S=O[G]`, `O=completed Lambda_(2)`, this uses the
  source's active Frobenius and moving inertia contractions. In primitive
  scalar `Lambda_p`, p not (2), it uses ramified active inertia -2 and moving
  inertia t away from (t), or central Frobenius at (t). At unused good places
  retain the unramified comparison. No inverse of t in a finite Artin ring.
- Actual local orthogonal and conjugate-condition diagrams have maps a_v and
  inclusion homotopies h_v. The global complex and its localization map are the
  SAME after identifying only the conjugate coefficient system, not M with its
  ordinary dual. Source old Kummer diagrams retain finite torsion and isotropy.
- The same bounded finite models retain these maps and homotopies when limits
  are used. This derivation proves polynomial identities on that tuple; it
  does not independently establish existence or uniform bounds for all such
  finite models. That source-level arithmetic/model premise remains visible.
- For the strict-H2 reduction only: use a fraction/test field K; the finite
  complex has cohomology (1,1) in degrees (1,2), no other cohomology; actual A
  spans H1 and its finite localization v is nonzero. For target independence,
  use either the actual exact relaxed-image statement or independently nonzero
  actual cup cross-evaluations. These two routes are recorded separately below.

### 2) Lemma-by-lemma resolution

**L1 — PROVED: an explicit orthogonal cone comparison preserves global projection.**

Put `G=continuous global cochains`, `L=direct sum of local cochains`, and
write the source and target local-condition sums as U and U'. Use H22's convention

```
C_U^n = G^n + U^n + L^(n-1)
D(g,u,q) = (dg,du,loc(g)-i(u)-dq).
```

After the coefficient identification, the global term and loc are common. Let
`a:U->U'` be a chain map and `i-i'a=dh+hd`. Define on ALL cochains, not only cycles,

```
j(g,u,q) = (g,a(u),q+h(u)).
```

Compute its third differential entry:

```
D' j: loc(g)-i'a(u)-dq-dh(u)
j D : loc(g)-i(u)-dq+h(du).
```

Their difference is `i(u)-i'a(u)-dh(u)-h(du)=0`; the first two entries agree
because a is a chain map. Thus j is a chain map and `p_G j=p_G` literally.
This is the constructed cone comparison, rather than an arbitrary equivalence
with assumed local-coordinate behavior.

The manuscript supplies these local maps in the indicated regimes:

- At the derivative place, finite and singular are separately self-orthogonal.
  Under their actual integral local-condition identifications, `a=id,h=0`.
  For singular this is stated and justified at 5351–5361; finite uses the same
  retained D0/D2 and F/S cross pairing at 5020–5059. This argument is independent
  of the singular terminal-rank conclusion surrounding 5351–5373.
- At active/moving discrepancies between zero and full, use the supplied
  contraction of the full local complex. A full-to-zero local map is `a=0`
  and h is its contraction, giving `i=dh+hd`; zero-to-full uses `a=0,h=0`.
  Thus this is still a comparison with global map the identity.
- Old Kummer/unramified maps and the specified homotopies are those of their
  actual local comparison diagrams, carried by derived scalar extension. Their
  inclusion square supplies exactly the displayed equation for h.

For Nekovar's alternative local entry `l=-q`, the differential becomes
`(dg,du,-loc(g)+i(u)-dl)` and the same map becomes
`j(g,u,l)=(g,a(u),l-h(u))`. This changes no global or derivative H1 class.
The boundary-cup packet uses that latter convention; its common trace sign must
be retained there, not inferred from this localization lemma.

**L2 — PROVED: a homotopy inverse preserves global and local H1.**

Let `k` be the source's actual homotopy inverse and choose
`j k-id = D H+H D` on the conjugate-condition cone. For a cocycle y, apply the
common global projection to obtain

```
p_G(k y)-p_G(y) = d(p_G H y).
```

Here `p_G j=p_G` was proved in L1. Apply the actual localization chain map:

```
loc(p_G(k y))-loc(p_G(y)) = d(loc(p_G H y)).
```

The two local H1 classes therefore agree. The comparison need not preserve
individual local-condition coordinates literally on cochains. H22 says their
images represent the same local class; a retained contraction changes the
representative by the explicitly retained boundary. Thus finite/tame coordinates
computed on H1 also agree. Any two homotopy inverses give the same local H1
identity, because each satisfies this proof.

Lean's `inverse_preserves_global_homotopy`,
`inverse_preserves_global_homology`, `inverse_preserves_local_homotopy`, and
`inverse_preserves_local_homology` prove this on Mathlib's actual
`HomologicalComplex`/`Homotopy`/`homologyMap`. They are generic theorems. Their
source application is L1 plus the actual localized contractions, not a new Lean
definition of continuous Galois Selmer complexes.

**L3 — REUSED + PROVED application: the actual partner's local coordinates.**

For actual z, take `y=c(z)` with the conjugate representation. L2 gives
`loc(z_perp)=loc(c(z))` on H1 for `z_perp=k c(z)`. The already separately proved
local conjugation theorem
`Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1_local_transport`
in `ConjugateLocalH1.lean`, with
its source arithmetic/retained-limit guards, gives

```
loc(A_perp)=(u v,0),
loc(B_perp)=(0,-u Jv).
```

Here `(v,0)` and `(0,Jv)` are the actual class localizations, u is the one
specified transport unit, and coefficient J is inserted once in the pairing
`Q(a,b)=e(a,Jb)`. L2 introduces no new scalar, denominator, primitive vector,
coefficient involution or extra J. The coefficient carrier remains the conjugate
carrier until its given Weil identification is used.

Consequently the two functionals are exactly those specified by the source:

```
lambda_A = PD_F(-,k_F c(A)),
lambda_B = PD_S(-,k_S c(B)).
```

The source defines these for any actual retained class, before knowing singular
rank one. Closedness/integrality follow from the actual inverse and duality
chain maps, with the localization scopes in the assumption ledger. This lemma
does not prove PD is the actual cone cup/trace; that is the parallel boundary
packet's obligation.

**L4 — PROVED ordinary linear/homological algebra: strict H2 is the canonical
2-dimensional target in the genuine rank-one generic case.**

Use the actual triangle `Cstr -> CF -> F[-1] -> Cstr[1]`. Its LES gives

```
0 -> H1(Cstr) -> H1(CF) --f--> F --partial_F--> W
  --pi_F--> H2(CF) -> 0,       W=H2(Cstr).
```

A spans H1(CF) and f(A)=v nonzero, so f is injective, H1(Cstr)=0, and
`dim W=(2-1)+1=2`. The other LES terms, using CF concentration and F[-1]
concentration in degree1, give no strict cohomology outside degree2. Over K,
`Cstr ~ W[-2]`. Each actual triangle therefore presents its middle complex
by `[local plane --partial_U--> W]` in degrees1,2, compatibly with that triangle.
This is a field presentation. It does not remove any integral strict torsion.

Define the rows basis-free FIRST:

```
r_F = lambda_A o pi_F : W -> K,
r_S = lambda_B o pi_S : W -> K.
```

They exist regardless of singular rank. Exactness gives
`r_F partial_F=0` and `r_S partial_S=0`. These are the actual PD functionals
pulled to W, not arbitrarily scaled dual generators. A change of a closed
cochain representative has no effect on these H2 functionals.

**L5 — PROVED under either stated source guard: independence of opposite
boundary directions and singular rank one.**

Choose x with `eta=area(v,x) !=0`; no integral primitivity of v is asserted.
Put `a=partial_F x`, `b=partial_S Jx`.

Route A: the actual relaxed image is
`U=K(v,0)+K(0,Jv)=ker(partial)` for the COMMON connecting map on F+S.
If `alpha a+beta b=0`, then `(alpha x,beta Jx)` lies in U. Since x and v
are independent, both alpha and beta are zero. This requires the source's
actual exact-annihilator argument at 5074–5082; it is not deduced from the
following determinant conclusion.

Route B: actual adjunction plus L3 gives nonzero opposite evaluations when its
shared trace/local-pairing scalar is independently nonzero:
`r_F(a)=r_S(b)=0`, `r_F(b)!=0`, `r_S(a)!=0`. Applying r_F and r_S to
`alpha a+beta b=0` proves beta=alpha=0. This route cannot be invoked merely
because the frozen unit theorem permits a zero common normalizer. The actual
trace factor's nonvanishing must be established separately.

In either route, W has dimension2, `partial_S(Jv)=0`, and
`partial_S(Jx)=b !=0`, so partial_S has rank1. The singular LES then gives
H1(CS) and H2(CS) each dimension1, no other cohomology; B spans H1(CS).

**L6 — PROVED dictionary, formal common-strict application still needs the
determinant bridge and source tuple.**

Choose ONE basis `(w1,w2)` of actual W and the retained local bases. The frozen
`CommonStrictData K Empty` dictionary is:

| Datum | Actual object |
| --- | --- |
| `D0,hF,hS` | unique empty matrices/vectors |
| `AF,AS` | matrices of actual partial_F and partial_S in the SAME W basis |
| `v,Jv` | actual f(A), s(B) with original common multiplier |
| `lamF,lamS` | rows r_F,r_S in that W basis |
| `cycleF,cycleS` | actual LES equations partial_F(v)=partial_S(Jv)=0 |
| `closedF,closedS` | exactness pi_U partial_U=0 followed by actual lambda |
| `area_ne` | chosen fractional complement x |
| `target_ne` | L5 independence, with Empty+Fin2 order used consistently |

No independent row scaling or functional-space map is introduced. The opposite
row evaluations are `lambda_A pi_F partial_S` and
`lambda_B pi_S partial_F`, precisely the consumer of boundary–cup adjunction.
The matrices are field models, so the strict integral determinant generator
must still be transported into their common basis. That is the determinant
packet's shared scalar c; this dictionary alone proves no actual integral
coordinate equality and supplies no unit assertion about c.

### 3) Main theorem

**Bounded source-interface result:** for the actual orthogonal/conjugate Selmer
comparison constructed from the source local diagrams at each legitimate
localization, its homotopy inverse preserves global and derivative local H1.
Hence the actual paired-functional partners have precisely the conjugate local
coordinates, with no extra normalization. The source generic rank-one triangles
have the above canonical strict-H2/Empty dictionary under the visible rank and
independence guards.

**OPEN for the combined arithmetic application:** actual cone cup/trace descent
and boundary identity; shared strict determinant lattice transport; compatibility
of all new cup/trace/comparison entries in the retained inner tuple; integral
universal group-ring descent where a scalar field theorem is insufficient.
Neither generic rank reduction nor this note licenses inference between
valuations at different height-one primes. No statement here refutes or newly
certifies the restricted converse or the full Diophantine theorem.

### 4) If refuted: repaired statement

No counterexample found to L1–L6 with their stated guards. A comparison merely
isomorphic on abstract cohomology is insufficient for L2: it must be the
constructed same-global-component map with actual homotopy inverse. For the
strict-H2 route, v=0 or finite generic ranks other than (1,1) invalidate L4.

### 5) Verification plan for the verifier role

- Recompute the j differential on arbitrary cochains; compare H22 and Nekovar
  signs by q=-l, not by independently changing one boundary sign.
- Check actual comparison direction, global carrier and local condition maps
  at derivative and old/active/moving places; retain the whole diagram.
- Verify Mathlib homotopy lemma direction k then j, and equality after the
  actual global and local projections. Do not infer literal row equality.
- Independently derive the strict LES dimensions and actual row pullbacks;
  reject v=0, rank jumps, zero trace in Route B, and row rescaling by2.
- Run `check_comparison.py`: exact finite-ring cone and homotopy model checks
  include wrong-sign, arbitrary-map, and nilpotent-inverse negative controls.
  These checks validate algebraic identities, not actual arithmetic existence.
- Review source hashes and native theorem statements/axioms; no local paranoid
  or external replay is claimed. Independent review is pending until authored
  by a separate agent against the final bytes.

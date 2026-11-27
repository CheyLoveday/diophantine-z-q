# The Heegner anchor at the fixed scale

`HeegnerAnchor.genuineHeegnerAnchor` constructs the fields and elliptic
points of `GenuineHeegnerAnchor` on the actual curve `Ecurve ℓ`. With
the existing curve and split imaginary quadratic field data and a
rational representative of the fixed scale supplied, the only remaining
geometric input is `CMFieldOfDefinition (X0Branch.model N)`. The
companion theorem `cmPointsAtScale` exhibits one rational morphism
`π` and, for every admissible conductor, an actual ring class field
point of the constructed model and the equality with `phiAn` at its
Heegner root.

The existing source audit records a citation error at tex 1784 and
1788: the cited pair covers the map and the quotient, but does not
supply the normalized newform or the stated Hecke identity. This proof
obtains the interior map from the parametrization join and uses no
Hecke relation. See Known issues below.

## Statements and consumers

Use `E := Ecurve ℓ`, `N := newformLevel E`, `X := X0Branch.model N`,
`D_K := NumberField.discr K`, and `Δ_d := D_K * (d : ℤ)^2`.
All names below are under `ZInQ.Manuscript.RC.HeegnerAnchor`.
The input `p : CSTParam E` can be literally
`⟨f, hf, Lat, hLat, hNC, κ, hκ⟩`; its `f`, `Lat`, and `κ` fields
reduce to the original data by definition (on-the-spot, provenance (c)).

| Declaration | Statement and role |
| --- | --- |
| `conductorOrder_discr` | For a quadratic number field and `[NeZero d]`, `(conductorOrder K d).discr = Δ_d`. Reuses the integral basis argument of the join (its lemma is private): the order is the kernel of the second coordinate modulo `d` in a basis `(1, ω)`, so its index is `d`. This supplies the order used for CM descent. |
| `splitPrime` (private) | For a rational prime `q` split in a quadratic `K`, there is a prime above `q` of absolute norm `q`, and `q ∤ D_K`. The two primes in the split hypothesis rule out the singleton cases of the degree formula. |
| `conductorForm` | For `N > 0`, quadratic `K` split at the primes of `2N`, and `Nat.Coprime d (N * D_K.natAbs)`, `IsCoprime Δ_d (N : ℤ)` and `∃ B C, IsHeegnerForm N Δ_d N B C`. Splitting at two makes the discriminant odd; the existing decomposition law gives the local unit square conditions, and the existing ring form theorem scales the conductor-one form. The arithmetic checks are on-the-spot (c). |
| `factor_embedding` (private) | For any algebraic extension `H/ℚ` and embeddings `ι : ℚ̄ →ₐ[ℚ] ℂ`, `j : H →ₐ[ℚ] ℂ`, there is `e : H →ₐ[ℚ] ℚ̄` with `ι.comp e = j`. The image of `ι` contains the roots of every minimal polynomial of an element of `H`. This factors the embedding returned by CM descent through the anchor embedding (c). |
| `fieldPoint_map_map` (private) | For composable rational algebra homomorphisms `e,j` and any field-valued scheme point `x` over ℚ, `(x.map e).map j = x.map (j.comp e)`. This is composition of maps of spectra (c). |
| `cmPointValue` | Given a fixed morphism over ℚ whose interior values agree with `phiAn`, `CMFieldOfDefinition X`, and an eligible order and form `(A,B,C)` of discriminant `Δ`, it gives `e : ringClassField O →ₐ[ℚ] ℚ̄` and `x ∈ X(e.fieldRange)` with `x.map (ι.comp e.fieldRange.val) = X.complexPoint (cmPoint A B Δ)`. For `Y = projectiveValue (x.comp π hπQ).val`, it gives `ι(e.fieldRange.val(Y)) = phiAn E p.f p.Lat p.κ (cmPoint A B Δ)`. Here both embeddings on `Y` mean coordinate maps. The proof uses `PreparedParam.projectiveValue_map`, including when `Y` is the origin. |
| `cmPointsAtScale` | On `X`, there is a single dominant `π` over ℚ such that for each `d > 0` coprime to `N * D_K.natAbs` there is a form `(N,B,C)` of discriminant `Δ_d` and the two comparisons of `cmPointValue` for `O = conductorOrder K d`. The equality for `Y` is the evaluation of `π_ℂ` at the same embedded source point. This supplies the CM comparison for the anchor at every admissible conductor. |
| `genuineHeegnerAnchor` | There exist `H : ℕ → IntermediateField ℚ ℚ̄` and `y : ℕ → E(ℚ̄)` such that for all `relGal, frob`, the record `⟨D_K, N, H, y, relGal, frob⟩` satisfies `GenuineHeegnerAnchor E K p ι`. At each admissible `d` the proof takes `H d = e.fieldRange` and `y d` to be the inclusion of `π(x_d) ∈ E(H d)`. These supply the coordinates and analytic comparison of `CCLGenuine`'s anchor. The fields and points outside the anchor's domain are filled with the bottom intermediate field and zero, respectively. |

The anchor is independent of the two Galois slots; the theorem leaves
both as arguments in its conclusion so that the caller can provide
lifts for the actual trace computation. It does not prove the
`NormRelations` conjunct of `CCLGenuine`, nor does it identify an
independently supplied witness of the norm print with this datum.
Cai–Chen–Liu is still used for the norm relations on the appropriate
geometric family; the comparison theorem can also be specialized at
a supplied form via `cmPointValue`. Pointwise existence does not give
the compatibility of ideal lattices and fixed orientations, a shared
identification of all the fields with the transport tower in `K̄`,
or the exact forms and reference points pinned by the prepared
selectors. Those selectors are unchanged.

No new structure, named assumption, or print was added.
`ConductorComparison` is a private definition used only to express
the conclusion of `cmPointsAtScale` at a given conductor. In
`cmPointValue`, the map and its interior comparison are the ingredients
of the existing `AlgebraicParametrizationAtScale` theorem. The interior
comparison has a wider analytic domain than the CM equality, but
contains no arithmetic descent or compatibility with the fixed
embedding. `CMFieldOfDefinition` only descends the source CM point;
it mentions neither an elliptic curve nor the anchor. The rational
representative only describes a scalar.

## Exact remaining inputs

These are all the hypotheses of `cmPointsAtScale` and
`genuineHeegnerAnchor`. Their arithmetic helpers take just the field,
degree, level and conductor inputs shown in the statements above.
The general `cmPointValue` replaces the actual curve and fixed-scale
construction by an elliptic `E/ℚ`, a nonzero newform level,
`X : X0Model (newformLevel E)`, a morphism `π`, its triangle over ℚ
and its interior comparison, and takes the indicated order,
discriminant, sign, coprimality and form explicitly.

| Input | Tex and owner |
| --- | --- |
| `ℓ : ℕ`, `[E.IsElliptic]`, `[NeZero N]`; `p.f : S₂(Γ₀(N))` and `p.hf : ∀ n : ℕ, 0 < n → (qExpansion 1 p.f).coeff n = (E.LFunction n : ℂ)` | 1761–1787, 2836–2838. Existing actual curve and newform data. |
| `p.Lat : PeriodPair`, `p.hLat : IsLatticeOf E p.Lat`, `p.hCM : IsNonCMLattice p.Lat`, `p.κ : ℂ`, and `p.hκ : IsParamScale N p.f p.Lat p.κ` | 1765–1767, 1785–1787, 1825–1828. Existing curve and fixed normalization data. The lattice non-CM proof is carried by the existing CST record; the CM evaluation only uses the lattice and scale proofs. |
| `K : Type`, `[Field K]`, `[NumberField K]`, `[IsTotallyComplex K]`, `Module.finrank ℚ K = 2`, `∀ q : ℕ, q.Prime → q ∣ 2 * N → CST.SplitsIn K q`; `ι : ℚ̄ →ₐ[ℚ] ℂ` | 2839–2844, 2915–2917. Existing field data and chosen complex embedding of the cloud anchor. The exclusion of extra units is needed in the norm application and is unnecessary here. |
| `∃ c : ℚ, (c : ℂ) = p.κ` | 1785–1787, 1825–1828. ELLIOT input, fixed scale. The sibling rationality report reduces it to identifying the independently given rational map at this scale on a width-one cusp tail. The identification for the manuscript map is substantial; choosing a new rational scale would change the input. |
| `CMFieldOfDefinition (X0Branch.model N)` | 2839–2844, 2915–2917. Sibling CM field of definition. Substantial CM theory on this rational model. The specialization needed here is exactly: for every admissible `d` and level-`N` Heegner form of discriminant `Δ_d`, `∃ j : ringClassField (conductorOrder K d) →ₐ[ℚ] ℂ, ∃ x : FieldPoint X.overQ (ringClassField (conductorOrder K d)), x.map j = X.complexPoint (cmPoint A B Δ_d)`. With that source descent and the rational scale, the anchor follows. |

## Known issues

- The locators for the citation error at tex 1784 and 1788 come from
  the existing `RC/PrintsAnalytic/Milne.lean` audit: normalized
  newforms are addressed in Proposition 11.21, and the pair cited
  by the manuscript does not give the Hecke identity. The same audit
  records two unused misprints in Conjecture 11.17, concerning
  coprimality and the conductor factor.
- The exact independent field-of-definition passage in Cai–Chen–Liu
  and the Shimura fallback locator remain **UNVERIFIED**, as recorded
  in `PreparedParam/Prints.lean`. The
  [repository audit](../theorem-application-audit/evidence/parallel-geometry-acceptance-report.md#a034--heegner-norm-relations)
  locates the trace theorem as Theorem 2.15, p. 3730. The proof here
  does not read the offprint or take source point descent from its
  trace interface.
- The anchor uses a conductor `d`, whereas `CMFieldOfDefinition`
  uses an order discriminant as its integer input. The conductor
  formula proves the translation. The form construction gives an
  existential choice at each conductor, as required by the anchor.
  No new manuscript or source error was found in the steps used.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1761–1767, 1779–1783: actual elliptic curve and the newform and lattice setup. | OK — uses the existing curve and CST data. |
| 1784, 1787–1788: source locator for the normalized newform and Hecke property. | error — the cited pair does not give these statements, per the existing audit. |
| 1785–1787, 2836–2838: rational modular map. | gap filled — the existing algebraization gives a single interior morphism at the given rational scale on the constructed model. The cusp and Abel–Jacobi comparisons are outside this step. |
| 1825–1828: use the same period normalization throughout. | OK — the CST record uses the original `f, Lat, κ` by definition. |
| 2839–2844: split field and order of conductor `d`. | gap filled — splitting gives the local square checks and the order has discriminant `Δ_d`. |
| 2915–2916: CM point over the ring class field. | unverified — assumed as the existing source descent on the constructed model; the exact literature passage is not verified. |
| 2915–2917: evaluate at the chosen point. | gap filled — identify the complex chart at a Heegner root, compose over `H_d`, and use the fixed embedding to obtain the analytic value. |
| 2915–2916: compatible ideal lattices and fixed orientations through the family. | unverified — the anchor only quantifies over one form per conductor and does not certify compatibility. |
| 2917–2936: split specialization and trace identities. | unverified — this proof does not check or invoke the norm application; the trace statement remains with the existing print. |

## Verification

All three new Lean files passed `lake env lean -j1 -DautoImplicit=false`.
All eight theorem axiom checks reported only `propext`,
`Classical.choice`, and `Quot.sound`. The final checks ran serially.
An earlier dependency build briefly overlapped its replacement after
an attempted stop; both jobs were stopped and confirmed exited before
work resumed under a single build lock. This violated the run's
one-process limit.

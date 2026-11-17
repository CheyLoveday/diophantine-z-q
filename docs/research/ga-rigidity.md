# ga-rigidity: rigidity for 𝔾_a, and the two SGA 7 IX rows with Déf. 3.4's hypothesis

Task ga-rigidity (2026-11-17). Base wip/leaf-fold33b (75d94fe7) with origin/main merged (795180cf).

## 1. Result

**Proved in Lean (no `sorry`, standard axioms only)**, over an algebraically closed field `k`, in the kernel's
functor-of-points language (`ZInQ.HeightSplit.algPt k R = Spec R` over `k`):

1. every homomorphism of `k`-group schemes `𝔾_a → 𝔾_m^r` is trivial (`GaRigidity.gaHom_torus_trivial`; any field);
2. every homomorphism `𝔾_a → B` to a proper group scheme, in particular to an abelian variety `PkgI3.AbVar k`, is trivial
   (`GaRigidity.gaHom_proper_trivial`, `GaRigidity.gaHom_abVar_trivial`);
3. if the identity component of `G` is an extension of an abelian variety by a split torus (the kernel's
   `ZInQ.HeightSplit.HasSemiAbelianIdentityComponent`, i.e. `GroupModelO.IsSemistable` on the geometric special
   fibre), every homomorphism `𝔾_a → G` is trivial and `G` contains no subgroup scheme isomorphic to `𝔾_a`
   (`GaRigidity.gaHom_trivial_of_semiAbelian`, `GaRigidity.noGaSubgroup_of_semiAbelian`).

**Wired into both rows.** `GaRigidity.SGA7` states the two rows with SGA 7 IX Déf. 3.4's hypothesis ("the identity
component of the geometric special fibre contains no `𝔾_a`", per the queue11 reviewer verdict) and proves each field,
statement unchanged, from its new form:

| field (statement unchanged) | proved by | from the new leaf |
| --- | --- | --- |
| `sga7_IX_Cor3_3` : `SGA33Steps.SGA7_IX_Cor3_3` | `GaRigidity.SGA7.sga7_IX_Cor3_3_of_def34` | `GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34` |
| `sga7_IX_3_5_ForwardGeom` : `UnipotentForward.SGA7_IX_3_5_ForwardGeom` | `GaRigidity.SGA7.sga7_IX_3_5_ForwardGeom_of_def34` | `GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34` |

Each new leaf is its old statement character for character with only the semistability hypothesis replaced by
`IsSemistableDef34 𝒩 := NoGaInIdComp (geomSpecialFibre 𝒩)` (no homomorphism `𝔾_a → 𝒩_κ̄` that is a closed immersion
with image in the identity component `idCompSet`). The glue between the two (the shared reason both rows were GLUE) is
now a Lean proof: `GaRigidity.SGA7.isSemistableDef34_of_isSemistable`.

COMPILE STATUS: see §5.

## 2. Files

* `ZInQKernel/Contrib/OneProof/GaRigidity.lean` — Steps (1)-(3); imports only `ZInQKernel.OneProof.H.TailY` (where
  `algPt`, `HasSemiAbelianIdentityComponent` and, through it, `PkgI3.AbVar` live).
* `ZInQKernel/Contrib/OneProof/GaRigiditySGA7.lean` — the printed condition, the two new leaves, the two discharges;
  imports `GaRigidity`, `SGA7IX33Cor` (declares `SGA7_IX_Cor3_3`) and `UnipotentForward` (declares
  `SGA7_IX_3_5_ForwardGeom`).
* `scratch/ga-rigidity/` — `GaR.lean` (the development copy of `GaRigidity.lean`), `G1.lean`, `G2.lean` (pieces),
  `autofold.json`, `Discharges.lean` and its output, `log.md`.

## 3. The proofs

**Step (1).** A homomorphism `𝔾_a → 𝔾_m` is, by Yoneda, a unit `u ∈ k[X]ˣ` with `u(X + Y) = u(X)u(Y)`. Over a field
`k[X]ˣ = kˣ` (`Polynomial.isUnit_iff`), so `u = c` with `c = c²`, `c ≠ 0`, i.e. `u = 1` (`unit_additive_eq_one`). For
`𝔾_m^r` embedded in `U` by `e` (injective, multiplicative, natural, as in `HasSemiAbelianIdentityComponent`),
naturality turns the homomorphism condition on `e(t)` into the condition on each `tᵢ` (`gaHom_torus_trivial`).

**Step (2).** Valuative criterion at the point `∞` of `ℙ¹`, no `ℙ¹` and no extension of rational maps needed:
* `R = k[s]_(s) ⊆ K = Frac k[s]` (a DVR; `s = 1/x`); the residue map `ρ : R → k`, `f ↦ f(0)`; the translation
  `τ_c : R → R`, `s ↦ s/(1 + cs)` (an automorphism with inverse `τ_{-c}`, `ρ ∘ τ_c = ρ`), extended to `K`, with
  `τ_c(1/s) = 1/s + c` (§3 of the file);
* for `g : 𝔾_a → B`, `B` proper: the `K`-point `g(1/s)` extends to `Q : Spec R → B` (existence); both `Q ∘ τ_c` and
  `Q · g(c)` extend `g(1/s + c) = g(1/s) g(c)`, so they are equal (uniqueness, `B` separated); composing with
  `ρ` gives `Q(∞) = Q(∞) g(c)` in the group `B(k)`, so `g(c) = 1` for every `c ∈ k` (`gaHom_proper_point`, any field);
* morphisms `𝔸¹ → Y` to a separated `k`-scheme of finite type agreeing at all `k`-points are equal (`k` algebraically
  closed: closed points are `k`-points, `pointOfClosedPoint`; Mathlib's `ext_of_apply_eq`) (`ext_of_points`).

**Step (3).** Let `U ⊆ G` be the open connected subgroup, `π : U → B` the map to the abelian variety, `ker π = 𝔾_m^r`.
* `g` lands in `U` (`gaHom_factors_open`): `V = g⁻¹(U)` is open and contains `0`, hence a basic open `D(f)`, `f(0) ≠ 0`;
  the `c ∈ k` with `g(c) ∈ U(k)` form a subgroup (`U(k)` is a subgroup, `g(a + b) = g(a)g(b)`), containing all `c` with
  `f(c) ≠ 0`; for any `c` choose `b` with `f(b) ≠ 0 ≠ f(b − c)` (`k` infinite), so `c = b − (b − c)` is in it; then `V`
  contains every closed point, and `𝔸¹` is Jacobson, so `V = 𝔸¹` and `g = g' ≫ inc`;
* `g' ≫ π : 𝔾_a → B` is trivial (Step (2)), so `g' ∈ ker π`, `g' = e(t)`, trivial by Step (1);
* a trivial homomorphism is not a closed immersion (it identifies the `k`-points `0` and `1` of `𝔸¹`).

## 4. The new leaves

Both are published leaves in **printed form under the queue11 reading** of SGA 7 IX Déf. 3.4: the hypothesis is
"the identity component of the geometric special fibre of the Néron model contains no subgroup isomorphic to `𝔾_a`",
stated literally (`NoGaInIdComp`: no `𝔾_a`-homomorphism that is a closed immersion with image in `G⁰`). The
conclusions and all other hypotheses are unchanged from the rows (which carry their own readings: Cor. 3.3 specialized
to traits; Prop. 3.5 (i) ⇒ (iv) at `σ = τ`, per the 11-17 reading recorded in kinds.tsv).

| leaf | rating | reason |
| --- | --- | --- |
| `SGA7_IX_Cor3_3_Def34` | printed form (specialization to traits), under the queue11 reading of Déf. 3.4 | the old leaf's only gap to the print (the semistability dictionary) is removed; the base specialization is the old leaf's, proved as a consequence step there |
| `SGA7_IX_3_5_ForwardGeom_Def34` | printed form (direct instance of Prop. 3.5 (i) ⇒ (iv), `σ = τ`), under the queue11 reading | same |

**Reading risk (recorded, not resolved; no network, SGA 7 not read here).** If Déf. 3.4 instead states semistability
as "`N⁰_s̄` is an extension of an abelian variety by a torus" (semi-abelian), the *old* rows were already literal and
the new leaves are consequences of the print only together with the converse dictionary ("no `𝔾_a` ⇒ semi-abelian",
Chevalley's structure theorem plus "a nonzero smooth connected unipotent group over `k̄` contains `𝔾_a`"), which is
not proved here. The fold should then keep the old fields. Under either reading the dictionary proved here
(semi-abelian ⇒ no `𝔾_a`) is the direction the old rows needed.

**Dictionary choices.**
* `𝔾_a`-homomorphisms are stated by Yoneda (a morphism `Spec k[X] → G` with `g ∘ add = (g ∘ pr₁)·(g ∘ pr₂)` on
  `Spec k[X,Y]`), the same functor-of-points style as the kernel's `HasSemiAbelianIdentityComponent`.
* "Subgroup isomorphic to `𝔾_a`" = image of a homomorphism `𝔾_a → G` that is a closed immersion. "In `G⁰`" = image
  contained in `idCompSet G` (for a group over a field: the connected component of the unit).
* `NoGaSubgroup` (no `𝔾_a` in `G`, proved from semi-abelian) implies `NoGaInIdComp` (no `𝔾_a` in `G⁰`) trivially; the
  leaves use the weaker `NoGaInIdComp`, so they are the stronger (literal) statements.

## 5. Checks

(filled in below as they run)

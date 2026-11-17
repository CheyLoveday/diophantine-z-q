# hcm-lattice: `hCM` as a direct instance of Shimura 1971 Thm 5.4

Task hcm-lattice, 2026-11-17. Base: wip/leaf-fold33b d879bb73. Log: `scratch/hcm-lattice/log.md`. Lean:
`scratch/hcm-lattice/HCMLattice.lean`. Its proposed path is `ZInQKernel/Contrib/OneProof/HCMLattice.lean`; it imports
only `ZInQKernel.Contrib.OneProof.ShimuraMainCM`, not `Main`.

## 1. Result

A reviewer found two steps between the print and hcm-dict's leaf `HCMDict.ShimuraThm54`. Both are now closed in
Lean. The task allowed one step, the Weierstrass-map step, to become a Silverman leaf; it is proved instead, so no
new leaf enters. Everything in this section is VERIFIED (compiled; no `sorry`, no `axiom`; only `propext`,
`Classical.choice`, `Quot.sound`).

**The new leaf.** `ZInQ.Contrib.HCMLattice.ShimuraThm54Local` is a new `def`; the old one is kept. It states
Shimura's Thm 5.4 with the print's own hypotheses and definitions:

* **The hypothesis on `ξ`** is `IsAnalyticIso`, an analytic isomorphism `ℂ/𝔞 → E(ℂ)` written in `ℙ²(ℂ)` coordinates:
  * a bijection `ℂ/κ𝔞 → E(ℂ)`;
  * near every point, a holomorphic lift to `ℂ³ ∖ 0`;
  * a differential that vanishes nowhere.

  The group law is assumed as well.
* **The lattice `s⁻¹𝔞`** is the print's: any lattice `𝔟` with `𝔟_p = s_p⁻¹𝔞_p` for every prime `p`, where
  `K_p = ∏_{v∣p} K_v` and `𝔞_p` is the closure of `𝔞` in `K_p`.
* **The element `s⁻¹u`** is the print's: `v` represents `s⁻¹u` when `v ≡ s_p⁻¹u (mod 𝔟_p)` for every prime `p`.

**Theorems.**

```
theorem shimuraMainCM_of_local (h : ShimuraThm54Local) : T5Glue.ShimuraMainCM          -- what hCM's consumers use
theorem shimuraThm54_of_local (h : ShimuraThm54Local) : HCMDict.ShimuraThm54          -- the old leaf, from the new one
```

**`#discharges`** (`scratch/hcm-lattice/FoldCheck-output.txt`, run against the built `Main`):

```
DISCHARGES [hCM] by ZInQ.Contrib.HCMLattice.shimuraThm54_of_local
  still assumes: [ZInQ.Contrib.HCMLattice.ShimuraThm54Local]
  axioms: [propext, Classical.choice, Quot.sound]
```

**The manual Main fold.**

* `scratch/hcm-lattice/FoldCheck.lean` imports `OneProof.Main` and `OneProof.Discharges` and inlines `HCMLattice.lean`.
  It contains:
  * `frozenTarget_hCMLocal`, which is `frozenTarget` with `hCM := shimuraThm54_of_local hCM`;
  * `frozenTarget_hCMLocal'`, the folded `Main.lean` body. In it the binder becomes
    `hCM : HCMLattice.ShimuraThm54Local`, and both uses become `(HCMLattice.shimuraMainCM_of_local hCM)`.

  Both depend only on the standard axioms.
* `scratch/hcm-lattice/MainFolded.lean` is `Main.lean` with the fold applied and `HCMLattice` inlined. It compiles,
  and `ZInQ.OneProof.frozenTarget` depends only on `[propext, Classical.choice, Quot.sound]`.

**Count.**

* `hCM` was rated `consequence / GLUE / GLUE` (Addendum 2). The proposed rating is `published (unread) / LEAF /
  LEAF`, pending a reviewer (section 3).
* Strict GLUE among the Tian–Yuan–Zhang and Gross–Zagier hypotheses goes from 4 to 3 (h21C, h33, hGZ remain).
* The H part is unchanged (16/18).
* Over all 39 hypotheses: 17 LEAF / 22 GLUE becomes 18 / 21.
* No other count rises. The Weierstrass-map step is proved, so there is no Silverman leaf, and no new GLUE `def` is
  introduced.

## 2. The new leaf

```lean
def ShimuraThm54Local : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) = I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (𝔟 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔟) →
    (∀ p : ℕ, p.Prime → locLat p 𝔟 = (fun x => ideleComp p s⁻¹ * x) '' locLat p 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticIso E (kappa m '' 𝔞) ξ → (∀ z w, ξ (z + w) = ξ z + ξ w) →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      InducesBij (E.map (σ : ℂ →+* ℂ)) (kappa m '' 𝔟) ξ' ∧ IsHolomorphicMap (E.map (σ : ℂ →+* ℂ)) ξ' ∧
      ∀ u v : QNeg m, (∀ p : ℕ, p.Prime → diagP p v - ideleComp p s⁻¹ * diagP p u ∈ locLat p 𝔟) →
        HCMDict.conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)
```

### New definitions

Each is genuine: it is stated directly in terms of Mathlib's objects, with no new structures.

**Local objects at a rational prime `p`** (§L):

* `PlacesAbove m p` is the set of height-one primes of `𝓞_K` that contain `p`.
* `Kp m p = ∏_{v ∣ p} K_v` uses Mathlib's `adicCompletion`. It is the standard model of `K ⊗_ℚ ℚ_p` (STANDARD; e.g.
  Neukirch II §8, UNVERIFIED number).
* `projP p : 𝔸_{K,f} → K_p` is the restriction to the places above `p`, and `diagP p : K → K_p` is the diagonal map.
* `locLat p 𝔞 = closure (diagP p '' 𝔞)` is `𝔞_p`. For a finitely generated `ℤ`-module this is `𝔞 ⊗ ℤ_p`, because
  `ℤ` is dense in `ℤ_p`.
* `ideleComp p s = projP p s_f` is `s_p`, and `ideleComp p s⁻¹` is `s_p⁻¹`.

**Maps into `E(ℂ) ⊂ ℙ²(ℂ)`** (§A):

* `IsProjCoord W P X Y Z` says that `[X : Y : Z]` are homogeneous coordinates of the point `P`:
  * an affine point is `(X/Z, Y/Z)` with `Z ≠ 0`;
  * the point `O` is `[0 : Y : 0]` with `Y ≠ 0`.
* `IsHoloLift` / `IsHolomorphicMap` say that, near every point, `ξ` has a holomorphic lift `(X, Y, Z) : U → ℂ³ ∖ 0`.
  This is the complex structure of `ℙ²(ℂ)`.
* `IsImmersion` says that the differential vanishes nowhere: `F ∧ F' ≠ 0` for a lift `F` (`wedge`).
* `InducesBij W Λ ξ` says that `ξ` is `Λ`-periodic, injective modulo `Λ`, and onto.
* `IsAnalyticIso := InducesBij ∧ IsHolomorphicMap ∧ IsImmersion`. This is a biholomorphism of Riemann surfaces
  `ℂ/Λ ≅ E(ℂ)`: a bijective holomorphic map whose differential never vanishes has a holomorphic inverse.

### Rating: printed form (direct instance)

Every difference from the print is a special case or a weakening of the conclusion:

1. **`E` ranges over short Weierstrass models only.** This is a special case.
2. **The hypothesis on `ξ` is stronger than the print's, so the leaf is weaker.** The hypothesis is the print's
   analytic isomorphism (biholomorphic) together with the group law. It therefore implies the print's hypothesis in
   both readings of "analytic isomorphism": with the group law and without it.
3. **The conclusion keeps only part of what the print gives.** It keeps that `ξ'` is holomorphic and induces a
   bijection `ℂ/𝔟 → E^σ(ℂ)`, together with the commutation law. It drops the uniqueness of `ξ'`, its group law, and
   the holomorphy of its inverse.
4. **`𝔞` and `𝔟` are lattices of `K`, given as period-pair lattices `κ𝔞`.** This is the print's hypothesis on `𝔞`.
   It also restates the print's fact that `s⁻¹𝔞` is a lattice.
5. **`s⁻¹𝔞` and `s⁻¹u` are the print's definitions through `p`-components**, in Shimura's §5 notation (UNVERIFIED,
   from memory). The leaf quantifies over every lattice `𝔟` with those components, and over every `v` that satisfies
   the local congruences. Reading this as the print's single `s⁻¹𝔞` and single class `s⁻¹u` uses the local–global
   principle for lattices of `K`: `𝔟 = {x ∈ K : x ∈ 𝔟_p for all p}`. This principle is part of the definition the
   print uses (STANDARD). It is the one point in this list that is not proved in Lean here (section 5).
6. **The setting is the one hcm-dict and `ShimuraMainCM` already use, unchanged.** This covers `ArtinCond`, Tau Ceti's
   arithmetic-Frobenius normalization of the Artin map, the normalization of `e`, and `conjPt`.

**Locator.** G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm 5.4. The
definitions of `s𝔞` and `su` through `p`-components are in the same section. Also S. Lang, *Elliptic functions*,
Ch. 10, Thm 3. Both numbers are UNVERIFIED: I recalled them and did not read the pages; there is no network access
here. Proposed `locators.md` row: `ShimuraThm54Local | Shimura 1971 Thm 5.4 (Lang, Elliptic functions, Ch. 10
Thm 3) | unread | numbers UNVERIFIED`. I did not edit that file, because it is shared.

## 3. Rating discussion: what changed relative to Addendum 2

| reviewer's step (hcm-dict leaf) | now |
|---|---|
| hypothesis `IsAnalyticUnif` is a Lean surrogate for "analytic isomorphism" | hypothesis is `IsAnalyticIso` over `ℙ²` coordinates (genuine). The consumer supplies it: `toPoint_isAnalyticIso` proves the Weierstrass map `z ↦ [℘ : ℘'/2 : 1]` is one. |
| `IsAnalyticUnif ⇔ (℘(αz), ℘'(αz)/2)` dictionary needed between print and use | the conclusion is only "holomorphic and bijective". The use goes through the proved `eq_toPoint_of_holo` (the Weierstrass-map step), and the leaf does not depend on the dictionary. |
| `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂` (`sInvLat`) instead of Shimura's `(s⁻¹𝔞)_p = s_p⁻¹𝔞_p` | the leaf uses the localization form. `locLat_sInvLat` proves `(sInvLat s 𝔞)_p = s_p⁻¹𝔞_p` for every lattice and every `p`, and `exists_periodPair_sInvLat` proves that `sInvLat s 𝔞` is a lattice. |
| "`v` represents `s⁻¹u`" as `s_f v − u ∈ 𝔞̂` | the leaf uses `v ≡ s_p⁻¹u (mod 𝔟_p)` for every `p`. `rep_local_of_global` proves that the global condition implies the local ones. |

## 4. Proofs (all compiled, `scratch/hcm-lattice/HCMLattice.lean`)

### §B. The Weierstrass map is an analytic isomorphism (`toPoint_isAnalyticIso`)

* **Bijection.** This comes from the vendored FLT theorem `isUniformization_toPoint`.
* **Away from `L`.** The lift is `(℘, ℘'/2, 1)`. It is an immersion because `℘'` and `℘''` have no common zero
  (`deriv_derivWeierstrassP_ne`). The argument:
  * Differentiating `℘'² = 4℘³ − g₂℘ − g₃` gives `℘'(2℘'' − 12℘² + g₂) = 0`.
  * The zeros of `℘'` are isolated. If instead `℘' ≡ 0` near a point, then `℘` would be constant there, and the
    Weierstrass map would not be injective modulo `L`.
  * Hence `℘'' = 6℘² − g₂/2` at a zero of `℘'`.
  * At such a zero, `g₂ = 12e²` and `g₃ = −8e³` would force `g₂³ − 27g₃² = 0`, which contradicts
    `discriminant_ne_zero`.
* **At `l₀ ∈ L`.** Write `w = z − l₀`. Mathlib's `℘[L - l₀]` and `℘'[L - l₀]` give `℘ = w⁻² + h` and `℘' = −2w⁻³ + k`,
  with `h` and `k` holomorphic near `l₀`. The lift is `[w + w³h : (−2 + w³k)/2 : w³]`; the third component of its
  wedge at `l₀` is `1`.

### §C. The Weierstrass-map step (`eq_toPoint_of_holo`)

**Statement.** Let `ξ : ℂ → E_{L₀}(ℂ)` be holomorphic in the `ℙ²` sense, induce a bijection `ℂ/L → E_{L₀}(ℂ)`, and
satisfy `ξ(0) = O`. Then `ξ = ξ_{L₀}(α·)` with `IsScale L₀ L α`.

**Proof.**

1. **The bad set is countable.** The bad set is `ξ⁻¹(O) ∪ ξ⁻¹(E[2] ∖ O)`:
   * the points with `y = 0` are the finitely many roots of the cubic;
   * each fibre of `ξ` is a coset of `L`.

   So the good set `G` is dense.
2. **`x'/(2y)` has a holomorphic extension near every point** (`exists_local_ext`):
   * near a point with `y = 0` it equals `y'/(3x² − g₂/4)`, using that the cubic has simple roots;
   * near a point of `ξ⁻¹(O)` it equals `−u' + uq'/(2q)`, where `u = X/Y`, `w = Z/Y`, `q = 1 − a₄uw − a₆w²`, and
     `wq = u³` (the homogeneous equation).
3. **Gluing.** The local extensions glue to an entire `L`-periodic function (`exists_entire_of_local`). It is
   therefore a constant `α`, by Liouville and `IsZLattice.isCompact_range_of_periodic`.
4. **Near one point.** A local lift `g` through `ξ_{L₀}` (`exists_local_lift'`, hcm-dict's lift) satisfies
   `x' = ℘'(g)g'`. Hence `g' = α`, so `ξ = ξ_{L₀}(α · + β)` on a ball.
5. **Off a countable set.** By the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), the
   equality holds on the complement of the countable closed set `L ∪ (αz + β ∈ L₀)`. That complement is path-connected
   (`Set.Countable.isPathConnected_compl_of_one_lt_rank`).
6. **Everywhere.** At every point, compare homogeneous lifts. Their cross product vanishes on a dense set, hence at
   the point (`IsProjCoord.cross_eq_zero` and `eq_of_cross`).
7. **Conclusion.** `ξ(0) = O` gives `β ∈ L₀`. The kernels then give `L₀ = αL`.

### §L–§O. Lattices

* **`isOpen_latHat`.** For a lattice `𝔞`, `𝔞̂` is open: it contains `N·𝒪̂_K`, since `N·𝒪_K ⊆ 𝔞` (`two_coords`).
* **`locLat_sInvLat`.** Let `U = s_f⁻¹𝔞̂`, which is open, and use that `K` is dense in `𝔸_{K,f}`:
  * `(K ∩ U)_p` contains `projP(U)`;
  * `projP(U) = s_p⁻¹𝔞_p`, by continuity of `projP`.
* **`exists_periodPair_sInvLat`.** The lattice `sInvLat s 𝔞` satisfies `c₀𝒪_K ⊆ sInvLat s 𝔞 ⊆ c₁⁻¹𝒪_K`. The bounds
  come from Tau Ceti's `mul_nonZeroDivisor_mem_integralAdeles` applied to `s_f^{±1}`, together with
  `algebraMap_mem_integralAdeles_iff`. So `κ(sInvLat s 𝔞)` is a discrete, full-rank `ℤ`-submodule of `ℂ`. A basis from
  `ZLattice.rank` and `Basis.ofZLatticeBasis_span` gives the period pair.

### §P. From the new leaf to the uses

* **`shimuraMainCM_of_local`.** Apply the leaf with:
  * `𝔟 = sInvLat s 𝔞` (localization by `locLat_sInvLat`);
  * `ξ = ξ_P` (`toPoint_isAnalyticIso`).

  Then get `ξ'(0) = O` from the commutation law at `u = v = 0`, turn `ξ'` into hcm-dict's `IsAnalyticUnif` by
  `eq_toPoint_of_holo`, and finish as in hcm-dict (`eq_scaled_of_isAnalyticUnif`).
* **`shimuraThm54_of_local`.** The same route, with three more ingredients:
  * `isAnalyticIso_of_unif`: the old hypothesis implies the new one, through hcm-dict's dictionary and
    `IsImmersion.comp_mul`;
  * `exists_periodPair_sInvLat`, for the lattice `𝔟`;
  * `rep_local_of_global`, for the commutation law.

## 5. Open points

* **Local–global principle for lattices (item 5 of section 2).** The statement is:
  `𝔟 = {x ∈ K : diagP p x ∈ 𝔟_p for every prime p}` for every lattice `𝔟`.
  * It is not needed by any Lean proof here.
  * It is needed only for the informal argument that the leaf's "every `𝔟` / every `v` with these local data" is
    the print's single `s⁻¹𝔞` and single class `s⁻¹u`.
  * Ingredients:
    * `K ∩ 𝔟̂ = 𝔟` for general lattices. This follows from the tree's `latHat_inter_of_sandwich`, since every
      lattice has `n𝒪 ⊆ 𝔟 ⊆ d⁻¹𝒪`.
    * Local membership at every `p` gives `𝔟̂` membership, by a CRT argument with valuations at the places above
      the primes dividing `nd`.

  I did not formalize it (see the log for the status at the deadline).
* **Theorem numbers** for Shimura Thm 5.4 and Lang Ch. 10 Thm 3 are UNVERIFIED. The new leaf enters as "unread" until
  someone compares it with the print. The facts that need checking: whether Shimura's "analytic isomorphism" includes
  the group law (the leaf covers both readings), and whether the `p`-component definitions of `s𝔞` and `su` appear as
  stated.
* **Integration.**
  * Move `HCMLattice.lean` to `ZInQKernel/Contrib/OneProof/HCMLattice.lean`.
  * In `Main.lean`, add `import ZInQKernel.Contrib.OneProof.HCMLattice`, change the binder to
    `hCM : ZInQ.Contrib.HCMLattice.ShimuraThm54Local`, and replace both `(ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)` by
    `(ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM)`. `MainFolded.lean` is exactly this.
  * Proposed new kinds.tsv `hCM` row: `frozenTarget hCM published "hcm-lattice: printed Shimura 1971 Thm 5.4 with the
    print's hypotheses (IsAnalyticIso over P^2 coordinates) and s^-1 a by p-components; pending review" LEAF LEAF`.
* **Deliverables** (in `scratch/hcm-lattice/`):
  * `HCMLattice.lean`, the contribution (1.5k lines);
  * `FoldCheck.lean` with `FoldCheck-output.txt`;
  * `MainFolded.lean` with `MainFolded-output.txt`;
  * `log.md`;
  * the development copies `Lattice.lean` and `Analytic.lean`.

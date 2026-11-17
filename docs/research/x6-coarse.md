# x6-coarse: the Atkin–Lehner clause of `X₀(6,1)` in printed form; Elkies' `W` in isogeny form

Task x6-coarse, 2026-11-17. Base `e1b31749` (fork main, top `sixContactMin_of_open55`, bundle `OpenResearchLeaves38`).
Contribution: `ZInQKernel/Contrib/OneProof/X6AtkinLehnerIdeal.lean` (namespace `X6ALIdeal`). It imports only
`ZInQKernel.Contrib.OneProof.GRX6AbPrint` and `ZInQKernel.Contrib.OneProof.ElkiesX6StarEvery`, the modules that declare
the two statements it replaces. Working copy and checks: `scratch/x6-coarse/`. No other file under `ZInQKernel/` or
`blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a locator recalled without a source (no network on this host).

## 1. Main result

**The Atkin–Lehner reading risk of `x6CoarseModuli` is removed.** The leaf stated `w_m` in *twist form*,
`(A, ι) ↦ (A, ι ∘ Ad μ_m)`. The printed definition is the *ideal-quotient form*, `(A, ι) ↦ (A/A[I_m], ι_m)`, with
`I_m` the two-sided ideal of reduced norm `m`. This form is in Rotger, Trans. AMS 356 (2004), and Baba–Granath,
Canad. J. Math. 60 (2008) §2, as recorded in docs/research/gt-elkies.md §3; locators UNVERIFIED. It is also
Elkies' p. 10 form `A ↦ A/ker I_p`, per the lead's reading of arXiv math/0005160.

The new file states the printed form over genuine definitions and proves **both directions from the bundle's
existing fields** (all VERIFIED, compiled, standard axioms only). It adds no new textbook leaf.

| statement | content | hypotheses |
|---|---|---|
| `mem_idealI_iff` | `I_m := {a ∈ 𝒪 : m ∣ nrd a} = 𝒪 μ_m`, `μ_m = 1, i, j, ij` (the ideals are principal at `D = 6`) | none |
| `canonical` | `ι(μ_m) : (A, ι) → (A, ι ∘ Ad μ_m)` is a quotient of `A` by `A[I_m]` (`IsIdealQuotient`: equivariant isogeny whose kernel, as a functor of points on all `K`-schemes, is `A[I_m]`) | none |
| `iso_of_quotient_lat` | **every** quotient of `(A, ι)` by `A[I_m]` is isomorphic to `(A, ι ∘ Ad μ_m)` ("A/A[I] ≅ A with the conjugated action when `I` is principal", the fact the tree lacked) | textbook fields `gagaMorphism`, `mumfordTorsionAlgClosed` (and `uniformizationLeafAll`, proved) |
| `alTwist_of_alIdeal`, `x6CoarseModuli_of_ideal` | printed clause ⇒ twist clause of `X6CoarseModuli`/`X6Props` (every `α ∈ Aut 𝒪`, via `rep_cover` and inner twists); printed leaf ⇒ `X6CoarseModuli` | none |
| `alIdeal_of_alTwist`, `x6CoarseModuliIdeal_of_twist`, `x6CoarseModuliIdeal_iff` | twist ⇒ printed; the two leaves are equivalent | `gagaMorphism`, `mumfordTorsionAlgClosed` |
| `atkinLehnerWIdeal_subset`, `atkinLehnerW_eq_of_clause` | Elkies' isogeny-form `W` ⊆ the twist-form `W`; equal on every witness carrying the printed clause | none (`hom_ext_qbar`: maps of proper smooth curves over `ℚ` agree if they agree on `ℚ̄`-points) |
| `atkinLehnerW_eq` | the two `W`'s are equal on every witness | `gagaMorphism`, `mumfordTorsionAlgClosed` |
| `galoisClause_iff_natural` | the Galois clause ⇔ the naturality square of the coarse map at `Spec σ` (Mumford GIT Def. 5.6); uses the base change `bcAut` of a QM pair along `σ` | none |
| `gr512At_of_iso`, `gonzalezRotgerThm512X6_of_one` | GR Thm 5.12's conclusion transports between coarse witnesses (residue fields, CM points); one witness ⇒ every witness | T5 |
| `elkiesX6StarEvery_of_ideal'` | `ElkiesX6StarEvery` from `ElkiesX6StarEveryIdeal` (Elkies with his isogeny-form `W`), `X6CoarseModuliIdeal`, `shimuraMainThmIDeligneY3AbU`, `mumfordTorsionAlgClosed` | — |
| `ideal_of_elkiesX6StarEvery` | converse | `gagaMorphism`, `mumfordTorsionAlgClosed` |

So the leaf holds under either reading, and both readings are equivalent given two textbook fields already in the
bundle. The direction that the consumers use, printed ⇒ twist, needs nothing.

**How `iso_of_quotient_lat` is proved** (lattice model, §3 of the file). Let `φ : (A, ι) → (A', ι')` be a quotient
by `A[I_m]`.
1. Base-change to `ℂ` along `σQ` (`GR56.bcQ`) and take lattice data `D, D'` (`GR56.datQ`).
2. Lift `φ` to a linear `F`, and `ι(μ)` to `M = ρ(ι(μ))` (`HomLatticeCorr`, `AvSplit.Final.h69`).
3. The kernel hypothesis, transported to `ℂ`-points by the adjunction `Over.map ⊣ Over.pullback` (`ker_bc`), says
   `F z ∈ Λ' ⟺ M z ∈ Λ`.
4. `G F = n` (lift uniqueness, from `ψ φ = [n]`) and `M² = μ²` make `F` and `M` invertible.
5. So `M F⁻¹ : Λ' → Λ` and `F M⁻¹ : Λ → Λ'` are mutually inverse lattice maps, realized over `ℂ` (`HomLatticeCorr`)
   and equivariant (lift uniqueness).
6. The isomorphism descends to `ℚ̄` (`GR56.qmIso_descend`, T11(b)).

(Discharge output and fold: §5.)

## 2. Which form the print uses

* **The repository's reading** (VERIFIED, read). docs/research/gt-elkies.md §3 records the reading. The docstring of
  `ElkiesX6Star.IsAtkinLehner` and that of `ElkiesCoord`'s leaf repeat it: "the moduli definition of `w_m` on
  `X₀(D,1)` is `(A, ι) ↦ (A/A[I_m], ι_m)`, `I_m` the two-sided ideal of reduced norm `m`" (Rotger 2004;
  Baba–Granath 2008 §2; locators UNVERIFIED). gt-elkies notes explicitly: "Proving it from the ideal-quotient form
  would need quotients of abelian varieties by finite subgroup schemes, which the chain does not have."
* **The lead's reading of Elkies** (task statement): p. 10, `w_p : A ↦ A/ker I_p`, the same form.
* **The twist form is not printed** (SPECULATIVE, consistent with all of the above). It is the standard
  identification when `I_m = μ_m𝒪`, and it is now proved in Lean (`canonical`, `iso_of_quotient_lat`).

Verdict: **the print uses the ideal-quotient (isogeny) form** (reading as recorded in the repository; the primary
sources were not available on this host, UNVERIFIED).

## 3. The Lean definitions (namespace `X6ALIdeal`)

```lean
def mu (k : Fin 4) : O := ⟨(tt k : B), tt_mem k⟩                     -- 1, i, j, ij
def idealI (k : Fin 4) : Set O := {a | ∃ c : ℤ, nrd (a : B) = (N k : ℚ) * c}   -- I_m, m = |N k| = 1, 2, 3, 6
def InTors (q : QMStr A) (I : Set O) {T : Over (Spec K)} (x : T ⟶ A.X) : Prop := ∀ a ∈ I, x ≫ (q.iota a).hom = 1
def IsIdealQuotient (P : QMPair K) (I : Set O) (P' : QMPair K) (φ : AbVar.Hom P.A P'.A) : Prop :=
  (∀ a, (P.q.iota a).hom ≫ φ.hom = φ.hom ≫ (P'.q.iota a).hom) ∧                       -- ι' induced
  (∃ ψ (n : ℤ), n ≠ 0 ∧ φ.hom ≫ ψ.hom = (n : End P.A).hom ∧ ψ.hom ≫ φ.hom = (n : End P'.A).hom) ∧  -- isogeny
  (∀ T (x : T ⟶ P.A.X), x ≫ φ.hom = 1 ↔ InTors P.q I x)                                 -- ker φ = A[I]
def IsAtkinLehnerIdeal X Ψ k g : Prop :=
  ∀ x P, Ψ x = ⟦P⟧ → ∀ P' φ, IsIdealQuotient P (idealI k) P' φ → Ψ (x ≫ g.hom) = ⟦P'⟧
def ALIdealClause X Ψ : Prop := ∀ k : Fin 4, ∃ g : X ≅ X, IsAtkinLehnerIdeal X Ψ k g
def X6CoarseModuliIdeal : Prop := -- X6CoarseModuli with its Atkin–Lehner clause replaced by ALIdealClause X Ψ
def ElkiesX6StarEveryIdeal : Prop := -- ElkiesX6StarEvery with W := atkinLehnerWIdeal, on witnesses with ALIdealClause
```

**Why the printed clause is a consequence of the print, not stronger.** Rotger's `w_m` sends `[(A, ι)]` to
`[(A/A[I_m], ι_m)]`. The Lean clause quantifies over every `(A', ι', φ)` with `φ` an `𝒪`-equivariant isogeny
whose scheme-theoretic kernel is `A[I_m]`. For such `φ`, `A'` is the fppf quotient `A/ker φ = A/A[I_m]`. This
holds because a surjective homomorphism of abelian varieties is flat and is the quotient by its kernel (Mumford,
*Abelian varieties* §7 and §12; STANDARD, locators UNVERIFIED). Moreover `ι'` is the induced action because `φ` is
an epimorphism. So every such `(A', ι')` is isomorphic to the printed `(A/A[I_m], ι_m)`, and the clause is the
printed statement up to the unique isomorphism. The kernel is stated as a functor of points on all `K`-schemes
`T`, which is the definition of `A[I] = ⋂_{a ∈ I} ker ι(a)` as a subgroup scheme. The semiab-descend leaf
(Chevalley) uses the same reading of a quotient: "the target of a faithfully flat homomorphism with kernel `H`".

**`I_m` is the printed ideal.** For `p` ramified in `B` the unique two-sided prime of `𝒪` over `p` is
`{a : p ∣ nrd a}` of reduced norm `p` (Vignéras, LNM 800, II §1; Voight, *Quaternion algebras*, 13.3; UNVERIFIED
numbers). At `D = 6` the two-sided ideals of norm `2, 3, 6` are `P₂, P₃, P₂P₃`, so `I_m = {a : m ∣ nrd a}`. Lean
checks: `idealI` is closed under left and right multiplication by `𝒪` (`mul_mem_idealI_left/right`). It equals
`𝒪 μ_m` (`mem_idealI_iff`, from the chain's `two_dvd_mulCoord_ei` and `three_dvd_mulCoord_ej`); here `nrd μ_m = N k`
and `[𝒪 : 𝒪μ] = nrd(μ)²`. Counted by hand from the congruence conditions in those lemmas: index 4 for `m = 2`
(`n₀, n₂` even) and 9 for `m = 3` (`n₀ ≡ n₂`, `n₁ ≡ n₃ mod 3`), i.e. norm `m`.

## 4. The Elkies and González–Rotger steps (extension)

### 4.1 `elkiesX6StarEvery` (priority 1)

* **(b) Twist-defined `W` = Elkies' isogeny-form `w_p`: done.** `ElkiesX6StarEveryIdeal` states Elkies' clauses
  with `W = atkinLehnerWIdeal` (`w_m(A, ι) = (A/A[I_m], ι_m)`, p. 10). It implies `ElkiesX6StarEvery`, proved with
  no further published input (`elkiesX6StarEvery_of_ideal'`). On the witness built from `X6CoarseModuliIdeal` the
  two `W`'s coincide (`atkinLehnerW_eq_of_clause`). Transport to every witness is the existing
  `ElkiesPrint.every_of_functionField`, i.e. step (d), which needs T5 from `mumfordTorsionAlgClosed`. The converse
  holds given the textbook fields `gagaMorphism` and `mumfordTorsionAlgClosed` (`ideal_of_elkiesX6StarEvery`). Its docstring cites `X*(1)` with `Σ = {2, 3}` and
  the verified page numbers. The old docstring is in `ElkiesX6StarEvery.lean`, which may not be edited: integrator,
  please carry the citation of the new leaf's docstring.
* **(d) Transport to every witness: already a Lean proof** (`every_of_functionField`, elkies-print).
* **(a) `ℚ(X/W) = ℚ(X)^W`: not done, and it cannot be stated more literally today.** Mathlib v4.35 and the tree
  have no quotient of a curve by a finite group, so `X*(1) = X(1)/W` has no Lean object. A more literal leaf
  would posit a curve `X*` with `π : X → X*` that is `W`-invariant and universal among `W`-invariant morphisms,
  plus an isomorphism `X* ≅ P¹_t`. Deriving `ℚ(X)^W = π^*ℚ(X*)` from that needs three inputs. (i) Extension of a
  rational function on a smooth proper curve to a morphism to `P¹` (valuative criterion). (ii) Factorization
  through `π`. (iii) `[ℚ(X) : ℚ(X)^W] = |W| = 4`: Artin's theorem (`FixedPoints.finrank_eq_card` in Mathlib) applied
  to a *faithful* action of the four `w_m` on `ℚ(X)`. Faithfulness needs a QM pair over `ℚ̄` whose four twists by
  `Ad μ_m` are pairwise non-isomorphic, i.e. a point with trivial `W`-stabilizer, and no such existence statement is
  in the tree. Estimated cost: several days. SPECULATIVE.
  The function-field form stays a consequence: `ℚ(X/W) = ℚ(X)^W` is how the quotient's function field is defined
  (Serre, *Groupes algébriques et corps de classes* III §12; STANDARD, locator UNVERIFIED), as elkies-coord §4
  argued.
* **(c) "every point with that CM" from "the CM point of `X*(1)`": not done; the tree is two closed
  number-theoretic facts short.** The counting route the lead proposes, with GR Prop. 5.6 (bundle field
  `gonzalezRotgerProp56X6`) and Thm 5.12 (bundle field `gonzalezRotgerThm512X6`), would go as follows. At
  `(6, 1)` each of the three orders has `#CM(R) = 2^{b} h = 2`, with `(b, h) = (0, 2), (1, 1), (1, 1)` for
  `ℤ[√−6], ℤ[i], ℤ[ζ₃]`. Thm 5.12 gives `[ℚ(x) : ℚ] = 2`. So the two CM points of each discriminant are one
  `Gal(ℚ̄/ℚ)`-orbit, and since `t` is defined over `ℚ`, `t(σx) = σ(t(x))` (the chain's `val_galPt`). Hence one
  printed value `t(x₀) = 0, 1, ∞` at one CM point gives the value at every CM point of that discriminant. The
  chain already has this argument's pieces for `ℤ[i]` and `ℤ[ζ₃]`. In `LPrefix.lean`: `pic_R4`, `pic_R3`,
  `inertCount6_K4`, `inertCount6_K3`, `residue_eq_adjoin_of_R5pt`, `fibre_le_two_of_R5count`, `val_galPt`,
  `subsingleton_of_galois` (the `π₀` core of pi0-x6). Missing:
  1. the closed facts for `k = ℚ(√−6)`: `R = ℤ[√−6]` is its ring of integers (conductor 1) and
     `inertCount6 k = 0` (2 and 3 ramify). The class number itself is **not** needed: Thm 5.12 gives degree
     `2^{[b ≠ 0]} h` and Prop. 5.6 gives `#CM = 2^b h`, and these agree for `b ≤ 1`. So the Galois orbit
     (`#Hom_ℚ(ℚ(x), ℚ̄) = [ℚ(x) : ℚ]`) exhausts `CM(R)` without computing `h(−24) = 2`;
  2. "exactness": `HasCM24 P.q` (some `φ ∈ End_𝒪 A` with `φ² = −6`) ⇒ `End_𝒪 A ≅ ℤ[√−6]`, and likewise for
     `HasCM4`, `HasCM3`. The chain's `subsingleton_of_bundle` takes these as the hypotheses `hexact₄`, `hexact₃`
     for the same reason. GR56's lattice model (`com_equiv_of_eig`) is the likely route;
  3. the CM order is Galois-invariant: `End_𝒪` of a base change along `σ` (the Galois clause gives
     `IsBaseChangeOfPair σ P Q`) is isomorphic to `End_𝒪 A`, plus `#Hom_ℚ(ℚ(x), ℚ̄) = [ℚ(x):ℚ]` for the orbit count.
  Until (1) and (2) are proved, the leaf's CM clause ("every point with that CM") remains a consequence of
  Table 1 together with the uniqueness of the CM point of each discriminant on `X*(1)`. That uniqueness is
  implicit in Elkies' "the CM point of discriminant `D`" (p. 17 and Table 1, per the lead's reading).

### 4.2 `gonzalezRotgerThm512X6` (priority 2): analysed, not reduced

The leaf (`GRDict.GonzalezRotgerThm512X6`) is GR Thm 5.12 at `(6, 1)`, weakened by and-elimination, on every
witness, over `IsGRCMPoint`. The lead names two unprinted transport steps.

* **T1, the moduli dictionary `Γ∖ℍ ∋ [z] ↦ (ℂ²/Λ_z, ι)`.** `IsGRCMPoint Ψ R x` builds it into the definition: the
  pair of `x`, base-changed to `ℂ` along `σQ`, is the torus `ℂ²/ι(𝒪)(z, 1)ᵀ` with `z` the CM point of an optimal
  embedding. GR's `CM(R)` lives on `X₀(D,N)(ℂ) = Γ∖ℍ`, and GR's uniformization (Thm 5.1 per the lead) carries no
  moduli statement. The missing fact is Shimura's moduli interpretation of the complex uniformization: the point
  `[z]` of the canonical model is the moduli point of `(A_z, ι_z)` (Shimura, Ann. of Math. 78 (1963) and 85
  (1967); STANDARD, locators UNVERIFIED). **It cannot be proved as glue**, for two reasons. The tree has no Lean
  object for `Γ∖ℍ → X(ℂ)`, and `Ψ` is a bijection on `ℚ̄`-points only, not on `ℂ`-points. Removing T1 needs a new
  printed leaf (the moduli interpretation of the uniformization) stated over such an object. That is outside this
  task's reach today (SPECULATIVE).
* **T2, the Galois equivariance of `Ψ`.** The Lean statement uses the residue field `ℚ(x) = residueImage x`
  directly, so the field of moduli never enters. What is needed is that a witness's residue fields are those of
  GR's canonical model. That follows from three facts:
  1. the canonical model with its moduli map is itself a coarse witness; this is the content of `x6CoarseModuli`,
     whose Galois clause is the naturality square of §4.3;
  2. any two coarse witnesses are isomorphic over `ℚ` compatibly with `Ψ`; this is a Lean proof
     (`ElkiesPrint.coarse_compare_ab`, from T5);
  3. residue fields and `IsGRCMPoint` are invariant under such an isomorphism (`IsGRCMPoint` depends on `Ψ x`
     only).

  Items 2 and 3 are now Lean proofs. `residueImage_comp_iso` and `gr512At_of_iso` transport GR's conclusion
  (`GR512At X Ψ`) along a `Ψ`-compatible isomorphism. `gonzalezRotgerThm512X6_of_one` then gives: GR's statement
  on one witness (with `R1fpPropsAb`, `X6Props`) implies `GRDict.GonzalezRotgerThm512X6` on every witness, given
  T5. The converse is `gr512At_of_thm512`. VERIFIED, compiled. So T2 is covered by `x6CoarseModuli` together with
  proved glue. It is not an additional reading of GR.
* **Docstring correction** (`GRDict.lean` may not be edited). "`R` of conductor prime to `DN`" is not in GR (lead's
  reading: Thm 5.8 p. 16 for `ℚ(P)`, Def. 5.5 p. 14 for `CM(R)`, p. 15 for `D(R), N(R), N*(R)`, Thm 5.12
  pp. 18–19 of arXiv v2). The Lean hypothesis `Nat.Coprime (conductor R) 6` only weakens the leaf, so the
  statement is fine; only the docstring's "Published statement" should drop the clause. Proposed replacement
  for the docstring's second paragraph: "*Published statement* (arXiv math/0612732v2, Thm 5.12 pp. 18–19; the
  print's numbering unconfirmed): for `P ∈ CM(R) ⊂ X₀(D,N)` (Def. 5.5), `ℚ(P) = H_R` if `D(R)N*(R) ≠ 1`, and
  otherwise a specified subfield of `H_R` of index two. The Lean form adds the hypothesis that the conductor is
  prime to 6, which only weakens it."

Net for priority 2: no change to the leaf. T2 is not an extra risk, and T1 is a genuine extra printed input
(Shimura's moduli interpretation of `Γ∖ℍ`), which should be recorded in the row's flag.

### 4.3 The Galois clause of `x6CoarseModuli`

`GaloisClause X Ψ` (the clause verbatim) says: for `σ ∈ Aut(ℚ̄/ℚ)` and `Ψ x = [P]`, some `Q` with
`IsBaseChangeOfPair σ P Q` has `Ψ(Spec σ ≫ x) = [Q]`. `GaloisNatural X Ψ` says: for every base change `Q` of `P`
along `σ`, `Ψ(Spec σ ≫ x) = [Q]`. That is literally the naturality square of the coarse map `Φ : M → Hom(−, X)` at
the morphism `Spec σ : Spec ℚ̄ → Spec ℚ̄` over `ℚ` (Mumford, GIT Def. 5.6). Proved:
`galoisNatural_of_clause` (via the chain's `bc_uniquePair`). The converse `clause_of_galoisNatural` uses the base
change `bcAut σ P` of a QM pair along `σ` (`AbVar.baseChange` along `σ.toAlgebra`, `ι_σ = endBC ∘ ι`;
`isBaseChange_bcAut`). So `galoisClause_iff_natural` holds with no hypothesis, and the new leaf states the clause in
the literal naturality form `GaloisNatural`.

So the Galois clause adds nothing to "the canonical model over `ℚ` is a coarse moduli scheme over `ℚ`" (the
natural transformation is defined on all `ℚ`-schemes and `Spec σ` is one of their morphisms). The remaining
question is the locator of the coarse-moduli statement over `ℚ` (Deligne 1971 §§4–5; Buzzard 1997 §1; Milne,
*Introduction to Shimura varieties* §14, UNVERIFIED). That question is the leaf's own locator, not a reading risk
of the clause.

## 5. Discharges and fold

All VERIFIED, run on this host after `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`
(14273 jobs, success) and `lake build ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal`.

`#discharges` (`scratch/x6-coarse/Discharges.lean`, output `scratch/x6-coarse/discharges.txt`):

```
DISCHARGES [OpenResearchLeaves38.elkiesX6StarEvery] by X6ALIdeal.elkiesX6StarEvery_of_ideal'
  still assumes: [X6ALIdeal.ElkiesX6StarEveryIdeal,
 X6ALIdeal.X6CoarseModuliIdeal,
 RayClassCFT.ShimuraMainThmIDeligneY3AbU,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves38.x6CoarseModuli] by X6ALIdeal.x6CoarseModuli_of_ideal
  still assumes: [X6ALIdeal.X6CoarseModuliIdeal]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 39 open hypotheses, 11185 theorems checked, 52 discharge one
```

(`elkiesX6StarEvery_of_ideal`, the same with `ObjBridge.TorsionStructure` instead of `mumfordTorsionAlgClosed`, is
also listed; the run reports `11185 theorems checked`.) `#print axioms` on every theorem of the file gives the
standard three
(`scratch/x6-coarse/axioms.txt`).

**Autofold spec** `scratch/x6-coarse/autofold.json`: `x6CoarseModuli` → leaf `x6CoarseModuliIdeal` (kind
published), `elkiesX6StarEvery` → leaf `elkiesX6StarEveryIdeal` (kind consequence), proofs
`X6ALIdeal.x6CoarseModuli_of_ideal {n}.x6CoarseModuliIdeal` and
`X6ALIdeal.elkiesX6StarEvery_of_ideal' {n}.elkiesX6StarEveryIdeal {n}.x6CoarseModuliIdeal
{n}.shimuraMainThmIDeligneY3AbU {t}.mumfordTorsionAlgClosed`. Dry run:
`strict count: 16/18 on 34 -> 16/18 on 34; strictest 16/18 -> 16/18`. The new rows are flagged so they count GLUE
until a reviewer rates them (Addendum 1). The generated module (`scratch/x6-coarse/FoldDryRun.lean`:
`OpenResearchLeaves39`, `sixContactMin_of_open56`) compiles, and `#print axioms HDec.HSyn.sixContactMin_of_open56`
gives the standard three (`scratch/x6-coarse/foldcheck.txt`).

## 6. Leaf and glue table, with ratings

| statement | kind | rating (printed form or not) | reason |
|---|---|---|---|
| `X6CoarseModuliIdeal` | published (replaces `x6CoarseModuli`) | **printed form**, pending review | Each clause is the coarse-moduli theorem's own content: the moduli bijection on `ℚ̄`-points; the naturality square at `Spec σ`, literally (`GaloisNatural`); Rotger's `w_m` in his ideal-quotient form; the classifying map, a specialization of the natural transformation as before. No twist-form reading is left. The remaining flag is the locator (Shimura/Deligne/Buzzard, UNVERIFIED). If the reviewer accepts, strict count −1. |
| `ElkiesX6StarEveryIdeal` | consequence (replaces `elkiesX6StarEvery`) | **not printed form**: consequence | Its `W` is now Elkies' p. 10 isogeny form, so step (b) is gone. Steps (a) `ℚ(X/W) = ℚ(X)^W` and (c) "every point with that CM" remain (§4.1). |
| `idealI`, `InTors`, `IsIdealQuotient`, `IsAtkinLehnerIdeal`, `ALIdealClause`, `GaloisNatural`, `atkinLehnerWIdeal`, `fixedByWIdeal`, `bcAut` | definitions over genuine objects (`LeafQM.O`, `PkgI3.AbVar`, Mathlib schemes) | — | — |
| everything else in `X6AtkinLehnerIdeal.lean` | glue | proved | — |

## 7. What remains

* Reviewer: rate `X6CoarseModuliIdeal` (Atkin–Lehner and Galois reading risks removed; only the locator is left).
* Elkies (a) and (c) (§4.1): needs a quotient-curve object (a), and exactness of `HasCM*` together with the closed
  facts for `ℚ(√−6)` (c).
* González–Rotger T1 (§4.2): Shimura's moduli interpretation of `Γ∖ℍ` is a genuine extra printed input; the
  `GRDict.lean` docstring correction is in §4.2.
* Done after the first draft: the fact "every quotient by `A[I_m]` is the twist" is proved from the bundle's
  textbook fields (`iso_of_quotient_lat`), so the draft's textbook leaf `IsogenyQuotient` was dropped.

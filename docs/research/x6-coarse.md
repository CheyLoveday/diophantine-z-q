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

The new file states the printed form over genuine definitions and proves both directions (all VERIFIED, compiled,
standard axioms only):

| statement | content | hypotheses |
|---|---|---|
| `mem_idealI_iff` | `I_m := {a ∈ 𝒪 : m ∣ nrd a} = 𝒪 μ_m`, `μ_m = 1, i, j, ij` (the ideals are principal at `D = 6`) | none |
| `canonical` | `ι(μ_m) : (A, ι) → (A, ι ∘ Ad μ_m)` is a quotient of `A` by `A[I_m]` (`IsIdealQuotient`: equivariant isogeny whose kernel, as a functor of points on all `K`-schemes, is `A[I_m]`) | none |
| `alTwist_of_alIdeal` | printed clause ⇒ twist clause of `X6CoarseModuli`/`X6Props` (every `α ∈ Aut 𝒪`, via `rep_cover` and inner twists) | none |
| `x6CoarseModuli_of_ideal` | `X6CoarseModuliIdeal → GRX6AbPrint.X6CoarseModuli` | none |
| `iso_of_quotient`, `alIdeal_of_alTwist`, `x6CoarseModuliIdeal_of_twist`, `x6CoarseModuliIdeal_iff` | twist ⇒ printed: every quotient of `(A, ι)` by `A[I_m]` is isomorphic to `(A, ι ∘ Ad μ_m)` | the textbook fact `IsogenyQuotient` (an isogeny is the quotient by its kernel) |
| `atkinLehnerWIdeal_subset`, `atkinLehnerW_eq_of_clause` | Elkies' isogeny-form `W` ⊆ the twist-form `W`; equal on every witness carrying the printed clause | none (`hom_ext_qbar`: maps of proper smooth curves over `ℚ` agree if they agree on `ℚ̄`-points) |
| `atkinLehnerW_eq_of_isogenyQuotient` | the two `W`'s are equal on every witness | `IsogenyQuotient` |
| `elkiesX6StarEvery_of_ideal'` | `ElkiesX6StarEvery` from `ElkiesX6StarEveryIdeal` (Elkies with his isogeny-form `W`), `X6CoarseModuliIdeal`, `shimuraMainThmIDeligneY3AbU`, `mumfordTorsionAlgClosed` | — |
| `ideal_of_elkiesX6StarEvery` | converse | `IsogenyQuotient` |
| `galoisNatural_of_clause`, `clause_of_galoisNatural` | the Galois clause ⇔ naturality of the coarse map at `Spec σ` (Mumford GIT Def. 5.6) | converse needs a base change of `P` along `σ` |

So the leaf holds under either reading. The direction that the consumers use, printed ⇒ twist, needs nothing. The
converse needs only the textbook fact `IsogenyQuotient`, and serves only to show that the printed form is not
stronger.

(Discharge output and fold: §5.)

## 2. Which form the print uses

* **The repository's reading** (VERIFIED, read). docs/research/gt-elkies.md §3 records the reading. The docstring of
  `ElkiesX6Star.IsAtkinLehner` and that of `ElkiesCoord`'s leaf repeat it: "the moduli definition of `w_m` on
  `X₀(D,1)` is `(A, ι) ↦ (A/A[I_m], ι_m)`, `I_m` the two-sided ideal of reduced norm `m`" (Rotger 2004;
  Baba–Granath 2008 §2; locators UNVERIFIED). gt-elkies notes explicitly: "Proving it from the ideal-quotient form
  would need quotients of abelian varieties by finite subgroup schemes, which the chain does not have."
* **The lead's reading of Elkies** (task statement): p. 10, `w_p : A ↦ A/ker I_p`, the same form.
* **The twist form is not printed** (SPECULATIVE, consistent with all of the above). It is the standard
  identification when `I_m = μ_m𝒪`, and it is now proved in Lean (`canonical`, `iso_of_quotient`).

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
def IsogenyQuotient : Prop :=     -- textbook: an isogeny f (g f = [n], f g = [n]) is the quotient by its kernel over ℚ̄
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
  holds given `IsogenyQuotient` (`ideal_of_elkiesX6StarEvery`). Its docstring cites `X*(1)` with `Σ = {2, 3}` and
  the verified page numbers. The old docstring is in `ElkiesX6StarEvery.lean`, which may not be edited: integrator,
  please carry the citation of the new leaf's docstring.
* **(d) Transport to every witness: already a Lean proof** (`every_of_functionField`, elkies-print).
* **(a) `ℚ(X/W) = ℚ(X)^W`: not done.** (filled in below)
* **(c) "every CM point of discriminant `D`" from "the CM point of `X*(1)`": not done.** (filled in below)

### 4.2 `gonzalezRotgerThm512X6` (priority 2) — (filled in below)

### 4.3 The Galois clause of `x6CoarseModuli` — (filled in below)

## 5. Discharges and fold — (filled in below)

# r16-used: the field `r16CoreY` (Eichler–Shimura for `A_f`), its consumer and a printed existence form

Task r16-used, branch `wip/r16-used`, base 43513d87 (leaf-fold25 on fork main), 2026-11-15.
Lean: `ZInQKernel/Contrib/OneProof/R16Used.lean` (new) and `scratch/r16-used/` (results log `log.md`).
Nothing else under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file of this tree. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network on this
host).

## 0. Verdict

**`r16CoreY` can be replaced by a single printed-form leaf, the existence form of Diamond–Shurman Lemma 9.5.3
and Theorem 9.5.4; it cannot be removed.**

1. **Consumer and weakest form** (VERIFIED, by grep and reading): R16 is used once on the route, by
   `G0ModNewform.g13` through `commonConstituent_of_attached` (`OneProof/H/TailA.lean`). The instance is
   `ℓ = 5`, the embedding `ι = ι₅ ∘ ι_C⁻¹` (`embOf`), and the newform `f` that T24 and T25 make out of
   Pan–Berger's eigenform for `r₅`, at an arbitrary level `N`, for every `J₁(N)`. The consumer reads
   `[K_f : ℚ] < ∞`, the quotient `π : J ↠ A`, `θ`, the rank-two clause and the trace clause. It does not
   read the dimension clause or the determinant clause. That weakest form is `R16Used.R16Trace`. The
   consumer is re-proved from it in `scratch/r16-used/Bypass.lean` (§2).
2. **No bundle field implies it** (§3, an argument, SPECULATIVE only in that sense). The content is "ρ_{f,ι}
   occurs in `V_ℓ(J₁(N))`". That is Eichler–Shimura. R14/`dsThm965`, Faltings (`r9a`, `r9b`), NOS (`r7a`)
   and the Tate-module and modular-curve leaves do not place `ρ_f` inside the Tate module of the
   Jacobian.
3. **Discharge, autofold-compatible** (VERIFIED, compiled, standard axioms):

   ```lean
   theorem R16Used.r16CoreY_of_printed (h : R16Used.AfTateCharPoly)
       (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
   theorem R16Used.r16_of_afTate (h : R16Used.AfTateCharPoly) (hT : PkgI3.TateModuleFree) :
       LeafModCurves.R16_EichlerShimuraJ1'
   ```

   The new leaf `AfTateCharPoly` says the following. There are a quotient `π : J₁(N) ↠ A` over `ℚ` and
   `θ : K_f → End⁰(A)` such that, for every prime `ℓ`:
   - `V_ℓ(A)` is **free of rank 2 over `ℚ_ℓ ⊗_ℚ K_f`**, with the module structure given by `θ`;
   - for `p ∤ Nℓ`, the **characteristic polynomial over `ℚ_ℓ ⊗ K_f`** of arithmetic Frobenius is
     `X² − a_p X + χ(p) p`.

   This is how Diamond–Shurman print it, through `ρ_{A_f,ℓ} : G_ℚ → GL₂(K_f ⊗ ℚ_ℓ)`, with Shimura's
   `A_f = J₁(N)/I_f J₁(N)` replaced by an existential. The existential is needed because `A_f` has no Lean
   definition (r16-split §4). The other parts of the field's content are proved in Lean, not assumed:
   - `[K_f : ℚ] < ∞`;
   - the rank-two clause on each `ι`-component;
   - the passage to `ι`-components, with trace `ι(a_p)` and determinant `ι(χ(p))p`;
   - `dim A = [K_f : ℚ]`, which also uses the bundle's existing published leaf `mumfordTorsionAlgClosed`.

**Count.** `r16CoreY` is a composite GLUE field: Shimura 1973 Thm 1 together with DS 9.5.4. The proposed
leaf is kind `published`, flag unread (DS Lemma 9.5.3 + Thm 9.5.4 at one object, `A_f`). The fold is therefore
**−1 strict GLUE**. The autofold `--dry-run` result is in §5. It is also one literature input fewer:
Shimura 1973 Thm 1 (the dimension clause) is no longer cited, because `dim A_f = [K_f:ℚ]` is proved from the
freeness. If a statement check finds that DS 9.5.4 prints only the annihilating relation `x² − a_p x + χ(p)p
= 0` and not the characteristic polynomial, the flag becomes "pending reading" and the fold no longer changes
the count. The content is the same as today's, with three sources replaced by one.

## 1. Where `r16` / `r16CoreY` is used (VERIFIED: grep and reading)

The route reaches `r16CoreY` as follows:

1. The field is `OpenResearchLeaves22.r16CoreY`.
2. `TailZ35.lean:94` turns it into `r16` with `R16Split.r16_of_printed n.r16CoreY t.mumfordTorsionAlgClosed
   t.charPolyIndepOfEllAlgClosed`.
3. From there, `r16` is passed through the earlier generations: `r16 := n.r16` / `r.r16` in TailZ34 … TailZ4,
   TailX, TailE and TailD. `TailN.lean:117` (`eichlerShimuraJ1_ofK5`) only changes the textual copy.
4. The **only non-pass-through use** is the G0 term of `TailK.lean`: `G0AssembleMod.afterG7_of3` (TailD) →
   `newformLeaves_of3` (`TailD.lean:150`, field `G0ModNewform.NewformLeaves.r16`) →
   `modularConstituent_tail` → `g13_g16_ram` → `g13_g16` (`TailA.lean:3712`) →
   **`g13 … lv.r16 …`** (`TailA.lean:3717`) → `commonConstituent_of_attached hR16 … 5 D.ιC D.ι5 D.r5 …`
   (`TailA.lean:3404`).
5. The other occurrences are not on the route. `newformLeaves_of` (`TailA.lean:4659`) belongs to an older
   generation. `LeafModCurves.exists_J1_quotient`, `rhoF_traces`, `rhoF_attached` (Glue.lean),
   `E1Sub.rhoF_subrep_J*`, `c9`, `c9_R14` (C9.lean) and the LPrefix C9 bundle forms are kernel glue. Their
   only route-relevant pieces (`c9_core`, `E1Sub.rhoF_subrep_of_surj`) take the R16 data as arguments, and
   they are fed from `commonConstituent_of_attached`.

**Instance.**
- `ℓ = 5`.
- `emb = embOf 5 ιC ι5 (coeffField f)`, that is `ι₅ ∘ ι_C⁻¹` restricted to `K_f`.
- The newform `f` comes from `newform_of_pan`: T24 twists Pan–Berger's eigenform for `r₅`, and T25 gives the
  newform. `N` is not computed and varies with `u`.
- `J` is every `J₁(N)`, as `G13Spec` asks.

Nothing about the instance is special.

**What the consumer reads** (`commonConstituent_of_attached`, VERIFIED):
- `obtain ⟨hfin, Af, π, θ, hπ, -, hrest⟩`: the dimension clause is discarded.
- `hrest 5 emb` gives `h2` (rank two) and `hfr`, of which only `.1` (the trace) is used, through
  `(hfr p hp hpN σ hσ).1 _ rfl`.
- `hfin` is needed by `embOf`.
- `π` and `hπ` go to `jSide` (`E1Sub.vSurjOfSurjective`), and `θ`, `h2` and the traces go to `c9_core`.

The determinant clause and `dim A = [K_f:ℚ]` are never read.

## 2. The weakest form and the bypass check

```lean
def R16Used.R16Trace : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      AlgebraicGeometry.Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) =
            emb ⟨coeff f p, coeff_mem_coeffField f p⟩
```

`ℓ` and `ι` are general here for readability. The route instantiates only `ℓ = 5` and `ι = embOf`.
- `r16Trace_of_r16` and `r16Trace_of_coreY` (in the contribution) show that it is a consequence of R16 and of
  the current field.
- `scratch/r16-used/Bypass.lean` copies `commonConstituent_of_attached` and `g13` verbatim, except for the two
  lines that read R16, as `commonConstituent_of_attached_trace` and `g13_trace` (hypothesis `R16Trace`). It
  recovers the original `g13` as `g13_via_trace`.

This is not proposed as a leaf. `R16Trace` drops the determinant and dimension clauses, but neither is the
hard part: the print gives them in the same statement. A bypass fold would also have to restate the G0 term of
`TailK.lean` and would gain nothing in the count. It is recorded so that the dependence of the route on R16
is pinned down exactly.

## 3. Why no bundle field gives it (argument)

`R16Trace` at the consumer's instance asserts: for the newform `f` of level `N`, a 2-dimensional
`G_ℚ`-representation with traces `ι(a_p)` occurs, through `π`, in `V_5(J₁(N)) ⊗ ℚ̄_5`. The consumer needs it
inside `J₁(N)`, because `G16Out` asks for a common constituent of `V_5(A)` and `V_5(J₁(N)_{L'})`, and E1/E2
use that `J₁(N)`. Here is what the bundles say about `f` and `J₁(N)`:
- **R14 (`dsThm965`, DS 9.6.5)** gives an abstract `ρ_{f,λ}`. It does not say that `ρ_{f,λ}` occurs in the
  Tate module of any abelian variety, let alone `J₁(N)`.
- **Faltings (`r9a`, `r9b`)** compares `Hom(A, B)` with `Hom_G(V_ℓ A, V_ℓ B)` for two given abelian varieties.
  To produce `A_f` from `J₁(N)` it would need `ρ_f ⊂ V_ℓ(J₁(N))` as input, which is the claim itself.
- **NOS (`r7a`), de Rham (`r10`), Kato (`eigenformHTNew`), Raynaud and the CM leaves** concern `A`, local
  places or Hodge–Tate weights.
- **The modular-curve leaves** (`x1`, `dimJ1`, `jac`) give a model of `X₁(N)`, its Jacobian and its genus, but
  no Hecke action and no zeta function.

No field relates `J₁(N)` to `S₂(Γ₁(N))`. That relation is exactly the Eichler–Shimura content: the
congruence relation, or Shimura's zeta-function theorem. So the field cannot be removed (SPECULATIVE in the
sense that "no combination implies it" is an argument; each field's content was read).

## 4. The discharge (VERIFIED: compiled; `#print axioms` = `propext, Classical.choice, Quot.sound`)

### 4.1 The leaf

```lean
-- ZInQKernel/Contrib/OneProof/R16Used.lean
def tensorModule (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] (θ : F →+* A.End0) :
    Module (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ) := tModule (R16Split.rhoV ℓ A θ)  -- x ⊗ a ↦ x · V_ℓ(θ a)
def frobMat … (b : Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ)) (σ : GQ) :
    Matrix (Fin 2) (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) := Matrix.of fun i j => b.repr (A.galRep ℓ σ (b j)) i
def esPoly (a d : F) : Polynomial (ℚ_[ℓ] ⊗[ℚ] F) := X ^ 2 - C (1 ⊗ₜ a) * X + C (1 ⊗ₜ d)

def AfTateCharPoly : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      AlgebraicGeometry.Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime],
        ∃ b : (letI := tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
          ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
            ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
              (frobMat ℓ A θ b σ).charpoly =
                esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f) (c * (p : coeffField f))
```

All the objects are the kernel's or Mathlib's:
- `AbVar`, `Hom`, `V`, `galRep`, `End0` from `HDecomp/Objects.lean`;
- `IsJ1`, `IsFrobAt` (arithmetic Frobenius: `g x ≡ x^p` modulo a prime of `ℤ̄` over `p`), `coeffField`;
- `CF`, `IsNewform`, `coeff` from pkg-I4;
- Mathlib's tensor product of `ℚ`-algebras, `Module.Basis` and `Matrix.charpoly`.

The `ℚ_ℓ ⊗ K_f`-module structure is the one through which Diamond–Shurman define `ρ_{A_f,ℓ}`. `galRep_tsmul`
proves that `G_ℚ` acts `ℚ_ℓ ⊗ K_f`-linearly (from `endV_comm`), so `frobMat` is the matrix of a linear map
and its characteristic polynomial does not depend on `b`.

### 4.2 The proof of `r16_of_afTate` (glue)

1. **`liftHom`** (§1 of the file): for a ring homomorphism `ψ : F → S` into a `k`-algebra, `x ⊗ a ↦ x ψ(a)`
   is a ring homomorphism `k ⊗_ℚ F → S`. It is applied to `ρ = rhoV θ` (giving the module structure) and to
   `ι : F → ℚ̄_ℓ` (giving `ι_R`).
2. **The `ι`-eigenfunctionals of a free rank-two module** (§2, in general linear algebra):
   - an eigenfunctional `φ` (`φ ∘ ρ(a) = ι(a) φ`) is `ι_R`-semilinear (`semilin`);
   - so `φ ↦ (φ(b₀), φ(b₁))` is injective (`eval_eq`), and it is surjective with the explicit inverse
     `w ↦ Σ ι_R(b^*_i) w_i` (`coordInv`, `coordInv_mem`). Hence `E_ι ≅ Ω²` (`coordEquiv`) and
     `dim E_ι = 2`;
   - precomposition by `g` becomes `(ι_R M)ᵀ` in these coordinates, where `M` is the matrix of `g` in `b`
     (`coord_conj`). So `tr = ι_R(tr M)` and `det = ι_R(det M)` (`trace_det_of_basis`). This needs no
     linearity of `g`.
3. **Characteristic polynomial**: `trace_det_of_charpoly` reads `tr M = 1 ⊗ a_p` and `det M = 1 ⊗ χ(p)p` off
   the coefficients. `ι_R(1 ⊗ a) = ι(a)`.
4. **`[K_f : ℚ] < ∞`** (`finiteDimensional_of_basis`):
   - `r ↦ r • b₀` embeds `ℚ_2 ⊗ K_f` into `V_2(A)` as a `ℚ_2`-linear map;
   - `V_2(A)` is finite-dimensional by `TateModuleFree`;
   - so `ℚ_2 ⊗ K_f` is finite over `ℚ_2`, and `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`
     descends this to `K_f` over `ℚ`.
5. **`dim A = [K_f : ℚ]`**: `R16Split.dim_eq_of_rank_two` from the rank-two clause at `ℓ = 2`.
6. `r16CoreY_of_printed` is `R16Split.coreY_of_r16 ∘ r16_of_afTate`. For `TateModuleFree` it uses the kernel
   bridges `AvSplit.torsionStructure_of_mumford` and `T5Torsion.TateFree.tateModuleFree_of_torsionStructure`,
   both from the bundle's published leaf `mumfordTorsionAlgClosed`. Unlike `r16_of_printed`,
   `charPolyIndepOfEllAlgClosed` is **not** needed.

### 4.3 Rating of the new leaf

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `afTateCharPoly` | `R16Used.AfTateCharPoly` | **yes (existence form)**, unread | published, unread | It is Diamond–Shurman's Lemma 9.5.3 (`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`, which defines `ρ_{A_f,ℓ}`) and Theorem 9.5.4 (characteristic polynomial of `ρ_{A_f,ℓ}(Frob_𝔭)` is `x² − a_p x + χ(p)p` for `p ∤ ℓN`), at the abelian variety of their Definition 6.6.3. All numbers are UNVERIFIED, recalled from memory with no network. The only repackaging is that `A_f` (with its `K_f`-action and its surjection from `J₁(N)`) is replaced by an existential, as the published leaf `dsThm965` does for `ρ_{f,λ}`. `A_f` has no Lean definition: there are no Hecke correspondences on `X₁(N)` and no `S₂ ≅ H⁰(Ω¹)` comparison. It is **not stronger** than the print. It covers newforms only (the print covers normalized eigenforms), and it drops the unramifiedness clause. The witness `A_f` satisfies every clause. `χ(p) ∈ K_f` holds because `χ(p)p = a_p² − a_{p²}` (STANDARD); the print states the polynomial over `K_f ⊗ ℚ_ℓ`. The remaining convention steps are those of r16's docstring: (a) the print is for Shimura's model of `X₁(N)`, and the statement quantifies over every `IsJ1` Jacobian, which are `ℚ`-isomorphic (leaf MC9 of bp-modcurves); (b) a convention that gives `ā_p` is absorbed by `θ ↦ θ ∘ c`, which the existential allows. |

**What a statement check must confirm** (pages wanted):
1. DS Lemma 9.5.3 states freeness of rank 2 over `K_f ⊗ ℚ_ℓ`, for all primes `ℓ`.
2. DS Theorem 9.5.4 states the **characteristic polynomial**, over `K_f ⊗ ℚ_ℓ`, of `ρ_{A_f,ℓ}(Frob_𝔭)` with
   arithmetic Frobenius, and not only an annihilating polynomial.
3. DS's `A_f` and its `K_f`-action are defined over `ℚ`, as a quotient of `J₁(N)`. This is used in §9.5;
   DS §6.6 works over `ℂ`.

If item 2 fails, use Shimura 1971 Thm 7.11 / Ribet 1977 for the characteristic polynomial (UNVERIFIED), or
flag the leaf "pending reading".

Proposed `locators.md` row (not added, since it is another task's file):
`R16 (existence form, r16-used) | Diamond–Shurman GTM 228 (2005) Def. 6.6.3, Lemma 9.5.3, Thm 9.5.4;
Shimura 1971 §7.5 (Thms 7.9–7.14) | — | UNVERIFIED | V_ℓ(A_f) free of rank 2 over K_f⊗ℚ_ℓ and char.
poly. of Frob_p over K_f⊗ℚ_ℓ; check it is the characteristic polynomial, not only the congruence relation`.

## 5. Compile status, `#discharges` and the fold check

All runs on this host, 2026-11-15, one Lean process at a time (VERIFIED).

| what | command | outcome |
| --- | --- | --- |
| contribution | `lake env lean ZInQKernel/Contrib/OneProof/R16Used.lean` | no errors, no warnings |
| build | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.R16Used` | success, 12995 jobs, 9 min (partial rebuild; `scratch/r16-used/build-output.txt`) |
| discharge check | `lake env lean scratch/r16-used/Discharges.lean` | see below (`Discharges-output.txt`) |
| bypass | `lake env lean scratch/r16-used/Bypass.lean` | `HDec.G0ModNewform.g13_trace`, `g13_via_trace`: `[propext, Classical.choice, Quot.sound]` |
| fold | `python3 scripts/one_proof/autofold.py scratch/r16-used/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/r16-used/FoldDryRun.lean` | `strict count: 46/10 on 56 -> 47/9 on 56; strictest 45/11 -> 46/10`; `HDec.HSyn.sixContactMin_of_open30` has standard axioms |

`#discharges` (the entry for this contribution; the others are the already-folded contributions and
r16-split's converse `coreY_of_r16`):

```
DISCHARGES [OpenResearchLeaves22.r16CoreY] by R16Used.r16CoreY_of_printed
  still assumes: [R16Used.AfTateCharPoly, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1865 theorems checked, 8 discharge one
```

`mumfordTorsionAlgClosed` is already a published LEAF field of `OpenTextbookLeaves11`, so the only new
hypothesis is `AfTateCharPoly`. The fold was not applied: `Main.lean`, `kinds.tsv` and `claims.tsv` are
unchanged, because folding is the integrator's step. The autofold count (LEAF/GLUE) drops by one GLUE in both the strict and
the strictest columns.

## 6. Files

- `ZInQKernel/Contrib/OneProof/R16Used.lean`: the contribution. It imports only
  `ZInQKernel.Contrib.OneProof.R16Split` (not `OneProof.Main`), and has no build-time code.
- `scratch/r16-used/Used.lean`: the same mathematics as a scratch file, with `#print axioms`.
- `scratch/r16-used/Bypass.lean`: the consumer `g13` re-proved from the weakest form `R16Trace`.
- `scratch/r16-used/Discharges.lean`: the `#discharges` check; its output is in `Discharges-output.txt`.
- `scratch/r16-used/autofold.json`: the fold spec (field `r16CoreY`, leaf `afTateCharPoly`, kind published).
- `scratch/r16-used/FoldDryRun.lean`: the autofold `--dry-run` module.
- `scratch/r16-used/log.md`: the results log.

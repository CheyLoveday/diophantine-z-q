# nv-local: `NVLocalInertia` reduced to the local geometry of one branch (`BranchRegular`)

Task nv-local, 2026-11-15/16. Base `56478c75` (sgr-direct on main `43513d87`).

- **Lean** (new): `ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean`, namespace `SGRDirect.NVLocal`, importing
  `ZInQKernel.Contrib.OneProof.SGRDirectElkies` (which imports `SGRDirectNV`, where `NVLocalInertia` is declared).
- **Scratch** (`scratch/nv-local/`): `log.md`; `NVLocal.lean` (a copy of the Contrib file); `Core-first.lean` (the first compiled version, whose `BranchRegular` still had an existence clause);
  `Discharges.lean` with `Discharges-output.txt`; `autofold.json`.
- **Marks:** **VERIFIED** (compiled, read, or computed), **STANDARD** (published; locators from memory are
  **UNVERIFIED**, there is no network), **SPECULATIVE**.

## 0. Verdict

**`NVLocalInertia` is not proved outright. It is proved from one strictly smaller GLUE Prop, `BranchRegular`**
(VERIFIED: `lake build`, standard axioms):

```lean
theorem SGRDirect.NVLocal.nvLocalInertia_of_branchRegular (h : BranchRegular) : SGRDirect.NVLocalInertia

theorem SGRDirect.NVLocal.heckeVertWitness_of_branchRegular (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hBR : BranchRegular) (hEl : QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted) :
    HDec.HeckeRestNV.HeckeVertWitness
```

- `NVLocalInertia` is **true as stated** (STANDARD; §2.3). No statement was changed.
- `BranchRegular` keeps only the geometry of h-b1's step 3. Over a closed point `𝔓` of the normalization above
  `(p, X − b)`:
  - exactly one branch of `X = b` passes through `𝔓`;
  - that branch is normal at `𝔓`.
- `BranchRegular` has no Galois action, no residue-field arithmetic and no hypothesis on the residue fields.
- **Everything else in Lemma NV step 3 is now compiled.** That covers:
  - the inertia comparison;
  - the residue fields of the branch;
  - the unramified-number-field argument.
- **Rating of the new leaf `BranchRegular`: not printed form; GLUE (project, local commutative algebra).** It is
  a consequence of Abhyankar's lemma (SGA 1 XIII 5.2–5.3) and Zariski–Nagata purity (SGA 1 X 3.1); both locators
  are UNVERIFIED. No published statement has this form (§2.2).
- **Counts.** `BranchRegular` replaces `NVLocalInertia` one for one in sgr-direct's bypass fold. So that fold
  still goes **−1 GLUE**: `shimuraIntegralModelRep` and `quotientP1Coordinate` out, `branchRegular` in. The
  **−2 GLUE** target (both fields out with nothing in) needs `BranchRegular` proved. §4 gives the route and why it
  was out of reach by the deadline.

## 1. What compiles (VERIFIED)

The file `ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean` (about 580 lines) contains:

| declaration | content |
|---|---|
| `eq_one_of_inertia_of_unram` | `K` a number field, `P` a prime of `𝓞 K` with `P.ramificationIdx ℤ = 1`, and `σ ∈ Aut(K/ℚ)` with `σx − x ∈ P` for all `x ∈ 𝓞 K`. Then `σ = 1`. |
| `primeOf`, `primeOf_isPrime`, `mem_primeOf_of_mem` | for `ψ : C → L` with `ker ψ ⊆ 𝔓` and `𝓞 L` inside the localization `{ψ c₁ / ψ c₂ : c₂ ∉ 𝔓}`: the prime `{y : y·ψ(d₂) = ψ(d₁), d₁ ∈ 𝔓, d₂ ∉ 𝔓}` of `𝓞 L`, which contains `p` when `p ∈ 𝔓` |
| `inertia_primeOf`, `eq_one_of_primeOf` | an automorphism `σ` of `L` with `σ(ψ c) = ψ(c')` and `c' ≡ c mod 𝔓` lies in the inertia of `primeOf`; if that prime is unramified then `σ = 1` |
| `zqIncl`, `galB`, `galC_mem` | the inclusion of the `ℤ[X]`-closure in the `ℚ[X]`-closure, and the Galois action on both |
| `exists_int_mul_mem` | every element of the `ℚ[X]`-closure has a nonzero integer multiple in the `ℤ[X]`-closure (Mathlib's `IsIntegral.exists_multiple_integral_of_isLocalization`) |
| `exists_branch` | through every maximal `𝔓 ⊂ C` over `(p, dX − a)` passes a branch: a prime `Q` of `B` over `X − b` with `Q ∩ C ⊆ 𝔓` (going down for `C/ℤ[X]`, then `Q = {y : ky ∈ Q_C for some integer k ≠ 0}`) |
| `BranchRegular` | the new GLUE Prop (§2) |
| `nvLocalInertia_of_branchRegular` | `BranchRegular → NVLocalInertia` |
| `heckeVertWitness_of_branchRegular` | `HeckeVertWitness` from the bundle fields of `heckeVertWitness_of_nvElkies` and `BranchRegular` |

**Checks.**
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` succeeds (12 s on the copied build tree).
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for the seven main theorems.
  - The commands are in `scratch/nv-local/Discharges.lean`; the output is in `Discharges-output.txt`.
- `#discharges` reports "63 open hypotheses, 1906 theorems checked, 7 discharge one".
  - None of the seven is from this file, as expected: `HeckeVertWitness` and `NVLocalInertia` are not open
    fields of the current bundles.
  - The seven are the same as in sgr-direct's run.
- The file has no code that runs at build time. Its only options are `set_option maxHeartbeats 1600000 in` on the
  main theorem and the `haveI` linter switch.

**The proof of `nvLocalInertia_of_branchRegular`** (`g = 1` in the conclusion):
1. **A closed point.** Let `q` be a vertical prime of `C` and `τ ∈ InertiaZ E q`.
   - `exists_secIdeal` gives the maximal ideal `m = (p, dX − a)` of `ℤ[X]`, where `b = a/d`.
   - `vertPrime p ⊆ m`, so going up (`Ideal.exists_ideal_over_prime_of_isIntegral`) gives a maximal `𝔓 ⊇ q`
     over `m`.
2. **The branch.** `exists_branch` gives a prime `Q` of `B` over `X − b` with `Q ∩ C ⊆ 𝔓`. `BranchRegular` says it
   is the only one and is normal at `𝔓`.
3. **`τQ = Q`.** The prime `τQ` lies over `X − b`. It also has `τQ ∩ C ⊆ 𝔓`:
   - if `c ∈ τQ ∩ C` then `τ⁻¹c ∈ Q ∩ C ⊆ 𝔓`;
   - and `c − τ⁻¹c = τ(τ⁻¹c) − τ⁻¹c ∈ q ⊆ 𝔓`.

   By uniqueness `τQ = Q`, so `τ` induces `σ_κ` on `κ = B/Q`.
4. **The residue field.** `Q` is maximal, `κ` is algebraic over `ℚ`, and `IsAlgClosed.lift` gives `φ : κ → ℚ̄`.
   - Let `L = ℚ(φ(κ))`. It is finite over ℚ (`PropTSGlue.finiteDimensional_residue`) and unramified at `p` (the
     hypothesis of `NVLocalInertia`).
   - Transport `σ_κ` to `σ ∈ Aut(L/ℚ)` along `e : κ ≃ L`, and set `ψ := e ∘ mk_Q ∘ zqIncl : C → L`.
5. **Inertia.** The normality clause of `BranchRegular` says `𝓞 L ⊆ {ψ c₁ / ψ c₂ : c₂ ∉ 𝔓}`.
   - `τ ≡ id mod q ⊆ 𝔓`, so `σ` lies in the inertia of `primeOf` (`inertia_primeOf`).
   - That prime contains `p` and is unramified, so `σ = 1` (`eq_one_of_primeOf`).
6. **Conclusion.** `σ = 1` means `τy − y ∈ Q` for all `y ∈ B`, i.e. `τ ∈ InertiaQ E Q`.

`eq_one_of_inertia_of_unram` works over the fixed field `K₀` of `⟨σ⟩`:
- `IsGaloisGroup ⟨σ⟩ (𝓞 K₀) (𝓞 K)` holds (`IsGaloisGroup.fixedPoints`, `of_isFractionRing`).
- `|I(P | P₀)| = e(P | P₀)` (`Ideal.card_inertia_eq_ramificationIdxIn`).
- The tower gives `e(P | ℤ) = e(P₀ | ℤ) · e(P | P₀)` (`Ideal.ramificationIdx_tower`), and the left side is 1.

## 2. `BranchRegular`

### 2.1 Statement

The hypotheses are those of `NVLocalInertia` minus the residue-field hypothesis:
- `E/ℚ(X)` finite Galois of degree `< p`;
- `BranchData E S n nInf`;
- the points of `S` are `p`-integral and pairwise distinct mod `p`;
- `b ∈ S`.

Notation:
- `C` and `B` are the integral closures of `ℤ[X]` and `ℚ[X]` in `E`;
- `𝔓` is a maximal ideal of `C` with `p, dX − a ∈ 𝔓`, where `b = a/d`.

Let `Q` be any prime of `B` over `X − b` with `Q ∩ C ⊆ 𝔓`. One exists: this is `exists_branch`, which is
compiled. Then:
- **(UB)** every prime `Q'` of `B` over `X − b` with `Q' ∩ C ⊆ 𝔓` equals `Q`;
- **(N)** every `z ∈ B/Q` integral over `ℤ` is `c₁/c₂` for some `c₁, c₂ ∈ C` with `c₂ ∉ 𝔓`.
  - In other words, the local ring of the branch `C/(Q ∩ C)` at `𝔓` contains the ring of integers of the number
    field `B/Q`.
  - Its fraction field is `B/Q`, so (N) says that this local ring is normal (a DVR).

The Prop is exactly the geometric content of h-b1's step 3: uniqueness and normality of the branch. Its
existence is proved. Earlier, in `scratch/nv-local/Core-first.lean`, it was a clause of the Prop.

### 2.2 Rating

**Not printed form; GLUE.**
- It is the geometric half of h-b1 §3 step 3. That step assumes strict henselization and says, in effect,
  "unique branch through `𝔓`, residue degree 1 on it". rv-h-b1 found that step "holds as stated".
- The published statements behind it are about tame covers étale-locally:
  - Abhyankar's lemma (SGA 1 XIII 5.2): after extracting `n`-th roots of a normal-crossings divisor, a tame
    cover becomes étale;
  - the tame local fundamental group of `Spec A^{sh} ∖ D` is `Ẑ'(1)^r` (SGA 1 XIII 5.3; Grothendieck–Murre,
    LNM 208).

  Locators UNVERIFIED.
- Neither published statement is the Zariski-local statement about one branch over `ℤ[X]` used here. So it is
  not proposed as a LEAF.

### 2.3 Why it is true (paper proof; SPECULATIVE until compiled)

Notation: `R = ℤ[X]_m`, `S` the integral closure of `R` in `E` (the localization of `C`), `G = Gal(E/ℚ(X))`,
`n = |G| < p`.

1. **Only two divisors ramify near `m`.** The height-one primes of `R` are `(p)`, `(X − b)`, and `(f)` for other
   irreducible horizontal `f ∈ m`.
   - At `(f)`, `E` is unramified. By `BranchData`, ramified horizontal primes lie over `X − b'` with `b' ∈ S`.
     If `b' ≠ b`, then `X − b' ∈ m` would force `b' ≡ b mod p`, which distinctness excludes.
   - This is the argument of the chain's `SNHorizontalTransfer` and `NonMeeting` pieces.
   - Ramification at `(p)` and at `(X − b)` is tame: inertia orders divide `n < p`, and residue extensions of
     degree `< p` are separable.
2. **The Kummer base change.** Let `N = n` and `ζ = ζ_N`.
   - Let `O = ℤ_(p)[ζ][w]/(w^N − p)`, localized at a prime above `p`. It is a DVR with uniformizer `w`.
   - Let `A' = O[r]_{(w, r)}`, mapped from `R` by `X ↦ b + r^N`. It is a regular local ring of dimension 2.
   - Let `Ω = E(ζ, w, r)`, inside an algebraic closure of `ℚ(X)`. It is Galois over `ℚ(X)`.
   - `Γ = Gal(Ω/E)` has order dividing `φ(N)N²`, which is prime to `p`.
3. **Unramified in codimension 1.** Let `S'` be the integral closure of `A'` in `Ω`. It is finite and normal. Its
   height-one primes `P` are of three kinds:
   - `P = (w)`, over `(p)`. By the kernel's T2 (`PkgI2.AbhyankarDVR`, proved: `t2_proved`), applied to
     `ℤ[ζ][X][r]_{(p)}` with `π = p` and `M = L(w)`, every prime of `S'` over `P` has `e = N` over that DVR. Since
     `e(P | p) = N`, the tower gives `e(Q' | P) = 1`, and the residue extensions are separable.
   - `P = (r)`, over `(X − b)`: the same argument in characteristic 0.
   - Any other `P` lies over some `(f)` from step 1. There `E` and `ℚ(ζ, w, r)` are both unramified, so their
     compositum `Ω` is unramified.
     - In terms of inertia groups: the inertia group of `Ω/ℚ(X)` restricts trivially to both fields, and `Ω` is
       generated by them.
4. **Purity.** `PropTSGlue.purityGlobalDim2` (proved) shows that `S'` is étale over `A'`.
5. **Specialization.** `S'/rS'` is étale over the DVR `A'/r = O`. So it is normal, and its local rings at the
   maximal ideals `𝔐` are DVRs. Hence:
   - (UB') exactly one prime `Q'` of `S'` over `(r)` (equivalently over `(X − b)`) lies in `𝔐`;
   - (N') `(S'/Q')_𝔐` is a DVR.
6. **Descent to `E`.**
   - **(UB).** Let `Q₁, Q₂ ⊆ 𝔓` lie over `X − b`, and pick `𝔐` over `𝔓`. Going down for `S ⊆ S'` gives
     `Q'ᵢ ⊆ 𝔐` over `Qᵢ`. These lie over `(r)`, so `Q'₁ = Q'₂` by (UB'), hence `Q₁ = Q₂`.
   - **(N).** Let `Q'` lie over `Q` and let `D = Stab_Γ(Q')`. The ideals `γQ'`, for `γ ∈ Γ/D`, are pairwise
     comaximal after localizing at `𝔓`: by (UB'), no `𝔐` contains two of them. So by CRT,
     `(S'/I)_𝔓 ≅ ∏_{Γ/D} (S'/γQ')_𝔓`, where `I = ∩ γQ'`.
   - `|Γ|` is invertible, so the Reynolds operator gives
     `(S/Q)_𝔓 = ((S'/I)_𝔓)^Γ ≅ ((S'/Q')_𝔓)^D =: T^D`. Here `T` is the semilocalization of `S'/Q'` at `𝔓`, which
     is normal by (N').
   - An element `z ∈ B/Q` integral over `ℤ` lies in `T` (normal, containing `ℤ`). It is also `D`-invariant,
     because `κ(Q')^D = κ(Q)` (char 0). Hence `z ∈ T^D = (S/Q)_𝔓`. ∎

**Test cases** (by hand; `p` a large prime):

| cover | (UB) | (N) |
|---|---|---|
| `ℚ(X)(√(p(X − b)))`, `S = R[z]`, `z² = p(X − b)` | `S/(X − b) = ℤ_(p)[z]/(z²)` has one minimal prime | `S/Q = ℤ_(p)`: holds |
| `ℚ(√(pu))(X)`, `u` a `p`-adic unit (vertical ramification only) | `S/(X − b) = ℤ_(p)[√(pu)]`, a domain | it is a DVR (Eisenstein): holds |
| `ℚ(X)(√(X − b + p²))` (branch point `b − p² ≡ b`, so distinctness fails) | `S/(X − b) = ℤ_(p)[y]/(y² − p²)` has two branches `y = ±p` through one closed point | **(UB) fails**, so the distinctness hypothesis is needed |

## 3. Relation to sgr-direct and to the fold

- sgr-direct's composite `heckeVertWitness_of_nvElkies` needed one open Prop, `NVLocalInertia`.
  `heckeVertWitness_of_branchRegular` needs `BranchRegular` instead. The other inputs are the same bundle fields:
  `r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints`, `elkiesX6StarPrinted`.
- **Fold.** As in sgr-direct §5, no fold was executed; `scratch/nv-local/autofold.json` records the plan.
  - `HeckeVertWitness` is not a top-level field. The fold is a bypass at generation 5: regenerate the bundles
    without `shimuraIntegralModelRep` and `quotientP1Coordinate`, with the new field
    `branchRegular : SGRDirect.NVLocal.BranchRegular`.
  - In `glue4_of_open5`, use
    `heckeVertWitness := SGRDirect.NVLocal.heckeVertWitness_of_branchRegular … n.branchRegular r.elkiesX6StarPrinted`.
  - Strict count 56 → 55 (GLUE −1), the same as sgr-direct's plan.
- **Leaf table.**

| new leaf | kind | flag | strict | printed form? |
|---|---|---|---|---|
| `branchRegular : SGRDirect.NVLocal.BranchRegular` | project glue | — | GLUE | no: a Zariski-local consequence of Abhyankar's lemma and purity; no published statement of this form (§2.2) |

## 4. Why `NVLocalInertia` was not proved outright, and what a proof of `BranchRegular` needs

- Every route to the local structure at `𝔓` has to remove the vertical ramification. That requires extracting a
  root of `p`, a constant extension ramified at `p`, so the base leaves `ℤ[X]`.
  - The route of §2.3, h-b1's route, and the report's variant (sgr-direct §6) all do this.
  - The chain's specialization machinery is written over `ℤ[X]`, `ℚ[X]` and `ℚ(X)`, and none of it applies to
    the new base `O[r]`: `SpecNonMeeting`, `snSpecializeUnram`, the height and regularity lemmas for `ℤ[X]_m`, the
    horizontal transfer, and `KummerCompositum`.
  - Purity (`purityGlobalDim2`) and T2 (`AbhyankarDVR`) are stated for general rings and would be reused.
- **What remains to compile for `BranchRegular`**, in the order of §2.3:
  1. `O = ℤ_(p)[ζ_N, p^{1/N}]` as a DVR, with `p ∤ N` unramified in `ℤ[ζ_N]`.
  2. `A' = O[r]_{(w, r)}`: regular local of dimension 2, with fraction field `ℚ(ζ, w)(r)`.
     - Mathlib's instance that gives `IsRegularLocalRing` for localizations of `ℤ[X]` (used by
       `regular_dim2_intPoly`) may extend.
  3. `Ω` as a splitting field over `ℚ(X)` of `f_E·(T^N − (X − b))·(T^N − p)`, with `E ↪ Ω` and `Gal(Ω/E)` tame.
  4. The integral closure `S'` of `A'` in `Ω`, finite and normal (as in `snLocalData`).
  5. Unramifiedness at every height-one prime of `A'`: T2 twice, plus base change of unramified primes.
  6. Purity: `S'` is étale over `A'`.
  7. Étale over the DVR `O` implies normal; hence (UB') and (N').
  8. Descent: going down for (UB); Reynolds operator plus CRT for (N).
- Estimated at several thousand lines of Lean. That was beyond the deadline, so the arithmetic and Galois half was
  compiled instead and the geometric half isolated.

## 5. What remains

1. **`BranchRegular`** (GLUE): a self-contained commutative-algebra target; route in §2.3 and §4.
2. **The deep fold** (sgr-direct §5), with `branchRegular` in place of `nvLocalInertia`.

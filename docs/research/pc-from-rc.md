# pc-from-rc: Theorem 5.2 from Theorem 5.3 (fork issue #83)

Task pc-from-rc, 2026-11-17, base `19fdd483`. Lean 4.35.0, Mathlib v4.35.0.
Sources: `diophantine_zq.tex` Section 5 (lines 973–1121), read for this task.

## Main result

**Proved in Lean** (no `sorry`; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound` for each theorem below):

```
ZInQ.Manuscript.PoleRC.poleCompleteness_of_crm :
  CRM → SimultaneousConstruction → Manuscript.PoleCompleteness

ZInQ.Manuscript.PoleRC.crm_of_restrictedConverse (P) :
  RestrictedConverse P → Lemma54At P → KolyvaginRankOne → MordellWeil → DescentGlueM → CRM

ZInQ.Manuscript.PoleRC.simultaneousConstruction_of :
  MatrixRealization → DimThreeCount → SimultaneousConstruction

ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse (P) :
  RestrictedConverse P → Lemma54At P → KolyvaginRankOne → MordellWeil →
  DescentGlueM → MatrixRealization → DimThreeCount → Manuscript.PoleCompleteness
```

`Manuscript.PoleCompleteness` (Theorem 5.2, `hyp:PC`) and `Manuscript.RestrictedConverse`
(Theorem 5.3, `hyp:RC`) are the unchanged statements of `ZInQKernel/Hypotheses/PoleManuscript.lean`.

So Theorem 5.2 follows in Lean from Theorem 5.3 together with: one interface hypothesis on the
abstract Selmer predicate (`Lemma54At`, Lemma 5.4), two published leaves (`KolyvaginRankOne`:
BCDT Theorem A with Kolyvagin Theorem 1; `MordellWeil`), and three GLUE statements that are not
proved in Lean (`DescentGlueM`, `DimThreeCount`, `MatrixRealization`). All three GLUE statements
were tested numerically and no counterexample was found (section 5).

The Lean proofs cover the squareclass bookkeeping (lines 1020–1032) and the rescaling to the eleven
witnesses (lines 1107–1121) completely, with no hypotheses. The simultaneous construction
(lines 1033–1060) and the dimension-three count (lines 1061–1074) are stated precisely as the
named GLUE Props `MatrixRealization` and `DimThreeCount`, but not proved.

## 0. Known issues with the cited sources and the text

1. **S11–S12.** The manuscript credits the simultaneous construction of `n` and `nθ` to its
   supplementary files S11–S12 (lines 1033–1035). As instructed, they were not used.
   `MatrixRealization` is the explicit content of lines 1036–1060 and is labelled ELLIOT.
2. **The shape of a Selmer representative (line 1062) is asserted, not derived.** The text says a
   class with positive second coordinate is `(3^δ ∏ q_i^{u_i}, ∏ q_i^{v_i})`, with no factor `2`
   and positive first coordinate. This follows from the local images at the real place
   (`a > 0`) and at `2`. For `ℓ ≡ 3 (mod 4)` the image at `2` is exactly
   `{a, b odd, b ≡ 1 (mod 4)}`, which I computed (VERIFIED by sampling, `local2.py`); the text does
   not state it. ELLIOT.
3. **"The matrix properties force v = 0, δ = 0, u ∈ ker K" (line 1068) needs more than the
   printed properties.** The proof (ON THE SPOT, by hand, not in Lean) also uses three identities
   that come from quadratic reciprocity, none of them in the text:
   `Kᵗ = K + ssᵗ + diag(s)` (from `[q_i/q_j] = [q_j/q_i] + s_i s_j`);
   `sᵗ1 = 1` (`ℓ ≡ 3 (mod 4)`); and `λᵗ1 = 0` (`(3/ℓ) = 1` for `ℓ ≡ 11 (mod 12)`).
   It also uses rank–nullity: the left kernel of `K` has dimension 2, it contains `1`, and
   `λ ∉ im K` means `λᵗw = 1` for the other generator `w`.
   With these, the case `sᵗv = 0` gives `Kᵗv = 0`, so `v ∈ {0, 1, w, w + 1}`, and
   `(λ + s)ᵗv = 0` leaves only `v = 0`. The case `sᵗv = 1` would give `Kᵗv = s`, but
   `s ∉ im Kᵗ = (ker K)^⊥` because `sᵗ1 = 1`. The full system also contains the 2-adic equation
   `sᵗv = σ` and allows a negative second coordinate (`σ = 1`); the substitution `v ↦ v + 1`,
   `δ ↦ δ + 1` reduces that case to `σ = 0`. Result: exactly the 8 classes
   `{1, ℓ, β, ℓ/β} × {(1, 1), (3, −ℓ)}`. ELLIOT for the missing identities.
4. **The Boolean assignment (lines 1055–1058) is a sketch.** "Free `q₀`-symbols toggle the new
   diagonal entries; the determinant's full-product coefficient is one" reads as follows: the
   determinant is a multilinear polynomial over `𝔽₂` in the free symbols, and its top coefficient
   is the (nonsingular) `n`-block determinant. A nonzero multilinear polynomial has a nonzero value,
   so the `nθ`-block can be made nonsingular while the `n`-block conditions, which do not involve
   these symbols, stay as they are. That is how I read it (SPECULATIVE); the link from this
   bordered matrix to `ker K = ⟨1, 1_β⟩` and `λ ∉ im K` is not spelled out. ELLIOT.
5. **Lemma 5.5 citations.** Kolyvagin is cited as the MPIM preprint MPI/90-69 (1990), "On the
   Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves". A paper with
   that title is in the Proceedings of the ICM 1990 (Kyoto); this is from memory, UNVERIFIED.
   BCDT is cited as the author manuscript; the refereed version is J. Amer. Math. Soc. 14 (2001)
   843–939 (STANDARD). Neither was read for this task, and the theorem numbers are as the manuscript
   gives them (UNVERIFIED).
6. **Lemma 5.4** is a manuscript lemma with a proof (Kummer sequence plus the Cassels–Tate pairing,
   Poonen–Stoll, Ann. of Math. 150 (1999)). With `SelmerCorankOne` abstract it can only enter as an
   interface hypothesis (`Lemma54At`). It holds for the genuine predicate only once `SelM` is
   identified with `Sel₂(E_ℓ/ℚ)` (Silverman X.1.4) and `P` with the corank statement.

No statement was found false. The target statements were not changed.

## 1. Files

| file | content | status |
| --- | --- | --- |
| `ZInQKernel/Contrib/PoleRC/Defs.lean` | `LocM`, `SelM`, `CRM`, `SimultaneousConstruction` | definitions |
| `ZInQKernel/Contrib/PoleRC/Rescale.lean` | `point_of_locM`, `polePoly_eq_zero_of`, `witnesses_of_points` | proved |
| `ZInQKernel/Contrib/PoleRC/Bookkeeping.lean` | `bookkeeping` (lines 1020–1032) | proved |
| `ZInQKernel/Contrib/PoleRC/Reduction.lean` | `poleCompleteness_of_crm` | proved |
| `ZInQKernel/Contrib/PoleRC/CRM.lean` | `Lemma54At`, `KolyvaginRankOne`, `MordellWeil`, `DescentGlueM`, `crm_of_restrictedConverse` | proved from the hypotheses |
| `ZInQKernel/Contrib/PoleRC/Matrix.lean` | `lsym`, `Kmat`, `lam`, `sgn`, `oneB`, `MatrixConditions`, `DimThreeCount`, `MatrixRealization`, `simultaneousConstruction_of` | proved from the hypotheses |
| `ZInQKernel/Contrib/OneProof/PoleCompletenessFromRC.lean` | `poleCompleteness_of_restrictedConverse` | proved from the hypotheses |
| `scratch/pc-from-rc/*.py` | numerical checks | section 5 |

Every file imports only `ZInQKernel.Hypotheses.PoleManuscript` (and through it `Pole.lean` and
Mathlib) and the other PoleRC files. None imports `ZInQKernel.OneProof.Main`.

## 2. The statements

`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` (`Manuscript.curve`). Kummer coordinates `(x + 3ℓ, x − ℓ)`
(line 1061).

* `LocM K ℓ a b`: the class `(a, b)` lies in the Kummer image of `E_ℓ(K)`, in x-form: `a, b` are
  squares, or some `x` makes `(x + 3ℓ)/a`, `(x − ℓ)/b` and `x/(ab)` squares. The three 2-torsion
  points give `(ℓ, 1)`, `(3, −ℓ)`, `(3ℓ, −ℓ)`. Analogue of `RouteK.Selmer.Loc`.
* `SelM ℓ`: pairs of squarefree integers in the local image over `ℝ` and every `ℚ_p`. This is the
  explicit `Sel₂(E_ℓ/ℚ)`; dimension 3 is `ncard = 8`. Analogue of `RouteK.Selmer.Sel2`.
* **`CRM`** (first deliverable): for positive squarefree `ℓ ≡ 11 (mod 12)`, `#SelM ℓ = 8` and
  `(β, 1) ∈ SelM ℓ` imply `LocM ℚ ℓ β 1` (a rational point in the class `(β, 1)`).
* `SimultaneousConstruction`: for `β, θ` positive squarefree with `β ≡ 17`, `θ ≡ 1 (mod 24)`,
  coprime and mutually local squares, there is `n > 0`, `n ≡ 11 (mod 12)`, `nθ` squarefree, with
  `#SelM n = #SelM nθ = 8`, both containing `(β, 1)`.
* `MatrixConditions ℓ β`: with `[a/q]` the additive Legendre symbol, `s_i = [−1/q_i]`,
  `λ_i = [3/q_i]`, `(Kv)_i = Σ_{j≠i}[q_j/q_i](v_j + v_i)` over the primes `q_i` of `ℓ`:
  `1_β ∉ {0, 1}`, `K1_β = 0`, every `v` with `Kv = 0` is in `{0, 1, 1_β, 1 + 1_β}`, and `λ ∉ im K`.
* `DimThreeCount`: positive squarefree `ℓ ≡ 11 (mod 12)`, `β ∣ ℓ`, `β ≡ 1 (mod 8)`,
  `MatrixConditions ℓ β` give `#SelM ℓ = 8` and `(β, 1) ∈ SelM ℓ`.
* `MatrixRealization`: for `β, θ` as above, there is `n` with `β ∣ n` and `MatrixConditions` for
  both `n` and `nθ`.
* `Lemma54At P`, `KolyvaginRankOne`, `MordellWeil`, `DescentGlueM`: see section 3.

## 3. Leaves, glue, interface: ratings

| statement | kind | printed form? | reason |
| --- | --- | --- | --- |
| `Manuscript.RestrictedConverse P` | target hypothesis (Theorem 5.3) | the manuscript's statement, Selmer condition abstract | unchanged |
| `Lemma54At P` | interface (Lemma 5.4 at `E_ℓ`) | no | `P` is abstract; becomes Lemma 5.4 (Poonen–Stoll) once `P` and `Sel₂` are genuine |
| `KolyvaginRankOne` | LEAF (published) | consequence of printed theorems | BCDT Thm A (modularity) with Kolyvagin Thm 1 (rank = 1 when `ord = 1`), over Mathlib's `LSeries` and points; the finiteness of `Ш` is dropped, since it has no Lean definition. It combines two prints, as `Literature.GrossZagier` does; flag "unread: new printed leaf; locator UNVERIFIED" |
| `MordellWeil` | LEAF (textbook) | yes | Mordell 1922; Silverman VIII.6.7 (number UNVERIFIED); Route K proves it for `C_d` |
| `DescentGlueM` | GLUE | no | complete 2-descent of `E_ℓ` (Silverman X.1.4) with the count `#E(ℚ)/2E(ℚ) ≥ 8`; Route K proves the same for `C_d` (`loc_of_mem_sel2_of_infinite_order`) |
| `DimThreeCount` | GLUE (ELLIOT parts: items 0.2, 0.3) | no | local images at `ℝ, 2, 3, q ∣ ℓ` and good primes, then `𝔽₂` linear algebra |
| `MatrixRealization` | GLUE (ELLIOT: S11–S12, item 0.4) | no | slots, reciprocity, CRT, Dirichlet |

## 4. Proof outline as formalized

1. `bookkeeping` (lines 1020–1032), proved. Write `B = N/D²` and `N = k²r` with `r` squarefree.
   Let `r₀ = gcd(r, 2730)`, `r₁ = r/r₀` (prime to `2730`). Choose `f ∈ {1,5,7,13,35,65,91,455}`
   with `f r₁ ≡ 17 (mod 24)`; these eight numbers represent `(ℤ/24)ˣ`. Then
   `m = r₀ f / gcd(r₀, f)²` is a positive divisor of `2730` (bits `bᵢ`), `β = f r₁`,
   `A = mB = β (k r₀ / (gcd·D))²`.
   Next `T = D² − N/m ≡ 1 (mod 24)`, since `2⁴3⁴5²7²13² ∣ N` and `D` is prime to `6`. Then
   `θ` is the squarefree part of `T`, and `H = A(A − B²) = T (mB/D)²`.
   For the local squares: at `p ∣ β` we have `p ∣ N/m`, so `T ≡ D²` is a nonzero square mod `p`.
   At `p ∣ θ` we have `p ∤ 2730 D`, so `N/m ≡ D²`, hence `β ≡ (mDg/(kr₀))²`. Coprimality
   follows.
   This differs in form from the manuscript's wording ("choose positive `m` making `A` square at
   two and a nonsquare unit at three") but gives the same `m`, since `β ≡ 17 (mod 24)` says exactly
   that.
2. `SimultaneousConstruction` (hypothesis; reduced to `MatrixRealization` and `DimThreeCount`).
3. `CRM` at `n` and at `nθ`: rational points with `x − ℓ` a square and `x ≡ β` modulo squares
   (`point_of_locM`; `β ≡ 2 (mod 3)` is not a square).
4. `witnesses_of_points` (lines 1111–1119), proved. Take `q = t₁/s` and `e = n/q²`, so that
   `(A, y₁/q³) ∈ E_e`. The second point rescaled by `c², c³` lies on `E_{nH}`; dividing by
   `q², q³` gives abscissa `Az²` with `z = c t₂/(s q)`, and `w = (eHz)⁻¹`.
   `polePoly_eq_zero_of` then evaluates `Q_pole` to zero.
5. `CRM` from Theorem 5.3. Lemma 5.4 gives `P(E_ℓ)`; Theorem 5.3 gives `ord_{s=1} = 1`; Lemma 5.5
   gives rank 1, hence a point of infinite order (`exists_not_isOfFinAddOrder_of_rank`).
   `DescentGlueM` then gives the rational point in the class.

## 5. Numerical checks (plain python3; PARI/sympy are not installed on this host)

* `local2.py`: for `ℓ ≡ 3 (mod 4)`, every residue mod 32, the 2-adic Kummer image is the 8 classes
  `{a odd, b ≡ 1 (mod 4)}`. VERIFIED (sampled).
* `compare.py`: for all 55 squarefree `ℓ < 700`, `ℓ ≡ 11 (mod 12)`, the brute-force `SelM ℓ`
  (local searches at `p ∣ 6ℓ` and over `ℝ`) equals the set predicted by the local image formulas
  used in `DimThreeCount`: `a > 0`; `a, b` odd with `b ≡ 1 (mod 4)`; `b ≡ 1 (mod 3)`; at `q ∣ ℓ`,
  the span of `(ℓ, 1)` and `(3, −ℓ)`. 0 mismatches. VERIFIED.
* `selmer.py`: `ℓ = 323 = 17·19`, `β = 17` satisfies `MatrixConditions`, and brute force gives
  `#Sel = 8` with `(17, 1) ∈ Sel`. The same holds for `n = 5627 = 17·331` found by the
  construction. VERIFIED.
* `batch.py`, `batch2.py`: 30 random `β` with `θ = 1`, and 30 random `(β, θ)` with `θ > 1`
  (1–3 primes, all conditions of the bookkeeping). In all 60 cases a random search over
  `n = β q₀ p₁ ⋯ p_{d−1}` (`q₀ ≡ 7`, `p_k ≡ 1 (mod 12)`, the slot types of line 1042) finds `n`
  with `MatrixConditions` for `n` (and for `nθ`), within at most 697 tries. This is evidence for
  `MatrixRealization`, not a proof.

## 6. `#discharges` and autofold

`Manuscript.PoleCompleteness` is not a field of any bundle of `ZInQ.OneProof.frozenTarget`, so no
open hypothesis is discharged and autofold does not apply (no bundle field changes).
`scratch/pc-from-rc/autofold.json` records this and lists the new statements with their kinds and
flags, for use if the manuscript-faithful headline (issue #74) takes `PoleCompleteness`.
`#discharges` output: see `scratch/pc-from-rc/discharges-output.txt`.

## 7. What remains

* `DescentGlueM`: port Route K's Kummer machinery (`RouteK/Rank/KummerAt.lean`, `Delta.lean`,
  `Image.lean`, `RK9.lean`, for `y² = x³ + bx`) to `y² = x(x − ℓ)(x + 3ℓ)`; the counting lemma
  `RouteK.Rank.eight_le_card_quotient_two` is generic.
* `DimThreeCount`: state the local images (real place, `2`, `3`, `q ∣ ℓ`, good primes) as lemmas
  over `ℚ_p` and prove them (Route K's `Selmer/BadOdd.lean`, `Good.lean`, `PadicSquare.lean` are
  models). Then formalize the `𝔽₂` count of item 0.3, with the reciprocity identities from
  Mathlib's `legendreSym.quadratic_reciprocity`.
* `MatrixRealization`: the construction of lines 1036–1060 (ELLIOT), using Dirichlet's theorem
  (`Nat.setOf_prime_and_eq_mod_infinite`), CRT and reciprocity.
* `Lemma54At`: fix the form of `SelmerCorankOne` (another design pass).

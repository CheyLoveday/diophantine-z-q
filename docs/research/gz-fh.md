# gz-fh: `FHNonvanishing` split into Friedberg–Hoffstein Theorem B, the twisted root number, and proved glue

Status: research note (task gz-fh, 2026-11-15). Branch `wip/gz-fh` (base `wip/w72` 24f97774).
Lean: `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` (new file, the deliverable),
`scratch/gz-fh/FH.lean` (the same content as a scratch check), `scratch/gz-fh/Discharges.lean`
(the `#discharges` run). Results log: `scratch/gz-fh/log.md`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published
theorem with its reference. **SPECULATIVE**: an assessment. No copy of Friedberg–Hoffstein,
Atkin–Li or Iwaniec–Kowalski is on this host and there is no network: **every literature locator
in this note is UNVERIFIED**, and the statement of Friedberg–Hoffstein's theorem is recalled from
memory.

---

## 0. Main result

**`ZInQ.GZDecomp.FHNonvanishing` is proved from two printed leaves, and all of the glue is proved
in Lean.** `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` builds
(`lake build +ZInQKernel.Contrib.OneProof.FHNonvanishing`, VERIFIED), and
`#print axioms ZInQ.GZFH.fhNonvanishing_of_printed` gives `[propext, Classical.choice, Quot.sound]`
(VERIFIED, `scratch/gz-fh/FH.lean`). The `#discharges` output is in §4.

```lean
theorem ZInQ.GZFH.fhNonvanishing_of_printed
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB) (hTw : ZInQ.GZFH.TwistNewformRootNumber) :
    ZInQ.GZDecomp.FHNonvanishing
```

`FHNonvanishing` (hypothesis `hL2` of `ZInQ.OneProof.frozenTarget`, rated composite) now rests on
two printed leaves over genuine definitions, and everything else is proved:

| Name (`ZInQ.GZFH.`) | Kind | Source (UNVERIFIED locators) | Printed form? |
| --- | --- | --- | --- |
| `FriedbergHoffsteinB` | LEAF (research) | Friedberg–Hoffstein, Ann. of Math. (2) 142 (1995) 385–423, Theorem B | specialization of the printed theorem (`F = ℚ`, `π = π_f` weight 2 trivial central character, `χ₀` unramified at the finite places of `S`, `S ∋ 2`), with the local conditions `χ_v = χ₀,v` written as `D/D₀ ∈ (ℚ_v^×)²` (Mathlib's `ℚ_[p]`) and `ε(½, π ⊗ χ₀) = 1` written as Tau Ceti's root number of the twisted newform. Not literal: the idelic language is translated by a standard dictionary (§2). Flag: unread. |
| `TwistNewformRootNumber` | LEAF (textbook) | Iwaniec–Kowalski, *Analytic Number Theory* (2004), Prop. 14.20; Atkin–Li, Invent. Math. 48 (1978) 221–243, Thm 3.1; Shimura 1971 Prop. 3.64 | consequence of the printed proposition: specialized to `k = 2`, trivial nebentypus, `χ = χ_D` with `D` odd fundamental, and the Gauss sum evaluated (`τ(χ_D)² = χ_D(−1)|D|`). Flag: unread. |
| `fhNonvanishing_of_printed` and helpers | GLUE, proved | Dirichlet's theorem (Mathlib), gz-statements' `heegnerHyp_iff_split`, `jacobiSym_neg_level`, `coprime_of_heegnerHyp`, reduction `ℤ_p → ℤ/p`, `ℤ_2 → ℤ/8` | — |

The root-number computation the proof needs is proved in Lean: for the auxiliary discriminant
`D₀ = −q` (`q ≡ −1 mod 8N` prime, from Dirichlet's theorem in Mathlib)
`χ_{D₀}(−N) = −1`, so `rootNumber(f ⊗ χ_{D₀}) = χ_{D₀}(−N)·(−1) = +1`, which is Friedberg–Hoffstein's
compatibility hypothesis. What cannot be proved from Mathlib or Tau Ceti today is the *formula*
`ε(f ⊗ χ) = χ(−N) ε(f)` itself together with the newform property of the twist (Tau Ceti has
`CuspForm.twist` and its `q`-expansion, but neither newness of twists nor the twisted Fricke
eigenvalue; VERIFIED by reading `Contrib/TauCeti/NumberTheory/ModularForms/Twist/Basic.lean`), so
it is the separate leaf `TwistNewformRootNumber`.


---

## 1. The statements (verbatim from the Lean file)

```lean
def IsOddFundDisc (D : ℤ) : Prop := D ≠ 1 ∧ D % 4 = 1 ∧ Squarefree D

def FriedbergHoffsteinB : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    (∃ (M : ℕ) (_ : NeZero M) (g : Newform M 2) (hg : g.χ = 1),
        (∀ n : ℕ, n ≠ 0 → coeff g n = twistCoeff f D₀ n) ∧ rootNumber g hg = 1) →
    ∀ B : ℕ, ∃ D : ℤ, B < D.natAbs ∧ IsOddFundDisc D ∧ 0 < D * D₀ ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p]))) ∧
      ∀ G : ℂ → ℂ, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0

def TwistNewformRootNumber : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
  ∀ D : ℤ, IsOddFundDisc D → Nat.Coprime D.natAbs N →
    ∃ (M : ℕ) (_ : NeZero M) (g : Newform M 2) (hg : g.χ = 1), M = N * D.natAbs ^ 2 ∧
      (∀ n : ℕ, n ≠ 0 → coeff g n = twistCoeff f D n) ∧
      rootNumber g hg = (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) * rootNumber f hχ

theorem fhNonvanishing_of_printed (hFH : FriedbergHoffsteinB) (hTw : TwistNewformRootNumber) :
    FHNonvanishing
```

Objects (all genuine, none invented here): Tau Ceti's `HeckeRing.GL2.Newform` (eigen away from the
level, Petersson-new, `a₁ = 1`); `GZDecomp.coeff`, `twistCoeff f D n = aₙ(f)·(n/|D|)`,
`rootNumber f hχ = i²·frickeSign` (the sign of Tau Ceti's proved functional equation
`Λ_N(2 − s) = rootNumber · Λ_N(s)`), `IsEntireCont`; Mathlib's `jacobiSym`, `ℚ_[p]`, `Squarefree`.
The one new definition, `IsOddFundDisc`, is the elementary predicate "odd fundamental discriminant
`≠ 1`".

## 2. `FriedbergHoffsteinB` against the printed theorem

**The printed theorem as recalled (UNVERIFIED in every detail; same recollection as
gz-statements §2.2).** S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic
L-functions on GL(2)*, Ann. of Math. (2) 142 (1995), 385–423, Theorem B: let `π` be a cuspidal
automorphic representation of `GL₂(𝔸_F)` (trivial central character, or self-contragredient: not
remembered), `S` a finite set of places containing the archimedean places, the places where `π`
ramifies (and possibly those above 2), and `χ₀` a quadratic idele class character with
`ε(½, π ⊗ χ₀) = 1`. Then there are infinitely many quadratic idele class characters `χ` with
`χ_v = χ₀,v` for all `v ∈ S` and `L(½, π ⊗ χ) ≠ 0`. Whether this is labelled A or B is not reliably
remembered (gz-statements §2.2); the task brief and gz-decomp say B.

**Clause by clause** (`F = ℚ`, `π = π_f`):

| Lean clause | Printed counterpart | Relation |
| --- | --- | --- |
| `f : Newform N 2`, `f.χ = 1` | `π` cuspidal, trivial central character | specialization |
| `S ⊇ {p ∣ 2N}` (with `∞` implicit) | `S` contains `∞`, the ramified places, (places above 2) | specialization (`2 ∈ S` imposed even if the print does not need it) |
| `IsOddFundDisc D₀`, `p ∤ D₀` for `p ∈ S` | `χ₀` quadratic; here unramified at the finite places of `S` | specialization; quadratic characters of `ℚ` ↔ fundamental discriminants (STANDARD), and `χ₀,2` unramified ↔ `D₀` odd |
| `∃ g, coeff g = twistCoeff f D₀, rootNumber g = 1` | `ε(½, π ⊗ χ₀) = 1` | the hypothesis implies the printed one: such a `g` has `π_g ≅ π_f ⊗ χ₀` (strong multiplicity one), and `rootNumber g` is `ε(½, π_g)` (the sign of the proved functional equation of `Λ(g, s)`, which is `≢ 0`). Stronger hypothesis ⇒ weaker leaf. |
| `∀ B, ∃ D, B < |D|` | infinitely many `χ` | `χ = χ_D`, finitely many `D` per bound |
| `IsOddFundDisc D` | `χ` quadratic, `χ_2 = χ₀,2` unramified | `D` fundamental and odd |
| `0 < D * D₀` | `χ_∞ = χ₀,∞` | `χ_{D,∞} = sgn^{[D<0]}` |
| `IsSquare (D / D₀)` in `ℚ_p`, `p ∈ S` | `χ_p = χ₀,p` | `χ_{D,p}(x) = (D, x)_p` (Hilbert symbol), nondegenerate, so `χ_{D,p} = χ_{D₀,p}` iff `D/D₀ ∈ (ℚ_p^×)²` (Serre, *A course in arithmetic*, Ch. III Thm 2, UNVERIFIED number) |
| `∀ G, IsEntireCont (twistCoeff f D) 2 G → G 1 ≠ 0` | `L(½, π ⊗ χ) ≠ 0` | for `(D, N) = 1` (forced by `χ_p = χ₀,p` unramified at `p ∣ N`) the series `∑ aₙ(f) χ_D(n) n^{−s}` is the finite `L(s − ½, π ⊗ χ_D)`; `G` exists (G6) and is unique, so the clause is not vacuous; if the print uses `L^S`, the omitted Euler factors are finite and nonzero at the centre (gz-statements §2.3) |

**Rating: printed form up to the stated dictionary, a specialization, never stronger** (provided
the recalled statement is right). It inherits gz-statements' open human checks §6 H1 (a)-(f):
no level restriction, dihedral `π` allowed (the use is the CM newform of `C_d`), arbitrary local
data at `S ∋ 2`, the form of the root-number hypothesis, "infinitely many", the label and page.
The improvement over the composite `FHNonvanishing`: the root number of the twist is no longer
folded in, and the leaf's hypothesis is the printed compatibility hypothesis, applied to one
explicit `χ₀`, instead of a consequence of it computed under the Heegner conditions.

## 3. `TwistNewformRootNumber` against the printed proposition

Printed (UNVERIFIED, from memory): Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloquium
Publ. 53 (2004), Prop. 14.20: if `f ∈ S_k(N, ψ)` is primitive and `χ` is a primitive character
mod `r` with `(r, N) = 1`, then `f ⊗ χ` is primitive in `S_k(N r², ψ χ²)` and
`η(f ⊗ χ) = ψ(r) χ(N) τ(χ)² r⁻¹ η(f)`, `η` the pseudo-eigenvalue of `W`. Also Atkin–Li,
*Twists of newforms and pseudo-eigenvalues of W-operators*, Invent. Math. 48 (1978) 221–243,
Thm 3.1 (UNVERIFIED number), and Shimura 1971 Prop. 3.64 for the twisted functional equation.

Specialization: `k = 2`, `ψ = 1`, `χ = χ_D` with `D` an odd fundamental discriminant, `r = |D|`;
`τ(χ_D)² = χ_D(−1)|D|` (Gauss), so `η(f ⊗ χ_D) = χ_D(−1)χ_D(N) η(f) = χ_D(−N) η(f)`, and
`rootNumber = i^k η` turns this into `rootNumber(g) = χ_D(−N) rootNumber(f)`. `χ_D(−N)` is
`jacobiSym (−N) |D|`, the Kronecker symbol `(D/·)` at `−N` for `D ≡ 1 mod 4`. The nebentypus
`χ_D²` is principal mod `|D|`, so `g.χ = 1` at level `N D²`. For real `χ` the possible readings
`χ(N)`, `χ̄(N)`, `χ(−N)` of the print agree after `τ(χ)²` is evaluated (gz-statements §6 H2).

**Rating: consequence of the printed form** (specialization plus the Gauss-sum evaluation), not
literal. It could become glue: Tau Ceti has `CuspForm.twist` and its `q`-expansion
(`Twist/Basic.lean`), but not that the twist of a newform is new (that is the hard half of
Atkin–Li) nor the conjugation of the Fricke involution through the twist. The root-number half
alone (Fricke conjugation of the twist by Gauss sums, Iwaniec, *Topics*, §7.3) is a feasible
project proof; newness is not, today. The glue uses the leaf once, at the auxiliary `D₀ = −q`.

## 4. The glue (proved) and `#discharges`

Proof of `fhNonvanishing_of_printed` (all VERIFIED by compilation):

1. Dirichlet's theorem in Mathlib (`Nat.forall_exists_prime_gt_and_eq_mod`) gives a prime
   `q ≡ −1 (mod 8N)`.
2. `D₀ = −q` is an odd imaginary fundamental discriminant with the Heegner hypothesis for `N`
   (`heegner_neg_prime`: `−q ≡ 1 mod 8`, `−q ≡ 1 mod p` for odd `p ∣ N`, via gz-statements'
   `heegnerHyp_iff_split`).
3. `TwistNewformRootNumber` at `D₀` (coprimality from `coprime_of_heegnerHyp`) gives the twisted
   newform `g` with `rootNumber g = χ_{D₀}(−N)·rootNumber f = (−1)(−1) = 1`
   (`jacobiSym_neg_level`). **This is the root-number computation the proof needs, in Lean.**
4. `FriedbergHoffsteinB` with `S = (2N).primeFactors` (`p ∤ D₀` for `p ∈ S` since `p ∣ q + 1`)
   gives `D` with `|D| > B`, `IsOddFundDisc D`, `D·D₀ > 0` (so `D < 0`), `D/D₀` a square in every
   `ℚ_p`, `p ∣ 2N`, and the nonvanishing.
5. Local squares to the Heegner hypothesis: `exists_padicInt_of_isSquare_div` (`a/b = x²`,
   `p ∤ b` ⇒ `x ∈ ℤ_p`); `zmod_of_isSquare_div` (odd `p`: reduce mod `p`, `D ≡ ȳ²`, and `p ∤ D`
   since otherwise `p² ∣ D`, against squarefree); `mod_eight_of_isSquare_div` (`p = 2`: reduce
   `ℤ_2 → ℤ/8`, `D ≡ ȳ²`, and `5` is not a square mod 8, so `D ≡ 1 mod 8`). Then
   `heegnerHyp_iff_split` gives `HeegnerHyp N D`.

DISCHARGES_PLACEHOLDER

**Main.lean edit (for the integrator; not made here).** `hL2` is a top-level hypothesis of
`ZInQ.OneProof.frozenTarget`, not a bundle field, so autofold does not cover it. The edit: replace
the argument `(hL2 : ZInQ.GZDecomp.FHNonvanishing)` by the two arguments
`(hFH : ZInQ.GZFH.FriedbergHoffsteinB) (hTw : ZInQ.GZFH.TwistNewformRootNumber)`, pass
`(ZInQ.GZFH.fhNonvanishing_of_printed hFH hTw)` where `hL2` was passed, and add
`import ZInQKernel.Contrib.OneProof.FHNonvanishing` to `Main.lean`. kinds.tsv: remove the
composite row for `FHNonvanishing`; add `FriedbergHoffsteinB` (LEAF, research, unread) and
`TwistNewformRootNumber` (LEAF, textbook, unread). Proposed locators.md rows: Friedberg–Hoffstein
1995 Thm B (label and page unread; checks H1 (a)-(f) of gz-statements §6), Iwaniec–Kowalski
Prop. 14.20 / Atkin–Li 1978 Thm 3.1 (number unread; check H2). The GLUE count does not rise: one
composite is replaced by two leaves and proved glue.

## 5. Would the `C_d` form (`FHNonvanishingCd`) make the split easier?

Not for this split: the same two leaves imply it (`FHNonvanishing ⇒ FHNonvanishingCd`,
`GZStatements.fhNonvanishingCd_of_fhNonvanishing`, so
`fhNonvanishingCd_of_fhNonvanishing (fhNonvanishing_of_printed hFH hTw)`), and the glue would be
the same with `B = 4`. The `C_d` form helps in two other ways (SPECULATIVE assessment):

* **`TwistNewformRootNumber` could become project glue.** For `f` the newform of `C_d` and
  `D ≡ 1 (mod 8)` (forced by the Heegner condition at 2), `f ⊗ χ_D` has the coefficients of
  `C_{d|D|} : y² = x³ − d²D²x` (the quadratic twist; additive reduction at `p ∣ 2dD` makes both
  sides vanish there). So the twisted newform and its sign are those of another congruent-number
  curve, `n = d|D| ≡ 3 (mod 8)`, whose root number is `+1`. The project has the needed machinery
  for `n ≡ 5 (mod 8)` (`HeckeThetaNewform` for `n ≡ 1 mod 4`, proved by atkin-li;
  `functionalEquation5`, Hecke-character functional equation with sign `−1`; `signOfSimpleZero`
  matching Tau Ceti's root number with that sign). Extending these to `n ≡ 3 (mod 8)`
  (Hecke character of conductor dividing `(1+i)^5 n`, sign `+1`) would replace the leaf by glue. Not
  attempted here.
* **The FH leaf can be narrowed** to the one dihedral family (H1 (a), (b) then only concern level
  `32 d²` and CM by `ℚ(i)`), which makes its statement check easier, and the "infinitely many"
  clause is used only to avoid `D = −3`.

Recommendation: keep the general split now (it is what the source states); the `C_d` form is
worth choosing if the project wants to prove the twisted root number rather than cite it.

## 6. What remains

* Human statement checks: FH Theorem B (gz-statements §6 H1 (a)-(f)), Iwaniec–Kowalski Prop. 14.20
  / Atkin–Li (H2). No locator here was read.
* The Main.lean edit and kinds.tsv/locators.md rows (§4), for the integrator.

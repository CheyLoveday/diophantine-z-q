# deg-det: `DegEqDetTate` (Mumford §19 Thm 4, `deg ψ = det T_ℓ ψ`) reduced to its two geometric inputs

Task deg-det (2026-11-16). Base: wip/charpoly-ell 0d75311f, merged with origin/main 0caafe66 (STATUS.md only).
Scratch: `scratch/deg-det/` (results log `log.md`). Contribution: `ZInQKernel/Contrib/OneProof/DegEqDetTate.lean`
with helpers `ZInQKernel/Contrib/OneProof/DegEqDetTate/Algebra.lean` and `.../DegEqDetTate/TateIndex.lean`
(namespace `ZInQ.Contrib.OneProof.DegDet`). Autofold spec: `scratch/deg-det/autofold.json`.

## 1. Result

**The target (`charPolyIndepOfEllAlgClosed` removed, −1, no new leaf) is not reachable, and the report says
why (§4).** What is proved instead (VERIFIED: compiled, axioms `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_printed
    (hP : DegDet.DegHomogPoly) (hS : DegDet.SepDegKernel)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed

theorem ZInQ.Contrib.OneProof.DegDet.degEqDetTate_of_printed
    (hP : DegHomogPoly) (hS : SepDegKernel) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : CharPolyEll.DegEqDetTate
```

So charpoly-ell's leaf `DegEqDetTate` (Mumford §19 Thm 4, first assertion) is **proved** from

| statement | content | rating |
| --- | --- | --- |
| `DegHomogPoly` (new) | `deg` is a homogeneous polynomial function of degree `2g` on `End(A)` | LEAF, printed form (Mumford §19; UNVERIFIED locator) |
| `SepDegKernel` (new) | for an isogeny `ψ`: `ker ψ(k̄)` is finite and `deg ψ = #ker ψ(k̄) · p^e` (`p` = characteristic exponent) | LEAF, printed form (Mumford §4, §7; UNVERIFIED locators) |
| `mumfordTorsionAlgClosed` | `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | existing open field of the same bundle |
| `homFreeFiniteAlgClosed` | `End(A)` finite free over `ℤ` (only finiteness is used) | existing open field of the same bundle |

with **no glue left open**: everything else in Mumford's proof is now Lean (§3). The intermediate statement
`DegLadicIsogeny` (`|det V_ℓ ψ|_ℓ = |deg ψ|_ℓ` for isogenies) is proved from `SepDegKernel` and
`mumfordTorsionAlgClosed` (`degLadicIsogeny_of_sepDegKernel`).

**Count.** The fold `scratch/deg-det/autofold.json` (dry run, VERIFIED) gives `strict 34/11 on 45 → 35/11 on 46`
(strictest the same): −1 field, +2 printed leaves, no glue. charpoly-ell's fold (one leaf, `DegEqDetTate`) gives
`34/11 → 34/11` and **remains the better fold for the count**. The value of this task is that the theorem
charpoly-ell left as a leaf is now proved down to its two textbook inputs, and a crowdsourced formalization of
`DegEqDetTate` only has to supply `DegHomogPoly` and `SepDegKernel` (§5). My recommendation: fold charpoly-ell's
spec now (net 0); keep this file as the route from `DegEqDetTate` to its inputs (it compiles against the
current chain, and `degEqDetTate_of_printed` can be folded later if `DegHomogPoly` and `SepDegKernel` are
preferred over `DegEqDetTate` as crowdsourcing targets).

## 2. Statements (new)

All three are over the genuine degree `CharPolyEll.degEnd` (charpoly-ell): `[K(A) : ψ^*K(A)]` via the stalk map at
the generic point for `ψ` finite and surjective, `0` otherwise.

```lean
/-- LEAF (printed form), Mumford §19 (UNVERIFIED locator; also Milne, Abelian varieties (2008), §12). -/
def DegHomogPoly : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (r : ℕ) (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((degEnd (∑ i, x i • e i) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N

/-- LEAF (printed form), Mumford §4, §7 (UNVERIFIED locators; also Milne (2008), §7). -/
def SepDegKernel : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    PkgI3.AbVar.IsIsogenyMor ψ.hom →
      Finite (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ).ker ∧
        ∃ e : ℕ, degEnd ψ =
          Nat.card (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) ψ).ker * ringExpChar k ^ e

/-- consequence of DegEqDetTate; proved here from SepDegKernel + mumfordTorsionAlgClosed. -/
def DegLadicIsogeny : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → PkgI3.AbVar.IsIsogenyMor ψ.hom →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        ‖(LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ])).det‖ =
          ‖(degEnd ψ : ℚ_[ℓ])‖
```

**Ratings.**

* `DegHomogPoly`: **printed form** (a consequence of the printed statement, never stronger). Mumford's §19 (in
  the proof of Thm 4) and Milne's §12 state that `deg : End(X) → ℤ` is a homogeneous polynomial function of
  degree `2g`: a polynomial with rational coefficients in the coordinates of the free `ℤ`-module `End(X)`.
  The Lean statement reads this in coordinates of an arbitrary finite family `e₁, …, e_r` (composing a
  polynomial function with a linear map `ℤ^r → End(X)`), which is a consequence. Locator UNVERIFIED (no access
  to the book from this host). Sanity: for `dim A = 0` both sides are the constant `1`; for an elliptic curve
  with CM by `ℤ[i]`, `deg(a + bi) = a² + b²`, homogeneous of degree 2 (STANDARD).
* `SepDegKernel`: **printed form**. Mumford §4 (isogenies: `#ker f = deg_s f`) and the fact that the inseparable
  degree of a finite field extension is a power of `p` (Mumford §7 for isogenies; general field theory).
  The kernel is taken on the points over `AlgebraicClosure k`, the points that carry `T_ℓ` in the kernel; for
  `k` algebraically closed `k → k̄` is an isomorphism, so these are Mumford's closed points. Locators UNVERIFIED.
* `DegLadicIsogeny`: not a new hypothesis of the final theorem (proved).

## 3. The proof (all in Lean)

Fix `k`, `A`, `φ ∈ End(A)`, `ℓ ≠ char k`, a basis `b` of `V_ℓ`, and `ρ = rho b : End(A) →+* M_I(ℚ_ℓ)`
(charpoly-ell). `End(A)` is finite over `ℤ` (`homFreeFiniteAlgClosed`), so `R(φ) = 0` for a monic `R ∈ ℤ[X]`.

**3.1 `deg` is multiplicative on isogenies** (`degEnd_mul_of_isIsogeny`; tower law). A surjective morphism of
irreducible schemes maps the generic point to the generic point (`map_genericPoint`); the stalks at points equal
to the generic point are fields (`isField_stalk`); `Scheme.Hom.stalkMap_comp` and `Module.finrank_mul_finrank`
give `deg(ψχ) = deg ψ · deg χ`.

**3.2 The algebra of Mumford's proof** (`DegEqDetTate/Algebra.lean`, Mathlib only; abstract theorem
`det_eq_deg_abstract`). For a ring `E`, `φ ∈ E` with `R(φ) = 0`, `deg : E → ℕ` that is a homogeneous polynomial
function of degree `n` on `ℤ[φ]`, multiplicative on pairs of nonzero values with `deg 1 = 1`, and
`ρ : E →+* M_I(ℚ_ℓ)` with `|det ρ(ψ)|_ℓ = |deg ψ|_ℓ` whenever `deg ψ ≠ 0`: `det ρ(φ) = deg φ`. Steps:

1. *Extension* (`Nt_mul`). Read `deg` on `ℤ[X]/(R)` as `N(coefficients of F mod R)`, `N ∈ ℚ[x₀, …, x_{d−1}]`.
   On generic coefficients the polynomial `(N(FG) − N(F)N(G)) N(F) N(G)` vanishes at every point of `ℕ^{2d}`
   (multiplicativity where both values are nonzero), hence is `0` (Combinatorial Nullstellensatz,
   `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`); `N(F) ≢ 0` because `N(1) = 1`. So `N` is multiplicative
   on `S[X]/(R)` for every `ℚ`-algebra `S`, in particular `S = Ω = PadicAlgCl ℓ`. Homogeneity gives
   `N(c) = cⁿ`, and `P₀(t) = N(t − X)` is monic of degree `n` (`P0_monic`).
2. *Products over roots* (`eq_Rs_of_mul`, `det_aeval_eq_Rs`). A multiplicative `Ω[X] → Ω` with `c ↦ cⁿ` and
   `X − r ↦ (−1)ⁿ P(r)` is `F ↦ ∏_{P(a)=0} F(a)`; so `N(F) = ∏_{P₀(a)=0} F(a)` and
   `det F(ρφ) = ∏_{χ(b)=0} F(b)` for `χ` the characteristic polynomial of `ρ(φ)`.
3. *Comparison lemma* (`eq_of_norm_RsZ`, `mult_eq_of_norm_Rs`). Two monic `P, Q ∈ ℚ_ℓ[X]` with
   `|∏_{P(a)=0} F(a)| = |∏_{Q(b)=0} F(b)|` in `PadicAlgCl ℓ` for every `F ∈ ℤ[X]` with nonzero left side are equal:
   for each monic irreducible `μ` (`P = μ^e P₁`, `Q = μ^f Q₁`), test `F_n ∈ ℤ[X]` approximating `ℓ^s μ + ℓⁿ`
   to precision `ℓ^{2n}` (`PadicInt.appr`); ultrametric estimates give `|∏ F_n(roots of P)| = ℓ^{−n e deg μ} C_P`
   for `n` large, so `e = f`; equal multiplicities of all irreducible factors give `P = Q`
   (`UniqueFactorizationMonoid`).
4. With `ψ = F(φ)`: `∏_{P₀(a)=0}F(a) = deg F(φ)` and `∏_{χ(b)=0} F(b) = det ρ(F(φ))`; the hypothesis on `ρ` gives
   the comparison, so `P₀ = χ`, and at `F = X`: `deg φ = det ρ(φ)`.

**3.3 `|det T_ℓ ψ|_ℓ = |#ker ψ|_ℓ`** (`DegEqDetTate/TateIndex.lean`, abstract theorem
`TateIndex.norm_det_map_eq`): for an abelian group `M` with `#M[ℓⁿ] = ℓ^{nr}` for all `n` and a homomorphism
`φ : M → M` with **finite kernel** (surjectivity is not needed), `|det T_ℓ φ|_ℓ = |#ker φ|_ℓ` in `ℤ_ℓ`. Steps:
`T_ℓ φ` is injective (`map_injective_of_finite_ker`); for an injective `ℤ_ℓ`-linear `F` on a free module of finite
rank, `|det F|_ℓ = [T : F T]⁻¹` and the index is a power of `ℓ` (`norm_det_eq_inv_card`,
`card_quot_range_pow`; Smith normal form `Submodule.quotientEquivPiSpan`, `ℤ_ℓ/(a) ≅ ℤ/ℓ^{v(a)}`); every
`y ∈ M[ℓⁿ]` is `xₙ` for some `x ∈ T_ℓ M` (`exists_tate_lift_n`, from t5-torsion's `exists_lift`), and `xₙ = 0`
implies `x ∈ ℓⁿ T` (`exists_eq_pow_smul`); hence for `n` larger than the exponent of `T/FT`,
`T/FT ≅ M[ℓⁿ]/φ(M[ℓⁿ])`, whose order is `#(ker φ)[ℓⁿ]`; these orders stabilize, and Cauchy's theorem shows that
`(ker φ)[ℓⁿ]` then has index prime to `ℓ` in `ker φ`.

**3.4 Assembly.** `degLadicIsogeny_of_sepDegKernel`: with `M = A(k̄)`, the counts `#M[ℓⁿ] = ℓ^{2gn}` from
`mumfordTorsionAlgClosed` (as in t5-torsion's `tateModuleFree_at`), `T_ℓ ψ = homT ψ`, `det` over `V_ℓ` in any basis
equal to `det` over `ℤ_ℓ` (`LinearMap.det_baseChange`), and `deg ψ = #ker · p^e` with `ℓ ∤ p^e`
(`coprime_ringExpChar_pow`). Then `degEqDetTate_of_degHomogPoly` applies 3.2 with `E = End(A)`, `deg = degEnd`,
`ρ = rho b`, the leaf `DegHomogPoly` at the family `e_i = φ^i` (`i < deg R`), `degEnd_one` (charpoly-ell) and 3.1.
Finally charpoly-ell's `charPolyIndepOfEllAlgClosed_of_degEqDetTate` gives the field.

## 4. Why the target (−1, no new leaf) is not reachable

* **Polynomiality is a genuine input.** Counting `ker ψ` on `ℓ`-power torsion gives only
  `|det T_ℓ ψ|_ℓ = |deg ψ|_ℓ` (now proved from `SepDegKernel`), one prime at a time. The comparison lemma (3.2,
  step 3) turns this into `det = deg` only when `deg F(φ) = ∏_{P(a)=0} F(a)` for one fixed polynomial `P`, which is
  what polynomiality gives. Without it the `ℓ`-adic absolute values do not determine the integers: `X² + 1` and
  `X² + 1 + ℓ³` (`ℓ ≡ 3 mod 4`) have equal `ℓ`-adic absolute values at every integer (charpoly-ell §4; VERIFIED,
  math), and `det T_ℓ` is not known to be an `ℓ`-independent integer before Thm 4 is proved. Mumford's and Milne's
  proofs get polynomiality from the theorem of the cube and Riemann–Roch (`χ(f^*L) = deg f · χ(L)`), which nothing
  in the tree supplies. Checked (VERIFIED, read): the open fields `homFreeFiniteAlgClosed`,
  `mumfordTorsionAlgClosed`, `milneIsogenyQuasiInverse`, `weilPairingMumford`, `phiAmpleIsogeny`, `picZeroAbVar`,
  `picRepresentableAbVar`, `uniformizationLeafAll`, `gagaMorphism`.
* **The analytic route** (`uniformizationLeafAll`, `gagaMorphism`, both open fields) would give `T_ℓ = Λ ⊗ ℤ_ℓ`
  and `det = det_ℤ(ψ|Λ) = |det_ℂ|²` over `ℂ` only; the field quantifies over every algebraically closed `k`,
  including characteristic `p`, and a Lefschetz transfer is absent.
* **Narrowing to characteristic 0.** The consumers of `charPolyIndepOfEllAlgClosed` are all in characteristic 0
  (VERIFIED, read: `t7_of_algClosed5` → `PkgI3.CharPolyIndepOfEll` → `G0AssembleMod.linkedTateData_of_local`,
  an abelian variety over a number field; `R16Split.r16_of_printed`, over `ℚ`). Narrowing would not help:
  polynomiality is needed in characteristic 0 as well (outside the analytic route above), and in
  characteristic 0 `SepDegKernel` only simplifies to `deg ψ = #ker ψ`. The field's statement is kept.
* **The task's suggested steps (1)–(4).** (3) is proved (3.3), in the stronger form that needs only a finite
  kernel. (2) is `SepDegKernel` (characteristic 0: `deg = #ker`), kept as a printed leaf. (1) (finite and flat)
  is not needed by this route: the degree is the function-field degree, and flatness enters only through
  `SepDegKernel`. (4) has the gap of the first bullet: "both sides are integers independent of `ℓ`" is not known
  for `det T_ℓ` without polynomiality (it is the second assertion of Thm 4, i.e. the field itself).
* **What could remove `SepDegKernel`** (not attempted to completion; rating mine): the inequality
  `|deg ψ|_ℓ ≤ |#ker ψ|_ℓ` suffices for a one-sided comparison lemma together with
  `deg P₀ = deg χ = 2g` (T26). It follows from `#ker ψ ∣ deg ψ`, which is Artin's theorem applied to the action of
  `ker ψ` on `K(A)` by translations (`ψ ∘ τ_x = ψ`; faithful because a translation acting trivially on the
  function field is the identity, `ext_of_isDominant`). That would leave `DegHomogPoly` as the only new leaf
  (net 0, as charpoly-ell), at the cost of Lean scheme theory for translations and their action on stalks.

## 5. For contributors

To formalize Mumford §19 Thm 4 (`DegEqDetTate`, or the field `charPolyIndepOfEllAlgClosed` directly), it now
suffices to prove `DegHomogPoly` and `SepDegKernel` (plus the two open fields already listed in OPEN.md):
`degEqDetTate_of_printed` does the rest. `DegHomogPoly` is the deep input (theorem of the cube, `χ(f^*L) =
deg f · χ(L)`, Riemann–Roch on abelian varieties); `SepDegKernel` is the separable/inseparable degree theory of
isogenies.

## 6. Compile record

All VERIFIED on this host (Lean 4.35.0, Mathlib v4.35.0):

* `lake env lean scratch/deg-det/Algebra.lean`, `scratch/deg-det/TateIndex.lean`: OK (no `sorry`).
* `lake build ZInQKernel.Contrib.OneProof.DegEqDetTate`: OK. `scratch/deg-det/CheckAxioms.lean`: the axioms of
  `degEqDetTate_of_degHomogPoly`, `charPolyIndepOfEllAlgClosed_of_degHomogPoly`, `degEnd_mul_of_isIsogeny`,
  `det_eq_deg_abstract`, `degLadicIsogeny_of_sepDegKernel`, `charPolyIndepOfEllAlgClosed_of_printed`,
  `TateIndex.norm_det_map_eq` are `[propext, Classical.choice, Quot.sound]`; the two `example`s check the exact
  types against `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` and `CharPolyEll.DegEqDetTate`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.DegEqDetTate`: OK (13701 jobs). `#discharges`
  (`scratch/deg-det/Discharges.lean`, output `Discharges-output.txt`):

```
DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly
  still assumes: [ZInQ.Contrib.OneProof.DegDet.DegHomogPoly,
 ZInQ.Contrib.OneProof.DegDet.DegLadicIsogeny,
 ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_printed
  still assumes: [ZInQ.Contrib.OneProof.DegDet.DegHomogPoly,
 ZInQ.Contrib.OneProof.DegDet.SepDegKernel,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2970 theorems checked, 10 discharge one
```

* `python3 scripts/one_proof/autofold.py scratch/deg-det/autofold.json --dry-run`:
  `strict count: 34/11 on 45 -> 35/11 on 46; strictest 34/11 -> 35/11`; the printed module
  (`scratch/deg-det/FoldDryRun.lean`, line 1 stripped) compiles: `'HDec.HSyn.sixContactMin_of_open36' depends on
  axioms: [propext, Classical.choice, Quot.sound]`.

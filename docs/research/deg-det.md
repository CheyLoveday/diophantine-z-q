# deg-det: `DegEqDetTate` (Mumford §19 Thm 4, `deg ψ = det T_ℓ ψ`) proved from the polynomiality of the degree

Task deg-det (2026-11-16). Base: wip/charpoly-ell 0d75311f, merged with origin/main 0caafe66 (STATUS.md only).
Scratch: `scratch/deg-det/` (results log `log.md`). Contribution (namespace `ZInQ.Contrib.OneProof.DegDet`):
`ZInQKernel/Contrib/OneProof/DegEqDetTate.lean` (top) with helpers in `ZInQKernel/Contrib/OneProof/DegEqDetTate/`:
`Algebra.lean` (Mathlib only), `TateIndex.lean`, `Reduction.lean`, `KerDvd.lean`. Autofold spec:
`scratch/deg-det/autofold.json`.

## 1. Result

**charpoly-ell's leaf `DegEqDetTate` is proved in Lean from one new printed leaf and two open fields of the same
bundle; no glue is left open.** VERIFIED (compiled; axioms `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem ZInQ.Contrib.OneProof.DegDet.degEqDetTate_of_degHomogPoly_mumford
    (hP : DegDet.DegHomogPoly) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : CharPolyEll.DegEqDetTate

theorem ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford
    (hP : DegDet.DegHomogPoly) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
```

| hypothesis | content | rating |
| --- | --- | --- |
| `DegHomogPoly` (new) | `deg` is a homogeneous polynomial function of degree `2g` on `End(A)` | LEAF, printed form (Mumford §19; locator UNVERIFIED) |
| `mumfordTorsionAlgClosed` | `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | existing open field, same bundle |
| `homFreeFiniteAlgClosed` | `End(A)` finite free over `ℤ` (only finiteness is used) | existing open field, same bundle |

**The target "−1, no new leaf" is not met; the count is net 0** (dry run: strict `34/11 on 45 → 34/11 on 45`,
strictest the same; VERIFIED), the same count as charpoly-ell's fold. §4 explains why −1 is out of reach: the
polynomiality of the degree is a genuine geometric input (theorem of the cube and Riemann–Roch) that nothing in
the tree supplies. What changed is the leaf: instead of Mumford §19 Thm 4 itself, the open statement is now its one
deep input, and every other step of Mumford's proof is Lean:

* the algebra of the proof (multiplicative polynomial functions, products over roots, the `ℓ`-adic comparison
  lemma), §3.1;
* `deg(ψχ) = deg ψ · deg χ` for isogenies (tower law of function fields), §3.2;
* `|det T_ℓ ψ|_ℓ = |#ker ψ|_ℓ` for every endomorphism with finite kernel (elementary divisors over `ℤ_ℓ` and
  `A[ℓⁿ] ≅ (ℤ/ℓⁿ)^{2g}`), §3.3 (the task's step (3));
* `#ker ψ(k̄) ∣ deg ψ`, with the kernel finite, whenever `deg ψ ≠ 0` (translations by the kernel act faithfully
  on the function field over `ψ^*K(A)`; Artin's theorem), §3.4 (replaces the task's steps (1)–(2));
* `rank V_ℓ = 2g`.

**Recommendation.** Fold this spec instead of charpoly-ell's: same count, and the crowdsourcing target becomes
`DegHomogPoly` (cube + Riemann–Roch) instead of the whole of Thm 4, of which everything else is done.

Two intermediate routes also compile and are kept in `Reduction.lean` (they are superseded):
`charPolyIndepOfEllAlgClosed_of_degHomogPoly` (assumes `DegLadicIsogeny`, `|det V_ℓ ψ|_ℓ = |deg ψ|_ℓ`) and
`charPolyIndepOfEllAlgClosed_of_printed` (assumes the printed `SepDegKernel`, `deg ψ = #ker ψ · p^e`, Mumford §4,
§7, from which `DegLadicIsogeny` is proved, `degLadicIsogeny_of_sepDegKernel`).

## 2. The new leaf

Over the genuine degree `CharPolyEll.degEnd` (charpoly-ell): `[K(A) : ψ^*K(A)]` via the stalk map at the generic
point for `ψ` finite and surjective, `0` otherwise.

```lean
/-- LEAF (printed form), Mumford §19 (UNVERIFIED locator; also Milne, Abelian varieties (2008), §12). -/
def DegHomogPoly : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (r : ℕ) (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((degEnd (∑ i, x i • e i) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N
```

**Rating: printed form** (a consequence of the printed statement, never stronger). D. Mumford, *Abelian
varieties* (1970), §19, in the proof of Thm 4 (and Milne's notes, §12): `deg : End(X) → ℤ` is a homogeneous
polynomial function of degree `2g`, i.e. a rational polynomial in the coordinates of the free `ℤ`-module `End(X)`
(Thm 3). The Lean statement reads it in the coordinates of an arbitrary finite family `e₁, …, e_r`, which is the
composite with a linear map `ℤ^r → End(X)`: a consequence. `k` is algebraically closed, as in the book. Mumford's
`deg` is `0` on non-isogenies, as `degEnd`. Locator UNVERIFIED (no access to the book from this host). Sanity
(STANDARD): for `dim A = 0` both sides are the constant `1` (`End A = 0`, `deg 0 = deg 1 = 1`); for an elliptic
curve with CM by `ℤ[i]`, `deg(a + bi) = a² + b²`. Proposed kinds.tsv row (autofold spec): bundle textbook, kind
published, flag "unread: new printed leaf …; locator UNVERIFIED". Proposed locators.md row: Mumford, *Abelian
varieties*, §19 (deg homogeneous polynomial of degree 2g on End X), UNVERIFIED.

The superseded statements (kept in `Reduction.lean`): `DegLadicIsogeny` (`|det V_ℓ ψ|_ℓ = |deg ψ|_ℓ` for
isogenies; consequence of Thm 4) and `SepDegKernel` (for an isogeny, `ker ψ(k̄)` is finite and
`deg ψ = #ker ψ(k̄) · (ringExpChar k)^e`; printed form, Mumford §4, §7, locators UNVERIFIED).

## 3. The proof (all in Lean)

Fix `k`, `A`, `φ ∈ End(A)`, `ℓ ≠ char k`, a basis `b` of `V_ℓ`, `ρ = rho b : End(A) →+* M_I(ℚ_ℓ)` (charpoly-ell).
`End(A)` is finite over `ℤ` (`homFreeFiniteAlgClosed`), so `R(φ) = 0` for a monic `R ∈ ℤ[X]`. `DegHomogPoly` at
the family `e_i = φ^i` (`i < deg R`) makes `deg` a homogeneous polynomial function of degree `2g` on `ℤ[φ]`.

**3.1 The algebra** (`Algebra.lean`, Mathlib only; `det_eq_deg_abstract_le`). For a ring `E`, `φ ∈ E` with
`R(φ) = 0`, `deg : E → ℕ` homogeneous polynomial of degree `n` on `ℤ[φ]`, multiplicative on pairs of nonzero values
with `deg 1 = 1`, `ρ : E →+* M_I(ℚ_ℓ)` with `#I = n` and `|deg ψ|_ℓ ≤ |det ρ(ψ)|_ℓ` whenever `deg ψ ≠ 0`:
`det ρ(φ) = deg φ`.

1. *Extension* (`Nt_mul`): read `deg` as `N(coefficients of F mod R)`; on generic coefficients
   `(N(FG) − N(F)N(G)) N(F) N(G)` vanishes on `ℕ^{2d}`, hence is `0` (Combinatorial Nullstellensatz,
   `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`), and `N(F) ≢ 0` as `N(1) = 1`; so `N` is multiplicative on
   `S[X]/(R)` for every `ℚ`-algebra `S`, in particular `Ω = PadicAlgCl ℓ`. `P₀(t) = N(t − X)` is monic of degree
   `n` (`P0_monic`).
2. *Products over roots* (`eq_Rs_of_mul`, `det_aeval_eq_Rs`): `N(F) = ∏_{P₀(a)=0} F(a)` and
   `det F(ρφ) = ∏_{χ(b)=0} F(b)`, `χ` the characteristic polynomial of `ρ(φ)`.
3. *Comparison lemma* (`eq_of_norm_RsZ_le`, from `mult_le_of_norm_Rs_le`): monic `P, Q ∈ ℚ_ℓ[X]` of equal degree
   with `|∏_{P(a)=0} F(a)| ≤ |∏_{Q(b)=0} F(b)|` for all `F ∈ ℤ[X]` (nonzero left side) are equal. For a monic
   irreducible `μ` with `P = μ^e P₁`, `Q = μ^f Q₁`, test `F_n ∈ ℤ[X]` approximating `ℓ^s μ + ℓⁿ` to precision
   `ℓ^{2n}` (`PadicInt.appr`): ultrametric estimates give `|∏ F_n(roots of P)| = ℓ^{−n e deg μ} C_P` for `n`
   large, so `f ≤ e`; then `Q ∣ P` (`UniqueFactorizationMonoid`) and equal degrees give `P = Q`. (The two-sided
   version `eq_of_norm_RsZ` is also proved.)
4. With `ψ = F(φ)` the comparison gives `P₀ = χ`, and at `F = X`, `deg φ = det ρ(φ)`.

**3.2 `deg` is multiplicative on isogenies** (`Reduction.lean`, `degEnd_mul_of_isIsogeny`): a surjective morphism
of irreducible schemes fixes the generic point (`map_genericPoint`); stalks at points equal to it are fields
(`isField_stalk`); `Scheme.Hom.stalkMap_comp` and `Module.finrank_mul_finrank`.

**3.3 `|det T_ℓ ψ|_ℓ = |#ker ψ|_ℓ`** (`TateIndex.lean`, `TateIndex.norm_det_map_eq`): for an abelian group `M` with
`#M[ℓⁿ] = ℓ^{nr}` and a homomorphism `φ : M → M` with finite kernel (no surjectivity needed): `T_ℓ φ` is injective;
`|det F|_ℓ = [T : F T]⁻¹` and the index is a power of `ℓ` (Smith normal form, `Submodule.quotientEquivPiSpan`,
`ℤ_ℓ/(a) ≅ ℤ/ℓ^{v(a)}`); every `y ∈ M[ℓⁿ]` is `xₙ` for some `x ∈ T_ℓ M` (`exists_tate_lift_n`, from t5-torsion's
`exists_lift`) and `xₙ = 0 ⇒ x ∈ ℓⁿT`; so for `n` large `T/FT ≅ M[ℓⁿ]/φ(M[ℓⁿ])`, of order `#(ker φ)[ℓⁿ]`; these
stabilize and, by Cauchy's theorem, have index prime to `ℓ` in `ker φ`. Applied to `M = A(k̄)` with the counts from
`mumfordTorsionAlgClosed` (`card_tb_of_mumford`, as t5-torsion's `tateModuleFree_at`): `norm_det_V_eq_card_ker`.

**3.4 `#ker ψ(k̄) ∣ deg ψ`** (`KerDvd.lean`, `KerDvd.kerDvdDeg`, for `deg ψ ≠ 0`). A point `P ∈ ker ψ ⊆ A(k̄)` gives
the translation `τ_P = (A → Spec k → Spec k̄ →ᴾ A) · id` (using `k ≅ k̄`), with `τ_P ≫ ψ = ψ`,
`τ_{PQ} = τ_Q ≫ τ_P`, `τ_1 = id`, and `τ_P = id ⇒ P = 1` (`Q ≫ τ_P = P·Q`). An endomorphism `f` of the integral
scheme fixing the generic point acts on `K(A)` by `σ f` (generization map then stalk map), characterized by
`Spec(σ f) ≫ ι = ι ≫ f` for `ι = fromSpecStalk : Spec K(A) → A` (a monomorphism). Hence `σ(f ≫ g) = σ g ≫ σ f`,
`σ(τ_P)` fixes `ψ^*K(A)` (`stalkMap_comp_σP`), and `σ(τ_P) = id ⇒ τ_P = id` (`eq_id_of_σ_eq`, Mathlib's
`ext_of_isDominant_of_isSeparated`, `ι` dominant). So `ker ψ ↪ Aut(K(A)/ψ^*K(A))`, which is finite as
`deg ψ ≠ 0`; Artin (`IntermediateField.finrank_fixedField_eq_card`) and the tower law give the divisibility. Then
`|deg ψ|_ℓ ≤ |#ker ψ|_ℓ = |det V_ℓ ψ|_ℓ` (`norm_deg_le_norm_det`).

**3.5 Assembly** (`DegEqDetTate.lean`). `card_basis_V`: `#I = rank V_ℓ = rank T_ℓ = 2g`
(`Module.finrank_baseChange`, t5-torsion's `tate_linearEquiv`). `degEqDetTate_of_degHomogPoly_mumford` applies 3.1
with `E = End(A)`, `deg = degEnd`, `n = 2g`, 3.2, 3.4 and `degEnd_one` (charpoly-ell); charpoly-ell's
`charPolyIndepOfEllAlgClosed_of_degEqDetTate` gives the field.

## 4. Why −1 (no new leaf) is not reachable

* **Polynomiality is a genuine input.** The kernel count gives `|det T_ℓ ψ|_ℓ` versus `deg ψ` one prime at a time.
  The comparison lemma turns this into `det = deg` only when `deg F(φ) = ∏_{P(a)=0} F(a)` for one fixed polynomial
  `P`, which is what polynomiality provides; without it the `ℓ`-adic absolute values do not determine the integers
  (`X² + 1` and `X² + 1 + ℓ³`, `ℓ ≡ 3 mod 4`, have equal `ℓ`-adic absolute values at all integers; charpoly-ell §4;
  VERIFIED, math), and `det T_ℓ ψ` is not known to be an `ℓ`-independent integer before Thm 4 (that is the field
  itself). Mumford and Milne get polynomiality from the theorem of the cube and `χ(f^*L) = deg f · χ(L)` with
  Riemann–Roch on abelian varieties; nothing in the tree supplies these. Checked (VERIFIED, read): the open fields
  `homFreeFiniteAlgClosed`, `mumfordTorsionAlgClosed`, `milneIsogenyQuasiInverse`, `weilPairingMumford`,
  `phiAmpleIsogeny`, `picZeroAbVar`, `picRepresentableAbVar`, `uniformizationLeafAll`, `gagaMorphism`.
* **The analytic route** (`uniformizationLeafAll`, `gagaMorphism`): `T_ℓ = Λ ⊗ ℤ_ℓ`, `det = det_ℤ(ψ|Λ)` over `ℂ`
  only; the field quantifies over every algebraically closed `k`, characteristic `p` included, and there is no
  Lefschetz transfer in the tree.
* **Narrowing to characteristic 0** (checked as asked). The consumers of `charPolyIndepOfEllAlgClosed` are in
  characteristic 0 (VERIFIED, read: `t7_of_algClosed5` → `PkgI3.CharPolyIndepOfEll` →
  `G0AssembleMod.linkedTateData_of_local`, abelian varieties over number fields; `R16Split.r16_of_printed`, over
  `ℚ`). Narrowing would not remove `DegHomogPoly` (polynomiality is needed in characteristic 0 too, outside the
  analytic route) and the proof above works in every characteristic, so the field's statement is kept as is.
* **The task's steps.** (3) is proved (3.3), for any finite kernel. (1)–(2) (finite flatness; kernel of order `d`
  in characteristic 0) are not needed: the route only uses `#ker ∣ deg` (3.4), proved in every characteristic
  without flatness. (4) ("both sides are integers independent of `ℓ`") is replaced by the comparison lemma with
  polynomiality, see the first bullet.

## 5. For contributors

`DegHomogPoly` is now the only statement between the tree and Mumford §19 Thm 4 (both assertions) beyond the open
fields `mumfordTorsionAlgClosed` and `homFreeFiniteAlgClosed`. Its proof needs the theorem of the cube (so that
`ψ ↦ ψ^*L` is quadratic), `χ(f^*L) = deg f · χ(L)` for finite flat `f`, and Riemann–Roch `χ(L)² = deg φ_L` (or
`χ(L) = (L^g)/g!`) on abelian varieties. The reusable pieces proved here: `det_eq_deg_abstract(_le)` (pure algebra),
`TateIndex.norm_det_map_eq` (Tate modules of abelian groups), `KerDvd.kerDvdDeg` (scheme theory of translations).

## 6. Compile record

All VERIFIED on this host (Lean 4.35.0, Mathlib v4.35.0):

* `lake env lean` on `scratch/deg-det/Algebra.lean`, `TateIndex.lean`, `KerDvd.lean`: OK, no `sorry`.
* `lake build ZInQKernel.Contrib.OneProof.DegEqDetTate`: OK. `scratch/deg-det/CheckAxioms.lean`: axioms of
  `charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford`, `degEqDetTate_of_degHomogPoly_mumford`,
  `KerDvd.kerDvdDeg`, `TateIndex.norm_det_map_eq`, `det_eq_deg_abstract_le` (and the superseded routes) are
  `[propext, Classical.choice, Quot.sound]`; two `example`s check the exact types against
  `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` and `CharPolyEll.DegEqDetTate`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.DegEqDetTate`: OK (13704 jobs; `frozenTarget` standard axioms). `#discharges`
  (`scratch/deg-det/Discharges.lean`, full output `Discharges-output.txt`), the line for the recommended theorem:

```
DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford
  still assumes: [ZInQ.Contrib.OneProof.DegDet.DegHomogPoly,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 3019 theorems checked, 11 discharge one
```

  (the output also lists the two superseded routes, assuming `DegLadicIsogeny` resp. `SepDegKernel` in addition).
* `python3 scripts/one_proof/autofold.py scratch/deg-det/autofold.json --dry-run`:
  `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`; the printed module
  (`scratch/deg-det/FoldDryRun.lean`, line 1 stripped) compiles: `'HDec.HSyn.sixContactMin_of_open36' depends on
  axioms: [propext, Classical.choice, Quot.sound]`.
* File sizes: `DegEqDetTate.lean` 7 KB, `Algebra.lean` 62 KB, `TateIndex.lean` 16 KB, `Reduction.lean` 15 KB,
  `KerDvd.lean` 13 KB (all under 150 KB).

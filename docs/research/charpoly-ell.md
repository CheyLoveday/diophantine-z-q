# charpoly-ell: `charPolyIndepOfEllAlgClosed` reduced to `deg φ = det T_ℓ(φ)`

Task charpoly-ell (2026-11-16), base origin/main 2880fef1 (fork main after leaf-fold31). Scratch:
`scratch/charpoly-ell/`. Contribution: `ZInQKernel/Contrib/OneProof/CharPolyIndepOfEllAlgClosed.lean` (namespace
`ZInQ.Contrib.OneProof.CharPolyEll`). Fold spec: `scratch/charpoly-ell/autofold.json`.

## 1. Result

**The field is not proved outright. It is reduced, with every step proved in Lean, to one new printed leaf plus a
field already open in its own bundle.** VERIFIED (compiled; axioms `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem ZInQ.Contrib.OneProof.CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate
    (hD : ZInQ.Contrib.OneProof.CharPolyEll.DegEqDetTate)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
```

* `DegEqDetTate` (**new LEAF, printed form**) is the *first* assertion of Mumford §19 Thm 4, `deg φ = det T_ℓ(φ)`,
  stated over a genuine Lean degree `degEnd`, the function-field degree. The field `charPolyIndepOfEllAlgClosed`
  is a specialization of the *second* assertion of the same theorem.
* `HomFreeFiniteAlgClosed` is the open field `homFreeFiniteAlgClosed` of the same bundle (`OpenTextbookLeaves12`;
  Mumford §19 Thm 3). Only `Module.Finite ℤ (End A)` is used from it, to get that `φ` is integral over `ℤ`.

Count: the fold removes `charPolyIndepOfEllAlgClosed` and adds `degEqDetTate`, **net 0** (dry run: strict
34/11 on 45 → 34/11 on 45, strictest 34/11 → 34/11). **The target (field removed, −1, no new leaf) is not met.**
Section 4 explains why the tree cannot supply the missing input today. The gap the frontier keeper named,
`deg φ = det T_ℓ(φ)`, is now the only input besides an open field, and it is a printed statement in its own right.

## 2. Statements

**The field** (`ZInQKernel/Contrib/AVB1/AlgClosed.lean:51`; bundle field
`HDec.HSyn.OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed`, `ZInQKernel/OneProof/H/TailZ42.lean:16`). A verbatim
copy `CharPolyEll.CharPolyIndepOfEllAlgClosedCopy` is in `scratch/charpoly-ell/CharPolyEll.lean`, with
`CharPolyIndepOfEllAlgClosedCopy = ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed := rfl` (compiled). For every
algebraically closed `k`, abelian variety `A` and `φ ∈ End A`, there is a monic `P ∈ ℤ[X]` such that for every
prime `ℓ` with `(ℓ : k) ≠ 0` and every finite basis `b` of `V_ℓ(A)`, the characteristic polynomial of the matrix of
`V_ℓ(φ)` is `P`.

**The degree** (new definition, genuine):

```lean
def degEnd {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) : ℕ :=
  if PkgI3.AbVar.IsIsogenyMor ψ.hom then
    letI := (ψ.hom.left.stalkMap (genericPoint A.X.left)).hom.toAlgebra
    Module.finrank (A.X.left.presheaf.stalk (ψ.hom.left (genericPoint A.X.left)))
      (A.X.left.presheaf.stalk (genericPoint A.X.left))
  else 0
```

For `ψ` finite and surjective (the tree's `IsIsogenyMor`), `ψ(η) = η` for the generic point `η`, so this is
`[K(A) : ψ^* K(A)]`, Mumford's degree of an isogeny. For any other `ψ` it is `0`, Mumford's convention for
non-isogenies in §19 (UNVERIFIED locator). For an endomorphism of an abelian variety, "isogeny" in Mumford's sense
(surjective with finite kernel) is the same as finite and surjective. Sanity checks, compiled: `degEnd_one :
degEnd 1 = 1`, and `degEqDetTate_one`: the leaf holds at `ψ = 1`, both sides being `1`.

**The new leaf:**

```lean
def DegEqDetTate : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ])).det =
          (degEnd ψ : ℚ_[ℓ])
```

**Rating: printed form.** D. Mumford, *Abelian varieties* (1970), §19, Theorem 4 (locator UNVERIFIED: no access to
the book from this host): for `φ ∈ End(X)`, `deg φ = det(T_ℓ φ)`. The ground field is algebraically closed
throughout the book. The only change from the print is that the determinant is taken on `V_ℓ = ℚ_ℓ ⊗ T_ℓ` in an
arbitrary finite basis, not on `T_ℓ`. Since `T_ℓ` is free of finite rank over `ℤ_ℓ` (Mumford §18; the kernel's
T26), the two determinants are equal. The statement uses the same `T_ℓ`, `V_ℓ`, `homT` and basis convention as the
field it replaces. It is never stronger than the print.
Proposed kinds.tsv row (from the autofold spec): bundle textbook, kind published, flag "unread: new printed leaf …;
locator UNVERIFIED". Proposed locators.md row: Mumford, *Abelian varieties*, §19 Thm 4, first assertion,
UNVERIFIED (same source as the field it replaces).

## 3. The proof (all glue, proved in Lean)

Fix `k`, `A`, `φ`, and let `f(n) = deg(n − φ) ∈ ℤ` for `n ∈ ℤ`.

1. **`T_ℓ` is a ring homomorphism** (`homTRingHom : End A →+* Module.End ℤ_ℓ (T_ℓ A)`, from `ptMap (f * g) =
   ptMap f ∘ ptMap g` and `ptMap 1 = id`). Composed with base change to `ℚ_ℓ` and `toMatrixAlgEquiv b`, it gives
   a ring homomorphism `rho b : End A →+* Matrix I I ℚ_ℓ` with `rho b ψ = toMatrix b b (V_ℓ ψ)` (`rho_apply`).
2. **Values at integers.** `charpoly(M).eval n = det(n − M) = det(rho b (n − φ)) = deg(n − φ)`, by
   `Matrix.eval_charpoly`, the ring-hom property and the leaf at `ψ = n − φ`.
3. **Rational coefficients** (`exists_rat_of_int_values`, for any field of characteristic 0): a polynomial taking
   integer values at all integers is the image of the Lagrange interpolant over `ℚ` at `0, …, natDegree`.
4. **Integer coefficients** (`exists_int_of_rat`). By `HomFreeFiniteAlgClosed`, `End A` is a finite `ℤ`-module, so
   `R(φ) = 0` for some monic `R ∈ ℤ[X]` (`IsIntegral.of_finite`), and `R(M) = rho b (R(φ)) = 0`. Over
   `Ω = AlgebraicClosure ℚ_ℓ`, every root `α` of `charpoly(M)` is in the spectrum of `M`, so `R(α)` is in the
   spectrum of `R(M) = 0` (`spectrum.subset_polynomial_aeval`), hence `R(α) = 0` and `α` is integral over `ℤ`. The
   coefficients of the split monic `charpoly(M)` are then integral over `ℤ` (`isIntegral_coeff_of_factors`). They
   are rational, and `ℤ` is integrally closed, so they lie in `ℤ`.
5. **Independence of `ℓ`** (`int_poly_ext`). For each `(ℓ, b)` the integer polynomial `Z_{ℓ,b}` of step 4 satisfies
   `Z_{ℓ,b}(n) = f(n)` for all `n`, so any two of them agree at infinitely many points and are equal. The proof
   takes `P` to be any monic `Z` with `Z(n) = f(n)` for all `n`, if one exists. Otherwise it takes `P = 1`; then no
   `(ℓ, b)` exists, since each one would give such a `Z`.

The pure-algebra lemmas (steps 3–5, `charpoly_eq_map_int`) are stated for any field of characteristic 0 and any
matrix, independently of abelian varieties.

## 4. Why not outright, and why the suggested shortcut fails

* **The tree has no theory of the degree.** It has no degree of an isogeny (grep: no definition of a degree or
  function-field degree on `PkgI3.AbVar`, before this task's `degEnd`). It has no theorem of the cube, no
  Riemann–Roch or Euler characteristic of line bundles on abelian varieties, and no comparison of `deg` with
  kernel orders (separable and inseparable degree). (VERIFIED, read.)
* **No open field supplies an `ℓ`-independent integer invariant of an endomorphism.** The other endomorphism
  statements (`homFreeFiniteAlgClosed`, `mumfordTorsionAlgClosed`, `milneIsogenyQuasiInverse`,
  `weilPairingMumford`, `phiAmpleIsogeny`) give the eigenvalue *set*, since `V_ℓ` is a faithful `End⁰ ⊗ ℚ_ℓ`-module
  and the minimal polynomial of `φ` is rational. They do not give the multiplicities on the `ℚ_ℓ`-factors of each
  `ℚ`-irreducible factor, which is exactly what `ℓ`-independence asserts. Some integer invariant such as `deg` is
  needed. (VERIFIED, math.)
* **The sketch "det(n − T_ℓφ) and deg(n − φ) agree for all integers n because both compute the order of the
  kernel on ℓ-power torsion" has a gap.** Counting the kernel on `A[ℓ^∞]` gives only the ℓ-part:
  `|det(n − T_ℓφ)|_ℓ = |deg(n − φ)|_ℓ`. Equality of ℓ-adic absolute values at every integer does not determine a
  monic polynomial. Example: for `ℓ ≡ 3 (mod 4)`, `X² + 1` and `X² + 1 + ℓ³` are both ℓ-adic units at every integer
  (and every ℓ-adic integer), because −1 is not a square mod ℓ, yet they differ (VERIFIED, math). Mumford's and
  Milne's proofs need two more facts. First, `deg` is a homogeneous polynomial function of degree `2g` on all of
  `End⁰(A)`, not only on `n − φ`, and is multiplicative. Second, a lemma comparing two multisets in `ℚ̄_ℓ` through
  `|∏ F(a_i)|_ℓ = |∏ F(b_i)|_ℓ` for all `F ∈ ℤ[T]`.

**What a Lean proof of `DegEqDetTate` would need** (not attempted; ratings are mine):

| piece | content | kind |
| --- | --- | --- |
| P1 | `deg` is a homogeneous polynomial function of degree `2g` on `End(A)`: theorem of the cube, plus `χ(ψ^*L) = deg ψ · χ(L)` and Riemann–Roch on `A` (Mumford §§6, 16, 19; numbering UNVERIFIED) | LEAF (printed) |
| P2 | `deg(ψχ) = deg ψ · deg χ` (tower law of function fields; Mathlib `Scheme.Hom.stalkMap_comp`, `Module.finrank_mul_finrank`) | GLUE, provable |
| P3 | for an isogeny `ψ` and `ℓ ≠ char k`, `v_ℓ(deg ψ) = v_ℓ(#ker ψ(k))` (separable degree = number of points in a fibre, inseparable degree a power of `p`; Mumford §§4, 7, UNVERIFIED) | LEAF (printed) |
| P4 | `#(ker ψ(k) ∩ A[ℓ^∞]) = |det T_ℓ ψ|_ℓ^{-1}`, from `A[ℓ^n] ≅ (ℤ/ℓ^n)^{2g}` (`mumfordTorsionAlgClosed`) and the surjectivity of `ψ` on points (ℓ-adic elementary divisors) | GLUE |
| P5 | P1 + P2 ⇒ `deg F(φ) = ∏ F(a_i)` on `ℤ[φ]`, plus the multiset lemma in `ℚ̄_ℓ` | GLUE |

This would trade one printed leaf (`DegEqDetTate`) for two (P1, P3) and much glue. That is worse for the count, so
the printed `DegEqDetTate` is the leaf recommended for crowdsourcing.

## 5. Compile record

* `lake build ZInQKernel.Contrib.AVB1.AlgClosed`: OK.
* `lake env lean scratch/charpoly-ell/CharPolyEll.lean`: OK, no `sorry`. `#print axioms` of
  `CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate` and of `CharPolyEll.degEqDetTate_one`:
  `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (`scratch/charpoly-ell/Discharges.lean`): see §6.
* `python3 scripts/one_proof/autofold.py scratch/charpoly-ell/autofold.json --dry-run`:
  `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`. The module it prints is in
  `scratch/charpoly-ell/FoldDryRun.lean` (line 1 stripped); compile result in §6.

## 6. `#discharges` and the dry-run fold

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.CharPolyIndepOfEllAlgClosed`: OK (13699 jobs, about 70 minutes on a shared host). It
prints `frozenTarget` with axioms `[propext, Classical.choice, Quot.sound]`.

`lake env lean scratch/charpoly-ell/Discharges.lean` (full output in `scratch/charpoly-ell/Discharges-output.txt`),
the line for this file:

```
DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate
  still assumes: [ZInQ.Contrib.OneProof.CharPolyEll.DegEqDetTate, ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2890 theorems checked, 8 discharge one
```

(`HomFreeFiniteAlgClosed` is an open field of the same bundle, so it stays as it is. `DegEqDetTate` is the new
leaf.)

`lake env lean scratch/charpoly-ell/FoldDryRun.lean` (the autofold dry-run module, line 1 stripped): OK. It prints
`'HDec.HSyn.sixContactMin_of_open36' depends on axioms: [propext, Classical.choice, Quot.sound]`.

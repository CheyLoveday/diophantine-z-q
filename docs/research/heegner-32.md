# heegner-32: the Heegner point of `C_d` without the canonical model of `X₀(32 d²)`

Status: research note (task heegner-32, 2026-11-16), branch `wip/heegner-32` (base 60a3fac7 + gz-weil ad22e947).
Lean: new files `ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd.lean` and
`ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd/{Used,Twist,Recip}.lean`. Nothing else under `ZInQKernel/` was
edited. Development copies, numerics, checks and log: `scratch/heegner-32/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network. **Every theorem number and locator of the
literature below is UNVERIFIED** (from memory).

---

## 0. Main results

**(A) Finding: `GZHL3.HeegnerPointRationalCd` is stronger than the chain needs, and its odd-`c` part cannot come from
level 32.**

* `HeegnerPointRationalCd` quantifies over every `c ∈ ℚ^×` with `c Λ_f ⊆ L` (`PeriodsIn`). Odd `c` really occur. For
  `d = 5` and `d = 13` the period lattice of `f_d` is all of `L(C_d)`, so `c = 1` is allowed (VERIFIED, numerical:
  `scratch/heegner-32/py/periods.py`, 12 periods each, with integer coordinates in a basis of `L` that include both
  basis vectors).
* Any route through the level-32 parametrization (gz-weil's twist `g Φ_d(τ) = Σ_a (a/d) Φ₁(τ + a/d)`, `g² = d`)
  reaches only `c ∈ 2ℤ`. The lattice of `32a1` is `((1 + i)/2) Λ₁`, and `z ↦ c z` maps `ℂ/g⁻¹L(32a1)` to `ℂ/L(C_d)`
  only for even `c`. For odd `c` the individual summands are only determined up to the kernel of a 2-isogeny.
* The chain uses only one `c`, the one that `ShimuraCMParamCd` supplies. `HeegnerPointRationalCdEven` (the same
  statement for `c ∈ 2ℤ`) suffices: `grossZagierHeegnerCd_of_even` proves `GZStatements.GrossZagierHeegnerCd` from
  `HeegnerPointRationalCdEven`, `GrossZagierFormulaCd` and `GrossConjugationCd`. The given `c` is replaced by
  `2·num(c)` (`periodsIn_two_num`). VERIFIED, compiled.

**(B) The even Heegner point without the canonical model.** The following compile (VERIFIED):

```lean
theorem ZInQ.Heegner32.heegnerPointRationalCdEven_of_twist (hT : TwistTransportCd) : HeegnerPointRationalCdEven
theorem ZInQ.Heegner32.twistTransportCd_of (hCM : T5Glue.ShimuraMainCM) (hL : TwistLatticeCd) : TwistTransportCd
theorem ZInQ.Heegner32.grossZagierHeegnerCd_of_lattice (hCM : T5Glue.ShimuraMainCM) (hL : TwistLatticeCd)
    (hGZ : GZHL3.GrossZagierFormulaCd) (hGC : GZHL3.GrossConjugationCd) : GZStatements.GrossZagierHeegnerCd
```

The proof has three parts:

1. **The analytic part, proved.** The parametrization of `C_d` at even `c` is a twisted sum of points of `X₀(32)`
   (`weierPt_two_eichlerCd`):
   `weierPt C_d L (2 Φ_d(τ)) = S_{λg}(Z(τ)) + S_{λ̄g}(Z(τ))`, where
   - `Z(τ) = Σ_{a mod d} (a/d)·(x, y)(τ + a/d) ∈ 32a1(ℂ)`, with `(x, y)` x0-32's eta-quotient parametrization;
   - `λ = (1 + i)/2`, `g = gaussD d`;
   - `S_μ(x, y) = (μ²x, μ³y)`.
2. **The level-32 Shimura reciprocity, already proved.** It comes from `hCM` through hx-used's eta route and
   theta-wp8's `ThetaWeierstrass8`.
3. **One algebraic GLUE statement, `TwistLatticeCd`.** It covers the conductor-`d` Heegner-point combinatorics and
   the genus character of `K(√d)/K`. It contains no analysis and no canonical model.

**(C) The smallest instance of the canonical model actually used** (the fallback, for the statement as given, all
`c`):

```lean
theorem ZInQ.Heegner32.heegnerPointRationalCd_of_used (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisParamCd) :
    GZHL3.HeegnerPointRationalCd
theorem ZInQ.Heegner32.x0ModuliGaloisParamCd_of_mero (h : GZHeegner.X0ModuliGaloisMero) : X0ModuliGaloisParamCd
```

`X0ModuliGaloisParamCd` is gz-heegner's `X0ModuliGaloisMero` restricted as follows:

* level `N` = the level of the newform of `C_d`, which is forced to be `32 d²`;
* `g ∈ {x∘φ, y∘φ, 1/(x∘φ − t)}` for the parametrization `φ = weierPt C_d L (c φ_f)`;
* Heegner points `τ_Q`, `τ_{Q'}` of level `N` and one odd fundamental discriminant.

**Effect on the counts (SPECULATIVE ratings).** On main, `hL3` is one composite GLUE.

* With (B), the `C_d` chain replaces it by:
  - `TwistLatticeCd` (GLUE, elementary);
  - `GrossZagierFormulaCd` (printed, constant forgotten);
  - `GrossConjugationCd` (printed).
* With (C), it replaces it by:
  - `X0ModuliGaloisParamCd` (consequence, GLUE);
  - the same two printed statements.

Both are strict-GLUE neutral against `hL3` (1 → 1). (B) has the property that the remaining GLUE needs no
literature: it is a statement about lattices and the Artin symbol of `√d`, provable in the project.

(Sections 1–6 below.)

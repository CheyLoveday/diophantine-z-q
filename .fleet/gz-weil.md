# gz-weil (fleet summary)

**Result.** On the route the proof uses (the curves `C_d : y² = x³ − d²x`), gz-hl3's composite leaves
`StrongWeilCurve` (Eichler–Shimura, rational Manin constant) and `IsogenyLattice` (Faltings, analytic form) are
gone, and no new leaf replaces them. Their only consumer, `GZHL3.ShimuraCMParamCd` (the analytic modular
parametrization of every `C_d`), is now a Lean theorem: `ZInQ.GZWeil.shimuraCMParamCd_proved`, with standard
axioms only.

The proof has four steps, all in Lean:
- the twist from `C_d` to `C₁` (Gauss sum of `(·/d)`, Tau Ceti's intertwining lemma, scaling of lattices);
- the uniformization of x0-32's eta-quotient model of `X₀(32)`: surjectivity of ℘, order of vanishing in place of
  ODE uniqueness, identity theorem, and the lattices `((1±i)/2)L`;
- x0-32's eta identity `x' = 4πi f y` from Jacobi's `dλ/dt = πiλθ₄⁴` plus a product identity;
- Jacobi's formula itself, by the classical modular proof: the theta functions are permuted by `SL₂(ℤ)`, and
  symmetric functions of the three log-derivative identities are level-one cusp forms of weight 4 and 8, which
  vanish by Mathlib's dimension formula.

By-product: x0-32's leaf `X0.EtaModelDifferential` is a theorem.

**Count.** The `C_d` split of `hL3` now has four leaves, against five for gz-hl3's `C_d` split and six for its
general split:
- `WeierstrassUniformization` (printed);
- `HeegnerPointRationalCd` (composite);
- `GrossZagierFormulaCd` (printed, constant forgotten);
- `GrossConjugationCd` (printed).

That is one composite instead of gz-hl3's two or three. Against `hL3` itself the composite count is neutral (1 → 1);
making it negative needs `HeegnerPointRationalCd`, which was outside this task. The general (all-`E`) form of `hL3`
is unchanged.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/{Weil,WeilParam,WeilTheta,WeilJacobi}.lean` (new files only);
  `lake build …WeilJacobi` succeeds.
- `scratch/gz-weil/Check.lean`: 26 theorems, standard axioms.
- `MainEdit.lean`: `frozenTarget_gzweil_final` = `frozenTarget` with `hL3` replaced by the four leaves above, via
  gz-statements' `C_d` chain; standard axioms.
- `#discharges` is recorded. It shows no direct discharge of `hL3`, because `hL3` is stated for all `E`; the
  integrator must swap `hL3` for the `C_d` chain (report §5).

**What remains.**
- `HeegnerPointRationalCd`.
- `WeierstrassUniformization` could also go on the `C_d` route, via `g₂(ℤ[i]) ≠ 0`; not attempted.
- Report: `docs/research/gz-weil.md`.

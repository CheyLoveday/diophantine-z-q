# gz-heegner results log

Task: prove `ZInQ.GZHL3.HeegnerPointRational` (gz-hl3) from `T5Glue.ShimuraMainCM` and
`T5Glue.X0ModuliGalois` plus glue.

## 2026-11-15
- Build: copied `.lake/build` and `lean/.lake/build` from ~/dzq-wt/gz-hl3 (bbb6c764; no ZInQKernel diff vs base c118e9d2).
- FINDING (analysis, SPECULATIVE until written up): `X0ModuliGalois` only covers `g` with
  `IsRatModFn N g`, whose third clause is a `q`-expansion valid on all of `ℍ` (so `g` is holomorphic on `ℍ`).
  The coordinates `x∘φ`, `y∘φ` of a modular parametrization `φ = weierPt E L (c·φ_f)` have poles at the
  non-cuspidal points of `φ⁻¹(O)` (nonempty unless every preimage of `O` is a cusp, e.g. deg φ > #cusps over O),
  so they are not `IsRatModFn`; no regular-on-ℍ rational function on `X₀(N)` built from `φ` is available without
  the algebraic theory of `X₀(N)_ℚ`. Plan: state the printed form of the canonical-model theorem for every
  `g ∈ ℚ(X₀(N))` regular at the two points (`X0ModuliGaloisMero`), derive `X0ModuliGalois` from it, and derive
  `HeegnerPointRational` from it and `ShimuraMainCM` (via kernel `CMModuli`).
- VERIFIED (compiled, `lake env lean scratch/gz-heegner/Heegner.lean`, axioms [propext, Classical.choice, Quot.sound]):
  `ZInQ.GZHeegner.heegnerPointRational_of (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero)
   (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion) (hJ : HeegnerClassJ) : ZInQ.GZHL3.HeegnerPointRational`.
  Proved glue in the file: `exists_compose` (Dirichlet composition `J·Q'.lat = Q.lat`, `J·Q'.latN = Q.latN`, residue kept;
  sympy check 401/401 for the sign `B' ≡ −b (mod 2a)`, `py/compose.py`; the other sign fails 285/401),
  `pairHom_of_equiv` / `equiv_of_pairHom` (homothetic lattice pairs ⇔ Γ₀(N)-equivalent), `exists_galQ_of_sigma`,
  `mem_kappa_of_fixed` (fixed field of Aut(ℂ/κK) is κK), `weierPt_add`, `point_transport` (poles handled with
  `1/(x∘φ − t)`), `heegnerC_fixed` (σ permutes the Heegner points; injectivity on classes).
  Open glue Props: `ParamRegular`, `ParamCuspGrowth`, `ParamQExpansion` (analysis of x∘φ), `HeegnerClassJ` (class group).
- VERIFIED (compiled): `x0ModuliGalois_of_mero : X0ModuliGaloisMero → T5Glue.X0ModuliGalois` (via
  `regularAt_of_hasSum`: a `q`-expansion valid on all of ℍ gives holomorphy, radius ≥ 1 from `le_radius_of_tendsto`).
  So a fold may replace the kernel leaf `X0ModuliGalois` by `X0ModuliGaloisMero`.
- VERIFIED (compiled): `heegnerClassJ : HeegnerClassJ` (Tau Ceti Chebotarev in the Hilbert class field, copy of
  `RingClassTwo.exists_prime_picClass_eq` for the maximal order; Redei `prime_trichotomy`; split/ramified prime
  `𝔭 = ⟨p, θ − r⟩` by `ℤ + ℤθ` coordinates; inert prime principal ⇒ class 1 ⇒ `J = 𝓞_K`). Dev copy `ClassJ.lean`.
  Remaining open glue: `ParamRegular`, `ParamCuspGrowth`, `ParamQExpansion` (analysis of the coordinates of φ).
- VERIFIED (lake build): contributor file `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean`
  (imports GrossZagierHeegner + RingClassLattice; 69 KB). `#discharges` output in `discharges-output.txt`:
  `[hL3] by ZInQ.GZHeegner.grossZagierHeegner_of_printed` (assumes gz-hl3's 5 other leaves, ShimuraMainCM,
  X0ModuliGaloisMero, ParamRegular, ParamCuspGrowth, ParamQExpansion) and `[hX] by x0ModuliGalois_of_mero`.
- Count (kinds.tsv convention: strict GLUE = kind not `published`): HeegnerPointRational (composite) −1;
  hX → X0ModuliGaloisMero (both consequence) 0; ParamRegular/CuspGrowth/QExpansion (glue) +3 while unproved.
  So the analytic glue must be proved for a net decrease. Next: prove them.
- VERIFIED (compiled, scratch `Analytic.lean`): `paramRegular : ParamRegular` (℘, ℘' meromorphic everywhere via
  `weierstrassPExcept`; `1/(℘ − c₀)` analytic at lattice points (value 0); φ_f = Σ aₙ/n qⁿ with radius ≥ 1 from the
  q-expansion of f converging on |q| < 1 (Mathlib `hasSum_qExpansion`, Tau Ceti `one_mem_strictPeriods_Gamma1_map`)).

# theta-glue results log

## 2026-11-14

- Setup: `.lake/build` and `lean/.lake/build` copied from the t5-glue worktree (its ZInQKernel tree differs
  from this base only in TailZ10-Z15, Main, Contrib/TYZGenus/CM.lean, none upstream of TailA).
  `lake env lean scratch/theta-glue/T0.lean` (imports `ZInQKernel.OneProof.H.TailA`) COMPILES, 14 s.
- No sympy available (no `~/pyenv`, no network): exact algebra uses `py/poly.py` (pure-python
  multivariate polynomials over Q, `fractions`).
- `py/dup_num.py` (VERIFIED, computed, double precision, 5 random Ω ∈ 𝔥₂, all 10 even chars):
  duplication formula in the project's convention (`thetaConst m Ω = Σ_n exp(πi vᵀΩv + πi v·b)`,
  `v = n + a/2`): `θ[a;b](Ω)² = Σ_{c ∈ {0,1}²} (−1)^{(c⊕a)·b} U_c U_{c⊕a}`, `U_c = θ[c;0](2Ω)`;
  worst relative error 1.2e-15.
- `py/dup_sym.py` (VERIFIED, exact): with `θ_m² = S_m(U)` (the ten explicit quadratic forms above),
  `4 Σ_m S_m⁸ − (Σ_m S_m⁴)² = 0` in `Q[U0..U3]`. So `ThetaEightSquare` follows from the duplication
  formula by a degree-16 polynomial identity.
- `Dup.lean` (imports `ZInQKernel.OneProof.H.TailA`) COMPILES, ~14 s, no sorry; `#print axioms` =
  [propext, Classical.choice, Quot.sound] (VERIFIED):
  * `summable_norm_thetaTerm`: absolute convergence of every theta series on `𝔥₂` (bound
    `(y₀₀+y₁₁)q_Y(x) − det Y |x|² = (y₀₀x₀+y₀₁x₁)² + (y₀₁x₀+y₁₁x₁)²`, Mathlib's `jacobiTheta₂` majorant);
  * `dupEquiv`: the change of variables `(c,k,l) ↦ (l+k+c(1−a), l−k−ca)` as an `Equiv`;
  * `thetaConst_sq_eq` (**duplication formula**): `θ[a;b](Ω)² = Σ_c exp(πi (c⊕a)·b) θ[c;0](2Ω) θ[c⊕a;0](2Ω)`
    for `IsSiegel Ω`;
  * `sq0`..`sq9`: the ten explicit squares `θ_m² = S_m(U)`; `evenChars_eq` (decide);
  * `thetaEightSquare'`: `∀ Ω, IsSiegel Ω → Σ_m θ_m¹⁶ = (Σ_m θ_m⁸)²/4` — **ThetaEightSquare PROVED**.
- `py/jtrans.py` (VERIFIED, numeric): `U(−Ω⁻¹) = s·(H/2)·U(Ω)`, `s² = det(−iΩ)`, `H` the 4×4 Hadamard
  matrix `(−1)^{c·d}`.
- `py/invariants.py` (VERIFIED, exact): polynomials of degree `2k` in `U` invariant under
  `U₁₀,U₁₁ ↦ iU₁₀,iU₁₁`; `U₀₁,U₁₁ ↦ iU₀₁,iU₁₁`; `U₁₁ ↦ −U₁₁`; permutations of `U₀₁,U₁₀,U₁₁`; `H/2`
  (the images of generators of `Sp₄(ℤ)`): dimensions 1,1,1,2,3,2,4 in weights 4,6,8,10,12,14,16 = Igusa's
  `dim M_k(Sp₄(ℤ))` (generating function `1/((1−t⁴)(1−t⁶)(1−t¹⁰)(1−t¹²))`).
- `py/igusa2.py` (VERIFIED, exact in `Q[U]`): `ψ₄ = Σθ⁸/4` and `χ₁₀ = −∏θ²/2¹⁴` are invariant;
  `ψ₄|diag = E₄⊗E₄`, `χ₁₀|diag = 0`; the normalized weight-6 invariant `ψ₆` has `ψ₆|diag = E₆⊗E₆`;
  the weight-12 form with `χ₁₂|diag = Δ⊗Δ` **equals Igusa's theta expression**
  `2⁻¹⁷3⁻¹ Σ_{15 Göpel quadruples Q} ∏_{m∉Q} θ_m⁴` exactly.
- `py/signs.py` (VERIFIED, exact): the ten `θ_m⁴` are permuted with signs by the generators; invariance
  forces the signs `ε_T` in `ψ₆ = 2⁻² Σ_{60 syzygous T} ε_T (θ_{m₁}θ_{m₂}θ_{m₃})⁴` uniquely (group transitive
  on the 60 triples), and with them the theta expression equals `ψ₆` exactly (`py/psi6_signs.pkl`).
  Igusa's printed sign convention itself: UNVERIFIED (no access to the paper).
- `py/curve_check.py` (VERIFIED, 80 digits, 12 random τ on the Lean curve `Ω(τ)`): Lin–Yang's
  relations hold: `ψ₄ψ₆ = 2¹²3⁵χ₁₀` (rel. res. ≤ 9e-78) and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂` (≤ 5e-75), and
  `j_θ = ψ₆²/ψ₄³` (≤ 3e-73).

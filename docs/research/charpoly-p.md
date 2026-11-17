# charpoly-p: `charPolyIndepOfEllAlgClosed` in characteristic `p`

Task charpoly-p, 2026-11-17. Base: main `0fcc7e36`, with origin/wip/degpoly-proof `0a9e6698` merged in. That
branch carries the charpoly-ell, deg-det and degpoly-proof contributions under `ZInQKernel/Contrib/OneProof/`.
Scratch: `scratch/charpoly-p/` (the results log is `log.md`).

Marks: VERIFIED means read in a source, computed or compiled. STANDARD means published, with an exact
reference. SPECULATIVE means unchecked. There is no network here, so every theorem number recalled from memory
is UNVERIFIED.

## 1. Verdict

**The field is not proved in characteristic `p`.** Two results came out of the attempt.

1. **New Lean (VERIFIED, standard axioms; see §4 for the compile record).** The field follows from the
   polynomiality of the degree alone. The finiteness of `End(A)` over `ℤ` (Mumford §19 Thm 3, which the lead's
   plan listed as step 2) is not needed:

   ```lean
   theorem ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'
       (HR : DegPolyC.DegHomogPolyNoEmb) : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
   theorem ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
       (hP : DegDet.DegHomogPoly) : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
   ```

   - `DegHomogPolyNoEmb` is degpoly-proof's printed-form leaf: `deg` is a homogeneous polynomial function of
     degree `2g` on `End(A)`, for algebraically closed `k` with no ring homomorphism to `ℂ`.
   - On fields that do embed in `ℂ`, degpoly-proof's period-lattice proof applies. It uses
     `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed_proof`, both proved on main.

   The swap is count-neutral: one field out, one leaf in. The leaf it leaves is exactly the first milestone of
   the lead's plan, and step 2 drops out. Before this, the deg-det route needed `DegHomogPolyNoEmb` together with
   `homFreeFiniteAlgClosed`. The latter is no longer an open field on main, so that route cost +1.

2. **Survey: the tree has more of the foundations than expected, but not all of them.** The vendored
   AnthropicFLT copy under `ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT` proves several of the
   inputs (§2):
   - the theorem of the cube;
   - a Snapper-type polynomiality of `χ(M ⊗ L^n)`;
   - the leading-coefficient form of `χ(f^*L^m) = deg f · χ(L^m)` for finite flat `f`;
   - `deg [n] = n^{2g}`;
   - a symmetric line bundle with positive leading coefficient.

   The vendored Jacobian-Challenge library (CloudW07) adds coherent cohomology, finiteness on proper schemes and
   flat base change.

   One published input is missing (M1, §3): for a homomorphism `ψ` that is not an isogeny, `χ(ψ^*L) = 0`. This
   is a consequence of Mumford §16 (Riemann–Roch, `χ(L)² = deg φ_L`). Large glue is also missing: bridges
   between the tree's `degEnd` and AnthropicFLT's `RelativeGroupLaw.endDegree` and Čech `eulerChar`, the
   quadratic formula in `Pic` from the cube, and joint polynomiality in several exponents.

   §6 compiles a finer split of `DegHomogPoly` into four Euler-characteristic statements over genuine tree
   definitions (`ChiDecomp.lean`, `charPolyIndepOfEllAlgClosed_of_chi`). Three of them are in the tree up to
   framework bridges; the fourth contains M1.

   So the first milestone ("`deg(nφ − m)` is a polynomial of degree `2g` in `(n, m)`, in characteristic `p`") is
   not reachable in this task. Per the pivot signal, §3 reports the missing inputs, what the tree has, and the
   smallest printed statements that would close the gap.

## 2. Survey: what the libraries have (theorem of the cube, χ, deg(f^*L))

Method:
- Mathlib 4.35: grep over the local checkout.
- The tree: a code-search subagent read candidate files found by filename globs (no content grep of the whole
  tree, so absence claims are not exhaustive). I then read the key statements myself.

| input | where | status |
| --- | --- | --- |
| coherent cohomology `H^n(X, M)` of `X.Modules`, `finrankH`, `eulerChar` | CW07 `Jacobian/AlgebraicGeometry/Cohomology/Basic.lean` (Ext over Mathlib's `Sheaf.H`) | definitions (VERIFIED read) |
| finiteness of `H^q` for coherent modules on proper schemes over noetherian `A` | CW07 `Cohomology/Proper.lean`, `Scheme.Modules.hasFiniteH_of_isProper` | proved |
| Riemann–Roch, Serre duality, degree on smooth proper curves | CW07 `Curve/CanonicalDegree.lean` etc. | proved (curves only) |
| **theorem of the cube** `(fgh)^*L ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ (fg)^*L ⊗ (fh)^*L ⊗ (gh)^*L` | AnthropicFLT `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso.lean` (k algebraically closed; proper smooth geometrically connected commutative group object; `f g h : Y → A`) | proved (VERIFIED statement read) |
| seesaw (three slices) | `…nonempty_iso_tensorUnit_of_pullback_three_slices` | proved |
| `n^*L ≅ L^{n²}` for symmetric `L` | `…nonempty_pullback_zpow_iso_tensorPow_of_symmetric` | proved |
| Snapper-type: `χ(M ⊗ L^n)` polynomial in `n` of degree `≤ dim supp M` (Čech `eulerChar` over an ordered affine cover) | `OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq` | proved (VERIFIED statement read) |
| leading coefficient: `coeff_d χ(F ⊗ L^m) = (generic rank of F) · coeff_d χ(L^m)` | `OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq` | proved (VERIFIED statement read) |
| `deg [n] = n^{2g}` (`(n : K) ≠ 0`) | `RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero` | proved |
| symmetric invertible `𝓛` with `coeff_g χ(𝓛^m) > 0` | `RelativeGroupLaw.exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq` | proved (VERIFIED statement read) |
| `PkgI3.AbVar`-style group object → AnthropicFLT `RelativeGroupLaw` | `CloudB3W16Torsion/RelativeBridges.lean` (`relativeLaw`) | proved (bridge used for `mumfordTorsionAlgClosed_proof`) |
| theorem of the square | `PicDict.MumfordSquareAC` | proved from L1, L2 only (`PhiSurj.mumfordSquareAC_of_open`) |
| `χ(ψ^*L) = 0` (or its leading coefficient) for a non-isogeny `ψ`; Leray; Mumford §16 RR `χ(L)² = deg φ_L` | — | **not found** |
| joint polynomiality of `χ(⊗ N_k^{a_k})` in several exponents | — | **not found** (single-variable only) |
| `χ(f^*L) = deg f · χ(L)` in full | — | not found (leading-coefficient form only) |
| "deg is a polynomial function on `End(A)`" | — | **not found** |

Mathlib 4.35 itself has no theorem of the cube, seesaw, Riemann–Roch, Snapper or Hilbert polynomial of sheaves,
intersection numbers or `χ(f^*L)` (VERIFIED by grep). It has abelian sheaf cohomology on sites
(`CategoryTheory.Sheaf.H`) and `Polynomial.hilbertPoly` for series only.

## 3. The three items of the pivot signal

**(a) Missing inputs** for `DegHomogPoly` in characteristic `p`, via Mumford's proof (`deg f · χ(L) = χ(f^*L)`,
the cube makes `x ↦ (∑ xᵢ eᵢ)^*L` quadratic in `Pic`, and `χ` is polynomial):

- **M1 (published consequence, missing):** for `ψ ∈ End(A)` not an isogeny and `L` invertible,
  `χ(ψ^*L^m) = 0` for all `m`. A leading-coefficient version would do: `coeff_g` of the χ-polynomial of
  `ψ^*L` is `0`.
  - Source: Mumford §16, Riemann–Roch `χ(L)² = deg φ_L` (UNVERIFIED locator), with
    `φ_{ψ^*L} = ψ̂ ∘ φ_L ∘ ψ` not an isogeny.
  - Without M1, the polynomial `x ↦ c_g((∑ xᵢ eᵢ)^*L)/c_g(L)` agrees with `deg` only at the isogenies. The
    algebra (multiplicativity, the `ℓ`-adic comparison) breaks at the non-isogenies. §5 explains why no
    density argument replaces M1.
- **Glue, each a project-size formalization:**
  - G1: `degEnd ψ = endDegree` of the bridged `RelativeGroupLaw` (function-field degree = rank of `ψ_*𝒪` =
    rank of the kernel). Isogenies are flat (MilneQuasiInverse `finite_surjective_abVarHom_flat`); Mathlib has
    `Scheme.Hom.finrank`.
  - G2: `χ(ψ^*L^m) = χ(ψ_*𝒪 ⊗ L^m)` for finite `ψ` (projection formula, affine pushforward), feeding the
    leading-coefficient theorem.
  - G3: the cube gives that `x ↦ [(∑ xᵢ eᵢ)^*L]` is quadratic in `Pic(A)`.
  - G4: joint polynomiality of `χ(⊗ N_k^{a_k})`. It follows from the single-variable theorem with
    `M = ⊗_{k≠k₀} N_k^{a_k}` coherent, since separately polynomial of bounded degree implies jointly polynomial
    (Lagrange interpolation).
  - G5: homogeneity of degree `2g` from `deg [m] = m^{2g}` and multiplicativity.
  - G6: transport between CW07/PkgI3 `X.Modules` and AnthropicFLT's `OModulePresheaf` Čech `eulerChar`.

**(b) What the tree already has:** everything in the §2 table, and the Lean of this task and of
charpoly-ell, deg-det and degpoly-proof. All of Mumford's proof of §19 Thm 4 except the polynomiality of `deg`
is now in Lean, and so is the field over every field that embeds into `ℂ`.

**(c) The smallest printed statement that would close the gap:** `DegPolyC.DegHomogPolyNoEmb`.
- It is degpoly-proof's specialization of deg-det's `DegHomogPoly` (Mumford §19: `deg` is a homogeneous
  polynomial function of degree `2g` on `End X`; locator UNVERIFIED).
- With this task's theorem it is the only input. Rating: printed form, a ∀-specialization of the printed
  statement, never stronger.
- Below it, given the tree's AnthropicFLT results, the only further published input needed is M1. The rest is
  glue G1–G6.

## 4. What compiles (all VERIFIED; axioms `propext`, `Classical.choice`, `Quot.sound`)

New files under `ZInQKernel/Contrib/OneProof/`:

- **`CharPolyCharP/Algebra.lean`** (imports deg-det's `DegEqDetTate/Algebra.lean`, which imports only Mathlib).
  - `eq_Rs_of_mul_trunc`: a function `L[X] → L`, multiplicative on pairs of total degree `≤ D`, with `Φ(c) = cⁿ`
    and `Φ(X − r) = (−1)ⁿ P(r)`, equals `F ↦ ∏_{P(a)=0} F(a)` on polynomials of degree `≤ D`.
  - `NtD`, `NtD_mul`: a polynomial function `N` on the coefficients `0..D`. If it is multiplicative on integer
    polynomials of degrees `≤ a, ≤ b` (`a + b ≤ D`, nonzero values), then it is multiplicative on such pairs over
    every `ℚ`-algebra (Combinatorial Nullstellensatz, as in deg-det's `Nt_mul`).
  - `P0D_monic`: `P₀(t) = N(t − X)` is monic of degree `n`.
  - `mult_le_of_norm_Rs_le_bdd`, `eq_of_norm_RsZ_le_bdd`: deg-det's one-sided comparison lemma, with test
    polynomials of degree `≤ deg Q` only (they approximate `ℓ^s μ + ℓⁿ`, `μ ∣ Q`).
  - `norm_roots_le_one`, `exists_int_poly_of_Rs`: if `∏_{P(a)=0}(a^m − q)` is an integer for all primes `q` and
    all `m`, the monic `P ∈ ℚ[X]` lies in `ℤ[X]`. Roots in `ℚ̄_q` of absolute value `> 1` would give `q`-adic
    absolute value `≥ |a₀|^m |q|^K → ∞`. The step from coefficients to `ℤ` goes through `PadicInt.isUnit_den`.
  - `charpoly_eq_P0D`: `charpoly ρ(φ) = P₀` with no relation for `φ` (any `D ≥ n`).
  - `P0D_int`: `P₀ ∈ ℤ[X]` from `N` on polynomials of every degree in `φ` (`deg(φ^m − q) ∈ ℕ`).
- **`CharPolyCharP.lean`** (imports the above, degpoly-proof's `DegHomogPolyC`, `MumfordTorsionAlgClosed`,
  `UniformizationLeafAll`).
  - `DegPolyAt A` (deg-det's `DegHomogPoly` at one `k, A`).
  - `charPoly_of_degPoly : DegPolyAt A → ∀ φ, ∃ P ∈ ℤ[X] monic, ∀ ℓ ≠ char k, charpoly V_ℓ(φ) = P`. It uses deg-det's
    `card_basis_V`, `norm_deg_le_norm_det` (KerDvd + TateIndex), `degEnd_mul_of_isIsogeny`, charpoly-ell's
    `rho`, `degEnd_one`, and `mumfordTorsionAlgClosed_proof`.
  - `charPolyIndepOfEllAlgClosed_of_degHomogPoly'`, `charPolyIndepOfEllAlgClosedNoEmb_of_degHomogPolyNoEmb`,
    `charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'`.

Checks:

- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.CharPolyCharP`
  exits 0.
- `#discharges` (`scratch/charpoly-p/Discharges.lean`, output `Discharges-output.txt`):

  ```
  DISCHARGES [OpenTextbookLeaves17.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'
    still assumes: [ZInQ.Contrib.OneProof.DegPolyC.DegHomogPolyNoEmb]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenTextbookLeaves17.charPolyIndepOfEllAlgClosed] by ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
    still assumes: [ZInQ.Contrib.OneProof.DegDet.DegHomogPoly]
    axioms: [propext, Classical.choice, Quot.sound]
  ```

- Autofold spec `scratch/charpoly-p/autofold.json`: field `charPolyIndepOfEllAlgClosed` out, leaf
  `degHomogPolyNoEmb` in.
  - Kind: published.
  - Flag: unread; ∀-specialization of deg-det's printed `DegHomogPoly`; the characteristic-`p` case is used;
    locator UNVERIFIED.
  - Dry run: `strict count: 15/16 on 31 -> 15/16 on 31; strictest 15/16 -> 15/16` (count-neutral).
    `FoldDryRun.lean` (`sixContactMin_of_open59` over TailZ65) compiles with standard axioms.
  - The fold needs the files of charpoly-ell (`CharPolyIndepOfEllAlgClosed.lean`), deg-det (`DegEqDetTate.lean`
    and `DegEqDetTate/`) and degpoly-proof (`CharPolyLattice.lean`, `DegHomogPolyC.lean`). This branch carries
    them through its merge of origin/wip/degpoly-proof, unchanged.
- `scratch/charpoly-p/M1Statement.lean` compiles. It states M1 (`NonIsogPullbackEulerZero`) and
  `EulerPullbackDeg` over CW07's `Scheme.Modules.eulerChar`, AnthropicFLT's `Scheme.Modules.IsInvertible`,
  Mathlib's `Scheme.Modules.pullback` and `CharPolyEll.degEnd`.

**Rating of the new leaf** `DegHomogPolyNoEmb`: printed form. It is a ∀-instance (fields with no embedding into
`ℂ`) of deg-det's `DegHomogPoly`, which reads Mumford §19's "deg is a homogeneous polynomial function of degree
`2g` on `End X`" in the coordinates of a finite family. That is a composite with a linear map `ℤ^r → End X`, so a
consequence, never stronger. Locator UNVERIFIED (Milne, *Abelian varieties*, §12 has the same statement;
UNVERIFIED).

## 5. Why M1 is not avoidable by the tree's leading-coefficient tools

Let `Q(x) = c_g((∑ xᵢ eᵢ)^*L) / c_g(L)`. It is a polynomial, homogeneous of degree `2g` by `[m]^*L ≅ L^{m²}`.
At isogenies it equals `deg`. deg-det's algebra needs three things at every non-isogeny `ψ` in `ℤ[φ]`:
- multiplicativity on nonzero values;
- `|deg ψ|_ℓ ≤ |det ρ ψ|_ℓ`, where `det ρ ψ = 0` for a non-isogeny;
- agreement with `deg` at integer points.

All three need `Q(ψ) = 0` there, which is M1. A Zariski-density argument would need the isogenies to be dense
in the family's coordinates. That is the statement `deg(t − φ) ≠ 0` for large `t`, which is the polynomiality
itself.

## 6. A finer decomposition of `DegHomogPoly` (compiled; for crowdsourcing, not for folding)

The file is `ZInQKernel/Contrib/OneProof/CharPolyCharP/ChiDecomp.lean` (scratch copy `scratch/charpoly-p/ChiDecomp.lean`),
VERIFIED with standard axioms. It splits Mumford's proof of the polynomiality at the Euler characteristic. The
statements are over genuine tree definitions:
- `χ` is CW07's coherent-cohomology `Scheme.Modules.eulerChar` over `k` (on `A.X.left` with `A.X.hom`);
- invertibility is AnthropicFLT's `Scheme.Modules.IsInvertible` (locally trivial);
- pullback is Mathlib's `Scheme.Modules.pullback`;
- `deg` is charpoly-ell's `degEnd`.

| statement | content | rating | tree support |
| --- | --- | --- | --- |
| `EulerPullbackDegAt A` | `χ(ψ^*L) = deg ψ · χ(L)` for all `ψ ∈ End A`, `L` invertible | consequence of printed theorems: Mumford §12 (isogenies) and §16 Riemann–Roch (non-isogenies: both sides `0`); locators UNVERIFIED | leading coefficient of the isogeny case in AnthropicFLT (Čech χ); the non-isogeny case is M1, **not in the tree** |
| `ChiPullbackPolyAt A` | `x ↦ χ((∑ xᵢ eᵢ)^*L)` is a polynomial on `ℤ^r` | composite of printed theorems: cube (Mumford §6/§10) and Snapper/RR (Kleiman 1966, Mumford §16); UNVERIFIED | cube proved (AnthropicFLT); one-variable Snapper proved; bridges and joint polynomiality are glue |
| `ExistsChiNeZeroAt A` | some invertible `L` has `χ(L) ≠ 0` | consequence of printed theorems: projectivity (Mumford §6 App. 1) and §16; UNVERIFIED | AnthropicFLT: symmetric `𝓛` with positive leading coefficient (Čech χ; bridge is glue) |
| `DegMulNDimAt A` | `∃ g, dim A = g` and `deg [m] = m^{2g}` for `(m : k) ≠ 0` | printed (Mumford §4); UNVERIFIED | AnthropicFLT `endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero` (bridge `degEnd = endDegree` is glue G1) |

Proved theorems:

- `degPolyAt_of_chi : EulerPullbackDegAt A → ChiPullbackPolyAt A → ExistsChiNeZeroAt A → DegMulNAt A g → DegPolyAt A`.
  - `deg = χ(·^*L)/χ(L)` at integer points.
  - Homogeneity: `deg(mψ) = m^{2g} deg ψ` follows from `(mψ)^*L ≅ ψ^*[m]^*L` (`Scheme.Modules.pullbackComp`) and
    `EulerPullbackDegAt` at the invertible `[m]^*L`. Then `eval_eq_homogeneousComponent` shows that a rational
    polynomial scaling like `m^n` for infinitely many `m` agrees at integer points with its degree-`n` component.
    `infinite_natCast_ne_zero` supplies infinitely many such `m` (`m ≡ 1 mod char k`).
- `charPolyIndepOfEllAlgClosed_of_chi`: the field from the four, each restricted to fields with no ring
  homomorphism to `ℂ`.
- `#discharges` (`scratch/charpoly-p/Discharges2-output.txt`) shows that it discharges the field and still
  assumes exactly these four.

This trades one leaf for four, so it is not proposed as a fold. Its use is as a map: three of the four are in
the tree's vendored AnthropicFLT up to framework bridges. These are G1 (`degEnd` versus `endDegree`) and G6
(CW07 χ versus AnthropicFLT's Čech χ over an ordered affine cover; AnthropicFLT has
`OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated`, not read). The one published
input the tree lacks is M1, the non-isogeny half of `EulerPullbackDegAt`.

Sanity checks (math):
- If `dim A = 0`, then `A` is a point and every statement holds with `g = 0`.
- For `ψ = 0` and `g ≥ 1`, `χ(0^*L) = χ(𝒪_A) = 0 = deg 0 · χ(L)`.
- The degree in CW07's `eulerChar` is a `finsum`. It is correct here because `H^q` vanishes above `dim A`
  (Grothendieck) and is finite-dimensional on proper `A` (CW07 `hasFiniteH_of_isProper`).

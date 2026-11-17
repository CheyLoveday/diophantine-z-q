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

## 4. What compiles

(Filled in from the log once the build finishes.)

## 5. Why M1 is not avoidable by the tree's leading-coefficient tools

Let `Q(x) = c_g((∑ xᵢ eᵢ)^*L) / c_g(L)`. It is a polynomial, homogeneous of degree `2g` by `[m]^*L ≅ L^{m²}`.
At isogenies it equals `deg`. deg-det's algebra needs three things at every non-isogeny `ψ` in `ℤ[φ]`:
- multiplicativity on nonzero values;
- `|deg ψ|_ℓ ≤ |det ρ ψ|_ℓ`, where `det ρ ψ = 0` for a non-isogeny;
- agreement with `deg` at integer points.

All three need `Q(ψ) = 0` there, which is M1. A Zariski-density argument would need the isogenies to be dense
in the family's coordinates. That is the statement `deg(t − φ) ≠ 0` for large `t`, which is the polynomiality
itself.

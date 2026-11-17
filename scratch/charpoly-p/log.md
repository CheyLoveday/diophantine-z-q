# charpoly-p results log

Base: main 0fcc7e36 (origin/main = main, merge no-op), merged origin/wip/degpoly-proof 0a9e6698
(brings charpoly-ell, deg-det, degpoly-proof contributions under ZInQKernel/Contrib/OneProof/).

## Survey (11-17)
- Mathlib 4.35: abelian sheaf cohomology on sites (`CategoryTheory.Sheaf.H`, Ext-based; Cech, Mayer–Vietoris),
  `Algebra/Homology/EulerCharacteristic.lean` (chain complexes only). No theorem of the cube, seesaw,
  Riemann–Roch, Snapper/Hilbert polynomial of sheaves, intersection numbers, χ(f^*L). VERIFIED (grep).
- Tree, vendored frenzymath Jacobian-Challenge (ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/):
  `Scheme.Modules.H`, `finrankH`, `eulerChar` (Cohomology/Basic.lean), finiteness for coherent modules on
  proper schemes (Cohomology/Proper.lean `hasFiniteH_of_isProper`), flat base change, Serre vanishing on
  projective space, curve Riemann–Roch / genus / line bundle degree on curves, Picard functor + Poincaré
  bundle for curves, rigidity. VERIFIED (read headers).
- Tree, vendored AnthropicFLT under ZInQKernel/Contrib/CloudB3W16Torsion/Vendor/AnthropicFLT (VERIFIED: statements read;
  proofs are p2m wrappers of P2M/Sol bodies, built as part of mumfordTorsionAlgClosed_proof's closure):
  * theorem of the cube `Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso` (k alg. closed, proper smooth
    geometrically connected commutative group object, L invertible, f g h : Y → A);
  * seesaw (three slices) `Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices`;
  * symmetric L: `nonempty_pullback_zpow_iso_tensorPow_of_symmetric` (n^*L ≅ L^{n²});
  * Snapper-type: `OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq` (χ(M ⊗ L^n) polynomial in n
    of degree ≤ dim supp M; Čech χ over an ordered affine cover; L locally trivial);
  * leading coefficient: `OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq`
    (coeff_d χ(F ⊗ L^m) = generic rank of F · coeff_d χ(L^m), V integral, dim V ≤ d);
  * `RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero` (deg [n] = n^{2g}, (n:K) ≠ 0);
  * `RelativeGroupLaw.exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq`
    (symmetric invertible 𝓛 with coeff_g χ(𝓛^m) > 0).
  Not found: χ(ψ^*L) (or its leading coefficient) = 0 for a non-isogeny ψ (Leray / Mumford §16 RR); joint
  polynomiality χ(⊗ N_k^{a_k}) in several exponents; the general χ(f^*L) = deg f · χ(L) (only leading coefficient);
  "deg is a polynomial on End(A)". Survey by a code-search subagent (filename globs + reads, no full grep): treat
  absence claims as SPECULATIVE-strength.

## Finding F1 (math, VERIFIED by the Lean below once it compiles)
deg-det's route needs `End(A)` finite over ℤ only for (i) integrality of φ (to read deg on ℤ[φ] = ℤ[X]/(R)) and
(ii) P ∈ ℤ[X]. Both are avoidable: work with polynomials of degree ≤ D in φ (no relation; the comparison lemma's
test polynomials have degree ≤ deg μ ≤ 2g), and get p-integrality of P₀ from ∏(a_i^m − q) = deg(φ^m − q) ∈ ℤ for
all m (a root with |a|_q > 1 makes the q-adic norm grow like |a|_q^m). So
CharPolyIndepOfEllAlgClosed ⇐ DegHomogPolyNoEmb alone (char 0 with σ : k → ℂ from CharPolyLattice).

## Compile log (11-17)
- `lake build` of the merged chain (DegHomogPolyC, CharPolyLattice, MumfordTorsionAlgClosed, UniformizationLeafAll):
  EXIT 0 (rebuilt H chain + vendored AnthropicFLT, ~13.4k jobs). VERIFIED.
- `ZInQKernel/Contrib/OneProof/CharPolyCharP/Algebra.lean` (Mathlib + deg-det Algebra): compiles, no sorry;
  `charpoly_eq_P0D`, `P0D_int` axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `ZInQKernel/Contrib/OneProof/CharPolyCharP.lean`: compiles; `charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'`
  (HR : DegPolyC.DegHomogPolyNoEmb) : CharPolyIndepOfEllAlgClosed and `charPolyIndepOfEllAlgClosed_of_degHomogPoly'`
  (hP : DegDet.DegHomogPoly), axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Pitfall: `A.V ℓ` instances need `open … MonoidalCategory CartesianMonoidalCategory MonObj`.
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.CharPolyCharP`: EXIT 0.
- `#discharges` (scratch/charpoly-p/Discharges.lean, output Discharges-output.txt): DISCHARGES
  [OpenTextbookLeaves17.charPolyIndepOfEllAlgClosed] by `CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'`,
  still assumes [DegPolyC.DegHomogPolyNoEmb], standard axioms; same with `…_of_degHomogPoly'` / [DegDet.DegHomogPoly]. VERIFIED.
- autofold dry run (scratch/charpoly-p/autofold.json): "strict count: 15/16 on 31 -> 15/16 on 31; strictest 15/16 -> 15/16";
  FoldDryRun.lean (`sixContactMin_of_open59`, TailZ65 base) compiles, standard axioms. VERIFIED.
- scratch/charpoly-p/M1Statement.lean: `NonIsogPullbackEulerZero` (M1) and `EulerPullbackDeg` stated over CW07
  `Scheme.Modules.eulerChar`, AnthropicFLT `Scheme.Modules.IsInvertible`, Mathlib pullback, `CharPolyEll.degEnd`; compiles. VERIFIED.

## Phase 2: χ-decomposition of DegHomogPoly (scratch/charpoly-p/ChiDecomp.lean, compiles, standard axioms; VERIFIED)
Statements over CW07 `Scheme.Modules.eulerChar` (χ), AnthropicFLT `Scheme.Modules.IsInvertible`, Mathlib pullback, `degEnd`:
- `EulerPullbackDegAt A`: χ(ψ^*L) = deg ψ · χ(L) ∀ψ ∈ End A, L invertible (Mumford §12 isogenies + §16 non-isogenies; consequence).
- `ChiPullbackPolyAt A`: x ↦ χ((Σ xᵢeᵢ)^*L) polynomial (cube + Snapper/RR; composite consequence).
- `ExistsChiNeZeroAt A`: ∃ L invertible, χ(L) ≠ 0 (projectivity + §16; consequence).
- `DegMulNDimAt A`: ∃ g, dim A = g ∧ deg[m] = m^{2g} for (m:k) ≠ 0 (Mumford §4; printed).
- `degPolyAt_of_chi`: DegPolyAt A from the four (homogeneity: N(mx) = m^{2g}N(x) for infinitely many m ⇒ N agrees
  with its degree-2g homogeneous component at integer points, `eval_eq_homogeneousComponent`).
- `charPolyIndepOfEllAlgClosed_of_chi`: the field from the four, on fields with no embedding into ℂ.
Not a fold (4 leaves for 1); a crowdsourcing map: three of the four are in the tree's vendored AnthropicFLT up to
framework bridges (ExistsChiNeZero, DegMulN, the cube half of ChiPullbackPoly); EulerPullbackDeg's non-isogeny half is M1.

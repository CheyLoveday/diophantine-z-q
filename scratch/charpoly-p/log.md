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

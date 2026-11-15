# flt-cqj2 results log

## 2026-11-15 03:30 PST setup
- Fresh start (no earlier log). Base 0d8105c7. Build tree: reflink copy of ~/dzq-wt/flt-cqj/.lake/build and lean/.lake/build.
- FLT source: ~/flt-src (read-only, 6e837e75 per task; toolchain v4.33.1, Mathlib db584cd6). VERIFIED (lakefile, lean-toolchain).
- Import cone of Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
  (scratch/flt-cqj2/tools/cone.py, cone.json): 661 FLT modules + P2M.Util. 247 of them already vendored by Cloud Worker 14
  (SOURCE_MANIFEST.json); 414 new (new_modules.txt, topological order). VERIFIED.
- The MapsTo half has no smaller cone in FLT's proof: P2M/Sol/S_..._of_transcendental_j.lean proves the bijection by
  induction on N (bijOn_one, bijOn_step via bijOn_core for N = ℓM), using injectivity/counting at level M to get MapsTo at
  level ℓM. The heaviest import is Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
  (461-module cone, 294 not yet vendored), needed already for prime N. So the full cone is ported. VERIFIED (read).
- tools/port.py copies each module into ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/<same path>, relocating
  imports, adding a 'Modified for the Z-in-Q kernel' header and the upstream lakefile options (maxHeartbeats 4000000,
  synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false, autoImplicit false) as set_option lines.

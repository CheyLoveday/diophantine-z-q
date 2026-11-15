# st-qbar results log

## Plan (2026-11-15 05:45)
Route: fixed point of an automorphism `h = g_α ≫ g_u⁻¹` of `Y₃` (R1hecke) at the CM ℂ-point; `Y₃` integral
(Y3Connected + componentIrreducible + smooth ⇒ reduced); a non-closed point of `Y₃` is generic (stalk dim 1
at closed points); at the generic point `h = 𝟙` (ext_of_isDominant), contradicting ALFixedPoints at a non-CM
ℚ̄-point; so the point is closed, residue field finite over ℚ, factor through ℚ̄.
Automorphism ψ of A with ψι(a)ψ⁻¹ = ι(w a w⁻¹): ψ = ι(w)c/n, (w,c,n) = (i, 1+φ, 2), (j, 2φ−1, 3), (ij, φ, 6);
integrality: ι(w)c kills A[n] (A[p] ≅ 𝒪/p𝒪, decide mod p) and divisibility via uniformization + HomLatticeCorr.

## Part E (scheme part) — VERIFIED (compiled, scratch/st-qbar/PartE.lean, 05:55)
- `GapST.closure_eq_univ_of_not_closed`: non-closed point of an irreducible proper smooth curve over a field is dense
  (stalk dim 1 at a closed point z, `isDomain_of_dim_one`, `Ring.KrullDimLE 1`, prime ≠ ⊥ is maximal).
- `GapST.exists_qbar_factor`: `y : fieldPt ℂ ⟶ Y`, `h : Y ⟶ Y`, `y ≫ h = y`, some ℚ̄-point `s` with `s ≫ h ≠ s`
  ⇒ `∃ ιe y₀, fieldMap ιe.toRatAlgHom ≫ y₀ = y` (Y proper, smooth rel. dim 1, irreducible, over ℚ).
  Note: lean/.lake/build had to be copied from ~/dzq (same commit 9a100aa7).

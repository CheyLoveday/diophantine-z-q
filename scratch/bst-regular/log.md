# bst-regular results log

Base 182e3388b7416a1d625b1786b945b2e2b77b2e4e (confirmed). Worktree needed `lean/.lake` (helper package build) copied in
(build artifact only, not committed).

## Step (a), (b): ZInQKernel/Contrib/OneProof/BstRegular/Abstract.lean — COMPILES (lake build OK)

- `BstRegular.IsRegularB p B H` (structure): `stable` (H maps B to B), `frac` ((Frac B)^H = B^H, fraction-free:
  x,y ∈ B, y ≠ 0, σx·y = x·σy ∀σ∈H ⇒ x = c·y, c ∈ B^H), `line` (b ∈ B, b ≠ 0, σb ∈ ℚ_p·b ∀σ∈H ⇒ ∃ b' ∈ B, b b' = 1).
- `isDomain_sub` (b): every ℚ_p-subalgebra of B_dR is a domain. VERIFIED.
- `IsRegularB.inv_fixed`: B^H is a field. VERIFIED.
- `repr_inclT`, `repr_tensorAct`, `toMatrix_vAct_det_ne_zero`: coordinate lemmas (bases 1 ⊗ e_i). VERIFIED.
- `isAdmissibleT_of_isAdmissible_of_regular` (a): IsRegularB B H → IsAdmissible B H ρ → IsAdmissibleT B H ρ. VERIFIED.
  #print axioms: [propext, Classical.choice, Quot.sound].
  Proof: N = dim V B^H-independent d_j ∈ D (exists_linearIndependent_of_le_finrank); coordinate matrix M over B;
  minimal-support kernel vector + `frac` ⇒ contradiction, so det M ≠ 0 (Matrix.exists_mulVec_eq_zero_iff, B domain);
  M = R(σ)·σ(M) ⇒ σ(det M) = det R(σ)^{-1} det M ⇒ `line` ⇒ det M unit ⇒ basis (Pi.basisFun mapped by toLinearEquiv').
- Compile pitfalls: `simpa using hsum` / `linearIndependent_iff'` on `dB` timed out (AddCommGroup unification);
  `Fintype.linearIndependent_iffₛ` works. `simp_rw [hrel]` loops (rhs contains lhs). No Field instance on BdR p
  (no map_inv₀); keep inverses in ℚ_p.

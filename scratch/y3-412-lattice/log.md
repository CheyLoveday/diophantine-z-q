# y3-412-lattice results log

Base: d28aef9839b8c12dcda2b24b3a22c993f4975dbf (VERIFIED, git rev-parse HEAD at start).

## Tree facts read (VERIFIED, read in the tree)
- `ShimuraCFT.rat_mem_zhat_iff` (RayClassShimura.lean) is A0 already; `inO_of_bEmb_mem`, `bEmb_mem_of_inO` give A1.
- `RayClassCFT.exists_den`, `exists_den_B` (denominators of finite adeles, via `FiniteAdeleRing.cofinite_mem_adicCompletionIntegers`).
- `RayClassCFT.classNumberOneB_proof : ClassNumberOneB` (g = bEmb γ * u, u ∈ OhatU); its proof uses I = {x | bEmb x * g ∈ OhatQ}, i.e. latticeAt g.
- `LeafQM.B` has no `Inv`; inverse is `RayClassCFT.binv γ = nrd(γ)⁻¹ • star γ` (`mul_binv`, `binv_mul`).
- `HDec.QMSplit.CNO.nrd_ne_zero : x ≠ 0 → nrd x ≠ 0` (B is a division algebra).
- `ModuliAtUnitsHP` takes Ψ : HPM → BAQˣ → _, evaluated at `toPM τ`; `ModuliAtUsedUnitsHP` takes Ψ : UpperHalfPlane → BAQˣ → _.
- bridges: `toGAf g = (x ↦ x g⁻¹)` (`app_toGAf`, rfl), `dcRelDel_iff_PM`: Deligne's class of toGAf g = kernel's class of g⁻¹.

## Part A (Y3Lattice412/Lattice.lean, Convention.lean)
- Lattice.lean: `lake env lean` clean after one fix (bounds proof: rw [bEmb_natSmul, Nat.cast_comm, mul_assoc]). COMPILED.
- Convention.lean (A5): needed `noncomputable section`; `show`/`change` to beta-reduce image lambdas. COMPILED.
- Constructions: L_g = 𝒪·binv γ from classNumberOneB_proof + A4 (with k := u ∈ OhatU, g := 1) + A2.
  Basis e_i = ofInt(Pi.single i 1) * α; lin. indep. via right mult by binv α and coordinates; span via `eq_sum_oVec` (cQ coordinates).

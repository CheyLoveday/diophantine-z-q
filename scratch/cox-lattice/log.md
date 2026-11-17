# cox-lattice results log

- Base: origin/wip/cm-branch2 120fa22b (includes cm-branch2's CoxCore.lean); origin/main d435851d merged (0af3a3a6, clean).
- Target (verbatim): HDec.CMBranch.CoxProperLattice (ZInQKernel/Contrib/OneProof/CMBranch/ReducedPeriod.lean L65).
- 12:05 scratch/cox-lattice/Cox.lean (import Mathlib; verbatim copies of LeafQM.AV.conductor [made `noncomputable`:
  the original sits in a `noncomputable section`], IsImagQuadOrder, orderDisc, latticeMultipliers, CoxProperLattice;
  CoxCore discr_pair/ringOfIntegers_eq_closure/discr_order copied from cm-branch2 120fa22b) COMPILES:
  `HDec.CMBranch.CoxLattice.coxProperLattice_proof : CoxProperLattice`, axioms [propext, Classical.choice, Quot.sound].
  VERIFIED (lake env lean). Statement unchanged; no extra hypothesis needed.
  Proof steps: exists_nonint (f•ω ∈ R, ω ∈ 𝓞_k \ ℚ; AddSubgroup.nsmul_relIndex_mem) → α = φ(fω) ∉ ℤ multiplier →
  α = p+qτ, ατ ∈ ℤ+ℤτ, q ≠ 0 → integral quadratic for τ → exists_prim_form (divide by gcd, sign) →
  mem_mult_iff_order (Cox 7.5 elementary half: multipliers of c(ℤ+ℤτ) = ℤ+ℤaτ) → θ = φ⁻¹(aτ): R = ℤ+ℤθ,
  θ²+bθ+ac' = 0, θ ∉ ℚ (disc_neg) → discr_order: b²−4ac' = [𝓞_k:R]²·d_k = orderDisc R.
  The ring-isomorphism invariance of the discriminant is NOT needed: the isomorphism is used only to pull the
  generator aτ back to R, and the discriminant is computed in k.

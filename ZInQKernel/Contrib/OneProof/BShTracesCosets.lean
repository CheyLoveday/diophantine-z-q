import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! ON THE SPOT (provenance (c)): reindex the lattice series by cosets before
taking the finite sum. The subtraction in each Weierstrass summand is retained. -/

noncomputable section

namespace BShTraces

open PeriodPair

/-- A coset enumeration of the larger lattice, with representatives using
the sign convention (l-r_i). -/
structure CosetEnumeration (L M : PeriodPair) (ι : Type*) where
  representative : ι → ℂ
  equiv : ι × L.lattice ≃ M.lattice
  coe_equiv (i : ι) (l : L.lattice) :
    (equiv (i, l) : ℂ) = (l : ℂ) - representative i

variable {L M : PeriodPair} {ι : Type*} [Fintype ι] (D : CosetEnumeration L M ι)

/-- Summing the translates relative to their values at the origin gives
the Weierstrass function of the larger lattice. -/
theorem weierstrassP_cosets (z : ℂ) :
    M.weierstrassP z =
      ∑ i, (L.weierstrassP (z + D.representative i) - L.weierstrassP (D.representative i)) := by
  classical
  let f : M.lattice → ℂ := fun l => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2
  have hs : Summable f := (M.hasSum_weierstrassP z).summable
  change ∑' l, f l = _
  rw [← D.equiv.tsum_eq f]
  change ∑' l, (f ∘ D.equiv) l = _
  rw [(hs.comp_injective D.equiv.injective).tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weierstrassP, weierstrassP, ← Summable.tsum_sub
    (L.hasSum_weierstrassP _).summable (L.hasSum_weierstrassP _).summable]
  apply tsum_congr
  intro l
  have h₁ : z - (D.equiv (i, l) : ℂ) = z + D.representative i - (l : ℂ) := by
    rw [D.coe_equiv]; ring
  have h₂ : (D.equiv (i, l) : ℂ) ^ 2 = (D.representative i - (l : ℂ)) ^ 2 := by
    rw [D.coe_equiv]; ring
  dsimp [f]
  rw [h₁, h₂]
  ring

/-- The same coset enumeration reindexes the convergent inverse power sums.
The term with representative zero recovers the original invariant (G_n). -/
theorem G_cosets {n : ℕ} (hn : 2 < n) :
    M.G n = ∑ i, L.sumInvPow (D.representative i) n := by
  classical
  let f : M.lattice → ℂ := fun l => ((l : ℂ) ^ n)⁻¹
  have hs : Summable f := by
    simpa [f] using (M.hasSum_sumInvPow 0 hn).summable
  change ∑' l, f l = _
  rw [← D.equiv.tsum_eq f]
  change ∑' l, (f ∘ D.equiv) l = _
  rw [(hs.comp_injective D.equiv.injective).tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  apply tsum_congr
  intro l
  simp only [Function.comp_apply, f, D.coe_equiv]

#print axioms weierstrassP_cosets
#print axioms G_cosets

end BShTraces

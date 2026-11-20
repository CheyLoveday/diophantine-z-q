import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusLower
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Prints
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.GeodesicIntegral.BetweenCusps

/-!
# From cusp classes to the lattice convention

The finite cuspidal subgroup supplies a common denominator after the image of each cusp class
has been identified in `ℂ/Lat`. This identification is the cusp restriction of the modular
parametrization, including the rational pullback scalar. The remaining analytic input is
the twisted central value formula. The integral and lattice normalization are fixed below.
-/

noncomputable section

open Complex Topology
open scoped ComplexConjugate
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ElkikMD

/-- The symbol oriented from `∞` to `r`, with differential `2πif(z) dz`. -/
def cuspSymbol (f : UpperHalfPlane → ℂ) (r : ℚ) : ℂ :=
  -(2 * (Real.pi : ℂ) * I) * TauCeti.cuspIntegral f (r : OnePoint ℚ) OnePoint.infty

/-- The positive common denominator of the symbols, after the pullback scale `κ`.
`hAJ` is the cusp image under `φ = α q_f`, in analytic uniformization (tex 1781–1787,
2937–2941). The conclusion is stronger than separate rational period coordinates. -/
theorem cuspSymbols_clear_denominator {N : ℕ} [NeZero N] {J : Type*} [AddCommGroup J]
    {cuspClass : OnePoint ℚ → J} (hMD : ManinDrinfeld N cuspClass)
    (Lat : PeriodPair) (f : UpperHalfPlane → ℂ) (κ : ℚ)
    (φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup) {S : Set ℚ}
    (hAJ : ∀ r ∈ S, φ (cuspClass r) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ : ℂ) * cuspSymbol f r)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r ∈ S, (m : ℂ) * ((κ : ℂ) * cuspSymbol f r) ∈ Lat.lattice := by
  obtain ⟨m, hm, hann⟩ := cuspidalImage_annihilator hMD φ
  refine ⟨m, hm, fun r hrS => ?_⟩
  have hr := hann (r : OnePoint ℚ)
  rw [hAJ r hrS, ← map_nsmul] at hr
  have hmem := (QuotientAddGroup.eq_zero_iff (m • ((κ : ℂ) * cuspSymbol f r))).mp
    (show ((m • ((κ : ℂ) * cuspSymbol f r) : ℂ) : ℂ ⧸ Lat.lattice.toAddSubgroup) = 0 from hr)
  change m • ((κ : ℂ) * cuspSymbol f r) ∈ Lat.lattice at hmem
  simpa only [nsmul_eq_mul] using hmem

/-- The values at `1` of the entire continuations of the curve's integral-coefficient Dirichlet
series are real. This also holds for the junk value in the absence of continuation. -/
theorem lval_eq_ofReal_re (E : WeierstrassCurve ℚ) : ((Lval E).re : ℂ) = Lval E := by
  by_cases h : ∃ F, IsLContinuation E F
  · obtain ⟨F, hF⟩ := h
    have hconj : IsLContinuation E (fun z => conj (F (conj z))) := by
      refine ⟨fun z => differentiableAt_conj_conj_iff.mpr (hF.1 _), fun z hz => ?_⟩
      change conj (F (conj z)) = E.LSeries z
      rw [hF.2 _ (by simpa only [conj_re] using hz), WeierstrassCurve.LSeries, LSeries, conj_tsum]
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · simp [hn]
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
          ← Complex.conj_cpow _ _ (by rw [natCast_arg]; positivity)]
        simp
    have heq := congrFun (IsLContinuation.unique hconj hF) 1
    rw [Lval_eq hF]
    change conj (F (conj 1)) = F 1 at heq
    rw [map_one] at heq
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im heq
      simp only [conj_im] at him
      simp only [ofReal_im]
      linarith
  · simp [Lval, h]

private def imaginaryLine : ℝ →+ ℂ where
  toFun t := (t : ℂ) * I
  map_zero' := by simp
  map_add' a b := by push_cast; ring

/-- If an imaginary period is nonzero, the imaginary intersection of the lattice is generated
by `i * omegaMinus Lat`, where `omegaMinus` is the actual infimum of `GenusOdd.Defs`. -/
theorem imaginaryLattice_generator (Lat : PeriodPair) {x : ℝ} (hx : x ≠ 0)
    (hLat : (x : ℂ) * I ∈ Lat.lattice) :
    0 < omegaMinus Lat ∧ ∃ n : ℤ, x = (n : ℝ) * omegaMinus Lat := by
  let H := Lat.lattice.toAddSubgroup.comap imaginaryLine
  have hxH : x ∈ H := hLat
  let j : H → Lat.lattice := fun t => ⟨imaginaryLine t, t.property⟩
  have hjc : Continuous j := (by
    change Continuous (fun t : H => (t.val : ℂ) * I)
    fun_prop : Continuous fun t : H => imaginaryLine t).subtype_mk _
  have hji : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    have he := congrArg (fun t : Lat.lattice => t.val.im) hab
    simpa [j, imaginaryLine, mul_im] using he
  let : DiscreteTopology H := DiscreteTopology.of_continuous_injective hjc hji
  have hcyc : IsAddCyclic H := AddSubgroup.isAddCyclic_iff_discreteTopology.mpr inferInstance
  obtain ⟨u, hgen⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp hcyc
  have hu0 : u ≠ 0 := by
    intro h0
    rw [← hgen, h0] at hxH
    exact hx (by simpa using hxH)
  obtain ⟨v, hv, hgen⟩ : ∃ v : ℝ, 0 < v ∧ AddSubgroup.zmultiples v = H := by
    rcases lt_or_gt_of_ne hu0 with hn | hp
    · exact ⟨-u, neg_pos.mpr hn, AddSubgroup.zmultiples_neg.trans hgen⟩
    · exact ⟨u, hp, hgen⟩
  have hleast : IsLeast {t : ℝ | 0 < t ∧ (t : ℂ) * I ∈ Lat.lattice} v := by
    refine ⟨⟨hv, show v ∈ H from hgen ▸ AddSubgroup.mem_zmultiples v⟩, ?_⟩
    rintro t ⟨ht, htH⟩
    change t ∈ H at htH
    rw [← hgen, AddSubgroup.mem_zmultiples_iff] at htH
    obtain ⟨a, rfl⟩ := htH
    rw [zsmul_eq_mul] at ht ⊢
    have ha : (0 : ℝ) < a := (mul_pos_iff_of_pos_right hv).mp ht
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast (show (1 : ℤ) ≤ a by exact_mod_cast ha)
    nlinarith
  have hΩ : omegaMinus Lat = v := hleast.csInf_eq
  rw [hΩ]
  rw [← hgen, AddSubgroup.mem_zmultiples_iff] at hxH
  obtain ⟨a, ha⟩ := hxH
  exact ⟨hv, a, by simpa only [zsmul_eq_mul] using ha.symm⟩

/-- The unnormalized period sum for the Jacobi character of an odd discriminant. -/
def quadraticCuspSum (f : UpperHalfPlane → ℂ) (d : ℤ) : ℂ :=
  ∑ a ∈ Finset.range d.natAbs, (chiD d a : ℂ) * cuspSymbol f ((a : ℚ) / d.natAbs)

/-- The actual genus partner supplies the nonzero central value; the signed Birch formula
and the rational-scale cusp comparison transport the period sum into the exact `omegaMinus`
convention. `hBirch` needs the quadratic Gauss sum only up to sign.
Neither `hAJ` nor `hBirch` is an additional printed-form leaf. -/
theorem hElkikMD_of_cuspidalSubgroup {ℓ : ℕ} {d : ℤ} (hgp : GenusPartner (Ecurve ℓ) d)
    {J : Type*} [AddCommGroup J] [NeZero (newformLevel (Ecurve ℓ))]
    {cuspClass : OnePoint ℚ → J} (hMD : ManinDrinfeld (newformLevel (Ecurve ℓ)) cuspClass)
    (Lat : PeriodPair) (f : UpperHalfPlane → ℂ) {κ : ℚ} (hκ : κ ≠ 0)
    (φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup)
    (hAJ : ∀ a < d.natAbs, chiD d a ≠ 0 → φ (cuspClass (((a : ℚ) / d.natAbs : ℚ) : OnePoint ℚ)) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ : ℂ) * cuspSymbol f ((a : ℚ) / d.natAbs)))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hBirch : quadraticCuspSum f d = (ε : ℂ) * (Real.sqrt |(d : ℝ)| : ℂ) *
      Lval (qtwist (Ecurve ℓ) d) * I) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  obtain ⟨F, hF, hF1⟩ := analyticRank_zero_iff.mp hgp.2.2.2.2.2
  have hLv : Lval (qtwist (Ecurve ℓ) d) ≠ 0 := by rwa [Lval_eq hF]
  let S : Set ℚ := (fun a : ℕ => (a : ℚ) / d.natAbs) '' {a : ℕ | a < d.natAbs ∧ chiD d a ≠ 0}
  have hAJ' : ∀ r ∈ S, φ (cuspClass r) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ : ℂ) * cuspSymbol f r) := by
    rintro r ⟨a, ⟨ha, hχ⟩, rfl⟩
    exact hAJ a ha hχ
  obtain ⟨m, hm, hperiod⟩ := cuspSymbols_clear_denominator hMD Lat f κ φ hAJ'
  have hsum : (m : ℂ) * ((κ : ℂ) * quadraticCuspSum f d) ∈ Lat.lattice := by
    unfold quadraticCuspSum
    simp only [Finset.mul_sum]
    apply Submodule.sum_mem
    intro a ha
    by_cases hχ : chiD d a = 0
    · simp [hχ]
    have hmem : (a : ℚ) / d.natAbs ∈ S := ⟨a, ⟨Finset.mem_range.mp ha, hχ⟩, rfl⟩
    convert Lat.lattice.smul_mem (chiD d a) (hperiod _ hmem) using 1
    rw [zsmul_eq_mul]
    ring
  let x : ℝ := (m : ℝ) * (κ : ℝ) * Real.sqrt |(d : ℝ)| * (Lval (qtwist (Ecurve ℓ) d)).re
  have hx : x ≠ 0 := by
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast hgp.1.ne
    have hre : (Lval (qtwist (Ecurve ℓ) d)).re ≠ 0 := by
      intro hh
      apply hLv
      rw [← lval_eq_ofReal_re, hh, ofReal_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast hm.ne')
      (by exact_mod_cast hκ)) (Real.sqrt_pos.mpr (abs_pos.mpr hd)).ne') hre
  have hxLat : (x : ℂ) * I ∈ Lat.lattice := by
    have hsum' := Lat.lattice.smul_mem ε hsum
    rw [zsmul_eq_mul, hBirch] at hsum'
    have hεsq : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    convert hsum' using 1
    dsimp [x]
    push_cast
    rw [lval_eq_ofReal_re]
    calc
      _ = (ε : ℂ) ^ 2 * ((m : ℂ) * (κ : ℂ) * (Real.sqrt |(d : ℝ)| : ℂ) *
          Lval (qtwist (Ecurve ℓ) d) * I) := by rw [hεsq, one_mul]
      _ = _ := by ring
  obtain ⟨hΩ, n, hn⟩ := imaginaryLattice_generator Lat hx hxLat
  have hn0 : n ≠ 0 := by
    intro hh
    apply hx
    simp [hn, hh]
  refine ⟨(n : ℚ) / ((m : ℚ) * κ), div_ne_zero (by exact_mod_cast hn0)
    (mul_ne_zero (by exact_mod_cast hm.ne') hκ), ?_⟩
  have hnC := congrArg Complex.ofReal hn
  dsimp [x] at hnC
  push_cast at hnC ⊢
  rw [lval_eq_ofReal_re] at hnC
  unfold Lstar
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hΩC : (omegaMinus Lat : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  apply (div_eq_div_iff (mul_ne_zero hmC hκC) hΩC).mpr
  linear_combination -hnC

#print axioms cuspSymbols_clear_denominator
#print axioms lval_eq_ofReal_re
#print axioms imaginaryLattice_generator
#print axioms hElkikMD_of_cuspidalSubgroup

end ZInQ.Manuscript.RC.ElkikMD

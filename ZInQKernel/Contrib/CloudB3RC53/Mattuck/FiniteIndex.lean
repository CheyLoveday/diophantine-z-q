import ZInQKernel.Contrib.CloudB3RC53.Mattuck.CloseSub
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Division

/-!
# Mattuck, odd residue characteristic, part 3: `E₁(K_w)` has finite index in `E(K_w)`

Manuscript `diophantine_zq.tex`, tex 4551–4556 (the old Kummer row; Mattuck's theorem).

Let `A` be a Dedekind domain with fraction field `F`, `u` a height-one prime, `K_u` the completion,
`𝒪_u` its ring of integers, and `C` a Weierstrass curve over `𝒪_u`, elliptic over `K_u` (any
reduction type). **`finiteIndex_kerReduction`**: if `𝒪_u` is compact (e.g. `K_u` a local field),
the kernel of reduction `E₁(K_u)` (Tau Ceti's `kerReduction`, the image of the formal group) has
finite index in `E(K_u)`.

Proof: the points outside `E₁` are the points with integral coordinates; cover `𝒪_u × 𝒪_u` by
finitely many `δ`-balls (`δ = v(Δ)`, compactness); two integral points in the same ball differ by
a point of `E₁` (`sub_eq_zero_or_one_lt_valuation_xCoord`, the discriminant certificate). Hence
`E(K_u) ⧸ E₁` is covered by finitely many classes.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open IsDedekindDomain WeierstrassCurve Topology

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A)
  (C : WeierstrassCurve (u.adicCompletionIntegers F))

/-- `C` over `K_u` has `v`-integral coefficients. -/
theorem isIntegral_baseChange_adic :
    WeierstrassCurve.IsIntegral
      (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ))).valuationSubring
      (C.baseChange (u.adicCompletion F)).toAffine :=
  ⟨⟨C, rfl⟩⟩

/-- The `δ`-ball around `c` is a neighbourhood of `c` in `K_u`, for `δ ≠ 0`. -/
theorem ball_mem_nhds {δ : WithZero (Multiplicative ℤ)} (d : u.adicCompletion F)
    (hd : Valued.v d = δ) (hδ : δ ≠ 0) (c : u.adicCompletion F) :
    {y : u.adicCompletion F | Valued.v (y - c) < δ} ∈ 𝓝 c := by
  rw [Valued.mem_nhds]
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hδ hd.symm
  have h' : (Valued.v : Valuation (u.adicCompletion F) _).restrict d ≠ 0 := by simp [hd0]
  refine ⟨Units.mk0 _ h', fun y hy => ?_⟩
  rw [Set.mem_ofPred_eq, Units.val_mk0] at hy
  rw [Set.mem_ofPred_eq, ← hd]
  exact (Valued.v : Valuation (u.adicCompletion F) _).restrict_lt_iff.mp hy

variable [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- Membership in the kernel of reduction: `P = 0` or the `x`-coordinate of `P` has a pole. -/
theorem mem_kerReduction_iff' {P : (C.baseChange (u.adicCompletion F)).toAffine.Point} :
    P ∈ C.kerReduction u ↔ P = 0 ∨ 1 < Valued.v P.xCoord := by
  have := isIntegral_baseChange_adic u C
  rw [mem_kerReduction_iff, Affine.Point.reduction_eq_zero_iff]

open scoped Classical in
/-- **`E₁(K_u)` has finite index in `E(K_u)`** (any reduction type), when `𝒪_u` is compact.
PROVED. -/
theorem finiteIndex_kerReduction [CompactSpace (u.adicCompletionIntegers F)] :
    (C.kerReduction u).FiniteIndex := by
  have hI := isIntegral_baseChange_adic u C
  have hΔ : (C.baseChange (u.adicCompletion F)).toAffine.Δ ≠ 0 :=
    (C.baseChange (u.adicCompletion F)).isUnit_Δ.ne_zero
  set δ := Valued.v (C.baseChange (u.adicCompletion F)).toAffine.Δ with hδdef
  have hδ : δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hΔ
  -- the cover of `𝒪_u × 𝒪_u` by `δ`-balls
  let U : (u.adicCompletionIntegers F) × (u.adicCompletionIntegers F) →
      Set ((u.adicCompletionIntegers F) × (u.adicCompletionIntegers F)) := fun c =>
    {z : (u.adicCompletionIntegers F) | Valued.v ((z : u.adicCompletion F) - c.1) < δ} ×ˢ
      {z : (u.adicCompletionIntegers F) | Valued.v ((z : u.adicCompletion F) - c.2) < δ}
  have hU : ∀ c ∈ (Set.univ : Set ((u.adicCompletionIntegers F) × (u.adicCompletionIntegers F))),
      U c ∈ 𝓝 c := by
    intro c _
    refine prod_mem_nhds ?_ ?_
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        (ball_mem_nhds u (C.baseChange (u.adicCompletion F)).toAffine.Δ hδdef.symm hδ
          (c.1 : u.adicCompletion F))
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        (ball_mem_nhds u (C.baseChange (u.adicCompletion F)).toAffine.Δ hδdef.symm hδ
          (c.2 : u.adicCompletion F))
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U hU
  -- the points with integral coordinates in the ball around `c`
  let near : (u.adicCompletionIntegers F) × (u.adicCompletionIntegers F) →
      (C.baseChange (u.adicCompletion F)).toAffine.Point → Prop := fun c P =>
    ∃ (x y : u.adicCompletion F) (h : (C.baseChange (u.adicCompletion F)).toAffine.Nonsingular x y),
      P = .some x y h ∧ Valued.v x ≤ 1 ∧
      Valued.v (x - c.1) < δ ∧ Valued.v (y - c.2) < δ
  let g : Option t → (C.baseChange (u.adicCompletion F)).toAffine.Point ⧸ C.kerReduction u :=
    fun o =>
    match o with
    | none => 0
    | some c => if h : ∃ P, near c P then QuotientAddGroup.mk h.choose else 0
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_cases hP : P ∈ C.kerReduction u
    · exact ⟨none, ((QuotientAddGroup.eq_zero_iff P).mpr hP).symm⟩
    · rcases P with _ | ⟨x, y, h⟩
      · exact absurd (C.kerReduction u).zero_mem hP
      have hx : Valued.v x ≤ 1 := by
        by_contra! hx
        exact hP ((mem_kerReduction_iff' u C).mpr (Or.inr hx))
      have hy : Valued.v y ≤ 1 := Affine.valuation_y_le_one_of_valuation_x_le_one _ h.1 hx
      let z : (u.adicCompletionIntegers F) × (u.adicCompletionIntegers F) :=
        (⟨x, (Valuation.mem_valuationSubring_iff _ x).mpr hx⟩,
        ⟨y, (Valuation.mem_valuationSubring_iff _ y).mpr hy⟩)
      obtain ⟨c, hct, hzc⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
      have hnear : near c (.some x y h) := ⟨x, y, h, rfl, hx, hzc.1, hzc.2⟩
      have hex : ∃ P, near c P := ⟨_, hnear⟩
      refine ⟨some ⟨c, hct⟩, ?_⟩
      simp only [g, dite_eq_left hex]
      obtain ⟨x', y', h', hP', hx', hxc', hyc'⟩ := hex.choose_spec
      rw [hP', QuotientAddGroup.eq, ← sub_eq_neg_add]
      have hsub := sub_eq_zero_or_one_lt_valuation_xCoord _ h h' hx hx' hΔ
        (by
          have : x - x' = (x - c.1) - (x' - c.1) := by ring
          rw [this]; exact Valuation.map_sub_lt _ hzc.1 hxc')
        (by
          have : y - y' = (y - c.2) - (y' - c.2) := by ring
          rw [this]; exact Valuation.map_sub_lt _ hzc.2 hyc')
      exact (mem_kerReduction_iff' u C).mpr hsub
  have : Finite ((C.baseChange (u.adicCompletion F)).toAffine.Point ⧸ C.kerReduction u) :=
    Finite.of_surjective g hg
  exact AddSubgroup.finiteIndex_of_finite_quotient

end ZInQ.Contrib.CloudB3RC53.Mattuck

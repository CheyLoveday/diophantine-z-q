import ZInQKernel.Contrib.OneProof.ElkiesX6Star

namespace HDec.QMSplit.Moduli.ElkiesCoord

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

section Domain

open X6Glue Polynomial

/-- `r² + 3(s² + 1)` over `ℚ[s]` (Elkies' ring with `t = −s²` eliminated). -/
noncomputable def conicPoly : (Polynomial ℚ)[X] := X ^ 2 + C (3 * (X ^ 2 + 1))

theorem conicPoly_monic : conicPoly.Monic := monic_X_pow_add_C _ two_ne_zero

theorem conicPoly_natDegree : conicPoly.natDegree = 2 := natDegree_X_pow_add_C

theorem conicPoly_not_isRoot (b : Polynomial ℚ) : ¬ conicPoly.IsRoot b := by
  intro h
  simp only [conicPoly, IsRoot, eval_add, eval_pow, eval_X, eval_C] at h
  have hm : (X ^ 2 + C 1 : Polynomial ℚ).Monic := monic_X_pow_add_C _ two_ne_zero
  have h' : b ^ 2 = C (-3) * (X ^ 2 + C 1) := by
    rw [map_neg, map_one]
    have : (C 3 : Polynomial ℚ) = 3 := rfl
    linear_combination h + (X ^ 2 + 1) * this
  have := congrArg leadingCoeff h'
  rw [leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_C, hm.leadingCoeff] at this
  nlinarith [sq_nonneg (leadingCoeff b)]

theorem conicPoly_irreducible : Irreducible conicPoly := by
  rw [conicPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [conicPoly_natDegree])
    (by rw [conicPoly_natDegree]; norm_num)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro b hb
  rw [mem_roots conicPoly_monic.ne_zero] at hb
  exact conicPoly_not_isRoot b hb

theorem conicPoly_prime : Prime conicPoly :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp conicPoly_irreducible

instance : IsDomain (AdjoinRoot conicPoly) := AdjoinRoot.isDomain_of_prime conicPoly_prime

/-- `ElkiesRing → ℚ[s][r]/(r² + 3(s² + 1))`, `t ↦ −s²`. -/
noncomputable def toAdj : ElkiesRing →+* AdjoinRoot conicPoly :=
  elkiesLift (K := AdjoinRoot conicPoly) (-(AdjoinRoot.of conicPoly X) ^ 2) (AdjoinRoot.of conicPoly X)
    (AdjoinRoot.root conicPoly) (by ring) (by
      have h : AdjoinRoot.mk conicPoly (X ^ 2 + C (3 * (X ^ 2 + 1))) = 0 := AdjoinRoot.mk_self
      rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_mul, map_add, map_pow, map_one,
        map_ofNat] at h
      linear_combination h)

/-- The inverse direction. -/
noncomputable def fromAdj : AdjoinRoot conicPoly →+* ElkiesRing :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℚ ElkiesRing) eS) eR (by
    have e1 := rel1
    have e2 := rel2
    simp only [conicPoly, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom, eval₂_mul,
      eval₂_ofNat, eval₂_one]
    linear_combination e2 + 3 * e1)

theorem fromAdj_toAdj : fromAdj.comp toAdj = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [toAdj, fromAdj, elkiesLift_S]
  · simp [toAdj, fromAdj, elkiesLift_R]

instance elkiesRing_isDomain : IsDomain ElkiesRing := by
  have hinj : Function.Injective toAdj := by
    intro a b h
    have := congrArg fromAdj h
    simpa [← RingHom.comp_apply, fromAdj_toAdj] using this
  exact hinj.isDomain toAdj

end Domain

end HDec.QMSplit.Moduli.ElkiesCoord

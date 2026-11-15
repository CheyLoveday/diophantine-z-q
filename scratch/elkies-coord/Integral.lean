import ZInQKernel.Contrib.OneProof.ElkiesX6Star

namespace HDec.QMSplit.Moduli.ElkiesCoord

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

theorem exists_sq_eq (a : Qbar) : ∃ b : Qbar, b ^ 2 = a :=
  IsAlgClosed.exists_pow_nat_eq a two_pos

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

/-! ## `X₆` is integral, from the charts -/

section Integral

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}

theorem isIntegral_open {A : X.left.Opens} (hA : IsAffineOpen A) (φ : ElkiesRing ≃+* Γ(X.left, A))
    (hne : (A : Set X.left).Nonempty) : IsIntegral A.toScheme := by
  have : IsAffine A.toScheme := hA
  have : Nonempty A.toScheme := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsDomain Γ(X.left, A) := φ.symm.injective.isDomain (φ.symm : Γ(X.left, A) →+* ElkiesRing)
  have : IsDomain Γ(A.toScheme, ⊤) :=
    (A.topIso.commRingCatIsoToRingEquiv).injective.isDomain
      (A.topIso.commRingCatIsoToRingEquiv : Γ(A.toScheme, ⊤) →+* Γ(X.left, A))
  exact isIntegral_of_isAffine_of_isDomain A.toScheme

theorem isIrreducible_open {A : X.left.Opens} (h : IsIntegral A.toScheme) :
    IsIrreducible (A : Set X.left) := by
  have := (IrreducibleSpace.isIrreducible_univ A.toScheme).image A.ι A.ι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι] at this

/-- A `ℚ̄`-point of `t.U ∩ t.V` (where `s = 1`, `r = √−6`, `t = −1`). -/
theorem exists_pt_inter (hU : IsAffineOpen t.U) (hV : IsAffineOpen t.V)
    (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))
    (hT : φU eT = t.f) (hTg : φV eT = t.g) :
    ∃ p : X.left, p ∈ t.U ∧ p ∈ t.V := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  obtain ⟨y, hy⟩ := conicMapL_surjective φU φV hTg hU hV
    (Sum.inl ⟨(1, b), by simp only; linear_combination hb⟩)
  have hyU : pt (X := X) y ∈ t.U := by
    by_contra h
    rw [conicMapL, dif_neg h] at hy
    exact absurd hy (by simp)
  refine ⟨_, hyU, ?_⟩
  rw [conicMapL, dif_pos hyU] at hy
  have hs : psiU φU y hyU eS = 1 := by
    have := congrArg (fun c => match c with | Sum.inl q => q.1.1 | Sum.inr _ => 0) hy
    simpa using this
  have ht : ev t.U y hyU t.f ≠ 0 := by
    rw [← hT]
    change psiU φU y hyU eT ≠ 0
    have e1 := congrArg (psiU φU y hyU) rel1
    simp only [map_add, map_pow, map_zero, hs] at e1
    intro h0
    rw [h0] at e1
    norm_num at e1
  have hb' : pt (X := X) y ∈ X.left.basicOpen t.f := by
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hyU]
    intro h0
    apply ht
    rw [ev_apply, h0, map_zero]
  rw [t.basicOpen_f] at hb'
  exact hb'.2

theorem irreducibleSpace_of_charts (hc : ElkiesCharts X t) : IrreducibleSpace X.left := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, hpV⟩ := exists_pt_inter hU hV φU φV hT hTg
  have iU := isIrreducible_open (isIntegral_open hU φU ⟨p, hpU⟩)
  have iV := isIrreducible_open (isIntegral_open hV φV ⟨p, hpV⟩)
  have hcl : (Set.univ : Set X.left) ⊆ closure (t.U : Set X.left) := by
    intro x _
    have hx : x ∈ (t.U ⊔ t.V : X.left.Opens) := by rw [t.cover]; trivial
    rcases hx with h | h
    · exact subset_closure h
    · have := subset_closure_inter_of_isPreirreducible_of_isOpen iV.isPreirreducible t.U.isOpen
        ⟨p, hpV, hpU⟩ h
      exact closure_mono Set.inter_subset_right this
  have heq : closure (t.U : Set X.left) = Set.univ := Set.eq_univ_of_univ_subset hcl
  have hirr : IsIrreducible (Set.univ : Set X.left) := heq ▸ iU.closure
  exact { isPreirreducible_univ := hirr.2, toNonempty := ⟨p⟩ }

theorem isReduced_of_charts (hc : ElkiesCharts X t) : IsReduced X.left := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, hpV⟩ := exists_pt_inter hU hV φU φV hT hTg
  have key : ∀ (A : X.left.Opens), IsIntegral A.toScheme → ∀ x ∈ A,
      _root_.IsReduced (X.left.presheaf.stalk x) := by
    intro A hA x hx
    let q : A.toScheme := ⟨x, hx⟩
    have hinj : Function.Injective (A.ι.stalkMap q) :=
      (asIso (A.ι.stalkMap q)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_injective (A.ι.stalkMap q).hom hinj
  have : ∀ x : X.left, _root_.IsReduced (X.left.presheaf.stalk x) := by
    intro x
    have hx : x ∈ (t.U ⊔ t.V : X.left.Opens) := by rw [t.cover]; trivial
    rcases hx with h | h
    · exact key t.U (isIntegral_open hU φU ⟨p, hpU⟩) x h
    · exact key t.V (isIntegral_open hV φV ⟨p, hpV⟩) x h
  exact isReduced_of_isReduced_stalk X.left

/-- **Elkies' charts make `X₆` an integral scheme.** -/
theorem isIntegral_of_charts (hc : ElkiesCharts X t) : IsIntegral X.left := by
  have := irreducibleSpace_of_charts hc
  have := isReduced_of_charts hc
  exact isIntegral_of_irreducibleSpace_of_isReduced X.left

/-- **The generic point lies in `t.U = {t ≠ ∞}`** (`t` is not identically `∞`). -/
theorem genericPoint_mem_of_charts (hc : ElkiesCharts X t) [IrreducibleSpace X.left] :
    genericPoint X.left ∈ t.U := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, -⟩ := exists_pt_inter hU hV φU φV hT hTg
  exact ((genericPoint_spec X.left).mem_open_set_iff t.U.isOpen).mpr ⟨p, trivial, hpU⟩

end Integral

end HDec.QMSplit.Moduli.ElkiesCoord

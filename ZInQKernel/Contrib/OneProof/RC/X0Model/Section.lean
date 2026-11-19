import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart
import Mathlib.Analysis.Meromorphic.NormalForm

/-! Local comparison of regular sections with the meromorphic branch
at each upper half-plane parameter, as used at tex 2915–2919.
The comparison is on the spot (provenance (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model

private theorem top_le_preimage_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro x _
  change (f ≫ g) x ∈ U
  rw [Scheme.Hom.comp_apply]
  exact h (show f x ∈ ⊤ from trivial)

private theorem analyticArc_closedPoint (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    complexPoint N τ (default : Spec (.of ℂ)) =
      analyticArc N τ (IsLocalRing.closedPoint (meromorphicValuation (τ : ℂ))) := by
  have : IsLocalHom (CommRingCat.ofHom (valueOfGerm (τ : ℂ))).hom :=
    valueOfGerm_isLocalHom _
  rw [complexPoint, Scheme.Hom.comp_apply]
  rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ),
    Spec_closedPoint]

/-- Pullback of a regular section to the valuative lift, and its value at the
complex point, agree respectively with the model's function field and the
residue of its meromorphic germ. -/
theorem sectionGerm (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (U : (curve N).Opens) [Nonempty U] (r : Γ(curve N, U))
    (h : complexPoint N τ (default : Spec (.of ℂ)) ∈ U) :
    ∃ s : meromorphicValuation (τ : ℂ),
      s.val = fieldGerm N τ (functionField N ((curve N).germToFunctionField U r)) ∧
      valueOfGerm (τ : ℂ) s = sectionMap (complexPoint N τ) U (by
        intro x _
        rwa [Subsingleton.elim x (default : Spec (.of ℂ))]) r := by
  let R := meromorphicValuation (τ : ℂ)
  let K := MeromorphicGerm (τ : ℂ)
  let u := analyticArc N τ
  let e := algebraMap R K
  have hu : ⊤ ≤ u ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem u ((analyticArc_closedPoint N τ) ▸ h)).ge
  have he := top_le_preimage_comp (Spec.map (CommRingCat.ofHom e)) u U hu
  have hv := sectionMap_comp u e U hu he
  have hv' (w : Spec (.of K) ⟶ curve N) (hw : ⊤ ≤ w ⁻¹ᵁ U)
      (hg : w = genericMap N (fieldGerm N τ)) :
      sectionMap w U hw = (curve N).germToFunctionField U ≫
        CommRingCat.ofHom ((fieldGerm N τ).comp (functionField N).toRingHom) := by
    subst w
    exact sectionMap_generic N _ U hw
  refine ⟨sectionMap u U hu r, ?_, ?_⟩
  · have hh := hv.symm.trans (hv' _ he (analyticArc_generic N τ))
    exact congrArg (fun k : Γ(curve N, U) ⟶ CommRingCat.of K => k r) hh
  · have hi := top_le_preimage_comp (Spec.map (CommRingCat.ofHom (valueOfGerm (τ : ℂ)))) u U hu
    have hh := sectionMap_comp u (valueOfGerm (τ : ℂ)) U hu hi
    exact congrArg (fun k : Γ(curve N, U) ⟶ CommRingCat.of ℂ => k r) hh.symm

/-- At a point where a section is regular, its meromorphic germ has a
holomorphic representative, with the section value at the parameter. -/
theorem sectionAnalyticAt (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (U : (curve N).Opens) [Nonempty U] (r : Γ(curve N, U))
    (h : complexPoint N τ (default : Spec (.of ℂ)) ∈ U) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (g : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (functionField N ((curve N).germToFunctionField U r))) ∧
      sectionMap (complexPoint N τ) U (by
        intro x _
        rwa [Subsingleton.elim x (default : Spec (.of ℂ))]) r = g τ := by
  obtain ⟨s, hs, hv⟩ := sectionGerm N τ U r h
  obtain ⟨f, he, hf⟩ := s.val.property
  have hlim : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝 (valueOfGerm (τ : ℂ) s)) :=
    hasValue_coe.mp (he ▸ finiteValue_spec (meromorphicIncl (τ : ℂ)) s)
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).mp ⟨_, hlim⟩
  let g := toMeromorphicNFAt f (τ : ℂ)
  have hg : AnalyticAt ℂ g (τ : ℂ) :=
    hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp ho
  have hgerm : (f : PuncturedGerm (τ : ℂ)) = (g : PuncturedGerm (τ : ℂ)) :=
    Germ.coe_eq.mpr hf.eq_nhdsNE_toMeromorphicNFAt
  refine ⟨g, hg, hgerm.symm.trans (he.trans (congrArg (meromorphicIncl (τ : ℂ)) hs)), ?_⟩
  rw [← hv]
  exact tendsto_nhds_unique (hlim.congr' hf.eq_nhdsNE_toMeromorphicNFAt)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

private theorem meromorphicIncl_inv {z : ℂ} (g : MeromorphicGerm z) :
    meromorphicIncl z g⁻¹ = (meromorphicIncl z g)⁻¹ := by
  by_cases hz : g = 0
  · simp only [hz, inv_zero, map_zero]
    exact (congrArg (fun f : ℂ → ℂ => (f : PuncturedGerm z))
      (show (0 : ℂ → ℂ)⁻¹ = 0 from funext fun _ => inv_zero)).symm
  obtain ⟨f, e, hf⟩ := g.property
  have hn : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
      hz (Subtype.ext (e.symm.trans (Germ.coe_eq.mpr h)))
  let u : MeromorphicGerm z := ⟨((f⁻¹ : ℂ → ℂ) : PuncturedGerm z), _, rfl, hf.inv⟩
  have hm : g * u = 1 := by
    apply Subtype.ext
    change meromorphicIncl z g * ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) = 1
    rw [← show (f : PuncturedGerm z) = meromorphicIncl z g from e]
    exact Germ.coe_eq.mpr (hn.mono fun _ h => mul_inv_cancel₀ h)
  have : g⁻¹ = u := inv_eq_of_mul_eq_one_right hm
  rw [this, ← show (f : PuncturedGerm z) = meromorphicIncl z g from e]
  exact Germ.coe_inv f

set_option maxHeartbeats 500000 in
private theorem exists_meromorphicRepresentative (N : ℕ) [NeZero N]
    (a : modularFunctionField N) :
    ∃ f : ℂ → ℂ, MeromorphicOn f {z : ℂ | 0 < z.im} ∧
      ∀ τ : UpperHalfPlane, (f : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ a) := by
  let motive (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionField N) : Prop :=
    ∃ f : ℂ → ℂ, MeromorphicOn f {z : ℂ | 0 < z.im} ∧
      ∀ τ : UpperHalfPlane, (f : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ ⟨x, hx⟩)
  exact IntermediateField.adjoin_induction ℚ (s := {jq, jqN N}) (motive := motive)
    (fun x hx => by
      rcases Set.mem_insert_iff.mp hx with rfl | h
      · refine ⟨_, analyticOn_j.meromorphicOn, fun τ => ?_⟩
        rw [fieldGerm_j]
        exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun _ => by simp)
      · obtain rfl := Set.mem_singleton_iff.mp h
        exact ⟨_, (analyticOn_jN N).meromorphicOn, fun τ => (fieldGerm_jN N τ).symm⟩)
    (fun c => by
      refine ⟨fun _ => (c : ℂ), MeromorphicOn.const _, fun τ => ?_⟩
      have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (modularFunctionField N).algebraMap_mem c⟩ :
          modularFunctionField N) = algebraMap ℚ (modularFunctionField N) c :=
        Subtype.ext (DFunLike.congr_fun (Subsingleton.elim
          (algebraMap ℚ (LaurentSeries ℚ))
          ((modularFunctionField N).toSubfield.subtype.comp (algebraMap ℚ (modularFunctionField N)))) c)
      rw [hc]
      change ((fun _ : ℂ => (c : ℂ)) : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (algebraMap ℚ (modularFunctionField N) c))
      have hmap : fieldGerm N τ (algebraMap ℚ (modularFunctionField N) c) =
          constantGerm (τ : ℂ) (c : ℂ) :=
        DFunLike.congr_fun (Subsingleton.elim
          ((fieldGerm N τ).comp (algebraMap ℚ (modularFunctionField N)))
          ((constantGerm (τ : ℂ)).comp (Rat.castHom ℂ))) c
      rw [hmap]
      rfl)
    (fun x y hx hy ⟨f, hf, he⟩ ⟨g, hg, he'⟩ => by
      refine ⟨f + g, hf.add hg, fun τ => ?_⟩
      change ((f + g : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [Germ.coe_add, he, he']
      exact (((meromorphicIncl (τ : ℂ)).comp (fieldGerm N τ)).map_add ⟨x, hx⟩ ⟨y, hy⟩).symm)
    (fun x hx ⟨f, hf, he⟩ => by
      refine ⟨f⁻¹, hf.inv, fun τ => ?_⟩
      change ((f⁻¹ : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (⟨x, hx⟩⁻¹))
      rw [Germ.coe_inv, he]
      have hmap := map_inv₀ (fieldGerm N τ) (⟨x, hx⟩ : modularFunctionField N)
      rw [hmap, meromorphicIncl_inv])
    (fun x y hx hy ⟨f, hf, he⟩ ⟨g, hg, he'⟩ => by
      refine ⟨f * g, hf.mul hg, fun τ => ?_⟩
      change ((f * g : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (⟨x, hx⟩ * ⟨y, hy⟩))
      rw [Germ.coe_mul, he, he']
      exact (((meromorphicIncl (τ : ℂ)).comp (fieldGerm N τ)).map_mul ⟨x, hx⟩ ⟨y, hy⟩).symm)
    a.property

/-- A single meromorphic continuation realizes the modular function field at
every upper half-plane parameter, in meromorphic normal form. -/
theorem exists_meromorphicContinuation (N : ℕ) [NeZero N] (a : modularFunctionField N) :
    ∃ g : ℂ → ℂ, MeromorphicNFOn g {z : ℂ | 0 < z.im} ∧
      ∀ τ : UpperHalfPlane, (g : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ a) := by
  obtain ⟨f, hf, h⟩ := exists_meromorphicRepresentative N a
  exact ⟨_, meromorphicNFOn_toMeromorphicNFOn _ _, fun τ =>
    (Germ.coe_eq.mpr (hf.toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos)).trans (h τ)⟩

/-- The meromorphic continuation agrees with section evaluation on the whole
regular locus, with one choice of the continuation for all parameters. -/
theorem sectionMeromorphicContinuation (N : ℕ) [NeZero N]
    (U : (curve N).Opens) [Nonempty U] (r : Γ(curve N, U)) :
    ∃ g : ℂ → ℂ, MeromorphicNFOn g {z : ℂ | 0 < z.im} ∧
      (∀ τ : UpperHalfPlane, (g : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGerm N τ (functionField N ((curve N).germToFunctionField U r)))) ∧
      ∀ (τ : UpperHalfPlane) (h : complexPoint N τ (default : Spec (.of ℂ)) ∈ U),
        AnalyticAt ℂ g (τ : ℂ) ∧
        sectionMap (complexPoint N τ) U (by
          intro x _
          rwa [Subsingleton.elim x (default : Spec (.of ℂ))]) r = g τ := by
  obtain ⟨g, hg, he⟩ := exists_meromorphicContinuation N
    (functionField N ((curve N).germToFunctionField U r))
  refine ⟨g, hg, he, fun τ h => ?_⟩
  obtain ⟨f, hf, he', hv⟩ := sectionAnalyticAt N τ U r h
  have hfg := ((hg τ.im_pos).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hf.meromorphicNFAt).mp
    (Germ.coe_eq.mp ((he τ).trans he'.symm))
  exact ⟨(analyticAt_congr hfg).mpr hf, hv.trans hfg.eq_of_nhds.symm⟩

#print axioms top_le_preimage_comp
#print axioms analyticArc_closedPoint
#print axioms sectionGerm
#print axioms sectionAnalyticAt
#print axioms meromorphicIncl_inv
#print axioms exists_meromorphicRepresentative
#print axioms exists_meromorphicContinuation
#print axioms sectionMeromorphicContinuation

end ZInQ.Manuscript.RC.X0Model

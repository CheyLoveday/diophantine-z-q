import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Mathlib.Algebra.Algebra.Hom.Rat

/-! Reparametrization of the normalized chart and its invariance by the
level group (tex 2915–2919, on the spot, provenance (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open scoped Topology MatrixGroups

namespace ZInQ.Manuscript.RC.X0Model2

private def puncturedPrecomp {z w : ℂ} (f : ℂ → ℂ) (h : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) :
    PuncturedGerm w →+* PuncturedGerm z where
  toFun g := g.compTendsto f h
  map_one' := Germ.const_compTendsto 1 h
  map_zero' := Germ.const_compTendsto 0 h
  map_add' g k := by induction g, k using Germ.inductionOn₂; rfl
  map_mul' g k := by induction g, k using Germ.inductionOn₂; rfl

private theorem precomp_hasValue {z w c : ℂ} {f : ℂ → ℂ}
    (ht : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) {u : PuncturedGerm w} (hu : HasValue u c) :
    HasValue (puncturedPrecomp f ht u) c := by
  induction u using Germ.inductionOn with
  | h g => exact hasValue_coe.mpr ((hasValue_coe.mp hu).comp ht)

private def meromorphicPrecomp {z w : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z)
    (h : f z = w) (ht : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) :
    X0Model.MeromorphicGerm w →+* X0Model.MeromorphicGerm z :=
  ((puncturedPrecomp f ht).comp (X0Model.meromorphicIncl w)).codRestrict _ (by
    rintro ⟨_, g, rfl, hg⟩
    exact ⟨g ∘ f, rfl, (h ▸ hg : MeromorphicAt g (f z)).comp_analyticAt hf⟩)

private def finitePrecomp {z w : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z)
    (h : f z = w) (ht : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) :
    X0Model.meromorphicValuation w →+* X0Model.meromorphicValuation z :=
  ((meromorphicPrecomp hf h ht).comp (X0Model.meromorphicValuation w).toSubring.subtype).codRestrict
    (X0Model.meromorphicValuation z).toSubring
    (fun g => ⟨X0Model.valueOfGerm w g,
      precomp_hasValue ht (finiteValue_spec (X0Model.meromorphicIncl w) g)⟩)

private theorem valueOfGerm_precomp {z w : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z)
    (h : f z = w) (ht : Tendsto f (𝓝[≠] z) (𝓝[≠] w)) :
    (X0Model.valueOfGerm z).comp (finitePrecomp hf h ht) = X0Model.valueOfGerm w := by
  ext g
  exact hasValue_unique (finiteValue_spec (X0Model.meromorphicIncl z) (finitePrecomp hf h ht g))
    (precomp_hasValue ht (finiteValue_spec (X0Model.meromorphicIncl w) g))

private theorem fieldGerm_first (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ ⟨jq, jq_mem N⟩) =
      ((X0Model.analyticJ ∘ UpperHalfPlane.ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
  rw [X0Model.fieldGerm_j]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp)

set_option synthInstance.maxHeartbeats 80000 in
private theorem fieldGerm_reparam (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f (τ : ℂ)) (h : f τ = (σ : ℂ))
    (ht : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝[≠] (σ : ℂ)))
    (hj : X0Model.analyticJ ∘ UpperHalfPlane.ofComplex ∘ f =ᶠ[𝓝[≠] (τ : ℂ)]
      X0Model.analyticJ ∘ UpperHalfPlane.ofComplex)
    (hjN : X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex ∘ f =ᶠ[𝓝[≠] (τ : ℂ)]
      X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex) :
    (meromorphicPrecomp hf h ht).comp (X0Model.fieldGerm N σ) = X0Model.fieldGerm N τ := by
  let e := (meromorphicPrecomp hf h ht).comp (X0Model.fieldGerm N σ)
  let g := X0Model.fieldGerm N τ
  apply RingHom.ext
  intro a
  exact IntermediateField.adjoin_induction ℚ (s := {jq, jqN N})
    (motive := fun x hx => e ⟨x, hx⟩ = g ⟨x, hx⟩)
    (fun x hx => by
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · apply (X0Model.meromorphicIncl (τ : ℂ)).injective
        change puncturedPrecomp f ht (X0Model.meromorphicIncl (σ : ℂ)
          (X0Model.fieldGerm N σ ⟨jq, jq_mem N⟩)) = _
        rw [fieldGerm_first, fieldGerm_first]
        exact Germ.coe_eq.mpr hj
      · obtain rfl := Set.mem_singleton_iff.mp hx
        apply (X0Model.meromorphicIncl (τ : ℂ)).injective
        change puncturedPrecomp f ht (X0Model.meromorphicIncl (σ : ℂ)
          (X0Model.fieldGerm N σ ⟨jqN N, jqN_mem N⟩)) = _
        rw [X0Model.fieldGerm_jN, X0Model.fieldGerm_jN]
        exact Germ.coe_eq.mpr hjN)
    (fun c => by
      have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (modularFunctionField N).algebraMap_mem c⟩ :
          modularFunctionField N) = (c : modularFunctionField N) := by
        apply Subtype.ext
        exact DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ))
          ((modularFunctionField N).subtype.comp (Rat.castHom (modularFunctionField N)))) c
      change e _ = g _
      rw [hc, map_ratCast, map_ratCast])
    (fun x y hx hy hx' hy' => by
      change e (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [e.map_add, g.map_add, hx', hy'])
    (fun x hx hx' => by
      change e ((⟨x, hx⟩ : modularFunctionField N)⁻¹) = g ((⟨x, hx⟩ : modularFunctionField N)⁻¹)
      rw [map_inv₀ e, map_inv₀ g, hx'])
    (fun x y hx hy hx' hy' => by
      change e (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [e.map_mul, g.map_mul, hx', hy'])
    a.property

private theorem maps_to_rat_unique {R : Type} [CommRing R]
    (f g : Spec (.of R) ⟶ Spec (.of ℚ)) : f = g := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- An analytic change of parameter that preserves both coordinate germs
preserves the point of the normalization. The calculation takes place on
the valuative lifts, so it applies at plane collisions. -/
theorem complexPoint_eq_of_reparam (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f (τ : ℂ)) (h : f τ = (σ : ℂ))
    (ht : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝[≠] (σ : ℂ)))
    (hj : X0Model.analyticJ ∘ UpperHalfPlane.ofComplex ∘ f =ᶠ[𝓝[≠] (τ : ℂ)]
      X0Model.analyticJ ∘ UpperHalfPlane.ofComplex)
    (hjN : X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex ∘ f =ᶠ[𝓝[≠] (τ : ℂ)]
      X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex) :
    X0Model.complexPoint N τ = X0Model.complexPoint N σ := by
  let z : ℂ := τ
  let w : ℂ := σ
  let A := X0Model.meromorphicValuation z
  let B := X0Model.meromorphicValuation w
  let p := finitePrecomp hf h ht
  let q := meromorphicPrecomp hf h ht
  let ι : ℚ →+* A := ((X0Model.constantGerm z).comp (Rat.castHom ℂ)).codRestrict
    A.toSubring (fun c => by
      change ∃ d, HasValue (((fun _ => (c : ℂ)) : ℂ → ℂ) : PuncturedGerm z) d
      exact ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩)
  let : Algebra ℚ A := ι.toAlgebra
  have hh : (algebraMap A (X0Model.MeromorphicGerm z)).comp p =
      q.comp (algebraMap B (X0Model.MeromorphicGerm w)) := rfl
  have hg := fieldGerm_reparam N τ σ hf h ht hj hjN
  have hgen : Spec.map (CommRingCat.ofHom q) ≫ X0Model.genericMap N (X0Model.fieldGerm N σ) =
        X0Model.genericMap N (X0Model.fieldGerm N τ) := by
    simp only [X0Model.genericMap, ← Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom ((X0Model.fieldGerm N σ).comp (X0Model.functionField N).toRingHom) ≫
      CommRingCat.ofHom q =
        CommRingCat.ofHom ((q.comp (X0Model.fieldGerm N σ)).comp
          (X0Model.functionField N).toRingHom) from rfl]
    rw [show q.comp (X0Model.fieldGerm N σ) = _ from hg]
  have hcomm : Spec.map (CommRingCat.ofHom (algebraMap A (X0Model.MeromorphicGerm z))) ≫
      Spec.map (CommRingCat.ofHom p) =
        Spec.map (CommRingCat.ofHom q) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (X0Model.MeromorphicGerm w))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hh)
  obtain ⟨u, hu, huniq⟩ := X0Model.existsUnique_specialization (R := A) N (X0Model.fieldGerm N τ)
  have hp : Spec.map (CommRingCat.ofHom p) ≫ X0Model.analyticArc N σ = X0Model.analyticArc N τ := by
    refine (huniq _ ⟨?_, maps_to_rat_unique _ _⟩).trans
      (huniq _ ⟨X0Model.analyticArc_generic N τ, maps_to_rat_unique _ _⟩).symm
    rw [← Category.assoc, hcomm, Category.assoc, X0Model.analyticArc_generic, hgen]
  unfold X0Model.complexPoint
  rw [← hp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun a => Spec.map (CommRingCat.ofHom a) ≫ X0Model.analyticArc N σ)
    (valueOfGerm_precomp hf h ht)

def slMoebius (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))

theorem coe_sl_smul (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ((γ • τ : UpperHalfPlane) : ℂ) = slMoebius γ τ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

private theorem slMoebius_analyticAt (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (slMoebius γ) (τ : ℂ) := by
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  exact UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ

theorem slMoebius_tendsto (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    Tendsto (slMoebius γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : UpperHalfPlane) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · rw [coe_sl_smul]
    exact (slMoebius_analyticAt γ τ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)]
      with z hz hzpos
    let σ : UpperHalfPlane := ⟨z, hzpos⟩
    change slMoebius γ (σ : ℂ) ≠ _
    rw [← coe_sl_smul]
    intro he
    have hh := (MulAction.injective γ) (UpperHalfPlane.ext he : γ • σ = γ • τ)
    exact hz (congrArg (fun x : UpperHalfPlane => (x : ℂ)) hh)

private theorem dilate_smul (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ δ : SL(2, ℤ), ∀ τ, X0Model.dilate N (γ • τ) = δ • X0Model.dilate N τ := by
  obtain ⟨c, hc⟩ := (CharP.intCast_eq_zero_iff (ZMod N) N (γ 1 0)).mp
    (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet := γ.property
  rw [Matrix.det_fin_two] at hdet
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![γ 0 0, N * γ 0 1; c, γ 1 1]
  have ha : A.det = 1 := by
    rw [Matrix.det_fin_two]
    change γ 0 0 * γ 1 1 - (N : ℤ) * γ 0 1 * c = 1
    rw [hc] at hdet
    linear_combination hdet
  let δ : SL(2, ℤ) := ⟨A, ha⟩
  refine ⟨δ, fun τ => UpperHalfPlane.ext ?_⟩
  change (N : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
    ((δ • X0Model.dilate N τ : UpperHalfPlane) : ℂ)
  rw [coe_sl_smul, coe_sl_smul]
  unfold slMoebius
  change (N : ℂ) * (((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) /
    ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) =
    (((γ 0 0 : ℂ) * ((N : ℂ) * (τ : ℂ)) + (((N : ℤ) * γ 0 1 : ℤ) : ℂ)) /
    ((c : ℂ) * ((N : ℂ) * (τ : ℂ)) + (γ 1 1 : ℂ)))
  rw [hc]
  push_cast
  have hd : (c : ℂ) * ((N : ℂ) * (τ : ℂ)) + (γ 1 1 : ℂ) =
      (N : ℂ) * (c : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) := by ring
  rw [hd, ← mul_div_assoc, mul_add]
  congr 1
  ring

/-- The chart identifies parameters in the same `Γ₀(N)` orbit. -/
theorem complexPoint_smul (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    X0Model.complexPoint N (γ • τ) = X0Model.complexPoint N τ := by
  obtain ⟨δ, hδ⟩ := dilate_smul N γ hγ
  symm
  refine complexPoint_eq_of_reparam N τ (γ • τ) (slMoebius_analyticAt γ τ)
    (coe_sl_smul γ τ).symm (slMoebius_tendsto γ τ) ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz
    let w : UpperHalfPlane := ⟨z, hz⟩
    change X0Model.analyticJ (UpperHalfPlane.ofComplex (slMoebius γ (w : ℂ))) =
      X0Model.analyticJ (UpperHalfPlane.ofComplex (w : ℂ))
    rw [← coe_sl_smul, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
    exact ModularCurve.E4_cube_div_discriminant_smul γ w
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz
    let w : UpperHalfPlane := ⟨z, hz⟩
    change X0Model.analyticJN N (UpperHalfPlane.ofComplex (slMoebius γ (w : ℂ))) =
      X0Model.analyticJN N (UpperHalfPlane.ofComplex (w : ℂ))
    rw [← coe_sl_smul, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply,
      X0Model.analyticJN, hδ]
    exact ModularCurve.E4_cube_div_discriminant_smul δ (X0Model.dilate N w)

/-- The orbit implication of the model's chart axiom, including elliptic parameters. -/
theorem complexPoint_eq_of_gamma0_orbit (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    (h : ∃ γ ∈ CongruenceSubgroup.Gamma0 N, γ • τ = σ) :
    X0Model.complexPoint N τ = X0Model.complexPoint N σ := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact (complexPoint_smul N γ hγ τ).symm

/-- The stabilizer can act on a label from the right without changing the lift. -/
theorem complexPoint_eq_of_rightOrbit (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (γ₁ γ₂ : SL(2, ℤ))
    (h : ∃ δ s : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N ∧
      s • τ = τ ∧ γ₂ = δ * γ₁ * s) :
    X0Model.complexPoint N (γ₁ • τ) = X0Model.complexPoint N (γ₂ • τ) := by
  obtain ⟨δ, s, hδ, hs, rfl⟩ := h
  rw [mul_smul, hs, mul_smul, complexPoint_smul N δ hδ]


end ZInQ.Manuscript.RC.X0Model2

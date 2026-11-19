import ZInQKernel.Contrib.OneProof.JDescent5Parameter
import ZInQKernel.Contrib.OneProof.JDescent2

/-! Evaluation of the local parameter on the specified period. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Filter Set TauCeti
open scoped Topology UpperHalfPlane _root_.PeriodPair
open _root_.ZInQ.LeafPush2 (CPts cDom cEvalAt IsUniformization)

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem cpt_one_left {L : Type} [Field L] (A : PkgI3.AbVar L) (σ : L →+* ℂ) :
    (1 : CPts A σ).left = Spec.map (CommRingCat.ofHom σ) ≫ abVarUnit A := rfl

/-- The unit complex point is the only one whose underlying scheme point is the rational
identity. The residue spectrum of the identity is isomorphic to the ground spectrum. -/
theorem cpt_support_eq_identity_iff {L : Type} [Field L] (A : PkgI3.AbVar L)
    {σ : L →+* ℂ} (p : CPts A σ) :
    p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A ↔ p = 1 := by
  let X := A.X.left
  let O := abVarIdentity A
  let u := abVarUnit A
  let j := X.fromSpecResidueField O
  let g := Scheme.descResidueField (Scheme.stalkClosedPointTo u)
  have hu : Spec.map g ≫ j = u :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X u
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := Spec.map_surjective (j ≫ A.X.hom)
    have hrg : r ≫ g = 𝟙 (CommRingCat.of L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_id, hr, ← Category.assoc, hu]
      exact Over.w (η[A.X])
    have hgr : g ≫ r = 𝟙 (X.residueField O) := by
      ext a
      apply g.hom.injective
      have he := congrArg (fun f : CommRingCat.of L ⟶ CommRingCat.of L => f (g a)) hrg
      exact he
    have hd : ∃ d : Spec (CommRingCat.of ℂ) ⟶ Spec (X.residueField
        (p.left (IsLocalRing.closedPoint ℂ))),
        d ≫ X.fromSpecResidueField (p.left (IsLocalRing.closedPoint ℂ)) = p.left :=
      ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ X p.left⟩
    rw [hp] at hd
    obtain ⟨d, hd⟩ := hd
    have hj : (j ≫ A.X.hom) ≫ Spec.map g = 𝟙 _ := by
      rw [← hr, ← Spec.map_comp, hgr, Spec.map_id]
    have hdj : d ≫ j = p.left := hd
    have hd' : p.left ≫ A.X.hom ≫ Spec.map g = d := calc
      _ = d ≫ ((j ≫ A.X.hom) ≫ Spec.map g) := by rw [← hdj]; simp only [Category.assoc]
      _ = d := by rw [hj, Category.comp_id]
    have hw : p.left ≫ A.X.hom = Spec.map (CommRingCat.ofHom σ) := Over.w p
    apply Over.OverMorphism.ext
    rw [cpt_one_left]
    calc
      p.left = d ≫ j := hdj.symm
      _ = (p.left ≫ A.X.hom ≫ Spec.map g) ≫ j := congrArg (fun f => f ≫ j) hd'.symm
      _ = (p.left ≫ A.X.hom) ≫ (Spec.map g ≫ j) := by simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom σ) ≫ abVarUnit A := by rw [hu, hw]
  · rintro rfl
    rw [cpt_one_left]
    change (Spec.map (CommRingCat.ofHom σ) ≫ u) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) = O
    rw [Scheme.Hom.comp_apply, Spec_closedPoint]

/-- Evaluation on an open agrees with evaluation through the local ring at the point. -/
private theorem cEvalAt_eq_stalkClosedPointTo {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (f : Γ(A.X.left, U))
    (h : p.left (IsLocalRing.closedPoint ℂ) ∈ U) :
    cEvalAt p U f = Scheme.stalkClosedPointTo p.left
      (A.X.left.presheaf.germ U (p.left (IsLocalRing.closedPoint ℂ)) h f) := by
  have hpre := (Scheme.preimage_eq_top_of_closedPoint_mem p.left h).ge
  let q : Spec (CommRingCat.of ℂ) ⟶ A.X.left := p.left
  have hq : q (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U := h
  have hg := Scheme.germ_stalkClosedPointTo q U hq
  have hrest : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ⟶ p.left ⁻¹ᵁ U :=
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem p.left h).symm).hom
  have he : hrest = homOfLE hpre := Subsingleton.elim _ _
  have hg' : A.X.left.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo p.left =
      p.left.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    change A.X.left.presheaf.germ U _ hq ≫ Scheme.stalkClosedPointTo q = _
    rw [hg]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
    change p.left.app U ≫ (Spec (CommRingCat.of ℂ)).presheaf.map hrest.op ≫ _ = _
    rw [he, Scheme.Hom.appLE, Category.assoc]
    rfl
  rw [cEvalAt, dite_eq_left hpre]
  exact (congrArg (fun g : Γ(A.X.left, U) ⟶ CommRingCat.of ℂ => g f) hg').symm

private theorem cEvalAt_restrict {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) {U V : A.X.left.Opens} (hVU : V ≤ U)
    (h : p.left (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(A.X.left, U)) :
    cEvalAt p V (A.X.left.presheaf.map (homOfLE hVU).op f) = cEvalAt p U f := by
  rw [cEvalAt_eq_stalkClosedPointTo p V _ h, cEvalAt_eq_stalkClosedPointTo p U _ (hVU h),
    TopCat.Presheaf.germ_res_apply]

private theorem cEvalAt_via_germ_nonunit {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (hp : p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A)
    (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (s : Γ(A.X.left, V))
    (hs : ¬ IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV s)) :
    cEvalAt p V s = 0 := by
  have hh : p.left (IsLocalRing.closedPoint ℂ) ∈ V := hp.symm ▸ hV
  rw [cEvalAt_eq_stalkClosedPointTo p V s hh]
  let M (q : A.X.left) : Prop := ∀ hq : q ∈ V, ¬ IsUnit (A.X.left.presheaf.germ V q hq s)
  have hM : M (abVarIdentity A) := fun _ => hs
  have hs' := (hp.symm ▸ hM : M _) hh
  have : IsLocalHom (Scheme.stalkClosedPointTo p.left).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' p.left
  by_contra h
  exact hs' (IsLocalHom.map_nonunit (f := (Scheme.stalkClosedPointTo p.left).hom) _ (isUnit_iff_ne_zero.mpr h))

private theorem cEvalAt_via_germ_unit {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (hp : p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A)
    (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (s : Γ(A.X.left, V))
    (hs : IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV s)) :
    cEvalAt p V s ≠ 0 := by
  have hh : p.left (IsLocalRing.closedPoint ℂ) ∈ V := hp.symm ▸ hV
  rw [cEvalAt_eq_stalkClosedPointTo p V s hh]
  let M (q : A.X.left) : Prop := ∀ hq : q ∈ V, IsUnit (A.X.left.presheaf.germ V q hq s)
  have hM : M (abVarIdentity A) := fun _ => hs
  have hs' := (hp.symm ▸ hM : M _) hh
  exact (hs'.map (Scheme.stalkClosedPointTo p.left).hom).ne_zero

/-- The minimal derivative comparison for the weak period witness: a regular section with
order one at the rational identity has a nonzero derivative on that very witness. -/
def CMPeriodIdentityParameterDerivative : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L), A.dim = 1 →
    ∀ (σ : L →+* ℂ) (τ : ℍ) (Λ : Submodule ℤ (Fin 1 → ℂ))
      (Φ : (Fin 1 → ℂ) → CPts A σ) (s : ℂ), IsUniformization σ Λ Φ → s ≠ 0 →
      (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ))) →
      ∀ (P : Place L (AbVarFunctionField A)),
        (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
          P.integers.toSubring →
        ∀ (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (t : Γ(A.X.left, V)),
          letI : Nonempty V := ⟨⟨abVarIdentity A, hV⟩⟩
          P.ord (A.X.left.germToFunctionField V t) = 1 →
          deriv (fun z : ℂ => cEvalAt (Φ (fun _ => s * z)) V t) 0 ≠ 0

/-- Every point off the period lattice evaluates the sections on the complement of the
identity. -/
theorem abVar_period_mem_punctured {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ} (hΦ : IsUniformization σ Λ Φ)
    (hs : s ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    {z : ℂ} (hz : z ∉ (PeriodPair.ofTau τ).lattice) :
    ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ abVarPunctured A := by
  let p := Φ (fun _ => s * z)
  apply (Scheme.preimage_eq_top_of_closedPoint_mem p.left _).ge
  intro hp
  have h₁ := (cpt_support_eq_identity_iff A p).mp hp
  obtain ⟨m, n, h⟩ := (hΛ _).mp ((hΦ.2.1 _).mp h₁)
  have h' : z = (m : ℂ) + (n : ℂ) * (τ : ℂ) := mul_left_cancel₀ hs h
  apply hz
  refine PeriodPair.mem_lattice.mpr ⟨n, m, ?_⟩
  change (n : ℂ) * (τ : ℂ) + (m : ℂ) * 1 = z
  rw [h']
  ring

/-- Given the nonzero derivative of the regular local parameter, the exact order-two pole
in the generic stalk gives an analytic double pole on the given period. -/
theorem abVar_evaluatedPole_of_parameterDerivative
    (hderiv : CMPeriodIdentityParameterDerivative) {L : Type} [Field L] [NumberField L]
    (A : PkgI3.AbVar L) (hdim : A.dim = 1) {σ : L →+* ℂ} {τ : ℍ}
    {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ}
    (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) (x : Γ(A.X.left, abVarPunctured A))
    (hx : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2) :
    HasDoublePoleAtZero (fun z => cEvalAt (Φ (fun _ => s * z)) (abVarPunctured A) x) := by
  have := abVarPunctured_nonempty A P hp
  let U := abVarPunctured A
  let X := A.X.left
  obtain ⟨V, hV, t, u, ht, htNU, huU, hrel⟩ := abVar_orderTwo_localParameter A P hp U x hx
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  let ev (z : ℂ) := Φ (v z)
  have hv : Differentiable ℂ v := by
    apply differentiable_pi.mpr
    intro i
    change Differentiable ℂ (fun z : ℂ => s * z)
    fun_prop
  have hv0 : v 0 = 0 := by ext i; simp [v]
  have hzero : ev 0 = 1 := (hΦ.2.1 _).mpr (hv0.symm ▸ Λ.zero_mem)
  have hsupport : (ev 0).left (IsLocalRing.closedPoint ℂ) = abVarIdentity A :=
    (cpt_support_eq_identity_iff A (ev 0)).2 hzero
  have hV0 : v 0 ∈ cDom Φ V :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ev 0).left (hsupport.symm ▸ hV)).ge
  have hopen : IsOpen (v ⁻¹' cDom Φ V) := (hΦ.2.2.2.1 V).preimage hv.continuous
  have hV0' : 0 ∈ v ⁻¹' cDom Φ V := hV0
  have ha (f : Γ(X, V)) : AnalyticAt ℂ (fun z => cEvalAt (ev z) V f) 0 := by
    apply (DifferentiableOn.analyticOnNhd _ hopen) 0 hV0'
    exact (hΦ.2.2.2.2 V f).comp hv.differentiableOn (mapsTo_preimage _ _)
  have ht0 : cEvalAt (ev 0) V t = 0 := cEvalAt_via_germ_nonunit (ev 0) hsupport V hV t htNU
  have hu0 : cEvalAt (ev 0) V u ≠ 0 := cEvalAt_via_germ_unit (ev 0) hsupport V hV u huU
  have hd := hderiv L A hdim σ τ Λ Φ s hΦ hs hΛ P hp V hV t ht
  refine hasDoublePoleAtZero_of_localParameter (ha t) ht0 hd (ha u) hu0 ?_
  let Q := PeriodPair.ofTau τ
  have hl : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∉ Q.lattice := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Q.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz h0
    exact fun h => hz ⟨h, h0⟩
  have hn0 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ v ⁻¹' cDom Φ V := hopen.mem_nhds hV0'
  have hn := hn0.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  filter_upwards [hl, hn] with z hz hzV
  have hU' : ⊤ ≤ (ev z).left ⁻¹ᵁ U := abVar_period_mem_punctured hΦ hs hΛ hz
  have hS : (ev z).left (IsLocalRing.closedPoint ℂ) ∈ V ⊓ U :=
    ⟨hzV trivial, hU' trivial⟩
  have hT : ⊤ ≤ (ev z).left ⁻¹ᵁ (V ⊓ U) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ev z).left hS).ge
  let φ := (((ev z).left.appLE (V ⊓ U) ⊤ hT) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
  have hval := congrArg φ hrel
  rw [map_mul, map_pow] at hval
  have hE (f : Γ(X, V ⊓ U)) : φ f = cEvalAt (ev z) (V ⊓ U) f := by
    simp only [cEvalAt, dite_eq_left hT]; rfl
  rw [hE, hE, hE, cEvalAt_restrict _ inf_le_left hS, cEvalAt_restrict _ inf_le_right hS,
    cEvalAt_restrict _ inf_le_left hS] at hval
  exact hval

#print axioms cpt_one_left
#print axioms cpt_support_eq_identity_iff
#print axioms cEvalAt_eq_stalkClosedPointTo
#print axioms cEvalAt_restrict
#print axioms cEvalAt_via_germ_nonunit
#print axioms cEvalAt_via_germ_unit
#print axioms abVar_period_mem_punctured
#print axioms abVar_evaluatedPole_of_parameterDerivative

end

end HDec.CMBranch.CMjBridges

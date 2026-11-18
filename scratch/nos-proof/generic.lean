
/-! ## 5. (a) ⇒ (b) over any field `Ω ⊇ K` (generalizing av-split's §3-§5 from `K̄` to `Ω`)

The injectivity half of av-split's proof of `PkgI2.ReductionTorsionBijective` (`AvSplit.T4`, TailQ) uses
nothing about `K̄`: the valuative criterion of separatedness and universal closedness for the valuation ring
`w ⊆ Ω`, the adjunction for points of `𝒜_K`, and the proved `UnramifiedSectionsEq` with `[m]` étale. Copied
here with `AlgebraicClosure K` replaced by `Ω`, it gives (a) ⇒ (b) for every valuation ring `w` of every field
`Ω ⊇ K` over `O` (in particular for a separable closure, the form of dict-galois's `NeronOggShafarevichSep`). -/

section Omega

variable {K : Type} [Field K] {O : ValuationSubring K} {Ω : Type} [Field Ω] [Algebra K Ω]
  {w : ValuationSubring Ω} (hw : w.comap (algebraMap K Ω) = O)

/-- `Spec w` over `Spec O`. -/
abbrev PwΩ : Over (Spec (.of O)) := Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw)))

/-- `Spec κ(w)` over `Spec O`. -/
abbrev PkΩ : Over (Spec (.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (toW O w hw))))

variable (K O Ω) in
/-- `Spec Ω` over `Spec O`. -/
abbrev PΩ : Over (Spec (.of O)) :=
  (Over.map (AvSplit.T4.fK K O)).obj (PkgI2.specOver K Ω)

/-- `Spec Ω → Spec w` over `O`. -/
def iotaΩ : PΩ K O Ω ⟶ PwΩ hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom w.subtype)) (by
    show Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (toW O w hw)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)

/-- `Spec κ(w) → Spec w` over `O`. -/
def rhoΩ : PkΩ hw ⟶ PwΩ hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) (by
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

variable {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
  (e : (Over.pullback (AvSplit.T4.fK K O)).mapGrp.obj 𝒜 ≅ A)

variable (Ω) in
/-- `x ∈ A(Ω)` as an `Ω`-point of `𝒜` over `O` (through `e` and the adjunction). -/
def GΩ : Pts A Ω →* (PΩ K O Ω ⟶ 𝒜.X) :=
  MonoidHom.mk' (fun x => ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm
      (x ≫ e.inv.hom.hom)) (fun x y => by
    let u : Pts A Ω →
        (PkgI2.specOver K Ω ⟶ ((Over.pullback (AvSplit.T4.fK K O)).mapGrp.obj 𝒜).X) :=
      fun x => x ≫ e.inv.hom.hom
    have hmul : u (x * y) = u x * u y := MonObj.mul_comp _ _ _
    show ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm (u (x * y)) = _
    rw [hmul]
    exact AvSplit.T4.pb_symm_mul' _ 𝒜 _ _ _)

theorem GΩ_left (x : Pts A Ω) :
    (GΩ Ω 𝒜 e x).left = (x ≫ e.inv.hom.hom).left ≫ pullback.fst 𝒜.X.hom (AvSplit.T4.fK K O) := rfl

theorem GΩ_injective : Function.Injective (GΩ Ω 𝒜 e) := by
  intro x y h
  have h1 : x ≫ e.inv.hom.hom = y ≫ e.inv.hom.hom :=
    ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm.injective h
  have h2 := congrArg (· ≫ e.hom.hom.hom) h1
  simp only [Category.assoc, AvSplit.T4.inv_hom_hom, Category.comp_id] at h2
  exact h2

theorem PΩ_hom_eq : (PΩ K O Ω).hom =
    Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫
      Spec.map (CommRingCat.ofHom (toW O w hw)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O K)) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The valuative square of an `Ω`-point of `𝒜` over `Spec w → Spec O`. -/
def vsqΩ (t : PΩ K O Ω ⟶ 𝒜.X) : ValuativeCommSq 𝒜.X.hom where
  R := w
  K := Ω
  i₁ := t.left
  i₂ := Spec.map (CommRingCat.ofHom (toW O w hw))
  commSq := ⟨(Over.w t).trans (PΩ_hom_eq hw)⟩

/-- **Uniqueness of lifts** (Mathlib, valuative criterion of separatedness). -/
theorem iotaΩ_comp_injective [h : IsAbelianScheme 𝒜] :
    Function.Injective (fun x' : PwΩ hw ⟶ 𝒜.X => iotaΩ hw ≫ x') := by
  intro x₁ x₂ hx
  haveI := h.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsqΩ hw 𝒜 (iotaΩ hw ≫ x₁))
  have e1 : (⟨x₁.left, rfl, Over.w x₁⟩ : (vsqΩ hw 𝒜 (iotaΩ hw ≫ x₁)).commSq.LiftStruct) =
      ⟨x₂.left, (congrArg Over.Hom.left hx).symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

/-- **Existence of lifts** (Mathlib, valuative criterion of universal closedness). -/
theorem iotaΩ_comp_surjective [h : IsAbelianScheme 𝒜] (t : PΩ K O Ω ⟶ 𝒜.X) :
    ∃ x' : PwΩ hw ⟶ 𝒜.X, iotaΩ hw ≫ x' = t := by
  haveI := h.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsqΩ hw 𝒜 t)
  exact ⟨Over.homMk l hl2, Over.OverMorphism.ext hl1⟩

/-- **Reduction is injective on `m`-torsion of `𝒜(w)`** (av-split's `rho_inj` over `Ω`, with the proved
`UnramifiedSectionsEq` and `MulEtaleAbelianScheme`). -/
theorem rhoΩ_inj [h : IsAbelianScheme 𝒜]
    (m : ℕ) (hm : IsUnit (m : O)) (a b : PwΩ hw ⟶ 𝒜.X) (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : rhoΩ hw ≫ a = rhoΩ hw ≫ b) : a = b := by
  haveI := h.proper
  haveI : Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof O 𝒜 m hm
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left ≫ 𝒜.X.hom) := by
    rw [Over.w (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X)]; infer_instance
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) :=
    IsSeparated.of_comp _ 𝒜.X.hom
  have hcomp : a.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left =
      b.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left := by
    rw [← Over.comp_left, ← Over.comp_left, AvSplit.T4.comp_mulN, AvSplit.T4.comp_mulN, ha, hb]
  let p : Spec (.of (IsLocalRing.ResidueField w)) ⟶ Spec (.of w) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))
  have hp : p ≫ a.left = p ≫ b.left := congrArg Over.Hom.left hab
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
    (IsLocalRing.ResidueField w) (Spec (.of w)) p
  haveI : Epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))) := by
    have := AvSplit.T4.epi_spec_field ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p)).hom
    rwa [CommRingCat.ofHom_hom] at this
  have hx : (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ a.left =
      (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ b.left := by
    rw [← cancel_epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))),
      ← Category.assoc, hfac, ← Category.assoc, hfac]
    exact hp
  exact Over.OverMorphism.ext (AvSplit.T4.unramifiedSectionsEq (Spec (.of w)) 𝒜.X.left 𝒜.X.left _
    a.left b.left inferInstance hcomp _ hx)

end Omega

section OmegaForward

variable {K : Type} [Field K]

/-- The restriction `σ|_w : w → w` of an element of the decomposition group of `w ⊆ Ω`. -/
def resWΩ {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hd : σ ∈ w.decompositionSubgroup K) : w →+* w :=
  MulSemiringAction.toRingHom (w.decompositionSubgroup K) w ⟨σ, hd⟩

/-- **(a) ⇒ (b) of Serre–Tate's Theorem 1 over any field `Ω ⊇ K` (proved).** If `A` has good reduction at
`O`, then for every valuation ring `w` of `Ω` over `O`, every element of the inertia group of `w` in
`Aut(Ω/K)` fixes `A(Ω)[m]` for every `m ≥ 1` invertible in `O`. -/
theorem inertiaTrivialOn_of_goodReduction_any (O : ValuationSubring K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (A : Grp (Over (Spec (.of K)))) (hA : HasGoodReduction A O)
    (m : ℕ) (hmO : IsUnit (m : O)) : InertiaTrivialOn A w m := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hA
  intro σ hσ x hx
  obtain ⟨hd, hi⟩ := hσ
  let s := resWΩ w σ hd
  have hs1 : (CommRingCat.ofHom (toW O w hw) ≫ CommRingCat.ofHom s) =
      CommRingCat.ofHom (toW O w hw) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext a
    change σ (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
    exact σ.commutes _
  have hs2 : (CommRingCat.ofHom s ≫ CommRingCat.ofHom (IsLocalRing.residue w)) =
      CommRingCat.ofHom (IsLocalRing.residue w) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext a
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi
    have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
    change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a =
      IsLocalRing.residue w a at h1
    rw [← IsLocalRing.ResidueField.residue_smul] at h1
    exact h1
  obtain ⟨x', hx'⟩ := iotaΩ_comp_surjective hw 𝒜 (GΩ Ω 𝒜 e x)
  let x'' : PwΩ hw ⟶ 𝒜.X :=
    Over.homMk (Spec.map (CommRingCat.ofHom s) ≫ x'.left) (by
      have hx'w := Over.w x'
      simp only [Over.mk_hom] at hx'w ⊢
      rw [Category.assoc, hx'w, ← Spec.map_comp, hs1])
  have hxm : x ^ m = 1 := hx
  have hσx : galAct A σ x ^ m = 1 := by
    rw [← PkgI2.galAct_pow, hxm]
    exact PkgI2.galAct_one _ _
  -- `x''` lifts `σ x`
  have hlift : iotaΩ hw ≫ x'' = GΩ Ω 𝒜 e (galAct A σ x) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GΩ_left]
    have h1 : (galAct A σ x ≫ (e.inv.hom.hom : A.X ⟶
          (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left =
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
            (x ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left := by
      simp only [galAct, PkgI2.galHom, Category.assoc, Over.comp_left]
      rfl
    rw [h1]
    have h2 : (x ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (AvSplit.T4.fK K O) = Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left := by
      rw [← GΩ_left, ← hx']
      rfl
    refine Eq.trans ?_ ((congrArg (fun t => Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t)
      h2.symm).trans (Category.assoc _ _ _).symm)
    show Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  have hpow1 : x' ^ m = 1 := by
    apply iotaΩ_comp_injective hw 𝒜
    show iotaΩ hw ≫ x' ^ m = iotaΩ hw ≫ 1
    rw [MonObj.comp_pow, hx', ← map_pow, hxm, map_one, MonObj.comp_one]
  have hpow2 : x'' ^ m = 1 := by
    apply iotaΩ_comp_injective hw 𝒜
    show iotaΩ hw ≫ x'' ^ m = iotaΩ hw ≫ 1
    rw [MonObj.comp_pow, hlift, ← map_pow, hσx, map_one, MonObj.comp_one]
  have hred : rhoΩ hw ≫ x'' = rhoΩ hw ≫ x' := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left
    rw [← Category.assoc, ← Spec.map_comp, hs2]
  have heq := rhoΩ_inj hw 𝒜 m hmO x'' x' hpow2 hpow1 hred
  apply GΩ_injective 𝒜 e
  rw [← hlift, heq, hx']

end OmegaForward

end NOSProof

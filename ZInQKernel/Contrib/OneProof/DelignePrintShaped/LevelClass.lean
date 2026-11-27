import ZInQKernel.Contrib.OneProof.DelignePrintShaped.Bridges

/-! # The row `deligneCanonicalModelY3EveryPrint`: the fibre half of the level-3 classification over `ℂ`

Proved here (standard axioms only), for the moduli objects `(ℂ²/Λ_τ, ι_τ, η_w)` of the points `[z, g]` of
`B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` (`IsLevelPoint`):

* `levelClassification_of_corr`: given the analytic representation of homomorphisms of complex abelian varieties
  (`ZInQ.HomUnify.HomLatticeCorr`: Birkenhake–Lange, *Complex abelian varieties*, §1.2, with GAGA for the
  realization half), two moduli objects are isomorphic exactly when their points lie in one double coset
  (`LevelClassification`);
* `levelClassification_of`: the same from the textbook field `ZInQ.HomLattice.GAGAMorphism` alone, through
  `AvSplit.Final.h69` and the proved uniformization theorem `uniformizationLeafAll_proof`.

*The argument.* Both points are moved to unit representatives `(τ, u)`, `(τ', u')` with `τ, τ' ∈ ℍ`,
`u, u' ∈ 𝒪̂^×`, `w u ≡ 1` and `w' u' ≡ 1 (mod 3𝒪̂)` (`dcRelPM_symm`, `dcRelPM_trans`).
* (⇒) An isomorphism `φ` lifts to a `ℂ`-linear map commuting with `ι(𝒪)`, hence to a scalar `c`
  (`LevelClass.lift_scalar_of_iso`); then `c (τ, 1)ᵀ = ι(β)(τ', 1)ᵀ` with `β ∈ 𝒪`, the inverse isomorphism
  gives `β' ∈ 𝒪` with `β β' = β' β = 1` and `ι(β')(τ, 1)ᵀ ∈ ℂ^× (τ', 1)ᵀ`, i.e. `β' τ = τ'`; comparing the
  level points gives `w β ≡ w' (mod 3𝒪)`, so that `k = u⁻¹ β u' ∈ K₃` and `u' = β' u k`
  (`LevelClass.dcRelPM_of_iso`).
* (⇐) For `(τ', u') = (γ τ, γ u k)` with `k ∈ K₃`, `γ = u' k⁻¹ u⁻¹` and `γ⁻¹ = u k u'⁻¹` lie in `𝒪̂ ∩ B = 𝒪`;
  the scalar `c = j(γ, τ)⁻¹` satisfies `c ℓ_τ(x) = ℓ_{τ'}(x γ⁻¹)`, so it maps `Λ_τ` onto `Λ_{τ'}`, commutes
  with `ι`, and carries `η_w` to `η_{w'}` because `w γ⁻¹ ≡ w' (mod 3𝒪)`; the realization half of the analytic
  representation turns `c` and `c⁻¹` into mutually inverse isomorphisms (`LevelClass.nonempty_iso_of_dcRelPM`).
-/

set_option autoImplicit false

noncomputable section

namespace DelignePS

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open Y3Hodge (HPM DCRelPM toPM)

namespace LevelClass

/-! ## 1. `ℓ_τ` through `ι : B → M₂(ℂ)` -/

/-- `ℓ_τ(b) = ι(b)(τ, 1)ᵀ`. -/
theorem ell_eq_mulVec (τ : UpperHalfPlane) (b : B) : ell τ b = (iotaC b).mulVec ![(τ : ℂ), 1] := by
  funext i
  fin_cases i <;>
    simp [ell, Y3Fix.ellE_apply, Y3Fix.ellF, iotaC_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem ell_sub (τ : UpperHalfPlane) (x y : B) : ell τ (x - y) = ell τ x - ell τ y := by
  rw [ell_eq_mulVec, ell_eq_mulVec, ell_eq_mulVec, map_sub, Matrix.sub_mulVec]

/-- If `ι(β)(τ', 1)ᵀ = c (τ, 1)ᵀ`, then `c ℓ_τ(x) = ℓ_{τ'}(x β)` for every `x ∈ B`. -/
theorem smul_ell_eq {τ τ' : UpperHalfPlane} {β : B} {c : ℂ}
    (h : (iotaC β).mulVec ![(τ' : ℂ), 1] = c • ![(τ : ℂ), 1]) (x : B) :
    c • ell τ x = ell τ' (x * β) := by
  rw [ell_eq_mulVec, ell_eq_mulVec, map_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]

/-- If moreover `β ∈ 𝒪`, then `c Λ_τ ⊆ Λ_{τ'}`. -/
theorem smul_mem_lattice {τ τ' : UpperHalfPlane} {β : B} (hβ : β ∈ O) {c : ℂ}
    (h : (iotaC β).mulVec ![(τ' : ℂ), 1] = c • ![(τ : ℂ), 1]) {v : Fin 2 → ℂ}
    (hv : v ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne') :
    c • v ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne' := by
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_qmLattice τ.im_pos.ne' hv
  rw [← ell_eq_mulVec, smul_ell_eq h, ell_mem_iff]
  exact O.mul_mem hb hβ

/-- `ι(γ)(z, 1)ᵀ = (az + b, cz + d)ᵀ` for `ι(γ) = [[a, b], [c, d]]`: the numerator and denominator of the Möbius
transformation `ι(γ)`. -/
theorem iotaC_mulVec_eq (gam : B) (hgam : ShimuraGlue.nrdQ ℚ gam ≠ 0) (z : ℂ) :
    (iotaC gam).mulVec ![z, 1] =
      ![UpperHalfPlane.num (iotaGL gam hgam) z, UpperHalfPlane.denom (iotaGL gam hgam) z] := by
  funext i
  fin_cases i <;> simp [iotaC_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.num,
    UpperHalfPlane.denom, iotaGL_coe]

theorem vec_eq_smul {a b : ℂ} (hb : b ≠ 0) : ![a, b] = b • ![a / b, 1] := by
  funext i
  fin_cases i <;> simp [mul_div_cancel₀ _ hb]

/-- `γ τ = τ'` gives `ι(γ)(τ, 1)ᵀ = j (τ', 1)ᵀ` with `j = j(γ, τ) ≠ 0`. -/
theorem iotaC_mulVec_of_mob {gam : B} (hgam : ShimuraGlue.nrdQ ℚ gam ≠ 0) {τ τ' : UpperHalfPlane}
    (hmob : Y3Hodge.mobPM (iotaGL gam hgam) (toPM τ) = toPM τ') :
    ∃ j : ℂ, j ≠ 0 ∧ (iotaC gam).mulVec ![(τ : ℂ), 1] = j • ![(τ' : ℂ), 1] := by
  have hj : UpperHalfPlane.denom (iotaGL gam hgam) (τ : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  have hnum : UpperHalfPlane.num (iotaGL gam hgam) (τ : ℂ) / UpperHalfPlane.denom (iotaGL gam hgam) (τ : ℂ) =
      (τ' : ℂ) := congrArg Subtype.val hmob
  refine ⟨_, hj, ?_⟩
  rw [iotaC_mulVec_eq gam hgam, ← hnum, vec_eq_smul hj]

/-- Conversely, `ι(γ)(τ, 1)ᵀ = j (τ', 1)ᵀ` with `j ≠ 0` gives `γ τ = τ'`. -/
theorem mob_of_iotaC_mulVec {gam : B} (hgam : ShimuraGlue.nrdQ ℚ gam ≠ 0) {τ τ' : UpperHalfPlane} {j : ℂ}
    (hj : j ≠ 0) (h : (iotaC gam).mulVec ![(τ : ℂ), 1] = j • ![(τ' : ℂ), 1]) :
    Y3Hodge.mobPM (iotaGL gam hgam) (toPM τ) = toPM τ' := by
  apply Subtype.ext
  show UpperHalfPlane.num (iotaGL gam hgam) (τ : ℂ) / UpperHalfPlane.denom (iotaGL gam hgam) (τ : ℂ) =
    (τ' : ℂ)
  rw [iotaC_mulVec_eq gam hgam] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h0 h1
  rw [h0, h1, mul_div_cancel_left₀ _ hj]

/-! ## 2. Uniformizations: equality of values modulo the lattice -/

open scoped MonObj in
theorem unif_eq_of_sub_mem {A : PkgI3.AbVar ℂ} {Λ : Submodule ℤ (Fin 2 → ℂ)}
    {Φ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)} (hU : IsUniformization (RingHom.id ℂ) Λ Φ)
    {x y : Fin 2 → ℂ} (h : x - y ∈ Λ) : Φ x = Φ y := by
  have e := hU.1 (x - y) y
  rw [sub_add_cancel, (hU.2.1 _).2 h, _root_.one_mul] at e
  exact e

open scoped MonObj in
theorem sub_mem_of_unif_eq {A : PkgI3.AbVar ℂ} {Λ : Submodule ℤ (Fin 2 → ℂ)}
    {Φ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)} (hU : IsUniformization (RingHom.id ℂ) Λ Φ)
    {x y : Fin 2 → ℂ} (h : Φ x = Φ y) : x - y ∈ Λ := by
  rw [← hU.2.1]
  have e := hU.1 (x - y) y
  rw [sub_add_cancel, h] at e
  exact mul_eq_right.1 e.symm

/-! ## 3. Thirds in `𝒪` and in `𝒪̂` -/

theorem three_mul_third (X : BAQ) : (3 : BAQ) * ((3 : ℚ)⁻¹ • X) = X := by
  have e3 : (3 : BAQ) = algebraMap ℚ BAQ 3 := (map_ofNat (algebraMap ℚ BAQ) 3).symm
  have hinv : algebraMap ℚ BAQ 3 * algebraMap ℚ BAQ (3 : ℚ)⁻¹ = 1 := by rw [← map_mul]; norm_num
  rw [Algebra.smul_def, ← mul_assoc, e3, hinv, one_mul]

theorem third_smul_three_mul (X : BAQ) : (3 : ℚ)⁻¹ • ((3 : BAQ) * X) = X := by
  have e3 : (3 : BAQ) = algebraMap ℚ BAQ 3 := (map_ofNat (algebraMap ℚ BAQ) 3).symm
  have hinv : algebraMap ℚ BAQ (3 : ℚ)⁻¹ * algebraMap ℚ BAQ 3 = 1 := by rw [← map_mul]; norm_num
  rw [Algebra.smul_def, ← mul_assoc, e3, hinv, one_mul]

/-- `x/3 ∈ 𝒪` gives `x ∈ 3𝒪̂`. -/
theorem bEmb_eq_three_mul {x : B} (h : (3 : ℚ)⁻¹ • x ∈ O) : ∃ T ∈ OhatQ, bEmb x = 3 * T :=
  ⟨bEmb ((3 : ℚ)⁻¹ • x), bEmb_mem_of_inO h, by rw [map_smul, three_mul_third]⟩

/-- `x ∈ 3𝒪̂` gives `x/3 ∈ 𝒪` (`𝒪̂ ∩ B = 𝒪`). -/
theorem third_mem_of_bEmb {x : B} {T : BAQ} (hT : T ∈ OhatQ) (h : bEmb x = 3 * T) :
    (3 : ℚ)⁻¹ • x ∈ O := by
  apply inO_of_bEmb_mem
  rw [map_smul, h, third_smul_three_mul]
  exact hT

/-! ## 4. The analytic representation of an isomorphism is a scalar -/

/-- A `ℂ`-linear map of `ℂ²` commuting with `ι(𝒪)` is a scalar (the argument of `RayClassCFT.liftM_scalar`,
for a map between two tori). -/
theorem scalar_of_comm (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hM : ∀ (a : O) (z : Fin 2 → ℂ), M ((qmMat a).mulVec z) = (qmMat a).mulVec (M z))
    (z : Fin 2 → ℂ) : M z = (M ![1, 0] 0) • z := by
  have hs : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  have hI0 := hM oI ![1, 0]
  have hI1 := hM oI ![0, 1]
  have hJ0 := hM oJ ![1, 0]
  rw [qmMat_oI] at hI0 hI1
  rw [qmMat_oJ] at hJ0
  have e0 : (!![(√2 : ℂ), 0; 0, -(√2 : ℂ)]).mulVec ![1, 0] = (√2 : ℂ) • ![1, 0] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  have e1 : (!![(√2 : ℂ), 0; 0, -(√2 : ℂ)]).mulVec ![0, 1] = (-(√2 : ℂ)) • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  have eJ : (!![(0 : ℂ), -3; 1, 0]).mulVec ![1, 0] = ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  rw [e0, map_smul] at hI0
  rw [e1, map_smul] at hI1
  rw [eJ] at hJ0
  have u1 : M ![1, 0] 1 = 0 := by
    have := congrFun hI0 1
    simp [Matrix.mulVec, dotProduct] at this
    have h2 : (√2 : ℂ) * (2 * M ![1, 0] 1) = 0 := by linear_combination this
    have := (mul_eq_zero.mp h2).resolve_left hs
    linear_combination this / 2
  have w0 : M ![0, 1] 0 = 0 := by
    have := congrFun hI1 0
    simp [Matrix.mulVec, dotProduct] at this
    have h2 : (√2 : ℂ) * (2 * M ![0, 1] 0) = 0 := by linear_combination -this
    have := (mul_eq_zero.mp h2).resolve_left hs
    linear_combination this / 2
  have w1 : M ![0, 1] 1 = M ![1, 0] 0 := by
    have := congrFun hJ0 1
    simpa [Matrix.mulVec, dotProduct] using this
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  rw [hz, map_add, map_smul, map_smul]
  ext i; fin_cases i <;> simp [u1, w0, w1] <;> ring

/-- **An isomorphism `(ℂ²/Λ_τ, ι) ≅ (ℂ²/Λ_{τ'}, ι)` is induced by a scalar** (lifting half of the analytic
representation, then `scalar_of_comm`). -/
theorem lift_scalar_of_iso (hL : ZInQ.HomUnify.HomLinearLift) {P P' : QML3 ℂ}
    {τ τ' : UpperHalfPlane} {Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)}
    {Φu' : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hU' : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ'.im_pos.ne') Φu')
    (hι : IotaCompatible P Φu) (hι' : IotaCompatible P' Φu') (f : P.Iso P') :
    ∃ c : ℂ, ∀ z, Φu z ≫ f.φ.hom = Φu' (c • z) := by
  obtain ⟨M, hM⟩ := hL ℂ P.A P'.A (RingHom.id ℂ) 2 2 _ _ Φu Φu' (RayClassCFT.dim_two P)
    (RayClassCFT.dim_two P') hU hU' f.φ
  have hc : ∀ (a : O) (z : Fin 2 → ℂ), M ((qmMat a).mulVec z) = (qmMat a).mulVec (M z) := by
    intro a z
    have h := congrArg (fun N => N z) (RayClassCFT.lift_unique hU'
      (M := M ∘ₗ Matrix.mulVecLin (qmMat a)) (M' := Matrix.mulVecLin (qmMat a) ∘ₗ M) fun z => by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
        rw [hM, hι, hι', hM, Category.assoc, Category.assoc, f.equivariant a])
    simpa using h
  exact ⟨M ![1, 0] 0, fun z => by rw [← hM, scalar_of_comm M hc z]⟩

/-! ## 5. (⇐) An isomorphism from a scalar carrying the lattices and the level points -/

/-- **A scalar `c` with `c Λ_τ ⊆ Λ_{τ'}`, `c⁻¹ Λ_{τ'} ⊆ Λ_τ`, carrying the level points of `P` to those of `P'`,
induces an isomorphism `P ≅ P'`** (realization half of the analytic representation). -/
theorem nonempty_iso_of_scalar (hC : ZInQ.HomUnify.HomLatticeCorr) {P P' : QML3 ℂ}
    {τ τ' : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)} {Φu' : (Fin 2 → ℂ) → CPts P'.A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hU' : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ'.im_pos.ne') Φu')
    (hι : IotaCompatible P Φu) (hι' : IotaCompatible P' Φu') {c : ℂ} (hc : c ≠ 0)
    (h1 : ∀ v ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne', c • v ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne')
    (h2 : ∀ v ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne', c⁻¹ • v ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne')
    (hlev : ∀ a : O, ∃ z, Additive.toMul (P.e.eta a) = Φu z ∧
      Additive.toMul (P'.e.eta a) = Φu' (c • z)) :
    Nonempty (P.Iso P') := by
  obtain ⟨φ, hφ, -⟩ := hC.2 P.A P'.A 2 2 _ _ Φu Φu' (RayClassCFT.dim_two P) (RayClassCFT.dim_two P')
    hU hU' (c • LinearMap.id) (fun z hz => h1 z hz)
  obtain ⟨ψ, hψ, -⟩ := hC.2 P'.A P.A 2 2 _ _ Φu' Φu (RayClassCFT.dim_two P') (RayClassCFT.dim_two P)
    hU' hU (c⁻¹ • LinearMap.id) (fun z hz => h2 z hz)
  have hφ' : ∀ z, Φu z ≫ φ.hom = Φu' (c • z) := fun z => (hφ z).symm
  have hψ' : ∀ z, Φu' z ≫ ψ.hom = Φu (c⁻¹ • z) := fun z => (hψ z).symm
  refine ⟨⟨φ, ψ, ?_, ?_, fun a => ?_, fun a => ?_⟩⟩
  · apply ZInQ.HomUnify.hom_ext_of_cpts
    intro p
    obtain ⟨z, rfl⟩ := hU.2.2.1 p
    rw [← Category.assoc, hφ', hψ', smul_smul, inv_mul_cancel₀ hc, one_smul, Category.comp_id]
  · apply ZInQ.HomUnify.hom_ext_of_cpts
    intro p
    obtain ⟨z, rfl⟩ := hU'.2.2.1 p
    rw [← Category.assoc, hψ', hφ', smul_smul, mul_inv_cancel₀ hc, one_smul, Category.comp_id]
  · apply ZInQ.HomUnify.hom_ext_of_cpts
    intro p
    obtain ⟨z, rfl⟩ := hU.2.2.1 p
    rw [← Category.assoc, ← hι, hφ', ← Category.assoc, hφ', ← hι', Matrix.mulVec_smul]
  · obtain ⟨z, hz, hz'⟩ := hlev a
    have e : Additive.toMul (P.e.eta a) ≫ φ.hom = Additive.toMul (P'.e.eta a) :=
      (congrArg (· ≫ φ.hom) hz).trans ((hφ' z).trans hz'.symm)
    exact congrArg Additive.ofMul e

/-! ## 6. (⇒) An isomorphism of moduli objects relates the unit representatives -/

/-- **(⇒)** If `(ℂ²/Λ_τ, ι, η_w) ≅ (ℂ²/Λ_{τ'}, ι, η_{w'})` with `w u ≡ 1`, `w' u' ≡ 1 (mod 3𝒪̂)`, `u, u' ∈ 𝒪̂^×`,
then `(τ, u)` and `(τ', u')` lie in one double coset. -/
theorem dcRelPM_of_iso (hL : ZInQ.HomUnify.HomLinearLift) {P P' : QML3 ℂ} {τ τ' : UpperHalfPlane}
    {u u' : BAQˣ} {w w' : O} (hu : u ∈ OhatU) (hu' : u' ∈ OhatU) (hw : InvModThree u w)
    (hw' : InvModThree u' w') (hT : IsLevelTorusAt P τ w) (hT' : IsLevelTorusAt P' τ' w')
    (f : P.Iso P') : DCRelPM (toPM τ) u (toPM τ') u' := by
  obtain ⟨Φu, hU, hι, hη⟩ := hT
  obtain ⟨Φu', hU', hι', hη'⟩ := hT'
  obtain ⟨c, hc⟩ := lift_scalar_of_iso hL hU hU' hι hι' f
  obtain ⟨c', hc'⟩ := lift_scalar_of_iso hL hU' hU hι' hι f.symm
  have hc'' : ∀ z, Φu' z ≫ f.ψ.hom = Φu (c' • z) := hc'
  -- `c' c = 1`
  have hcc : c' * c = 1 := by
    have h := RayClassCFT.lift_unique hU (M := (c' * c) • LinearMap.id) (M' := LinearMap.id) fun z => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [mul_smul, ← hc'', ← hc, Category.assoc, f.left, Category.comp_id]
    have h2 := congrArg (fun N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) => N ![1, 0] 0) h
    simpa using h2
  have hc0' : c' ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  -- `c (τ, 1)ᵀ = ι(β)(τ', 1)ᵀ` and `c' (τ', 1)ᵀ = ι(β')(τ, 1)ᵀ` with `β, β' ∈ 𝒪`
  have hm : c • ![(τ : ℂ), 1] ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne' := by
    rw [← hU'.2.1, ← hc, (hU.2.1 _).2 (qmVec0_mem τ.im_pos.ne')]
    exact MonObj.one_comp _
  have hm' : c' • ![(τ' : ℂ), 1] ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
    rw [← hU.2.1, ← hc'', (hU'.2.1 _).2 (qmVec0_mem τ'.im_pos.ne')]
    exact MonObj.one_comp _
  obtain ⟨β, hβO, hβ⟩ := exists_of_mem_qmLattice τ'.im_pos.ne' hm
  obtain ⟨β', hβO', hβ'⟩ := exists_of_mem_qmLattice τ.im_pos.ne' hm'
  have hββ' : β * β' = 1 := by
    apply iota_eig_inj τ.im_pos.ne'
    rw [map_mul, ← Matrix.mulVec_mulVec, hβ', Matrix.mulVec_smul, hβ, smul_smul, hcc, one_smul,
      map_one, Matrix.one_mulVec]
  have hβ'β : β' * β = 1 := by
    apply iota_eig_inj τ'.im_pos.ne'
    rw [map_mul, ← Matrix.mulVec_mulVec, hβ, Matrix.mulVec_smul, hβ', smul_smul, mul_comm c c', hcc,
      one_smul, map_one, Matrix.one_mulVec]
  have hn : ShimuraGlue.nrdQ ℚ β' ≠ 0 := nrd_ne_zero_of_mul hβ'β
  -- the level points: `w β ≡ w' (mod 3𝒪)`
  have hcong : (3 : ℚ)⁻¹ • ((w : B) * β - (w' : B)) ∈ O := by
    have e1 : Φu' ((3 : ℂ)⁻¹ • ell τ' (w' : B)) = Φu' (c • ((3 : ℂ)⁻¹ • ell τ (w : B))) := by
      have h1 := hη' 1
      have h2 := hη 1
      simp only [one_mul] at h1 h2
      have h3 : Additive.toMul (P'.e.eta 1) = Additive.toMul (P.e.eta 1) ≫ f.φ.hom :=
        congrArg Additive.toMul (f.level 1).symm
      exact h1.symm.trans (h3.trans ((congrArg (· ≫ f.φ.hom) h2).trans (hc _)))
    have h3 : c • ((3 : ℂ)⁻¹ • ell τ (w : B)) - (3 : ℂ)⁻¹ • ell τ' (w' : B) ∈
        BPAnalytic.QM.qmLattice τ'.im_pos.ne' := sub_mem_of_unif_eq hU' e1.symm
    have key : c • ((3 : ℂ)⁻¹ • ell τ (w : B)) - (3 : ℂ)⁻¹ • ell τ' (w' : B) =
        ell τ' ((3 : ℚ)⁻¹ • ((w : B) * β - (w' : B))) := by
      rw [smul_comm c, smul_ell_eq hβ, ← smul_sub, ← ell_sub, third_smul_ell]
    rwa [key, ell_mem_iff] at h3
  obtain ⟨T, hT, hTe⟩ := bEmb_eq_three_mul hcong
  obtain ⟨y, hy, hwu⟩ := hw
  obtain ⟨y', hy', hwu'⟩ := hw'
  -- `k = u⁻¹ β u'`, where `β = β'⁻¹`
  obtain ⟨k, hk_def⟩ : ∃ k : BAQˣ, k = u⁻¹ * bUnit β β' hββ' hβ'β * u' := ⟨_, rfl⟩
  have hkv : (k : BAQ) = ((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ) := by
    rw [hk_def]; simp only [Units.val_mul]; rfl
  have hkiv : ((k⁻¹ : BAQˣ) : BAQ) = ((u'⁻¹ : BAQˣ) : BAQ) * bEmb β' * (u : BAQ) := by
    rw [hk_def, mul_inv_rev, mul_inv_rev, inv_inv]; simp only [Units.val_mul, mul_assoc]; rfl
  have hUi : ((u⁻¹ : BAQˣ) : BAQ) = bEmb (w : B) - 3 * (y * ((u⁻¹ : BAQˣ) : BAQ)) := by
    have e : bEmb (w : B) = (bEmb (w : B) * (u : BAQ)) * ((u⁻¹ : BAQˣ) : BAQ) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [hwu] at e
    rw [e]; noncomm_ring
  have hWB : bEmb (w : B) * bEmb β = bEmb (w' : B) + 3 * T := by
    rw [← map_mul bEmb, ← sub_eq_iff_eq_add', ← map_sub bEmb, hTe]
  have hK3 : k ∈ K3Q := by
    refine ⟨?_, ?_, y' + T * (u' : BAQ) - y * (k : BAQ), ?_, ?_⟩
    · rw [hkv]; exact OhatQ_mul (OhatQ_mul hu.2 (bEmb_mem_of_inO hβO)) hu'.1
    · rw [hkiv]; exact OhatQ_mul (OhatQ_mul hu'.2 (bEmb_mem_of_inO hβO')) hu.1
    · rw [sub_eq_add_neg]
      exact OhatQ_add (OhatQ_add hy' (OhatQ_mul hT hu'.1)) (OhatQ_neg (OhatQ_mul hy (by
        rw [hkv]; exact OhatQ_mul (OhatQ_mul hu.2 (bEmb_mem_of_inO hβO)) hu'.1)))
    · rw [hkv]
      calc ((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ)
          = (bEmb (w : B) - 3 * (y * ((u⁻¹ : BAQˣ) : BAQ))) * bEmb β * (u' : BAQ) := by rw [← hUi]
        _ = (bEmb (w : B) * bEmb β) * (u' : BAQ) -
              3 * (y * (((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ))) := by noncomm_ring
        _ = (bEmb (w' : B) + 3 * T) * (u' : BAQ) -
              3 * (y * (((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ))) := by rw [hWB]
        _ = bEmb (w' : B) * (u' : BAQ) + 3 * (T * (u' : BAQ)) -
              3 * (y * (((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ))) := by noncomm_ring
        _ = 1 + 3 * (y' + T * (u' : BAQ) - y * (((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ))) := by
          rw [hwu']; noncomm_ring
  refine ⟨β', hn, mob_of_iotaC_mulVec hn hc0' hβ', k, hK3, ?_⟩
  rw [hkv]
  have e : bEmb β' * bEmb β = 1 := by rw [← map_mul bEmb, hβ'β, map_one]
  calc (u' : BAQ) = (bEmb β' * bEmb β) * (u' : BAQ) := by rw [e, one_mul]
    _ = bEmb β' * ((u : BAQ) * ((u⁻¹ : BAQˣ) : BAQ)) * bEmb β * (u' : BAQ) := by
        rw [Units.mul_inv, mul_one]
    _ = bEmb β' * (u : BAQ) * (((u⁻¹ : BAQˣ) : BAQ) * bEmb β * (u' : BAQ)) := by noncomm_ring

/-! ## 7. (⇐) Related unit representatives give isomorphic moduli objects -/

/-- **(⇐)** If `(τ, u)` and `(τ', u')` lie in one double coset (`u, u' ∈ 𝒪̂^×`, `w u ≡ 1`, `w' u' ≡ 1 (mod 3𝒪̂)`),
then `(ℂ²/Λ_τ, ι, η_w) ≅ (ℂ²/Λ_{τ'}, ι, η_{w'})`. -/
theorem nonempty_iso_of_dcRelPM (hC : ZInQ.HomUnify.HomLatticeCorr) {P P' : QML3 ℂ}
    {τ τ' : UpperHalfPlane} {u u' : BAQˣ} {w w' : O} (hu : u ∈ OhatU) (hu' : u' ∈ OhatU)
    (hw : InvModThree u w) (hw' : InvModThree u' w') (hT : IsLevelTorusAt P τ w)
    (hT' : IsLevelTorusAt P' τ' w') (h : DCRelPM (toPM τ) u (toPM τ') u') :
    Nonempty (P.Iso P') := by
  obtain ⟨gam, hgam, hmob, k, hk, hg⟩ := h
  obtain ⟨Φu, hU, hι, hη⟩ := hT
  obtain ⟨Φu', hU', hι', hη'⟩ := hT'
  obtain ⟨y, hy, hwu⟩ := hw
  obtain ⟨y', hy', hwu'⟩ := hw'
  obtain ⟨hk1, hk2, tk, htk, hkt⟩ := hk
  -- `γ ∈ 𝒪^×`
  have hG : bEmb gam = (u' : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) * ((u⁻¹ : BAQˣ) : BAQ) := by
    rw [hg, mul_assoc, mul_assoc, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have hGi : bEmb (binv gam) = (u : BAQ) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ) := by
    have e1 : bEmb (binv gam) * bEmb gam = 1 := by rw [← map_mul bEmb, binv_mul hgam, map_one]
    calc bEmb (binv gam) = bEmb (binv gam) * ((u' : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ)) := by
          rw [Units.mul_inv, mul_one]
      _ = (bEmb (binv gam) * bEmb gam) * (u : BAQ) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ) := by
          rw [hg]; noncomm_ring
      _ = (u : BAQ) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ) := by rw [e1, one_mul]
  have hgO : gam ∈ O := inO_of_bEmb_mem (by rw [hG]; exact OhatQ_mul (OhatQ_mul hu'.1 hk2) hu.2)
  have hgO' : binv gam ∈ O :=
    inO_of_bEmb_mem (by rw [hGi]; exact OhatQ_mul (OhatQ_mul hu.1 hk1) hu'.2)
  -- the scalar: `ι(γ)(τ, 1)ᵀ = j (τ', 1)ᵀ`, `ι(γ⁻¹)(τ', 1)ᵀ = j⁻¹ (τ, 1)ᵀ`
  obtain ⟨j, hj, hvec⟩ := iotaC_mulVec_of_mob hgam hmob
  have hvec' : (iotaC (binv gam)).mulVec ![(τ' : ℂ), 1] = j⁻¹ • ![(τ : ℂ), 1] := by
    have e : (iotaC (binv gam)).mulVec ((iotaC gam).mulVec ![(τ : ℂ), 1]) = ![(τ : ℂ), 1] := by
      rw [Matrix.mulVec_mulVec, ← map_mul, binv_mul hgam, map_one, Matrix.one_mulVec]
    rw [hvec, Matrix.mulVec_smul] at e
    rw [← e, smul_smul, inv_mul_cancel₀ hj, one_smul]
  -- the level points: `w' ≡ w γ⁻¹ (mod 3𝒪)`
  have hcong : (3 : ℚ)⁻¹ • ((w' : B) - (w : B) * binv gam) ∈ O := by
    refine third_mem_of_bEmb (T := -((tk + y * (k : BAQ) + -y') * ((u'⁻¹ : BAQˣ) : BAQ)))
      (OhatQ_neg (OhatQ_mul (OhatQ_add (OhatQ_add htk (OhatQ_mul hy hk1)) (OhatQ_neg hy')) hu'.2)) ?_
    rw [map_sub, map_mul, hGi]
    calc bEmb (w' : B) - bEmb (w : B) * ((u : BAQ) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ))
        = (bEmb (w' : B) * (u' : BAQ)) * ((u'⁻¹ : BAQˣ) : BAQ) -
            (bEmb (w : B) * (u : BAQ)) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ) := by
          rw [mul_assoc (bEmb (w' : B)), Units.mul_inv, mul_one]; noncomm_ring
      _ = (1 + 3 * y') * ((u'⁻¹ : BAQˣ) : BAQ) - (1 + 3 * y) * (k : BAQ) * ((u'⁻¹ : BAQˣ) : BAQ) := by
          rw [hwu', hwu]
      _ = 3 * -((tk + y * (k : BAQ) + -y') * ((u'⁻¹ : BAQˣ) : BAQ)) := by
          rw [hkt]; noncomm_ring
  refine nonempty_iso_of_scalar hC hU hU' hι hι' (inv_ne_zero hj)
    (fun v hv => smul_mem_lattice hgO' hvec' hv)
    (fun v hv => by rw [inv_inv]; exact smul_mem_lattice hgO hvec hv) fun a => ?_
  refine ⟨(3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B)), hη a, ?_⟩
  rw [hη' a]
  apply unif_eq_of_sub_mem hU'
  have key : (3 : ℂ)⁻¹ • ell τ' ((a : B) * (w' : B)) - j⁻¹ • ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) =
      ell τ' ((a : B) * ((3 : ℚ)⁻¹ • ((w' : B) - (w : B) * binv gam))) := by
    rw [smul_comm j⁻¹, smul_ell_eq hvec', ← smul_sub, ← ell_sub, third_smul_ell, mul_smul_comm,
      mul_sub, mul_assoc]
  show (3 : ℂ)⁻¹ • ell τ' ((a : B) * (w' : B)) - j⁻¹ • ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) ∈ _
  rw [key, ell_mem_iff]
  exact O.mul_mem a.2 hcong

/-- The classes of two objects agree exactly when the objects are isomorphic. -/
theorem mk_eq_iff_nonempty (P P' : QML3 ℂ) : M3.mk P = M3.mk P' ↔ Nonempty (P.Iso P') :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

end LevelClass

/-! ## 8. The fibre half of the level-3 classification -/

/-- **The fibre half of the level-3 classification over `ℂ`, from the analytic representation of
homomorphisms** (`ZInQ.HomUnify.HomLatticeCorr`). -/
theorem levelClassification_of_corr (hC : ZInQ.HomUnify.HomLatticeCorr) : LevelClassification := by
  intro P P' z g z' g' hP hP'
  obtain ⟨τ, u, w, hu, hr, hw, hT⟩ := hP
  obtain ⟨τ', u', w', hu', hr', hw', hT'⟩ := hP'
  rw [LevelClass.mk_eq_iff_nonempty]
  constructor
  · rintro ⟨f⟩
    exact dcRelPM_trans hr (dcRelPM_trans (LevelClass.dcRelPM_of_iso
      (ZInQ.HomUnify.homLinearLift_of_corr hC) hu hu' hw hw' hT hT' f) (dcRelPM_symm hr'))
  · intro h
    exact LevelClass.nonempty_iso_of_dcRelPM hC hu hu' hw hw' hT hT'
      (dcRelPM_trans (dcRelPM_symm hr) (dcRelPM_trans h hr'))

/-- **The fibre half of the level-3 classification over `ℂ`** (`LevelClassification`): two moduli objects
`(ℂ²/Λ_τ, ι_τ, η_w)` of points of `B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` are isomorphic exactly when the points are
equal, given the textbook field `GAGAMorphism` (with the proved uniformization theorem, it gives the analytic
representation of homomorphisms, `AvSplit.Final.h69`). -/
theorem levelClassification_of (hG : ZInQ.HomLattice.GAGAMorphism) : LevelClassification :=
  levelClassification_of_corr (AvSplit.Final.h69 uniformizationLeafAll_proof hG)

end DelignePS

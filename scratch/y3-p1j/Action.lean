import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30

set_option linter.all false

noncomputable section

namespace Y3P1j

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open Y3Fix SGRSplit HDec.VertWitness HDec.ModelGlue Y3Audit Y3RouteA
open scoped CategoryTheory.Obj

/-! ## 1. The generators of `N` acting on the moduli problem over a base

One combined operation `op α u`: `ι ↦ ι ∘ α`, `η ↦ η ∘ α ∘ (· u)`, for `α ∈ Aut 𝒪` and `u ∈ 𝒪^×`. (Elaborating the
two special cases directly makes the structure-instance elaborator loop; with `α` free it does not.) -/

section Ops

variable {S : Scheme.{0}}

/-- `op α u` on families. -/
def famOp (α : O ≃+* O) (u : Oˣ) (𝒜 : QMFamily S) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over _
  eta a := 𝒜.eta (α (a * u))
  eta_sec a := 𝒜.eta_sec _

theorem zm (u : Oˣ) : (0 : O) * (u : O) = 0 := MulZeroClass.zero_mul _

theorem op_zero (α : O ≃+* O) (u : Oˣ) : α ((0 : O) * (u : O)) = 0 := by rw [zm, map_zero]

/-- **The combined operation on objects of the printed moduli problem**, without the level clause. -/
def opNL (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S :=
  letI := 𝒜.grp
  { toQMFamily := famOp α u 𝒜.toQMFamily
    grp := 𝒜.grp
    geomConn := 𝒜.geomConn
    one_eq := 𝒜.one_eq.trans (congrArg 𝒜.eta (op_zero α u).symm)
    iota_hom := fun a => 𝒜.iota_hom (α a)
    iota_one := by
      change 𝒜.iota (α 1) = _
      rw [map_one]; exact 𝒜.iota_one
    iota_mul := fun a b => by
      change 𝒜.iota (α (a * b)) = 𝒜.iota (α b) ≫ 𝒜.iota (α a)
      rw [map_mul]; exact 𝒜.iota_mul _ _
    iota_add := fun a b => by
      change Over.homMk (𝒜.iota (α (a + b))) (𝒜.iota_over _) =
        Over.homMk (𝒜.iota (α a)) (𝒜.iota_over _) * Over.homMk (𝒜.iota (α b)) (𝒜.iota_over _)
      rw [map_add]; exact 𝒜.iota_add _ _
    eta_add := fun a b => by
      change secF 𝒜.toQMFamily (α ((a + b) * u)) = secF 𝒜.toQMFamily (α (a * u)) * secF 𝒜.toQMFamily (α (b * u))
      rw [add_mul, map_add]; exact 𝒜.eta_add _ _
    eta_linear := fun a b => by
      change 𝒜.eta (α (a * b * u)) = 𝒜.eta (α (b * u)) ≫ 𝒜.iota (α a)
      rw [_root_.mul_assoc, map_mul]; exact 𝒜.eta_linear _ _
    eta_three := fun b => by
      change 𝒜.eta (α (3 * b * u)) = 𝒜.eta (α (0 * u))
      rw [op_zero, _root_.mul_assoc, map_mul, map_ofNat]; exact 𝒜.eta_three _ }

theorem level_opNL (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : LevelPrint (opNL α u 𝒜) := by
  intro k _ _ s
  obtain ⟨h1, h2⟩ := 𝒜.level k s
  refine ⟨fun a => ?_, fun x hx => ?_⟩
  · change s ≫ 𝒜.eta (α (a * u)) = s ≫ 𝒜.eta (α (0 * u)) ↔ _
    rw [op_zero, h1]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨α.symm b * ↑u⁻¹, ?_⟩
      have : a * ↑u = 3 * α.symm b := by
        apply α.injective; rw [hb, map_mul, map_ofNat, RingEquiv.apply_symm_apply]
      rw [← _root_.mul_assoc, ← this, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    · rintro ⟨b, rfl⟩
      exact ⟨α (b * u), by rw [_root_.mul_assoc, map_mul, map_ofNat]⟩
  · obtain ⟨a, ha⟩ := h2 x hx
    refine ⟨α.symm a * ↑u⁻¹, ?_⟩
    change x = cpt s ≫ (Over.pullback s).map (secF 𝒜.toQMFamily (α (α.symm a * ↑u⁻¹ * ↑u)))
    rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one, RingEquiv.apply_symm_apply]; exact ha

/-- **The combined operation on objects of the printed moduli problem.** -/
def opP (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S :=
  { toQMAbSchemeNL := opNL α u 𝒜, level := level_opNL α u 𝒜 }

/-- **`rightMul u`** (`u ∈ 𝒪^×`): the action of `K₀` through `𝒪^× → (𝒪/3𝒪)^×` on the three-marking. -/
def rightMulP (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S := opP (RingEquiv.refl O) u 𝒜

/-- **`twist α`** (`α ∈ Aut 𝒪`; by Skolem–Noether `α = Ad(b)` for `b` in the normalizer of `𝒪` in `B^×`, the
global part of `N`). -/
def twistP (α : O ≃+* O) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S := opP α 1 𝒜

theorem qmFamFibre_op {T : Scheme.{0}} (α : O ≃+* O) (u : Oˣ) {𝒜 : QMFamily T} {g : S ⟶ T}
    {𝒜' : QMFamily S} (h : QMFamFibre 𝒜 g 𝒜') : QMFamFibre (famOp α u 𝒜) g (famOp α u 𝒜') := by
  obtain ⟨h, hpb, hi, he⟩ := h
  exact ⟨h, hpb, fun a => hi (α a), fun a => he (α (a * u))⟩

theorem qmFamFibreP_op {T : Scheme.{0}} (α : O ≃+* O) (u : Oˣ) {𝒜 : QMAbSchemeP T} {g : S ⟶ T}
    {𝒜' : QMAbSchemeP S} (h : QMFamFibre 𝒜.toQMFamily g 𝒜'.toQMFamily) :
    QMFamFibre (opP α u 𝒜).toQMFamily g (opP α u 𝒜').toQMFamily :=
  qmFamFibre_op α u h

/-- `QMFamFibre` only sees `F`, `ι`, `η`: transport along pointwise equalities. -/
theorem qmFamFibre_congr {T : Scheme.{0}} {𝒜 : QMFamily T} {g : S ⟶ T} {𝒜' 𝒜'' : QMFamily S}
    (hF : 𝒜'.F = 𝒜''.F) (hi : ∀ a, HEq (𝒜'.iota a) (𝒜''.iota a)) (he : ∀ a, HEq (𝒜'.eta a) (𝒜''.eta a))
    (h : QMFamFibre 𝒜 g 𝒜') : QMFamFibre 𝒜 g 𝒜'' := by
  obtain ⟨F', p', s', i', o', e', es'⟩ := 𝒜'
  obtain ⟨F'', p'', s'', i'', o'', e'', es''⟩ := 𝒜''
  cases hF
  have hi' : i' = i'' := funext fun a => eq_of_heq (hi a)
  have he' : e' = e'' := funext fun a => eq_of_heq (he a)
  subst hi' he'
  exact h

theorem qmFamFibre_id (𝒜 : QMFamily S) : QMFamFibre 𝒜 (𝟙 S) 𝒜 :=
  ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩, fun a => by simp, fun a => by simp⟩

end Ops

/-! ## 2. Yoneda: the operations act on the representing scheme of `Y3FullThreeRepZ30` -/

section Yoneda

variable {𝒴 : Over (Spec (CommRingCat.of Z30))} {𝒜 : QMAbSchemeP 𝒴.left}

/-- The representing scheme is locally noetherian (smooth over the noetherian `ℤ[1/30]`). -/
theorem isLocallyNoetherian_of_smooth (h : SmoothOfRelativeDimension 1 𝒴.hom) : IsLocallyNoetherian 𝒴.left := by
  haveI := h
  exact LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom

/-- The universal property, packaged. -/
def IsUniv (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
    ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-- **The endomorphism induced by an operation `T` on the functor** (Yoneda): the unique `σ : 𝒴 → 𝒴` over
`ℤ[1/30]` with `T 𝒜 ≅ σ^* 𝒜`. -/
theorem exists_induced (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (𝒜' : QMAbSchemeP 𝒴.left) :
    ∃! σ : 𝒴 ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily σ.left 𝒜'.toQMFamily :=
  hU 𝒴 hN 𝒜'

/-- Uniqueness, as an equation. -/
theorem induced_eq (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) {𝒜' : QMAbSchemeP 𝒴.left}
    {σ τ : 𝒴 ⟶ 𝒴} (hσ : QMFamFibre 𝒜.toQMFamily σ.left 𝒜'.toQMFamily)
    (hτ : QMFamFibre 𝒜.toQMFamily τ.left 𝒜'.toQMFamily) : σ = τ :=
  (hU 𝒴 hN 𝒜').unique hσ hτ

/-- The induced map of `rightMul u`. -/
def sigmaR (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) : 𝒴 ⟶ 𝒴 :=
  (exists_induced hU hN (rightMulP u 𝒜)).exists.choose

theorem sigmaR_spec (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) :
    QMFamFibre 𝒜.toQMFamily (sigmaR hU hN u).left (rightMulP u 𝒜).toQMFamily :=
  (exists_induced hU hN (rightMulP u 𝒜)).exists.choose_spec

/-- The induced map of `twist α`. -/
def sigmaT (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) : 𝒴 ⟶ 𝒴 :=
  (exists_induced hU hN (twistP α 𝒜)).exists.choose

theorem sigmaT_spec (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) :
    QMFamFibre 𝒜.toQMFamily (sigmaT hU hN α).left (twistP α 𝒜).toQMFamily :=
  (exists_induced hU hN (twistP α 𝒜)).exists.choose_spec

/-- `rightMul 1` induces the identity. -/
theorem sigmaR_one (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) : sigmaR hU hN 1 = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaR_spec hU hN 1) ?_
  refine qmFamFibre_congr (𝒜' := 𝒜.toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) (qmFamFibre_id 𝒜.toQMFamily)
  change 𝒜.eta a = 𝒜.eta (RingEquiv.refl O (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one]; rfl

/-- **Composition law of `rightMul`**: `σ_u ≫ σ_v = σ_{v u}`. -/
theorem sigmaR_comp (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u v : Oˣ) :
    sigmaR hU hN u ≫ sigmaR hU hN v = sigmaR hU hN (v * u) := by
  refine induced_eq hU hN ?_ (sigmaR_spec hU hN (v * u))
  have h := qmFamFibre_trans (sigmaR_spec hU hN v) (qmFamFibreP_op (RingEquiv.refl O) v (sigmaR_spec hU hN u))
  refine qmFamFibre_congr (𝒜' := (opP (RingEquiv.refl O) v (rightMulP u 𝒜)).toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) h
  change 𝒜.eta (RingEquiv.refl O (RingEquiv.refl O (a * ↑v) * ↑u)) = 𝒜.eta (RingEquiv.refl O (a * ↑(v * u)))
  rw [Units.val_mul, ← _root_.mul_assoc]; rfl

/-- **`rightMul u` acts by automorphisms** of the integral model. -/
def isoR (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) : 𝒴 ≅ 𝒴 where
  hom := sigmaR hU hN u
  inv := sigmaR hU hN u⁻¹
  hom_inv_id := by rw [sigmaR_comp, inv_mul_cancel, sigmaR_one]
  inv_hom_id := by rw [sigmaR_comp, mul_inv_cancel, sigmaR_one]

/-- `twist (refl)` induces the identity. -/
theorem sigmaT_refl (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) :
    sigmaT hU hN (RingEquiv.refl O) = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaT_spec hU hN _) ?_
  refine qmFamFibre_congr (𝒜' := 𝒜.toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) (qmFamFibre_id 𝒜.toQMFamily)
  change 𝒜.eta a = 𝒜.eta (RingEquiv.refl O (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one]; rfl

/-- **Composition law of `twist`**: `σ_α ≫ σ_β = σ_{β.trans α}` (`(β.trans α) a = α (β a)`). -/
theorem sigmaT_comp (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α β : O ≃+* O) :
    sigmaT hU hN α ≫ sigmaT hU hN β = sigmaT hU hN (β.trans α) := by
  refine induced_eq hU hN ?_ (sigmaT_spec hU hN (β.trans α))
  have h := qmFamFibre_trans (sigmaT_spec hU hN β) (qmFamFibreP_op β 1 (sigmaT_spec hU hN α))
  refine qmFamFibre_congr (𝒜' := (opP β 1 (twistP α 𝒜)).toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) h
  change 𝒜.eta (α (β (a * ((1 : Oˣ) : O)) * ((1 : Oˣ) : O))) = 𝒜.eta ((β.trans α) (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one, _root_.mul_one]; rfl

/-- **`twist α` acts by automorphisms** of the integral model. -/
def isoT (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) : 𝒴 ≅ 𝒴 where
  hom := sigmaT hU hN α
  inv := sigmaT hU hN α.symm
  hom_inv_id := by
    rw [sigmaT_comp]
    rw [RingEquiv.symm_trans_self, sigmaT_refl]
  inv_hom_id := by
    rw [sigmaT_comp]
    rw [RingEquiv.self_trans_symm, sigmaT_refl]

/-- `ι(-1)` is an automorphism of `A` over the base. -/
theorem iota_neg_one_sq (𝒜 : QMAbSchemeP 𝒴.left) : 𝒜.iota (-1) ≫ 𝒜.iota (-1) = 𝟙 _ := by
  rw [← 𝒜.iota_mul, _root_.neg_one_mul, neg_neg, 𝒜.iota_one]

/-- **The central element `−1` acts trivially** (manuscript L430-434 for the central idele `−1`, whose image
in `(𝒪/3𝒪)^×` is the only central unit not in `K₃`): `(A, ι, η(·(−1))) ≅ (A, ι, η)` through `ι(−1) = [−1]`, so
the induced map is the identity. -/
theorem sigmaR_neg_one (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) : sigmaR hU hN (-1) = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaR_spec hU hN (-1)) ?_
  haveI : IsIso (𝒜.iota (-1)) := ⟨⟨𝒜.iota (-1), iota_neg_one_sq 𝒜, iota_neg_one_sq 𝒜⟩⟩
  have hpb : IsPullback (𝒜.iota (-1)) 𝒜.F.hom 𝒜.F.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [𝒜.iota_over, Category.comp_id]⟩
  refine ⟨𝒜.iota (-1), hpb, fun a => ?_, fun a => ?_⟩
  · change 𝒜.iota a ≫ 𝒜.iota (-1) = 𝒜.iota (-1) ≫ 𝒜.iota a
    rw [← 𝒜.iota_mul, ← 𝒜.iota_mul, _root_.neg_one_mul, _root_.mul_neg_one]
  · change 𝒜.eta (RingEquiv.refl O (a * ↑(-1 : Oˣ))) ≫ 𝒜.iota (-1) = 𝟙 _ ≫ 𝒜.eta a
    rw [RingEquiv.refl_apply, ← 𝒜.eta_linear, Units.val_neg, Units.val_one, _root_.mul_neg_one,
      _root_.neg_one_mul, neg_neg, Category.id_comp]

/-- **The Yoneda action on the integral model of `Y₃`**, from the leaf `Y3FullThreeRepZ30` alone: there are a
proper smooth curve `𝒴/ℤ[1/30]` with a universal object and automorphisms `isoR u` (`u ∈ 𝒪^×`) and `isoT α`
(`α ∈ Aut 𝒪`) of `𝒴` over `ℤ[1/30]`, each characterized by `σ^*𝒜 ≅ T 𝒜`, with the composition laws of the
operations, and `−1 ∈ 𝒪^×` acting trivially. -/
theorem action_of_z30 (h : Y3FullThreeRepZ30) :
    ∃ (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left)
      (σR : Oˣ → (𝒴 ≅ 𝒴)) (σT : (O ≃+* O) → (𝒴 ≅ 𝒴)),
      IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧ IsUniv 𝒴 𝒜 ∧
      (∀ u, QMFamFibre 𝒜.toQMFamily (σR u).hom.left (rightMulP u 𝒜).toQMFamily) ∧
      (∀ α, QMFamFibre 𝒜.toQMFamily (σT α).hom.left (twistP α 𝒜).toQMFamily) ∧
      (∀ u v, (σR u).hom ≫ (σR v).hom = (σR (v * u)).hom) ∧
      (∀ α β, (σT α).hom ≫ (σT β).hom = (σT (β.trans α)).hom) ∧
      (σR (-1)).hom = 𝟙 𝒴 := by
  obtain ⟨𝒴, 𝒜, hP, hS, hU⟩ := h
  have hN := isLocallyNoetherian_of_smooth hS
  exact ⟨𝒴, 𝒜, isoR hU hN, isoT hU hN, hP, hS, hU, sigmaR_spec hU hN, sigmaT_spec hU hN,
    sigmaR_comp hU hN, sigmaT_comp hU hN, sigmaR_neg_one hU hN⟩

end Yoneda

end Y3P1j

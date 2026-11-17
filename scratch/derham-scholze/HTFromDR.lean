import ZInQKernel.Contrib.OneProof.DeRhamScholze

/-!
# derham-scholze, part 2: de Rham with Hodge jumps in `[0, 1]` implies Hodge–Tate (`DeRhamHodgeTate01`)

The manuscript reads the Hodge–Tate weights of `V_ℓ(A)` off the filtered de Rham comparison
(`lem:de-rham-descent`, L10993-10998: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`. Consequently the Tate
module has weights `0,0,−1,−1`"). The step behind "consequently" is Fontaine's: a de Rham representation is
Hodge–Tate, with `gr^j D_dR ↪ (ℂ_p(j) ⊗ W)^{G_F}`. Here it is proved for jumps in `[0, 1]` from

* Tate's theorems `ℂ_p(i)^{G_K} = 0` (`i ≠ 0`) and `ℂ_p^{G_K} = K` (`tateTwistInvariants_proof`,
  `axSenTate_proof`, both proved in the tree), and
* `FontaineTwistT`: `B_dR^+` has a uniformizer `t` with `σ(t) = χ(σ) t` (Fontaine's `t = log [ε]`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace DeRhamScholze.HT

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-- **GLUE (standard; Fontaine's `t`).** `B_dR^+` has a uniformizer `t` (`𝔪 = (t)`) on which `G_{ℚ_p}` acts by
the cyclotomic character: `σ(t) = χ(σ) t`. Fontaine's `t = log [ε]` (Fontaine, Astérisque 223 (1994), Exp. II,
§1.5; Brinon–Conrad, CMI notes, §4.3; numbers UNVERIFIED). In the tree: `TDict.tt` is `log [ε]` and
`TDict.tt_eq_varpi_mul_unit` makes it a uniformizer; the Galois equivariance is not proved there. -/
def FontaineTwistT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ t : BDeRhamPlus 𝓞_ℂ_[p] p,
    IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t} ∧
    ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `θ` on `Fil⁰ B_dR` -/

section Theta

/-- `B_dR^+ → B_dR`. -/
abbrev iota : BDeRhamPlus 𝓞_ℂ_[p] p →+* BdR p := algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)

theorem iota_injective : Function.Injective (iota p) := BdRInv.alg_injective p

/-- `θ : B_dR^+ → ℂ_p`. -/
abbrev theta : BDeRhamPlus 𝓞_ℂ_[p] p →+* ℂ_[p] := BdrKer.Cp.thetaPlusCp p

theorem ker_theta : RingHom.ker (theta p) = IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by
  haveI : (RingHom.ker (theta p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (BdrKer.Cp.thetaPlusCp_surjective p)
  exact IsLocalRing.eq_maximalIdeal this

theorem mem_filB_zero (x : BdR p) : x ∈ filB p 0 ↔ ∃ b, iota p b = x := by
  constructor
  · rintro ⟨b, -, hb⟩; exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩; exact ⟨b, by simp, hb⟩

/-- The preimage in `B_dR^+` of an element of `Fil⁰ B_dR`. -/
def pre (x : filB p 0) : BDeRhamPlus 𝓞_ℂ_[p] p := ((mem_filB_zero p x).mp x.2).choose

theorem iota_pre (x : filB p 0) : iota p (pre p x) = x := ((mem_filB_zero p x).mp x.2).choose_spec

theorem pre_eq {x : filB p 0} {b : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p b = x) : pre p x = b :=
  iota_injective p ((iota_pre p x).trans h.symm)

theorem theta_qpToPlus (c : ℚ_[p]) : theta p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c :=
  thetaPlusCp_qpToPlus p c

theorem iota_qpToPlus_mul (c : ℚ_[p]) (b : BDeRhamPlus 𝓞_ℂ_[p] p) :
    iota p (qpToPlus p c * b) = c • iota p b := by
  rw [map_mul, Algebra.smul_def]
  rfl

/-- `θ` on `Fil⁰ B_dR = B_dR^+`, as a `ℚ_p`-linear map. -/
def theta0 : filB p 0 →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := theta p (pre p x)
  map_add' x y := by
    rw [pre_eq p (show iota p (pre p x + pre p y) = ((x + y : filB p 0) : BdR p) by
      rw [map_add, iota_pre, iota_pre]; rfl), map_add]
  map_smul' c x := by
    rw [pre_eq p (show iota p (qpToPlus p c * pre p x) = ((c • x : filB p 0) : BdR p) by
      rw [iota_qpToPlus_mul, iota_pre]; rfl), map_mul, theta_qpToPlus, RingHom.id_apply, Algebra.smul_def]

theorem theta0_spec {x : filB p 0} {b : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p b = x) : theta0 p x = theta p b := by
  change theta p (pre p x) = _
  rw [pre_eq p h]

end Theta

/-! ## §2. The graded pieces `gr⁰`, `gr¹` of `D_dR(V^∨) = Hom_{G_F}(V, B_dR)` -/

section FilH

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `Fil^j Hom(V, B_dR) = Hom(V, Fil^j B_dR)`. -/
def filH (j : ℕ) : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ v, φ v ∈ filB p j}
  zero_mem' v := by simp only [LinearMap.zero_apply]; exact zero_mem _
  add_mem' ha hb v := by simp only [LinearMap.add_apply]; exact add_mem (ha v) (hb v)
  smul_mem' c φ h v := by simp only [LinearMap.smul_apply]; exact (filB p j).smul_mem c (h v)

end FilH

section Graded

variable {p}
variable {t : BDeRhamPlus 𝓞_ℂ_[p] p} (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})
include ht

theorem mem_filB_iff (j : ℕ) (x : BdR p) : x ∈ filB p j ↔ ∃ c, iota p (t ^ j * c) = x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, rfl⟩ := hb
    exact ⟨c, by rw [mul_comm]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨t ^ j * c, ?_, rfl⟩
    rw [ht, Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem t_ne_zero : t ≠ 0 := by
  intro h
  have h1 : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = ⊥ := by
    rw [ht, h, Ideal.span_singleton_eq_bot]
  have h2 := DeRhamPrint.TDict.varpi_mem_max p
  rw [h1, Ideal.mem_bot] at h2
  exact DeRhamPrint.TDict.varpi_ne_zero p h2

theorem mul_left_cancel_t {c c' : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = iota p (t * c')) : c = c' :=
  mul_left_cancel₀ (t_ne_zero ht) (iota_injective p h)

/-- The preimage `c` of `x = ι(t c) ∈ Fil¹ B_dR`. -/
def pre1 (x : filB p 1) : BDeRhamPlus 𝓞_ℂ_[p] p := ((mem_filB_iff ht 1 x).mp x.2).choose

theorem iota_pre1 (x : filB p 1) : iota p (t * pre1 ht x) = x := by
  have := ((mem_filB_iff ht 1 x).mp x.2).choose_spec
  rwa [pow_one] at this

theorem pre1_eq {x : filB p 1} {c : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = x) : pre1 ht x = c :=
  mul_left_cancel_t ht ((iota_pre1 ht x).trans h.symm)

/-- `gr¹ B_dR → ℂ_p(1)`: `ι(t c) ↦ θ(c)`, a `ℚ_p`-linear map on `Fil¹ B_dR`. -/
def theta1 : filB p 1 →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := theta p (pre1 ht x)
  map_add' x y := by
    rw [pre1_eq ht (show iota p (t * (pre1 ht x + pre1 ht y)) = ((x + y : filB p 1) : BdR p) by
      rw [mul_add, map_add, iota_pre1, iota_pre1]; rfl), map_add]
  map_smul' c x := by
    rw [pre1_eq ht (show iota p (t * (qpToPlus p c * pre1 ht x)) = ((c • x : filB p 1) : BdR p) by
      rw [mul_left_comm, iota_qpToPlus_mul, iota_pre1]; rfl), map_mul, theta_qpToPlus, RingHom.id_apply,
      Algebra.smul_def]

theorem theta1_spec {x : filB p 1} {c : BDeRhamPlus 𝓞_ℂ_[p] p} (h : iota p (t * c) = x) :
    theta1 ht x = theta p c := by
  change theta p (pre1 ht x) = _
  rw [pre1_eq ht h]

end Graded

section GrMaps

variable {p}
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `gr⁰ : Hom(V, Fil⁰ B_dR) → Hom(V, ℂ_p)`, `φ ↦ θ ∘ φ`. -/
def gr0 : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun φ := theta0 p ∘ₗ LinearMap.codRestrict (filB p 0) φ.1 φ.2
  map_add' φ ψ := LinearMap.ext fun v => by
    change theta0 p ⟨φ.1 v + ψ.1 v, _⟩ = theta0 p ⟨φ.1 v, φ.2 v⟩ + theta0 p ⟨ψ.1 v, ψ.2 v⟩
    rw [← map_add]; rfl
  map_smul' c φ := LinearMap.ext fun v => by
    change theta0 p ⟨c • φ.1 v, _⟩ = c • theta0 p ⟨φ.1 v, φ.2 v⟩
    rw [← map_smul]; rfl

theorem gr0_apply (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (v : V) {b : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hb : iota p b = φ.1 v) : gr0 φ v = theta p b :=
  theta0_spec p (x := ⟨φ.1 v, φ.2 v⟩) hb

variable {t : BDeRhamPlus 𝓞_ℂ_[p] p} (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})

/-- `gr¹ : Hom(V, Fil¹ B_dR) → Hom(V, ℂ_p)`, `φ ↦ θ ∘ (φ/t)`. -/
def gr1 : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun φ := theta1 ht ∘ₗ LinearMap.codRestrict (filB p 1) φ.1 φ.2
  map_add' φ ψ := LinearMap.ext fun v => by
    change theta1 ht ⟨φ.1 v + ψ.1 v, _⟩ = theta1 ht ⟨φ.1 v, φ.2 v⟩ + theta1 ht ⟨ψ.1 v, ψ.2 v⟩
    rw [← map_add]; rfl
  map_smul' c φ := LinearMap.ext fun v => by
    change theta1 ht ⟨c • φ.1 v, _⟩ = c • theta1 ht ⟨φ.1 v, φ.2 v⟩
    rw [← map_smul]; rfl

theorem gr1_apply (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (v : V) {c : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hc : iota p (t * c) = φ.1 v) : gr1 ht φ v = theta p c :=
  theta1_spec ht (x := ⟨φ.1 v, φ.2 v⟩) hc

/-- `gr⁰` lands in `Hom_{G_F}(V, ℂ_p)`. -/
theorem gr0_mem (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (hφ : φ.1 ∈ ddrSpaceOver p ρ) :
    gr0 φ ∈ htSpaceOver p ρ 0 := by
  intro σ v
  obtain ⟨b, hb⟩ := (mem_filB_zero p _).mp (φ.2 v)
  have h2 : iota p (DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) b) = φ.1 (ρ σ v) := by
    rw [hφ σ v, ← hb]
    exact (BdRInv.bdrAct_algebraMap p _ b).symm
  rw [gr0_apply φ (ρ σ v) h2, gr0_apply φ v hb, cycPow_zero, one_smul]
  exact thetaPlusCp_bdrPlusMap p _ b

/-- `gr¹` lands in `Hom_{G_F}(V, ℂ_p(1))`, given `σ(t) = χ(σ) t`. -/
theorem gr1_mem (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (hφ : φ.1 ∈ ddrSpaceOver p ρ) :
    gr1 ht φ ∈ htSpaceOver p ρ 1 := by
  intro σ v
  obtain ⟨c, hc⟩ : ∃ c, iota p (t * c) = φ.1 v := by
    obtain ⟨c, hc⟩ := (mem_filB_iff ht 1 _).mp (φ.2 v)
    exact ⟨c, by rwa [pow_one] at hc⟩
  have h2 : iota p (t * (qpToPlus p (cycPow p (gfToGqp p F σ) 1) *
      DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) c)) = φ.1 (ρ σ v) := by
    rw [hφ σ v, ← hc, BdRInv.bdrAct_algebraMap, map_mul, hσ]
    congr 1
    ring
  rw [gr1_apply ht φ (ρ σ v) h2, gr1_apply ht φ v hc, map_mul, theta_qpToPlus, thetaPlusCp_bdrPlusMap,
    Algebra.smul_def]

include ht in
theorem mem_filH1_of_gr0 (φ : (filH p 0 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (h : gr0 φ = 0) :
    φ.1 ∈ (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  intro v
  obtain ⟨b, hb⟩ := (mem_filB_zero p _).mp (φ.2 v)
  have h0 : theta p b = 0 := by rw [← gr0_apply φ v hb, h]; rfl
  have hm : b ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by rw [← ker_theta]; exact h0
  rw [ht, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  exact (mem_filB_iff ht 1 _).mpr ⟨c, by rw [pow_one, mul_comm, hb]⟩

theorem mem_filH2_of_gr1 (φ : (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))) (h : gr1 ht φ = 0) :
    φ.1 ∈ (filH p 2 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  intro v
  obtain ⟨c, hc⟩ : ∃ c, iota p (t * c) = φ.1 v := by
    obtain ⟨c, hc⟩ := (mem_filB_iff ht 1 _).mp (φ.2 v)
    exact ⟨c, by rwa [pow_one] at hc⟩
  have h0 : theta p c = 0 := by rw [← gr1_apply ht φ v hc, h]; rfl
  have hm : c ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by rw [← ker_theta]; exact h0
  rw [ht, Ideal.mem_span_singleton'] at hm
  obtain ⟨d, rfl⟩ := hm
  exact (mem_filB_iff ht 2 _).mpr ⟨d, by rw [← hc]; congr 1; ring⟩

/-- **`dim D_dR(V^∨) ≤ dim Hom_{G_F}(V, ℂ_p) + dim Hom_{G_F}(V, ℂ_p(1))`** when the Hodge filtration of
`Hom_{G_F}(V, B_dR)` has its jumps in `[0, 1]` (`gr⁰ ↪ Hom_{G_F}(V, ℂ_p)`, `gr¹ ↪ Hom_{G_F}(V, ℂ_p(1))`). -/
theorem finrank_ddr_le (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (h0 : ddrSpaceOver p ρ ≤ filH p 0) (h2 : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥)
    [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 0)] [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 1)] :
    finrank ℚ_[p] (ddrSpaceOver p ρ) ≤
      finrank ℚ_[p] (htSpaceOver p ρ 0) + finrank ℚ_[p] (htSpaceOver p ρ 1) := by
  by_cases hz : finrank ℚ_[p] (ddrSpaceOver p ρ) = 0
  · rw [hz]; exact Nat.zero_le _
  haveI : FiniteDimensional ℚ_[p] (ddrSpaceOver p ρ) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hz)
  let G0 : ddrSpaceOver p ρ →ₗ[ℚ_[p]] htSpaceOver p ρ 0 :=
    LinearMap.codRestrict _ (gr0 ∘ₗ Submodule.inclusion h0) (fun φ => gr0_mem ρ _ φ.2)
  let incl : LinearMap.ker G0 →ₗ[ℚ_[p]] (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    { toFun := fun φ => ⟨φ.1.1, mem_filH1_of_gr0 ht ⟨φ.1.1, h0 φ.1.2⟩
        (congrArg Subtype.val (LinearMap.mem_ker.mp φ.2))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G1 : LinearMap.ker G0 →ₗ[ℚ_[p]] htSpaceOver p ρ 1 :=
    LinearMap.codRestrict _ (gr1 ht ∘ₗ incl) (fun φ => gr1_mem ρ ht hσ _ φ.1.2)
  have hG1 : Function.Injective G1 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro φ hφ
    have h3 : gr1 ht (incl φ) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hφ)
    have h4 : φ.1.1 ∈ ddrSpaceOver p ρ ⊓ filH p 2 := ⟨φ.1.2, mem_filH2_of_gr1 ht (incl φ) h3⟩
    rw [h2, Submodule.mem_bot] at h4
    rw [Submodule.mem_bot]
    exact Subtype.ext (Subtype.ext h4)
  rw [← LinearMap.finrank_range_add_finrank_ker G0]
  exact Nat.add_le_add (Submodule.finrank_le _) (LinearMap.finrank_le_finrank_of_injective hG1)

end GrMaps

/-! ## §3. Tate–Sen: `F'`-independent invariant vectors of weights `0` and `1` are `ℂ_p`-independent -/

section TateSen

variable {p}
variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ℂ_p` as an `F'`-algebra through `F' ⊆ ℚ̄_p ⊆ ℂ_p` (`iotaCp`). -/
@[instance_reducible] def algCp : Algebra (fieldF p F) ℂ_[p] := (iotaCp p F).toRingHom.toAlgebra

attribute [local instance] algCp

theorem algebraMap_algCp (x : fieldF p F) : algebraMap (fieldF p F) ℂ_[p] x = iotaCp p F x := rfl

instance towerCp : IsScalarTower ℚ_[p] (fieldF p F) ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq fun c => ((iotaCp p F).commutes c).symm

variable {F} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

/-- `Hom_{G_F}(V, ℂ_p(i))` as an `F'`-space (same carrier as `htSpaceOver`). -/
def htF (i : ℤ) : Submodule (fieldF p F) (V →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ σ v, φ (ρ σ v) = cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) (φ v)}
  zero_mem' σ v := by simp
  add_mem' ha hb σ v := by simp only [LinearMap.add_apply, ha σ v, hb σ v, map_add, smul_add]
  smul_mem' c φ hφ σ v := by
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, algebraMap_algCp, cpAct_iotaCp_gf, ← algebraMap_algCp,
      ← Algebra.smul_def, smul_comm]

theorem restrictScalars_htF (i : ℤ) : (htF ρ i).restrictScalars ℚ_[p] = htSpaceOver p ρ i :=
  Submodule.ext fun _ => Iff.rfl

theorem finrank_htSpaceOver_eq (i : ℤ) :
    finrank ℚ_[p] (htSpaceOver p ρ i) = finrank ℚ_[p] F * finrank (fieldF p F) (htF ρ i) := by
  rw [← restrictScalars_htF, ← finrank_fieldF p F,
    ((htF ρ i).restrictScalarsEquiv ℚ_[p] (fieldF p F)).restrictScalars ℚ_[p] |>.finrank_eq]
  have : Module.Free (fieldF p F) (htF ρ i) := Module.Free.of_divisionRing (fieldF p F) (htF ρ i)
  exact (Module.finrank_mul_finrank ℚ_[p] (fieldF p F) (htF ρ i)).symm

theorem cycPow_add (σ : GQp p) (i j : ℤ) : cycPow p σ (i + j) = cycPow p σ i * cycPow p σ j := by
  simp only [cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

omit [FiniteDimensional ℚ_[p] F] in
theorem smul_eq_iota (c : fieldF p F) (φ : V →ₗ[ℚ_[p]] ℂ_[p]) : c • φ = iotaCp p F c • φ :=
  LinearMap.ext fun v => by simp only [LinearMap.smul_apply, Algebra.smul_def, algebraMap_algCp]; rfl

variable (hT : TateTwistInvariants) (hA : AxSenTate)
include hT in
theorem twist_fixed_eq_zero {i : ℤ} (hi : i ≠ 0) {x : ℂ_[p]}
    (h : ∀ σ : Field.absoluteGaloisGroup F, cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) x = x) :
    x = 0 := by
  apply hT p (fieldF p F) i hi x
  intro τ hτ
  have : τ ∈ Set.range (gfToGqp p F) := by rw [range_gfToGqp_eq]; exact hτ
  obtain ⟨σ, rfl⟩ := this
  exact h σ

include hA in
theorem fixed_mem_range {x : ℂ_[p]} (h : ∀ σ : Field.absoluteGaloisGroup F, cpAct p (gfToGqp p F σ) x = x) :
    ∃ y : fieldF p F, x = iotaCp p F y := by
  obtain ⟨y, hy⟩ := hA p (fieldF p F) x (fun τ hτ => by
    have : τ ∈ Set.range (gfToGqp p F) := by rw [range_gfToGqp_eq]; exact hτ
    obtain ⟨σ, rfl⟩ := this
    exact h σ)
  refine ⟨y, hy.trans ?_⟩
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq]
  rfl

/-- The weight of an index: `0` on `Fin a`, `1` on `Fin b`. -/
def wt {a b : ℕ} : Fin a ⊕ Fin b → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)

include hT hA in
/-- **Tate–Sen.** `F'`-linearly independent families in `Hom_{G_F}(V, ℂ_p)` and in `Hom_{G_F}(V, ℂ_p(1))`
together are `ℂ_p`-linearly independent in `Hom_{ℚ_p}(V, ℂ_p)` (minimal relation; Tate's `ℂ_p(±1)^{G_F} = 0` and
`ℂ_p^{G_F} = F'`). -/
theorem linIndep_two {a b : ℕ} (x : Fin a → htF ρ 0) (y : Fin b → htF ρ 1)
    (hx : LinearIndependent (fieldF p F) x) (hy : LinearIndependent (fieldF p F) y) :
    LinearIndependent ℂ_[p]
      (Sum.elim (fun i => (x i : V →ₗ[ℚ_[p]] ℂ_[p])) (fun j => (y j : V →ₗ[ℚ_[p]] ℂ_[p]))) := by
  classical
  set z : Fin a ⊕ Fin b → (V →ₗ[ℚ_[p]] ℂ_[p]) :=
    Sum.elim (fun i => (x i : V →ₗ[ℚ_[p]] ℂ_[p])) (fun j => (y j : V →ₗ[ℚ_[p]] ℂ_[p])) with hz
  have hzk : ∀ k σ v, z k (ρ σ v) = cycPow p (gfToGqp p F σ) (wt k) • cpAct p (gfToGqp p F σ) (z k v) := by
    rintro (i | j) σ v
    · exact (x i).2 σ v
    · exact (y j).2 σ v
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (N : ℕ) (c : Fin a ⊕ Fin b → ℂ_[p]), (Finset.univ.filter fun k => c k ≠ 0).card = N →
      c ≠ 0 → ∑ k, c k • z k = 0 → False by
    intro c hc
    by_contra hne
    push_neg at hne
    obtain ⟨k, hk⟩ := hne
    exact H _ c rfl (fun h0 => hk (congrFun h0 k)) hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hcard hc0 hrel
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc0 (funext h)
  set c' : Fin a ⊕ Fin b → ℂ_[p] := fun k => (c j)⁻¹ * c k with hc'
  have hc'j : c' j = 1 := inv_mul_cancel₀ hj
  have hrel' : ∑ k, c' k • z k = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hsupp' : ∀ k, c' k ≠ 0 ↔ c k ≠ 0 := fun k => by
    simp only [hc', ne_eq, mul_eq_zero, inv_eq_zero, hj, false_or]
  -- the twisted relation: `Σ_k χ(σ)^{wt j - wt k} σ(c'_k) z_k = 0`
  set e : Field.absoluteGaloisGroup F → Fin a ⊕ Fin b → ℂ_[p] := fun σ k =>
    algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (wt j - wt k)) * cpAct p (gfToGqp p F σ) (c' k) with he
  have htw : ∀ σ, ∑ k, e σ k • z k = 0 := by
    intro σ
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ : ∃ v, ρ σ v = w := ⟨ρ σ⁻¹ w, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    have h0 : ∑ k, c' k * z k v = 0 := by
      have := LinearMap.congr_fun hrel' v
      simpa using this
    have h1 := congrArg (fun y => algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (wt j)) *
      cpAct p (gfToGqp p F σ) y) h0
    simp only [map_sum, map_mul, map_zero, mul_zero, Finset.mul_sum] at h1
    rw [LinearMap.sum_apply, LinearMap.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, hzk, he, smul_eq_mul, Algebra.smul_def]
    have hcy : cycPow p (gfToGqp p F σ) (wt j) =
        cycPow p (gfToGqp p F σ) (wt j - wt k) * cycPow p (gfToGqp p F σ) (wt k) := by
      rw [← cycPow_add, sub_add_cancel]
    rw [hcy, map_mul]
    ring
  by_cases hfix : ∀ σ k, e σ k = c' k
  · -- all coefficients are fixed: they vanish off the weight of `j` and lie in `F'` on it
    have hzero : ∀ k, wt k ≠ wt j → c' k = 0 := fun k hk =>
      twist_fixed_eq_zero hT (i := wt j - wt k) (sub_ne_zero.mpr (Ne.symm hk)) (fun σ => by
        rw [Algebra.smul_def]; exact hfix σ k)
    have hin : ∀ k, wt k = wt j → ∃ d : fieldF p F, c' k = iotaCp p F d := fun k hk =>
      fixed_mem_range hA (fun σ => by
        have := hfix σ k
        rwa [he, hk, sub_self, show cycPow p (gfToGqp p F σ) 0 = 1 from cycPow_zero p _, map_one,
          one_mul] at this)
    rcases j with j0 | j0
    · choose d hd using fun i : Fin a => hin (Sum.inl i) rfl
      have hsum : ∑ i, d i • x i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero, ← hrel', Fintype.sum_sum_type]
        have h2 : ∑ i : Fin b, c' (Sum.inr i) • z (Sum.inr i) = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hzero (Sum.inr i) (by simp [wt]), zero_smul]
        rw [h2, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, smul_eq_iota, ← hd i]
        rfl
      have := (Fintype.linearIndependent_iff.mp hx) d hsum j0
      have h1 : iotaCp p F (d j0) = 1 := (hd j0).symm.trans hc'j
      rw [this, map_zero] at h1
      exact zero_ne_one h1
    · choose d hd using fun i : Fin b => hin (Sum.inr i) rfl
      have hsum : ∑ i, d i • y i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero, ← hrel', Fintype.sum_sum_type]
        have h2 : ∑ i : Fin a, c' (Sum.inl i) • z (Sum.inl i) = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hzero (Sum.inl i) (by simp [wt]), zero_smul]
        rw [h2, zero_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, smul_eq_iota, ← hd i]
        rfl
      have := (Fintype.linearIndependent_iff.mp hy) d hsum j0
      have h1 : iotaCp p F (d j0) = 1 := (hd j0).symm.trans hc'j
      rw [this, map_zero] at h1
      exact zero_ne_one h1
  · push_neg at hfix
    obtain ⟨σ, k₀, hk₀⟩ := hfix
    set d : Fin a ⊕ Fin b → ℂ_[p] := fun k => e σ k - c' k with hd
    have hdrel : ∑ k, d k • z k = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib, htw σ, hrel', sub_zero]
    have hdj : d j = 0 := by
      simp only [hd, he, hc'j, sub_self, show cycPow p (gfToGqp p F σ) 0 = 1 from cycPow_zero p _, map_one,
        one_mul]
    have hd0 : d ≠ 0 := fun h0 => hk₀ (sub_eq_zero.mp (congrFun h0 k₀))
    have hsub : (Finset.univ.filter fun k => d k ≠ 0) ⊂ (Finset.univ.filter fun k => c k ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun k hk => ?_) |>.mpr ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        rw [← hsupp']
        intro h0
        apply hk
        simp only [hd, he, h0, map_zero, mul_zero, sub_zero]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdj, ne_eq, not_true_eq_false,
          not_false_eq_true]
    exact ih _ (hcard ▸ Finset.card_lt_card hsub) d rfl hd0 hdrel

end TateSen

end

end DeRhamScholze.HT

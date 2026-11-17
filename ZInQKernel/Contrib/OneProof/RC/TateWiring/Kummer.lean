import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image

/-!
# Lane RC17 (Tate wiring): the genuine Kummer layer of the moving character

Manuscript (11/5 version), Proposition `ex:arith-moving-character`, proof, tex 3545–3563 (the
Kummer layer `L_∞ = F_∞(α_a^{1/2^n} : a)` over `F_∞ = K(μ_{2^∞})` and the multipliers (4.4a)),
tex 3606 ("`J_K = ρ_T(G_{F_∞})` has index at most two in `J`") and tex 3624–3626 ("such lifts fix
`L_∞`, whose Galois group over `F_∞` is abelian").

Lane RC4's interface `ZInQ.Manuscript.RC.Moving.MovingSetting T n` carries the subgroups
`GF = G_{F_∞}` and `HL = G_{L_∞}` of `T.G = G_{ℚ(μ_{2^∞})}`, the Kummer multipliers
`kum : G_{F_∞} →* (ℤ/2^n)^t` and the Kummer relations `KR` as abstract data, with GLUE fields
`GF_index`, `HL_le`, `kum_of_mem_HL`, `mem_HL_of_kum`.  Over the genuine Tate image
(`tateImage`, file `Image.lean`) these objects exist in Lean, and this file constructs them:

* `quadField s = ℚ(s)` (the allowed field `K = ℚ(√D)` embedded in `ℚ̄` by a square root `s` of
  `D`), `Finf s = K(μ_{2^∞})` and `GFinf s = G_{F_∞} ≤ G_{ℚ(μ_{2^∞})}` (genuine);
  `GFinf_index` (PROVED): index one or two (tex 3606);
* `KummerData s n t`: a primitive `2^n`-th root of unity `ζ`, radicands `α_a ∈ K^×` and chosen
  roots `γ_a`, `γ_a^{2^n} = α_a`; `Linf = F_∞(γ_a : a)` and `HLinf = G_{L_∞}` (genuine);
  `HLinf_le` (PROVED);
* `KummerData.kum` (genuine, PROVED to be a homomorphism): `σ(γ_a) = ζ^{kum σ a} γ_a`;
  `KummerData.kum_of_mem_HL`, `KummerData.mem_HL_of_kum` (PROVED): `G_{L_∞}` is its kernel;
* `KummerData.KR` (genuine): the exponent vectors `b` with `∏ α_a^{b_a}` a `2^n`-th power in
  `F_∞`;
* `MovingData E n`: lane RC4's `MovingSetting` with the Kummer layer and the trace made genuine:
  the fields that remain are exactly RC4's other fields, with `KR_val` and `kum_surj` (GLUE)
  stated over the genuine `KR` and `kum`, and `cheb` over the genuine trace of `ρ_T`;
  `MovingData.toMovingSetting` and `moving_character_genuine`, `moving_character_ecurve_genuine`
  (PROVED from lane RC4's `moving_character`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TateWiring

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Moving
open scoped WeierstrassCurve MatrixGroups

/-! ### Fixing an adjoined field -/

/-- An automorphism of `ℚ̄` fixes `ℚ(S)` pointwise iff it fixes `S` (PROVED). -/
theorem mem_fixingSubgroup_adjoin_iff {S : Set Qbar} {σ : GalQ} :
    σ ∈ (IntermediateField.adjoin ℚ S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  constructor
  · intro h x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 h x
      (IntermediateField.subset_adjoin ℚ S hx)
  · intro h
    have hle : IntermediateField.adjoin ℚ S ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      have hst : σ ∈ MulAction.stabilizer GalQ x := MulAction.mem_stabilizer_iff.2 (h x hx)
      exact MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer GalQ x).zpow_mem hst k)
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers σ)

/-! ### `K = ℚ(√D)`, `F_∞ = K(μ_{2^∞})` and `G_{F_∞}` -/

/-- The `2`-power roots of unity of `ℚ̄`. -/
def mu2inf : Set Qbar :=
  {ζ : Qbar | ∃ k : ℕ, ζ ^ 2 ^ k = 1}

/-- The quadratic field `K = ℚ(s) ⊂ ℚ̄` (for `s = √D`, an embedding of the allowed field). -/
def quadField (s : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {s}

/-- `F_∞ = K(μ_{2^∞}) ⊂ ℚ̄` (tex 3545). -/
def Finf (s : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ (insert s mu2inf)

/-- **`G_{F_∞}`** (tex 3606), the automorphisms fixing `F_∞`, as a subgroup of
`G_{ℚ(μ_{2^∞})}`. -/
def GFinf (s : Qbar) : Subgroup GalQmu2 :=
  (Finf s).fixingSubgroup.comap GalQmu2.subtype

/-- `σ ∈ G_{ℚ(μ_{2^∞})}` lies in `G_{F_∞}` iff it fixes `s` (PROVED). -/
theorem mem_GFinf_iff {s : Qbar} {σ : GalQmu2} : σ ∈ GFinf s ↔ (σ : GalQ) s = s := by
  rw [GFinf, Subgroup.mem_comap, Subgroup.coe_subtype, Finf, mem_fixingSubgroup_adjoin_iff]
  constructor
  · intro h
    exact h s (Set.mem_insert _ _)
  · intro h x hx
    rcases hx with rfl | ⟨k, hk⟩
    · exact h
    · exact mem_GalQmu2_iff.1 σ.2 k x hk

/-- An element of `G_{F_∞}` fixes `K` pointwise (PROVED). -/
theorem apply_eq_of_mem_quadField {s : Qbar} {σ : GalQmu2} (hσ : σ ∈ GFinf s) {x : Qbar}
    (hx : x ∈ quadField s) : (σ : GalQ) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1
    (mem_fixingSubgroup_adjoin_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact mem_GFinf_iff.1 hσ) x hx

/-- `σ(√D) = ±√D` (PROVED). -/
theorem apply_eq_or_eq_neg {D : ℚ} {s : Qbar} (hs : s ^ 2 = algebraMap ℚ Qbar D) (σ : GalQ) :
    σ s = s ∨ σ s = -s := by
  have h : σ s ^ 2 = s ^ 2 := by rw [← map_pow, hs, AlgEquiv.commutes]
  have h2 : (σ s - s) * (σ s + s) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- **`[G_{ℚ(μ_{2^∞})} : G_{F_∞}] ≤ 2`** (tex 3606; PROVED, lane RC4's GLUE field `GF_index`):
for `K = ℚ(s)` with `s² ∈ ℚ`. -/
theorem GFinf_index {D : ℚ} {s : Qbar} (hs : s ^ 2 = algebraMap ℚ Qbar D) :
    (GFinf s).index = 1 ∨ (GFinf s).index = 2 := by
  by_cases h : ∀ σ : GalQmu2, (σ : GalQ) s = s
  · left
    rw [Subgroup.index_eq_one, eq_top_iff]
    intro σ _
    exact mem_GFinf_iff.2 (h σ)
  · right
    obtain ⟨a, ha⟩ := not_forall.1 h
    have ha' : (a : GalQ) s = -s := (apply_eq_or_eq_neg hs a).resolve_left ha
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact ha (map_zero _)
    have hneg : -s ≠ s := by
      intro h
      apply hs0
      have h2 : (2 : Qbar) * s = 0 := by linear_combination -h
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun b => ?_⟩
    rw [mem_GFinf_iff, mem_GFinf_iff]
    have hba : ((b * a : GalQmu2) : GalQ) s = -((b : GalQ) s) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply, ha', map_neg]
    rw [hba]
    rcases apply_eq_or_eq_neg hs b with hb | hb
    · rw [hb]
      exact Or.inr ⟨rfl, hneg⟩
    · rw [hb, neg_neg]
      exact Or.inl ⟨rfl, hneg⟩

/-! ### The Kummer layer `L_∞ = F_∞(α_a^{1/2^n})` -/

/-- **The Kummer data at level `n`** (tex 3536–3550): a primitive `2^n`-th root of unity `ζ` (the
`ζ_{2^n}` of (4.4a)), radicands `α_a ∈ K` (`α_a = β_a/β̄_a`, nonzero) and chosen roots
`γ_a = α_a^{1/2^n}` in `ℚ̄`. -/
structure KummerData (s : Qbar) (n t : ℕ) where
  /-- a primitive `2^n`-th root of unity -/
  ζ : Qbar
  hζ : IsPrimitiveRoot ζ (2 ^ n)
  /-- the radicands `α_a ∈ K` -/
  α : Fin t → Qbar
  α_mem : ∀ a, α a ∈ quadField s
  /-- the chosen roots `α_a^{1/2^n}` -/
  γ : Fin t → Qbar
  γ_pow : ∀ a, γ a ^ 2 ^ n = α a
  γ_ne : ∀ a, γ a ≠ 0

namespace KummerData

variable {s : Qbar} {n t : ℕ} (K : KummerData s n t)

theorem α_ne (a : Fin t) : K.α a ≠ 0 := by
  rw [← K.γ_pow a]
  exact pow_ne_zero _ (K.γ_ne a)

/-- `L_∞ = F_∞(α_a^{1/2^n} : a) ⊂ ℚ̄` (tex 3562). -/
def Linf : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ (insert s mu2inf ∪ Set.range K.γ)

/-- **`G_{L_∞}`**, as a subgroup of `G_{ℚ(μ_{2^∞})}`. -/
def HLinf : Subgroup GalQmu2 :=
  K.Linf.fixingSubgroup.comap GalQmu2.subtype

theorem mem_HLinf_iff {σ : GalQmu2} :
    σ ∈ K.HLinf ↔ (σ : GalQ) s = s ∧ ∀ a, (σ : GalQ) (K.γ a) = K.γ a := by
  rw [HLinf, Subgroup.mem_comap, Subgroup.coe_subtype, Linf, mem_fixingSubgroup_adjoin_iff]
  constructor
  · intro h
    exact ⟨h s (Or.inl (Set.mem_insert _ _)), fun a => h _ (Or.inr ⟨a, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases hx with (rfl | ⟨k, hk⟩) | ⟨a, rfl⟩
    · exact h1
    · exact mem_GalQmu2_iff.1 σ.2 k x hk
    · exact h2 a

/-- `L_∞ ⊃ F_∞`, so `G_{L_∞} ≤ G_{F_∞}` (PROVED, lane RC4's field `HL_le`). -/
theorem HLinf_le : K.HLinf ≤ GFinf s := fun _ hσ => mem_GFinf_iff.2 (K.mem_HLinf_iff.1 hσ).1

/-- For `σ ∈ G_{F_∞}`, `σ(γ_a) = ζ^e γ_a` for some `e ∈ ℤ/2^n` (PROVED: `σ(γ_a)/γ_a` is a
`2^n`-th root of unity since `σ` fixes `α_a ∈ K`). -/
theorem exists_exp {σ : GalQmu2} (hσ : σ ∈ GFinf s) (a : Fin t) :
    ∃ e : ZMod (2 ^ n), (σ : GalQ) (K.γ a) = K.ζ ^ e.val * K.γ a := by
  have hξ : ((σ : GalQ) (K.γ a) / K.γ a) ^ 2 ^ n = 1 := by
    rw [div_pow, ← map_pow, K.γ_pow, apply_eq_of_mem_quadField hσ (K.α_mem a)]
    exact div_self (K.α_ne a)
  obtain ⟨i, hi, hζi⟩ := K.hζ.eq_pow_of_pow_eq_one hξ
  refine ⟨(i : ZMod (2 ^ n)), ?_⟩
  rw [ZMod.val_natCast_of_lt hi, hζi, div_mul_cancel₀ _ (K.γ_ne a)]

/-- The exponent is unique (PROVED). -/
theorem exp_unique (a : Fin t) {e f : ZMod (2 ^ n)}
    (h : K.ζ ^ e.val * K.γ a = K.ζ ^ f.val * K.γ a) : e = f :=
  ZMod.val_injective _
    (K.hζ.pow_inj (ZMod.val_lt e) (ZMod.val_lt f) (mul_right_cancel₀ (K.γ_ne a) h))

/-- The Kummer exponent of `σ ∈ G_{F_∞}` on `γ_a`. -/
def kumExp (σ : GFinf s) (a : Fin t) : ZMod (2 ^ n) :=
  Classical.choose (K.exists_exp σ.2 a)

theorem kumExp_spec (σ : GFinf s) (a : Fin t) :
    ((σ : GalQmu2) : GalQ) (K.γ a) = K.ζ ^ (K.kumExp σ a).val * K.γ a :=
  Classical.choose_spec (K.exists_exp σ.2 a)

theorem kumExp_eq (σ : GFinf s) (a : Fin t) (e : ZMod (2 ^ n))
    (h : ((σ : GalQmu2) : GalQ) (K.γ a) = K.ζ ^ e.val * K.γ a) : K.kumExp σ a = e :=
  K.exp_unique a ((K.kumExp_spec σ a).symm.trans h)

theorem pow_val_mod (m : ℕ) : K.ζ ^ (m % 2 ^ n) = K.ζ ^ m := by
  conv_lhs => rw [K.hζ.eq_orderOf]
  exact pow_mod_orderOf _ _

/-- **The Kummer multipliers** (tex 3545–3550, 3559–3563; genuine): `σ ↦ (e_a)_a` with
`σ(α_a^{1/2^n}) = ζ^{e_a} α_a^{1/2^n}`, a homomorphism on `G_{F_∞}` because `G_{F_∞}` fixes
`ζ` (PROVED). -/
def kum : GFinf s →* Multiplicative (Fin t → ZMod (2 ^ n)) where
  toFun σ := Multiplicative.ofAdd (K.kumExp σ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext a
    change K.kumExp 1 a = 0
    apply K.kumExp_eq
    rw [ZMod.val_zero, pow_zero, one_mul]
    rfl
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    funext a
    change K.kumExp (σ * τ) a = K.kumExp σ a + K.kumExp τ a
    apply K.kumExp_eq
    have hζσ : ((σ : GalQmu2) : GalQ) K.ζ = K.ζ :=
      mem_GalQmu2_iff.1 (σ : GalQmu2).2 n K.ζ K.hζ.pow_eq_one
    rw [Subgroup.coe_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, K.kumExp_spec τ a, map_mul,
      map_pow, hζσ, K.kumExp_spec σ a, ZMod.val_add, K.pow_val_mod, pow_add]
    ring

theorem toAdd_kum (σ : GFinf s) (a : Fin t) : Multiplicative.toAdd (K.kum σ) a = K.kumExp σ a :=
  rfl

/-- `G_{L_∞}` fixes the radicals, so its multipliers vanish (PROVED, lane RC4's GLUE field
`kum_of_mem_HL`). -/
theorem kum_of_mem_HL (σ : GFinf s) (hσ : (σ : GalQmu2) ∈ K.HLinf) : K.kum σ = 1 := by
  apply Multiplicative.toAdd.injective
  funext a
  change K.kumExp σ a = 0
  apply K.kumExp_eq
  rw [(K.mem_HLinf_iff.1 hσ).2 a, ZMod.val_zero, pow_zero, one_mul]

/-- An element of `G_{F_∞}` with trivial multipliers fixes `L_∞` (PROVED, lane RC4's GLUE field
`mem_HL_of_kum`). -/
theorem mem_HL_of_kum (σ : GFinf s) (hσ : K.kum σ = 1) : (σ : GalQmu2) ∈ K.HLinf := by
  rw [K.mem_HLinf_iff]
  refine ⟨mem_GFinf_iff.1 σ.2, fun a => ?_⟩
  have h0 : K.kumExp σ a = 0 := congrFun (congrArg Multiplicative.toAdd hσ) a
  rw [K.kumExp_spec σ a, h0, ZMod.val_zero, pow_zero, one_mul]

/-- **The Kummer relations** (tex 3551–3559; genuine): the exponent vectors `b` such that
`∏_a α_a^{b_a}` is a `2^n`-th power in `F_∞`. -/
def KR : AddSubgroup (Fin t → ℤ) where
  carrier := {b | ∃ y ∈ Finf s, y ^ 2 ^ n = ∏ a, K.α a ^ b a}
  zero_mem' := ⟨1, (Finf s).one_mem, by simp⟩
  add_mem' := by
    rintro b c ⟨y, hy, hyb⟩ ⟨z, hz, hzc⟩
    refine ⟨y * z, (Finf s).mul_mem hy hz, ?_⟩
    rw [mul_pow, hyb, hzc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Pi.add_apply, zpow_add₀ (K.α_ne a)]
  neg_mem' := by
    rintro b ⟨y, hy, hyb⟩
    refine ⟨y⁻¹, (Finf s).inv_mem hy, ?_⟩
    rw [inv_pow, hyb, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Pi.neg_apply, zpow_neg]

end KummerData

/-- Non-vacuity: Kummer data exist at every level `n`, for every `s` (a primitive `2^n`-th root of
unity of `ℚ̄`, the radicand `1` and its root `1`). -/
example (s : Qbar) (n : ℕ) : KummerData s n 1 where
  ζ := Classical.choose (HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar (2 ^ n))
  hζ := Classical.choose_spec (HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar (2 ^ n))
  α := fun _ => 1
  α_mem := fun _ => (quadField s).one_mem
  γ := fun _ => 1
  γ_pow := fun _ => one_pow _
  γ_ne := fun _ => one_ne_zero

/-! ### The moving-character setting over the genuine Kummer layer and Tate image -/

/-- **The moving-character data over the genuine objects** (tex 3530–3595, 3662–3684): lane RC4's
`MovingSetting` with `G_{F_∞}`, `G_{L_∞}`, the Kummer multipliers, the Kummer relations and the
trace of `ρ_T` genuine.  The fields are RC4's remaining fields, with the same kinds and locators
(see `ZInQ.Manuscript.RC.Moving.MovingSetting`); `KR_val` and `kum_surj` (GLUE) are stated over
the genuine `KR` and `kum`, and `cheb` (PRINT/GLUE) over the genuine trace. -/
structure MovingData (E : WeierstrassCurve ℚ) (n : ℕ) where
  /-- the allowed field `K = ℚ(√D)`, embedded in `ℚ̄` by `√D ↦ sqrtD` -/
  D : ℚ
  sqrtD : Qbar
  sqrtD_sq : sqrtD ^ 2 = algebraMap ℚ Qbar D
  /-- number of chosen primes -/
  s : ℕ
  /-- number of radicands -/
  t : ℕ
  /-- the Kummer layer at level `n` -/
  kd : KummerData sqrtD n t
  act : Fin s → Prop
  [decAct : DecidablePred act]
  over2N : Fin s → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  Cl : Type
  [clGrp : AddCommGroup Cl]
  cls : Fin s → Cl
  /-- `GLUE` (tex 3532–3534), as in RC4 -/
  cls_gen : ∀ c : Cl, ∃ v : Fin s → ℤ, ∑ j, v j • cls j = c
  m : Fin t → Fin s → ℤ
  m_span : ∀ v : Fin s → ℤ, ∑ j, v j • cls j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  /-- `GLUE` (tex 3551–3557), over the genuine Kummer relations -/
  KR_val : ∀ b ∈ kd.KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j
  /-- `GLUE` (tex 3559–3563, perfect Kummer pairing), over the genuine multipliers -/
  kum_surj : ∀ φ : Fin t → ZMod (2 ^ n),
    (∀ b ∈ kd.KR, ∑ a, (b a : ZMod (2 ^ n)) * φ a = 0) →
      ∃ σ : GFinf sqrtD, kd.kum σ = Multiplicative.ofAdd φ
  good : ℕ → Prop
  ap : ℕ → ℤ
  P : ℕ → Type
  [pGrp : ∀ r, AddCommGroup (P r)]
  Pl : ℕ → Type
  δ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ P r)
  π : ∀ r, P r →+ Cl
  /-- `GLUE` (tex 3566–3575), as in RC4 -/
  δ_inj : ∀ r, good r → ∀ v, Function.Injective (δ r v)
  exact : ∀ r, good r → ∀ v, ∀ p : P r, π r p = 0 ↔ ∃ y, δ r v y = p
  q : ∀ r, Fin s → P r
  qbar : ∀ r, Fin s → P r
  /-- `GLUE` (tex 3575–3576), as in RC4 -/
  π_q : ∀ r, good r → ∀ j, π r (q r j) = cls j
  /-- `GLUE` (tex 3683–3684), as in RC4 -/
  qbar_eq : ∀ r, good r → ∀ j, qbar r j = -q r j
  x : ∀ r, Pl r → Fin t → Additive (ZMod r)ˣ
  /-- `GLUE` (tex 3576–3579), as in RC4 -/
  rel : ∀ r, good r → ∀ v a, ∑ j, m a j • q r j + δ r v (x r v a) = 0
  κ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ ZMod (2 ^ n))
  /-- `GLUE` (tex 3585–3586), as in RC4 -/
  κ_surj : ∀ r, good r → ∀ v, (2 : ℤ) ^ n ∣ (r : ℤ) - 1 → Function.Surjective (κ r v)
  inertia : ∀ r, AddSubgroup (P r)
  /-- `GLUE` (tex 3679–3681), as in RC4 -/
  inertia_eq : ∀ r, good r → ∀ v, inertia r = (δ r v).range
  decomp : ∀ r, Fin s → AddSubgroup (P r)
  decompBar : ∀ r, Fin s → AddSubgroup (P r)
  /-- `GLUE` (tex 3681–3682), as in RC4 -/
  decomp_eq : ∀ r, good r → ∀ j, decomp r j = AddSubgroup.zmultiples (q r j)
  decompBar_eq : ∀ r, good r → ∀ j, decompBar r j = AddSubgroup.zmultiples (qbar r j)
  /-- `PRINT`/`GLUE` (tex 3670–3679), as in RC4, with the genuine trace of `ρ_T(σ)` on `T₂E` and
  the genuine Kummer multipliers -/
  cheb : ∀ (σ : GFinf sqrtD) (B' : ℕ) (S : Finset ℕ), ∃ (r : ℕ) (v : Pl r), r ∉ S ∧ r.Prime ∧
    good r ∧ (2 : ℤ) ^ B' ∣ (r : ℤ) - 1 ∧
    (2 : ℤ_[2]) ^ B' ∣ (ap r : ℤ_[2]) -
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 ((σ : GalQmu2) : GalQ)) ∧
    ∀ a, κ r v (x r v a) = Multiplicative.toAdd (kd.kum σ) a

attribute [instance] MovingData.decAct MovingData.clGrp MovingData.pGrp

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (hS : SerreThm3) (hE : HasNoCM E)
  (hdetEq : DetTateTwoEqCyclotomic E)

/-- **Lane RC4's `MovingSetting` over the genuine Tate image, from `MovingData`**: the fields
`GF`, `GF_index`, `HL`, `HL_le`, `kum`, `kum_of_mem_HL`, `mem_HL_of_kum`, `KR` are the genuine
objects and PROVED facts of this file; `cheb` is converted from the genuine trace by
`tr_tateImage_ρ`; the other fields are copied. -/
def MovingData.toMovingSetting {n : ℕ} (M : MovingData E n) :
    MovingSetting (tateImage E hS hE hdetEq) n where
  s := M.s
  t := M.t
  act := M.act
  over2N := M.over2N
  act_not_over2N := M.act_not_over2N
  Cl := M.Cl
  cls := M.cls
  cls_gen := M.cls_gen
  m := M.m
  m_span := M.m_span
  GF := GFinf M.sqrtD
  GF_index := GFinf_index M.sqrtD_sq
  HL := M.kd.HLinf
  HL_le := M.kd.HLinf_le
  kum := M.kd.kum
  kum_of_mem_HL := M.kd.kum_of_mem_HL
  mem_HL_of_kum := M.kd.mem_HL_of_kum
  KR := M.kd.KR
  KR_val := M.KR_val
  kum_surj := M.kum_surj
  good := M.good
  ap := M.ap
  P := M.P
  Pl := M.Pl
  δ := M.δ
  π := M.π
  δ_inj := M.δ_inj
  exact := M.exact
  q := M.q
  qbar := M.qbar
  π_q := M.π_q
  qbar_eq := M.qbar_eq
  x := M.x
  rel := M.rel
  κ := M.κ
  κ_surj := M.κ_surj
  inertia := M.inertia
  inertia_eq := M.inertia_eq
  decomp := M.decomp
  decompBar := M.decompBar
  decomp_eq := M.decomp_eq
  decompBar_eq := M.decompBar_eq
  cheb σ B' S := by
    obtain ⟨r, v, h1, h2, h3, h4, h5, h6⟩ := M.cheb σ B' S
    refine ⟨r, v, h1, h2, h3, h4, ?_, h6⟩
    convert h5 using 2
    exact tr_tateImage_ρ hS hE hdetEq σ.1

/-- The subgroup `GF` of the setting is the genuine `G_{F_∞}`. -/
theorem MovingData.toMovingSetting_GF {n : ℕ} (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq).GF = GFinf M.sqrtD :=
  rfl

/-- The subgroup `HL` of the setting is the genuine `G_{L_∞}`. -/
theorem MovingData.toMovingSetting_HL {n : ℕ} (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq).HL = M.kd.HLinf :=
  rfl

/-- The Kummer relations of the setting are the genuine ones. -/
theorem MovingData.toMovingSetting_KR {n : ℕ} (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq).KR = M.kd.KR :=
  rfl

/-- **Proposition `ex:arith-moving-character` over the genuine Tate image and Kummer layer**
(tex 3500–3702; PROVED from lane RC4's `moving_character`): with `c_E = 16 d + 21` for the Serre
level `d` of `tateImage`. -/
theorem moving_character_genuine {n : ℕ} (M : MovingData E n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character (M.toMovingSetting hS hE hdetEq) B S

/-- **The same for `E_ℓ`** (tex 3500–3702; PROVED), over `tateImageEcurve`. -/
theorem moving_character_ecurve_genuine (P : ArithPrints) (hcm : CMjInteger) (H : GlueTate)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {n : ℕ} (M : MovingData (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n)
    (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ M.ap r - 2 * χ :=
  @moving_character_genuine (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) P.serre
    (curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')) (@H.detEq _ (ecurve_isElliptic hℓ)) n M B S

end ZInQ.Manuscript.RC.TateWiring

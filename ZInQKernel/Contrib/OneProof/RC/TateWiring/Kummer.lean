import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Basic

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
* `MovingData E n`: lane RC4's `MovingSetting` with the Kummer layer, the trace, the coefficient
  `a_r` and the good primes made genuine: the fields that remain are RC4's other fields, with
  `KR_val` and `kum_surj` (GLUE) stated over the genuine `KR` and `kum`;
  `MovingData.toMovingSetting` and `moving_character_genuine`, `moving_character_frobenius`,
  `moving_character_ecurve_genuine` (PROVED from lane RC4's `moving_character`).

**Lane RC27 (the mismatch "`tr ρ_T(Fr_r) = a_r` missing" in RC4/RC17's `cheb`).** Elliot uses
`a_r` in the statement of the proposition (tex 3509–3512: `v₂(2 ± a_r) ≤ c_E`) and in its last step
(tex 3686–3693: "Finally `a_r ≡ tr ρ_T(σ) (mod 2^{B'})` and `det(Fr_r) = r`"); `a_r` is the
coefficient of `E`, and the consumers use it as such: `m_i = a_{r_i} − 2χ_h(r_i)` in (4.5),
tex 3915, and the local lengths `v₂(r_i + 1 − χ_h(r_i) a_{r_i})` of the calibration (4.6), tex
4066–4074; and in the budget (5.7), tex 5323–5331, "`Φ_{r_i}` is arithmetic Frobenius on `T`, with
trace `a_{r_i}` and determinant `r_i`", `det(Φ_{r_i} − r_i) = r_i det(1 − Φ_{r_i})`.  The identity
`tr ρ_T(Fr_r) = a_r` is therefore needed.  Lane RC17's `MovingData` had an abstract `ap : ℕ → ℤ`,
an abstract `good` and the bundled field `cheb`; now:
* `a_r` is the genuine `E.LFunction r` (no field `ap`), and the good primes are the genuine
  `GoodPrime E sqrtD Sexc` (no field `good`);
* (i) the Chebotarev step (a Frobenius element `Fr_r` at a good prime `r` agreeing with `σ` on
  `K(μ_{2^{B'}}, α_a^{1/2^n})` and on `E[2^{B'}]`, so `r` splits in `K`, `r ≡ 1 (mod 2^{B'})` and
  `ρ_T(Fr_r) ≡ ρ_T(σ) (mod 2^{B'})`) is PROVED: `MovingData.exists_frobenius`, from the tree's
  Chebotarev density theorem through lane RC22's `GlueSweep.Tate.exists_frob_congr`;
* (ii) `tr ρ_T(Fr_r) = a_r` at good odd `r` is the explicit GLUE `FrobeniusTrace E` (Silverman,
  AEC, Theorem V.2.3.1 with Propositions VII.3.1(b), VII.4.1; locators in its docstring), a
  hypothesis; `det ρ_T(Fr_r) = r` is PROVED (`GlueSweep.Tate.det_tateRep_eq_of_isFrobAt`);
* (iii) the power-residue (Frobenius) formula on the radicals is the GLUE field `frob_kummer`;
* lane RC4's field `cheb` is derived (`MovingData.cheb`), so RC4's abstract interface and
  `moving_character` are unchanged; `MovingData.trivial` is a non-vacuity witness.
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

/-! ### Frobenius elements at good primes: `a_r`, the trace and the determinant (Lane RC27) -/

/-- The primes at which the given model of `E` can fail to be good in the sense of lane RC13's
`Nonvanishing.GoodAt`: the prime factors of the denominators of `a₁, a₂, a₃, a₄, a₆` and of the
numerator and the denominator of `Δ` (definition; part of Elliot's "finitely many excluded primes",
tex 3676: the moving prime is good, `r ∤ 2N`). -/
def badPrimes (E : WeierstrassCurve ℚ) : Finset ℕ :=
  (E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den).primeFactors

/-- **Outside `badPrimes E` the model is good** (tex 3676; Kind: PROVED): for `Δ ≠ 0` and a prime
`p ∉ badPrimes E`, the coefficients of `E` are `p`-integral and `Δ` is a `p`-adic unit
(`Nonvanishing.GoodAt E p`). -/
theorem goodAt_of_not_mem_badPrimes {E : WeierstrassCurve ℚ} (hΔ : E.Δ ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ badPrimes E) : Nonvanishing.GoodAt E p := by
  set N := E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den
    with hN
  have hN0 : N ≠ 0 := by
    have h1 : E.Δ.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hΔ)
    simp only [hN, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨⟨⟨E.a₁.den_nz, E.a₂.den_nz⟩, E.a₃.den_nz⟩, E.a₄.den_nz⟩, E.a₆.den_nz⟩, h1⟩,
      E.Δ.den_nz⟩
  have hnd : ¬ p ∣ N := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, hN0⟩)
  have h1 : E.a₁.den ∣ N :=
    ⟨E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den, by rw [hN]; ring⟩
  have h2 : E.a₂.den ∣ N :=
    ⟨E.a₁.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den, by rw [hN]; ring⟩
  have h3 : E.a₃.den ∣ N :=
    ⟨E.a₁.den * E.a₂.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den, by rw [hN]; ring⟩
  have h4 : E.a₄.den ∣ N :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₆.den * E.Δ.num.natAbs * E.Δ.den, by rw [hN]; ring⟩
  have h6 : E.a₆.den ∣ N :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.Δ.num.natAbs * E.Δ.den, by rw [hN]; ring⟩
  have h7 : E.Δ.num.natAbs ∣ N :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.den, by rw [hN]; ring⟩
  have h8 : E.Δ.den ∣ N :=
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den * E.Δ.num.natAbs, by rw [hN]; ring⟩
  refine ⟨fun h => hnd (h.trans h1), fun h => hnd (h.trans h2), fun h => hnd (h.trans h3),
    fun h => hnd (h.trans h4), fun h => hnd (h.trans h6), hΔ, ?_⟩
  have hnum : ¬ p ∣ E.Δ.num.natAbs := fun h => hnd (h.trans h7)
  have hden : ¬ p ∣ E.Δ.den := fun h => hnd (h.trans h8)
  rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hnum,
    padicValNat.eq_zero_of_not_dvd hden]
  rfl

/-- **GLUE (not proved here): `tr ρ_T(Fr_r) = a_r` at the good odd primes** (tex 3686: "Finally
`a_r ≡ tr ρ_T(σ) (mod 2^{B'})`"; also the statement of the proposition, tex 3509–3512, where `a_r` is
the coefficient of `E`).  For every odd prime `r` at which the model `E` is good (lane RC13's
`Nonvanishing.GoodAt E r`: `r`-integral coefficients and `r`-adic unit discriminant, so that `E`
has good reduction at `r`, lane RC22's `GlueSweep.Ana.hasGoodReduction_of_goodAt`) and every
arithmetic Frobenius element `h ∈ G_ℚ` at `r` (the tree's `ZInQ.Contrib.ChebFD.C10.IsFrobAt`), the
trace of `ρ_T(h)` on `T₂E` is `a_r(E)`, the coefficient at `r` of Mathlib's L-function
`E.LFunction`, i.e. `r + 1 − |Ẽ(𝔽_r)|` for the reduction `Ẽ` of a minimal model at `r` (Mathlib's
`WeierstrassCurve.localPolynomial`; for `E_m` at `r ∤ 6m` lane RC3's
`KSplit.LFunction_curve_apply_prime`).

Printed (read for this lane in J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM
106, Springer 2009): Proposition VII.3.1(b), p. 192 (for good reduction, the reduction map
`E(K)[m] → Ẽ(k)` is injective for `m` prime to the residue characteristic), with Proposition
VII.4.1, p. 195 (`E[m]` and `T_ℓ(E)` are then unramified), which identify `T₂E` with `T₂Ẽ`
compatibly with the decomposition group at a prime of `ℤ̄` over `r`, `h` going to the `r`-power
Frobenius endomorphism `φ` of `Ẽ`; and Theorem V.2.3.1, p. 142, with its proof and Remark V.2.6,
p. 144 (`det(φ_ℓ) = r`, `tr(φ_ℓ) = 1 + r − |Ẽ(𝔽_r)| = a`, from Proposition V.2.3 = III.8.6,
p. 141). Kind: GLUE (the Eichler–Shimura relation for elliptic curves over finite fields); a
hypothesis of the final statements, never assumed globally. Non-vacuity: its premises are
satisfiable at infinitely many primes (`frobeniusTrace_premises`, PROVED from the tree's
Chebotarev theorem); for a singular model (`Δ = 0`) it is vacuous, since `GoodAt` asks `Δ ≠ 0`. -/
def FrobeniusTrace (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (r : ℕ), r.Prime → r ≠ 2 → Nonvanishing.GoodAt E r → ∀ h : GalQ,
    ZInQ.Contrib.ChebFD.C10.IsFrobAt h r →
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 h) = ((E.LFunction r : ℤ) : ℤ_[2])

/-- **The premises of `FrobeniusTrace` are satisfiable outside every finite set** (non-vacuity;
PROVED from the tree's Chebotarev theorem `ZInQ.Contrib.ChebFD.C10.frobDense`
`ZInQ.Contrib.chebotarevExists`): for an elliptic `E/ℚ` and a finite set `S` there are an odd prime
`r ∉ S` at which the model `E` is good and an arithmetic Frobenius element at `r`. -/
theorem frobeniusTrace_premises (E : WeierstrassCurve ℚ) [E.IsElliptic] (S : Finset ℕ) :
    ∃ (r : ℕ) (h : GalQ), r.Prime ∧ r ∉ S ∧ r ≠ 2 ∧ Nonvanishing.GoodAt E r ∧
      ZInQ.Contrib.ChebFD.C10.IsFrobAt h r := by
  obtain ⟨h, r, hr, hrS, hF, -⟩ := ZInQ.Contrib.ChebFD.C10.frobDense
    ZInQ.Contrib.chebotarevExists (insert 2 (S ∪ badPrimes E)) ⊥ inferInstance 1
  refine ⟨r, h, hr, fun h' => hrS (Finset.mem_insert_of_mem (Finset.mem_union_left _ h')),
    fun h2 => hrS (by rw [h2]; exact Finset.mem_insert_self _ _), goodAt_of_not_mem_badPrimes
    E.isUnit_Δ.ne_zero hr fun h' => hrS (Finset.mem_insert_of_mem (Finset.mem_union_right _ h')),
    hF⟩

/-- **Congruent Tate matrices have congruent traces** (tex 3686, "`a_r ≡ tr ρ_T(σ) (mod 2^{B'})`";
Kind: PROVED): if `ρ₂(h) ≡ ρ₂(σ) (mod 2^M)` (as matrices in lane RC9's basis), then
`2^M ∣ tr ρ_T(h) − tr ρ_T(σ)` in `ℤ₂`. -/
theorem two_pow_dvd_trace_sub_of_congr (E : WeierstrassCurve ℚ) [E.IsElliptic] {M : ℕ}
    {h σ : GalQ} (hc : (PadicInt.toZModPow M).mapMatrix (tateMatrix E h) =
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ)) :
    (2 : ℤ_[2]) ^ M ∣ LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 h) -
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) := by
  rw [← trace_tateMatrix, ← trace_tateMatrix]
  have hc' : (tateMatrix E h).map (PadicInt.toZModPow M) =
      (tateMatrix E σ).map (PadicInt.toZModPow M) := hc
  have h0 : PadicInt.toZModPow M ((tateMatrix E h).trace - (tateMatrix E σ).trace) = 0 := by
    rw [map_sub, AddMonoidHom.map_trace, AddMonoidHom.map_trace, hc', sub_self]
  have hmem : (tateMatrix E h).trace - (tateMatrix E σ).trace ∈
      RingHom.ker (PadicInt.toZModPow (p := 2) M) := h0
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  simpa using hmem

/-- **A good prime for the moving character** (tex 3502–3503, 3566, 3673–3677): `r` is an odd prime
at which the model `E` is good (so `r ∤ 2N`), outside the finite set `Sexc` of excluded primes
(Elliot's "finitely many excluded primes", tex 3676: the primes ramified in `K`, the primes under
the chosen primes, and any other prime to be avoided), and split in `K = ℚ(s)`: some arithmetic
Frobenius element at `r` fixes `s = √D` (for `r` unramified in `K` — `Sexc` is to contain the primes
ramified in `K` — this is "`r` splits in `K`"; definition).  Lane RC27: this replaces the abstract predicate `good` of lane RC17's
`MovingData` (lane RC4's `MovingSetting.good`). -/
def GoodPrime (E : WeierstrassCurve ℚ) (s : Qbar) (Sexc : Finset ℕ) (r : ℕ) : Prop :=
  r.Prime ∧ r ≠ 2 ∧ Nonvanishing.GoodAt E r ∧ r ∉ Sexc ∧
    ∃ h : GalQ, ZInQ.Contrib.ChebFD.C10.IsFrobAt h r ∧ h s = s

/-! ### The moving-character setting over the genuine Kummer layer and Tate image -/

/-- **The moving-character data over the genuine objects** (tex 3530–3595, 3662–3693): lane RC4's
`MovingSetting` with `G_{F_∞}`, `G_{L_∞}`, the Kummer multipliers, the Kummer relations, the trace of
`ρ_T`, the coefficient `a_r` and the good primes genuine.  The fields are RC4's remaining fields,
with the same kinds and locators (see `ZInQ.Manuscript.RC.Moving.MovingSetting`); `KR_val` and
`kum_surj` (GLUE) are stated over the genuine `KR` and `kum`.

Lane RC27 (fix of the mismatch "`tr ρ_T(Fr_r) = a_r` missing, `good`, `ap` abstract" of RC4/RC17's
field `cheb`):
* there is no field `ap`: `a_r` is the genuine coefficient `E.LFunction r` (Mathlib's L-function of
  `E`), as in tex 3509–3512 and 3686–3693;
* there is no field `good`: the good primes are the genuine `GoodPrime E sqrtD Sexc` (odd, model good,
  split in `K`, outside the finite data set `Sexc` of excluded primes); `MovingData.good`;
* the field `cheb` (finite Chebotarev, the trace congruence and the power-residue formula bundled)
  is split into its three ingredients, as Elliot uses them at tex 3670–3693: (i) the Chebotarev step
  — a Frobenius element at a good prime agreeing with `σ` on `K(μ_{2^{B'}}, α_a^{1/2^n})` and with
  `ρ_T(σ)` modulo `2^{B'}` — is PROVED (`MovingData.exists_frobenius`, from the tree's Chebotarev
  theorem); (ii) `tr ρ_T(Fr_r) = a_r` is the explicit GLUE `FrobeniusTrace E`, a hypothesis of
  `toMovingSetting` and of the final statements; (iii) the power-residue (Frobenius) formula
  on the radicals is the GLUE field `frob_kummer`.  RC4's field `cheb` is then derived
  (`MovingData.cheb`), so lane RC4's abstract `MovingSetting` and `moving_character` are unchanged.

Non-vacuity: `MovingData.trivial E n` (an inhabitant for every `E` and `n`, with no chosen prime and
no radicand) shows that the fields are jointly satisfiable; the final statements apply to it (the
`example` after `MovingData.trivial`). -/
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
  /-- `GLUE` (tex 3559–3563, perfect Kummer pairing), over the genuine multipliers (PROVED in the
  tree: lane RC22's `GlueSweep.Tate.kum_surj_genuine`) -/
  kum_surj : ∀ φ : Fin t → ZMod (2 ^ n),
    (∀ b ∈ kd.KR, ∑ a, (b a : ZMod (2 ^ n)) * φ a = 0) →
      ∃ σ : GFinf sqrtD, kd.kum σ = Multiplicative.ofAdd φ
  /-- the excluded primes (tex 3566, 3676: the primes ramified in `K`, the primes under the chosen
  primes; data); the good primes are `GoodPrime E sqrtD Sexc` -/
  Sexc : Finset ℕ
  P : ℕ → Type
  [pGrp : ∀ r, AddCommGroup (P r)]
  Pl : ℕ → Type
  δ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ P r)
  π : ∀ r, P r →+ Cl
  /-- `GLUE` (tex 3566–3575), as in RC4 -/
  δ_inj : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, Function.Injective (δ r v)
  exact : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, ∀ p : P r, π r p = 0 ↔ ∃ y, δ r v y = p
  q : ∀ r, Fin s → P r
  qbar : ∀ r, Fin s → P r
  /-- `GLUE` (tex 3575–3576), as in RC4 -/
  π_q : ∀ r, GoodPrime E sqrtD Sexc r → ∀ j, π r (q r j) = cls j
  /-- `GLUE` (tex 3683–3684), as in RC4 -/
  qbar_eq : ∀ r, GoodPrime E sqrtD Sexc r → ∀ j, qbar r j = -q r j
  x : ∀ r, Pl r → Fin t → Additive (ZMod r)ˣ
  /-- `GLUE` (tex 3576–3579), as in RC4 -/
  rel : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v a, ∑ j, m a j • q r j + δ r v (x r v a) = 0
  κ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ ZMod (2 ^ n))
  /-- `GLUE` (tex 3585–3586), as in RC4 -/
  κ_surj : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
    Function.Surjective (κ r v)
  inertia : ∀ r, AddSubgroup (P r)
  /-- `GLUE` (tex 3679–3681), as in RC4 -/
  inertia_eq : ∀ r, GoodPrime E sqrtD Sexc r → ∀ v, inertia r = (δ r v).range
  decomp : ∀ r, Fin s → AddSubgroup (P r)
  decompBar : ∀ r, Fin s → AddSubgroup (P r)
  /-- `GLUE` (tex 3681–3682), as in RC4 -/
  decomp_eq : ∀ r, GoodPrime E sqrtD Sexc r → ∀ j, decomp r j = AddSubgroup.zmultiples (q r j)
  decompBar_eq : ∀ r, GoodPrime E sqrtD Sexc r → ∀ j,
    decompBar r j = AddSubgroup.zmultiples (qbar r j)
  /-- `GLUE` (tex 3676–3677, "Choose a place realizing this representative ... The Frobenius
  formula on `α_a^{1/2^n}` gives (4.4b)"; Lane RC27, ingredient (iii) of RC4's `cheb`): **the
  power-residue (Frobenius) formula**.  For a good prime `r ≡ 1 (mod 2^n)` and an arithmetic
  Frobenius element `h` at `r` fixing `K`, some place `v` over `r` (the place of `h`, orienting the
  data at `r`) satisfies `h(α_a^{1/2^n}) = ζ_{2^n}^{κ_r(res α_a)} α_a^{1/2^n}` for every radicand: the
  `2^n`-th power-residue symbol of `α_a` at `v` (the root of unity `≡ α_a^{(r−1)/2^n}` modulo the
  place) is the Frobenius multiplier.  Kind: GLUE.  Its content is the identification of the
  abstract `Pl r`, `x`, `κ` with the places over `r`, the residues `α_a mod 𝔯` and the
  `2^n`-th power-residue characters normalized by `ζ` (they stay abstract because `rel` ties them
  to the ring-class data `δ`, `P r`, which are not in Mathlib); with that identification the
  formula is the one-line computation `h(γ_a) ≡ γ_a^r` modulo the place of `h`, so
  `h(γ_a)/γ_a ≡ α_a^{(r−1)/2^n}` (cf. the power residue symbol, J. Neukirch, *Algebraic number
  theory*, Ch. V, §3: `UNVERIFIED` locator, not read). -/
  frob_kummer : ∀ (r : ℕ) (h : GalQ), GoodPrime E sqrtD Sexc r →
    ZInQ.Contrib.ChebFD.C10.IsFrobAt h r → h sqrtD = sqrtD → (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
      ∃ v : Pl r, ∀ a, h (kd.γ a) = kd.ζ ^ (κ r v (x r v a)).val * kd.γ a

attribute [instance] MovingData.decAct MovingData.clGrp MovingData.pGrp

section Genuine

variable {E : WeierstrassCurve ℚ} {n : ℕ}

/-- **The good primes of the setting** (tex 3566, 3673–3677; definition, genuine):
`GoodPrime E M.sqrtD M.Sexc`. -/
def MovingData.good (M : MovingData E n) (r : ℕ) : Prop :=
  GoodPrime E M.sqrtD M.Sexc r

/-- **(i) The Chebotarev step of tex 3670–3679, over the genuine objects** (Lane RC27; PROVED, no
remaining hypothesis): for `σ ∈ G_{F_∞}`, `B` and a finite set `S`, there are a good prime `r ∉ S`
and an arithmetic Frobenius element `h` at `r` (at the place realizing `σ`) such that `h` fixes
`√D` (so `r` splits in `K`), `r ≡ 1 (mod 2^B)` (`h` agrees with `σ` on `μ_{2^B}`), `h = σ` on the
chosen radicals `α_a^{1/2^n}`, and `ρ₂(h) ≡ ρ₂(σ) (mod 2^B)` (`h = σ` on `E[2^B]`).  Elliot: "take a
finite normal extension of `ℚ` containing `K, μ_{2^{B'}}, E[2^{B'}]` and all the chosen radical
roots ... Finite Chebotarev supplies infinitely many rational primes in its Frobenius class ...
Then `r` splits in `K` and `r ≡ 1 (mod 2^{B'})`."  Proof: lane RC22's `exists_frob_congr`
(the tree's Chebotarev density theorem) for `ℚ(√D, ζ_{2^B}, α_a^{1/2^n})` and the avoidance set
`S ∪ Sexc ∪ badPrimes E`; `h ζ = ζ^r` on `μ_{2^B}` (`apply_eq_pow_of_isFrobAt`). -/
theorem MovingData.exists_frobenius [E.IsElliptic] (M : MovingData E n) (σ : GFinf M.sqrtD)
    (B : ℕ) (S : Finset ℕ) :
    ∃ (r : ℕ) (h : GalQ), r ∉ S ∧ M.good r ∧ ZInQ.Contrib.ChebFD.C10.IsFrobAt h r ∧
      h M.sqrtD = M.sqrtD ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      (∀ a, h (M.kd.γ a) = ((σ : GalQmu2) : GalQ) (M.kd.γ a)) ∧
      (PadicInt.toZModPow B).mapMatrix (tateMatrix E h) =
        (PadicInt.toZModPow B).mapMatrix (tateMatrix E ((σ : GalQmu2) : GalQ)) := by
  classical
  obtain ⟨ζB, hζB⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar (2 ^ B)
  set X : Set Qbar := insert M.sqrtD (insert ζB (Set.range M.kd.γ)) with hX
  have hXfin : X.Finite := ((Set.finite_range _).insert _).insert _
  have : Finite X := hXfin.to_subtype
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ X) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h, r, hr, hrS, hr2, hF, hagree, hcong, hfrob⟩ :=
    ZInQ.Manuscript.RC.GlueSweep.Tate.exists_frob_congr E ((σ : GalQmu2) : GalQ) B
      (IntermediateField.adjoin ℚ X) (S ∪ M.Sexc ∪ badPrimes E)
  have hmem : ∀ y ∈ X, h y = ((σ : GalQmu2) : GalQ) y := fun y hy =>
    hagree y (IntermediateField.subset_adjoin ℚ X hy)
  have hs : h M.sqrtD = M.sqrtD := by
    rw [hmem _ (Set.mem_insert _ _)]
    exact mem_GFinf_iff.1 σ.2
  have hζ : h ζB = ζB := by
    rw [hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))]
    exact mem_GalQmu2_iff.1 (σ : GalQmu2).2 B ζB hζB.pow_eq_one
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hpow : ζB ^ (r - 1) = 1 := by
    have h1 : ζB ^ r = ζB := by rw [← hfrob ζB hζB.pow_eq_one, hζ]
    have hne : ζB ≠ 0 := hζB.ne_zero (pow_ne_zero B two_ne_zero)
    have h2 : ζB ^ (r - 1) * ζB = 1 * ζB := by
      rw [← pow_succ, Nat.sub_add_cancel hr1, h1, one_mul]
    exact mul_right_cancel₀ hne h2
  have hdvd : (2 : ℤ) ^ B ∣ (r : ℤ) - 1 := by
    have h1 := Int.natCast_dvd_natCast.2 (hζB.dvd_of_pow_eq_one _ hpow)
    push_cast [Nat.cast_sub hr1] at h1
    exact h1
  refine ⟨r, h, fun h' => hrS (Finset.mem_union_left _ (Finset.mem_union_left _ h')),
    ⟨hr, hr2, goodAt_of_not_mem_badPrimes E.isUnit_Δ.ne_zero hr
      fun h' => hrS (Finset.mem_union_right _ h'),
      fun h' => hrS (Finset.mem_union_left _ (Finset.mem_union_right _ h')), h, hF, hs⟩,
    hF, hs, hdvd, fun a => hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨a, rfl⟩)),
    hcong⟩

/-- **Lane RC4's field `cheb`, derived** (tex 3670–3686; Lane RC27; PROVED from (i)
`exists_frobenius`, (ii) the GLUE `FrobeniusTrace E` and (iii) the GLUE field `frob_kummer`):
for `σ ∈ G_{F_∞}`, `B'` and a finite set `S` there are a good prime `r ∉ S` and a place `v` over `r`
with `r ≡ 1 (mod 2^{B'})`, `a_r ≡ tr ρ_T(σ) (mod 2^{B'})` for the genuine `a_r = E.LFunction r`
("Finally `a_r ≡ tr ρ_T(σ) (mod 2^{B'})`": `tr ρ_T(Fr_r) = a_r` and `Fr_r ≡ σ` on `E[2^{B'}]`), and
`κ_r(res α_a)` the Kummer multiplier of `σ` ("The Frobenius formula on `α_a^{1/2^n}` gives (4.4b)").
Chebotarev is applied with `max B' n`, so that also `r ≡ 1 (mod 2^n)`. -/
theorem MovingData.cheb [E.IsElliptic] (hT : FrobeniusTrace E) (M : MovingData E n)
    (σ : GFinf M.sqrtD) (B' : ℕ) (S : Finset ℕ) :
    ∃ (r : ℕ) (v : M.Pl r), r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B' ∣ (r : ℤ) - 1 ∧
      (2 : ℤ_[2]) ^ B' ∣ ((E.LFunction r : ℤ) : ℤ_[2]) -
        LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 ((σ : GalQmu2) : GalQ)) ∧
      ∀ a, M.κ r v (M.x r v a) = Multiplicative.toAdd (M.kd.kum σ) a := by
  obtain ⟨r, h, hrS, hgood, hF, hs, hr1, hγ, hcong⟩ := M.exists_frobenius σ (max B' n) S
  have hB' : (2 : ℤ) ^ B' ∣ (r : ℤ) - 1 := (pow_dvd_pow 2 (le_max_left _ _)).trans hr1
  have hn : (2 : ℤ) ^ n ∣ (r : ℤ) - 1 := (pow_dvd_pow 2 (le_max_right _ _)).trans hr1
  obtain ⟨v, hv⟩ := M.frob_kummer r h hgood hF hs hn
  refine ⟨r, v, hrS, hgood.1, hgood, hB', ?_, fun a => ?_⟩
  · rw [← hT r hgood.1 hgood.2.1 hgood.2.2.1 h hF]
    exact (pow_dvd_pow (2 : ℤ_[2]) (le_max_left B' n)).trans
      (two_pow_dvd_trace_sub_of_congr E hcong)
  · rw [KummerData.toAdd_kum]
    apply M.kd.exp_unique a
    rw [← hv a, hγ a, M.kd.kumExp_spec σ a]

section Setting

variable [E.IsElliptic] (hS : SerreThm3) (hE : HasNoCM E) (hdetEq : DetTateTwoEqCyclotomic E)

/-- **Lane RC4's `MovingSetting` over the genuine Tate image, from `MovingData`**: the fields
`GF`, `GF_index`, `HL`, `HL_le`, `kum`, `kum_of_mem_HL`, `mem_HL_of_kum`, `KR` are the genuine
objects and PROVED facts of this file; `good` is the genuine `MovingData.good`, `ap r` the genuine
`a_r = E.LFunction r`; `cheb` is `MovingData.cheb` (from the PROVED Chebotarev step, the GLUE
`FrobeniusTrace E` and the GLUE field `frob_kummer`), converted to the matrix trace by
`tr_tateImage_ρ`; the other fields are copied. -/
def MovingData.toMovingSetting (hT : FrobeniusTrace E) (M : MovingData E n) :
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
  ap r := E.LFunction r
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
    obtain ⟨r, v, h1, h2, h3, h4, h5, h6⟩ := M.cheb hT σ B' S
    refine ⟨r, v, h1, h2, h3, h4, ?_, h6⟩
    rw [tr_tateImage_ρ hS hE hdetEq σ.1]
    exact h5

/-- The subgroup `GF` of the setting is the genuine `G_{F_∞}` (tex 3606; Kind: PROVED, by
definition). -/
theorem MovingData.toMovingSetting_GF (hT : FrobeniusTrace E) (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq hT).GF = GFinf M.sqrtD :=
  rfl

/-- The subgroup `HL` of the setting is the genuine `G_{L_∞}` (tex 3624–3626; Kind: PROVED, by
definition). -/
theorem MovingData.toMovingSetting_HL (hT : FrobeniusTrace E) (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq hT).HL = M.kd.HLinf :=
  rfl

/-- The Kummer relations of the setting are the genuine ones (tex 3551–3559; Kind: PROVED, by
definition). -/
theorem MovingData.toMovingSetting_KR (hT : FrobeniusTrace E) (M : MovingData E n) :
    (M.toMovingSetting hS hE hdetEq hT).KR = M.kd.KR :=
  rfl

/-- The coefficient `ap r` of the setting is the genuine `a_r = E.LFunction r` (tex 3509–3512,
3686–3693; Lane RC27; Kind: PROVED, by definition). -/
theorem MovingData.toMovingSetting_ap (hT : FrobeniusTrace E) (M : MovingData E n) (r : ℕ) :
    (M.toMovingSetting hS hE hdetEq hT).ap r = E.LFunction r :=
  rfl

/-- The good primes of the setting are the genuine `GoodPrime E M.sqrtD M.Sexc` (tex 3566,
3673–3677; Lane RC27; Kind: PROVED, by definition). -/
theorem MovingData.toMovingSetting_good (hT : FrobeniusTrace E) (M : MovingData E n) (r : ℕ) :
    (M.toMovingSetting hS hE hdetEq hT).good r ↔ GoodPrime E M.sqrtD M.Sexc r :=
  Iff.rfl

/-- **Proposition `ex:arith-moving-character` over the genuine Tate image and Kummer layer**
(tex 3500–3702; PROVED from lane RC4's `moving_character`): with `c_E = 16 d + 21` for the Serre
level `d` of `tateImage`, and the genuine `a_r = E.LFunction r` (Lane RC27: the bounds of tex
3509–3512 and 3688–3693 are about the coefficient of `E`; hypotheses: `SerreThm3` (PRINT), non-CM,
`det ρ_T = χ_cyc`, the GLUE `FrobeniusTrace E` and the fields of `MovingData`). -/
theorem moving_character_genuine (hT : FrobeniusTrace E) (M : MovingData E n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 + E.LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 - E.LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 + E.LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 - E.LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ E.LFunction r - 2 * χ :=
  moving_character (M.toMovingSetting hS hE hdetEq hT) B S

/-- **`tr ρ_T(Fr_r) = a_r` and `det ρ_T(Fr_r) = r` at a good prime** (tex 3686, "Finally
`a_r ≡ tr ρ_T(σ)` ... and `det(Fr_r) = r`"): for a good prime `r` of the setting and every
arithmetic Frobenius element `h` at `r`.  Kind: the trace from the GLUE `FrobeniusTrace E`; the
determinant PROVED (`GlueSweep.Tate.det_tateRep_eq_of_isFrobAt`, from the tree's `det ρ₂ = χ₂`). -/
theorem MovingData.trace_det_frob (hT : FrobeniusTrace E) (M : MovingData E n) {r : ℕ}
    (hr : M.good r) {h : GalQ} (hF : ZInQ.Contrib.ChebFD.C10.IsFrobAt h r) :
    LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 h) = ((E.LFunction r : ℤ) : ℤ_[2]) ∧
      LinearMap.det (tateRep E 2 h) = (r : ℤ_[2]) :=
  ⟨hT r hr.1 hr.2.1 hr.2.2.1 h hF,
    ZInQ.Manuscript.RC.GlueSweep.Tate.det_tateRep_eq_of_isFrobAt E hr.2.1 hF⟩

/-- **Proposition `ex:arith-moving-character` with the genuine Frobenius at `r`** (tex 3500–3702;
Lane RC27; PROVED from `moving_character_genuine`, the GLUE `FrobeniusTrace E` and the PROVED
`det ρ_T(Fr_r) = r`): the prime `r` and the character `ξ` of `moving_character_genuine`, with all its
bounds for the genuine `a_r = E.LFunction r`, and, for every arithmetic Frobenius element `Fr_r` at
`r`, `tr ρ_T(Fr_r) = a_r`, `det ρ_T(Fr_r) = r` and `v₂ det(1 ± ρ_T(Fr_r)) = v₂(1 ± a_r + r) ≤ c_E`
(tex 3686–3691: the determinant bound over the genuine Frobenius matrix, `det_one_add_bound`). -/
theorem moving_character_frobenius (hT : FrobeniusTrace E) (M : MovingData E n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      (∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1)) ∧
      ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 + E.LFunction r ∧
      ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 - E.LFunction r ∧
      ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 + E.LFunction r + r ∧
      ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 - E.LFunction r + r ∧
      (∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ E.LFunction r - 2 * χ) ∧
      ∀ h : GalQ, ZInQ.Contrib.ChebFD.C10.IsFrobAt h r →
        LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 h) = ((E.LFunction r : ℤ) : ℤ_[2]) ∧
        LinearMap.det (tateRep E 2 h) = (r : ℤ_[2]) ∧
        v2Le (1 + tateMatrix E h).det (cE (tateImage E hS hE hdetEq).d) ∧
        v2Le (1 - tateMatrix E h).det (cE (tateImage E hS hE hdetEq).d) := by
  obtain ⟨r, hrS, -, hgood, hr1, ξ, hξ1, hξ2, hξ3, hb1, hb2, hb3, hb4, hb5⟩ :=
    moving_character_genuine hS hE hdetEq hT M B S
  refine ⟨r, hrS, hgood, hr1, ⟨ξ, hξ1, hξ2, hξ3⟩, hb1, hb2, hb3, hb4, hb5, fun h hF => ?_⟩
  obtain ⟨htr, hdet⟩ := M.trace_det_frob hT hgood hF
  refine ⟨htr, hdet, det_one_add_bound (cE (tateImage E hS hE hdetEq).d) (E.LFunction r) r
    (tateMatrix E h) ?_ ?_ hb3 hb4⟩
  · rw [trace_tateMatrix, htr]
  · rw [det_tateMatrix, hdet, Int.cast_natCast]

end Setting

/-- **The same for `E_ℓ`** (tex 3500–3702; PROVED), over `tateImageEcurve`, with the genuine
`a_r = (E_ℓ).LFunction r` (`= r + 1 − |Ẽ_ℓ(𝔽_r)|` at `r ∤ 6ℓ`, lane RC3's
`KSplit.LFunction_curve_apply_prime`); hypotheses: `ArithPrints` (only `serre` used), `CMjInteger`,
`GlueTate` and the GLUE `FrobeniusTrace (E_ℓ)`. -/
theorem moving_character_ecurve_genuine (P : ArithPrints) (hcm : CMjInteger) (H : GlueTate)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingData (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  @moving_character_genuine (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n (ecurve_isElliptic hℓ) P.serre
    (curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')) (@H.detEq _ (ecurve_isElliptic hℓ)) hT M B S

end Genuine

/-! ### Non-vacuity of `MovingData` -/

/-- `2^n` divides the order `r − 1` of `𝐅_r^×` when `r` is prime and `2^n ∣ r − 1` (tex 3585–3586;
Kind: PROVED; used only by the non-vacuity witness). -/
theorem kappaTriv_dvd (n r : ℕ) (h : r.Prime ∧ (2 : ℤ) ^ n ∣ (r : ℤ) - 1) :
    2 ^ n ∣ Nat.card (Additive (ZMod r)ˣ) := by
  have : Fact r.Prime := ⟨h.1⟩
  have hc : Nat.card (Additive (ZMod r)ˣ) = r - 1 := by
    rw [show Nat.card (Additive (ZMod r)ˣ) = Nat.card (ZMod r)ˣ from rfl,
      Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hc]
  have h1 : 1 ≤ r := h.1.one_lt.le
  apply Int.natCast_dvd_natCast.1
  push_cast [Nat.cast_sub h1]
  exact h.2

/-- A surjective homomorphism `𝐅_r^× → ℤ/2^n` when `r` is prime and `2^n ∣ r − 1` (the units of
`𝐅_r` form a cyclic group of order `r − 1`, tex 3585–3586); `0` otherwise (definition).  Used only by
the non-vacuity witness `MovingData.trivial`. -/
def kappaTriv (n r : ℕ) : Additive (ZMod r)ˣ →+ ZMod (2 ^ n) :=
  if h : r.Prime ∧ (2 : ℤ) ^ n ∣ (r : ℤ) - 1 then
    haveI : Fact r.Prime := ⟨h.1⟩
    (ZMod.castHom (kappaTriv_dvd n r h) (ZMod (2 ^ n))).toAddMonoidHom.comp
      (zmodAddCyclicAddEquiv (isAddCyclic_additive_iff.2 inferInstance)).symm.toAddMonoidHom
  else 0

/-- `kappaTriv n r` is onto when `r` is prime and `2^n ∣ r − 1` (tex 3585–3586; Kind: PROVED). -/
theorem kappaTriv_surjective {n r : ℕ} (hr : r.Prime) (hd : (2 : ℤ) ^ n ∣ (r : ℤ) - 1) :
    Function.Surjective (kappaTriv n r) := by
  have h : r.Prime ∧ (2 : ℤ) ^ n ∣ (r : ℤ) - 1 := ⟨hr, hd⟩
  have : Fact r.Prime := ⟨hr⟩
  rw [kappaTriv, dite_eq_left h]
  exact (ZMod.castHom_surjective (kappaTriv_dvd n r h)).comp (AddEquiv.surjective _)

/-- **Non-vacuity of `MovingData`** (Lane RC27): an inhabitant for every `E` and every `n`, with no
chosen prime and no radicand (`s = t = 0`), `K = ℚ(√1)`, `Cl(K)` trivial, `Gal(H_r/K)` replaced by
`𝐅_r^×` with `δ = id`, a single place over each `r`, a surjective `κ_r` (`kappaTriv`) and no excluded
prime.  It shows that the fields of `MovingData` (in particular the new GLUE field `frob_kummer` and
the genuine good primes) are jointly satisfiable.  It is degenerate: the genuine data (an allowed
imaginary quadratic `K`, ring class fields `H_r`, their Artin maps) are not in Mathlib, so no genuine
instance is constructed (as for lane RC4's `MovingSetting`). -/
def MovingData.trivial (E : WeierstrassCurve ℚ) (n : ℕ) : MovingData E n where
  D := 1
  sqrtD := 1
  sqrtD_sq := by simp
  s := 0
  t := 0
  kd :=
    { ζ := Classical.choose (HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar (2 ^ n))
      hζ := Classical.choose_spec (HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar (2 ^ n))
      α := fun a => a.elim0
      α_mem := fun a => a.elim0
      γ := fun a => a.elim0
      γ_pow := fun a => a.elim0
      γ_ne := fun a => a.elim0 }
  act := fun _ => False
  decAct := fun _ => instDecidableFalse
  over2N := fun _ => False
  act_not_over2N := fun _ h => h.elim
  Cl := Unit
  cls := fun _ => 0
  cls_gen := fun _ => ⟨fun _ => 0, Subsingleton.elim _ _⟩
  m := fun a => a.elim0
  m_span := fun _ _ => ⟨fun a => a.elim0, funext fun j => j.elim0⟩
  KR_val := fun _ _ _ h => h.elim
  kum_surj := fun _ _ => ⟨1, by
    rw [map_one]
    exact Multiplicative.toAdd.injective (funext fun a => a.elim0)⟩
  Sexc := ∅
  P := fun r => Additive (ZMod r)ˣ
  Pl := fun _ => Unit
  δ := fun _ _ => AddMonoidHom.id _
  π := fun _ => 0
  δ_inj := fun _ _ _ => Function.injective_id
  exact := fun _ _ _ p => ⟨fun _ => ⟨p, rfl⟩, fun _ => Subsingleton.elim _ _⟩
  q := fun _ j => j.elim0
  qbar := fun _ j => j.elim0
  π_q := fun _ _ j => j.elim0
  qbar_eq := fun _ _ j => j.elim0
  x := fun _ _ a => a.elim0
  rel := fun _ _ _ a => a.elim0
  κ := fun r _ => kappaTriv n r
  κ_surj := fun _ hr _ hd => kappaTriv_surjective hr.1 hd
  inertia := fun _ => ⊤
  inertia_eq := fun _ _ _ => (AddMonoidHom.range_eq_top.2 fun y => ⟨y, rfl⟩).symm
  decomp := fun _ j => j.elim0
  decompBar := fun _ j => j.elim0
  decomp_eq := fun _ _ j => j.elim0
  decompBar_eq := fun _ _ j => j.elim0
  frob_kummer := fun _ _ _ _ _ _ => ⟨(), fun a => a.elim0⟩

/-- Non-vacuity of the final statement: `moving_character_frobenius` applies to the inhabitant
`MovingData.trivial E n`, for every elliptic `E` and `n` (given its other hypotheses). -/
example (E : WeierstrassCurve ℚ) [E.IsElliptic] (hS : SerreThm3) (hE : HasNoCM E)
    (hdetEq : DetTateTwoEqCyclotomic E) (hT : FrobeniusTrace E) (n B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ (MovingData.trivial E n).good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 :=
  let ⟨r, hrS, hgood, hr1, _⟩ := moving_character_frobenius hS hE hdetEq hT
    (MovingData.trivial E n) B S
  ⟨r, hrS, hgood, hr1⟩

end ZInQ.Manuscript.RC.TateWiring

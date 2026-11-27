import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateWiring
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrintsArith

/-!
# Lane RC22 (glue sweep), Tate share: the perfect Kummer pairing (`kum_surj`) PROVED

Lane RC4's moving-character interface (`RC/Moving/Interface.lean`) takes as GLUE field
`MovingSetting.kum_surj` (tex 3559–3563, the perfect Kummer pairing; Guillot, Lemma 1.20 and
Theorem 1.22, `UNVERIFIED` there). Lane RC17 (`RC/TateWiring/Kummer.lean`) restated it over the
genuine Kummer layer (`KummerData.kum`, `KummerData.KR`, `GFinf`) as the field `kum_surj` of
`MovingData`, and flagged it as the next candidate to prove. It is not proved anywhere in the tree;
it is PROVED here (`kum_surj_genuine`) from Mathlib (character modules, infinite Galois theory) and
lane RC17's definitions, with no hypothesis.

`MovingDataK E n` is lane RC17's `MovingData E n` without the field `kum_surj`;
`MovingDataK.toMovingData` fills it with `kum_surj_genuine`. The bridges
`moving_character_genuineK` and `moving_character_ecurve_genuineK` are lane RC17's
`moving_character_genuine` and `moving_character_ecurve_genuine` with both the determinant GLUE and
`kum_surj` removed; `moving_character_ecurve_genuineS` is the form for `E_ℓ` that needs only
Serre's print `SerreThm3` (not the whole bundle `ArithPrints`) and `CMjInteger`.

Lane RC27: `MovingDataK` follows lane RC17's restructured `MovingData` (genuine `a_r = E.LFunction r`
and good primes; the field `cheb` replaced by the GLUE field `frob_kummer`, with the Chebotarev step
PROVED and `tr ρ_T(Fr_r) = a_r` the GLUE hypothesis `FrobeniusTrace`, which the bridges now take).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring
open scoped WeierstrassCurve MatrixGroups

/-- `m / N = 0` in `ℚ/ℤ` iff `N ∣ m` (PROVED). -/
theorem addCircle_coe_div_eq_zero_iff {N : ℕ} (hN : 0 < N) (m : ℤ) :
    ((((m : ℚ) / N : ℚ)) : AddCircle (1 : ℚ)) = 0 ↔ (N : ℤ) ∣ m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_one] at hk
    have h2 : (m : ℚ) = N * k := by
      field_simp at hk
      linarith
    exact_mod_cast h2
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [zsmul_one]
    push_cast
    field_simp

/-- **Duality for `(ℤ/N)^t`** (PROVED, from Mathlib's `CharacterModule`: characters into `ℚ/ℤ`
separate points): if `φ ∉ H`, some `c ∈ (ℤ/N)^t` pairs to zero with every element of `H` but not
with `φ`. -/
theorem exists_pairing_of_not_mem {N t : ℕ} [NeZero N] (H : AddSubgroup (Fin t → ZMod N))
    {φ : Fin t → ZMod N} (hφ : φ ∉ H) :
    ∃ c : Fin t → ZMod N, (∀ x ∈ H, ∑ a, c a * x a = 0) ∧ ∑ a, c a * φ a ≠ 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hne : (QuotientAddGroup.mk φ : (Fin t → ZMod N) ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ch, hch⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let g : (Fin t → ZMod N) →+ AddCircle (1 : ℚ) :=
    (ch : (Fin t → ZMod N) ⧸ H →+ AddCircle (1 : ℚ)).comp (QuotientAddGroup.mk' H)
  have hrep : ∀ a, ∃ B : ℤ, g (Pi.single a 1) = ((((B : ℚ) / N : ℚ)) : AddCircle (1 : ℚ)) := by
    intro a
    obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (g (Pi.single a 1))
    have hN0 : N • g (Pi.single a 1) = 0 := by
      rw [← map_nsmul]
      have : N • (Pi.single a (1 : ZMod N) : Fin t → ZMod N) = 0 := by
        ext i
        simp only [Pi.smul_apply, Pi.single_apply, Pi.zero_apply]
        split_ifs <;> simp
      rw [this, map_zero]
    rw [← hq, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hN0
    obtain ⟨k, hk⟩ := hN0
    refine ⟨k, ?_⟩
    rw [← hq]
    congr 1
    rw [zsmul_one, nsmul_eq_mul] at hk
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    linarith
  choose B hB using hrep
  have hx : ∀ x : Fin t → ZMod N, x = ∑ a, (x a).val • (Pi.single a (1 : ZMod N)) := by
    intro x
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hg : ∀ x, g x =
      (((((∑ a, ((x a).val : ℤ) * B a : ℤ) : ℚ) / N : ℚ)) : AddCircle (1 : ℚ)) := by
    intro x
    conv_lhs => rw [hx x]
    rw [map_sum]
    simp only [map_nsmul, hB, ← AddCircle.coe_nsmul]
    rw [show ((((∑ a, ((x a).val : ℤ) * B a : ℤ) : ℚ) / N : ℚ)) =
        ∑ a, (x a).val • ((B a : ℚ) / N) by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [nsmul_eq_mul]
      ring]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm
  have hcast : ∀ x : Fin t → ZMod N,
      (((∑ a, ((x a).val : ℤ) * B a : ℤ)) : ZMod N) = ∑ a, (B a : ZMod N) * x a := by
    intro x
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ZMod.natCast_zmod_val, mul_comm]
  refine ⟨fun a => (B a : ZMod N), fun x hx' => ?_, ?_⟩
  · have h0 : g x = 0 := by
      change ch (QuotientAddGroup.mk x) = 0
      rw [(QuotientAddGroup.eq_zero_iff x).mpr hx', map_zero]
    rw [hg, addCircle_coe_div_eq_zero_iff hN] at h0
    rw [← hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h0
  · intro h0
    apply hch
    change g φ = 0
    rw [hg, addCircle_coe_div_eq_zero_iff hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast]
    exact h0


/-- **The perfect Kummer pairing over `F_∞ = K(μ_{2^∞})`** (tex 3559–3563: "every assignment of
multipliers that respects the Kummer relations is realized by some `σ₀ ∈ G_{F_∞}`"): for Kummer data
at level `n` (a primitive `2^n`-th root of unity `ζ`, radicands `α_a ∈ K`, roots
`γ_a = α_a^{1/2^n}`), every `φ ∈ (ℤ/2^n)^t` that pairs to zero with all Kummer relations (exponent
vectors `b` with `∏ α_a^{b_a}` a `2^n`-th power in `F_∞`) is the multiplier vector `kum σ` of some
`σ ∈ G_{F_∞}`. Kind: PROVED (no remaining hypothesis). Consumer: the GLUE field `kum_surj` of lane
RC17's `MovingData` (= lane RC4's GLUE field `MovingSetting.kum_surj` for the genuine Kummer layer).
Proof: the multiplier vectors of `G_{F_∞}` form a subgroup `H`; if `φ ∉ H`, duality gives `c` with
`⟨c, H⟩ = 0`, `⟨c, φ⟩ ≠ 0`; then `y = ∏ γ_a^{c_a}` is fixed by `G_{F_∞}`, so `y ∈ F_∞` (infinite
Galois theory, `InfiniteGalois.fixedField_fixingSubgroup`), i.e. `c` is a Kummer relation, and
`⟨c, φ⟩ = 0`, a contradiction. -/
theorem kum_surj_genuine {s : Qbar} {n t : ℕ} (K : KummerData s n t) (φ : Fin t → ZMod (2 ^ n))
    (hφ : ∀ b ∈ K.KR, ∑ a, (b a : ZMod (2 ^ n)) * φ a = 0) :
    ∃ σ : GFinf s, K.kum σ = Multiplicative.ofAdd φ := by
  by_contra hno
  let H : AddSubgroup (Fin t → ZMod (2 ^ n)) :=
    { carrier := {x | ∃ σ : GFinf s, K.kum σ = Multiplicative.ofAdd x}
      zero_mem' := ⟨1, by rw [map_one]; rfl⟩
      add_mem' := by
        rintro x y ⟨σ, hσ⟩ ⟨τ, hτ⟩
        exact ⟨σ * τ, by rw [map_mul, hσ, hτ]; rfl⟩
      neg_mem' := by
        rintro x ⟨σ, hσ⟩
        exact ⟨σ⁻¹, by rw [map_inv, hσ]; rfl⟩ }
  have hφH : φ ∉ H := fun ⟨σ, hσ⟩ => hno ⟨σ, hσ⟩
  obtain ⟨c, hcH, hcφ⟩ := exists_pairing_of_not_mem H hφH
  apply hcφ
  have hb := hφ (fun a => ((c a).val : ℤ)) ?_
  · simpa [ZMod.natCast_zmod_val] using hb
  -- the exponent vector `((c a).val)_a` is a Kummer relation: `y = ∏ γ_a^{c_a}` lies in `F_∞`
  refine ⟨∏ a, K.γ a ^ (c a).val, ?_, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup (Finf s), IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσμ : σ ∈ GalQmu2 := by
      rw [mem_GalQmu2_iff]
      intro k ζ hζ
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ
        (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ ⟨k, hζ⟩))
    have hσs : σ s = s :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ s
        (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _))
    let σ' : GFinf s := ⟨⟨σ, hσμ⟩, mem_GFinf_iff.2 hσs⟩
    have hspec : ∀ a, σ (K.γ a) = K.ζ ^ (K.kumExp σ' a).val * K.γ a := K.kumExp_spec σ'
    have hmem : K.kumExp σ' ∈ H := ⟨σ', rfl⟩
    have hsum := hcH _ hmem
    have hdvd : 2 ^ n ∣ ∑ a, (c a).val * (K.kumExp σ' a).val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using hsum
    obtain ⟨m, hm⟩ := hdvd
    rw [map_prod]
    simp only [map_pow, hspec, mul_pow, Finset.prod_mul_distrib]
    have h1 : ∏ a, (K.ζ ^ (K.kumExp σ' a).val) ^ (c a).val = 1 := by
      simp only [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum]
      have hm' : ∑ a, (K.kumExp σ' a).val * (c a).val = 2 ^ n * m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      rw [hm', pow_mul, K.hζ.pow_eq_one, one_pow]
    rw [h1, one_mul]
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, K.γ_pow]


/-- **Lane RC17's `MovingData E n` without the field `kum_surj`** (tex 3530–3595, 3662–3693): the
remaining fields are lane RC4's other interface fields (kinds and locators as in
`ZInQ.Manuscript.RC.Moving.MovingSetting`), with the Kummer layer, the trace, `a_r` and the good
primes genuine.  Lane RC27: as `MovingData`, no field `ap` (`a_r = E.LFunction r`), no field `good`
(the genuine `GoodPrime E sqrtD Sexc`, with the data field `Sexc`), and the field `cheb` split: the
Chebotarev step is PROVED (`MovingData.exists_frobenius`), `tr ρ_T(Fr_r) = a_r` is the GLUE
`FrobeniusTrace E` (a hypothesis of the statements below) and the power-residue formula is the GLUE
field `frob_kummer`.  Non-vacuity: `MovingDataK.trivial`. -/
structure MovingDataK (E : WeierstrassCurve ℚ) (n : ℕ) where
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
  /-- `GLUE` (tex 3532–3534), as in lane RC4 -/
  cls_gen : ∀ c : Cl, ∃ v : Fin s → ℤ, ∑ j, v j • cls j = c
  m : Fin t → Fin s → ℤ
  m_span : ∀ v : Fin s → ℤ, ∑ j, v j • cls j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  /-- `ELLIOT/GLUE` (tex 3551–3557; Elliot's argument from textbook valuation facts), as in RC4,
  over the genuine Kummer relations -/
  KR_val : ∀ b ∈ kd.KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j
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

attribute [instance] MovingDataK.decAct MovingDataK.clGrp MovingDataK.pGrp

/-- **Lane RC17's `MovingData` from `MovingDataK`**: the field `kum_surj` is filled by the PROVED
`kum_surj_genuine`; every other field is copied. -/
def MovingDataK.toMovingData {E : WeierstrassCurve ℚ} {n : ℕ} (M : MovingDataK E n) :
    MovingData E n :=
  { M with kum_surj := fun φ hφ => kum_surj_genuine M.kd φ hφ }

/-- The good primes of `M : MovingDataK E n` (Lane RC27): the genuine `GoodPrime E M.sqrtD M.Sexc`,
those of `M.toMovingData`. -/
def MovingDataK.good {E : WeierstrassCurve ℚ} {n : ℕ} (M : MovingDataK E n) (r : ℕ) : Prop :=
  GoodPrime E M.sqrtD M.Sexc r

/-- **Non-vacuity of `MovingDataK`** (Lane RC27): lane RC17's inhabitant `MovingData.trivial E n`
without its field `kum_surj`. -/
def MovingDataK.trivial (E : WeierstrassCurve ℚ) (n : ℕ) : MovingDataK E n :=
  { MovingData.trivial E n with }

/-- **Proposition `ex:arith-moving-character` over the genuine Tate image and Kummer layer**
(tex 3500–3702), with `c_E = 16 d + 21` and the genuine `a_r = E.LFunction r` (Lane RC27). Kind:
PROVED from `SerreThm3` (PRINT), `HasNoCM E`, the GLUE `FrobeniusTrace E` (`tr ρ_T(Fr_r) = a_r`,
lane RC17's `Kummer.lean`) and the fields of `MovingDataK` (lane RC4's remaining GLUE/PRINT fields
other than the four Kummer fields and `kum_surj`, with the power-residue field `frob_kummer`).
Consumer: lane RC17's `moving_character_genuine` (hypotheses `hdetEq` and the field `kum_surj`
discharged by `detTateTwoEqCyclotomic_holds` and `kum_surj_genuine`). -/
theorem moving_character_genuineK {E : WeierstrassCurve ℚ} [E.IsElliptic] (hS : SerreThm3)
    (hE : HasNoCM E) (hT : FrobeniusTrace E) {n : ℕ} (M : MovingDataK E n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 + E.LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 - E.LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 + E.LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 - E.LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ E.LFunction r - 2 * χ :=
  moving_character_genuine_of hS hE hT M.toMovingData B S

/-- **The same for `E_ℓ`** (tex 3500–3702), with the genuine `a_r = (E_ℓ).LFunction r`. Kind:
PROVED from `ArithPrints` (only the field `serre` is used; PRINT), `CMjInteger` (GLUE), the GLUE
`FrobeniusTrace (E_ℓ)` and the fields of `MovingDataK`. Consumer: lane RC17's
`moving_character_ecurve_genuine` (hypotheses `H : GlueTate` and the field `kum_surj` discharged by
`glueTate` and `kum_surj_genuine`). -/
theorem moving_character_ecurve_genuineK (P : ArithPrints) (hcm : CMjInteger) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingDataK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  moving_character_ecurve_genuine_of P hcm hℓ hT M.toMovingData B S


/-- **The fixed Tate image of `E_ℓ` from Serre's print alone** (tex 3597–3605): lane RC17's
`tateImage` for `Ecurve ℓ`, with the determinant GLUE discharged and non-CM from `CMjInteger`.
Hypotheses: `SerreThm3` (PRINT) and `CMjInteger` (GLUE). Definitionally `tateImageEcurveOf P hcm hℓ`
when `hS = P.serre`. -/
def tateImageEcurveS (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) : TateImage :=
  @tateImageOf (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of hcm hℓ)

/-- **Proposition `ex:arith-moving-character` for `E_ℓ`** (tex 3500–3702), over the genuine Tate
image and Kummer layer, with the genuine `a_r = (E_ℓ).LFunction r` (`= r + 1 − |Ẽ_ℓ(𝔽_r)|` at
`r ∤ 6ℓ`, lane RC3's `KSplit.LFunction_curve_apply_prime`). Kind: PROVED from `SerreThm3` (PRINT),
`CMjInteger` (GLUE), the GLUE `FrobeniusTrace (E_ℓ)` (`tr ρ_T(Fr_r) = a_r`, Lane RC27) and the
fields of `MovingDataK` (lane RC4's remaining interface fields). Consumer: lane RC17's
`moving_character_ecurve_genuine` (hypotheses `P : ArithPrints` (only `P.serre` used),
`H : GlueTate` and the field `kum_surj` replaced/discharged by `SerreThm3`, `glueTate`,
`kum_surj_genuine`). -/
theorem moving_character_ecurve_genuineS (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingDataK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  @moving_character_genuineK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of hcm hℓ) hT n M B S

/-- **Lane RC4's `MovingSetting` over the genuine Tate image of `E_ℓ` and the genuine Kummer
layer, from `MovingDataK`** (tex 3530–3595, 3662–3693): lane RC17's `MovingData.toMovingSetting`
applied to `MovingDataK.toMovingData`; the fields `GF_index`, `HL_le`, `kum_of_mem_HL`,
`mem_HL_of_kum`, `kum_surj` are PROVED (lane RC17, `kum_surj_genuine`), `ap r = (E_ℓ).LFunction r`
and `cheb` is derived from the PROVED Chebotarev step, the GLUE `FrobeniusTrace (E_ℓ)` and the
field `frob_kummer` (Lane RC27); the Tate image needs only `SerreThm3` (PRINT) and `CMjInteger`
(GLUE). For consumers of lane RC4's interface. -/
def movingSettingEcurveS (hS : SerreThm3) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) {n : ℕ}
    (M : MovingDataK (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) :
    MovingSetting (tateImageEcurveS hS hcm hℓ) n :=
  @movingSettingOf (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hS
    (ecurve_hasNoCM_of hcm hℓ) hT n M.toMovingData

end ZInQ.Manuscript.RC.GlueSweep.Tate

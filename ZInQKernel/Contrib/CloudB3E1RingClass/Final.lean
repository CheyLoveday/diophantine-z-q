import ZInQKernel.Contrib.CloudB3E1RingClass.RelProof

/-!
# The genuine moving data, constructed

Manuscript `diophantine_zq.tex`, tex 3528–3595, 3662–3693.

`GenuineMovingFinal E n s C` lists what is still assumed for a genuine `MovingDataK` over
`K = ℚ(s)`, with setup `C`. Everything else is constructed:
* the relation basis `m` (`exists_relation_basis`);
* the integral generators `β_a` of `J_{m^{(a)}} = ∏_j 𝔭_j^{m⁺} 𝔭̄_j^{m⁻}`;
* the radicands `α_a = σβ_a/β_a`, the Kummer data, `Pl := kummerPlaces`, `x := kummerX`,
  `κ := kummerKappa`, and `δ := kummerDelta` (lane E2's connecting map at the split pair under `v`).

The fields of `GenuineMovingFinal`:
* the data `D` (`s² = D`), `act`, `over2N`, `Sexc`;
* facts about `K` and the setup: `finrank ℚ K = 2`, `𝒪_K^× = {±1}`, the `p_j` distinct and in `Sexc`,
  `𝔭_j ≠ 𝔭̄_j`, the classes `[𝔭_j]` generating `Cl(K)`, the active primes odd, the discriminant
  primes in `Sexc`, and `placeR_over`;
* **`inertia_eq`**, the one remaining open input (tex 3679–3681).

`GenuineMovingFinal.toInputs` builds `GenuineMovingInputs`, and every other field is PROVED:
`cls_gen`, `m_span`, `KR_val`, `δ_inj`, `exact`, `rel`, `κ_surj`, `frob_kummer`.
`moving_character_final` is the RC0 conclusion from it.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors Pointwise

variable {s : Qbar} {S : ℕ}

/-! ### The constructed data -/

/-- The number of basic relations. Kind: definition. -/
def relT (C : RingClassSetup (quadField s) S) : ℕ :=
  (exists_relation_basis (setupCls C)).choose

/-- **The relation basis** `m^{(a)}` (tex 3536–3538). Kind: definition. -/
def relM (C : RingClassSetup (quadField s) S) : Fin (relT C) → Fin S → ℤ :=
  (exists_relation_basis (setupCls C)).choose_spec.choose

theorem relM_rel (C : RingClassSetup (quadField s) S) (a : Fin (relT C)) :
    ∑ j, relM C a j • setupCls C j = 0 :=
  (exists_relation_basis (setupCls C)).choose_spec.choose_spec.1 a

theorem relM_span (C : RingClassSetup (quadField s) S) :
    ∀ v : Fin S → ℤ, ∑ j, v j • setupCls C j = 0 → ∃ b : Fin (relT C) → ℤ, v = ∑ a, b a • relM C a :=
  (exists_relation_basis (setupCls C)).choose_spec.choose_spec.2

/-- **The integral generators** `β_a` of `J_{m^{(a)}}` (tex 3536–3542). Kind: definition. -/
def relβ (C : RingClassSetup (quadField s) S) (a : Fin (relT C)) : 𝓞 (quadField s) :=
  (exists_integral_generator C (relM C a) (relM_rel C a)).choose

theorem relβ_spec (C : RingClassSetup (quadField s) S) (a : Fin (relT C)) :
    relIdeal C (relM C a) = Ideal.span {relβ C a} :=
  (exists_integral_generator C (relM C a) (relM_rel C a)).choose_spec

/-- The non-trivial automorphism of `K`. Kind: definition. -/
def conjσ (hK : Module.finrank ℚ (quadField s) = 2) : quadField s ≃ₐ[ℚ] quadField s :=
  (exists_conj hK).choose

theorem conjσ_spec (hK : Module.finrank ℚ (quadField s) = 2) :
    ∀ τ : quadField s ≃ₐ[ℚ] quadField s, τ ≠ 1 → τ = conjσ hK :=
  (exists_conj hK).choose_spec.2

/-- **The radicands** `α_a = σβ_a/β_a` (tex 3540). Kind: definition. -/
def radicand (hK : Module.finrank ℚ (quadField s) = 2) (C : RingClassSetup (quadField s) S)
    (a : Fin (relT C)) : quadField s :=
  ((conjσ hK • relβ C a : 𝓞 (quadField s)) : quadField s) / (relβ C a : quadField s)

theorem relβ_ne_zero (C : RingClassSetup (quadField s) S) (a : Fin (relT C)) :
    (relβ C a : quadField s) ≠ 0 := by
  intro h
  have hb : relβ C a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 (quadField s)) (quadField s))
    (h.trans (map_zero _).symm)
  have h0 : relIdeal C (relM C a) = ⊥ := by
    rw [relβ_spec, hb, Ideal.span_singleton_eq_bot.mpr rfl]
  exact nonZeroDivisors.coe_ne_zero (relIdeal0 C (relM C a)) ((coe_relIdeal0 C _).trans h0)

theorem radicand_ne_zero (hK : Module.finrank ℚ (quadField s) = 2)
    (C : RingClassSetup (quadField s) S) (a : Fin (relT C)) : radicand hK C a ≠ 0 :=
  div_ne_zero ((map_ne_zero (conjσ hK)).mpr (relβ_ne_zero C a)) (relβ_ne_zero C a)

/-- **The constructed Kummer data** (tex 3540–3542). Kind: definition. -/
def finalKd (hK : Module.finrank ℚ (quadField s) = 2) (C : RingClassSetup (quadField s) S)
    (n : ℕ) : KummerData s n (relT C) where
  ζ := (exists_primitive (2 ^ n) (pow_ne_zero _ two_ne_zero)).choose
  hζ := (exists_primitive (2 ^ n) (pow_ne_zero _ two_ne_zero)).choose_spec
  α a := ((radicand hK C a : quadField s) : Qbar)
  α_mem a := (radicand hK C a).2
  γ a := (IsAlgClosed.exists_pow_nat_eq ((radicand hK C a : quadField s) : Qbar)
    (pow_pos two_pos n)).choose
  γ_pow a := (IsAlgClosed.exists_pow_nat_eq ((radicand hK C a : quadField s) : Qbar)
    (pow_pos two_pos n)).choose_spec
  γ_ne a h := by
    have h0 := (IsAlgClosed.exists_pow_nat_eq ((radicand hK C a : quadField s) : Qbar)
      (pow_pos two_pos n)).choose_spec
    rw [h, zero_pow (pow_ne_zero _ two_ne_zero)] at h0
    exact radicand_ne_zero hK C a (Subtype.ext h0.symm)

/-! ### The valuations of the radicands -/

/-- `v_{𝔭_j}(α_a) = m_j^{(a)}`. Kind: PROVED. -/
theorem valuation_radicand_𝔭 (hK : Module.finrank ℚ (quadField s) = 2)
    (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p)
    (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) (j : Fin S) (a : Fin (relT C)) :
    (C.𝔭 j).valuation (quadField s) (radicand hK C a) = WithZero.exp (relM C a j) := by
  have hsw : (C.𝔭 j).asIdeal = conjσ hK • (C.𝔭bar j).asIdeal :=
    (conj_smul_split hK (conjσ_spec hK) (C.p_prime j) (hne j).symm
      (by rw [mul_comm]; exact C.𝔭_mul j)).symm
  obtain ⟨h1, -⟩ := valuation_relGenerator_𝔭 C hinj hne (relM C a) (relβ C a) (relβ_spec C a) j
  obtain ⟨-, h2⟩ := valuation_relGenerator_𝔭 C hinj hne (relM C a) (relβ C a) (relβ_spec C a) j
  rw [radicand, map_div₀]
  change (C.𝔭 j).valuation (quadField s) (conjσ hK (relβ C a : quadField s)) / _ = _
  rw [valuation_conj (conjσ hK) hsw]
  change (C.𝔭bar j).valuation (quadField s) (algebraMap _ _ (relβ C a)) /
    (C.𝔭 j).valuation (quadField s) (algebraMap _ _ (relβ C a)) = _
  rw [h1, h2, ← WithZero.exp_sub]
  congr 1
  omega

/-- The radicands are units away from `Sexc`. Kind: PROVED. -/
theorem valuation_radicand_away (hK : Module.finrank ℚ (quadField s) = 2)
    (C : RingClassSetup (quadField s) S) (Sexc : Finset ℕ) (p_mem : ∀ j, C.p j ∈ Sexc)
    (a : Fin (relT C)) (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ) (hq : q.Prime)
    (hqS : q ∉ Sexc) (h𝔯 : ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal) :
    𝔯.valuation (quadField s) (radicand hK C a) = 1 := by
  have hqp : ∀ j, q ≠ C.p j := fun j h => hqS (h ▸ p_mem j)
  have hc : ((q : ℤ) : 𝓞 (quadField s)) ∈ (conjPrime (conjσ hK) 𝔯).asIdeal :=
    (intCast_mem_conjPrime (conjσ hK) 𝔯 q).mpr h𝔯
  rw [radicand, map_div₀]
  change 𝔯.valuation (quadField s) (conjσ hK (relβ C a : quadField s)) / _ = _
  rw [valuation_conj (conjσ hK) (smul_conjPrime (conjσ hK) 𝔯)]
  change (conjPrime (conjσ hK) 𝔯).valuation (quadField s) (algebraMap _ _ (relβ C a)) /
    𝔯.valuation (quadField s) (algebraMap _ _ (relβ C a)) = _
  rw [valuation_relGenerator_away C _ _ (relβ_spec C a) hq hqp hc,
    valuation_relGenerator_away C _ _ (relβ_spec C a) hq hqp h𝔯, div_one]

/-! ### The remaining inputs and the construction -/

/-- **What is still assumed for the genuine moving data** (tex 3528–3595, 3662–3693): facts about
`K` and the setup, and the open `inertia_eq`. Kind: definition (of the structure). -/
structure GenuineMovingFinal (E : WeierstrassCurve ℚ) (n : ℕ) (s : Qbar) {S : ℕ}
    (C : RingClassSetup (quadField s) S) where
  hK : Module.finrank ℚ (quadField s) = 2
  hunits : ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1
  D : ℚ
  sqrtD_sq : s ^ 2 = algebraMap ℚ Qbar D
  act : Fin S → Prop
  [decAct : DecidablePred act]
  over2N : Fin S → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  hinj : Function.Injective C.p
  hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j
  hgen : Subgroup.closure (Set.range fun j =>
    ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤
  h2 : ∀ j, act j → (2 : 𝓞 (quadField s)) ∉ (C.𝔭 j).asIdeal
  Sexc : Finset ℕ
  p_mem : ∀ j, C.p j ∈ Sexc
  hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc
  placeR_over : ∀ r, GoodPrime E s Sexc r → ((r : ℤ) : 𝓞 (quadField s)) ∈ (C.placeR r).asIdeal
  /-- open: the genuine inertia group is the range of `δ` (tex 3679–3681) -/
  inertia_eq : ∀ r, GoodPrime E s Sexc r → ∀ v,
    setupInertia C r = (kummerDelta hK E Sexc hSdisc C r v).range

attribute [instance] GenuineMovingFinal.decAct

variable {E : WeierstrassCurve ℚ} {n : ℕ} {C : RingClassSetup (quadField s) S}

/-- **The genuine `MovingInputs`** (tex 3528–3595, 3662–3693): everything constructed, every field
but `inertia_eq` PROVED. Kind: definition. -/
def GenuineMovingFinal.toInputs (I : GenuineMovingFinal E n s C) : GenuineMovingInputs E n C where
  D := I.D
  sqrtD := s
  sqrtD_sq := I.sqrtD_sq
  t := relT C
  kd := finalKd I.hK C n
  act := I.act
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  cls_gen := clsGen_of_closure C I.hgen
  m := relM C
  m_span := relM_span C
  KR_val := by
    intro b hb j hj
    have h := krVal_genuine s (finalKd I.hK C n) I.act (fun a j => -relM C a j) C.𝔭 I.h2
      (fun j _ a => by
        rw [neg_neg]
        exact valuation_radicand_𝔭 I.hK C I.hinj I.hne j a) b hb j hj
    simp only [mul_neg, Finset.sum_neg_distrib, dvd_neg] at h
    exact h
  Sexc := I.Sexc
  p_mem := I.p_mem
  placeR_over := I.placeR_over
  Pl := kummerPlaces
  δ := kummerDelta I.hK E I.Sexc I.hSdisc C
  δ_inj := kummerDelta_injective I.hK I.hSdisc C I.hunits
  exact := kummerDelta_exact I.hK I.hSdisc C
  x _ v a := kummerX ((finalKd I.hK C n).α a) v
  rel r hgood v a := rel_genuine I.hK C (conjσ_spec I.hK) (relM C a) (relβ C a) (relβ_spec C a)
    E I.Sexc I.hSdisc I.p_mem hgood v
  κ _ v := kummerKappa n (finalKd I.hK C n).ζ v
  κ_surj := kappa_surj_genuine (finalKd I.hK C n) I.Sexc
  inertia_eq := I.inertia_eq
  frob_kummer := frob_kummer_genuine (finalKd I.hK C n) I.Sexc
    (hαunit_of_support s (finalKd I.hK C n) I.Sexc
      (fun a 𝔯 q hq hqS h𝔯 => valuation_radicand_away I.hK C I.Sexc I.p_mem a 𝔯 q hq hqS h𝔯))

open ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.Moving in
/-- **The moving character on the genuine groups** (tex 2729–2737, 3500–3506, 4258–4268):
`moving_character_genuine` for `GenuineMovingFinal.toInputs`. The only open input is
`inertia_eq`. Kind: PROVED. -/
theorem moving_character_final {ℓ : ℕ}
    (I : GenuineMovingFinal (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n s C)
    (hS : ZInQ.Manuscript.RC.PrintsArith.SerreThm3) (hcm : ZInQ.Manuscript.RC.PrintsArith.CMjInteger)
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 (quadField s))))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (T : Finset ℕ) :
    ∃ r : ℕ, r ∉ T ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) s I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : ZInQ.Manuscript.RC.SelmerComplex.GKS (quadField s) (C.Sr r) →*
          Multiplicative (ZMod (2 ^ n)),
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion (quadField s)),
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.placeR r) σ) =
            Multiplicative.ofAdd y) ∧
        (∀ v ∈ P, ∀ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) v,
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭 j) φ) =
              Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭bar j) φ) =
              Multiplicative.ofAdd (-1)) ∧
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
  moving_character_genuine I.toInputs hS hcm hℓ hT P hP B T

end ZInQ.Contrib.CloudB3E1RingClass

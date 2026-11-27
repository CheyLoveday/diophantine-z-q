import ZInQKernel.Contrib.CloudB3E1RingClass.SplitAtGood
import ZInQKernel.Contrib.CloudB3E1RingClass.Assembly
import ZInQKernel.Contrib.CloudB3E2Norm.RingClassDelta

/-!
# The connecting map `δ` on the genuine places

Manuscript `diophantine_zq.tex`, tex 3566–3575: "for split `r`, `δ : 𝐅_r^× → Gal(H_r/K)` …".

Lane E2's `deltaR` (`CloudB3E2Norm/RingClassDelta.lean`) is the connecting map at a split pair
`(𝔯, 𝔯̄)` over `r`. This file places it on the genuine places `kummerPlaces r`. At a good prime `r`
(with the primes of the discriminant excluded), the prime `𝔯 = v ∩ 𝒪_K` under the Frobenius place `v`
is split (`exists_split_of_good`), which gives the pair `splitPairOf`.
* `kummerDelta` is `deltaR` at that pair, and `0` at non-good `r`;
* `kummerDelta_injective` is `δ_inj` (given `𝒪_K^× = {±1}`);
* `kummerDelta_exact` is `exact`.

`GenuineMovingCoreδ` is `GenuineMovingCore` with `δ := kummerDelta`; its `δ_inj` and `exact` are
PROVED (`toCore`). Its remaining open fields are `rel` and `inertia_eq`, stated for `kummerDelta`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3E2.RingClassDelta
open scoped nonZeroDivisors

variable {s : Qbar}

/-- **The split pair at a Frobenius place over a good prime** (tex 3566): `(𝔯, 𝔯̄)` with
`𝔯 = v ∩ 𝒪_K`. Kind: definition. -/
def splitPairOf (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} {r : ℕ} (hgood : GoodPrime E s Sexc r)
    (hdisc : ¬ (r : ℤ) ∣ discr (quadField s)) (v : kummerPlaces r) :
    SplitPair (quadField s) (max r 1) :=
  haveI : Fact r.Prime := ⟨hgood.1⟩
  let h := exists_split_of_good s hK hgood hdisc v
  { P := placeRestrict s v
    Q := h.choose
    ne := h.choose_spec.1.symm
    span_eq := by
      rw [max_eq_left hgood.1.one_lt.le, ← Int.cast_natCast]
      exact h.choose_spec.2 }

theorem splitPairOf_P (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} {r : ℕ} (hgood : GoodPrime E s Sexc r)
    (hdisc : ¬ (r : ℤ) ∣ discr (quadField s)) (v : kummerPlaces r) :
    haveI : Fact r.Prime := ⟨hgood.1⟩
    (splitPairOf hK hgood hdisc v).P = placeRestrict s v := rfl

theorem max_prime_of_good {E : WeierstrassCurve ℚ} {Sexc : Finset ℕ} {r : ℕ}
    (hgood : GoodPrime E s Sexc r) : (max r 1).Prime := by
  rw [max_eq_left hgood.1.one_lt.le]; exact hgood.1

theorem not_dvd_discr_of_good {E : WeierstrassCurve ℚ} {Sexc : Finset ℕ}
    (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc) {r : ℕ}
    (hgood : GoodPrime E s Sexc r) : ¬ (r : ℤ) ∣ discr (quadField s) :=
  fun h => hgood.2.2.2.1 (hSdisc r hgood.1 h)

/-- **The interface's `δ r v` on the genuine places** (tex 3566–3575): lane E2's `deltaR` at the
split pair `splitPairOf` for good `r`, and `0` otherwise. Kind: definition. -/
def kummerDelta (hK : Module.finrank ℚ (quadField s) = 2) (E : WeierstrassCurve ℚ)
    (Sexc : Finset ℕ) (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    {S : ℕ} (C : RingClassSetup (quadField s) S) (r : ℕ) (v : kummerPlaces r) :
    Additive (ZMod r)ˣ →+ Additive (setupGal C r) := by
  classical
  exact if hgood : GoodPrime E s Sexc r then
    deltaR (max_prime_of_good hgood) (splitPairOf hK hgood (not_dvd_discr_of_good hSdisc hgood) v)
      hK (C.Sr r) (C.hSr r)
  else 0

theorem kummerDelta_of_good (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    {S : ℕ} (C : RingClassSetup (quadField s) S) {r : ℕ} (hgood : GoodPrime E s Sexc r)
    (v : kummerPlaces r) :
    kummerDelta hK E Sexc hSdisc C r v =
      deltaR (max_prime_of_good hgood)
        (splitPairOf hK hgood (not_dvd_discr_of_good hSdisc hgood) v) hK (C.Sr r) (C.hSr r) := by
  classical
  rw [kummerDelta, dite_eq_left_of_eq_true (eq_true hgood)]

/-- **`δ_inj`** on the genuine places (given `𝒪_K^× = {±1}`). Kind: PROVED. -/
theorem kummerDelta_injective (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    {S : ℕ} (C : RingClassSetup (quadField s) S)
    (hunits : ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1) :
    ∀ r, GoodPrime E s Sexc r → ∀ v, Function.Injective (kummerDelta hK E Sexc hSdisc C r v) := by
  intro r hgood v
  rw [kummerDelta_of_good hK hSdisc C hgood v]
  exact deltaR_injective (max_prime_of_good hgood)
    (splitPairOf hK hgood (not_dvd_discr_of_good hSdisc hgood) v) hK (C.Sr r) (C.hSr r) hunits

/-- **`exact`** on the genuine places. Kind: PROVED. -/
theorem kummerDelta_exact (hK : Module.finrank ℚ (quadField s) = 2) {E : WeierstrassCurve ℚ}
    {Sexc : Finset ℕ} (hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc)
    {S : ℕ} (C : RingClassSetup (quadField s) S) :
    ∀ r, GoodPrime E s Sexc r → ∀ v, ∀ p : Additive (setupGal C r),
      setupPi C r p = 0 ↔ ∃ y, kummerDelta hK E Sexc hSdisc C r v y = p := by
  intro r hgood v p
  rw [kummerDelta_of_good hK hSdisc C hgood v]
  exact deltaR_exact_setup C (max_prime_of_good hgood)
    (splitPairOf hK hgood (not_dvd_discr_of_good hSdisc hgood) v) hK p

/-- **The core inputs with the genuine `δ`** (tex 3530–3595, 3662–3693): `GenuineMovingCore`
without `δ`, `δ_inj`, `exact`. In their place it takes `finrank ℚ K = 2`, `𝒪_K^× = {±1}` and the
exclusion of the discriminant primes. `rel` and `inertia_eq` are stated for `kummerDelta`.
Kind: definition (of the structure). -/
structure GenuineMovingCoreδ (E : WeierstrassCurve ℚ) (n : ℕ) (s : Qbar) {S : ℕ}
    (C : RingClassSetup (quadField s) S) where
  hK : Module.finrank ℚ (quadField s) = 2
  hunits : ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1
  D : ℚ
  sqrtD_sq : s ^ 2 = algebraMap ℚ Qbar D
  t : ℕ
  kd : KummerData s n t
  act : Fin S → Prop
  [decAct : DecidablePred act]
  over2N : Fin S → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  hgen : Subgroup.closure (Set.range fun j =>
    ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤
  m : Fin t → Fin S → ℤ
  m_span : ∀ v : Fin S → ℤ, ∑ j, v j • setupCls C j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  h2 : ∀ j, act j → (2 : 𝓞 (quadField s)) ∉ (C.𝔭 j).asIdeal
  hval : ∀ j, act j → ∀ a,
    (C.𝔭 j).valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = WithZero.exp (-(m a j))
  Sexc : Finset ℕ
  p_mem : ∀ j, C.p j ∈ Sexc
  hSdisc : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ discr (quadField s) → q ∈ Sexc
  hsupp : ∀ a (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ), q.Prime → q ∉ Sexc →
    ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal →
      𝔯.valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = 1
  placeR_over : ∀ r, GoodPrime E s Sexc r → ((r : ℤ) : 𝓞 (quadField s)) ∈ (C.placeR r).asIdeal
  /-- open: the principal relations (tex 3576–3579) -/
  rel : ∀ r, GoodPrime E s Sexc r → ∀ v a,
    ∑ j, m a j • setupQ C r j + kummerDelta hK E Sexc hSdisc C r v (kummerX (kd.α a) v) = 0
  /-- open: the genuine inertia group is the range of `δ` (tex 3679–3681) -/
  inertia_eq : ∀ r, GoodPrime E s Sexc r → ∀ v,
    setupInertia C r = (kummerDelta hK E Sexc hSdisc C r v).range

attribute [instance] GenuineMovingCoreδ.decAct

variable {E : WeierstrassCurve ℚ} {n : ℕ} {S : ℕ} {C : RingClassSetup (quadField s) S}

/-- **`GenuineMovingCore` from the core with the genuine `δ`**: `δ := kummerDelta`, with `δ_inj`
and `exact` PROVED. Kind: definition. -/
def GenuineMovingCoreδ.toCore (I : GenuineMovingCoreδ E n s C) : GenuineMovingCore E n s C where
  D := I.D
  sqrtD_sq := I.sqrtD_sq
  t := I.t
  kd := I.kd
  act := I.act
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  hgen := I.hgen
  m := I.m
  m_span := I.m_span
  h2 := I.h2
  hval := I.hval
  Sexc := I.Sexc
  p_mem := I.p_mem
  hsupp := I.hsupp
  placeR_over := I.placeR_over
  δ := kummerDelta I.hK E I.Sexc I.hSdisc C
  δ_inj := kummerDelta_injective I.hK I.hSdisc C I.hunits
  exact := kummerDelta_exact I.hK I.hSdisc C
  rel := I.rel
  inertia_eq := I.inertia_eq

end ZInQ.Contrib.CloudB3E1RingClass

import ZInQKernel.Contrib.OneProof.RC.PicardFibers.IdeleClass
import Mathlib.RingTheory.Ideal.Int

/-! Group the finite ideles by rational primes, on-the-spot (c), tex 9157–9166. -/

noncomputable section

open IsDedekindDomain
open scoped NumberField RestrictedProduct

namespace ZInQ.Manuscript.RC.PicardFibers

section Regroup

variable {I J : Type*} (f : I → J) (G : I → Type*) [∀ i, Monoid (G i)]
  (U : ∀ i, Submonoid (G i))

/-- The integral subgroup condition in a block: all the coordinates over
that rational prime are integral. -/
def blockIntegral (j : J) : Submonoid (∀ i : {i : I // f i = j}, G i.val) where
  carrier := {a | ∀ i, a i ∈ U i.val}
  one_mem' := fun i => (U i.val).one_mem
  mul_mem' ha hb i := (U i.val).mul_mem (ha i) (hb i)

/-- Regrouping preserves the restricted product when each block is finite. -/
def regroup (hf : ∀ j : J, (f ⁻¹' ({j} : Set J)).Finite) :
    (Πʳ i : I, [G i, U i]) ≃*
      (Πʳ j : J, [(∀ i : {i : I // f i = j}, G i.val), blockIntegral f G U j]) where
  toFun a := ⟨fun _ i => a i.val, by
    rw [Filter.eventually_cofinite]
    exact ((Filter.eventually_cofinite.mp a.prop).image f).subset <| by
      intro j hj
      change ¬ ∀ i : {i : I // f i = j}, a i.val ∈ U i.val at hj
      push Not at hj
      obtain ⟨i, hi⟩ := hj
      exact ⟨i.val, hi, i.prop⟩⟩
  invFun b := ⟨fun i => b (f i) ⟨i, rfl⟩, by
    rw [Filter.eventually_cofinite]
    have hb := Filter.eventually_cofinite.mp b.prop
    exact (hb.preimage' (fun j _ => hf j)).subset <| by
      intro i hi hj
      exact hi (hj ⟨i, rfl⟩)⟩
  left_inv _ := rfl
  right_inv b := by
    ext j i
    obtain ⟨i, rfl⟩ := i
    rfl
  map_mul' _ _ := rfl

end Regroup

variable (F : Type*) [Field F] [NumberField F]

/-- A finite place of a number field lies above the rational prime obtained
by contracting its prime ideal to the integers. -/
def rationalPrimeUnder : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum ℤ :=
  HeightOneSpectrum.under ℤ

/-- There are finitely many places above each rational prime. -/
theorem rationalPrimeUnder_finite (p : HeightOneSpectrum ℤ) :
    (rationalPrimeUnder F ⁻¹' ({p} : Set (HeightOneSpectrum ℤ))).Finite := by
  let e : HeightOneSpectrum (𝓞 F) ↪ Ideal (𝓞 F) :=
    ⟨HeightOneSpectrum.asIdeal, fun _ _ h => HeightOneSpectrum.ext_iff.mpr h⟩
  exact ((IsDedekindDomain.primesOver_finite (B := 𝓞 F) p.asIdeal).preimage_embedding e).subset
    (fun v hv => ⟨v.isPrime, (Ideal.liesOver_iff _ _).mpr (congrArg
      HeightOneSpectrum.asIdeal (show rationalPrimeUnder F v = p from hv)).symm⟩)

/-- The local unit group at a rational prime is the product over all
completions above it (two factors at a split prime). -/
abbrev GroupedLocalUnits (p : HeightOneSpectrum ℤ) :=
  ∀ v : {v : HeightOneSpectrum (𝓞 F) // rationalPrimeUnder F v = p},
    (v.val.adicCompletion F)ˣ

/-- The integral condition in the restricted product of these blocks. -/
def groupedIntegral (p : HeightOneSpectrum ℤ) : Submonoid (GroupedLocalUnits F p) :=
  blockIntegral (rationalPrimeUnder F) (fun v => (v.adicCompletion F)ˣ)
    (fun v => (Submonoid.ofClass (v.adicCompletionIntegers F)).units.toSubmonoid) p

/-- The rational-prime-indexed restricted product of local unit groups. -/
abbrev GroupedIdeles :=
  Πʳ p : HeightOneSpectrum ℤ, [GroupedLocalUnits F p, groupedIntegral F p]

/-- Tex 9157–9166: the finite ideles are the same restricted product with
the completions grouped by rational prime. -/
def groupIdeles : (FiniteAdeleRing (𝓞 F) F)ˣ ≃* GroupedIdeles F :=
  (RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)).trans
    (regroup (rationalPrimeUnder F) _ _ (rationalPrimeUnder_finite F))

theorem groupIdeles_apply (a : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (p : HeightOneSpectrum ℤ) (v : {v : HeightOneSpectrum (𝓞 F) // rationalPrimeUnder F v = p}) :
    ((groupIdeles F a p v : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) = a.val v.val :=
  rfl


set_option maxHeartbeats 800000 in
/-- The class-map kernel before the diagonal quotient is the group of
everywhere integral blocks. -/
theorem mem_ker_ideleToIdeal_iff_grouped (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    a ∈ (ideleToIdeal (R := 𝓞 F) (K := F)).ker ↔
      ∀ p : HeightOneSpectrum ℤ, groupIdeles F a p ∈ groupedIntegral F p := by
  rw [mem_ker_ideleToIdeal]
  constructor
  · intro h p v
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [groupIdeles_apply]
    exact h v.val
  · intro h v
    let w : {w : HeightOneSpectrum (𝓞 F) // rationalPrimeUnder F w = rationalPrimeUnder F v} :=
      ⟨v, rfl⟩
    have hv : groupIdeles F a (rationalPrimeUnder F v) w ∈ (v.adicCompletionIntegers F).units :=
      h (rationalPrimeUnder F v) w
    have he := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hv
    rw [groupIdeles_apply] at he
    exact he

variable {F}

/-- A rational prime in the quaternion index convention defines a
height-one prime of the integers. -/
def rationalPrime (p : {p : ℕ // p.Prime}) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p.val : ℤ)}
  isPrime := Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr p.prop.ne_zero) |>.mpr
    (Nat.prime_iff_prime_int.mp p.prop)
  ne_bot := fun h => p.prop.ne_zero
    (Int.natCast_eq_zero.mp (Ideal.span_singleton_eq_bot.mp h))

/-- The two rational prime indexing conventions agree. -/
def rationalPrimeEquiv : {p : ℕ // p.Prime} ≃ HeightOneSpectrum ℤ where
  toFun := rationalPrime
  invFun p := ⟨p.asIdeal.absNorm, by
    let : p.asIdeal.IsPrime := p.isPrime
    let : NeZero p.asIdeal := ⟨p.ne_bot⟩
    simpa [Ideal.under_def] using Nat.absNorm_under_prime p.asIdeal⟩
  left_inv p := Subtype.ext (by simp [rationalPrime, Ideal.absNorm_span_singleton])
  right_inv p := HeightOneSpectrum.ext_iff.mpr (Int.ideal_span_absNorm_eq_self p.asIdeal)

end ZInQ.Manuscript.RC.PicardFibers

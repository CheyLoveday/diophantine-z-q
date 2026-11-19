import ZInQKernel.Contrib.CloudB3E1RingClass.CompanionField
import ZInQKernel.Contrib.CloudB3E1RingClass.SetupSr
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPinBinding

/-!
# The curve-specific moving data for the final companion and an admissible family

Manuscript `diophantine_zq.tex`, tex 2595–2613, 2674–2694, 2716–2721, 3500–3702, 4255–4280.

The data: `E = E_ℓ`, the final companion `k = D.kfin` of the actual `RCData`, `K = ℚ(√k) ⊂ ℚ̄`,
and an admissible final family `F` (`F.Admissible D.S D.kfin`). They are read as follows.
* `RCSteps.companion` (tex 2595–2603, 2720–2721; under `¬ D.OddEmptyUnit`):
  `k < 0` squarefree, `k ≠ −1, −3`, `k ≡ 1 (mod 4)`, the primes of `k` in `D.S`, and `k` a unit
  square at every prime of `2N`. So `K` is imaginary quadratic with `𝒪_K^× = {±1}`, and every
  `p ∣ 2N` splits in `K` (`splittingCriterion_proof`).
* `Family.Admissible` (tex 2678–2680, 4234–4237): every `q ∈ Q` is an odd prime outside `D.S` with
  `(k/q) = 1`, so `q ∤ k` and `q` splits in `K`.
* **`hS2N`** (named hypothesis, not recorded in `RCData`): every prime of `2N` lies in the fixed
  support `D.S`. This is the docstring of `Family.Admissible` ("the fixed support `S` (which
  contains the primes of `2N`, of `h_*` and of `k`)", tex 2678–2680, 4234–4237). It keeps the
  primes of `Q` away from `2N`, and it forces `N ≠ 0` (`D.S` is finite).

**`exists_genuineFamilyMovingCharacter`** (PROVED). It produces, for every `Q' ⊆ F.Q`, the leaf's
`GenuineFamilyMovingCharacter (ℚ(√k)) ℓ Q'`:
* one ring-class setup for all stages, whose prescribed pairs are the split pairs over the primes
  of `2N` (labelled `over2N`) and over `F.Q` (labelled active), extended by generators of `Cl(K)`;
* the stage inputs from `GenuineMovingComplete.toInputs`;
* the orientations at the pairs over `Q'`, and the covering of the places above `2N`;
* finite moving supports.
These feed `GenuineFamilyMovingCharacter.ofInputs`, and the remaining hypotheses are only those of
`ofInputs`: `SerreThm3`, `CMjInteger`, `0 < ℓ`, `FrobeniusTrace (E_ℓ)`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 CMjInteger)
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel SplitsIn)
open scoped nonZeroDivisors

/-! ### Auxiliary facts -/

/-- `GenuineMovingComplete` does not depend on the precision. Kind: definition. -/
def GenuineMovingComplete.changeN {E : WeierstrassCurve ℚ} {n : ℕ} {s : Qbar} {S : ℕ}
    {C : RingClassSetup (quadField s) S} (I : GenuineMovingComplete E n s C) (n' : ℕ) :
    GenuineMovingComplete E n' s C where
  hK := I.hK
  hunits := I.hunits
  D := I.D
  sqrtD_sq := I.sqrtD_sq
  act := I.act
  decAct := I.decAct
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  hinj := I.hinj
  hne := I.hne
  hgen := I.hgen
  h2 := I.h2
  Sexc := I.Sexc
  p_mem := I.p_mem
  hSdisc := I.hSdisc
  placeR_over := I.placeR_over

section Ring

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- **A prime containing a nonzero integer `m` contains a prime factor of `m`.** Kind: PROVED. -/
theorem exists_prime_dvd_of_mem (v : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : m ≠ 0)
    (h : ((m : ℕ) : 𝓞 K) ∈ v.asIdeal) : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  induction m using Nat.recOnMul with
  | zero => exact absurd rfl hm
  | one =>
    exact absurd ((Ideal.eq_top_iff_one _).mpr (by simpa using h)) v.isPrime.ne_top
  | prime p hp => exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hm
    have hb : b ≠ 0 := right_ne_zero_of_mul hm
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hpa, hpv⟩ := iha ha h
      exact ⟨p, hp, dvd_mul_of_dvd_left hpa b, hpv⟩
    · obtain ⟨p, hp, hpb, hpv⟩ := ihb hb h
      exact ⟨p, hp, dvd_mul_of_dvd_right hpb a, hpv⟩

/-- Only finitely many primes contain a nonzero integer. Kind: PROVED. -/
theorem finite_setOf_natCast_mem {m : ℕ} (hm : m ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((m : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((m : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  change v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

/-- **A split prime gives a split pair of height-one primes.** Kind: PROVED. -/
theorem exists_pair_of_splitsIn {p : ℕ} (hp : p.Prime) (h : SplitsIn K p) :
    ∃ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q ∧
      P.asIdeal * Q.asIdeal = Ideal.span {(((p : ℤ)) : 𝓞 K)} := by
  obtain ⟨𝔭, 𝔮, h𝔭, h𝔮, hne, hmul⟩ := h
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmem : ((p : ℕ) : 𝓞 K) ∈ 𝔭 * 𝔮 := hmul ▸ Ideal.mem_span_singleton_self _
  have h1 : 𝔭 ≠ ⊥ := by
    intro hb
    have := Ideal.mul_le_left (I := 𝔭) (J := 𝔮) hmem
    rw [hb] at this
    exact hp0 ((Submodule.mem_bot _).mp this)
  have h2 : 𝔮 ≠ ⊥ := by
    intro hb
    have := Ideal.mul_le_right (I := 𝔭) (J := 𝔮) hmem
    rw [hb] at this
    exact hp0 ((Submodule.mem_bot _).mp this)
  refine ⟨⟨𝔭, h𝔭.isPrime, h1⟩, ⟨𝔮, h𝔮.isPrime, h2⟩, fun he => hne ?_, ?_⟩
  · exact congrArg HeightOneSpectrum.asIdeal he
  · change 𝔭 * 𝔮 = _
    rw [← hmul, Int.cast_natCast]

end Ring

/-- **`(k/q) = 1` with `q ∤ k` makes `k` a unit square at `q`** (odd `q`). Kind: PROVED. -/
theorem squareAt_of_jacobiSym {k : ℤ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqk : ¬ (q : ℤ) ∣ k) (hj : jacobiSym k q = 1) :
    ZInQ.Contrib.CloudB3RC53.GenusOdd.SquareAt q k := by
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨hqk, fun h => absurd h hq2, fun _ => ?_⟩
  have h0 : (k : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqk
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  exact (legendreSym.eq_one_iff q h0).mp hj

/-- With the primes of `2N` in the finite support `S`, the level is nonzero. Kind: PROVED. -/
theorem twoN_ne_zero {ℓ : ℕ} {S : Finset ℕ}
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S) :
    2 * newformLevel (Ecurve ℓ) ≠ 0 := by
  intro h0
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (S.sup id + 1)
  have hmem := hS2N p hp (by rw [h0]; exact dvd_zero p)
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-! ### The curve-specific moving data -/

/-- **The curve-specific moving data** (tex 2595–2613, 2674–2694, 2716–2721, 3500–3702,
4255–4280): see the module docstring. For the final companion `k = D.kfin`, an admissible family
`F` and `Q' ⊆ F.Q`, the leaf's `GenuineFamilyMovingCharacter (ℚ(√k)) ℓ Q'`, with stage inputs over
`√k` and `D = k`. Kind: PROVED. -/
theorem exists_genuineFamilyMovingCharacter {ℓ : ℕ} {D : RCData ℓ} (St : RCSteps D)
    (hodd : ¬ D.OddEmptyUnit)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    {F : Family} (hF : F.Admissible D.S D.kfin) {Q : Finset ℕ} (hQ : Q ⊆ F.Q)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ)) :
    ∃ (s : Qbar) (_ : s ^ 2 = algebraMap ℚ Qbar D.kfin)
      (G : GenuineFamilyMovingCharacter (quadField s) ℓ Q),
      ∀ i, (G.I i).sqrtD = s ∧ (G.I i).D = D.kfin := by
  classical
  obtain ⟨hk0, hksq, hk1, hk3, hkS, hk4, hk2N, -, -⟩ := St.companion hodd
  set N := newformLevel (Ecurve ℓ)
  have hN := twoN_ne_zero hS2N
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ Qbar D.kfin) (by norm_num : 0 < 2)
  set K := quadField s
  let T2N : Finset ℕ := (2 * N).primeFactors
  let U : Finset ℕ := T2N ∪ F.Q
  have h2T : 2 ∈ T2N := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 N, hN⟩
  have h2U : 2 ∈ U := Finset.mem_union_left _ h2T
  -- every prime of `U` splits in `K`
  have hsplit : ∀ p ∈ U, p.Prime ∧ SplitsIn K p := by
    intro p hpU
    rcases Finset.mem_union.mp hpU with hpT | hpQ
    · obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.mp hpT
      exact ⟨hp, splitsIn_of_squareAt hs hk0 hksq hk4 hp (hk2N p hp hpd)⟩
    · obtain ⟨hp, hp2, hpS, hj, -⟩ := hF p hpQ
      exact ⟨hp, splitsIn_of_squareAt hs hk0 hksq hk4 hp
        (squareAt_of_jacobiSym hp hp2 (fun hd => hpS (hkS p hp hd)) hj)⟩
  have hpair : ∀ x : U, ∃ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q ∧
      P.asIdeal * Q.asIdeal = Ideal.span {((((x : ℕ) : ℤ)) : 𝓞 K)} := fun x =>
    exists_pair_of_splitsIn (hsplit x x.2).1 (hsplit x x.2).2
  choose Pc Qc hneC hmulC using hpair
  let e : U ≃ Fin U.card := U.equivFin
  let p₀ : Fin U.card → ℕ := fun j => (e.symm j : ℕ)
  let P₀ : Fin U.card → HeightOneSpectrum (𝓞 K) := fun j => Pc (e.symm j)
  let Q₀ : Fin U.card → HeightOneSpectrum (𝓞 K) := fun j => Qc (e.symm j)
  have hp₀ : ∀ j, (p₀ j).Prime := fun j => (hsplit _ (e.symm j).2).1
  have hinj₀ : Function.Injective p₀ := fun a b h =>
    e.symm.injective (Subtype.ext h)
  let act₀ : Fin U.card → Prop := fun j => p₀ j ∈ F.Q
  let over2N₀ : Fin U.card → Prop := fun j => p₀ j ∈ T2N
  have hdis : ∀ j, act₀ j → ¬ over2N₀ j := by
    intro j hQj hTj
    obtain ⟨hp, hpd, -⟩ := Nat.mem_primeFactors.mp hTj
    exact (hF _ hQj).2.2.1 (hS2N _ hp hpd)
  have hodd2 : ∀ j, act₀ j → p₀ j ≠ 2 := fun j hj => (hF _ hj).2.1
  have hsD : s ^ 2 = algebraMap ℚ Qbar ((D.kfin : ℤ) : ℚ) := hs
  obtain ⟨S₁, C, I0, hpre, -, hlab, -, -, hDk, hSr⟩ :=
    exists_genuineMovingComplete_Sr (Ecurve ℓ) 0 hsD (by exact_mod_cast hk0)
      (no_sqrt_neg_one_k hs hk0 hksq hk1) (no_cube_root_k hs hk0 hksq hk3) P₀ Q₀ p₀ hp₀ hinj₀
      (fun j => hneC _) (fun j => hmulC _) act₀ over2N₀ hdis hodd2 ∅ ∅ ∅ (Pc ⟨2, h2U⟩)
  let I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C := fun i => (I0.changeN (2 * i)).toInputs
  have hIact : ∀ i j, (I i).act j ↔ I0.act j := fun _ _ => Iff.rfl
  have hIover : ∀ i j, (I i).over2N j ↔ I0.over2N j := fun _ _ => Iff.rfl
  let idx : ℕ → Fin U.card := fun q => if h : q ∈ U then e ⟨q, h⟩ else e ⟨2, h2U⟩
  have hidx : ∀ q (h : q ∈ U), p₀ (idx q) = q := by
    intro q h
    simp only [idx, h, ↓reduceDIte, p₀, Equiv.symm_apply_apply]
  let o : ℕ → Fin (U.card + S₁) := fun q => Fin.castAdd S₁ (idx q)
  have hQU : ∀ q ∈ Q, q ∈ U := fun q hq => Finset.mem_union_right _ (hQ hq)
  have act_o : ∀ i, ∀ q ∈ Q, (I i).act (o q) := by
    intro i q hq
    rw [hIact]
    refine ((hlab (idx q)).1).mpr ?_
    change p₀ (idx q) ∈ F.Q
    rw [hidx q (hQU q hq)]
    exact hQ hq
  have p_o : ∀ q ∈ Q, C.p (o q) = q := by
    intro q hq
    rw [(hpre (idx q)).2.2, hidx q (hQU q hq)]
  have over2N : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∃ j, (I i).over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j) := by
    intro i v hv
    obtain ⟨p, hp, hpd, hpv⟩ := exists_prime_dvd_of_mem v hN hv
    have hpT : p ∈ T2N := Nat.mem_primeFactors.mpr ⟨hp, hpd, hN⟩
    have hpU : p ∈ U := Finset.mem_union_left _ hpT
    refine ⟨Fin.castAdd S₁ (idx p), ?_, ?_⟩
    · rw [hIover]
      refine ((hlab (idx p)).2).mpr ?_
      change p₀ (idx p) ∈ T2N
      rw [hidx p hpU]; exact hpT
    · rw [(hpre (idx p)).1, (hpre (idx p)).2.1]
      have hw : (((p₀ (idx p) : ℤ)) : 𝓞 K) ∈ v.asIdeal := by
        rw [hidx p hpU, Int.cast_natCast]; exact hpv
      exact eq_or_eq_of_mem_split (hmulC _) hw
  have Sr_finite : ∀ r, (C.Sr r).Finite := by
    intro r
    rw [hSr r, Set.empty_union]
    exact finite_setOf_natCast_mem (by omega)
  refine ⟨s, hs, GenuineFamilyMovingCharacter.ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ
    hT, fun i => ⟨rfl, ?_⟩⟩
  change I0.D = _
  exact hDk

end ZInQ.Contrib.CloudB3E1RingClass

import ZInQKernel.Contrib.CloudB3E1RingClass.CurveData

/-!
# The curve-specific moving data with exact moving supports

Manuscript `diophantine_zq.tex`, tex 3500–3702 and 4255–4280. In the text, a good prime not used
as a moving prime stays unramified, so the moving support at `r` is exactly the set of places
above `r`.

**`exists_genuineFamilyMovingCharacter_exactSr`** (PROVED) is `exists_genuineFamilyMovingCharacter`
with two more conclusions:
* every moving support of the constructed setup is `S_r = {v : max(r, 1) ∈ v}`;
* at each stage, the support `S_{r_i}` is exactly the places above `r_i`
  (`placesOf (ℚ(√k)) r_i`).

The proof is the same construction: its support argument `S_supp` is `∅`.

Kinds: PROVED.
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

/-- **The curve-specific moving data, with the moving supports exactly the places above `r`**
(tex 2595–2613, 2674–2694, 2716–2721, 3500–3702, 4255–4280, and the text's "unused good primes stay
unramified"). For the final companion `k = D.kfin`, an admissible family
`F` and `Q' ⊆ F.Q`, the leaf's `GenuineFamilyMovingCharacter (ℚ(√k)) ℓ Q'`, with stage inputs over
`√k` and `D = k`, and every moving support `S_r` equal to the places above `r`. Kind: PROVED. -/
theorem exists_genuineFamilyMovingCharacter_exactSr {ℓ : ℕ} {D : RCData ℓ} (St : RCSteps D)
    (hodd : ¬ D.OddEmptyUnit)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    {F : Family} (hF : F.Admissible D.S D.kfin) {Q : Finset ℕ} (hQ : Q ⊆ F.Q)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ)) :
    ∃ (s : Qbar) (_ : s ^ 2 = algebraMap ℚ Qbar D.kfin)
      (G : GenuineFamilyMovingCharacter (quadField s) ℓ Q),
      (∀ i, (G.I i).sqrtD = s ∧ (G.I i).D = D.kfin) ∧
      (∀ r, G.C.Sr r = {v | ((max r 1 : ℕ) : 𝓞 (quadField s)) ∈ v.asIdeal}) ∧
      ∀ i, G.C.Sr (G.r i) = placesOf (quadField s) (G.r i : ℤ) := by
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
    hT, fun i => ⟨rfl, hDk⟩, fun r => by
      change C.Sr r = _
      rw [hSr r, Set.empty_union], fun i => ?_⟩
  change C.Sr _ = _
  set G := GenuineFamilyMovingCharacter.ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT
  have hr1 : max (G.r i) 1 = G.r i := max_eq_left (G.r_prime i).one_lt.le
  rw [hSr, Set.empty_union, hr1]
  ext v
  simp only [placesOf, Set.mem_ofPred_eq, Int.cast_natCast]

end ZInQ.Contrib.CloudB3E1RingClass

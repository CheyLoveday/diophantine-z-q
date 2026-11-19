import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPinGenuine

/-!
**Theorem 5.3: the family's moving character bound to the genuine ring-class construction**

Proposition `ex:arith-moving-character` (tex 3500–3702) as used at tex 2729–2737 and 4255–4280.
`GenuineFamilyMovingCharacter K ℓ Q` asks for the moving primes `r_i` and characters `ξ₀ i` of
`Gal(H_{r_i}/K)` as named inputs. Here they are constructed, stage by stage, from the remaining
inputs of the genuine moving data (tex 3694–3695, 4269–4272: "perform this construction
separately at each coefficient stage, excluding `Q` ... and the previously chosen moving primes").

* `genuinePsi_isOpen_ker`: the pullback `genuinePsi C r m ξ₀` of any character `ξ₀` of
  `Gal(H_r/K)` has open kernel, since `H_r ⊂ K_{S_r}` is finite and normal over `K`.
* `moving_character_genuine_factored`: the genuine moving character (`moving_character_genuine`)
  with the character exposed as `genuinePsi C r n ξ₀`; the trace bounds are dropped.
* `not_dvd_twoN_of_goodPrime`: a good prime does not divide `2N` once the places above `2N` are
  chosen primes (the place over `r` of the setup lies over no chosen prime).
* `exists_injective_choice`: an injective choice of witnesses avoiding the earlier values.
* `IsGenuineMovingPrime`, `exists_genuineMovingPrimes`: at every stage `i` a moving prime outside
  `Q` and prime to `2N` with its genuine character at precision `2i`, injective in `i`.
* `GenuineFamilyMovingCharacter.ofInputs`: the family's moving character from the setup `C`, the
  stage inputs `I`, the orientations `o` and the covering of the places above `2N`; its `s`, `C`,
  `I`, `o` are the given ones (`ofInputs_s`, `ofInputs_C`, `ofInputs_I`, `ofInputs_o`), and
  `nonempty_genuineFamilyMovingCharacter`.

No hypothesis is added beyond the inputs of `moving_character_genuine` and the fields of the
structure: the open kernel is proved, and `r ∤ 2N` follows from the covering. Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Gloc locMap)
open ZInQ.Manuscript.RC.TateWiring (GoodPrime FrobeniusTrace)
open ZInQ.Manuscript.RC.PrintsArith (SerreThm3 CMjInteger)
open ZInQ.Manuscript.RC.GlueSweep.Tate (moving_character_ecurve_genuineS)
open ZInQ.Contrib.CloudB3E1RingClass
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)

variable {K : Type} [Field K] [NumberField K]

-- The open kernel of the genuine moving exponent.

/-- **The pullback of a character of `Gal(H_r/K)` has open kernel** (tex 2729, 3500–3506, 4272:
the moving character is finite): the ring class field `H_r ⊂ K_{S_r}` is finite and normal over `K`
(`finiteDimensional_ringClassFieldOf`, `normal_ringClassFieldOf`), so the kernel of
`ξ₀ ∘ res` contains the open fixing subgroup of `H_r` (`inflChar_isOpen_ker`). Kind: PROVED. -/
theorem genuinePsi_isOpen_ker {s : ℕ} (C : RingClassSetup K s) (r m : ℕ)
    (ξ₀ : Additive (setupGal C r) →+ ZMod (2 ^ m)) :
    IsOpen ((genuinePsi C r m ξ₀).ker : Set (GKS K (C.Sr r))) :=
  ZInQ.Manuscript.RC.CoefModules.inflChar_isOpen_ker
    (ringClassFieldOf (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r))
    (AddMonoidHom.toMultiplicative ξ₀)

-- The genuine moving character, factored through `Gal(H_r/K)`.

section Factored

variable {s : ℕ} {C : RingClassSetup K s} {n ℓ : ℕ}

/-- **The genuine moving character through the ring class field** (tex 2729–2737, 3500–3506,
3679–3684, 4258–4264): as `moving_character_genuine`, with the character exposed as
`genuinePsi C r n ξ₀`, the restriction `G_{K,S_r} → Gal(H_r/K)` followed by a character `ξ₀` of
`Gal(H_r/K)`: a good prime `r ∉ S` with `2^B ∣ r − 1`, and `ξ₀` such that every value of `ℤ/2^n`
is taken on the genuine inertia group at the place over `r`, the pullback is trivial on the
genuine decomposition groups at `v ∈ P`, and it takes the value `1` on every Frobenius lift at an
active `𝔭_j` and `−1` at `𝔭̄_j`. The trace bounds are dropped. Kind: PROVED. -/
theorem moving_character_genuine_factored (I : GenuineMovingInputs (Ecurve ℓ) n C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ₀ : Additive (setupGal C r) →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion K),
          genuinePsi C r n ξ₀ (locMap K (C.Sr r) (C.placeR r) σ) = Multiplicative.ofAdd y) ∧
        (∀ v ∈ P, ∀ σ : Gloc K v, genuinePsi C r n ξ₀ (locMap K (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
            genuinePsi C r n ξ₀ (locMap K (C.Sr r) (C.𝔭 j) φ) = Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
            genuinePsi C r n ξ₀ (locMap K (C.Sr r) (C.𝔭bar j) φ) =
              Multiplicative.ofAdd (-1)) := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ0, hin, h2N, hact, -⟩ :=
    moving_character_ecurve_genuineS hS hcm hℓ hT I.toMovingDataK B S
  have hgood' : GoodPrime (Ecurve ℓ) I.sqrtD I.Sexc r := hgood
  let res := ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
  let ξ0' : Additive (setupGal C r) →+ ZMod (2 ^ n) := ξ0
  have hξ : ∀ g, genuinePsi C r n ξ0' g =
      Multiplicative.ofAdd (ξ0' (Additive.ofMul (res g))) := fun _ => rfl
  refine ⟨r, hrS, hrp, hgood', hr1, ξ0', ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz, hzy⟩ := hin y
    obtain ⟨σ, hσ, hσz⟩ := (show Additive.toMul z ∈ inertiaGal (max r 1) (max_one_ne_zero r)
      (C.Sr r) (C.hSr r) (C.placeR r) from hz)
    refine ⟨σ, hσ, ?_⟩
    rw [hξ, ← hzy]
    exact congrArg (fun w => Multiplicative.ofAdd (ξ0' (Additive.ofMul w))) hσz
  · intro v hv σ
    obtain ⟨j, hj, hvj⟩ := hP v hv
    have hz : Additive.ofMul (res (locMap K (C.Sr r) v σ)) ∈
        setupDecomp C r j ⊔ setupDecompBar C r j := by
      rcases hvj with rfl | rfl
      · exact AddSubgroup.mem_sup_left (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
      · exact AddSubgroup.mem_sup_right (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
    rw [hξ]
    change Multiplicative.ofAdd (ξ0 _) = 1
    rw [h2N j hj _ hz]
    rfl
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).1
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭 j) hnm
      (primeToIdeal _ _ (C.𝔭 j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭 j) φ)) = I.toMovingDataK.q r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭 j) φ) = setupQ C r j
      rw [setupQ_eq hnm, h1]
    rw [h2]
    exact (hact j hj).1
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).2
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭bar j)
      hnm (primeToIdeal _ _ (C.𝔭bar j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭bar j) φ)) =
        I.toMovingDataK.qbar r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭bar j) φ) = setupQbar C r j
      rw [setupQbar_eq hnm, h1]
    rw [h2]
    exact (hact j hj).2

/-- **A good prime is prime to `2N`** (tex 2720, 3530–3533, 3566, 3676) when every place above
`2N` is a chosen prime `𝔭_j` or `𝔭̄_j` over `2N`: otherwise the place over `r` of the setup would
lie above `2N`, hence be a chosen prime, while a good `r` lies under no chosen prime.
Kind: PROVED. -/
theorem not_dvd_twoN_of_goodPrime (I : GenuineMovingInputs (Ecurve ℓ) n C)
    (hP : ∀ v ∈ placesTwoN K ℓ, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) {r : ℕ}
    (hr : GoodPrime (Ecurve ℓ) I.sqrtD I.Sexc r) : ¬ r ∣ 2 * newformLevel (Ecurve ℓ) := by
  rintro ⟨k, hk⟩
  have hw : ((r : ℕ) : 𝓞 K) ∈ (C.placeR r).asIdeal := by
    have h := I.placeR_over r hr
    rwa [Int.cast_natCast] at h
  have hmem : C.placeR r ∈ placesTwoN K ℓ := by
    change ((2 * newformLevel (Ecurve ℓ) : ℕ) : 𝓞 K) ∈ (C.placeR r).asIdeal
    rw [hk, Nat.cast_mul]
    exact (C.placeR r).asIdeal.mul_mem_right _ hw
  obtain ⟨j, -, hj⟩ := hP _ hmem
  have hnm := I.not_mem hr j
  rw [max_eq_left hr.1.one_lt.le] at hnm
  rcases hj with hj | hj
  · rw [hj] at hw
    exact hnm.1 hw
  · rw [hj] at hw
    exact hnm.2 hw

end Factored

-- An injective choice of moving primes.

/-- **An injective choice avoiding the earlier values** (tex 3694–3695, 4269–4271: the moving
primes are chosen stage by stage, excluding the previously chosen ones): if at every stage `i`
a witness of `P i` exists outside every finite set, there is an injective choice of witnesses.
The witness at stage `i` avoids the finite set of the witnesses at the stages `< i`, built by
recursion on `i`. Kind: PROVED. -/
theorem exists_injective_choice {P : ℕ → ℕ → Prop} (h : ∀ i (T : Finset ℕ), ∃ x ∉ T, P i x) :
    ∃ r : ℕ → ℕ, Function.Injective r ∧ ∀ i, P i (r i) := by
  choose g hg hP using h
  let F : ℕ → Finset ℕ := fun m => Nat.rec (motive := fun _ => Finset ℕ) ∅
    (fun i T => insert (g i T) T) m
  have hF : ∀ i, F (i + 1) = insert (g i (F i)) (F i) := fun _ => rfl
  have hmono : Monotone F := monotone_nat_of_le_succ fun i => by
    rw [hF]
    exact Finset.subset_insert _ _
  have hmem : ∀ i j, i < j → g i (F i) ∈ F j := by
    intro i j hij
    have h1 : g i (F i) ∈ F (i + 1) := by
      rw [hF]
      exact Finset.mem_insert_self _ _
    exact hmono (show i + 1 ≤ j from hij) h1
  refine ⟨fun i => g i (F i), fun i j hij => ?_, fun i => hP i (F i)⟩
  have hij' : g i (F i) = g j (F j) := hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hmem i j hlt
    rw [hij'] at h1
    exact hg j (F j) h1
  · have h1 := hmem j i hlt
    rw [← hij'] at h1
    exact hg i (F i) h1

-- The moving primes of the family with their genuine characters.

section Primes

variable {s ℓ : ℕ}

/-- **A moving prime at stage `i` with its genuine character** (tex 2729–2737, 3500–3506,
4258–4272): `x` is prime, outside `Q`, prime to `2N`, good for the stage inputs `I i`, and carries
a character `ξ₀` of `Gal(H_x/K)` with values in `ℤ/2^{2i}` whose pullback `genuinePsi` is
surjective on the genuine inertia group at the place over `x`, trivial on the genuine
decomposition groups above `2N`, and takes the value `1` on every Frobenius lift at the active
`𝔭_j` and `−1` at the active `𝔭̄_j`. Kind: definition. -/
def IsGenuineMovingPrime (C : RingClassSetup K s)
    (I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C) (Q : Finset ℕ) (i x : ℕ) : Prop :=
  x.Prime ∧ x ∉ Q ∧ ¬ x ∣ 2 * newformLevel (Ecurve ℓ) ∧
    GoodPrime (Ecurve ℓ) (I i).sqrtD (I i).Sexc x ∧
    ∃ ξ₀ : Additive (setupGal C x) →+ ZMod (2 ^ (2 * i)),
      (∀ y : ZMod (2 ^ (2 * i)),
        ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR x).adicCompletion K),
          genuinePsi C x (2 * i) ξ₀ (locMap K (C.Sr x) (C.placeR x) σ) =
            Multiplicative.ofAdd y) ∧
      (∀ v ∈ placesTwoN K ℓ, ∀ σ : Gloc K v,
        genuinePsi C x (2 * i) ξ₀ (locMap K (C.Sr x) v σ) = 1) ∧
      (∀ j, (I i).act j → ∀ φ : Gloc K (C.𝔭 j),
        TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
          genuinePsi C x (2 * i) ξ₀ (locMap K (C.Sr x) (C.𝔭 j) φ) = Multiplicative.ofAdd 1) ∧
      (∀ j, (I i).act j → ∀ φ : Gloc K (C.𝔭bar j),
        TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
          genuinePsi C x (2 * i) ξ₀ (locMap K (C.Sr x) (C.𝔭bar j) φ) =
            Multiplicative.ofAdd (-1))

/-- **The moving primes of the family** (tex 2737–2740, 3694–3698, 4269–4272): at every stage `i`
the genuine moving character at precision `2i` (`moving_character_genuine_factored` with `P` the
places above `2N`, `B = 0` and the avoidance set `T ∪ Q`), chosen injectively in `i`
(`exists_injective_choice`); the moving primes are prime to `2N` by
`not_dvd_twoN_of_goodPrime`. Kind: PROVED. -/
theorem exists_genuineMovingPrimes (C : RingClassSetup K s)
    (I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C)
    (over2N : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∃ j, (I i).over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j))
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ))
    (Q : Finset ℕ) :
    ∃ r : ℕ → ℕ, Function.Injective r ∧ ∀ i, IsGenuineMovingPrime C I Q i (r i) := by
  refine exists_injective_choice fun i T => ?_
  obtain ⟨x, hxS, hxp, hgood, -, ξ₀, hin, h2N, hact, hbar⟩ :=
    moving_character_genuine_factored (I i) hS hcm hℓ hT (placesTwoN K ℓ) (over2N i) 0 (T ∪ Q)
  exact ⟨x, fun hxT => hxS (Finset.mem_union_left Q hxT), hxp,
    fun hxQ => hxS (Finset.mem_union_right T hxQ),
    not_dvd_twoN_of_goodPrime (I i) (over2N i) hgood, hgood, ξ₀, hin, h2N, hact, hbar⟩

end Primes

-- The family's moving character from the inputs.

namespace GenuineFamilyMovingCharacter

section OfInputs

variable {s ℓ : ℕ} {Q : Finset ℕ} (C : RingClassSetup K s)
  (I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C) (o : ℕ → Fin s)
  (act_o : ∀ i, ∀ q ∈ Q, (I i).act (o q)) (p_o : ∀ q ∈ Q, C.p (o q) = q)
  (over2N : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∃ j, (I i).over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j))
  (Sr_finite : ∀ r, (C.Sr r).Finite) (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
  (hT : FrobeniusTrace (Ecurve ℓ))

/-- **The family's moving character from the inputs of the genuine moving data** (tex 2729–2737,
3500–3702, 4255–4280): the given setup `C`, stage inputs `I`, orientations `o` (`act_o`, `p_o`),
covering `over2N` of the places above `2N` and finite supports; the moving primes `r i` and the
characters `ξ₀ i` of `Gal(H_{r_i}/K)` from `exists_genuineMovingPrimes` (prime, injective, outside
`Q`, prime to `2N`, good); the open kernels from `genuinePsi_isOpen_ker`; the inertia and `2N`
properties at the stage; the orientation values at `j = o q`, active by `act_o`.
Kind: definition. -/
noncomputable def ofInputs : GenuineFamilyMovingCharacter K ℓ Q :=
  have hex := exists_genuineMovingPrimes C I over2N hS hcm hℓ hT Q
  have hP : ∀ i, IsGenuineMovingPrime C I Q i (Classical.choose hex i) :=
    (Classical.choose_spec hex).2
  { s := s
    C := C
    I := I
    o := o
    act_o := act_o
    p_o := p_o
    over2N := over2N
    Sr_finite := Sr_finite
    r := Classical.choose hex
    r_prime := fun i => (hP i).1
    r_injective := (Classical.choose_spec hex).1
    r_notQ := fun i => (hP i).2.1
    r_not_twoN := fun i => (hP i).2.2.1
    r_good := fun i => (hP i).2.2.2.1
    ξ₀ := fun i => Classical.choose (hP i).2.2.2.2
    ψ_open := fun i => genuinePsi_isOpen_ker C _ (2 * i) _
    inertia_onto := fun i => (Classical.choose_spec (hP i).2.2.2.2).1
    twoN := fun i => (Classical.choose_spec (hP i).2.2.2.2).2.1
    orient_one := fun i q hq =>
      (Classical.choose_spec (hP i).2.2.2.2).2.2.1 (o q) (act_o i q hq)
    orientBar_neg := fun i q hq =>
      (Classical.choose_spec (hP i).2.2.2.2).2.2.2 (o q) (act_o i q hq) }

/-- The constructed family has the given number of chosen primes (tex 3530–3533).
Kind: PROVED. -/
theorem ofInputs_s : (ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT).s = s :=
  rfl

/-- The constructed family has the given ring-class setup (tex 3530–3533, 3565–3570).
Kind: PROVED. -/
theorem ofInputs_C : (ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT).C = C :=
  rfl

/-- The constructed family has the given stage inputs (tex 3530–3595, 3662–3693).
Kind: PROVED. -/
theorem ofInputs_I : (ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT).I = I :=
  rfl

/-- The constructed family has the given orientations (tex 2733–2735, 3530–3531, 4260–4264).
Kind: PROVED. -/
theorem ofInputs_o : (ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT).o = o :=
  rfl

end OfInputs

end GenuineFamilyMovingCharacter

/-- **The family's moving character exists from the inputs** (tex 2729–2737, 3500–3702,
4255–4280): `GenuineFamilyMovingCharacter.ofInputs`. Kind: PROVED. -/
theorem nonempty_genuineFamilyMovingCharacter {s ℓ : ℕ} {Q : Finset ℕ} (C : RingClassSetup K s)
    (I : ∀ i, GenuineMovingInputs (Ecurve ℓ) (2 * i) C) (o : ℕ → Fin s)
    (act_o : ∀ i, ∀ q ∈ Q, (I i).act (o q)) (p_o : ∀ q ∈ Q, C.p (o q) = q)
    (over2N : ∀ i, ∀ v ∈ placesTwoN K ℓ, ∃ j, (I i).over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j))
    (Sr_finite : ∀ r, (C.Sr r).Finite) (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (Ecurve ℓ)) : Nonempty (GenuineFamilyMovingCharacter K ℓ Q) :=
  ⟨GenuineFamilyMovingCharacter.ofInputs C I o act_o p_o over2N Sr_finite hS hcm hℓ hT⟩

end ZInQ.Manuscript.RC.Wiring

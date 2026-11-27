import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSeed

/-! Intrinsic ramification and old degrees at a tested prime (tex 9754–9760). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget EvenExpansion EvenMoving PrintsAnalytic
open ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53

set_option maxHeartbeats 1000000

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {p : ℕ} (hpU : p ∈ U)

include hU hpU in
private theorem tested_coprime_complement :
    p.Coprime (movingLevel P (U.erase p)) := by
  apply movingLevel_test_coprime (P := P) (hS := hS)
    (fun q hq => hU q (Finset.mem_of_mem_erase hq))
  exact ⟨hU p hpU, Finset.notMem_erase p U⟩

include hpU in
private theorem movingLevel_split :
    movingLevel P U = p * movingLevel P (U.erase p) := by
  unfold movingLevel
  rw [← Finset.mul_prod_erase U (fun q : ℕ => q) hpU]
  ac_rfl

include hU hpU in
/-- A tested prime occurs exactly once in the ambient level. -/
theorem tested_square_not_dvd_movingLevel : ¬ p ^ 2 ∣ movingLevel P U := by
  rw [movingLevel_split (P := P) hpU, pow_two]
  intro h
  exact (Nat.Prime.coprime_iff_not_dvd (hU p hpU).1).mp
    (tested_coprime_complement (P := P) (hS := hS) hU hpU)
    ((Nat.dvd_of_mul_dvd_mul_left (hU p hpU).1.pos) h)

include hU hpU in
private theorem exists_tested_unit :
    ∃ n : ℕ, n.Coprime (movingLevel P U) ∧
      n ≡ 1 [MOD movingLevel P (U.erase p)] ∧ jacobiSym (p : ℤ) n = -1 := by
  let M := movingLevel P (U.erase p)
  have hp := (hU p hpU).1
  have hp2 := (hU p hpU).ne_two
  let : Fact p.Prime := ⟨hp⟩
  have hcop : p.Coprime M := tested_coprime_complement (P := P) (hS := hS) hU hpU
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨n, hnp, hnM⟩ := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnZ : (n : ZMod p) = (a : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (a : ZMod p), ZMod.natCast_eq_natCast_iff']
    exact hnp
  have hn₁ : n.Coprime p := (ZMod.isUnit_iff_coprime _ _).mp (hnZ.symm ▸ a.isUnit)
  have hn₂ : n.Coprime M := by
    rw [Nat.Coprime, hnM.gcd_eq, Nat.gcd_one_left]
  have h4 : 4 ∣ M := (evenMasked P hS).1.trans (dvd_mul_right _ _)
  have hn4 : n % 4 = 1 := Nat.ModEq.of_dvd h4 hnM
  refine ⟨n, ?_, hnM, ?_⟩
  · rw [movingLevel_split (P := P) hpU]
    exact hn₁.mul_right hn₂
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hp.odd_of_ne_two hp2) hn4,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hnZ]
    exact ha

private theorem jacobi_eq_one_of_congr {M n : ℕ} {d : ℤ} (hn : n ≡ 1 [MOD M])
    (hd : 4 * d.natAbs ∣ M) : jacobiSym d n = 1 := by
  have h4 : 4 ∣ M := (dvd_mul_right 4 d.natAbs).trans hd
  have hn4 : n % 4 = 1 := Nat.ModEq.of_dvd h4 hn
  have ho : Odd n := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.mod_right d ho, (Nat.ModEq.of_dvd hd hn : n % _ = 1 % _),
    ← jacobiSym.mod_right d (by decide : Odd 1), jacobiSym.one_right]

variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)

def evenBlockPrimes (b : EvenBlock U) : Finset ℕ :=
  match b with
  | none => U
  | some j => j.val.primeFactors

include hU hB hJ in
/-- A unit supported at a tested prime reads the quadratic character on
each block that contains that prime. The complementary level contains 4. -/
theorem even_blockChar_at_tested_unit (b : EvenBlock U)
    {n : ℕ} (hn : n.Coprime (movingLevel P U))
    (hnM : n ≡ 1 [MOD movingLevel P (U.erase p)])
    (hb : p ∈ evenBlockPrimes b) :
    (A b).χ n = (jacobiSym (p : ℤ) n : ℂ) := by
  let M := movingLevel P (U.erase p)
  have hmask : maskedLevel P ∣ M := dvd_mul_right _ _
  have h4 : 4 ∣ maskedLevel P := (evenMasked P hS).1
  have hn4 : n % 4 = 1 := Nat.ModEq.of_dvd (h4.trans hmask) hnM
  have ho : Odd n := Nat.odd_iff.mpr (by omega)
  have natCast_one {N : ℕ} (hN : N ∣ M) : (n : ZMod N) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    exact Nat.ModEq.of_dvd hN hnM
  have hminus : jacobiSym (-1) n = 1 :=
    jacobi_eq_one_of_congr hnM (by simpa using h4.trans hmask)
  have hpval : ∀ V : Finset ℕ, V ⊆ U → p ∈ V →
      ∏ q ∈ V, jacobiSym (q : ℤ) n = jacobiSym (p : ℤ) n := by
    intro V hV hpV
    rw [← Finset.mul_prod_erase V (fun q => jacobiSym (q : ℤ) n) hpV]
    have hrest : ∏ q ∈ V.erase p, jacobiSym (q : ℤ) n = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      have hqU : q ∈ U.erase p :=
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hq).1, hV (Finset.mem_of_mem_erase hq)⟩
      apply jacobi_eq_one_of_congr hnM
      simpa only [Int.natAbs_natCast, movingLevel] using
        Nat.mul_dvd_mul h4 (Finset.dvd_prod_of_mem (fun q : ℕ => q) hqU)
    rw [hrest, mul_one]
  cases b with
  | none =>
    calc
      (A none).χ (n : ℕ) = maskedCharacter P n * ∏ q ∈ U, (kronecker (q : ℤ) n : ℂ) :=
        hB n hn
      _ = _ := by
        rw [show maskedCharacter P n = 1 by rw [natCast_one hmask, map_one], one_mul]
        simp only [kronecker_of_odd _ ho, ← Int.cast_prod, hpval U (fun _ h => h) hb]
  | some j =>
    have hj := (mem_subscripts (fun q hq => (hU q hq).1) _).mp j.property
    have hjac : jacobiSym (j.val : ℤ) n = jacobiSym (p : ℤ) n := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hj.1, Nat.cast_prod]
      let J : ℤ →* ℤ :=
        { toFun := fun a => jacobiSym a n
          map_one' := jacobiSym.one_left n
          map_mul' := fun a b => jacobiSym.mul_left a b n }
      change J (∏ q ∈ j.val.primeFactors, (q : ℤ)) = jacobiSym (p : ℤ) n
      rw [map_prod]
      exact hpval _ hj.2 hb
    have hN : P.phaseData.N ∣ M :=
      ((dvd_mul_right _ _).trans (dvd_pow_self _ (by decide))).trans hmask
    calc
      (A (some j)).χ (n : ℕ) = P.phaseData.η n * (jacobiSym (-1) n : ℂ) ^ i.val *
          (kronecker (-(j.val : ℤ)) n : ℂ) :=
        hJ j n (hn.of_dvd_right (unaryLevel_dvd P U j))
      _ = _ := by
        rw [show P.phaseData.η n = 1 by rw [natCast_one hN, map_one], hminus, Int.cast_one,
          one_pow, one_mul, kronecker_of_odd _ ho, ← neg_one_mul (j.val : ℤ),
          jacobiSym.mul_left, hminus, hjac]
        simp

include hU hpU in
private theorem mem_evenBlockPrimes_of_dvd (b : EvenBlock U) (hd : p ∣ evenBlockLevel P b) :
    p ∈ evenBlockPrimes b := by
  cases b with
  | none => exact hpU
  | some j =>
    have hp := (hU p hpU).1
    rcases hp.dvd_mul.mp hd with hm | hj
    · exact False.elim (Nat.Prime.coprime_iff_not_dvd hp |>.mp
        ((tested_coprime_complement (P := P) (hS := hS) hU hpU).of_dvd_right (dvd_mul_right _ _)) hm)
    · exact Nat.mem_primeFactors.mpr ⟨hp, hj,
        ((mem_subscripts (fun q hq => (hU q hq).1) _).mp j.property).1.ne_zero⟩

include hU hpU hB hJ in
/-- At a tested prime, the ramified blocks force ramification already at the
source level. In the other blocks the prime is absent from the whole level. -/
theorem tested_dvd_source_iff (b : EvenBlock U) (c : ↥(A b).columns) :
    p ∣ ((A b).liftColumn (evenBlockLevel_dvd (P := P) b) c).source.level ↔
      p ∈ evenBlockPrimes b := by
  let x := (A b).liftColumn (evenBlockLevel_dvd (P := P) b) c
  have hp := (hU p hpU).1
  constructor
  · intro hd
    exact mem_evenBlockPrimes_of_dvd (hS := hS) hU hpU b (hd.trans (dvd_of_mul_left_dvd
      ((A b).liftColumn_level (evenBlockLevel_dvd (P := P) b) c)))
  · intro hb
    by_contra hnot
    obtain ⟨n, hn, hnM, hneg⟩ := exists_tested_unit (P := P) (hS := hS) hU hpU
    have hlevel : x.source.level ∣ movingLevel P (U.erase p) := by
      have hd := (congrArg (fun N => x.source.level ∣ N)
        (movingLevel_split (P := P) hpU)).mp x.source_dvd
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot).symm.dvd_of_dvd_mul_left hd
    have hone : (n : ZMod x.source.level) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
      exact Nat.ModEq.of_dvd hlevel hnM
    let u := ZMod.unitOfCoprime n hn
    have hu : ZMod.unitsMap x.source_dvd u = 1 := Units.ext (by
      rw [ZMod.unitsMap_unitOfCoprime, ZMod.coe_unitOfCoprime, Units.val_one, hone])
    have he := congrArg (fun χ => (χ u : ℂ)) ((A b).liftColumn_char
      (evenBlockLevel_dvd (P := P) b) c)
    have hχ : (A b).χ n = 1 := by
      change (x.char u : ℂ) = _ at he
      rw [CuspDilation.char, MonoidHom.comp_apply, hu, map_one, Units.val_one] at he
      simpa only [u, MonoidHom.comp_apply, ZMod.unitsMap_unitOfCoprime,
        MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] using he.symm
    rw [even_blockChar_at_tested_unit hU hB hJ b hn hnM hb, hneg,
      Int.cast_neg, Int.cast_one] at hχ
    exact (by norm_num : (-1 : ℂ) ≠ 1) hχ

include hU hpU hB hJ in
/-- All retained dilation degrees are prime to the tested prime. In a
ramified block the source level uses its single factor of the prime. In an
unramified block the prime already misses the intrinsic level. -/
theorem tested_not_dvd_degree
    (x : ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P)))) :
    ¬ p ∣ x.val.degree := by
  intro hd
  obtain ⟨b, c, he⟩ := (mem_distinctCuspColumns A (evenBlockLevel_dvd (P := P)) _).mp x.property
  have hlev := (A b).liftColumn_level (evenBlockLevel_dvd (P := P) b) c
  have hx : p ∣ x.val.source.level := by
    rw [← he, tested_dvd_source_iff hU hpU hB hJ b c]
    have hm := (dvd_mul_right _ _).trans hlev
    rw [he] at hm
    exact mem_evenBlockPrimes_of_dvd (hS := hS) hU hpU b (hd.trans hm)
  exact tested_square_not_dvd_movingLevel (P := P) (hS := hS) hU hpU
    ((by simpa only [pow_two] using Nat.mul_dvd_mul hd hx : p ^ 2 ∣
      x.val.degree * x.val.source.level).trans x.val.divides)

end ZInQ.Manuscript.RC.EvenJoin

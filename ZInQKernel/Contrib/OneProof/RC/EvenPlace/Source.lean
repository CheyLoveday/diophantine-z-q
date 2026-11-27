import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Scalars
import ZInQKernel.Contrib.OneProof.RC.Odd.DivisionsFinal

/-! The fixed shell recurrence extends the coefficient field and integral
lifts from the squarefree indices to the entire sieved sequence. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript.RC.Odd NumberField IsDedekindDomain HeightOneSpectrum

theorem all_mem_of_recurrence (O : Subring ℂ) {a η : ℕ → ℂ} {G : ℕ → Prop}
    {ap : ℕ → ℤ} (hη : ∀ n, η n ∈ O) (hzero : a 0 = 0)
    (hsupp : ∀ n, (∃ q ∈ n.primeFactors, ¬ G q) → a n = 0)
    (hbase : ∀ n, Squarefree n → a n ∈ O)
    (hrec : ∀ q (hq : q.Prime), G q → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @RecAt ℂ _ q ⟨hq⟩ (η q) ε (ap q) a)
    (n : ℕ) : a n ∈ O := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · simp [hn, hzero]
    by_cases hsq : Squarefree n
    · exact hbase n hsq
    have hnq := Nat.squarefree_iff_prime_squarefree.not.mp hsq
    push Not at hnq
    obtain ⟨q, hq, hd⟩ := hnq
    have hd₂ : q ^ 2 ∣ n := by simpa [pow_two] using hd
    by_cases hg : G q
    · obtain ⟨ε, _, he⟩ := hrec q hq hg
      let : Fact q.Prime := ⟨hq⟩
      let m := n / q ^ 2
      have hm : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_pow (by decide) hq.one_lt)
      have hh := he m
      rw [Nat.mul_div_cancel' hd₂] at hh
      rw [hh]
      apply O.sub_mem (O.mul_mem (O.mul_mem (hη q) (intCast_mem O _)) (ih m hm))
      apply O.mul_mem (O.mul_mem (natCast_mem O _) (O.pow_mem (hη q) _))
      unfold divCoeff
      split_ifs
      · exact ih _ ((Nat.div_le_self m _).trans_lt hm)
      · exact O.zero_mem
    · rw [hsupp n ⟨q, Nat.mem_primeFactors.mpr
        ⟨hq, (dvd_pow_self q (by decide : 2 ≠ 0)).trans hd₂, hn⟩, hg⟩]
      exact O.zero_mem

theorem recur_scale {a : ℕ → ℂ} {p : ℕ} [Fact p.Prime] {η c : ℂ} {ε ap : ℤ}
    (h : RecAt p η ε ap a) : RecAt p η ε ap (fun n => c * a n) := by
  intro n
  have hdiv : divCoeff (fun j => c * a j) (p ^ 2) n = c * divCoeff a (p ^ 2) n := by
    unfold divCoeff
    split_ifs <;> simp
  rw [hdiv]
  dsimp only
  rw [h n]
  ring

namespace Place

variable {F : IntermediateField ℚ ℂ} [NumberField F] (V : Place F)

/-- Recover the unshifted coefficient in the number field; only its shifted
image is required to lie in the valuation ring. -/
def unshiftedLift (k : ℤ) (z : ℂ) (hz : (2 : ℂ) ^ k * z ∈ V.complexIntegers) : F :=
  (2 : F) ^ (-k) * V.fieldLift ((2 : ℂ) ^ k * z) hz

theorem unshiftedLift_complex (k : ℤ) (z : ℂ) (hz : (2 : ℂ) ^ k * z ∈ V.complexIntegers) :
    F.subtype (V.unshiftedLift k z hz) = z := by
  let e : F →+* ℂ := F.subtype
  change e (V.unshiftedLift k z hz) = z
  rw [unshiftedLift, map_mul, map_zpow₀ e, map_ofNat,
    show e (V.fieldLift ((2 : ℂ) ^ k * z) hz) = _ from V.fieldLift_complex _ hz,
    ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), neg_add_cancel, zpow_zero, one_mul]

theorem unshiftedLift_local (k : ℤ) (z : ℂ) (hz : (2 : ℂ) ^ k * z ∈ V.complexIntegers) :
    algebraMap V.LocalIntegers V.LocalField (V.localLift ((2 : ℂ) ^ k * z) hz) =
      (2 : V.LocalField) ^ k * FinitePlace.embedding V.v (V.unshiftedLift k z hz) := by
  let : CharZero V.LocalField := charZero_of_injective_ringHom
    (FinitePlace.embedding (K := F) V.v).injective
  rw [V.localLift_eq, unshiftedLift, map_mul, map_zpow₀, map_ofNat,
    ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : V.LocalField) ≠ 0), add_neg_cancel, zpow_zero, one_mul]

/-- A single shift pays the fixed squarefree minimum at every index.
The same good-prime recurrence is reused after scaling. -/
theorem source_shift_mem {a η z : ℕ → ℂ} {r : ℕ → ℚ} {G adm : ℕ → Prop}
    {ap : ℕ → ℤ} (δ : ℤ)
    (hη : ∀ n, η n ∈ V.complexIntegers) (hz : ∀ n, adm n → z n ∈ V.complexIntegers)
    (hzero : a 0 = 0)
    (hsupp : ∀ n, (∃ q ∈ n.primeFactors, ¬ G q) → a n = 0)
    (hoff : ∀ n, Squarefree n → ¬ adm n → a n = 0)
    (hbase : ∀ n, Squarefree n → adm n → a n = z n * (r n : ℂ))
    (hdepth : ∀ n, adm n → r n ≠ 0 → δ ≤ padicValRat 2 (r n))
    (hrec : ∀ p (hp : p.Prime), G p → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @RecAt ℂ _ p ⟨hp⟩ (η p) ε (ap p) a)
    (n : ℕ) : (2 : ℂ) ^ (-δ) * a n ∈ V.complexIntegers := by
  refine all_mem_of_recurrence (a := fun j => (2 : ℂ) ^ (-δ) * a j)
    (G := G) (ap := ap) V.complexIntegers hη (by simp [hzero])
    (fun j hj => by simp [hsupp j hj]) ?_ ?_ n
  · intro j hj
    by_cases ha : adm j
    · obtain ⟨y, hy, he⟩ := V.scaled_phase_factor (hz j ha) (r j) (-δ) 0
        (fun hr => by simpa using hdepth j ha hr)
      rw [hbase j hj ha, he, pow_zero, one_mul]
      exact hy
    · simp [hoff j hj ha]
  · intro p hp hG
    obtain ⟨ε, hε, he⟩ := hrec p hp hG
    let : Fact p.Prime := ⟨hp⟩
    exact ⟨ε, hε, recur_scale he⟩

end Place

/-- Lift an integral complex sequence and its character to the subring
and transport the exact divisibility interface, at every cutoff. -/
theorem sourceHyp_of_complex (O : Subring ℂ) {a η : ℕ → ℂ} {G adm : ℕ → Prop}
    {ap : ℕ → ℤ} {δ : ℤ}
    (hη : ∀ n, η n ∈ O) (hηmul : ∀ x y, η (x * y) = η x * η y) (hηone : η 1 = 1)
    (hprime : ∀ p, G p → p.Prime) (hodd : ∀ p, G p → Odd (p : ℤ))
    (hap : ∀ p, G p → ap p ≡ p + 1 [ZMOD 4])
    (hzero : a 0 = 0)
    (hsupp : ∀ n, (∃ p ∈ n.primeFactors, ¬ G p) → a n = 0)
    (hoff : ∀ n, Squarefree n → ¬ adm n → a n = 0)
    (hbase : ∀ n, Squarefree n → adm n → ∃ y ∈ O,
      a n = (2 : ℂ) ^ (δ + ArithmeticFunction.cardDistinctFactors n).toNat * y)
    (hrec : ∀ p (hp : p.Prime), G p → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @RecAt ℂ _ p ⟨hp⟩ (η p) ε (ap p) a) :
    ∃ b χ : ℕ → O, (∀ n, (b n : ℂ) = a n) ∧ (∀ n, (χ n : ℂ) = η n) ∧
      ∀ t, SourceHyp t δ χ G adm ap b := by
  classical
  have ha : ∀ n, a n ∈ O :=
    all_mem_of_recurrence O hη hzero hsupp (fun n hsq => by
      by_cases hd : adm n
      · obtain ⟨y, hy, he⟩ := hbase n hsq hd
        exact he ▸ O.mul_mem (O.pow_mem (ofNat_mem O _) _) hy
      · rw [hoff n hsq hd]
        exact O.zero_mem) hrec
  let b (n : ℕ) : O := ⟨a n, ha n⟩
  let χ (n : ℕ) : O := ⟨η n, hη n⟩
  refine ⟨b, χ, fun _ => rfl, fun _ => rfl, fun t => ⟨⟨hprime, hodd, hap, ?_,
    Subtype.ext hzero, fun n hn => Subtype.ext (hsupp n hn),
    fun n hsq hn => Subtype.ext (hoff n hsq hn),
    fun x y => Subtype.ext (hηmul x y), Subtype.ext hηone⟩, ?_⟩⟩
  · intro p hp
    let : Fact p.Prime := ⟨hprime p hp⟩
    obtain ⟨ε, hε, h⟩ := hrec p (hprime p hp) hp
    refine ⟨ε, hε, fun n => Subtype.ext ?_⟩
    have hd : O.subtype (divCoeff b (p ^ 2) n) = divCoeff a (p ^ 2) n := by
      rw [← divCoeff_map]
      rfl
    change O.subtype (b (p ^ 2 * n)) =
      O.subtype (χ p * ((ap p - ε * legendreSym p (-(n : ℤ)) : ℤ) : O) * b n -
        (p : O) * χ p ^ 2 * divCoeff b (p ^ 2) n)
    simp only [map_sub, map_mul, map_pow, map_intCast, map_natCast, hd]
    exact h n
  · intro n hn hd
    obtain ⟨y, hy, h⟩ := hbase n hn hd
    apply (pow_dvd_pow 2 (show (min (t : ℤ) (δ + ArithmeticFunction.cardDistinctFactors n)).toNat ≤
      (δ + ArithmeticFunction.cardDistinctFactors n).toNat from Int.toNat_le_toNat (min_le_right _ _))).trans
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change a n = O.subtype
      ((2 : O) ^ (δ + ArithmeticFunction.cardDistinctFactors n).toNat * ⟨y, hy⟩)
    rw [map_mul, map_pow, map_ofNat]
    exact h

end ZInQ.Manuscript.RC.EvenPlace

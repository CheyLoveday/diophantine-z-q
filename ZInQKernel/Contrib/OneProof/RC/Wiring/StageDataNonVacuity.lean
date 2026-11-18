import ZInQKernel.Contrib.OneProof.RC.Wiring.StageData
import ZInQKernel.Contrib.OneProof.RC.Stages.DetectorStages

/-!
The stage examples use an intrinsic unit support disjoint from the chosen companion's prime
support. Later prime exclusions use `withPreparedStagesSeparated`; `stageClauses_fresh_prime` is a
concrete instance with the prime `5` of `k = −5` in the support but not in the intrinsic support. The detector and prime-sequence
statements remain conditional on their stated inputs; this file constructs neither the full odd
models nor `WitnessSpecialization`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages ZInQ.Contrib.CloudB3RC53 Filter
  Topology ZInQ.Manuscript.RC.TateWiring ZInQ.Contrib.CloudB3RC53.OpenImage

/-- **The constructed data satisfy the support clause** (PROVED; the intrinsic support is the
whole support, `preparedSeparated_self`). -/
theorem stageSupport_withPreparedStages {ℓ : ℕ} (W₀ : WData ℓ) {S : Finset ℕ} {hstar : ℤ}
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hS : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S) (hh : hstar.natAbs.primeFactors ⊆ S)
    (hdisj : Disjoint S W₀.kfin.natAbs.primeFactors) :
    StageSupport (withPreparedStages W₀ S hstar q) :=
  ⟨hS, hbase, hh, S, Finset.Subset.refl _, hbase, hh, hdisj,
    (preparedSeparated_self S).symm⟩

/-- **The constructed data satisfy the stage link, for every stage sequence** (PROVED, `rfl`). -/
theorem stagesFrom_withPreparedStages {ℓ : ℕ} (W₀ : WData ℓ) (S : Finset ℕ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B) :
    StagesFrom (withPreparedStages W₀ S hstar q) q :=
  ⟨rfl, rfl, rfl⟩

/-- The support `S₀ ∪ primes(h_*)` consists of primes (PROVED). -/
theorem s0_union_primeFactors_prime (ℓ : ℕ) (hstar : ℤ) :
    ∀ p ∈ S0 ℓ ∪ hstar.natAbs.primeFactors, p.Prime := by
  intro p hp
  rcases Finset.mem_union.mp hp with h | h
  · simp only [S0, Finset.mem_insert, Nat.mem_primeFactors] at h
    rcases h with rfl | rfl | ⟨hp', -⟩
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact hp'
  · exact Nat.prime_of_mem_primeFactors h

/-- **A concrete support** (PROVED): `S₀ ∪ primes(h_*)` satisfies the support clause, for non-stage data satisfying the displayed disjointness condition and every stage sequence. -/
theorem stageSupport_example {ℓ : ℕ} (W₀ : WData ℓ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hdisj : Disjoint (S0 ℓ ∪ hstar.natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    StageSupport (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) :=
  stageSupport_withPreparedStages W₀ q (s0_union_primeFactors_prime ℓ hstar)
    Finset.subset_union_left Finset.subset_union_right hdisj

/-- **The stage clauses from the detector construction** (PROVED from the construction's
`exists_detector_stages`; tex 2468–2493, 8308–8405): given its inputs, for non-stage data satisfying the displayed disjointness condition,
every admissible support and every finite exclusion, the detector value, an actual detecting
sequence of the type asked by `OddStagedInstance`, and the support clause, the stage link and the
data specification for the constructed data. -/
theorem stageClauses_of_detector {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ}
    (hDw : 0 < Dw) (hstar₀ : hstar < 0)
    [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (P : ((qtwist (Ecurve ℓ) Dw)⁄ℚ).toAffine.Point)
    (hnt : ¬ IsOfFinAddOrder P) (hS : SerreThm3) (hA : HasNoCM (qtwist (Ecurve ℓ) Dw))
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    {x y : Qbar} (hxmem : x ∈ F₀) (hymem : y ∈ F₀)
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar))
    (W₀ : WData ℓ) (S B : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S)
    (hh : hstar.natAbs.primeFactors ⊆ S)
    (hdisj : Disjoint S W₀.kfin.natAbs.primeFactors) :
    let A := qtwist (Ecurve ℓ) Dw
    let Q := Affine.Point.baseChange (W' := A) ℚ Qbar P
    let d := divisionTower (A := A) Q
    let hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q :=
      fun g => Affine.Point.map_baseChange (W' := A) g.toAlgHom P
    ∃ (a : ℕ) (σ : GalQ) (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])
      (q : StageSequence (ActualAt A (Ecurve ℓ) Q F₀ σ Dw hstar) (a + 1)
        (stageExclusions ℓ Dw hstar B)),
      b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1) ∧
      StageSupport (withPreparedStages W₀ S hstar q) ∧
      StagesFrom (withPreparedStages W₀ S hstar q) q ∧
      (withPreparedStages W₀ S hstar q).hstar = hstar ∧
      PreDataSpec (withPreparedStages W₀ S hstar q) := by
  intro A Q d hQ
  obtain ⟨a, σ, b, -, -, -, hc, hseq⟩ :=
    exists_detector_stages hℓ hDw hstar₀ P hnt hS hA F₀ hxmem hymem hx hy
  obtain ⟨q⟩ := hseq B
  have hsupp := stageSupport_withPreparedStages W₀ q hSp hbase hh hdisj
  have hfrom := stagesFrom_withPreparedStages W₀ S hstar q
  exact ⟨a, σ, b, q, hc, hsupp, hfrom, rfl, (preDataSpec_of_stagesFrom hsupp hfrom).1⟩

/-- **Actual stage sequences exist unconditionally** (PROVED from the construction's
`actualStageSequence`, i.e. Chebotarev by the repository's density theorem; tex 8358–8377,
8399–8405): for actual complex conjugation, the auxiliary field `ℚ(√D_w, √h_*)`, any point `Q`, any
precision offset and any finite exclusion. (The detector value `b c_Q(σ²) = 2^{a+1}` is not claimed
here: for `σ = τ` the square is trivial; it needs the translate of `stageClauses_of_detector`.) -/
theorem exists_conj_stageSequence {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ} (hDw : 0 < Dw)
    (hstar₀ : hstar < 0) [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (Q : GeomPoint (qtwist (Ecurve ℓ) Dw)) (cw : ℕ) (B : Finset ℕ) :
    ∃ F₀ : IntermediateField ℚ Qbar, Nonempty (StageSequence
      (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj Dw hstar) cw
      (stageExclusions ℓ Dw hstar B)) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((Dw : ℤ) : Qbar) (by norm_num : 0 < 2)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((hstar : ℤ) : Qbar) (by norm_num : 0 < 2)
  let F₀ := IntermediateField.adjoin ℚ ({x, y} : Set Qbar)
  have : FiniteDimensional ℚ F₀ := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral)
  refine ⟨F₀, ⟨actualStageSequence (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj
    (det_complexConj (Ecurve ℓ)) Dw hstar cw (stageExclusions ℓ Dw hstar B)
    (IntermediateField.subset_adjoin _ _ (by simp)) (IntermediateField.subset_adjoin _ _ (by simp))
    hx hy (complexConj_pos_sqrt hDw hx) (complexConj_neg_sqrt hstar₀ hy)
    (fun p hp hn => stageExclusions_good hℓ.ne' hDw.ne' hstar₀.ne B hp hn)⟩⟩

/-- **The definitional stage clauses with an actual sequence** (PROVED under the displayed disjointness condition): for non-stage data satisfying the displayed disjointness condition `W₀`, the data built at the support `S₀ ∪ primes(h_*)` and an actual sequence of
`exists_conj_stageSequence` satisfy `StageSupport`, `StagesFrom`, `PreDataSpec` and the advancing
precision. -/
theorem stageClauses_conj {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ} (hDw : 0 < Dw)
    (hstar₀ : hstar < 0) [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (Q : GeomPoint (qtwist (Ecurve ℓ) Dw)) (cw : ℕ) (B : Finset ℕ) (W₀ : WData ℓ)
    (hdisj : Disjoint (S0 ℓ ∪ hstar.natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj Dw hstar) cw
      (stageExclusions ℓ Dw hstar B)),
      StageSupport (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) ∧
      StagesFrom (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) q ∧
      PreDataSpec (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) ∧
      Tendsto (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q).Mθ
        ((withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q).stages : Filter ℕ)
        atTop := by
  obtain ⟨F₀, ⟨q⟩⟩ := exists_conj_stageSequence hℓ hDw hstar₀ Q cw B
  have hsupp := stageSupport_example W₀ hstar q hdisj
  have hfrom := stagesFrom_withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q
  exact ⟨F₀, q, hsupp, hfrom, preDataSpec_of_stagesFrom hsupp hfrom⟩

/-- **A concrete instance** (PROVED): `ℓ = 1`, `D_w = 1`, `h_* = −7`, the zero point, offset `0`,
no extra exclusion, non-stage data satisfying the displayed disjointness condition. -/
theorem stageClauses_concrete (W₀ : WData 1)
    (hdisj : Disjoint (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    letI := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
    letI : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
      Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
        (by norm_num)
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)) (Ecurve 1) 0 F₀ complexConj 1 (-7)) 0
      (stageExclusions 1 1 (-7) ∅)),
      StageSupport (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) ∧
      StagesFrom (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) q ∧
      PreDataSpec (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) := by
  let := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
  let : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
      (by norm_num)
  obtain ⟨F₀, q, h1, h2, h3, -⟩ :=
    stageClauses_conj (ℓ := 1) (by norm_num) (Dw := 1) (hstar := -7) (by norm_num) (by norm_num)
      0 0 ∅ W₀ hdisj
  exact ⟨F₀, q, h1, h2, h3⟩

/-- `S₀(1) = {2, 3}` lies in `{2, 3, 7}` (PROVED). -/
theorem s0_one_subset : S0 1 ⊆ ({2, 3, 7} : Finset ℕ) := by
  intro p hp
  simp only [S0, Nat.primeFactors_one, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl <;> simp

/-- The primes of `h_* = −7` lie in `{2, 3, 7}` (PROVED). -/
theorem primeFactors_neg_seven_subset : (-7 : ℤ).natAbs.primeFactors ⊆ ({2, 3, 7} : Finset ℕ) := by
  rw [show (-7 : ℤ).natAbs = 7 by rfl, Nat.Prime.primeFactors (by norm_num : Nat.Prime 7)]
  simp

/-- The data `W₀` with the final companion `k = −5` (definition). -/
def withKMinusFive (W₀ : WData 1) : WData 1 := { W₀ with kfin := -5 }

/-- **A concrete instance with a fresh prime of `k` in the support** (PROVED): `ℓ = 1`, `D_w = 1`,
`h_* = −7`, `k = −5`; the support `{5, 2, 3, 7}` contains the prime `5` of `k`, the unit tests are
at the intrinsic support `{2, 3, 7}` (no squareclass condition at `5`), and the data built from an
actual stage sequence satisfy `StageSupport`, `StagesFrom` and `PreDataSpec`. -/
theorem stageClauses_fresh_prime (W₀ : WData 1) :
    letI := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
    letI : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
      Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
        (by norm_num)
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)) (Ecurve 1) 0 F₀ complexConj 1 (-7)) 0
      (stageExclusions 1 1 (-7) ∅)),
      StageSupport
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) ∧
      StagesFrom
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) q ∧
      PreDataSpec
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) ∧
      (5 : ℤ) ∣
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q).kfin ∧
      5 ∈ (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q).S ∧
      5 ∉ ({2, 3, 7} : Finset ℕ) := by
  let := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
  let : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
      (by norm_num)
  obtain ⟨F₀, ⟨q⟩⟩ := exists_conj_stageSequence (ℓ := 1) (by norm_num) (Dw := 1) (hstar := -7)
    (by norm_num) (by norm_num) 0 0 ∅
  have hprime : ∀ p ∈ ({5, 2, 3, 7} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hkf : (withKMinusFive W₀).kfin = -5 := rfl
  have hdisj : Disjoint ({2, 3, 7} : Finset ℕ) (withKMinusFive W₀).kfin.natAbs.primeFactors := by
    rw [hkf, show (-5 : ℤ).natAbs = 5 by rfl, Nat.Prime.primeFactors (by norm_num : Nat.Prime 5)]
    decide
  have hsupp := stageSupport_withPreparedStagesSeparated (withKMinusFive W₀) q hprime
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢; omega)
    s0_one_subset primeFactors_neg_seven_subset hdisj
  have hfrom : StagesFrom
      (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) q :=
    ⟨rfl, rfl, rfl⟩
  exact ⟨F₀, q, hsupp, hfrom, (preDataSpec_of_stagesFrom hsupp hfrom).1,
    ⟨-1, by show (-5 : ℤ) = 5 * (-1); norm_num⟩,
    by simp [withPreparedStagesSeparated, withStages], by decide⟩

end ZInQ.Manuscript.RC.Wiring

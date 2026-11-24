import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Divided
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant

/-! The exact even version of the two-fresh test (tex 9712–9717,
9741–9745). The sequential density and continuity arguments follow the
two-fresh lane, with no odd-stage precision argument. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open AddressGenuine PrintsArith TraceLimits
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I O K : Type} [CommRing O] [Field K] [CharZero K] [Algebra O K]
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O}

private theorem dense_testPairs (T : TypeData L ε) (avoid : Finset ℕ) :
    Dense {x : GalQ × GalQ | ∃ q r, T.Good q ∧ T.Good r ∧ q ∉ avoid ∧ r ∉ avoid ∧
      q ≠ r ∧ IsFrobAt x.1 q ∧ IsFrobAt x.2 r} := by
  refine dense_iff_inter_open.mpr ?_
  rintro W hW ⟨⟨g, h⟩, hgh⟩
  obtain ⟨V₁, V₂, hV₁, hV₂, hg, hh, hVW⟩ := isOpen_prod_iff.mp hW g h hgh
  obtain ⟨x, ⟨q, hq, hqa, hx⟩, hxV⟩ :=
    (dense_frobeniusTests T avoid).exists_mem_open hV₁ ⟨g, hg⟩
  obtain ⟨y, ⟨r, hr, hra, hy⟩, hyV⟩ :=
    (dense_frobeniusTests T (insert q avoid)).exists_mem_open hV₂ ⟨h, hh⟩
  exact ⟨(x, y), hVW ⟨hxV, hyV⟩, q, r, hq, hr, hqa,
    fun e => hra (Finset.mem_insert_of_mem e),
    fun e => hra (e ▸ Finset.mem_insert_self q avoid), hx, hy⟩

variable [TopologicalSpace K] [IsTopologicalRing K]

private theorem continuous_doubleTrace (hcont : ContinuousOperators ρ Λ) (v : Λ) :
    Continuous fun x : GalQ × GalQ => tV ρ x.1 (tV ρ x.2 v) := by
  apply continuous_pi
  intro i
  by_cases hi : (v : I → K) i = 0
  · simpa only [tV, scalarOp_apply, hi, mul_zero] using
      (continuous_const : Continuous fun _ : GalQ × GalQ => (0 : K))
  · have hc : Continuous fun g : GalQ => tV ρ g v i :=
      (continuous_apply i).comp (hcont.trace v)
    have he (x : GalQ × GalQ) :
        tV ρ x.1 (tV ρ x.2 v) i =
          (tV ρ x.1 v i * tV ρ x.2 v i) * ((v : I → K) i)⁻¹ := by
      simp only [tV, scalarOp_apply, mul_assoc, mul_inv_cancel₀ hi, mul_one]
      ring
    simp_rw [he]
    exact ((hc.comp continuous_fst).mul (hc.comp continuous_snd)).mul continuous_const

variable [T2Space K] [TopologicalSpace O] [CompactSpace O] [ContinuousSMul O K]

/-- The constructor's two-fresh input before the constituent model is
built, from exact divided expansions and the ambient Hecke laws. -/
theorem two_trace_mem (B : ℕ) (F : Finset ℕ → Λ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (coeff : ℕ → Λ →ₗ[O] O) (hcoeff : ∀ n, Continuous (coeff n))
    (hhecke : ∀ q, T.Good q → q ∉ avoid → HeckeFourier coeff (ops.hecke q) (ops.diamond q) q)
    (hm2 : (2 : O) ∈ m) (hm : IsClosed (m : Set O)) (hΛ : Λ.FG)
    (hinj : Function.Injective (algebraMap O K))
    {δ : ℤ} {η a : ℕ → O} {adm : ℕ → Prop} {ap : ℕ → ℤ}
    (H : ∀ t, SourceHyp t δ η T.Good adm ap a) (i : Fin 2)
    (hexp : ∀ U : Finset ℕ, ∀ hU : (∀ s ∈ U, T.Good s), U.card + 1 ≤ B →
      ∀ n, n ≠ 0 → coeff n (F U) = ThetaCoeff.timesTheta
        (dividedCoeff H i U.toList U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))) n) :
    let st := (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1
    ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
      ∀ n : ℕ, n ≠ 0 → coeff n (latT ρ Λ st g (latT ρ Λ st h (F U))) ∈ m := by
  intro st U hU hB g h n hn
  let trace (g : GalQ) (x : Λ) : Λ := ⟨tV ρ g x, st g _ x.2⟩
  change coeff n (trace g (trace h (F U))) ∈ m
  let testAvoid := avoid ∪ U ∪ n.primeFactors
  have hc : Continuous fun x : GalQ × GalQ => coeff n (trace x.1 (trace x.2 (F U))) :=
    (hcoeff n).comp ((continuous_doubleTrace hcont (F U)).subtype_mk _)
  refine (dense_testPairs T testAvoid).induction
    (P := fun x => coeff n (trace x.1 (trace x.2 (F U))) ∈ m) ?_ (hm.preimage hc) (g, h)
  rintro ⟨x, y⟩ ⟨q, r, hq, hr, hqa, hra, hne, hx, hy⟩
  have ha {p : ℕ} (hp : p ∉ testAvoid) : p ∉ avoid := fun e =>
    hp (Finset.mem_union_left _ (Finset.mem_union_left _ e))
  have hu {p : ℕ} (hp : p ∉ testAvoid) : p ∉ U := fun e =>
    hp (Finset.mem_union_left _ (Finset.mem_union_right _ e))
  have hn' {p : ℕ} (hp : p.Prime) (hpa : p ∉ testAvoid) : ¬ p ∣ n := fun e =>
    hpa (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, e, hn⟩))
  have ht {z : GalQ} {p : ℕ} (hp : T.Good p) (hpa : p ∉ testAvoid) (hz : IsFrobAt z p)
      (v : Λ) : trace z v = ops.hecke p v := by
    apply Subtype.ext
    change tV ρ z v = _
    rw [(operators_eq_at_frobenius T hunr hp (ha hpa) hz (hfrob p hp)).1,
      ops.trace_eq p hp (ha hpa)]
  have hrn : ¬ r ∣ q * n := fun hd =>
    (hr.1.dvd_mul.mp hd).elim
      (fun hrq => hne ((Nat.prime_dvd_prime_iff_eq hr.1 hq.1).mp hrq).symm)
      (hn' hr.1 hra)
  let j := r * (q * n)
  have hj : j ≠ 0 := mul_ne_zero hr.1.ne_zero (mul_ne_zero hq.1.ne_zero hn)
  change coeff n (trace x (trace y (F U))) ∈ m
  rw [ht hr hra hy, ht hq hqa hx, hhecke q hq (ha hqa) n, ite_eq_right (hn' hq.1 hqa),
    add_zero, hhecke r hr (ha hra) (q * n), ite_eq_right hrn, add_zero, hexp U hU hB j hj]
  let J := U.toList
  have hJ : J.toFinset = U := Finset.toList_toFinset U
  have hg : ∀ p ∈ J, T.Good p := fun p hp => hU p (Finset.mem_toList.mp hp)
  have hw : 2 ≤ (oddPart j \ J.toFinset).card := by
    rw [hJ]
    exact two_fresh_weight hn hq.1 hr.1 hne (hn' hq.1 hqa) (hn' hr.1 hra) (hu hqa) (hu hra)
  have hoff : ¬ oddPart j ⊆ J.toFinset := by
    intro h
    rw [Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.card_empty] at hw
    omega
  obtain ⟨c, hc⟩ := normalized_double (K := K) H J U.nodup_toList hg hw
  have he : dividedCoeff H i J U.nodup_toList hg j = 2 * c := by
    apply hinj
    rw [dividedCoeff_spec, rawNumerator_off i J (fun p hp => (hg p hp).1) hoff,
      map_mul, map_ofNat]
    exact hc
  have hθ := timesTheta_congr (dividedCoeff H i J U.nodup_toList hg) j
  have hh : (2 : O) ∣ dividedCoeff H i J U.nodup_toList hg j := ⟨c, he⟩
  obtain ⟨d, hd⟩ : (2 : O) ∣ ThetaCoeff.timesTheta (dividedCoeff H i J U.nodup_toList hg) j := by
    simpa only [sub_add_cancel] using dvd_add hθ hh
  rw [hd]
  exact m.mul_mem_right d hm2


end ZInQ.Manuscript.RC.EvenBudget

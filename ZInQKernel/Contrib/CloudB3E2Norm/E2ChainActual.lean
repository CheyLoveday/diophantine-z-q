import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
import ZInQKernel.Contrib.CloudB3RC53.Finiteness.TwoInSupportCompositum

/-!
# The actual chain inputs of the staged leaf

Manuscript `diophantine_zq.tex`, tex 2595–2603, 2678–2680, 2720–2741, 2847–2855, 2914–2936,
3455–3463, 4142–4146.

**`e2ChainInputsS_of_actual`** (definition) builds lane RC32's `E2ChainInputsS P t` from the
genuinely external inputs:

* the modular parametrization, the embedding, the identification `ℚ̄ ≃ K̄` and the PRINT
  (Cai–Chen–Liu, Theorem 2.15, with the full anchor) — `cp`, `emb`, `κ`, `print`;
* the address data: `St : RCSteps D` in the branch `¬ D.OddEmptyUnit` (the companion facts),
  `Fam.Admissible D.S D.kfin`, the primes of `2N` in `D.S` (`hS2N`), `r_{t+1} ∤ k` (`hrk`), the
  places above the primes `q` with `λ_q(x) = 1` in the stage support (`hQS0`), every index of the
  chain is the index of a step (`hpidx`), no step prime is `3` (`hQ3`), and good reduction outside
  the stage support (`hgood`; GLUE: Néron–Ogg–Shafarevich for the places outside `S₀ ⊇` the
  places of `N`).

The other fields are derived: `k < 0`, squarefree, `≡ 1 (mod 4)` from `RCSteps.companion`; the
base conductor `d = θ-conductor = r_{t+1} ∏_{λ_q(x) = 1} q`, positive, divisible by itself, prime to
`2 N D_K` (`hd2`), with its primes in the stage support (`hdS0`); the places above `2` in the
support from `E[2^∞]` rational over `K_{S₀}` (`h2_of_hasFullTwoTorsion_proof`); `hsep` from the
split pairs of the steps; `hq` (the step prime does not divide `6 d_i N D_K`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.ChainActual

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15Applied)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Manuscript.RC.CoefModules (acoefTop acoefTop_discrete)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageIsoA)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)

/-! ### Arithmetic helpers -/

/-- A prime dividing a chain conductor divides `d` or an earlier step prime (PROVED). -/
theorem prime_dvd_chainCond {q : ℕ} (hq : q.Prime) (d : ℕ) (ps : List ℕ) :
    ∀ j, q ∣ chainCond d ps j → q ∣ d ∨ ∃ m < j, q ∣ ps.getD m 1
  | 0, h => Or.inl h
  | j + 1, h => by
    rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
    · rcases prime_dvd_chainCond hq d ps j h1 with h2 | ⟨m, hm, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨m, Nat.lt_succ_of_lt hm, h2⟩
    · exact Or.inr ⟨j, Nat.lt_succ_self j, h1⟩

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- A place of residue cardinality `q` contains `q` (PROVED). -/
theorem natCast_mem_of_card {v : HeightOneSpectrum (𝓞 K)} {q : ℕ}
    (hc : Nat.card (𝓞 K ⧸ v.asIdeal) = q) : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact v.asIdeal.zero_mem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  have hfin : Finite (𝓞 K ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  rw [← hc, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

omit [NumberField K] in
/-- A place does not contain two distinct primes (PROVED). -/
theorem not_two_primes {v : HeightOneSpectrum (𝓞 K)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) (hqv : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * q = 1 := by
    refine ⟨Nat.gcdA p q, Nat.gcdB p q, ?_⟩
    have := Nat.gcd_eq_gcd_ab p q
    rw [hcop] at this
    push_cast at this
    linarith
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * p + b * q : ℤ) : 𝓞 K) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hqv)
  rwa [hab, Int.cast_one] at h1

/-! ### The constructor -/

section Constructor

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {G : GenuineFamilyMovingCharacter C.K ℓ Fam.Q}

attribute [local instance] acoefTop acoefTop_discrete stageIsoA

omit [(Ecurve ℓ).IsElliptic] in
/-- A prime coprime to `2 N |k|` when it divides neither (PROVED helper). -/
theorem coprime_two_N_disc {p : ℕ} (hp : p.Prime) {k : ℤ}
    (h2N : ¬ p ∣ 2 * newformLevel (Ecurve ℓ)) (hk : ¬ (p : ℤ) ∣ k) :
    Nat.Coprime p (2 * newformLevel (Ecurve ℓ) * k.natAbs) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact h2N h1
  · exact hk (Int.natCast_dvd.mpr h1)

/-- **The actual chain inputs of the staged leaf** (tex 2595–2603, 2678–2680, 2720–2741,
2847–2855, 2914–2936, 3455–3463, 4142–4146), from the external inputs:

* `cp`, `emb`, `κ`, `print` (definition and PRINT: Cai–Chen–Liu, Trans. AMS 370 (2018),
  Theorem 2.15, with the full anchor; tex 2914–2936);
* `St`, `hodd` (the companion facts of `RCSteps`, in the branch `¬ D.OddEmptyUnit`; tex
  2595–2603), `hAdm` (`Family.Admissible`, tex 2678–2680, 4234–4237);
* `hS2N` — the primes of `2N` lie in `D.S`: stated by the text (the fixed support "contains the
  primes of `2N`", tex 2678–2680, 4234–4237), not recorded in `RCData`;
* `hrk` — `r_{t+1} ∤ k`: stated by the text (admissibility of `d`, `r ∤ 2Nk`, tex 2920–2921;
  the moving primes are chosen outside the fixed support containing the primes of `k`, tex
  4268–4270); a formalization requirement here since `GoodPrime` does not record it;
* `hQS0` — the places above the primes `q` with `λ_q(x) = 1` lie in the stage support: stated by
  the text (the support `S₀` contains the primes of the conductor, tex 3455–3463); a formalization
  requirement of `StagedPresentation`, whose `S₀` is free beyond `Sr ⊆ S₀`;
* `hpidx` — every index of the chain is the index of a step: a formalization requirement (the
  text's chain has one index per unused prime, tex 4142–4146);
* `hQ3` — no unused (step) prime is `3`: a formalization requirement for the factor `6` of `hq`
  (the text's admissibility `q ∤ 6 d N D_K`, tex 2920–2921, is a condition on the step primes;
  with `q ≠ 2` from `hprime` it amounts to `q ≠ 3`);
* `hgood` — good reduction outside the stage support: GLUE (Néron–Ogg–Shafarevich, Silverman AEC
  VII.7.1; the support contains the primes above `N`, tex 2729–2741, 2836–2838).

Kind: definition. -/
def e2ChainInputsS_of_actual (P : StagedPresentation C D Fam x G.toFamily) (t : ℕ)
    (cp : CSTParam (Ecurve ℓ)) (emb : Qbar →ₐ[ℚ] ℂ) (κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K)
    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
    (St : RCSteps D) (hodd : ¬ D.OddEmptyUnit) (hAdm : Fam.Admissible D.S D.kfin)
    (hS2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ D.S)
    (hrk : ¬ ((G.r (t + 1) : ℕ) : ℤ) ∣ D.kfin)
    (hQS0 : ∀ q ∈ Fam.Q, Fam.lam q x = 1 → ∀ v : HeightOneSpectrum (𝓞 C.K),
      ((q : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S₀ (t + 1))
    (hpidx : ∀ p : P.ι, ∃ j < P.ps.length, P.pidx j = p) (hQ3 : ∀ q ∈ unusedAt Fam x, q ≠ 3)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ P.S₀ (t + 1) →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v) :
    E2ChainInputsS P t :=
  have hcomp := St.companion hodd
  have hk0 : D.kfin < 0 := hcomp.1
  have hksq : Squarefree D.kfin := hcomp.2.1
  have hk4 : D.kfin % 4 = 1 := hcomp.2.2.2.2.2.1
  have hdisc : discr C.K = D.kfin := discr_of_sqrt P.hr P.hgen hk0 hksq hk4
  have hr := G.r_prime (t + 1)
  { cp := cp
    emb := emb
    κ := κ
    print := print
    hk0 := hk0
    hksq := hksq
    hk4 := hk4
    d := thetaCond Fam x (G.r (t + 1))
    hd := Nat.pos_of_ne_zero (thetaCond_ne_zero Fam x hr P.hprime)
    hd2 := by
      rw [hdisc]
      refine Nat.Coprime.mul_left (coprime_two_N_disc hr (G.r_not_twoN (t + 1)) hrk) ?_
      refine Nat.Coprime.prod_left fun q hq => ?_
      have hqQ := Finset.mem_of_mem_filter q hq
      obtain ⟨hqp, -, hqS, -, -⟩ := hAdm q hqQ
      exact coprime_two_N_disc hqp (fun h => hqS (hS2N q hqp h)) (P.split q hqQ).1
    hfd := dvd_refl _
    hdS0 := by
      intro v hv
      have hv' : ((G.r (t + 1) : ℕ) : 𝓞 C.K) *
          ((∏ q ∈ Fam.Q.filter (fun q => Fam.lam q x = 1), q : ℕ) : 𝓞 C.K) ∈ v.asIdeal := by
        simpa [thetaCond, Nat.cast_mul] using hv
      rcases v.isPrime.mem_or_mem hv' with h1 | h1
      · apply P.hSr (t + 1)
        apply G.toFamily.Sr_r (t + 1)
        change (((G.r (t + 1) : ℕ) : ℤ) : 𝓞 C.K) ∈ v.asIdeal
        exact_mod_cast h1
      · rw [Nat.cast_prod] at h1
        obtain ⟨q, hq, hqv⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 h1
        exact hQS0 q (Finset.mem_of_mem_filter q hq) (Finset.mem_filter.1 hq).2 v hqv
    htwo := by
      have := P.full (t + 1)
      exact ZInQ.Contrib.CloudB3RC53.Finiteness.h2_of_hasFullTwoTorsion_proof
        ((Ecurve ℓ).baseChange C.K)
    hgood := hgood
    hsep := by
      intro i hi p c hp hmem
      obtain ⟨j, hj, rfl⟩ := hpidx p
      have hij : j ≠ i := fun h => hp (h ▸ rfl)
      have hsp := P.places (t + 1) j hj
      have hjmem : ((P.ps.getD j 1 : ℕ) : 𝓞 C.K) ∈ (P.pl (P.pidx j, c)).asIdeal := by
        cases c
        · exact natCast_mem_of_card hsp.card
        · exact natCast_mem_of_card hsp.card'
      have hne : P.ps.getD i 1 ≠ P.ps.getD j 1 := by
        rw [List.getD_eq_getElem P.ps 1 hi, List.getD_eq_getElem P.ps 1 hj]
        exact fun h => hij ((P.hnd.getElem_inj_iff).1 h).symm
      exact not_two_primes (P.ps_getD_prime hi) (P.ps_getD_prime hj) hne hmem hjmem
    hq := by
      intro i hi h
      have hqp := P.ps_getD_prime hi
      obtain ⟨hqQ, hun⟩ := mem_unusedAt.mp (P.mem_unused hi)
      obtain ⟨-, -, hqS, -, -⟩ := hAdm _ hqQ
      rw [hdisc] at h
      rcases (Nat.Prime.dvd_mul hqp).1 h with h1 | h1
      · rcases (Nat.Prime.dvd_mul hqp).1 h1 with h2 | h2
        · rcases (Nat.Prime.dvd_mul hqp).1 h2 with h3 | h3
          · -- `q ∣ 6`
            have h6 : P.ps.getD i 1 ∣ 2 * 3 := h3
            rcases (Nat.Prime.dvd_mul hqp).1 h6 with h4 | h4
            · exact (P.hprime _ hqQ).2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h4)
            · exact hQ3 _ (P.mem_unused hi) ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1 h4)
          · -- `q ∣ d_i`
            rcases prime_dvd_chainCond hqp _ _ i h3 with h4 | ⟨m, hm, h4⟩
            · rcases (Nat.Prime.dvd_mul hqp).1 h4 with h5 | h5
              · have := (Nat.prime_dvd_prime_iff_eq hqp hr).1 h5
                exact G.r_notQ (t + 1) (this ▸ hqQ)
              · obtain ⟨q', hq', h6⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 h5
                have hq'p := (P.hprime q' (Finset.mem_of_mem_filter q' hq')).1
                have heq := (Nat.prime_dvd_prime_iff_eq hqp hq'p).1 h6
                have h1' := (Finset.mem_filter.1 hq').2
                rw [← heq, hun] at h1'
                exact zero_ne_one h1'
            · have hmi : m < P.ps.length := lt_trans hm hi
              have hpm := P.ps_getD_prime hmi
              have heq := (Nat.prime_dvd_prime_iff_eq hqp hpm).1 h4
              rw [List.getD_eq_getElem P.ps 1 hi, List.getD_eq_getElem P.ps 1 hmi] at heq
              exact (ne_of_gt hm) ((P.hnd.getElem_inj_iff).1 heq)
        · -- `q ∣ N`
          exact hqS (hS2N _ hqp (h2.trans (dvd_mul_left _ _)))
      · -- `q ∣ D_K = k`
        exact (P.split _ hqQ).1 (Int.natCast_dvd.mpr h1) }

end Constructor

end ZInQ.Contrib.CloudB3E2.ChainActual

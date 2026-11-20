import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18Pin
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
import ZInQKernel.Contrib.CloudB3E1RingClass.GenuineMovingData

/-!
# Lane E2's classes of the actual Heegner points as a class provider

Manuscript `diophantine_zq.tex`: the actual anchored Heegner points and their norm relations
(tex 2914–2936), the finite character of `Δ_f` (tex 2847–2855), the Kummer classes as classes of
the presentation (tex 3080–3084, 3203–3215, 3471–3487) and the step identity of Lemma
`ex:arith-common-coordinate` (tex 4142–4194, 4157–4172), at a positive stage `t + 1`.

On lane RC32's actual presentation `A : ActualPresentation C D Fam x`
(`CommonCoordinate17Actual.lean`):

* `chainCond` (definition): the chain conductors `d_0 = d`, `d_{j+1} = d_j · ps[j]`;
  `classSupport` (definition): the support `S₀ ∪ {v ∣ d_j}` of the division points of `y_{d_j}`;
* **`E2ChainInputs A t`** (data): the inputs of lane E2's construction that do not follow from
  `A`: the PRINT, the base conductor with its admissibility, the support conditions on `S₀`
  (the primes of `2` and of bad reduction, the primes of `d`), the separation of the chain's
  places, the splitting of the step primes, and the ELLIOT `ThetaOfDelta f` with `f ∣ d`;
* derived from `A` and the inputs (PROVED): the positivity, divisibility and coprimality of the
  conductors, the support conditions of lane E2's `heegnerActual` at every `d_j`
  (`classSupport_subset`, `hm`, `hgood'`, `hpl`: the chain's places off `chainT pidx j` do not
  divide `d_j`, `cond_not_mem`), the admissibility of every step for the anchored datum
  (`hadmD`, `hsplitD`), and at every step the hypotheses of lane E2's `gx_step_heegner_at`:
  `SplitPlacesAt.above` from `A.places` (`habove`), `AnticyclotomicAt` from `A.movingConj`
  (`hanti`, through `alphaStage_conj` and `frobConjugatePlaces_proved`), and the places prime
  to the conductors (`hwd`);
* **`E2ChainInputs.g`** (definition): `g_j` = lane E2's `gx` of `heegnerActual … d_j` on the
  support `chainT pidx j`;
* **`E2ChainInputs.hG`** (PROVED): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the
  leaf's values at the stage, from `gx_step_heegner_at` and the junction `stepFactor_eq`
  (`z = α(Frob_{w₀})` is the leaf's `z`, by `actual_stageFrobInput`);
* **`E2ChainInputs.hloc`** (PROVED): the local lifts, lane E2's `exists_ux`;
* **`e2Provider A t I : StageClassesAt A (t + 1)`** (definition).

Kinds: definitions, data, PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.PrintsArith (Qbar HeegnerPointData CCLThm2_15Applied)
open ZInQ.Contrib.CloudB3E2.NormCochain (CSTParam FullAnchor ThetaOfDelta heegnerActual gx
  gx_step_heegner_at exists_ux stageIsoA eK alphaStage alphaShap hα_of_theta groupRingTop)
open ZInQ.Contrib.CloudB3E1RingClass (mem_primeTo_of_not_mem ringClassOrder_eq_conductorOrder)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop

/-! ### The chain conductors -/

/-- **The chain conductors** `d_0 = d`, `d_{j+1} = d_j · ps[j]` (with `ps[j] = 1` past the end of
`ps`), i.e. `d_j = d ∏_{j' < j} ps[j']` (tex 2914–2921, 4142–4146). Kind: definition. -/
def chainCond (d : ℕ) (ps : List ℕ) : ℕ → ℕ
  | 0 => d
  | j + 1 => chainCond d ps j * ps.getD j 1

/-- `d ∣ d_j` (tex 2914–2921). Kind: PROVED. -/
theorem dvd_chainCond (d : ℕ) (ps : List ℕ) : ∀ j, d ∣ chainCond d ps j
  | 0 => dvd_refl d
  | j + 1 => (dvd_chainCond d ps j).mul_right _

section E2Inputs

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b}

attribute [local instance] acoefTop acoefTop_discrete stageIsoA

/-- **The support of the division points of the `j`-th point** (tex 3471–3487): `S₀` together
with the primes dividing `d_j`. Kind: definition. -/
def classSupport (A : ActualPresentation C D Fam x) (d j : ℕ) :
    Set (HeightOneSpectrum (𝓞 C.K)) :=
  A.S₀ ∪ {v | ((chainCond d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}

omit [(Ecurve ℓ).IsElliptic] in
/-- The step primes are positive: primes for the steps, `1` past the end (tex 2678–2680).
Kind: PROVED. -/
theorem ActualPresentation.ps_getD_pos (A : ActualPresentation C D Fam x) (j : ℕ) :
    0 < A.ps.getD j 1 := by
  by_cases hj : j < A.ps.length
  · obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (A.mem_unused hj)
    exact (A.hprime _ hqQ).1.pos
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact one_pos

omit [(Ecurve ℓ).IsElliptic] in
/-- The step primes are primes (tex 2678–2680). Kind: PROVED. -/
theorem ActualPresentation.ps_getD_prime (A : ActualPresentation C D Fam x) {i : ℕ}
    (hi : i < A.ps.length) : (A.ps.getD i 1).Prime := by
  obtain ⟨hqQ, -⟩ := mem_unusedAt.mp (A.mem_unused hi)
  exact (A.hprime _ hqQ).1

/-- **The inputs of lane E2's construction of the classes at the stage `t + 1`** that do not
follow from the actual presentation (tex 2847–2855, 2914–2936, 3471–3487, 4142–4194). Each
field's kind and tex lines are in its docstring. Kind: definition (data). -/
structure E2ChainInputs (A : ActualPresentation C D Fam x) (t : ℕ) where
  /-- the modular parametrization data (definition; tex 2914–2917) -/
  cp : CSTParam (Ecurve ℓ)
  /-- the complex embedding of `ℚ̄` (definition; tex 2914–2917) -/
  emb : Qbar →ₐ[ℚ] ℂ
  /-- the identification `ℚ̄ ≃ K̄` (definition; tex 2914–2936) -/
  κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K
  /-- PRINT: Cai–Chen–Liu, Trans. AMS 370 (2018), Theorem 2.15, through the parametrization,
  with lane E2's full anchor (tex 2914–2936) -/
  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
  /-- the values of the moving character are injective on the finite quotient (definition;
  tex 2779–2785) -/
  hψ : Function.Injective (A.ψ (t + 1))
  /-- the base conductor (definition; tex 2914–2921) -/
  d : ℕ
  /-- it is positive (definition) -/
  hd : 0 < d
  /-- it is prime to `2 N D_K` (definition: admissibility; tex 2920–2921) -/
  hd2 : Nat.Coprime d (2 * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs)
  /-- its primes lie in `S₀` (definition; tex 3455–3463) -/
  hdS0 : ∀ v : HeightOneSpectrum (𝓞 C.K), (d : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S₀
  /-- the primes above `2` lie in `S₀` (definition; tex 2729–2741) -/
  htwo : ∀ v : HeightOneSpectrum (𝓞 C.K), (2 : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S₀
  /-- `E` has good reduction outside `S₀` (definition: `S₀` contains the primes above `N`;
  tex 2729–2741) -/
  hgood : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ A.S₀ →
    ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v
  /-- the places of the other indices do not lie above the step prime (definition: distinct
  indices carry the places of distinct primes; tex 4142–4146) -/
  hsep : ∀ i < A.ps.length, ∀ (p : A.ι) (c : Bool), p ≠ A.pidx i →
    ((A.ps.getD i 1 : ℕ) : 𝓞 C.K) ∉ (A.pl (p, c)).asIdeal
  /-- the step prime does not divide `6 d_i N D_K` (definition: admissibility;
  tex 2920–2921) -/
  hq : ∀ i < A.ps.length, ¬ A.ps.getD i 1 ∣
    6 * chainCond d A.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs
  /-- the step prime splits in `K` (definition; tex 2720–2722, 4142–4146) -/
  hsplit : ∀ i < A.ps.length, jacobiSym (discr C.K) (A.ps.getD i 1) = 1
  /-- the conductor of the finite character (definition; tex 2847–2855) -/
  f : ℕ
  /-- it is nonzero (definition) -/
  [hf : NeZero f]
  /-- ELLIOT: `θ = χ_h [π]` is a character of `Δ_f = Gal(H_f/K)` (lane E2's `ThetaOfDelta`;
  tex 2847–2855) -/
  hθ : ThetaOfDelta A.hS (Set.Subset.refl A.S) A.sh A.hs A.hs0 (A.π (t + 1)) f
  /-- `f ∣ d` (definition; tex 2847–2855) -/
  hfd : f ∣ d

namespace E2ChainInputs

variable {A : ActualPresentation C D Fam x} {t : ℕ} (I : E2ChainInputs A t)

attribute [local instance] E2ChainInputs.hf

omit [(Ecurve ℓ).IsElliptic] in
/-- The chain conductors are positive (tex 2914–2921). Kind: PROVED. -/
theorem chainCond_pos : ∀ j, 0 < chainCond I.d A.ps j
  | 0 => I.hd
  | j + 1 => Nat.mul_pos (chainCond_pos j) (A.ps_getD_pos j)

omit [(Ecurve ℓ).IsElliptic] in
/-- The chain conductors are prime to `2 N D_K` (tex 2920–2921). Kind: PROVED. -/
theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d A.ps j)
    (2 * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs)
  | 0 => I.hd2
  | j + 1 => by
    refine Nat.Coprime.mul_left (chainCond_coprime j) ?_
    by_cases hj : j < A.ps.length
    · refine (Nat.Prime.coprime_iff_not_dvd (A.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
      exact h.trans ⟨3 * chainCond I.d A.ps j, by ring⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
      exact Nat.coprime_one_left _

omit [(Ecurve ℓ).IsElliptic] in
/-- **The chain's places off the support do not divide the conductor** (PROVED from `hdS0`,
`hsep` and `A.hw`; tex 3471–3487): for `p ∉ chainT pidx j`, `d_j ∉ pl (p, c)`. -/
theorem cond_not_mem : ∀ (j : ℕ) (p : A.ι) (c : Bool), p ∉ chainT A.pidx j →
    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∉ (A.pl (p, c)).asIdeal
  | 0, p, c, _ => fun h => A.hw (p, c) (I.hdS0 _ h)
  | j + 1, p, c, hp => by
    have hp' : p ≠ A.pidx j ∧ p ∉ chainT A.pidx j := by
      simpa [chainT, not_or] using hp
    intro h
    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (A.pl (p, c)).asIdeal at h
    rw [Nat.cast_mul] at h
    rcases (A.pl (p, c)).isPrime.mem_or_mem h with h1 | h1
    · exact cond_not_mem j p c hp'.2 h1
    · by_cases hj : j < A.ps.length
      · exact I.hsep j hj p c hp'.1 h1
      · rw [List.getD_eq_default _ _ (not_lt.mp hj), Nat.cast_one] at h1
        exact (A.pl (p, c)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes dividing a chain conductor lie in the Selmer support (PROVED from `hdS0` and
`A.places`; tex 3455–3463). -/
theorem mem_S_of_cond : ∀ (j : ℕ) (v : HeightOneSpectrum (𝓞 C.K)),
    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S
  | 0, v, h => A.hS (I.hdS0 v h)
  | j + 1, v, h => by
    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h1 | h1
    · exact mem_S_of_cond j v h1
    · by_cases hj : j < A.ps.length
      · rcases (A.places j hj).above v.asIdeal v.isPrime h1 with h2 | h2
        · exact Set.mem_union_right _ ⟨(A.pidx j, false), (HeightOneSpectrum.ext h2).symm⟩
        · exact Set.mem_union_right _ ⟨(A.pidx j, true), (HeightOneSpectrum.ext h2).symm⟩
      · rw [List.getD_eq_default _ _ (not_lt.mp hj), Nat.cast_one] at h1
        exact absurd ((Ideal.eq_top_iff_one _).2 h1) v.isPrime.ne_top

omit [(Ecurve ℓ).IsElliptic] in
/-- The support of the division points lies in the Selmer support (PROVED). -/
theorem classSupport_subset (j : ℕ) : classSupport A I.d j ⊆ A.S := by
  rintro v (hv | hv)
  · exact A.hS hv
  · exact I.mem_S_of_cond j v hv

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes of `d_j` lie in the support (PROVED). -/
theorem hSd (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j :=
  fun _ hv => Or.inr hv

omit [(Ecurve ℓ).IsElliptic] in
/-- The primes of `2^{t+1}` lie in the support (PROVED from `htwo`). -/
theorem hm (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
    ((2 ^ (t + 1) : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j := by
  intro v hv
  rw [Nat.cast_pow, Nat.cast_ofNat] at hv
  exact Or.inl (I.htwo v (v.isPrime.mem_of_pow_mem _ hv))

omit [(Ecurve ℓ).IsElliptic] in
/-- `E` has good reduction outside the support (PROVED from `hgood`). -/
theorem hgood' (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ classSupport A I.d j →
    ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt ((Ecurve ℓ).baseChange C.K) v :=
  fun v hv => I.hgood v fun h => hv (Or.inl h)

omit [(Ecurve ℓ).IsElliptic] in
/-- No place of the chain off `chainT pidx j` lies in the support (PROVED from `cond_not_mem`
and `A.hw`). -/
theorem hpl (j : ℕ) : ∀ jj : A.ι × Bool, jj.1 ∉ chainT A.pidx j →
    (A.place jj).1 ∉ classSupport A I.d j := by
  rintro ⟨p, c⟩ hp (h | h)
  · exact A.hw (p, c) h
  · exact I.cond_not_mem j p c hp h

omit [(Ecurve ℓ).IsElliptic] in
/-- `f ∣ d_j` (PROVED). -/
theorem hfd_cond (j : ℕ) : I.f ∣ chainCond I.d A.ps j := I.hfd.trans (dvd_chainCond _ _ j)

/-! ### The anchored datum and the classes -/

/-- **The anchored datum of lane E2's step identity at the stage** (tex 2914–2936): the datum
`D` of `gx_step_heegner_at` for the actual presentation at the stage `t + 1`.
Kind: definition. -/
def datum : HeegnerPointData (Ecurve ℓ) :=
  letI := Classical.decEq (Places C.K A.S₀)
  Classical.choose (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1) A.sh
    A.hs A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ
    (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)

/-- The full anchor of the datum (tex 2914–2936). Kind: PROVED. -/
theorem anchor : FullAnchor (Ecurve ℓ) C.K I.cp I.emb I.κ I.datum :=
  letI := Classical.decEq (Places C.K A.S₀)
  (Classical.choose_spec (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1)
    A.sh A.hs A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ
    (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)).fst

/-- The conductors are prime to `N D_K` for the datum (PROVED). -/
theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d A.ps j) (I.datum.N * I.datum.DK.natAbs) := by
  rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) (I.chainCond_coprime j)

/-- **Every step is admissible for the datum** (PROVED from `hd2`, `hq` and the anchor's
`D.N = N`, `D.DK = D_K`; tex 2920–2921). -/
theorem hadmD {i : ℕ} (hi : i < A.ps.length) :
    I.datum.Admissible (chainCond I.d A.ps i) (A.ps.getD i 1) := by
  refine ⟨I.chainCond_pos i, ?_, A.ps_getD_prime hi, ?_⟩
  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
    exact I.chainCond_coprime i
  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
    exact I.hq i hi

/-- **Every step prime splits for the datum** (PROVED from `hsplit`; tex 2720–2722). -/
theorem hsplitD {i : ℕ} (hi : i < A.ps.length) : jacobiSym I.datum.DK (A.ps.getD i 1) = 1 := by
  rw [I.anchor.anchor.2.1]
  exact I.hsplit i hi

/-- **The global class of conductor `d_j`** (tex 3080–3084, 4157–4170): lane E2's `gx` of the
actual Heegner point `heegnerActual … d_j` on the support `chainT pidx j`, at the stage `t + 1`.
Kind: definition. -/
def g (j : ℕ) : (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).X 1 :=
  letI := Classical.decEq (Places C.K A.S₀)
  haveI : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
  gx A.hS A.hS (Set.Subset.refl A.S) ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh A.hs A.hs0
    (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk (StageRing (t + 1)) A.place
    (heegnerActual (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1) A.sh A.hs A.hs0
      (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
      (I.hm j) (I.hgood' j)
      (hα_of_theta A.hS (Set.Subset.refl A.S) A.sh A.hs A.hs0 (A.π (t + 1))
        (I.classSupport_subset j) I.f I.hθ (I.hfd_cond j) (I.hSd j)) (I.hpl j))

/-! ### The step identities -/

omit [(Ecurve ℓ).IsElliptic] in
/-- **The places of a step are anticyclotomic for the stage character** (PROVED from
`A.movingConj`; tex 2778–2796, 4171): `α(Frob_{w₁}) = α(Frob_{w₀})⁻¹`. -/
theorem hanti {i : ℕ} (hi : i < A.ps.length) :
    AnticyclotomicAt (alphaStage (t + 1) A.sh A.hs A.hs0 (A.π (t + 1)) (A.ψ (t + 1)))
      (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
      (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true))) := by
  have hκh : A.Cc.κ ((Fam.h x : ℤ) : C.K) = ((Fam.h x : ℤ) : C.K) := map_intCast _ _
  obtain ⟨g, hg⟩ := frobConjugatePlaces_proved A.S A.Cc
    (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
    (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true))) (A.places i hi).conj
  exact anticyclotomicAt_of_conj A.Cc (alphaStage_conj A.Cc A.sh A.hs A.hs0 hκh (A.π (t + 1))
    (t + 1) (A.ψ (t + 1)) (A.movingConj (t + 1))) hg

omit [(Ecurve ℓ).IsElliptic] in
/-- **The places of a step are prime to the conductors** (PROVED from `cond_not_mem`, `A.hnew`
and lane E1's `mem_primeTo_of_not_mem`; tex 2914–2936). -/
theorem hwd {i : ℕ} (hi : i < A.ps.length) [NeZero (chainCond I.d A.ps i)] :
    ∀ w ∈ [newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)),
      newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true))],
      ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
      w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
        (CST.conductorOrder C.K (chainCond I.d A.ps i)).conductorModulus ∧
      w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d A.ps i)
          (NeZero.ne _)).conductorModulus := by
  intro w hw
  have hnot : ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact I.cond_not_mem i _ _ (A.hnew i hi)
    · exact I.cond_not_mem i _ _ (A.hnew i hi)
  have hJ := mem_primeTo_of_not_mem (chainCond I.d A.ps i) (NeZero.ne _) w.1 hnot
  refine ⟨hnot, ?_, hJ⟩
  rw [← ringClassOrder_eq_conductorOrder]
  exact hJ

/-- **The junction: lane E2's point factor at the stage is the leaf's** (PROVED; tex 3915,
4158–4172, 4176–4184): `a_q`, `z = α(Frob_{w₀})` and `z⁻¹` pushed to `StageRing (t + 1)` are the
leaf's `a`, `z`, `zi` at the stage (`actual_stageFrobInput` at the first place of the step). -/
theorem stepFactor_eq {i : ℕ} (hi : i < A.ps.length) :
    pointFactor (((Ecurve ℓ).LFunction (A.ps.getD i 1) : ℤ) : StageRing (t + 1))
        ((eK (StageRing (t + 1)) (t + 1)).symm
          (alphaStage (t + 1) A.sh A.hs A.hs0 (A.π (t + 1)) (A.ψ (t + 1))
            (urFrobElt C.K (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))) :
              Acoef (t + 1)))
        ((eK (StageRing (t + 1)) (t + 1)).symm
          (((alphaStage (t + 1) A.sh A.hs A.hs0 (A.π (t + 1)) (A.ψ (t + 1))
            (urFrobElt C.K (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))))⁻¹ :
              (Acoef (t + 1))ˣ) : Acoef (t + 1))) =
      pointFactor (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).a i)
        (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i)
        (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i) := by
  obtain ⟨⟨_, h1⟩, -⟩ := actual_stageFrobInput A (t + 1) hi
  set u := alphaStage (t + 1) A.sh A.hs A.hs0 (A.π (t + 1)) (A.ψ (t + 1))
    (urFrobElt C.K (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))) with hu
  have hz : (eK (StageRing (t + 1)) (t + 1)).symm (u : Acoef (t + 1)) =
      ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i := h1.charValue
  have hleaf : ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i *
      ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i = 1 := by
    change stageMk (t + 1) ((zAt Fam x (A.ps.getD i 1) : Lambdaˣ) : Lambda) *
      stageMk (t + 1) (((zAt Fam x (A.ps.getD i 1))⁻¹ : Lambdaˣ) : Lambda) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : (eK (StageRing (t + 1)) (t + 1)).symm (u : Acoef (t + 1)) *
      (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hzi : (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1)) =
      ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i := by
    rw [hz] at hinv
    calc _ = ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i *
          (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i *
            (eK (StageRing (t + 1)) (t + 1)).symm ((u⁻¹ : (Acoef (t + 1))ˣ) : Acoef (t + 1))) := by
          rw [← mul_assoc, mul_comm _ (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i),
            hleaf, one_mul]
      _ = _ := by rw [hinv, mul_one]
  have ha : (((Ecurve ℓ).LFunction (A.ps.getD i 1) : ℤ) : StageRing (t + 1)) =
      ((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).a i := by
    change _ = stageMk (t + 1) ((apE ℓ (A.ps.getD i 1) : ℤ) : Lambda)
    rw [map_intCast]
    rfl
  rw [ha, hz, hzi]

/-- **The global identities of the chain from lane E2's step identity** (PROVED; tex 2914–2936,
4157–4172): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the leaf's values at the
stage, from `gx_step_heegner_at` at the two places of the step (`habove` from `A.places`,
`hanti`, `hwd`) and the junction `stepFactor_eq`. -/
theorem hG : ∀ i < A.ps.length,
    ∃ bG : (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).X 0,
      I.g (i + 1) = pointFactor (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).a i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).z i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i) • I.g i +
        (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).d 0 1 rfl bG := by
  intro i hi
  let _ := Classical.decEq (Places C.K A.S₀)
  have : NeZero (chainCond I.d A.ps i) := ⟨(I.chainCond_pos i).ne'⟩
  have : NeZero (A.ps.getD i 1) := ⟨(A.ps_getD_pos i).ne'⟩
  obtain ⟨hA, -, hall⟩ := Classical.choose_spec (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS
    (Set.Subset.refl A.S) (t + 1) A.sh A.hs A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1))
    (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)
  obtain ⟨bG, hbG⟩ := hall (I.hadmD hi) (I.hsplitD hi) (Tp := chainT A.pidx i) (p := A.pidx i)
    (I.classSupport_subset i) (I.classSupport_subset (i + 1)) (I.hSd i) (I.hSd (i + 1)) (I.hm i)
    (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.f I.hθ (I.hfd_cond i) (I.hpl i)
    (I.hpl (i + 1)) (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
    (newPlace (A.place (A.pidx i, true)) (A.hwp (A.pidx i, true))) (A.places i hi).above
    (hanti hi) (I.hwd hi)
  refine ⟨bG, ?_⟩
  rw [← stepFactor_eq hi]
  exact hbG

/-- **The local lifts of the classes** (PROVED: lane E2's `exists_ux`; tex 3471–3487,
4169–4171). -/
theorem hloc (j : ℕ) :
    ∃ u : (piCx (presCondS C.K A.S₀ A.S (StageRing (t + 1)) (actualM A (t + 1))
        (actualConds A (t + 1)) A.place (actualX A (t + 1)) (actualEU A (t + 1))
        (chainT A.pidx j)).U).X 1,
      (piMap (presCondS C.K A.S₀ A.S (StageRing (t + 1)) (actualM A (t + 1))
        (actualConds A (t + 1)) A.place (actualX A (t + 1)) (actualEU A (t + 1))
        (chainT A.pidx j)).i).f 1 1 rfl u =
      (resS (StageRing (t + 1)) (GKS C.K A.S) (presGv C.K A.S₀ A.S A.place)
        (presLoc C.K A.S₀ A.S A.place) (actualM A (t + 1))).f 1 1 rfl (I.g j) := by
  let _ := Classical.decEq (Places C.K A.S₀)
  have : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
  have : ∀ jj : A.ι × Bool, ContinuousSMul (GUr C.K (A.place jj).1)
      (urRep (MonoidAlgebra ℤ (A.Dg (t + 1)))
        (ZInQ.Contrib.CloudB3E2.NormCochain.shapMod₀ ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh
          A.hs A.hs0 (A.π (t + 1))) (newPlace (A.place jj) (A.hwp jj))).V := fun jj =>
    urRep_continuousSMul (MonoidAlgebra ℤ (A.Dg (t + 1)))
      (ZInQ.Contrib.CloudB3E2.NormCochain.shapMod₀ ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh A.hs
        A.hs0 (A.π (t + 1))) (newPlace (A.place jj) (A.hwp jj))
  exact exists_ux A.hS A.hS (Set.Subset.refl A.S) ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh A.hs
    A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
    (StageRing (t + 1)) A.place A.hwp (actualEU A (t + 1)) (actualEU_i A (t + 1))
    (heegnerActual (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1) A.sh A.hs A.hs0
      (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
      (I.hm j) (I.hgood' j)
      (hα_of_theta A.hS (Set.Subset.refl A.S) A.sh A.hs A.hs0 (A.π (t + 1))
        (I.classSupport_subset j) I.f I.hθ (I.hfd_cond j) (I.hSd j)) (I.hpl j))

end E2ChainInputs

/-- **Lane E2's classes of the actual Heegner points as a class provider at the stage `t + 1`**
(tex 2914–2936, 3080–3084, 4142–4194, 4157–4172): `g_j` = lane E2's `gx` of the actual Heegner
point of conductor `d_j` on the support `chainT pidx j`, with the global identities from
`gx_step_heegner_at` at the leaf's values and the local lifts from `exists_ux`.
Kind: definition. -/
def e2Provider (A : ActualPresentation C D Fam x) (t : ℕ) (I : E2ChainInputs A t) :
    StageClassesAt A (t + 1) where
  g := I.g
  hG := I.hG
  hloc j _ := I.hloc j

end E2Inputs

end ZInQ.Manuscript.RC.Wiring

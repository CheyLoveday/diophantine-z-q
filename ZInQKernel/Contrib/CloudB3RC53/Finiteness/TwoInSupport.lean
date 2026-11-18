import ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness
import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.CharP.Two
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Inflation

/-!
# RC53 finiteness: the places above `2` lie in the support, from full `2`-power torsion

Several finiteness and division-point statements take the hypothesis

  `h2 : ∀ v, (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S`

that the support `S` contains every place above `2`. Classically it follows from full `2`-power
torsion over `K_S` (`HasFullTwoTorsion K S W`, i.e. `E[2^n] ⊆ E(K_S)` for all `n`). The Weil
pairing puts a primitive `2^n`-th root of unity in `K_S` for every `n` (Silverman, *The Arithmetic
of Elliptic Curves*, III.8.1.1). The field `K(μ_{2^∞})` is ramified above `2` with unbounded
ramification index, since `2` is totally ramified in `ℚ(μ_{2^n})` with index `2^(n-1)`, while
`e(v | 2) ≤ [K : ℚ]`. So no place above `2` is unramified in `K_S`, i.e. every such place lies
in `S`.

## Results

* `twoPowRoots_of_hasFullTwoTorsion` (`PROVED`): `HasFullTwoTorsion K S W` gives a primitive
  `2^n`-th root of unity in `K_S` for every `n` (`hasRootsOfUnity_of_fullTorsion`, through the
  Weil pairing of the vendored Tau Ceti library).
* `TwoPowerRootsRamified` (the ramification step, proved below): if `K_S` contains a primitive
  `2^n`-th root of unity for every `n`, then `S` contains every place above `2`.
* `h2_of_hasFullTwoTorsion` (`PROVED` from `TwoPowerRootsRamified`): the hypothesis `h2`.
* The consumers with `h2` replaced by full `2`-power torsion and `TwoPowerRootsRamified`:
  `moduleFinite_compactKummer_homology_of_ramified`, `kummerCohomologyFinite_of_prints_of_ramified`,
  `stageSelmer_residualCohomologyFinite_of_ramified` and
  `globalDivisionPointsInSupport_of_goodReduction_of_ramified`. The other variants with an `h2`
  argument take `h2_of_hasFullTwoTorsion hR W` the same way.
* `ecurve_baseChange_eq_curveEll` (`PROVED`): the base change of `E_ℓ` to `K` is
  `curveEll (algebraMap (𝓞 K) K ℓ)`, so `globalDivisionPointsInSupport_curveEll_of_integer`
  applies to the stage curve (`globalDivisionPointsInSupport_ecurve_of_integer`).
* Fragments of the ramification step (`PROVED`): `one_sub_mem_of_pow_two_pow_eq_one` (`1 − μ` lies
  in every prime containing `2`, for a `2`-power root of unity `μ`), `two_eq_prod_one_sub`
  (`2 = ∏ (1 − μ')` over the primitive `2^(n+1)`-th roots of unity) and `two_mem_pow_of_primitive`
  (`2 ∈ Q ^ (2^n)` for a prime `Q` containing `2` in a domain with a primitive `2^(n+1)`-th root).

## The ramification step at a finite level

* `mem_of_isPrimitiveRoot_of_isUnramifiedOutside` (`PROVED`): let `L/K` be finite and unramified
  outside `S`, containing a primitive `2^(n+1)`-th root of unity, with `[K : ℚ] < 2^n`. Then `S`
  contains every place above `2`. At a prime `P` of `𝓞_L` above `v ∉ S`: `2 ∈ P ^ (2^n)` by the
  fragments, so `e(P | 2) ≥ 2^n` (`ramificationIdx_eq_multiplicity`); but
  `e(P | 2) = e(v | 2) e(P | v) = e(v | 2) ≤ [K : ℚ]` (`ramificationIdx_tower`,
  `sum_ramification_inertia_eq_finrank`).
* `FiniteUnramifiedSupport` (b2, proved below): every element of `K_S` lies in a finite subextension
  unramified outside `S`. `K_S` is the supremum of such subextensions, so this needs the
  compositum of two extensions unramified outside `S` to be unramified outside `S`.
* `twoPowerRootsRamified_of_finiteUnramifiedSupport`,
  `h2_of_hasFullTwoTorsion_of_finiteUnramifiedSupport` (`PROVED` from (b2)): the ramification
  step and `h2`.

## (b2) from the compositum statement

* `isUnramifiedOutside_bot` (`PROVED`): `K` itself is unramified outside every `S`.
* `UnramifiedOutsideSup` (ii, proved below): the compositum of two finite normal subextensions
  unramified outside `S` is unramified outside `S`.
* `finiteUnramifiedSupport_of_sup` (`PROVED` from (ii)): with (ii) the finite normal
  subextensions unramified outside `S` form a nonempty directed family, so every element of their
  supremum `K_S` lies in one of them (`IntermediateField.coe_iSup_of_directed`).
* `h2_of_hasFullTwoTorsion_of_sup` (`PROVED` from (ii)).

## Fragments of (ii)

The classical proof of (ii): for a prime `Q` of `𝓞_M`, `M = L₁ ⊔ L₂` (finite Galois over `K`),
above `v ∉ S`, an element `σ` of the inertia group of `Q` in `Gal(M/K)` restricts to the inertia
group of `Q ∩ 𝓞_{L_i}` in `Gal(L_i/K)`, which is trivial (Tau Ceti's
`Ideal.isUnramifiedAt_iff_inertia_eq_bot`); so `σ` is trivial on `L₁` and on `L₂`, hence `σ = 1`,
and `M` is unramified at `Q`.
* `algEquiv_sup_eq_one` (`PROVED`): an automorphism of `L₁ ⊔ L₂` trivial on `L₁` and on `L₂` is
  the identity.
* `map_mem_inertia_comap` (`PROVED`): inertia restricts into inertia along any ring map compatible
  with a group homomorphism.

## (ii) proved, and `h2` unconditionally

* `inertia_eq_bot_of_isUnramifiedOutside`, `fix_of_mem_inertia` (`PROVED`): the instantiation for
  rings of integers of intermediate fields of `K̄`, with the restriction
  `(σ.liftNormal K̄).restrictNormal L_i` and the map `𝓞_{L_i} → 𝓞_M`.
* `unramifiedOutsideSup_proof`, `finiteUnramifiedSupport_proof`, `twoPowerRootsRamified_proof`
  (`PROVED`).
* `h2_of_hasFullTwoTorsion_proof` (`PROVED`): `h2` from `HasFullTwoTorsion K S W` alone.

Classification: `PROVED`. The propositions `TwoPowerRootsRamified`, `FiniteUnramifiedSupport`
and `UnramifiedOutsideSup` are proved (`*_proof`); `h2` follows from full `2`-power torsion.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Finiteness

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules (FullTorsion HasRootsOfUnity hasRootsOfUnity_of_fullTorsion
  curveEll curveEll_coeffs)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)

/-! ### Roots of unity from full `2`-power torsion -/

/-- **Primitive `2^n`-th roots of unity in `K_S`** (`PROVED`), from full `2`-power torsion over
`K_S`, through the Weil pairing. -/
theorem twoPowRoots_of_hasFullTwoTorsion {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
    [h : HasFullTwoTorsion K S W] (n : ℕ) : HasRootsOfUnity K S (2 ^ n) :=
  hasRootsOfUnity_of_fullTorsion K S W (2 ^ n) (h.full n)

/-- **The ramification step** (classical): if `K_S` contains a primitive `2^n`-th root of unity
for every `n`, then `S` contains every place above `2`. The field `K(μ_{2^∞})` has unbounded
ramification above `2`: `2` is totally ramified in `ℚ(μ_{2^n})` with index `2^(n-1)`
(`IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`), while `e(v | 2) ≤ [K : ℚ]`.
Proved in `twoPowerRootsRamified_proof`, from `FiniteUnramifiedSupport`
(`twoPowerRootsRamified_of_finiteUnramifiedSupport`). -/
def TwoPowerRootsRamified : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))),
    (∀ n : ℕ, HasRootsOfUnity K S (2 ^ n)) →
      ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S

/-- **`h2` from full `2`-power torsion** (`PROVED` from `TwoPowerRootsRamified`). -/
theorem h2_of_hasFullTwoTorsion (hR : TwoPowerRootsRamified) {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
    [HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  hR K S (twoPowRoots_of_hasFullTwoTorsion W)

/-! ### The consumers, with `h2` replaced by full `2`-power torsion -/

section Consumers

open ZInQ.Contrib.RC53Assist.Finiteness ZInQ.Contrib.RC53Assist.ResidualFiniteness
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC53Assist.CentralKummer (compactKummerComplex)
open ZInQ.Manuscript.RC53Assist.CentralUniversal

/-- `moduleFinite_compactKummer_homology` without `h2` (`PROVED` from `TwoPowerRootsRamified`
and the finiteness prints). -/
theorem moduleFinite_compactKummer_homology_of_ramified (hR : TwoPowerRootsRamified)
    {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness) (hS : S.Finite) (n : ℤ) :
    Module.Finite ℤ_[2] ((compactKummerComplex S W hFull).homology n) :=
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  moduleFinite_compactKummer_homology S W hFull hloc hglob hS (h2_of_hasFullTwoTorsion hR W) n

/-- `kummerCohomologyFinite_of_prints` without `h2` (`PROVED` from `TwoPowerRootsRamified` and the
finiteness prints). -/
theorem kummerCohomologyFinite_of_prints_of_ramified (hR : TwoPowerRootsRamified) (ℓ : ℕ) (k : ℤ)
    [(Ecurve ℓ).IsElliptic] (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
    (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness) (hS : S.Finite) :
    ZInQ.Manuscript.RC53Assist.CentralUniversal.KummerCohomologyFinite ℓ k S hFull :=
  have : HasFullTwoTorsion (QuadraticField k) S ((Ecurve ℓ).baseChange (QuadraticField k)) :=
    ⟨hFull⟩
  kummerCohomologyFinite_of_prints ℓ k S hFull hloc hglob hS
    (h2_of_hasFullTwoTorsion hR ((Ecurve ℓ).baseChange (QuadraticField k)))

/-- `stageSelmer_residualCohomologyFinite` without `h2` (`PROVED` from `TwoPowerRootsRamified`
and the finiteness prints), for a curve with full `2`-power torsion over `K_S`. -/
theorem stageSelmer_residualCohomologyFinite_of_ramified (hR : TwoPowerRootsRamified)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W] (i : ℕ) [NeZero i]
    (α : GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
    [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α]
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness) (hSfin : S.Finite)
    (Δ : GaloisLocalConditions K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (ZInQ.Manuscript.RC.CoefModules.Mcoef K S W i α))
    (hΔ : ∀ v, ResidualCohomologyFinite (Δ.U v)) :
    ResidualCohomologyFinite (selCx (galoisSelData K S
      (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (ZInQ.Manuscript.RC.CoefModules.Mcoef K S W i α) Δ)) :=
  stageSelmer_residualCohomologyFinite W i α hloc hglob hSfin (h2_of_hasFullTwoTorsion hR W) Δ hΔ

/-- `globalDivisionPointsInSupport_of_goodReduction` without `h2` (`PROVED` from
`TwoPowerRootsRamified`), for a curve with full `2`-power torsion over `K_{S₀}`. -/
theorem globalDivisionPointsInSupport_of_goodReduction_of_ramified (hR : TwoPowerRootsRamified)
    {K : Type} [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
    {S0 : Set (HeightOneSpectrum (𝓞 K))} [HasFullTwoTorsion K S0 W]
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S0 →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt W v) (i : ℕ) :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport
      (S0 := S0) W i :=
  ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_of_goodReduction W
    (h2_of_hasFullTwoTorsion hR W) hgood i

end Consumers

/-! ### The stage curve as `curveEll` -/

/-- **`E_ℓ` over `K` is `curveEll ℓ`** (`PROVED`): both are `y² = x³ + 2ℓ x² − 3ℓ² x`. -/
theorem ecurve_baseChange_eq_curveEll (K : Type) [Field K] [NumberField K] (ℓ : ℕ) :
    (Ecurve ℓ).baseChange K = curveEll (algebraMap (𝓞 K) K (ℓ : 𝓞 K)) := by
  rw [curveEll_coeffs, map_natCast]
  simp only [Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    map_zero, map_mul, map_pow, map_neg, map_ofNat, map_natCast]

/-- **Division points and full torsion for the stage curve** (`PROVED`):
`globalDivisionPointsInSupport_curveEll_of_integer` for `(Ecurve ℓ).baseChange K`. -/
theorem globalDivisionPointsInSupport_ecurve_of_integer {K : Type} [Field K] [NumberField K]
    [DecidableEq K] {S0 : Set (HeightOneSpectrum (𝓞 K))} {ℓ : ℕ} (hℓ0 : ℓ ≠ 0)
    (hS0 : ∀ v : HeightOneSpectrum (𝓞 K), 6 * (ℓ : 𝓞 K) ∈ v.asIdeal → v ∈ S0) (i : ℕ) :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport
        (S0 := S0) ((Ecurve ℓ).baseChange K) i ∧
      FullTorsion K S0 ((Ecurve ℓ).baseChange K) (2 ^ i) := by
  rw [ecurve_baseChange_eq_curveEll K ℓ]
  exact ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_curveEll_of_integer
    (Nat.cast_ne_zero.2 hℓ0) hS0 i

/-! ### Fragments of the ramification step -/

/-- **`1 − μ ∈ Q`** (`PROVED`) for a `2`-power root of unity `μ` and a prime `Q` containing `2`. -/
theorem one_sub_mem_of_pow_two_pow_eq_one {R : Type*} [CommRing R] {Q : Ideal R} [Q.IsPrime]
    (h2 : (2 : R) ∈ Q) {μ : R} {n : ℕ} (hμ : μ ^ (2 ^ n) = 1) : 1 - μ ∈ Q := by
  have h2' : (2 : R ⧸ Q) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk Q) 2]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have : CharP (R ⧸ Q) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
  have h := sub_pow_char_pow (R := R ⧸ Q) (p := 2) 1 (Ideal.Quotient.mk Q μ) (n := n)
  rw [one_pow, ← map_pow, hμ, map_one, sub_self] at h
  exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h

/-- **`2 = ∏ (1 − μ')`** (`PROVED`) over the primitive `2^(n+1)`-th roots of unity, in a domain
containing one. -/
theorem two_eq_prod_one_sub {R : Type*} [CommRing R] [IsDomain R] {μ : R} {n : ℕ}
    (hμ : IsPrimitiveRoot μ (2 ^ (n + 1))) :
    (2 : R) = ∏ μ' ∈ primitiveRoots (2 ^ (n + 1)) R, (1 - μ') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Polynomial.eval_one_cyclotomic_prime_pow (R := R) (p := 2) n
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hμ, Polynomial.eval_prod] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [h]
  norm_num

/-- **`2 ∈ Q ^ (2 ^ n)`** (`PROVED`) for a prime `Q` containing `2` in a domain with a primitive
`2^(n+1)`-th root of unity. -/
theorem two_mem_pow_of_primitive {R : Type*} [CommRing R] [IsDomain R] {Q : Ideal R} [Q.IsPrime]
    (h2 : (2 : R) ∈ Q) {μ : R} {n : ℕ} (hμ : IsPrimitiveRoot μ (2 ^ (n + 1))) :
    (2 : R) ∈ Q ^ (2 ^ n) := by
  have hcard : (primitiveRoots (2 ^ (n + 1)) R).card = 2 ^ n := by
    rw [hμ.card_primitiveRoots, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  rw [two_eq_prod_one_sub hμ, ← hcard, ← Finset.prod_const]
  refine Ideal.prod_mem_prod fun μ' hμ' => ?_
  have hpow : μ' ^ (2 ^ (n + 1)) = 1 :=
    ((mem_primitiveRoots (by positivity)).1 hμ').pow_eq_one
  exact one_sub_mem_of_pow_two_pow_eq_one h2 hpow


/-! ### The ramification step at a finite level, and its reduction to (b2) -/

section Finite

open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside)

/-- `(2) ⊆ ℤ` is prime (`PROVED`). -/
theorem span_two_isPrime : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two

/-- A prime containing `2` lies over `(2) ⊆ ℤ` (`PROVED`). -/
theorem liesOver_span_two {A : Type*} [CommRing A] [IsDomain A] [Algebra ℤ A]
    (P : Ideal A) [P.IsPrime] (h2 : (2 : A) ∈ P) : P.LiesOver (Ideal.span {(2 : ℤ)}) := by
  have : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two |>.isMaximal (by simp)
  refine ⟨(this.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_)⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simpa using h2

/-- **No unramified place above `2` in a field containing `μ_{2^(n+1)}`** (`PROVED`). Let `L/K` be
finite and unramified outside `S`, containing a primitive `2^(n+1)`-th root of unity with
`[K : ℚ] < 2^n`. Then `S` contains every place above `2`. -/
theorem mem_of_isPrimitiveRoot_of_isUnramifiedOutside {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] (hL : IsUnramifiedOutside K S L) {n : ℕ}
    (hn : Module.finrank ℚ K < 2 ^ n) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (n + 1)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : (2 : 𝓞 K) ∈ v.asIdeal) : v ∈ S := by
  by_contra hvS
  have hU := (RankCounts.KummerS.isUnramifiedOutside_iff K S L).1 hL v hvS
  have hU' := Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.1 hU
  have : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨P, hPmax, hPlo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have he1 : P.ramificationIdx (𝓞 K) = 1 := hU' P hPlo
  have h2P : (2 : 𝓞 L) ∈ P := by
    have h : (2 : 𝓞 K) ∈ P.under (𝓞 K) := Ideal.over_def P v.asIdeal ▸ hv
    rw [Ideal.under, Ideal.mem_comap, map_ofNat] at h
    exact h
  have hlo2 : P.LiesOver (Ideal.span {(2 : ℤ)}) := liesOver_span_two P h2P
  have hvlo2 : v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := liesOver_span_two v.asIdeal hv
  have htower := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P
  rw [he1, mul_one] at htower
  have hmap : (Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 L)) = Ideal.span {(2 : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
  have hmap0 : (Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  have hpow : (2 : 𝓞 L) ∈ P ^ (2 ^ n) :=
    two_mem_pow_of_primitive h2P hζ.toInteger_isPrimitiveRoot
  have hdvd : P ^ (2 ^ n) ∣ (Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 L)) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hpow
  have hlow : 2 ^ n ≤ P.ramificationIdx ℤ := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(2 : ℤ)}) P hmap0]
    exact (Ideal.finiteMultiplicity hPmax.ne_top hmap0).le_multiplicity_of_pow_dvd hdvd
  have : (Ideal.span {(2 : ℤ)}).IsMaximal := span_two_isPrime.isMaximal (by simp)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(2 : ℤ)}) (𝓞 K)
  have hv' : v.asIdeal ∈ (Ideal.span {(2 : ℤ)}).primesOver (𝓞 K) := ⟨inferInstance, hvlo2⟩
  have hle : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ ≤ Module.finrank ℤ (𝓞 K) := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun q : (Ideal.span {(2 : ℤ)}).primesOver (𝓞 K) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨v.asIdeal, hv'⟩)
  have hf := Ideal.inertiaDeg_pos (R := ℤ) v.asIdeal
  rw [RingOfIntegers.rank] at hle
  have : v.asIdeal.ramificationIdx ℤ ≤ Module.finrank ℚ K :=
    le_trans (Nat.le_mul_of_pos_right _ hf) hle
  omega

/-- **(b2) Every element of `K_S` lies in a finite subextension unramified outside `S`**
(classical). `K_S` is the supremum of the finite Galois subextensions unramified outside `S`;
an element of the supremum lies in a finite compositum of them, which is again unramified
outside `S`. Proved in `finiteUnramifiedSupport_proof`. -/
def FiniteUnramifiedSupport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ZInQ.Manuscript.RC.CoefModules.KS K S),
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
      IsUnramifiedOutside K S L ∧ (x : AlgebraicClosure K) ∈ L

/-- **The ramification step from (b2)** (`PROVED` from `FiniteUnramifiedSupport`). -/
theorem twoPowerRootsRamified_of_finiteUnramifiedSupport (h : FiniteUnramifiedSupport) :
    TwoPowerRootsRamified := by
  intro K _ _ S hroots v hv
  obtain ⟨ζ, hζ⟩ := hroots ((Module.finrank ℚ K) + 1)
  obtain ⟨L, hfin, hU, hmem⟩ := h K S ζ
  have : FiniteDimensional K L := hfin
  have hζK : IsPrimitiveRoot (ζ : AlgebraicClosure K) (2 ^ ((Module.finrank ℚ K) + 1)) :=
    hζ.map_of_injective (f := (ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S).val)
      Subtype.val_injective
  have hζL : IsPrimitiveRoot (⟨ζ, hmem⟩ : L) (2 ^ ((Module.finrank ℚ K) + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := L.val) (by exact hζK) Subtype.val_injective
  exact mem_of_isPrimitiveRoot_of_isUnramifiedOutside L hU
    (Nat.lt_two_pow_self) hζL v hv

/-- **`h2` from full `2`-power torsion and (b2)** (`PROVED` from `FiniteUnramifiedSupport`). -/
theorem h2_of_hasFullTwoTorsion_of_finiteUnramifiedSupport (h : FiniteUnramifiedSupport)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic]
    [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  h2_of_hasFullTwoTorsion (twoPowerRootsRamified_of_finiteUnramifiedSupport h) W

end Finite

/-! ### (b2) from the compositum statement -/

section Compositum

open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside unramifiedOutside UnrGal
  unramifiedOutside_eq_iSup_subtype)

/-- **`K` itself is unramified outside every `S`** (`PROVED`): `𝓞_K → 𝓞_⊥` is surjective, hence
formally unramified. -/
theorem isUnramifiedOutside_bot (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsUnramifiedOutside K S (⊥ : IntermediateField K (AlgebraicClosure K)) := by
  rw [RankCounts.KummerS.isUnramifiedOutside_iff]
  intro v _
  have hsurj : Function.Surjective
      (Algebra.ofId (𝓞 K) (𝓞 (⊥ : IntermediateField K (AlgebraicClosure K)))) := by
    intro x
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 (x : (⊥ : IntermediateField K
      (AlgebraicClosure K))).2
    have hk' : algebraMap K (⊥ : IntermediateField K (AlgebraicClosure K)) k = x := by
      apply Subtype.ext
      exact hk
    have hint : IsIntegral ℤ k := by
      have hx : IsIntegral ℤ (x : (⊥ : IntermediateField K (AlgebraicClosure K))) := x.2
      rw [← hk'] at hx
      exact (isIntegral_algHom_iff ((Algebra.ofId K _).restrictScalars ℤ)
        (algebraMap K _).injective).1 hx
    refine ⟨⟨k, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hk'
  have : Algebra.FormallyUnramified (𝓞 K) (𝓞 (⊥ : IntermediateField K (AlgebraicClosure K))) :=
    Algebra.FormallyUnramified.of_surjective _ hsurj
  intro P _ _
  infer_instance

/-- **(ii) The compositum of two finite normal subextensions unramified outside `S` is unramified
outside `S`** (classical: the inertia group of a prime of `L₁ L₂` restricts into the trivial
inertia groups of `L₁` and `L₂`, and `Gal(L₁ L₂/K) → Gal(L₁/K) × Gal(L₂/K)` is injective; Tau Ceti
has `Ideal.isUnramifiedAt_iff_inertia_eq_bot`). Proved in `unramifiedOutsideSup_proof`. -/
def UnramifiedOutsideSup : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (L₁ L₂ : IntermediateField K (AlgebraicClosure K)),
    UnrGal K S L₁ → UnrGal K S L₂ → IsUnramifiedOutside K S (L₁ ⊔ L₂)

/-- **(b2) from (ii)** (`PROVED` from `UnramifiedOutsideSup`): the finite normal subextensions
unramified outside `S` form a directed family (by (ii)), containing `⊥`
(`isUnramifiedOutside_bot`), so every element of their supremum `K_S` lies in one of them. -/
theorem finiteUnramifiedSupport_of_sup (h : UnramifiedOutsideSup) : FiniteUnramifiedSupport := by
  intro K _ _ S x
  have hne : Nonempty {L : IntermediateField K (AlgebraicClosure K) // UnrGal K S L} :=
    ⟨⟨⊥, inferInstance, inferInstance, isUnramifiedOutside_bot K S⟩⟩
  have hdir : Directed (· ≤ ·) (fun L : {L : IntermediateField K (AlgebraicClosure K) //
      UnrGal K S L} => (L : IntermediateField K (AlgebraicClosure K))) := by
    intro L₁ L₂
    have h₁ := L₁.2
    have h₂ := L₂.2
    have : FiniteDimensional K (L₁ : IntermediateField K (AlgebraicClosure K)) := h₁.1
    have : FiniteDimensional K (L₂ : IntermediateField K (AlgebraicClosure K)) := h₂.1
    have : Normal K (L₁ : IntermediateField K (AlgebraicClosure K)) := h₁.2.1
    have : Normal K (L₂ : IntermediateField K (AlgebraicClosure K)) := h₂.2.1
    refine ⟨⟨L₁.1 ⊔ L₂.1, inferInstance, inferInstance, h K S L₁.1 L₂.1 h₁ h₂⟩, le_sup_left,
      le_sup_right⟩
  have key : ∀ y : AlgebraicClosure K, y ∈ unramifiedOutside K S →
      ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
        IsUnramifiedOutside K S L ∧ y ∈ L := by
    intro y hy
    rw [unramifiedOutside_eq_iSup_subtype, ← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hy
    obtain ⟨L, hL⟩ := hy
    exact ⟨L.1, L.2.1, L.2.2.2, hL⟩
  exact key _ x.2

/-- **`h2` from full `2`-power torsion and (ii)** (`PROVED` from `UnramifiedOutsideSup`). -/
theorem h2_of_hasFullTwoTorsion_of_sup (h : UnramifiedOutsideSup)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic]
    [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  h2_of_hasFullTwoTorsion_of_finiteUnramifiedSupport (finiteUnramifiedSupport_of_sup h) W

end Compositum

/-! ### Fragments of (ii) -/

/-- **An automorphism of a compositum trivial on both factors is the identity** (`PROVED`). For
intermediate fields `L₁, L₂` of `E/F` and an `F`-automorphism `σ` of `L₁ ⊔ L₂` fixing every element
of `L₁` and of `L₂`, `σ = 1`: the fixed field of `σ` contains `L₁` and `L₂`, hence `L₁ ⊔ L₂`. -/
theorem algEquiv_sup_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L₁ L₂ : IntermediateField F E) (σ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂))
    (h₁ : ∀ (x : E) (hx : x ∈ L₁), σ ⟨x, le_sup_left (b := L₂) hx⟩ = ⟨x, le_sup_left (b := L₂) hx⟩)
    (h₂ : ∀ (x : E) (hx : x ∈ L₂), σ ⟨x, le_sup_right (a := L₁) hx⟩ =
      ⟨x, le_sup_right (a := L₁) hx⟩) :
    σ = 1 := by
  set T := IntermediateField.fixedField (Subgroup.zpowers σ)
  have hfix : ∀ y : ↥(L₁ ⊔ L₂), σ y = y → y ∈ T := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ ∈ MulAction.stabilizer (↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂)) y := hy
    exact (Subgroup.zpowers_le.2 hst) hf
  have hle : L₁ ⊔ L₂ ≤ T.map (L₁ ⊔ L₂).val := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨⟨x, le_sup_left (b := L₂) hx⟩, hfix _ (h₁ x hx), rfl⟩
    · exact ⟨⟨x, le_sup_right (a := L₁) hx⟩, hfix _ (h₂ x hx), rfl⟩
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have hzy' : z = y := Subtype.ext hzy
  subst hzy'
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz σ (Subgroup.mem_zpowers σ)

/-- **Inertia restricts into inertia** (`PROVED`). Let `f : A → B` be a ring map, `G` act on `B`
and `H` on `A`, and `φ : G → H` compatible with `f` (`f (φ g • a) = g • f a`). If `g` lies in the
inertia group of an ideal `Q` of `B`, then `φ g` lies in the inertia group of `f⁻¹(Q)`. -/
theorem map_mem_inertia_comap {A B G H : Type*} [CommRing A] [CommRing B] [Group G] [Group H]
    [MulAction G B] [MulAction H A] (f : A →+* B) (φ : G →* H)
    (hcompat : ∀ (g : G) (a : A), f (φ g • a) = g • f a) (Q : Ideal B) {g : G}
    (hg : g ∈ Q.inertia G) : φ g ∈ (Q.comap f).inertia H := by
  rw [Ideal.mem_inertia] at hg ⊢
  intro a
  rw [Ideal.mem_comap, map_sub, hcompat]
  exact hg (f a)

/-! ### (ii) proved -/

section CompositumProof

open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside UnrGal)

/-- **Trivial inertia** (`PROVED`): at a prime `P` of `𝓞_L` over `v ∉ S`, for `L` finite Galois and
unramified outside `S`, the inertia group is trivial (`Ideal.isUnramifiedAt_iff_inertia_eq_bot`). -/
theorem inertia_eq_bot_of_isUnramifiedOutside {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [Normal K L] (hL : IsUnramifiedOutside K S L)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.LiesOver v.asIdeal) : P.inertia (L ≃ₐ[K] L) = ⊥ := by
  have hU := (RankCounts.KummerS.isUnramifiedOutside_iff K S L).1 hL v hv
  have : IsGalois K L := IsGalois.mk
  have : Algebra.IsUnramifiedAt (𝓞 K) P := hU P inferInstance hP
  exact (Ideal.isUnramifiedAt_iff_inertia_eq_bot P).1 this

/-- **An inertia element of a compositum is trivial on an unramified factor** (`PROVED`). For
`L_i ≤ M` finite normal, `L_i` unramified outside `S`, and `σ` in the inertia group of a prime `P`
of `𝓞_M` above `v ∉ S`: the restriction of `σ` to `L_i` lies in the inertia group of `P ∩ 𝓞_{L_i}`
(the argument of `map_mem_inertia_comap`), which is trivial, so `σ` fixes `L_i`. -/
theorem fix_of_mem_inertia {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (Li M : IntermediateField K (AlgebraicClosure K))
    (hle : Li ≤ M) [FiniteDimensional K Li] [Normal K Li] [FiniteDimensional K M] [Normal K M]
    (hLi : IsUnramifiedOutside K S Li) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (P : Ideal (𝓞 M)) [P.IsPrime] (hP : P.LiesOver v.asIdeal) (σ : M ≃ₐ[K] M)
    (hσ : σ ∈ P.inertia (M ≃ₐ[K] M)) (x : AlgebraicClosure K) (hx : x ∈ Li) :
    σ ⟨x, hle hx⟩ = ⟨x, hle hx⟩ := by
  set χ := σ.liftNormal (AlgebraicClosure K)
  set τ : Li ≃ₐ[K] Li := χ.restrictNormal Li
  have hcompat : ∀ y : Li, ((τ y : Li) : AlgebraicClosure K) =
      ((σ ⟨y, hle y.2⟩ : M) : AlgebraicClosure K) := by
    intro y
    calc ((τ y : Li) : AlgebraicClosure K) = algebraMap Li (AlgebraicClosure K) (τ y) := rfl
      _ = χ (algebraMap Li (AlgebraicClosure K) y) := AlgEquiv.restrictNormal_commutes χ Li y
      _ = χ (algebraMap M (AlgebraicClosure K) ⟨y, hle y.2⟩) := rfl
      _ = algebraMap M (AlgebraicClosure K) (σ ⟨y, hle y.2⟩) :=
        AlgEquiv.liftNormal_commutes σ (AlgebraicClosure K) _
  set f : 𝓞 Li →+* 𝓞 M := RingOfIntegers.mapRingHom (IntermediateField.inclusion hle).toRingHom
  have hfalg : f.comp (algebraMap (𝓞 K) (𝓞 Li)) = algebraMap (𝓞 K) (𝓞 M) := by
    ext a
    rfl
  have hQprime : (P.comap f).IsPrime := Ideal.comap_isPrime f P
  have hQlo : (P.comap f).LiesOver v.asIdeal := by
    constructor
    rw [Ideal.under, Ideal.comap_comap, hfalg]
    exact hP.over
  have hτ : τ ∈ (P.comap f).inertia (Li ≃ₐ[K] Li) := by
    rw [Ideal.mem_inertia] at hσ ⊢
    intro a
    rw [Ideal.mem_comap, map_sub]
    have : f (τ • a) = σ • f a := by
      apply RingOfIntegers.ext
      apply Subtype.ext
      exact hcompat (a : Li)
    rw [this]
    exact hσ (f a)
  have hτ1 : τ = 1 := by
    have h := inertia_eq_bot_of_isUnramifiedOutside Li hLi hv (P.comap f) hQlo
    rw [h] at hτ
    exact hτ
  apply Subtype.ext
  have := hcompat ⟨x, hx⟩
  rw [hτ1] at this
  exact this.symm

/-- **(ii) `UnramifiedOutsideSup`** (`PROVED`): an inertia element `σ` at a prime of `𝓞_{L₁ ⊔ L₂}`
above `v ∉ S` is trivial on `L₁` and on `L₂` (`fix_of_mem_inertia`), hence `σ = 1`
(`algEquiv_sup_eq_one`); so the inertia group is trivial and `L₁ ⊔ L₂` is unramified there. -/
theorem unramifiedOutsideSup_proof : UnramifiedOutsideSup := by
  intro K _ _ S L₁ L₂ h₁ h₂
  obtain ⟨hf₁, hn₁, hu₁⟩ := h₁
  obtain ⟨hf₂, hn₂, hu₂⟩ := h₂
  rw [RankCounts.KummerS.isUnramifiedOutside_iff]
  intro v hv P _ hP
  have : IsGalois K ↥(L₁ ⊔ L₂) := IsGalois.mk
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot, Subgroup.eq_bot_iff_forall]
  intro σ hσ
  exact algEquiv_sup_eq_one L₁ L₂ σ
    (fun x hx => fix_of_mem_inertia L₁ (L₁ ⊔ L₂) le_sup_left hu₁ hv P hP σ hσ x hx)
    (fun x hx => fix_of_mem_inertia L₂ (L₁ ⊔ L₂) le_sup_right hu₂ hv P hP σ hσ x hx)

end CompositumProof

/-! ### `h2` from full `2`-power torsion, unconditionally -/

/-- **(b2) `FiniteUnramifiedSupport`** (`PROVED`). -/
theorem finiteUnramifiedSupport_proof : FiniteUnramifiedSupport :=
  finiteUnramifiedSupport_of_sup unramifiedOutsideSup_proof

/-- **The ramification step `TwoPowerRootsRamified`** (`PROVED`). -/
theorem twoPowerRootsRamified_proof : TwoPowerRootsRamified :=
  twoPowerRootsRamified_of_finiteUnramifiedSupport finiteUnramifiedSupport_proof

/-- **`h2` from full `2`-power torsion** (`PROVED`): if `E[2^n] ⊆ E(K_S)` for every `n`, then `S`
contains every place above `2`. The consumers `*_of_ramified` take
`twoPowerRootsRamified_proof`. -/
theorem h2_of_hasFullTwoTorsion_proof {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
    [HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  h2_of_hasFullTwoTorsion twoPowerRootsRamified_proof W

end ZInQ.Contrib.CloudB3RC53.Finiteness

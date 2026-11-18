import ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness
import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.CharP.Two

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
* `TwoPowerRootsRamified` (the ramification step, stated): if `K_S` contains a primitive `2^n`-th
  root of unity for every `n`, then `S` contains every place above `2`.
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

## What remains of `TwoPowerRootsRamified`

With the fragments, the ramification step reduces to two classical facts:
* (b1) the comparison of ramification indices: for `L` finite over `K` and unramified outside `S`,
  a prime `Q` of the integral closure of `𝓞_K` in `L` over `v ∉ S` has `e(Q | v) = 1`, so
  `2 ∈ Q ^ m` forces `m ≤ e(v | 2) ≤ [K : ℚ]`;
* (b2) every element of `K_S` lies in a finite subextension unramified outside `S`. `K_S` is the
  supremum of such subextensions, so this needs the compositum of two extensions unramified
  outside `S` to be unramified outside `S`.

Classification: `PROVED` from the named input; `TwoPowerRootsRamified` is stated, not proved.
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
Stated, not proved; the fragments below reduce it to the comparison of ramification indices and
the directedness of the finite subextensions of `K_S` unramified outside `S`. -/
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

end ZInQ.Contrib.CloudB3RC53.Finiteness

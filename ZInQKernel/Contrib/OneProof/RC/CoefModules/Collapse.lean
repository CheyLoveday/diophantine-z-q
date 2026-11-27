import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchCollapse
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchNonVacuity

/-!
# Lane RC28 (coefficient modules), part 11: the collapse condition of `RegularityInputsG` at the
actual coefficient data

Lane RC0's `regularityInputsG_iff_of_unitFibre` (`Wiring/GenuineSwitchCollapse.lean`) collapses
the height-one leaf `RegularityInputsG u` to its target `u ∈ Λ[1/2]` under the condition

`E`: at every height-one prime `𝔭 ≠ (2)` of `Λ = ℤ₂[[t]]`, `2 ≠ 0` in `k(𝔭)` and there is a genuine
Galois Selmer datum `F` over `k(𝔭)` (`IsGaloisSelData F`) whose Selmer complex is homotopy
equivalent to the one-stage fiber `[k --0--> k]` (`unitFibre P`).

This file decides `E` **for the actual coefficient data** of the manuscript (tex 2780–2830: the
modules `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)` over `A_i = (ℤ/2^i)[t]/(t^i)`, built in this lane), and for the
leaf tied to them:

* `two_ne_zero_resAt`: `2 ≠ 0` in `k(𝔭)` for **every** height-one `𝔭 ≠ (2)` (the first conjunct of
  `E` is a theorem; `Λ` is a UFD and `2` is prime).
* `isEmpty_ringHom_acoef_resAt`: there is no ring map `A_i → k(𝔭)` (`i ≥ 1`): the actual
  coefficient rings do not map to the leaf's coefficient fields.
* `subsingleton_of_two_pow_smul`, `subsingleton_resAt_tensor_mcoef`: every `k(𝔭)`-module killed by
  a power of `2` is zero; in particular `k(𝔭) ⊗_ℤ M_i = 0` (the base change of the actual module).
* `subsingleton_selCx_galois`: a genuine Galois Selmer complex (injective local conditions, the
  shape of `IsGaloisSelData`) with zero coefficients has zero terms;
  `isEmpty_homotopyEquiv_unitFibre`: it is **not** homotopy equivalent to the one-stage fiber.
* **`collapse_refuted_actual`**: at every height-one `𝔭 ≠ (2)`, **no genuine Galois Selmer datum
  over `k(𝔭)` whose coefficient module is `2`-power torsion** — in particular none built from the
  actual finite coefficient data `M_i` (`collapse_refuted_mcoef`) — is homotopy equivalent to
  `unitFibre P`; and over any genuine family whose actual fiber is such a datum there is **no**
  `GenuineSwitchData` for any coordinate `u` (`isEmpty_genuineSwitchData_actual`).
* **`RegularityInputsActual`** (the leaf tied to the actual finite coefficient data: the actual
  fiber of the witness family is a genuine Galois Selmer datum with `2`-power torsion
  coefficients) and **`regularityInputsActual_iff : RegularityInputsActual u ↔ u = 0`**: tied to
  the actual finite data, the leaf is refuted for every `u ≠ 0` (the prime `(t)` is a height-one
  prime `≠ (2)`, `height_span_X`, `span_X_ne_span_two`).

What is NOT decided: `E` itself quantifies over all genuine Galois Selmer data over `k(𝔭)` (any
number field, any coefficient module with any topology); a witness must have characteristic-zero
coefficients (`collapse_refuted_actual`), e.g. the fiber at `𝔭` of the `Λ`-adic module
`T_2E ⊗ Λ = lim M_i` with its `𝔭`-adic topology. That module, its continuous cohomology and the
Nekovář finiteness/duality statements for it are not in the tree (the PRINTs of lane RC26 are for
finite discrete modules), so `E` is neither proved nor refuted here.

Kinds: PROVED (all statements); `RegularityInputsActual` is a definition.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain CategoryTheory TensorProduct Module
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Uniform (Lambda height_eq_one_iff_exists_prime prime_two_lambda
  height_span_prime)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt unitFibre unitFibre_hom_inv IsGaloisSelData
  IsGenuineFamilyAt isEmpty_genuineSwitchData_of_h1_eq_zero homology_subsingleton_of_X)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData selCx selT)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily GenuineSwitchData)

/-! ### `2 ≠ 0` in `k(𝔭)` -/

section Two

variable (P : Ideal Lambda) [P.IsPrime]

/-- **`2 ∉ 𝔭` for a height-one prime `𝔭 ≠ (2)`** (`Λ` is a UFD, `𝔭 = (p)` for a prime `p`, and
`p ∣ 2` forces `(p) = (2)`). Kind: PROVED. -/
theorem two_not_mem (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) : (2 : Lambda) ∉ P := by
  intro h2
  obtain ⟨p, hp, rfl⟩ := (height_eq_one_iff_exists_prime P).mp hP
  have hdvd : p ∣ 2 := Ideal.mem_span_singleton.mp h2
  exact hne (Ideal.span_singleton_eq_span_singleton.mpr
    (hp.irreducible.associated_of_dvd prime_two_lambda.irreducible hdvd))

/-- **`2 ≠ 0` in `k(𝔭)`** for every height-one prime `𝔭 ≠ (2)` (the first conjunct of the collapse
condition is a theorem). Kind: PROVED. -/
theorem two_ne_zero_resAt (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) : (2 : ResAt P) ≠ 0 := by
  have hu : IsUnit (algebraMap Lambda (Localization.AtPrime P) 2) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P 2).mpr
      (two_not_mem P hP hne)
  intro h
  have h' : resAt P (algebraMap Lambda (Localization.AtPrime P) 2) = 0 := by
    rw [map_ofNat, map_ofNat]
    exact h
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  exact (IsLocalRing.mem_maximalIdeal _).mp h' hu

/-- `(t)` is a height-one prime of `Λ`. Kind: PROVED. -/
theorem height_span_X : (Ideal.span {(PowerSeries.X : Lambda)}).height = 1 :=
  height_span_prime PowerSeries.X_prime

instance isPrime_span_X : (Ideal.span {(PowerSeries.X : Lambda)}).IsPrime :=
  (Ideal.span_singleton_prime PowerSeries.X_prime.ne_zero).mpr PowerSeries.X_prime

/-- `(t) ≠ (2)`. Kind: PROVED. -/
theorem span_X_ne_span_two : Ideal.span {(PowerSeries.X : Lambda)} ≠ Ideal.span {2} := by
  intro h
  have h2 : (2 : Lambda) ∈ Ideal.span {(PowerSeries.X : Lambda)} := by
    rw [h]
    exact Ideal.mem_span_singleton_self 2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h2
  have := congrArg (PowerSeries.constantCoeff (R := ℤ_[2])) hc
  rw [map_mul, PowerSeries.constantCoeff_X, zero_mul, map_ofNat] at this
  exact two_ne_zero this

end Two

/-! ### The actual coefficient data vanish over `k(𝔭)` -/

section Vanish

/-- **A module over a field with `2 ≠ 0` that is killed by a power of `2` is zero.** Kind:
PROVED. -/
theorem subsingleton_of_two_pow_smul {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (M : Type)
    [AddCommGroup M] [Module k M] (n : ℕ) (hM : ∀ m : M, (2 ^ n : ℕ) • m = 0) : Subsingleton M := by
  have hu : ((2 ^ n : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero n h2
  refine ⟨fun a b => ?_⟩
  have key : ∀ m : M, m = 0 := fun m => by
    have h := hM m
    rw [← Nat.cast_smul_eq_nsmul k] at h
    exact (smul_eq_zero.mp h).resolve_left hu
  rw [key a, key b]

/-- **There is no ring map from the actual coefficient ring `A_i` to `k(𝔭)`** (`i ≥ 1`;
`2^i = 0` in `A_i`, `2 ≠ 0` in `k(𝔭)`). Kind: PROVED. -/
theorem isEmpty_ringHom_acoef_resAt (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2}) (i : ℕ) : IsEmpty (Acoef i →+* ResAt P) := by
  refine ⟨fun f => ?_⟩
  have h := congrArg f (acoef_two_pow_eq_zero i)
  rw [map_pow, map_ofNat, map_zero] at h
  exact two_ne_zero_resAt P hP hne (pow_eq_zero_iff'.mp h).1

/-- The actual `M_i` is killed by `2^i`. Kind: PROVED. -/
theorem two_pow_smul_mcoef {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (i : ℕ)
    (α : GKS K S →* (Acoef i)ˣ) (m : Mcoef K S W i α) : (2 ^ i : ℕ) • m = 0 := by
  have h0 : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact acoef_two_pow_eq_zero i
  rw [← Nat.cast_smul_eq_nsmul (Acoef i), h0]
  exact zero_smul (Acoef i) m

/-- **The base change of the actual module to `k(𝔭)` is zero**: `k(𝔭) ⊗_ℤ M_i = 0`. Kind:
PROVED. -/
theorem subsingleton_resAt_tensor_mcoef (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2}) {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (i : ℕ)
    (α : GKS K S →* (Acoef i)ˣ) : Subsingleton (ResAt P ⊗[ℤ] Mcoef K S W i α) := by
  refine subsingleton_of_two_pow_smul (two_ne_zero_resAt P hP hne) _ i fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [← TensorProduct.tmul_smul, two_pow_smul_mcoef, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

end Vanish

/-! ### Genuine Selmer complexes with zero coefficients -/

section Zero

variable {k : Type} [CommRing k]

theorem subsingleton_contCochains_X (G : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
    [Subsingleton M] (n : ℕ) : Subsingleton ((contCochains k G M).X n) := by
  constructor
  intro a b
  obtain ⟨f, hf⟩ := a
  obtain ⟨g, hg⟩ := b
  have hfg : f = g := by
    change ((Fin n → G) → M) at f g
    exact funext fun _ => Subsingleton.elim _ _
  subst hfg
  rfl

theorem subsingleton_natCx_X (C : CochainComplex (ModuleCat.{0} k) ℕ)
    (h : ∀ n, Subsingleton (C.X n)) : ∀ n : ℤ, Subsingleton ((natCx C).X n)
  | Int.ofNat n => h n
  | Int.negSucc _ => inferInstanceAs (Subsingleton PUnit)

/-- **A genuine Galois Selmer complex with zero coefficients and injective local conditions has
zero terms.** Kind: PROVED. -/
theorem subsingleton_selCx_galois (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M] [Subsingleton M]
    (Δ : GaloisLocalConditions K S k M) (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl))
    (n : ℤ) : Subsingleton ((selCx (galoisSelData K S k M Δ)).toCC.X n) := by
  have hloc : ∀ (v : Places K S) (m : ℤ), Subsingleton
      ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v).X m) :=
    fun v m => by
      have : Subsingleton (ResMod (locMap K S v.1) M) := inferInstanceAs (Subsingleton M)
      exact subsingleton_natCx_X _ (subsingleton_contCochains_X _ _) m
  have hG : Subsingleton ((globalCx k (GKS K S) M).X n) :=
    subsingleton_natCx_X _ (subsingleton_contCochains_X _ _) n
  have hU : Subsingleton (∀ v : Places K S, (Δ.U v).X n) := by
    refine ⟨fun a b => funext fun v => ?_⟩
    have := hloc v n
    exact hΔ v n (Subsingleton.elim _ _)
  have hL : Subsingleton (∀ v : Places K S,
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v).X
        (n - 1)) := by
    refine ⟨fun a b => funext fun v => ?_⟩
    have := hloc v (n - 1)
    exact Subsingleton.elim _ _
  refine ⟨fun a b => ?_⟩
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have e1 : a1 = b1 := @Subsingleton.elim _ hG a1 b1
  have e2 : a2 = b2 := @Subsingleton.elim _ hU a2 b2
  have e3 : a3 = b3 := @Subsingleton.elim _ hL a3 b3
  rw [e1, e2, e3]

variable (P : Ideal Lambda) [P.IsPrime]

/-- **A complex with zero degree-one term is not homotopy equivalent to the one-stage fiber**
(whose degree-one cohomology is `k(𝔭)`). Kind: PROVED. -/
theorem isEmpty_homotopyEquiv_unitFibre (F : SelData (ResAt P))
    (hF : Subsingleton ((selCx F).toCC.X 1)) :
    IsEmpty (HomotopyEquiv (selCx F).toCC (unitFibre P)) := by
  refine ⟨fun e => ?_⟩
  have h := unitFibre_hom_inv e (fun _ => (1 : ResAt P))
  rw [Subsingleton.elim ((e.inv.f 1).hom (fun _ => (1 : ResAt P))) 0, map_zero] at h
  have := congrFun h 0
  exact one_ne_zero this.symm

/-- **The collapse condition fails for every genuine Galois Selmer datum over `k(𝔭)` with
`2`-power torsion coefficients** (in particular for the actual finite coefficient data): at every
height-one prime `𝔭 ≠ (2)`, no such datum is homotopy equivalent to `unitFibre P`. Kind:
PROVED. -/
theorem collapse_refuted_actual (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) (K : Type)
    [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [AddCommGroup M]
    [Module (ResAt P) M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResAt P) M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul (ResAt P) M]
    [ContinuousSMul (GKS K S) M] (n : ℕ) (hM : ∀ m : M, (2 ^ n : ℕ) • m = 0)
    (Δ : GaloisLocalConditions K S (ResAt P) M)
    (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    IsEmpty (HomotopyEquiv (selCx (galoisSelData K S (ResAt P) M Δ)).toCC (unitFibre P)) := by
  have := subsingleton_of_two_pow_smul (two_ne_zero_resAt P hP hne) M n hM
  exact isEmpty_homotopyEquiv_unitFibre P _ (subsingleton_selCx_galois K S M Δ hΔ 1)

/-- **The collapse condition fails at the base change of the actual module `M_i`** to `k(𝔭)`
(whatever action, topology and injective local conditions are put on it). Kind: PROVED. -/
theorem collapse_refuted_mcoef (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) {K : Type}
    [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
    (i : ℕ) (α : GKS K S →* (Acoef i)ˣ)
    [DistribMulAction (GKS K S) (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    [SMulCommClass (GKS K S) (ResAt P) (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    [TopologicalSpace (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    [ContinuousAdd (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    [ContinuousConstSMul (ResAt P) (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    [ContinuousSMul (GKS K S) (ResAt P ⊗[ℤ] Mcoef K S W i α)]
    (Δ : GaloisLocalConditions K S (ResAt P) (ResAt P ⊗[ℤ] Mcoef K S W i α))
    (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    IsEmpty (HomotopyEquiv (selCx (galoisSelData K S (ResAt P) _ Δ)).toCC (unitFibre P)) := by
  have := subsingleton_resAt_tensor_mcoef P hP hne W i α
  exact isEmpty_homotopyEquiv_unitFibre P _ (subsingleton_selCx_galois K S _ Δ hΔ 1)

/-- **No genuine switching datum over a family whose actual fiber has `2`-power torsion
coefficients**, whatever the coordinate `u`. Kind: PROVED. -/
theorem isEmpty_genuineSwitchData_actual (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [AddCommGroup M] [Module (ResAt P) M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResAt P) M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul (ResAt P) M] [ContinuousSMul (GKS K S) M] (n : ℕ)
    (hM : ∀ m : M, (2 ^ n : ℕ) • m = 0) (Δ : GaloisLocalConditions K S (ResAt P) M)
    (hΔ : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl))
    (hΦ : Φ.fibre Φ.actual = galoisSelData K S (ResAt P) M Δ) (u : FractionRing Lambda) :
    IsEmpty (GenuineSwitchData Φ (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt P)
      (resAt P) u) := by
  have := subsingleton_of_two_pow_smul (two_ne_zero_resAt P hP hne) M n hM
  refine isEmpty_genuineSwitchData_of_h1_eq_zero u ?_
  rw [hΦ]
  have := homology_subsingleton_of_X _ 1 (subsingleton_selCx_galois K S M Δ hΔ 1)
  exact Module.finrank_zero_of_subsingleton

end Zero

/-! ### The leaf tied to the actual finite coefficient data -/

/-- **The height-one leaf tied to the actual finite coefficient data**: `RegularityInputsG u` with
the additional requirement that the actual fiber of the witness family is a genuine Galois Selmer
datum whose coefficient module is `2`-power torsion (as the actual `M_i` and all of its base
changes are; tex 2780–2830). Kind: definition. -/
def RegularityInputsActual (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
        (M : Type) (_ : AddCommGroup M) (_ : Module (ResAt P) M)
        (_ : DistribMulAction (GKS K S) M) (_ : SMulCommClass (GKS K S) (ResAt P) M)
        (_ : TopologicalSpace M) (_ : ContinuousAdd M) (_ : ContinuousConstSMul (ResAt P) M)
        (_ : ContinuousSMul (GKS K S) M) (Δ : GaloisLocalConditions K S (ResAt P) M) (n : ℕ),
        (∀ m : M, (2 ^ n : ℕ) • m = 0) ∧ (∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) ∧
          Φ.fibre Φ.actual = galoisSelData K S (ResAt P) M Δ) ∧
      Nonempty (GenuineSwitchData Φ (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt P)
        (resAt P) u)

/-- **Tied to the actual finite coefficient data, the leaf collapses to `u = 0`**: it is refuted
for every `u ≠ 0` (at the height-one prime `(t) ≠ (2)` no witness exists). Kind: PROVED. -/
theorem regularityInputsActual_iff (u : FractionRing Lambda) : RegularityInputsActual u ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | h
  · exact h
  · obtain ⟨Φ, -, ⟨K, _, _, S, M, _, _, _, _, _, _, _, _, Δ, n, hM, hΔ, hΦ⟩, ⟨G⟩⟩ :=
      h (Ideal.span {(PowerSeries.X : Lambda)}) height_span_X span_X_ne_span_two
    exact ((isEmpty_genuineSwitchData_actual _ height_span_X span_X_ne_span_two Φ K S M n hM Δ hΔ
      hΦ u).false G).elim

/-- **Non-vacuity of the tied leaf**: it holds at `u = 0`. -/
example : RegularityInputsActual 0 := Or.inl rfl

/-! ### The actual Selmer data are genuine in the leaf's sense -/

section Genuine

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The actual Selmer data are genuine Galois Selmer data** (`IsGaloisSelData`, the leaf's
predicate): finite support, subcomplex local conditions. Kind: PROVED. -/
theorem isGaloisSelData_actual {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (hSfin : S.Finite) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h, (c v h).IsInjective) : IsGaloisSelData (actualSelData hS W i α c) := by
  letI := acoefTop i
  haveI := acoefTop_discrete i
  exact ⟨K, inferInstance, inferInstance, S, MinS hS W i α, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    actualConditions hS W i α c, hSfin, actualConditions_injective hS W i α c hc, rfl⟩

/-- The actual Selmer data with full conditions are genuine. Kind: PROVED. -/
theorem isGaloisSelData_full (hSfin : S.Finite) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] : IsGaloisSelData (actualSelData_full W i α) :=
  ⟨K, inferInstance, inferInstance, S, Mcoef K S W i α, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    relaxedConditions (Acoef i) _ _ _ _, hSfin, fun _ _ _ _ h => h, rfl⟩

/-- The actual Selmer data with zero conditions are genuine. Kind: PROVED. -/
theorem isGaloisSelData_zero (hSfin : S.Finite) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
    (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] : IsGaloisSelData (actualSelData_zero W i α) :=
  ⟨K, inferInstance, inferInstance, S, Mcoef K S W i α, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    strictConditions (Acoef i) _ _ _ _, hSfin, fun _ _ x y _ => Subsingleton.elim (α := PUnit) x y,
    rfl⟩

end Genuine

end ZInQ.Manuscript.RC.CoefModules

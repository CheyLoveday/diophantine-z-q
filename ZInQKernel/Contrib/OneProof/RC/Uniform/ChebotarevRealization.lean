import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists
import ZInQKernel.Contrib.OneProof.RC.Limits.Ultralimit
import ZInQKernel.Contrib.OneProof.RC.Uniform.KernelDetection

/-!
# Lane RC16-uniform, repaired by Lane RC27: (5.4) over the genuine Galois groups

Manuscript (11/5 version), Lemma `ex:limits-kernel-detection`, statement tex 4755–4758 and the
last two paragraphs of the proof, tex 4809–4831:

> Chebotarev is applied at finite stages, not to the product group. Each of the finitely many
> original basis cochains in degrees zero through two factors through a finite quotient. Include
> their quotient, the required Tate precision, ring-class and quadratic fields and old diagrams in
> one compositum. The element just found, multiplied by conjugation, is a single actual
> automorphism of that compositum. Its restrictions agree on intersections. Choose the new prime
> and a place above it to realize that representative.
>
> This also resolves the precision issue caused by localization. Choose the new prime to match all
> original basis-cochain evaluations at a common retained precision `n(i) → ∞`. Taking the same
> inner ultrafilter gives an exact equality of `Λ`-matrices `L_j = E_{σ_j^2}` (5.4). Only afterward
> compose with the inclusion `I_j` from an `𝒪`-minimal model: `L_j I_j = E_{σ_j^2} I_j`.

and, for the use at the quadratic primes, tex 5108–5112: "Finite Chebotarev and the exact matrix
identity (5.4) realize this choice by a new inert prime, avoiding every previously used prime."

Lane RC16 recorded (5.4) as the interface `ExactChebotarevRealization` over abstract finite groups
(`KernelDetection.lean`); Lane RC22 flagged it MISMATCH. This file states (5.4) over the genuine
objects of the tree and proves its finite-Chebotarev half.

## The genuine objects

* `G_ℚ = Aut(ℚ̄/ℚ)` (`ZInQ.Contrib.ChebFD.C10.GQ`, Mathlib's absolute Galois group of `ℚ`).
* The compositum at stage `i`: a finite Galois `M i ⊆ ℚ̄` (an `IntermediateField`), with its genuine
  finite Galois group `Gal(M_i/ℚ) = M i ≃ₐ[ℚ] M i` and the genuine restriction
  `G_ℚ → Gal(M_i/ℚ)` (`AlgEquiv.restrictNormal`).
* `τ`: a genuine complex conjugation (`IsComplexConjugation`); `h i ∈ G_ℚ`: the stage-`i`
  component of the kernel element just found; `σ_i = τ h_i` the representative.
* The imaginary quadratic field `K = ℚ(s)`, `s^2 = k < 0`, included in every compositum
  (`s ∈ M i`); the kernel element is trivial on its quadratic character (`h i s = s`).
* A new prime at stage `i`: a rational prime `ℓ ∉ S i` (the finitely many previously used
  primes), unramified in `M i` (`UnramifiedIn`), with an arithmetic Frobenius `Fr ∈ G_ℚ` at a
  place above it (`ZInQ.Contrib.ChebFD.C10.IsFrobAt Fr ℓ`: `Fr x ≡ x^ℓ` modulo a prime of `ℤ̄`
  over `ℓ`).
* `Λ = ℤ₂[[t]]` with the stage ideals `(2^n, t^n)` and the inner ultralimit `ulimMat` of Lane RC6
  (`RC/Limits/Ultralimit.lean`, everything there PROVED).

## Main results

* `exists_newPrime_frob` (PROVED, the finite-Chebotarev half): for a finite Galois `M ⊆ ℚ̄`, a
  finite set `S` and `σ ∈ G_ℚ` there are a prime `ℓ ∉ S` unramified in `M` and a Frobenius
  `Fr ∈ G_ℚ` at `ℓ` with `Fr|_M = σ|_M`. From the tree's Chebotarev density theorem
  (`ZInQ.Contrib.chebotarevExists`) and the lift of a finite-level Frobenius
  (`ZInQ.Contrib.ChebFD.C10.frobLift`).
* `NewPrimeLocalization` (ELLIOT, the one input): at stage `i`, the localization matrix of the basis
  cochains at a new inert prime, at the place of the chosen Frobenius `Fr`, is their evaluation
  matrix at `Fr^2` at the retained precision `(2^{n(i)}, t^{n(i)})`.
* `ExactChebotarevRealizationGenuine` (the genuine (5.4)) and
  `exactChebotarevRealizationGenuine_of_localization` (PROVED from `NewPrimeLocalization`): at every
  stage a new inert prime with Frobenius realizing `σ_i` on `M i`, and the exact equality of
  `Λ`-matrices `L = E_{σ^2}` of the inner ultralimits.
* `ExactChebotarevRealizationGenuine.mul_inclusion` (PROVED): `L I = E_{σ^2} I` for any inclusion.
* `exactChebotarevRealizationGenuine_family` (PROVED): the same for every instance `j`, with one
  inner ultrafilter (the old interface's `∀ j`).
* `exactChebotarevRealization_stage` (PROVED): the old abstract interface
  `ExactChebotarevRealization` holds at every finite stage for the genuine data, with
  `Γ = Gal(M_i/ℚ)`, the new inert primes with their genuine Frobenius elements, and
  `Λ/(2^{n(i)}, t^{n(i)})` as coefficient ring.
* Non-vacuity (namespace `ChebotarevNonVacuity`): a complex conjugation exists; all hypotheses of
  the main theorem hold together (`K = ℚ(√-1)`); the input `NewPrimeLocalization` has content (it
  fails for a shifted localization matrix).
* The companion `ChebotarevTate.lean`: the required Tate precision (`ℚ(A[2^{n(i)}]) ⊆ M_i` gives
  `ρ₂(Fr_i) ≡ ρ₂(τ h_i) mod 2^{n(i)}`), and the arithmetic content of the new primes (for
  `K = ℚ(√-1)` they are `≡ 3 mod 4`).

## DEPARTUREs (form) and what is not modelled

* The original basis cochains, their localization maps and the Selmer complexes over `Λ` are not in
  the tree. The evaluation matrices `E i` are data on the genuine finite group `Gal(M_i/ℚ)` (this
  builds in "factors through a finite quotient"), evaluated at `g ∈ G_ℚ` through the genuine
  restriction; the localization matrices `L` are data, tied to `E` by the ELLIOT input. Entries are
  lifts to `Λ` of the stage values in `Λ/(2^{n(i)}, t^{n(i)})`; the ultralimit does not depend on
  the lifts (Lane RC6's `ulimMat_eq_of_sub_mem`, the ideals `(2^{n(i)}, t^{n(i)})` tending to zero
  by `idealsTendToZero_stageIdeal_comp`).
* The chosen place above `ℓ` is recorded by its arithmetic Frobenius `Fr` (`L i ℓ Fr`); for `ℓ`
  unramified in `M_i` the stage data depend only on `Fr|_{M_i}`.
* The compositum `M i` is any finite Galois subextension of `ℚ̄` containing `K`; that it also
  contains the ring-class fields and the fields of the old diagrams is not stated (ring-class fields
  are not in the tree), and any such fields are allowed. The Tate precision is the companion file.
* The kernel element enters only through `h i s = s` (trivial on the quadratic character of `K`);
  its triviality on the Tate module and the ring-class fields is used by the kernel argument (step
  1 of `KernelDetection.lean`), not by (5.4).
* The common retained precision is a function `n` with `n(i) → ∞`; the stage ideals are
  `(2^{n(i)}, t^{n(i)})`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Uniform

open Filter NumberField
open ZInQ.Contrib.ChebFD.C10 (GQ Qbar IsFrobAt)
open ZInQ.Manuscript.RC.Limits (Lambda stageIdeal ulimMat IdealsTendToZero)
open scoped PowerSeries.WithPiTopology

/-! ## Complex conjugation and the imaginary quadratic field -/

/-- **A complex conjugation** `τ ∈ G_ℚ` (tex 4813–4814, "multiplied by conjugation"): for some
`ℚ`-embedding `ι : ℚ̄ → ℂ`, `ι(τ x) = conj(ι x)` for every `x ∈ ℚ̄`. Definition. Non-vacuity:
`exists_isComplexConjugation`. -/
def IsComplexConjugation (τ : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x : Qbar, ι (τ x) = starRingEnd ℂ (ι x)

/-- **A complex conjugation exists** (PROVED: complex conjugation of `ℂ` restricted to the normal
extension `ℚ̄`, embedded in `ℂ`). -/
theorem exists_isComplexConjugation : ∃ τ : GQ, IsComplexConjugation τ := by
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let _ : Algebra Qbar ℂ := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ Qbar ℂ :=
    IsScalarTower.of_algebraMap_eq fun r => (ι.commutes r).symm
  let conjQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  exact ⟨conjQ.restrictNormal Qbar, ι, fun x => AlgEquiv.restrictNormal_commutes conjQ Qbar x⟩

/-- **A complex conjugation moves `√k` for `k < 0`** (PROVED): `ι(√k)` is purely imaginary and
nonzero, so it is not real. Hence `τ ∉ G_K` for the imaginary quadratic field `K = ℚ(√k)`. -/
theorem IsComplexConjugation.apply_ne {τ : GQ} (hτ : IsComplexConjugation τ) {k : ℚ}
    (hk : k < 0) {s : Qbar} (hs : s ^ 2 = algebraMap ℚ Qbar k) : τ s ≠ s := by
  obtain ⟨ι, hι⟩ := hτ
  intro h
  have hz : (ι s) ^ 2 = (k : ℂ) := by
    rw [← map_pow, hs, AlgHom.commutes]
    simp
  have hconj : starRingEnd ℂ (ι s) = ι s := by rw [← hι, h]
  have him : (ι s).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  have hre := congrArg Complex.re hz
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero] at hre
  have : (0 : ℝ) ≤ (ι s).re * (ι s).re := mul_self_nonneg _
  have hk' : (k : ℝ) < 0 := by exact_mod_cast hk
  rw [show ((k : ℂ)).re = (k : ℝ) by simp] at hre
  linarith

/-! ## Restriction to a finite Galois subextension -/

/-- Two elements of `G_ℚ` have the same restriction to a normal `M ⊆ ℚ̄` iff they agree on `M`
(PROVED). In particular the restrictions of one element to the fields it is built from "agree on
intersections" (tex 4815). -/
theorem restrictNormal_eq_restrictNormal_iff (M : IntermediateField ℚ Qbar) [Normal ℚ M]
    (g g' : GQ) :
    AlgEquiv.restrictNormal g M = AlgEquiv.restrictNormal g' M ↔ ∀ x ∈ M, g x = g' x := by
  constructor
  · intro h x hx
    have e1 := AlgEquiv.restrictNormal_apply M g ⟨x, hx⟩
    have e2 := AlgEquiv.restrictNormal_apply M g' ⟨x, hx⟩
    rw [h] at e1
    exact e1.symm.trans e2
  · intro h
    ext x
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictNormal_apply]
    exact h x x.2

/-- Restriction is multiplicative (PROVED; `AlgEquiv.restrictNormalHom`). -/
theorem restrictNormal_mul' (M : IntermediateField ℚ Qbar) [Normal ℚ M] (g g' : GQ) :
    AlgEquiv.restrictNormal (g * g') M =
      AlgEquiv.restrictNormal g M * AlgEquiv.restrictNormal g' M :=
  map_mul (AlgEquiv.restrictNormalHom M) g g'

/-- Restriction commutes with powers (PROVED). -/
theorem restrictNormal_pow' (M : IntermediateField ℚ Qbar) [Normal ℚ M] (g : GQ) (k : ℕ) :
    AlgEquiv.restrictNormal (g ^ k) M = AlgEquiv.restrictNormal g M ^ k :=
  map_pow (AlgEquiv.restrictNormalHom M) g k

/-! ## New primes and the finite-Chebotarev half -/

/-- **`ℓ` is unramified in the finite subextension `M ⊆ ℚ̄`**: some prime `Q` of `𝓞_M` over `ℓ`
is unramified over `ℤ` (for `M/ℚ` Galois all primes of `𝓞_M` over `ℓ` are conjugate).
Definition. -/
def UnramifiedIn (M : IntermediateField ℚ Qbar) (ℓ : ℕ) : Prop :=
  ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime, Q.under ℤ = Ideal.span {(ℓ : ℤ)} ∧
    Algebra.IsUnramifiedAt ℤ Q

/-- **Finite Chebotarev realizes a representative by a new prime** (tex 4809–4816: "Chebotarev is
applied at finite stages ... The element just found, multiplied by conjugation, is a single actual
automorphism of that compositum. ... Choose the new prime and a place above it to realize that
representative"; tex 5108–5109: "avoiding every previously used prime").

Kind: PROVED (no remaining hypothesis). For a finite Galois `M ⊆ ℚ̄`, a finite set `S` and
`σ ∈ G_ℚ`, there are a prime `ℓ ∉ S`, unramified in `M`, and an arithmetic Frobenius `Fr ∈ G_ℚ` at
a place above `ℓ` with `Fr|_M = σ|_M`. Proof: the tree's Chebotarev theorem
`ZInQ.Contrib.chebotarevExists` (from Tau Ceti's Chebotarev density theorem) gives `ℓ ∉ S` and an
unramified prime `Q ∣ ℓ` of `𝓞_M` at which `σ|_M` is the arithmetic Frobenius;
`ZInQ.Contrib.ChebFD.C10.frobLift` lifts it to a Frobenius of `G_ℚ` restricting to `σ|_M`. -/
theorem exists_newPrime_frob (M : IntermediateField ℚ Qbar) [FiniteDimensional ℚ M]
    [IsGalois ℚ M] (S : Finset ℕ) (σ : GQ) :
    ∃ (ℓ : ℕ) (Fr : GQ), ℓ.Prime ∧ ℓ ∉ S ∧ UnramifiedIn M ℓ ∧ IsFrobAt Fr ℓ ∧
      AlgEquiv.restrictNormal Fr M = AlgEquiv.restrictNormal σ M := by
  have : NumberField M := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hQf⟩ :=
    ZInQ.Contrib.chebotarevExists M S (AlgEquiv.restrictNormal σ M)
  obtain ⟨Fr, hFr, hres⟩ := ZInQ.Contrib.ChebFD.C10.frobLift M _ p Q hp hQp hQu hQf
  exact ⟨p, Fr, hp, hpS, ⟨Q, hQ, hQp, hQu⟩, hFr, hres⟩

/-- **The realizing Frobenius at the representative `σ = τ h` is inert in `K`** (tex 5108–5109,
"a new inert prime"). Kind: PROVED. If `K = ℚ(s)` with `s^2 = k < 0` lies in `M`, `τ` is a complex
conjugation and `h` is trivial on `K`, then any `Fr` with `Fr|_M = (τ h)|_M` moves `s`: `Fr ∉ G_K`,
i.e. the prime is inert in `K` and the Frobenius of the place of `K` above it is `Fr^2`. -/
theorem frob_apply_ne_of_restrict_eq {M : IntermediateField ℚ Qbar} [Normal ℚ M] {τ h Fr : GQ}
    (hτ : IsComplexConjugation τ) {k : ℚ} (hk : k < 0) {s : Qbar}
    (hs : s ^ 2 = algebraMap ℚ Qbar k) (hsM : s ∈ M) (hhs : h s = s)
    (hFr : AlgEquiv.restrictNormal Fr M = AlgEquiv.restrictNormal (τ * h) M) : Fr s ≠ s := by
  rw [(restrictNormal_eq_restrictNormal_iff M Fr (τ * h)).1 hFr s hsM, AlgEquiv.mul_apply, hhs]
  exact hτ.apply_ne hk hs

/-! ## The precision `n(i) → ∞` -/

/-- The stage ideals `(2^{n(i)}, t^{n(i)})` at a common retained precision `n(i) → ∞` tend to zero
(PROVED, from Lane RC6's `stageIdeal_tendsToZero`). -/
theorem idealsTendToZero_stageIdeal_comp {prec : ℕ → ℕ} (hprec : Tendsto prec atTop atTop) :
    IdealsTendToZero (fun i => stageIdeal (prec i)) := by
  intro V hV
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero V hV)
  filter_upwards [hprec.eventually_ge_atTop N] with i hi
  exact hN (prec i) hi

/-! ## (5.4) over the genuine Galois groups -/

/-- **ELLIOT input: localization at a new inert prime is evaluation at the Frobenius square, at the
retained precision** (tex 4818–4820: "This also resolves the precision issue caused by
localization. Choose the new prime to match all original basis-cochain evaluations at a common
retained precision `n(i) → ∞`"; tex 5108–5109, "a new inert prime").

Data, at each coefficient stage `i`:
* `M i ⊆ ℚ̄` the compositum (finite Galois), `E i γ` the matrix (lifted to `Λ`) of the evaluations
  of the finitely many original basis cochains of stage `i`, which factor through the finite
  quotient `Gal(M_i/ℚ)`; at `g ∈ G_ℚ` they are evaluated through the genuine restriction,
  `E i (g|_{M_i})`;
* `S i` the previously used primes; `s` a square root of `k < 0` generating `K`;
* `L i ℓ Fr` the matrix (lifted to `Λ`) of the localizations of the same basis cochains at the new
  prime `ℓ`, at the place above `ℓ` at which `Fr` is an arithmetic Frobenius.

The input: for every new prime `ℓ ∉ S i`, unramified in `M i`, every Frobenius `Fr` at `ℓ` with
`Fr ∉ G_K` (`ℓ` inert in `K`), `L i ℓ Fr ≡ E i ((Fr^2)|_{M_i})` modulo `(2^{n(i)}, t^{n(i)})`: the
localization of an unramified cochain at the place of `K` above the inert prime `ℓ` is its value at
that place's Frobenius `Fr^2`. Kind: ELLIOT (its content is the GLUE fact just stated; the Selmer
complexes over `Λ` with their localization maps are not in the tree, so `L` is abstract). It is
true for the genuine localization matrices; it is satisfiable
(`ChebotarevNonVacuity.newPrimeLocalization_locMat`, with `L i ℓ Fr = E i ((Fr^2)|_{M_i})`) and has
content (`ChebotarevNonVacuity.not_newPrimeLocalization_shift`). -/
def NewPrimeLocalization {m n : Type*} (prec : ℕ → ℕ) (M : ℕ → IntermediateField ℚ Qbar)
    [∀ i, IsGalois ℚ (M i)] (s : Qbar) (S : ℕ → Finset ℕ)
    (E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n Lambda) (L : ℕ → ℕ → GQ → Matrix m n Lambda) :
    Prop :=
  ∀ (i ℓ : ℕ) (Fr : GQ), ℓ.Prime → ℓ ∉ S i → UnramifiedIn (M i) ℓ → IsFrobAt Fr ℓ → Fr s ≠ s →
    ∀ a b, L i ℓ Fr a b - E i (AlgEquiv.restrictNormal (Fr ^ 2) (M i)) a b ∈ stageIdeal (prec i)

/-- **(5.4) over the genuine Galois groups, for one instance** (tex 4755–4758, 4809–4827).

For the inner ultrafilter `U` on the coefficient stages: at every stage `i` there are a new prime
`ℓ i ∉ S i`, unramified in the compositum `M i`, and a genuine Frobenius `Fr i ∈ G_ℚ` at a place
above it realizing the representative, `Fr_i|_{M_i} = (τ h_i)|_{M_i}`, with `ℓ i` inert in
`K = ℚ(s)` (`Fr i s ≠ s`); and the inner ultralimits satisfy the exact equality of `Λ`-matrices
`L = E_{σ^2}` (5.4), where `L = lim_U L_i(ℓ_i, Fr_i)` is the matrix of localizations at the new
prime and `E_{σ^2} = lim_U E_i((τ h_i)^2|_{M_i})` the matrix of evaluations at `σ^2`, `σ = τ h`
(the inner-limit evaluation at a sequence, as Lane RC6's `rhoInf`/`cInf`).

The new prime is chosen stage by stage, at the precision `n(i)` of stage `i`, as the moving primes
are (tex 4269–4275: "Perform this construction separately at each coefficient stage, excluding ...
the previously chosen moving primes. ... the retained inner limit is the limit of the finite
diagrams of Lemma `ex:limits-inner-limit`"); no infinite-level Chebotarev is used (tex 5111–5112).

Definition (the proposition). It is PROVED from the single ELLIOT input `NewPrimeLocalization` by
`exactChebotarevRealizationGenuine_of_localization`. -/
def ExactChebotarevRealizationGenuine {m n : Type*} (U : Ultrafilter ℕ)
    (M : ℕ → IntermediateField ℚ Qbar) [∀ i, IsGalois ℚ (M i)] (τ : GQ) (h : ℕ → GQ) (s : Qbar)
    (S : ℕ → Finset ℕ) (E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n Lambda)
    (L : ℕ → ℕ → GQ → Matrix m n Lambda) : Prop :=
  ∃ (ℓ : ℕ → ℕ) (Fr : ℕ → GQ),
    (∀ i, (ℓ i).Prime ∧ ℓ i ∉ S i ∧ UnramifiedIn (M i) (ℓ i) ∧ IsFrobAt (Fr i) (ℓ i) ∧
      AlgEquiv.restrictNormal (Fr i) (M i) = AlgEquiv.restrictNormal (τ * h i) (M i) ∧
      Fr i s ≠ s) ∧
    ulimMat U (fun i => L i (ℓ i) (Fr i)) =
      ulimMat U (fun i => E i (AlgEquiv.restrictNormal ((τ * h i) ^ 2) (M i)))

/-- **(5.4) over the genuine Galois groups** (tex 4809–4827). Kind: PROVED from the ELLIOT input
`NewPrimeLocalization`; the finite-Chebotarev half is PROVED from the tree's Chebotarev theorem
(`exists_newPrime_frob`), the exact `Λ`-identity from Lane RC6's inner ultralimit
(`ulimMat_eq_of_sub_mem`, "Taking the same inner ultrafilter gives an exact equality of
`Λ`-matrices").

Hypotheses: `U` a nonprincipal ultrafilter on the coefficient stages; `n(i) → ∞` the common
retained precision; `M i` the stage-`i` compositum (finite Galois, containing `K = ℚ(s)`,
`s^2 = k < 0`); `τ` a complex conjugation; `h i` the stage-`i` component of the kernel element,
trivial on `K` (the exact kernel is trivial on the quadratic characters, tex 4766–4767); `S i` the
previously used primes; `E`, `L` the evaluation and localization matrices with the input
`NewPrimeLocalization`. Non-vacuity: `ChebotarevNonVacuity.genuine_instance`. -/
theorem exactChebotarevRealizationGenuine_of_localization {m n : Type*} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) {prec : ℕ → ℕ} (hprec : Tendsto prec atTop atTop)
    (M : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (M i)] [∀ i, IsGalois ℚ (M i)]
    {τ : GQ} (hτ : IsComplexConjugation τ) (h : ℕ → GQ) {k : ℚ} (hk : k < 0) {s : Qbar}
    (hs : s ^ 2 = algebraMap ℚ Qbar k) (hsM : ∀ i, s ∈ M i) (hhs : ∀ i, h i s = s)
    (S : ℕ → Finset ℕ) (E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n Lambda)
    (L : ℕ → ℕ → GQ → Matrix m n Lambda) (hloc : NewPrimeLocalization prec M s S E L) :
    ExactChebotarevRealizationGenuine U M τ h s S E L := by
  choose ℓ Fr hℓ using fun i => exists_newPrime_frob (M i) (S i) (τ * h i)
  have hinert : ∀ i, Fr i s ≠ s := fun i =>
    frob_apply_ne_of_restrict_eq hτ hk hs (hsM i) (hhs i) (hℓ i).2.2.2.2
  refine ⟨ℓ, Fr, fun i => ⟨(hℓ i).1, (hℓ i).2.1, (hℓ i).2.2.1, (hℓ i).2.2.2.1, (hℓ i).2.2.2.2,
    hinert i⟩, ?_⟩
  refine ZInQ.Manuscript.RC.Limits.ulimMat_eq_of_sub_mem (idealsTendToZero_stageIdeal_comp hprec)
    hU (Eventually.of_forall fun i a b => ?_)
  have hsq : AlgEquiv.restrictNormal (Fr i ^ 2) (M i) =
      AlgEquiv.restrictNormal ((τ * h i) ^ 2) (M i) := by
    rw [restrictNormal_pow', restrictNormal_pow', (hℓ i).2.2.2.2]
  have := hloc i (ℓ i) (Fr i) (hℓ i).1 (hℓ i).2.1 (hℓ i).2.2.1 (hℓ i).2.2.2.1 (hinert i) a b
  rwa [hsq] at this

/-- **(5.4) for every instance, with one inner ultrafilter** (tex 4823: "`L_j = E_{σ_j^2}`" for
each instance `j`; the old interface's `∀ j`). Kind: PROVED from `NewPrimeLocalization` at each
instance (`exactChebotarevRealizationGenuine_of_localization` applied instance by instance; the
companion field `K_j = ℚ(s_j)`, the composita and the previously used primes may depend on `j`). -/
theorem exactChebotarevRealizationGenuine_family {J m n : Type*} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) {prec : ℕ → ℕ} (hprec : Tendsto prec atTop atTop)
    (M : J → ℕ → IntermediateField ℚ Qbar) [∀ j i, FiniteDimensional ℚ (M j i)]
    [∀ j i, IsGalois ℚ (M j i)] {τ : GQ} (hτ : IsComplexConjugation τ) (h : J → ℕ → GQ)
    (k : J → ℚ) (hk : ∀ j, k j < 0) (s : J → Qbar) (hs : ∀ j, s j ^ 2 = algebraMap ℚ Qbar (k j))
    (hsM : ∀ j i, s j ∈ M j i) (hhs : ∀ j i, h j i (s j) = s j) (S : J → ℕ → Finset ℕ)
    (E : ∀ j i, (M j i ≃ₐ[ℚ] M j i) → Matrix m n Lambda)
    (L : J → ℕ → ℕ → GQ → Matrix m n Lambda)
    (hloc : ∀ j, NewPrimeLocalization prec (M j) (s j) (S j) (E j) (L j)) :
    ∀ j, ExactChebotarevRealizationGenuine U (M j) τ (h j) (s j) (S j) (E j) (L j) := fun j =>
  exactChebotarevRealizationGenuine_of_localization hU hprec (M j) hτ (h j) (hk j) (hs j) (hsM j)
    (hhs j) (S j) (E j) (L j) (hloc j)

/-- **(5.4) composed with the inclusion** (tex 4825–4829: "Only afterward compose with the
inclusion `I_j` from an `𝒪`-minimal model: `L_j I_j = E_{σ_j^2} I_j`. The denominators in `I_j`
may depend on `j`; equality (5.4) makes this irrelevant."). Kind: PROVED from
`ExactChebotarevRealizationGenuine`: the same new primes give `L I = E_{σ^2} I` for every ring
`R` receiving `Λ` and every inclusion matrix `I` over `R`. -/
theorem ExactChebotarevRealizationGenuine.mul_inclusion {m n p : Type*} [Fintype n]
    {U : Ultrafilter ℕ} {M : ℕ → IntermediateField ℚ Qbar} [∀ i, IsGalois ℚ (M i)] {τ : GQ}
    {h : ℕ → GQ} {s : Qbar} {S : ℕ → Finset ℕ} {E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n Lambda}
    {L : ℕ → ℕ → GQ → Matrix m n Lambda} (h54 : ExactChebotarevRealizationGenuine U M τ h s S E L)
    {R : Type*} [Semiring R] (f : Lambda →+* R) (I : Matrix n p R) :
    ∃ (ℓ : ℕ → ℕ) (Fr : ℕ → GQ),
      (∀ i, (ℓ i).Prime ∧ ℓ i ∉ S i ∧ UnramifiedIn (M i) (ℓ i) ∧ IsFrobAt (Fr i) (ℓ i) ∧
        AlgEquiv.restrictNormal (Fr i) (M i) = AlgEquiv.restrictNormal (τ * h i) (M i) ∧
        Fr i s ≠ s) ∧
      (ulimMat U (fun i => L i (ℓ i) (Fr i))).map f * I =
        (ulimMat U (fun i => E i (AlgEquiv.restrictNormal ((τ * h i) ^ 2) (M i)))).map f * I := by
  obtain ⟨ℓ, Fr, hℓ, hL⟩ := h54
  exact ⟨ℓ, Fr, hℓ, matrix_identity_mul_inclusion _ _ _ (by rw [hL])⟩

/-! ## The abstract interface of Lane RC16 at the finite stages -/

/-- The new inert primes of stage `i`, each with a chosen Frobenius: pairs `(ℓ, Fr)` with `ℓ` a
prime outside `S`, unramified in `M`, `Fr ∈ G_ℚ` an arithmetic Frobenius at a place above `ℓ`,
and `Fr ∉ G_K` (`Fr s ≠ s`). Definition. -/
def NewInertPrime (M : IntermediateField ℚ Qbar) (s : Qbar) (S : Finset ℕ) : Type :=
  {p : ℕ × GQ // p.1.Prime ∧ p.1 ∉ S ∧ UnramifiedIn M p.1 ∧ IsFrobAt p.2 p.1 ∧ p.2 s ≠ s}

/-- **Lane RC16's abstract interface `ExactChebotarevRealization`, met by the genuine data at every
finite stage** (tex 4809–4821). Kind: PROVED from `NewPrimeLocalization`.

At stage `i` (one instance, `J = Unit`): `Γ = Gal(M_i/ℚ)` the genuine finite Galois group of the
compositum; `τ`, `h` the restrictions of the complex conjugation and of the kernel element;
`P = NewInertPrime (M i) s (S i)` the new inert primes with their genuine Frobenius elements and
`frob (ℓ, Fr) = Fr|_{M_i}`; the coefficient ring is the finite stage `Λ/(2^{n(i)}, t^{n(i)})`, in
which `L = E_{frob^2}` holds exactly. So the abstract interface is no longer an input: for the
genuine data it is a theorem. Over `Λ` itself the evaluations do not factor through one finite
group; there the exact identity is the inner-limit statement `ExactChebotarevRealizationGenuine`. -/
theorem exactChebotarevRealization_stage {m n : Type*} {prec : ℕ → ℕ}
    (M : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (M i)] [∀ i, IsGalois ℚ (M i)]
    {τ : GQ} (hτ : IsComplexConjugation τ) (h : ℕ → GQ) {k : ℚ} (hk : k < 0) {s : Qbar}
    (hs : s ^ 2 = algebraMap ℚ Qbar k) (hsM : ∀ i, s ∈ M i) (hhs : ∀ i, h i s = s)
    (S : ℕ → Finset ℕ) (E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n Lambda)
    (L : ℕ → ℕ → GQ → Matrix m n Lambda) (hloc : NewPrimeLocalization prec M s S E L) (i : ℕ) :
    ExactChebotarevRealization (J := Unit) (Λ := Lambda ⧸ stageIdeal (prec i))
      (fun _ => M i ≃ₐ[ℚ] M i) (fun _ => AlgEquiv.restrictNormal τ (M i))
      (fun _ => AlgEquiv.restrictNormal (h i) (M i)) (fun _ => NewInertPrime (M i) s (S i))
      (fun _ p => AlgEquiv.restrictNormal p.1.2 (M i))
      (fun _ γ => (E i γ).map (Ideal.Quotient.mk (stageIdeal (prec i))))
      (fun _ p => (L i p.1.1 p.1.2).map (Ideal.Quotient.mk (stageIdeal (prec i)))) := by
  intro _
  obtain ⟨ℓ, Fr, hp, hS, hur, hF, hres⟩ := exists_newPrime_frob (M i) (S i) (τ * h i)
  have hinert : Fr s ≠ s := frob_apply_ne_of_restrict_eq hτ hk hs (hsM i) (hhs i) hres
  refine ⟨⟨(ℓ, Fr), hp, hS, hur, hF, hinert⟩, ?_, ?_⟩
  · change AlgEquiv.restrictNormal Fr (M i) = _
    rw [hres, restrictNormal_mul']
  · change (L i ℓ Fr).map _ = (E i (AlgEquiv.restrictNormal Fr (M i) ^ 2)).map _
    ext a b
    simp only [Matrix.map_apply]
    rw [← restrictNormal_pow', Ideal.Quotient.eq]
    exact hloc i ℓ Fr hp hS hur hF hinert a b

/-! ## Non-vacuity -/

namespace ChebotarevNonVacuity

/-- A square root of `-1` in `ℚ̄`. -/
theorem exists_sqrt_neg_one : ∃ s : Qbar, s ^ 2 = algebraMap ℚ Qbar (-1) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (algebraMap ℚ Qbar (-1))
  exact ⟨z, by rw [hz, sq]⟩

/-- `i = √-1 ∈ ℚ̄`. -/
def sqrtNegOne : Qbar := exists_sqrt_neg_one.choose

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = algebraMap ℚ Qbar (-1) :=
  exists_sqrt_neg_one.choose_spec

/-- The Galois closure of `ℚ(√-1)` in `ℚ̄` (equal to `ℚ(√-1)`; only its finiteness, its normality
and `√-1 ∈ M` are used), a finite Galois compositum containing `K = ℚ(√-1)`. -/
def Mi : IntermediateField ℚ Qbar :=
  IntermediateField.normalClosure ℚ (IntermediateField.adjoin ℚ {sqrtNegOne}) Qbar

instance : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {sqrtNegOne}) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

instance : FiniteDimensional ℚ Mi := normalClosure.is_finiteDimensional ℚ _ Qbar

instance : Normal ℚ Mi := normalClosure.normal ℚ _ Qbar

instance : IsGalois ℚ Mi := ⟨⟩

theorem sqrtNegOne_mem : sqrtNegOne ∈ Mi :=
  (IntermediateField.adjoin ℚ {sqrtNegOne}).le_normalClosure
    (IntermediateField.mem_adjoin_simple_self ℚ sqrtNegOne)

/-- A complex conjugation. -/
def tau : GQ := exists_isComplexConjugation.choose

theorem tau_spec : IsComplexConjugation tau := exists_isComplexConjugation.choose_spec

/-- Evaluation matrices on `Gal(M/ℚ)` that see the group: `1` at the identity, `0` elsewhere. -/
def evalMat (γ : Mi ≃ₐ[ℚ] Mi) : Matrix (Fin 2) (Fin 2) Lambda := by
  classical
  exact if γ = 1 then 1 else 0

/-- The localization matrices equal to the evaluation at the Frobenius square: they satisfy the
ELLIOT input. -/
def locMat (_ : ℕ) (_ : ℕ) (Fr : GQ) : Matrix (Fin 2) (Fin 2) Lambda :=
  evalMat (AlgEquiv.restrictNormal (Fr ^ 2) Mi)

/-- **The ELLIOT input `NewPrimeLocalization` is satisfiable** (with `L i ℓ Fr = E((Fr^2)|_M)`). -/
theorem newPrimeLocalization_locMat :
    NewPrimeLocalization (fun i => i) (fun _ => Mi) sqrtNegOne (fun _ => ∅) (fun _ => evalMat)
      locMat := by
  intro i ℓ Fr _ _ _ _ _ a b
  simp [locMat]

/-- **All hypotheses of `exactChebotarevRealizationGenuine_of_localization` hold together**
(non-vacuity): `U` the hyperfilter on `ℕ` (nonprincipal), `n(i) = i`, `M i = Mi` (the Galois
closure of `ℚ(√-1)`), `τ` a complex conjugation, `h i = 1`, `k = -1`, `S i = ∅`, the evaluation
matrices `evalMat`, the localization matrices `locMat`. The conclusion (5.4) then holds with
genuine new primes inert in `ℚ(√-1)`. -/
theorem genuine_instance :
    ExactChebotarevRealizationGenuine (hyperfilter ℕ) (fun _ => Mi) tau (fun _ => 1) sqrtNegOne
      (fun _ => ∅) (fun _ => evalMat) locMat :=
  exactChebotarevRealizationGenuine_of_localization hyperfilter_le_cofinite
    (prec := fun i => i) tendsto_id (fun _ => Mi) tau_spec (fun _ => 1) (k := -1) (by norm_num)
    sqrtNegOne_sq (fun _ => sqrtNegOne_mem) (fun _ => rfl) (fun _ => ∅) (fun _ => evalMat) locMat
    newPrimeLocalization_locMat

/-- `1 ∉ (2^n, t^n)` for `n ≥ 1`. -/
theorem one_not_mem_stageIdeal {n : ℕ} (hn : 1 ≤ n) : (1 : Lambda) ∉ stageIdeal n := by
  rw [ZInQ.Manuscript.RC.Limits.mem_stageIdeal_iff]
  intro h
  have h0 := h 0 (by omega)
  simp only [PowerSeries.coeff_one, ↓reduceIte] at h0
  have h2 : (2 : ℤ_[2]) ∣ 1 := (dvd_pow_self 2 (by omega : n ≠ 0)).trans h0
  have hu : IsUnit (2 : ℤ_[2]) := isUnit_of_dvd_one h2
  have := PadicInt.p_nonunit (p := 2)
  exact this (by exact_mod_cast hu)

/-- **The ELLIOT input `NewPrimeLocalization` has content**: it fails for the localization
matrices shifted by the identity, `L' = E((Fr^2)|_M) + 1`, at precision `n(i) = i`; the
finite-Chebotarev half supplies a new inert prime at stage `1`, where the shift is not in
`(2, t)`. -/
theorem not_newPrimeLocalization_shift :
    ¬ NewPrimeLocalization (fun i => i) (fun _ => Mi) sqrtNegOne (fun _ => ∅) (fun _ => evalMat)
      (fun i ℓ Fr => locMat i ℓ Fr + 1) := by
  intro hloc
  obtain ⟨ℓ, Fr, hp, hS, hur, hF, hres⟩ := exists_newPrime_frob Mi ∅ (tau * 1)
  have hinert : Fr sqrtNegOne ≠ sqrtNegOne :=
    frob_apply_ne_of_restrict_eq tau_spec (k := -1) (by norm_num) sqrtNegOne_sq sqrtNegOne_mem
      rfl hres
  have h := hloc 1 ℓ Fr hp hS hur hF hinert 0 0
  simp only [Matrix.add_apply, locMat, add_sub_cancel_left, Matrix.one_apply_eq] at h
  exact one_not_mem_stageIdeal le_rfl h

end ChebotarevNonVacuity

end ZInQ.Manuscript.RC.Uniform

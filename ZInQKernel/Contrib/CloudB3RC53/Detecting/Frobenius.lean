import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.OneProof.RC.Uniform.KernelDetection

/-!
# Detecting primes, part 2: the Frobenius half of the finite Chebotarev realization

Item (a) of the detecting-prime sizing. RC16's interface `ExactChebotarevRealization`
(`RC/Uniform/KernelDetection.lean`, tex 4809–4831) asks, for each finite quotient
`Γ_j = Gal(M_j/ℚ)`, for a new prime `ℓ` whose Frobenius is `τ_j h_j`, together with the exact
identity (5.4) `L_j = E_{σ_j²}`. All `PROVED`:

* `AdmPrime M S`: admissible new primes. These are a rational prime `p ∉ S` with a chosen
  unramified prime `Q | p` of `𝓞_M` admitting a Frobenius; `AdmPrime.frob` is that Frobenius;
* `frob_unique`: the Frobenius at an unramified prime is unique (Mathlib);
* `exists_admPrime_frob`: every `σ ∈ Gal(M/ℚ)` is the Frobenius of an admissible new prime. This
  uses `ZInQ.Contrib.chebotarevExists`, from Tau Ceti's Chebotarev density theorem;
* `frobenius_realization`: the Frobenius half of the interface, `frob ℓ = τ_j h_j`;
* `exactChebotarevRealization_of_exactness`: the interface follows from the exactness (5.4) at the
  realized primes. That exactness (finite stages of precision and the inner ultrafilter) remains
  an input (item 5 of the sizing).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Detecting

open NumberField

variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]

/-- **An admissible new prime** for `M/ℚ` outside the finite set `S` of used primes: a rational
prime `p ∉ S` with a chosen prime `Q` of `𝓞_M` above it, unramified, at which some element of
`Gal(M/ℚ)` is an arithmetic Frobenius. -/
structure AdmPrime (S : Finset ℕ) where
  p : ℕ
  prime : p.Prime
  not_mem : p ∉ S
  Q : Ideal (𝓞 M)
  isPrime : Q.IsPrime
  under : Q.under ℤ = Ideal.span {(p : ℤ)}
  unram : Algebra.IsUnramifiedAt ℤ Q
  hasFrob : ∃ σ : M ≃ₐ[ℚ] M, IsArithFrobAt ℤ σ Q

variable {M}

/-- The Frobenius at the chosen place of an admissible prime. -/
def AdmPrime.frob {S : Finset ℕ} (ℓ : AdmPrime M S) : M ≃ₐ[ℚ] M := ℓ.hasFrob.choose

theorem AdmPrime.frob_spec {S : Finset ℕ} (ℓ : AdmPrime M S) : IsArithFrobAt ℤ ℓ.frob ℓ.Q :=
  ℓ.hasFrob.choose_spec

/-- **The Frobenius at an unramified prime is unique** (Mathlib's
`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`, transported to `Gal(M/ℚ)`). -/
theorem frob_unique {Q : Ideal (𝓞 M)} [Q.IsPrime] [Algebra.IsUnramifiedAt ℤ Q]
    {σ τ : M ≃ₐ[ℚ] M} (hσ : IsArithFrobAt ℤ σ Q) (hτ : IsArithFrobAt ℤ τ Q) : σ = τ := by
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 M) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt (R := ℤ) hσ hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) y
  have ha := congrArg (fun f => ((f a : 𝓞 M) : M)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 M) : M)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : M ≃ₐ[ℚ] M) (c : 𝓞 M), g (algebraMap (𝓞 M) M c) = ((g • c : 𝓞 M) : M) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-- **(a) Every element of `Gal(M/ℚ)` is the Frobenius of an admissible new prime** (`PROVED`
from `ZInQ.Contrib.chebotarevExists`, Tau Ceti's Chebotarev density theorem, and the uniqueness
of the Frobenius at unramified primes). -/
theorem exists_admPrime_frob (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : ∃ ℓ : AdmPrime M S, ℓ.frob = σ := by
  obtain ⟨p, hp, hpS, Q, hQ, hunder, hunr, hfrob⟩ := ZInQ.Contrib.chebotarevExists M S σ
  let ℓ : AdmPrime M S := ⟨p, hp, hpS, Q, hQ, hunder, hunr, ⟨σ, hfrob⟩⟩
  refine ⟨ℓ, ?_⟩
  have : Q.IsPrime := hQ
  have : Algebra.IsUnramifiedAt ℤ Q := hunr
  exact frob_unique ℓ.frob_spec hfrob

/-- **(a) The Frobenius half of RC16's `ExactChebotarevRealization`** (`PROVED`): for finite
Galois fields `M_j/ℚ`, used-prime sets `S_j` and elements `τ_j, h_j`, there is an admissible new
prime whose Frobenius is `τ_j h_j`. -/
theorem frobenius_realization {J : Type} (Mj : J → Type) [∀ j, Field (Mj j)]
    [∀ j, NumberField (Mj j)] [∀ j, IsGalois ℚ (Mj j)] (S : J → Finset ℕ)
    (τ h : ∀ j, Mj j ≃ₐ[ℚ] Mj j) :
    ∀ j, ∃ ℓ : AdmPrime (Mj j) (S j), ℓ.frob = τ j * h j :=
  fun j => exists_admPrime_frob (S j) (τ j * h j)

/-- **RC16's `ExactChebotarevRealization` from the exactness (5.4) alone** (`PROVED`): with
`Γ_j = Gal(M_j/ℚ)` and the admissible new primes with their Frobenius, the interface holds as
soon as the localization matrix at a prime with Frobenius `τ_j h_j` is the evaluation matrix at
its square. That exactness (the finite stages of precision and the inner ultrafilter of tex
4809–4831) is the remaining input. -/
theorem exactChebotarevRealization_of_exactness {J Λ m n : Type} (Mj : J → Type)
    [∀ j, Field (Mj j)] [∀ j, NumberField (Mj j)] [∀ j, IsGalois ℚ (Mj j)] (S : J → Finset ℕ)
    (τ h : ∀ j, Mj j ≃ₐ[ℚ] Mj j) (E : ∀ j, (Mj j ≃ₐ[ℚ] Mj j) → Matrix m n Λ)
    (L : ∀ j, AdmPrime (Mj j) (S j) → Matrix m n Λ)
    (hexact : ∀ j (ℓ : AdmPrime (Mj j) (S j)), ℓ.frob = τ j * h j → L j ℓ = E j (ℓ.frob ^ 2)) :
    ZInQ.Manuscript.RC.Uniform.ExactChebotarevRealization
      (fun j => Mj j ≃ₐ[ℚ] Mj j) τ h (fun j => AdmPrime (Mj j) (S j)) (fun j ℓ => ℓ.frob) E L := by
  intro j
  obtain ⟨ℓ, hℓ⟩ := exists_admPrime_frob (S j) (τ j * h j)
  exact ⟨ℓ, hℓ, hexact j ℓ hℓ⟩

end ZInQ.Contrib.CloudB3RC53.Detecting

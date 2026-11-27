import ZInQKernel.Contrib.OneProof.RC.Uniform.ChebotarevRealization
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev

/-!
# Lane RC27: the Tate precision in (5.4), and the arithmetic content of its new primes

Manuscript (11/5 version), Lemma `ex:limits-kernel-detection`, tex 4810–4813: "Each of the finitely
many original basis cochains in degrees zero through two factors through a finite quotient.
Include their quotient, the required Tate precision, ring-class and quadratic fields and old
diagrams in one compositum."; tex 5108–5109: "realize this choice by a new inert prime, avoiding
every previously used prime".

Companion of `ChebotarevRealization.lean` (the genuine (5.4), `ExactChebotarevRealizationGenuine`),
using Lane RC22's Tate share (`RC/GlueSweep/TateChebotarev.lean`: `ℚ(A[2^M]) ⊆ ℚ̄`, agreement on it
gives congruent Tate matrices; a Frobenius at an odd prime `p` acts on `2`-power roots of unity as
`ζ ↦ ζ^p`).

* `exactChebotarevRealizationGenuine_tate` (PROVED): if the stage-`i` compositum contains
  `ℚ(A[2^{n(i)}])` for an elliptic curve `A/ℚ` ("the required Tate precision"), the new primes of
  (5.4) have Frobenius elements with `ρ₂(Fr_i) ≡ ρ₂(τ h_i) (mod 2^{n(i)})`.
* `newPrime_mod_four`, `ExactChebotarevRealizationGenuine.mod_four` (PROVED): for `K = ℚ(√-1)` and
  `2` among the excluded primes, every new inert prime of (5.4) is `≡ 3 (mod 4)`. So the genuine
  statement has arithmetic content which no choice of junk data supplies (Lane RC16's abstract
  interface was met by `P j = Unit` and a constant `frob`).
* Non-vacuity: `ChebotarevNonVacuity.genuine_instance_two` (all hypotheses together, with `2`
  excluded) and `ChebotarevNonVacuity.genuine_instance_mod_four` (its new primes are `≡ 3 mod 4`);
  `ChebotarevNonVacuity.tate_instance` (the hypotheses of the Tate corollary hold together for any
  elliptic curve `A/ℚ`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Uniform

open Filter
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (IsFrobAt)
open ZInQ.Manuscript.RC.Limits (ulimMat)
open scoped PowerSeries.WithPiTopology

/-- **The required Tate precision** (tex 4810–4813). Kind: PROVED from
`ExactChebotarevRealizationGenuine`: if every stage compositum `M i` contains `ℚ(A[2^{n(i)}])`
(Lane RC22's `torsField A (n i)`), the new primes and Frobenius elements of (5.4) also satisfy
`ρ₂(Fr_i) ≡ ρ₂(τ h_i) (mod 2^{n(i)})` for the `2`-adic Tate matrices of `A` (Lane RC22's
`tateMatrix_congr_of_eqOn_torsField`): the restrictions of the single automorphism `τ h_i` "agree
on intersections" (tex 4815). Non-vacuity: `ChebotarevNonVacuity.tate_instance`. -/
theorem exactChebotarevRealizationGenuine_tate (A : WeierstrassCurve ℚ) [A.IsElliptic]
    {m n : Type*} {U : Ultrafilter ℕ} {prec : ℕ → ℕ} {M : ℕ → IntermediateField ℚ Qbar}
    [∀ i, IsGalois ℚ (M i)] {τ : GalQ} {h : ℕ → GalQ} {s : Qbar} {S : ℕ → Finset ℕ}
    {E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n ZInQ.Manuscript.RC.Limits.Lambda}
    {L : ℕ → ℕ → GalQ → Matrix m n ZInQ.Manuscript.RC.Limits.Lambda}
    (hT : ∀ i, ZInQ.Manuscript.RC.GlueSweep.Tate.torsField A (prec i) ≤ M i)
    (h54 : ExactChebotarevRealizationGenuine U M τ h s S E L) :
    ∃ (ℓ : ℕ → ℕ) (Fr : ℕ → GalQ),
      (∀ i, (ℓ i).Prime ∧ ℓ i ∉ S i ∧ UnramifiedIn (M i) (ℓ i) ∧ IsFrobAt (Fr i) (ℓ i) ∧
        AlgEquiv.restrictNormal (Fr i) (M i) = AlgEquiv.restrictNormal (τ * h i) (M i) ∧
        Fr i s ≠ s ∧
        (PadicInt.toZModPow (prec i)).mapMatrix (tateMatrix A (Fr i)) =
          (PadicInt.toZModPow (prec i)).mapMatrix (tateMatrix A (τ * h i))) ∧
      ulimMat U (fun i => L i (ℓ i) (Fr i)) =
        ulimMat U (fun i => E i (AlgEquiv.restrictNormal ((τ * h i) ^ 2) (M i))) := by
  obtain ⟨ℓ, Fr, hℓ, hL⟩ := h54
  refine ⟨ℓ, Fr, fun i => ⟨(hℓ i).1, (hℓ i).2.1, (hℓ i).2.2.1, (hℓ i).2.2.2.1,
    (hℓ i).2.2.2.2.1, (hℓ i).2.2.2.2.2, ?_⟩, hL⟩
  refine ZInQ.Manuscript.RC.GlueSweep.Tate.tateMatrix_congr_of_eqOn_torsField A fun x hx => ?_
  exact (restrictNormal_eq_restrictNormal_iff (M i) _ _).1 (hℓ i).2.2.2.2.1 x (hT i hx)

/-- **A new prime inert in `ℚ(√-1)` is `≡ 3 (mod 4)`** (PROVED). If `Fr` is a Frobenius at an odd
prime `ℓ` and `Fr` moves a square root `s` of `-1`, then `ℓ ≡ 3 (mod 4)`: `s` is a `4`-th root of
unity, so `Fr s = s^ℓ` (Lane RC22's `apply_eq_pow_of_isFrobAt`), and `s^ℓ = s` for
`ℓ ≡ 1 (mod 4)`. -/
theorem newPrime_mod_four {Fr : GalQ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hF : IsFrobAt Fr ℓ)
    {s : Qbar} (hs : s ^ 2 = -1) (hmove : Fr s ≠ s) : ℓ % 4 = 3 := by
  have h4 : s ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
    norm_num
  have hFs : Fr s = s ^ ℓ :=
    ZInQ.Manuscript.RC.GlueSweep.Tate.apply_eq_pow_of_isFrobAt hℓ2 hF (M := 2) s
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4)
  have hodd : ℓ % 2 = 1 := Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2)
  have h13 : ℓ % 4 = 1 ∨ ℓ % 4 = 3 := by omega
  rcases h13 with h1 | h3
  · exfalso
    apply hmove
    rw [hFs, ← Nat.div_add_mod ℓ 4, h1, pow_add, pow_mul, h4, one_pow, one_mul, pow_one]
  · exact h3

/-- **For `K = ℚ(√-1)` the new primes of (5.4) are `≡ 3 (mod 4)`** (PROVED from
`ExactChebotarevRealizationGenuine` and `newPrime_mod_four`, when `2` is among the excluded primes
`S i`). The genuine (5.4) thus asserts arithmetic facts about actual primes. -/
theorem ExactChebotarevRealizationGenuine.mod_four {m n : Type*} {U : Ultrafilter ℕ}
    {M : ℕ → IntermediateField ℚ Qbar} [∀ i, IsGalois ℚ (M i)] {τ : GalQ} {h : ℕ → GalQ}
    {s : Qbar} {S : ℕ → Finset ℕ}
    {E : ∀ i, (M i ≃ₐ[ℚ] M i) → Matrix m n ZInQ.Manuscript.RC.Limits.Lambda}
    {L : ℕ → ℕ → GalQ → Matrix m n ZInQ.Manuscript.RC.Limits.Lambda}
    (h54 : ExactChebotarevRealizationGenuine U M τ h s S E L) (hs : s ^ 2 = -1)
    (h2 : ∀ i, 2 ∈ S i) :
    ∃ (ℓ : ℕ → ℕ) (Fr : ℕ → GalQ),
      (∀ i, (ℓ i).Prime ∧ ℓ i % 4 = 3 ∧ ℓ i ∉ S i ∧ IsFrobAt (Fr i) (ℓ i) ∧
        AlgEquiv.restrictNormal (Fr i) (M i) = AlgEquiv.restrictNormal (τ * h i) (M i)) ∧
      ulimMat U (fun i => L i (ℓ i) (Fr i)) =
        ulimMat U (fun i => E i (AlgEquiv.restrictNormal ((τ * h i) ^ 2) (M i))) := by
  obtain ⟨ℓ, Fr, hℓ, hL⟩ := h54
  refine ⟨ℓ, Fr, fun i => ⟨(hℓ i).1, ?_, (hℓ i).2.1, (hℓ i).2.2.2.1, (hℓ i).2.2.2.2.1⟩, hL⟩
  have hne2 : ℓ i ≠ 2 := fun h' => (hℓ i).2.1 (h' ▸ h2 i)
  exact newPrime_mod_four (hℓ i).1 hne2 (hℓ i).2.2.2.1 hs (hℓ i).2.2.2.2.2

namespace ChebotarevNonVacuity

/-- The ELLIOT input with `2` excluded (`S i = {2}`), satisfied by `L i ℓ Fr = E((Fr^2)|_M)`. -/
theorem newPrimeLocalization_locMat_two :
    NewPrimeLocalization (fun i => i) (fun _ => Mi) sqrtNegOne (fun _ => {2}) (fun _ => evalMat)
      locMat := by
  intro i ℓ Fr _ _ _ _ _ a b
  simp [locMat]

/-- **All hypotheses of `exactChebotarevRealizationGenuine_of_localization` hold together with `2`
excluded** (non-vacuity, `K = ℚ(√-1)`, `S i = {2}`). -/
theorem genuine_instance_two :
    ExactChebotarevRealizationGenuine (hyperfilter ℕ) (fun _ => Mi) tau (fun _ => 1) sqrtNegOne
      (fun _ => {2}) (fun _ => evalMat) locMat :=
  exactChebotarevRealizationGenuine_of_localization hyperfilter_le_cofinite
    (prec := fun i => i) tendsto_id (fun _ => Mi) tau_spec (fun _ => 1) (k := -1) (by norm_num)
    sqrtNegOne_sq (fun _ => sqrtNegOne_mem) (fun _ => rfl) (fun _ => {2}) (fun _ => evalMat) locMat
    newPrimeLocalization_locMat_two

/-- **The new primes of the genuine instance are `≡ 3 (mod 4)`** (PROVED): content no junk model
can supply. -/
theorem genuine_instance_mod_four :
    ∃ (ℓ : ℕ → ℕ) (Fr : ℕ → GalQ),
      (∀ i, (ℓ i).Prime ∧ ℓ i % 4 = 3 ∧ ℓ i ∉ ({2} : Finset ℕ) ∧ IsFrobAt (Fr i) (ℓ i) ∧
        AlgEquiv.restrictNormal (Fr i) Mi = AlgEquiv.restrictNormal (tau * 1) Mi) ∧
      ulimMat (hyperfilter ℕ) (fun i => locMat i (ℓ i) (Fr i)) =
        ulimMat (hyperfilter ℕ) (fun _ => evalMat (AlgEquiv.restrictNormal ((tau * 1) ^ 2) Mi)) :=
  genuine_instance_two.mod_four (by rw [sqrtNegOne_sq, map_neg, map_one])
    (fun _ => Finset.mem_singleton_self 2)

/-- The compositum of `ℚ(√-1)` and `ℚ(A[2^i])`, Galois closure in `ℚ̄`. -/
def MiTate (A : WeierstrassCurve ℚ) (i : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.normalClosure ℚ
    (↥(IntermediateField.adjoin ℚ {sqrtNegOne} ⊔ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField A i))
    Qbar

instance (A : WeierstrassCurve ℚ) [A.IsElliptic] (i : ℕ) : FiniteDimensional ℚ (MiTate A i) :=
  normalClosure.is_finiteDimensional ℚ _ Qbar

instance (A : WeierstrassCurve ℚ) (i : ℕ) : Normal ℚ (MiTate A i) :=
  normalClosure.normal ℚ _ Qbar

instance (A : WeierstrassCurve ℚ) (i : ℕ) : IsGalois ℚ (MiTate A i) := ⟨⟩

theorem le_miTate (A : WeierstrassCurve ℚ) (i : ℕ) :
    IntermediateField.adjoin ℚ {sqrtNegOne} ⊔ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField A i ≤
      MiTate A i :=
  IntermediateField.le_normalClosure _

/-- **The hypotheses of `exactChebotarevRealizationGenuine_tate` hold together** for every elliptic
curve `A/ℚ` (non-vacuity): the composita `ℚ(√-1, A[2^i])` (Galois closure), a complex conjugation,
`h i = 1`, `S i = {2}`, `n(i) = i`, the evaluation matrices `1` at the identity and `0` elsewhere,
and the localization matrices `E((Fr^2)|_M)`. -/
theorem tate_instance (A : WeierstrassCurve ℚ) [A.IsElliptic] :
    ExactChebotarevRealizationGenuine (hyperfilter ℕ) (MiTate A) tau (fun _ => 1) sqrtNegOne
        (fun _ => {2})
        (fun _ γ => by classical exact if γ = 1 then (1 : Matrix (Fin 2) (Fin 2) _) else 0)
        (fun i _ Fr => by
          classical
          exact if AlgEquiv.restrictNormal (Fr ^ 2) (MiTate A i) = 1 then
            (1 : Matrix (Fin 2) (Fin 2) ZInQ.Manuscript.RC.Limits.Lambda) else 0) ∧
      ∀ i, ZInQ.Manuscript.RC.GlueSweep.Tate.torsField A i ≤ MiTate A i := by
  refine ⟨exactChebotarevRealizationGenuine_of_localization hyperfilter_le_cofinite
    (prec := fun i => i) tendsto_id (MiTate A) tau_spec (fun _ => 1) (k := -1) (by norm_num)
    sqrtNegOne_sq (fun i => le_miTate A i
      (le_sup_left (b := ZInQ.Manuscript.RC.GlueSweep.Tate.torsField A i)
        (IntermediateField.mem_adjoin_simple_self ℚ sqrtNegOne)))
    (fun _ => rfl) (fun _ => {2}) _ _ ?_, fun i => (le_miTate A i).trans' le_sup_right⟩
  intro i ℓ Fr _ _ _ _ _ a b
  simp

end ChebotarevNonVacuity

end ZInQ.Manuscript.RC.Uniform

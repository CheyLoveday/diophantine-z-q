import ZInQKernel.Contrib.CloudB3E2Norm.GenusRingClass
import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup

/-!
# The quadratic part of the character condition, from genus theory

Manuscript `diophantine_zq.tex`, tex 2683–2684 (`h_x = ∏_{q ∈ Q} (q*)^{λ_q(x)}`), 2847–2855
(`θ = χ_h Ψ` a character of `Δ_f`).

* `sqrt_prod_mem_ringClassField` (PROVED): for `K` imaginary quadratic, a finite set `Qs` of odd
  primes dividing `f`, and `s ∈ K̄` with `s² = ∏_{q ∈ Qs} q*`, `s` lies in the ring class field
  `H_f` (`GenusRingClass.sqrt_qstar_mem_ringClassField` for each `q`, `H_q ⊆ H_f`).
* **`quadOfDelta_of_genus`** (PROVED): `QuadOfDelta f` for `h = ∏_{q ∈ Qs} q*` (the address's
  `h_x`, its primes dividing `f`), when the primes of `f` lie in `S₁`: an element fixing `H_f`
  fixes the square root `s` of `h`, so `χ_h` is trivial on it.

* `qstar_eq_rc`, `family_h_eq_prod` (PROVED): the address's `h_x = ∏_{λ_q(x) = 1} q*`;
  **`quadOfDelta_family`** (PROVED): `QuadOfDelta f` for `h = h_x` of an admissible family.
* **`thetaOfDelta_of_genus`** (PROVED): with lane E1's factorisation clause for the moving
  character at the conductor `r` (`H20PiBridge.piOfDelta_of_moving`), `ThetaOfDelta f` — the
  condition `hα` of the actual Heegner points — at any `f` divisible by `r` and by the primes of
  `h`, with the primes of `f` in `S₁`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3E2.GenusSquare ZInQ.Contrib.CloudB3E2.GenusRingClass

variable {K : Type} [Field K] [NumberField K]

/-- **A square root of `∏_{q ∈ Qs} q*` lies in `H_f`** for odd primes `q ∣ f` (PROVED). -/
theorem sqrt_prod_mem_ringClassField (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, q.Prime ∧ q ≠ 2) (f : ℕ) [NeZero f]
    (hf : ∀ q ∈ Qs, q ∣ f) {s : AlgebraicClosure K}
    (hs : s ^ 2 = algebraMap K _ ((∏ q ∈ Qs, qstar q : ℤ) : K)) :
    s ∈ toAlgClosure (ringClassField (conductorOrder K f)) := by
  classical
  -- square roots of the `q*` in `Kˢ`, each in `H_f`
  have hx : ∀ q ∈ Qs, ∃ x : SeparableClosure K,
      x ^ 2 = algebraMap K _ ((qstar q : ℤ) : K) ∧ x ∈ ringClassField (conductorOrder K f) := by
    intro q hq
    have : Fact q.Prime := ⟨(hQs q hq).1⟩
    have : NeZero q := ⟨(hQs q hq).1.ne_zero⟩
    have : NeZero ((2 : ℕ) : SeparableClosure K) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K (SeparableClosure K)
      ((qstar q : ℤ) : K)) 2
    exact ⟨x, hx, ringClassField_mono (conductorOrder_le_of_dvd (hf q hq))
      (sqrt_qstar_mem_ringClassField hK2 hTC (hQs q hq).2 hx)⟩
  choose! x hx2 hxH using hx
  set y : SeparableClosure K := ∏ q ∈ Qs, x q
  have hyH : y ∈ ringClassField (conductorOrder K f) :=
    prod_mem fun q hq => hxH q hq
  have hy2 : y ^ 2 = algebraMap K _ ((∏ q ∈ Qs, qstar q : ℤ) : K) := by
    rw [← Finset.prod_pow, Finset.prod_congr rfl hx2, ← map_prod, Int.cast_prod]
  -- `s = ± y` in `K̄`
  set y' : AlgebraicClosure K := (separableClosure K (AlgebraicClosure K)).val y
  have hy'H : y' ∈ toAlgClosure (ringClassField (conductorOrder K f)) :=
    (IntermediateField.mem_map _).2 ⟨y, hyH, rfl⟩
  have hy'2 : y' ^ 2 = algebraMap K _ ((∏ q ∈ Qs, qstar q : ℤ) : K) := by
    rw [← map_pow, hy2]
    exact AlgHom.commutes _ _
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans hy'2.symm) with h | h
  · rw [h]; exact hy'H
  · rw [h]; exact neg_mem hy'H

variable {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S)
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)

include hs in
/-- **`QuadOfDelta f` from genus theory** (PROVED): for `K` imaginary quadratic and
`h = ∏_{q ∈ Qs} q*` with `Qs` odd primes dividing `f` (the primes of `f` in `S₁`), `χ_h` is
trivial on the elements fixing `H_f`. -/
theorem quadOfDelta_of_genus (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, q.Prime ∧ q ≠ 2) (f : ℕ) [NeZero f]
    (hf : ∀ q ∈ Qs, q ∣ f) (hh : h = ((∏ q ∈ Qs, qstar q : ℤ) : K))
    (hSf : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) :
    QuadOfDelta hS h1 s hs hs0 f := by
  intro g hg
  have hsH : (s : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f)) := by
    refine sqrt_prod_mem_ringClassField hK2 hTC Qs hQs f hf ?_
    have := congrArg (fun z : KS K S₀ => (z : AlgebraicClosure K)) hs
    rw [IntermediateField.coe_pow] at this
    rw [this, hh]
    rfl
  have hs1 : (s : AlgebraicClosure K) ∈ unramifiedOutside K S₁ :=
    ringClassField_le_KS _ S₁ (cond_primes f hSf) hsH
  have hfix := hg ⟨s, hs1⟩ hsH
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S g
  have e1 := congrArg Subtype.val hfix
  rw [show inflMap K h1 (resAbs K S σ) = resAbs K S₁ σ from resUnr_comp K h1 σ] at e1
  change ((galS K S₁ (resAbs K S₁ σ) ⟨s, hs1⟩ : unramifiedOutside K S₁) : AlgebraicClosure K) =
    s at e1
  rw [show inflMap K hS (resAbs K S σ) = resAbs K S₀ σ from resUnr_comp K hS σ]
  have e0 : galS K S₀ (resAbs K S₀ σ) s = s := by
    apply Subtype.ext
    change ((resAbs K S₀ σ) s : AlgebraicClosure K) = s
    rw [resAbs_apply_coe]
    change ((resAbs K S₁ σ) ⟨s, hs1⟩ : AlgebraicClosure K) = s at e1
    rwa [resAbs_apply_coe] at e1
  simp [quadChar, e0]

include hs in
/-- **`ThetaOfDelta f` from genus theory and the moving character** (PROVED): the quadratic part
from `quadOfDelta_of_genus` (`h = ∏_{q ∈ Qs} q*`, `q ∣ f`), the moving part from lane E1's
factorisation clause at the moving conductor `r ∣ f` (`piOfDelta_of_moving`). This is the
condition `hα` of the actual Heegner points (`hα_of_theta`) with no remaining hypothesis on the
character. -/
theorem thetaOfDelta_of_genus {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, q.Prime ∧ q ≠ 2) (f : ℕ) [NeZero f]
    (hf : ∀ q ∈ Qs, q ∣ f) (hh : h = ((∏ q ∈ Qs, qstar q : ℤ) : K))
    (hSf : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S₁)
    {r : ℕ} [NeZero r] (hrf : r ∣ f)
    (hclause : ∀ [NeZero r] {S' S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS' : S₀ ⊆ S')
      (h1 : S₁ ⊆ S'),
      (∀ v : HeightOneSpectrum (𝓞 K), ((r : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) →
      ∀ g : GKS K S', (∀ z : KS K S₁,
          (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K r)) →
          galS K S₁ (inflMap K h1 g) z = z) →
        π (inflMap K hS' g) = 1) :
    ThetaOfDelta hS h1 s hs hs0 π f :=
  thetaOfDelta_of hS h1 s hs hs0 π f
    (quadOfDelta_of_genus hS h1 s hs hs0 hK2 hTC Qs hQs f hf hh hSf)
    (piOfDelta_of_moving hS h1 π hrf
      (fun v hv => hSf v (by obtain ⟨c, rfl⟩ := hrf; push_cast; exact v.asIdeal.mul_mem_right _ hv))
      hclause)

/-- The two normalizations of `q*` agree at odd `q` (PROVED). -/
theorem qstar_eq_rc {q : ℕ} (hq : q % 2 = 1) : qstar q = ZInQ.Manuscript.RC.qstar q := by
  unfold qstar ZInQ.Manuscript.RC.qstar
  rw [show (q - 1) / 2 = q / 2 by omega]

/-- **The address's `h_x` as a product of `q*`** (PROVED): `h_x = ∏_{q ∈ Q, λ_q(x) = 1} q*` for a
family of odd primes. -/
theorem family_h_eq_prod (F : ZInQ.Manuscript.RC.Family) (x : ZInQ.Manuscript.RC.Addr F.b)
    (hodd : ∀ q ∈ F.Q, q % 2 = 1) :
    F.h x = ∏ q ∈ F.Q.filter (fun q => F.lam q x = 1), qstar q := by
  classical
  unfold ZInQ.Manuscript.RC.Family.h
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [qstar_eq_rc (hodd q hq)]
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (F.lam q x) with h | h
  · rw [h]; simp
  · rw [h]
    simp only [↓reduceIte]
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

include hs in
/-- **`QuadOfDelta f` for the address's character `χ_{h_x}`** (PROVED): for an admissible family
(odd primes) and `f` divisible by the primes `q` with `λ_q(x) = 1`. -/
theorem quadOfDelta_family (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (F : ZInQ.Manuscript.RC.Family) (x : ZInQ.Manuscript.RC.Addr F.b)
    (hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) (hh : h = ((F.h x : ℤ) : K)) (f : ℕ) [NeZero f]
    (hf : ∀ q ∈ F.Q, F.lam q x = 1 → q ∣ f)
    (hSf : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S₁) :
    QuadOfDelta hS h1 s hs hs0 f := by
  classical
  have hodd : ∀ q ∈ F.Q, q % 2 = 1 := fun q hq =>
    Nat.odd_iff.mp ((hQ q hq).1.odd_of_ne_two (hQ q hq).2)
  refine quadOfDelta_of_genus hS h1 s hs hs0 hK2 hTC (F.Q.filter fun q => F.lam q x = 1)
    (fun q hq => hQ q (Finset.mem_of_mem_filter q hq)) f
    (fun q hq => hf q (Finset.mem_of_mem_filter q hq) (Finset.mem_filter.1 hq).2) ?_ hSf
  rw [hh, family_h_eq_prod F x hodd]

end ZInQ.Contrib.CloudB3E2.NormCochain

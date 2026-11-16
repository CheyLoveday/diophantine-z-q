import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.TYZChain.Thm35
import ZInQKernel.Contrib.TYZGenus.RingClass

/-!
# TYZ Lemma 2.9 (`hL29`) from TYZ Theorem 2.1 for every pair and TYZ Lemma 2.8, through genus theory

Task h29-proof (2026-11-16); report `docs/research/h29-proof.md`, log and computations in
`scratch/h29-proof/`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Asian J. Math. 21 (2017). The source `Period7.tex` was **not on the host** for this task: every line number
`Lnnnn` below is quoted from the project notes that read it (`h29-split.md`, `h29-fix.md`, `h29-ne3.md`,
`rv-tyz-inputs.md`), not re-read here.

**What this file proves.** The top hypothesis `hL29 = H29Split.TYZLemma29PrintedNe3` (TYZ Lemma 2.9 as
printed, squarefree `1 < n ≡ 1, 3 (mod 8)`, `n ≠ 3`) follows from two printed statements of TYZ §2
(`tyzLemma29PrintedNe3_of_genus`):

* `TYZThm21Pairs`: TYZ Theorem 2.1 (L554–559) for every decomposition `n = d₁d₂`: the quadratic period
  `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552) vanishes if neither `d₁` nor `d₂` is `≡ 1 (mod 8)`,
  and equals `±2^{k−1} w_K 𝓛(d₁)𝓛(d₂)` if `d₂ ≡ 1 (mod 8)` (`k` the number of primes of `n`, `a = 1`);
* `TYZLemma28Sym`: TYZ Lemma 2.8 (L1009–1057), `P(d₁, d₂) = P(d₂, d₁)` for `n ≡ 1 (mod 8)`.

The glue is TYZ's own proof of Lemma 2.9 (L1068–1077 with (PQ), L1001): the genus characters `χ_T`,
`T ⊆ {primes of n}`, satisfy `Σ_T χ_T(t) = 2^k [t ∈ Cl²]` (Gauss's principal genus theorem, proved in the
project: `RouteK.Redei.range_sq_eq_ker_chi`), so `Σ_{d₂ ∣ n} P(n/d₂, d₂) = 2^k Q(n)`; for `n ≡ 3 (mod 8)`,
`χ_T = χ_{T^c}` (the product formula, `TYZ35.prod_sgn_chi_eq_one`) pairs `d₂ ≡ 3` with `d₁ ≡ 1`; for
`n ≡ 1 (mod 8)` Lemma 2.8 pairs `(d₁, d₂)` with `(d₂, d₁)`; and `w_K = #μ(K)/2 = 1` for `n ≠ 3`
(`torsionOrder_qNeg_eq_two`).

The same two leaves give the `w_K` form `TYZLemma29Printed` for every `n` including `3`
(`tyzLemma29Printed_of_genus`) and the instance `TYZThm21At31` (`tyzThm21At31_of_thm21Pairs`), and so
`h29 = TYZLemma29Mod2` from five leaves (`tyzLemma29Mod2_of_genusLeaves`).

**Rating (fallback).** This replaces one printed leaf (`hL29`) by two printed leaves; it does not lower the
count. It is the reduction of TYZ Lemma 2.9 to the theorem TYZ derive it from (Theorem 2.1, itself from the
explicit Waldspurger formula, TYZ Theorem 4.2) plus Lemma 2.8. An outright proof of `hL29` needs the explicit
Waldspurger formula, which is not in Lean (see the report).

**`χ_{d₁,d₂}`.** The leaves use the project's genus characters
`TYZ35.gchar n T = Π_{q ∈ T} χ_q`, `χ_q([𝔞]) = (N𝔞/q)` (`RouteK.Redei.chi`), with `T` the primes of `d₂`
(`TYZ35.divSet n d₂`). By Jacobi reciprocity `χ_T` is the character of `K_n(√d₂*)/K_n`,
`d* = (−1)^{(d−1)/2} d` (STANDARD); TYZ's convention `χ_{n,1} = 1` (L510) and `χ_{d₁,d₂} = χ_{d₂,d₁}χ₀`
(`n ≡ 1`), `χ_{d₁,d₂} = χ_{d₂,d₁}` (`n ≡ 3`) (L994–995, as read in `rv-tyz-inputs.md` §1.2) fit this. The two
leaves are insensitive to the choice between `χ_{T(d₂)}` and `χ_{T(d₁)}`: for `n ≡ 3` the two agree, and for
`n ≡ 1` Lemma 2.8 makes `P` symmetric; both conditions in `TYZThm21Pairs` are then symmetric too.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Genus

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b NumberField
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet sgn2 sgnHom sum_finset_eq_sum_divisors divSet_div
  prod_sgn_chi_eq_one)
open scoped Quaternion

/-! ## §1. TYZ's quadratic periods and the two leaves -/

/-- **TYZ's quadratic period** `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)` (L551–552), for the embedding
`τ` and the test vector `f`, indexed by `d₂` (`d₁ = n/d₂`): `χ_{d₁,d₂} = χ_T`, `T` the primes of `d₂`
(`TYZ35.divSet n d₂`), `χ_T = Π_{q ∈ T} χ_q` the genus character (`TYZ35.gchar`; `χ_∅ = 1`). The class
`t` is read in `B̂^×` as `τ̂` of a finite idele in the class (`clLift`; any idele in the class gives the same
value, `H29Split.tv_eq_of_toClassGroup_eq`). -/
def quadPeriod (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (d₂ : ℕ) : ℤ :=
  ∑ t : ClassGroup (𝓞 (QNeg n)),
    gchar n (divSet n d₂) t * f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ])

/-- **TYZ Theorem 2.1 (L554–559) for every decomposition, odd classes.** For squarefree `1 < n ≡ 1, 3 (mod 8)`,
every admissible `τ` (L527–534), every test vector `f_n` (L550), every sign choice `ℓ` of `𝓛` (TYZ L336–353;
`ℓ(m)² = 𝓛(m)²`, `IsLcalSign`) and every `n = d₁d₂`:

* if neither `d₁` nor `d₂` is `≡ 1 (mod 8)`, then `P(d₁, d₂) = 0`;
* if `d₂ ≡ 1 (mod 8)`, then `P(d₁, d₂) = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)` with `k` the number of prime factors of
  `n`, `a = 1` (`n` odd) and `2w_K` the number of roots of unity of `K_n` (L557–558; Mathlib's
  `NumberField.Units.torsionOrder`).

Against the print. The print's first assertion is "`P(d₁, d₂) ≠ 0` only if `d₂ ≡ 1 (mod 8)`"; read for
ordered pairs it is false at `n ≡ 3 (mod 8)`, `(d₁, d₂) ≡ (1, 3)` (`P(d₁, d₂) = P(d₂, d₁)`; h29-split §2,
rv-tyz-inputs §1.2 item 4). The leaf states only its consequence for pairs with **no** factor `≡ 1`, which is
what every reading gives and what TYZ's proof of Lemma 2.9 uses. The second clause is the displayed formula with
the factor `w_K` (the h29-fix computation shows Theorem 2.1, not Lemma 2.9, is right at `n = 3`). Restrictions,
each a weakening: odd classes only (TYZ: `n ≡ 1, 2, 3`), `n > 1`. At `n = 3` it contains `TYZThm21At31`
(`tyzThm21At31_of_thm21Pairs`), proved outright by task t21-proof. Checked numerically
(`scratch/h29-proof/genus_check.py`): 14 values of `n` up to 219, 2 embeddings each, every `T`: vanishing and
`P² = 4^{k−1} w_K² 𝓛(d₁)²𝓛(d₂)²` hold. -/
def TYZThm21Pairs : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℤ, IsLcalSign ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          quadPeriod n τ f d₂ = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℤ) * (ℓ d₁ * ℓ d₂))

/-- **TYZ Lemma 2.8 (L1009–1057; label `lem2.6`), the symmetry `P(d₁, d₂) = P(d₂, d₁)`**, for squarefree
`1 < n ≡ 1 (mod 8)`, every admissible `τ` (with TYZ's choice `4 ∣ c`, L533, which the proof uses, included in
`AdmissibleTau`) and every test vector `f_n`; stated for the decompositions with `d₂ ≡ 1 (mod 8)` (then also
`d₁ ≡ 1`), the only ones TYZ's proof of Lemma 2.9 uses (a weakening). Here `χ_{d₂,d₁} = χ_{d₁,d₂}χ₀`, so the
lemma is not a formal symmetry. TYZ's proof (as checked in rv-tyz-inputs §1.2 item 3): conjugation by
`g₀ = ai + bj + (c + √n)k`. Checked numerically (`genus_check.py`, the 16 runs with `n ≡ 1 (mod 8)`, every
`T`). -/
def TYZLemma28Sym : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → n % 8 = 1 →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ d₁ d₂ : ℕ, d₁ * d₂ = n → d₂ % 8 = 1 → quadPeriod n τ f d₂ = quadPeriod n τ f d₁

/-! ## §2. Genus theory: the character sum (PQ) -/

section Glue

variable {n : ℕ} [NeZero n]

open Classical in
/-- `Σ_T χ_T(c) = 2^k` if `c ∈ Cl²`, else `0` (Gauss: `Cl² = ⋂_q ker χ_q`, `RouteK.Redei.range_sq_eq_ker_chi`). -/
theorem sum_gchar_cl (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (c : ClassGroup (𝓞 (QNeg n))) :
    ∑ T : Finset n.primeFactors, gchar n T c =
      if c ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range then
        2 ^ n.primeFactors.card else 0 := by
  classical
  have e1 : ∑ T : Finset n.primeFactors, gchar n T c =
      ∏ q : n.primeFactors, (sgn2 (chi n q c) + 1) := by
    rw [Finset.prod_add_one, Finset.powerset_univ]; rfl
  rw [e1]
  have hiff : c ∈ (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range ↔
      ∀ q, chi n q c = 1 := by
    rw [range_sq_eq_ker_chi n hn hsq h1, Subgroup.mem_iInf]
    exact forall_congr' fun q => MonoidHom.mem_ker
  split_ifs with hc
  · rw [hiff] at hc
    have : ∀ q : n.primeFactors, sgn2 (chi n q c) + 1 = 2 := fun q => by
      rw [hc q]; simp [sgn2]
    rw [Finset.prod_congr rfl (fun q _ => this q), Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
  · rw [hiff, not_forall] at hc
    obtain ⟨q, hq⟩ := hc
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [sgn2, hq]

/-- **(PQ)** (TYZ L1001): `Σ_{d₂ ∣ n} P(n/d₂, d₂) = 2^k Q(n)`. -/
theorem sum_quadPeriod (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (f : ℍ[AQ] → ℤ) :
    ∑ e ∈ n.divisors, quadPeriod n τ f e = 2 ^ n.primeFactors.card * genusPeriodTV n τ f := by
  classical
  have h := sum_finset_eq_sum_divisors (n := n) hsq (fun T => ∑ t : ClassGroup (𝓞 (QNeg n)),
    gchar n T t * f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ]))
  simp only [quadPeriod]
  rw [← h, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_gchar_cl hn hsq h1, ite_mul, zero_mul]
  rw [← Finset.sum_filter, genusPeriodTV, Finset.mul_sum, sqClasses]

/-- For `n ≡ 3 (mod 4)`, `P(d₁, d₂) = P(d₂, d₁)`: `χ_T = χ_{T^c}` (product formula). -/
theorem quadPeriod_div (h4 : n % 4 = 3) (hsq : Squarefree n) (h1 : 1 < n) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (f : ℍ[AQ] → ℤ) {e : ℕ} (he : e ∣ n) : quadPeriod n τ f (n / e) = quadPeriod n τ f e := by
  classical
  unfold quadPeriod
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hp := prod_sgn_chi_eq_one h4 hsq h1 c
  rw [← Finset.prod_mul_prod_compl (divSet n e)] at hp
  rw [divSet_div hsq he]
  unfold gchar
  change ∏ q ∈ (divSet n e)ᶜ, sgnHom (chi n q c) = ∏ q ∈ divSet n e, sgnHom (chi n q c)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hp with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
    rw [h1', h2']

end Glue

end ZInQ.Contrib.TYZDecomp.H29Genus

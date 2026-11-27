import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.LocalCounts
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalConditions
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Places
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsFull

/-!
# Genuine instantiations, part 6: RC6's `hL` — the sum over places and the condition dimensions

Manuscript `diophantine_zq.tex`, tex 4544–4577 (the local terms of the Selmer cone: per place the
condition dimension `∑ hᵃ(U_w)` and `∑ hᵃ(K_w, W)`, summed over the places above the charged
primes) and 4593–4597.

* `genLocDim w = ∑_{a ≤ 2} dim Hᵃ(C^•_cont(G_{K_w}, W))` from the genuine local complex, equal to
  RC6's `hLoc` sum (`genLocDim_eq`); `finrank_genLocH_forms`: the forms `𝔽₂ × 𝔽₂` (global counts)
  and `Fin 2 → 𝔽₂` (RC6's place entries) of `W` give the same dimensions;
* `genCondDim`: the condition dimensions from genuine objects — the unramified condition is the
  complex `urCx K w W = [W --(Φ−1)--> W]` (the other team's genuine unramified local condition via
  `urToLocal_galois`), the zero condition `0`, the full condition the genuine local complex; the
  derivative and old-Kummer conditions are the **named input** `dD`. `genCondDim_eq`,
  `genCondDimFun_eq`: they are RC6's `condDimAt` / `condDimFun` (for the named rows, given `hD`);
* `cost_placeEntry`, `sum_cost_placesList`, `sum_cost_placesList'`: RC6's `placesList` costs as sums
  over the genuine places above `p`;
* **`hL_of_genuineModel`**: RC6's `hL` from a residual model of the genuine local complexes and
  conditions (total ranks of `U`, `L` bounded by the genuine dimensions over the places above the
  charged primes).

**Classification.** PROVED (the derivative/old-Kummer condition dimensions are a named input).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `W = 𝔽₂²` in RC6's form `Fin 2 → 𝔽₂`. -/
abbrev W2v : Type := Fin 2 → ZMod 2

/-- **The local-complex dimensions of a place from the genuine local complex**:
`∑_{a ≤ 2} dim Hᵃ(C^•_cont(G_{K_w}, W))`. -/
def genLocDim (w : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ∑ a ∈ Finset.range 3, Module.finrank (ZMod 2) (genLocH K S (W2v) w a)

/-- The genuine local dimensions are RC6's. PROVED. -/
theorem genLocDim_eq (w : HeightOneSpectrum (𝓞 K)) :
    genLocDim K S w = hLoc K w 0 + hLoc K w 1 + hLoc K w 2 := by
  simp only [genLocDim, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [finrank_genLocH K S W2v w 0 (by omega), finrank_genLocH K S W2v w 1 (by omega),
    finrank_genLocH K S W2v w 2 (by omega)]

/-- **The residual dimension of a local condition from genuine objects** (tex 4551–4573):
the unramified condition is the complex `urCx K w W = [W --(Φ−1)--> W]` (the other team's genuine
unramified local condition via `urToLocal_galois`), with `∑ dim Hⁿ`; the zero condition is `0`; the
full condition is the genuine local complex `C^•_cont(G_{K_w}, W)` itself; the derivative and old
Kummer conditions are the named input `dD`. -/
def genCondDim (w : HeightOneSpectrum (𝓞 K)) (c : LocalCondition) (dD : ℕ) : ℕ :=
  match c with
  | .unramified => Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 0) +
      Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 1)
  | .zero => 0
  | .full => genLocDim K S w
  | _ => dD

/-- **The genuine condition dimensions are RC6's** (`condDimAt`) for the unramified, zero and full
conditions; for the derivative and old-Kummer conditions this is the named input. PROVED. -/
theorem genCondDim_eq (w : HeightOneSpectrum (𝓞 K)) (c : LocalCondition) (dD : ℕ)
    (hD : c ≠ .unramified → c ≠ .zero → c ≠ .full → dD = condDimAt K w c dD) :
    genCondDim K S w c dD = condDimAt K w c dD := by
  cases c with
  | unramified =>
    simp only [genCondDim, condDimAt]
    rw [finrank_urCx_W2, hUr_zero, hUr_one]
  | zero => rfl
  | full => exact genLocDim_eq K S w
  | oldKummer => exact hD (by decide) (by decide) (by decide)
  | derivStrict => exact hD (by decide) (by decide) (by decide)
  | derivFiniteOrSingular => exact hD (by decide) (by decide) (by decide)
  | derivRelaxed => exact hD (by decide) (by decide) (by decide)

/-- `𝔽₂ × 𝔽₂ ≃ (Fin 2 → 𝔽₂)`, the two forms of `W`. -/
def wForms : (ZMod 2 × ZMod 2) ≃+ W2v := (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm.toAddEquiv

/-- **The two forms of `W` give the same genuine local dimensions** (`𝔽₂ × 𝔽₂` of the global
counts ↔ `Fin 2 → 𝔽₂` of RC6's place entries), in degrees `≤ 2`. PROVED. -/
theorem finrank_genLocH_forms (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≤ 2) :
    Module.finrank (ZMod 2) (genLocH K S (ZMod 2 × ZMod 2) w n) =
      Module.finrank (ZMod 2) (genLocH K S W2v w n) := by
  have := locallyCompactSpace_Gloc K w
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
  · refine (toLin (((contH0AddEquiv (ZMod 2) (Gloc K w)
      (locMod K S (ZMod 2 × ZMod 2) w)).trans ?_).trans
      (contH0AddEquiv (ZMod 2) (Gloc K w) (locMod K S W2v w)).symm)).finrank_eq
    exact { toFun := fun x => ⟨wForms x.1, fun _ => rfl⟩
            invFun := fun x => ⟨wForms.symm x.1, fun _ => rfl⟩
            left_inv := fun x => Subtype.ext (wForms.symm_apply_apply x.1)
            right_inv := fun x => Subtype.ext (wForms.apply_symm_apply x.1)
            map_add' := fun x y => Subtype.ext (map_add wForms x.1 y.1) }
  · exact (toLin (((contH1AddEquiv (ZMod 2) (Gloc K w)
      (locMod K S (ZMod 2 × ZMod 2) w)).trans
      (TauCeti.ContCohomology.explicitMap1Equiv (Gloc K w) (locMod K S (ZMod 2 × ZMod 2) w)
        (Gloc K w) (locMod K S W2v w) (ContinuousMulEquiv.refl _) wForms
        continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl))).trans
      (contH1AddEquiv (ZMod 2) (Gloc K w) (locMod K S W2v w)).symm)).finrank_eq
  · exact (toLin (((contH2AddEquiv (ZMod 2) (Gloc K w)
      (locMod K S (ZMod 2 × ZMod 2) w)).trans
      (TauCeti.ContCohomology.explicitMap2Equiv (Gloc K w) (locMod K S (ZMod 2 × ZMod 2) w)
        (Gloc K w) (locMod K S W2v w) (ContinuousMulEquiv.refl _) wForms
        continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl))).trans
      (contH2AddEquiv (ZMod 2) (Gloc K w) (locMod K S W2v w)).symm)).finrank_eq

open Classical in
/-- The genuine condition dimension as a function of the prime ideal (junk `0` off primes). -/
def genCondDimFun (cond : Ideal (𝓞 K) → LocalCondition) (dD : Ideal (𝓞 K) → ℕ)
    (P : Ideal (𝓞 K)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then genCondDim K S ⟨P, h.1, h.2⟩ (cond P) (dD P) else 0

/-- **The genuine condition dimensions are RC6's `condDimFun`**, given the named input for the
derivative and old-Kummer conditions. PROVED. -/
theorem genCondDimFun_eq (cond : Ideal (𝓞 K) → LocalCondition) (dD : Ideal (𝓞 K) → ℕ)
    (hD : ∀ (P : Ideal (𝓞 K)) (h : P.IsPrime ∧ P ≠ ⊥), cond P ≠ .unramified → cond P ≠ .zero →
      cond P ≠ .full → dD P = condDimAt K ⟨P, h.1, h.2⟩ (cond P) (dD P)) :
    genCondDimFun K S cond dD = condDimFun K cond dD := by
  funext P
  simp only [genCondDimFun, condDimFun]
  split_ifs with h
  · exact genCondDim_eq K S _ _ _ (hD P h)
  · rfl

/-- The cost of a place entry: the condition dimension plus the genuine local dimensions. -/
theorem cost_placeEntry (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p)
    (c : LocalCondition) (cd : ℕ) :
    (placeEntry K p P hP c cd).cost = cd + genLocDim K S (placeOf K p.2.ne_zero P hP) := by
  rw [genLocDim_eq]
  rfl

/-- **The sum over the places above `p`** (RC6's `placesList` ↔ the genuine places): the total
cost is `∑_{w ∣ p} (condDim w + ∑_{a ≤ 2} dim Hᵃ(C^•_cont(G_{K_w}, W)))`. PROVED. -/
theorem sum_cost_placesList (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    {p : ℕ} (hp : p.Prime) :
    ((placesList K cond condDim p).map PlaceData.cost).sum =
      ∑ P ∈ (primesAbove_finite (K := K) p).toFinset.attach,
        (condDim P.1 + genLocDim K S (placeOf K hp.ne_zero P.1
          ((primesAbove_finite (K := K) p).mem_toFinset.mp P.2))) := by
  rw [placesList, dif_pos hp, List.map_map]
  refine (Finset.sum_map_toList _ _).trans (Finset.sum_congr rfl fun P _ => ?_)
  exact cost_placeEntry K S ⟨p, hp⟩ P.1 _ (cond P.1) (condDim P.1)

/-- The genuine local dimensions summed over the places above `p`. -/
def genLocSum (p : ℕ) : ℕ :=
  if hp : p.Prime then
    ∑ P ∈ (primesAbove_finite (K := K) p).toFinset.attach,
      genLocDim K S (placeOf K hp.ne_zero P.1 ((primesAbove_finite (K := K) p).mem_toFinset.mp P.2))
  else 0

/-- A condition-dimension function summed over the places above `p`. -/
def condSum (condDim : Ideal (𝓞 K) → ℕ) (p : ℕ) : ℕ :=
  ∑ P ∈ (primesAbove_finite (K := K) p).toFinset, condDim P

/-- The `placesList` costs above a prime, split into conditions and local terms. PROVED. -/
theorem sum_cost_placesList' (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    {p : ℕ} (hp : p.Prime) :
    ((placesList K cond condDim p).map PlaceData.cost).sum =
      condSum K condDim p + genLocSum K S p := by
  rw [sum_cost_placesList K S cond condDim hp, Finset.sum_add_distrib, genLocSum, dif_pos hp,
    condSum, Finset.sum_attach]

/-- **RC6's `hL` from a residual model of the genuine local complexes and conditions** (tex
4544–4573, 4593–4597): if the condition part `U` of the Selmer-cone model has total rank at most
the genuine condition dimensions (`genCondDimFun`: the unramified condition `[W --(Φ−1)--> W]`, the
zero condition, the full condition `C^•_cont(G_{K_w}, W)`; the derivative and old-Kummer ones the
named input `dD`) and the local part `L` total rank at most the genuine local dimensions
`∑_{a ≤ 2} dim Hᵃ(C^•_cont(G_{K_w}, W))`, both summed over the places above the charged primes,
then `hL` holds with RC6's genuine `condDimFun`. PROVED. -/
theorem hL_of_genuineModel {N r : ℕ} {Dp : Finset ℕ} (hr : r.Prime) (hDp : ∀ p ∈ Dp, p.Prime)
    (cond : Ideal (𝓞 K) → LocalCondition) (dD : Ideal (𝓞 K) → ℕ)
    (hD : ∀ (P : Ideal (𝓞 K)) (h : P.IsPrime ∧ P ≠ ⊥), cond P ≠ .unramified → cond P ≠ .zero →
      cond P ≠ .full → dD P = condDimAt K ⟨P, h.1, h.2⟩ (cond P) (dD P))
    (Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2)) (s : Finset ℤ)
    (archTot : ℕ)
    (hUm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun K S cond dD) p)
    (hLm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p) :
    ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) +
        ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r Dp, ((placesList K cond (condDimFun K cond dD) p).map
        PlaceData.cost).sum + archTot := by
  have h : ∑ p ∈ chargedPrimes N r Dp, ((placesList K cond (condDimFun K cond dD) p).map
      PlaceData.cost).sum = ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun K S cond dD) p +
      ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [sum_cost_placesList' K S cond _ (prime_of_mem_chargedPrimes hr hDp p hp),
      genCondDimFun_eq K S cond dD hD]
  rw [h]
  omega

end ZInQ.Contrib.CloudB3RC53.GenuineInst

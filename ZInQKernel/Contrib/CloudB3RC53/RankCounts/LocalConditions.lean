import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalCounts
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.GlobalH1
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.ZHat
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# RankCounts: Elliot's table of local-condition dimensions (`hcond`) from genuine cohomology

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4551–4573. The input `hcond`
of `residualRankCounts_full` / `residualRankCounts_genus` says that each place's condition
dimension `Σ_a h^a(U_w)` is Elliot's table value. Here the condition dimensions are computed from
genuine cohomology of the completion `K_w` (`condDimAt`, `condDimFun`):

* unramified: `h⁰ + h¹` of `Gal(K_w^{ur}/K_w)` — Elliot's `[W --(Φ−1)--> W]`; `= 2 + 2` because
  `Gal(K_w^{ur}/K_w) ≃ ℤ̂` (Tau Ceti) and `H¹(ℤ̂, V) = Hom_cont(ℤ̂, V) ≅ V` for trivial finite `V`
  (`finrank_H1_trivial_of_zHat`);
* zero `0`; full `h⁰ + h¹ + h²` of `G_{K_w}` (`= 8 + 2d_w`, PRINT leaves Milne ADT I.2.3/I.2.8);
* derivative strict `h⁰ = 2`; derivative finite or singular `h⁰ + dim H¹_ur = 4`; derivative
  relaxed `h⁰ + h¹ = 6` at odd places;
* old Kummer: the derived Kummer image of `E^{(h)}(K_w)` is not available in Lean (the structure
  `E^{(h)}(K_w)^∧_2 ≅ ℤ₂^{d_w} ⊕ (torsion with two generators)`, tex 4552–4555); its dimension is the
  input `kummerDim` with hypothesis `kummerDim = 4 + d_w`.

`hcond_genuine` proves `hcond` (for every rational prime) for `condDim := condDimFun cond kummerDim`.
DEPARTURE (in form): the finite and singular derivative planes have the same dimension; the singular
row is computed through the finite plane `F = H¹_ur` (`dim S = h¹ − dim F = 2` as well).
Kinds: PROVED from the PRINT leaves and the named inputs.
-/

open NumberField IsDedekindDomain CategoryTheory
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.RankCounts

/-- A continuous multiplicative equivalence as a continuous homomorphism. -/
def cmhOf {G H : Type} [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) : G →ₜ* H := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩

@[simp] theorem cmhOf_apply {G H : Type} [Monoid G] [Monoid H] [TopologicalSpace G]
    [TopologicalSpace H] (e : G ≃ₜ* H) (x : G) : cmhOf e x = e x := rfl

/-- Continuous homomorphisms from a copy of `ℤ̂` to a profinite group `P` are its elements. -/
def homZHatEquiv {G : Type} [Group G] [TopologicalSpace G] (e : G ≃ₜ* TauCeti.zHat.{0})
    (P : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [TotallyDisconnectedSpace P] :
    (G →ₜ* P) ≃ P where
  toFun φ := φ (e.symm TauCeti.zHat.gen)
  invFun a := (TauCeti.zHat.lift a).comp (cmhOf e)
  left_inv φ := by
    ext g
    have := TauCeti.zHat.lift_unique (φ (e.symm TauCeti.zHat.gen))
      (φ.comp (cmhOf e.symm)) rfl
    have h2 := congrArg (fun ψ : TauCeti.zHat.{0} →ₜ* P => ψ (e g)) this
    simp only [ContinuousMonoidHom.comp_toFun] at h2
    simpa using h2.symm
  right_inv a := by simp

theorem finrank_H1_trivial_of_zHat {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G ≃ₜ* TauCeti.zHat.{0}) (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul (ZMod 2) V]
    [DiscreteTopology V] [Finite V] :
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS G V)) =
      Module.finrank (ZMod 2) V := by
  have hc : Nat.card (continuousCohomology 1 (trivialRepS G V)) = Nat.card V := by
    rw [Nat.card_congr (h1triv G V).toEquiv]
    exact Nat.card_congr (homZHatEquiv e (Multiplicative V))
  have : Finite (continuousCohomology 1 (trivialRepS G V)) := Nat.finite_of_card_ne_zero (by
    rw [hc]; exact Nat.card_pos.ne')
  have hV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have hH := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := continuousCohomology 1 (trivialRepS G V))
  rw [hc, hV, Nat.card_zmod] at hH
  exact (Nat.pow_right_injective le_rfl hH).symm

open ZInQ.Manuscript.RC.Limits

variable (K : Type) [Field K] [NumberField K]

/-- `Gal(K_w^{ur}/K_w)` for the completion `K_w` (a nonarchimedean local field). -/
abbrev GUr (w : HeightOneSpectrum (𝓞 K)) : Type :=
  Gal(TauCeti.maximalUnramifiedExtension (w.adicCompletion K)
    (AlgebraicClosure (w.adicCompletion K)) / (w.adicCompletion K))

/-- `h^i(K_w, W)`, `W = 𝔽₂²` trivial. -/
abbrev hLoc (w : HeightOneSpectrum (𝓞 K)) (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (continuousCohomology i (trivialGaloisRep (w.adicCompletion K) (Fin 2 → ZMod 2)))

/-- `h^i(Gal(K_w^{ur}/K_w), W)`: the unramified cohomology, Elliot's `[W --(Φ−1)--> W]`. -/
abbrev hUr (w : HeightOneSpectrum (𝓞 K)) (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (continuousCohomology i (trivialRepS (GUr K w) (Fin 2 → ZMod 2)))

/-- **The residual dimension `Σ_a h^a(U_w)` of the local condition `U_w`** (tex 4551–4573), from
the genuine local and unramified cohomology of `K_w`: unramified `h⁰_ur + h¹_ur`; zero `0`; full
`h⁰ + h¹ + h²`; derivative strict `D⁰ = h⁰`; derivative finite (or singular) `h⁰ + dim F` with
`F = H¹_ur` the finite plane; derivative relaxed `h⁰ + dim (F ⊕ S) = h⁰ + h¹`. The old Kummer
condition (the derived Kummer image of `E^{(h)}(K_w)`) is not available and is the input
`kummerDim`. -/
def condDimAt (w : HeightOneSpectrum (𝓞 K)) (c : LocalCondition) (kummerDim : ℕ) : ℕ :=
  match c with
  | .oldKummer => kummerDim
  | .unramified => hUr K w 0 + hUr K w 1
  | .zero => 0
  | .full => hLoc K w 0 + hLoc K w 1 + hLoc K w 2
  | .derivStrict => hLoc K w 0
  | .derivFiniteOrSingular => hLoc K w 0 + hUr K w 1
  | .derivRelaxed => hLoc K w 0 + hLoc K w 1

theorem hUr_zero (w : HeightOneSpectrum (𝓞 K)) : hUr K w 0 = 2 := by
  rw [hUr, finrank_H0_trivialRepS]; simp

theorem hUr_one (w : HeightOneSpectrum (𝓞 K)) : hUr K w 1 = 2 := by
  rw [hUr, finrank_H1_trivial_of_zHat
    (TauCeti.maximalUnramifiedGaloisGroupEquivZHat (w.adicCompletion K)
      (AlgebraicClosure (w.adicCompletion K)))]
  simp

theorem hLoc_zero (w : HeightOneSpectrum (𝓞 K)) : hLoc K w 0 = 2 := by
  rw [hLoc, finrank_H0_trivialGaloisRep]; simp


open Classical in
/-- The genuine condition dimension as a function of the prime ideal (junk `0` off primes). -/
def condDimFun (cond : Ideal (𝓞 K) → LocalCondition) (kummerDim : Ideal (𝓞 K) → ℕ)
    (P : Ideal (𝓞 K)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then condDimAt K ⟨P, h.1, h.2⟩ (cond P) (kummerDim P) else 0

/-- **Elliot's table (tex 4561–4573) for the genuine conditions at one place.** PROVED (the full and
relaxed rows from the PRINT leaves Milne ADT I.2.3/I.2.8; the unramified, finite and singular rows
from `Gal(K_w^{ur}/K_w) ≅ ℤ̂`; the old Kummer row is the input `hkum`). -/
theorem placeEntry_condDim_table (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p) (c : LocalCondition)
    (kd : ℕ) (hrel : c = .derivRelaxed → (p : ℕ) ≠ 2)
    (hkum : c = .oldKummer → kd = 4 + (placeEntry K p P hP c 0).deg) :
    (placeEntry K p P hP c (condDimAt K (placeOf K p.2.ne_zero P hP) c kd)).condDim =
      c.dim (placeEntry K p P hP c (condDimAt K (placeOf K p.2.ne_zero P hP) c kd)).deg := by
  have := placeOf_liesOver K p P hP
  let _ := qpAlg K p (placeOf K p.2.ne_zero P hP)
  have := qp_finiteDimensional K p P hP
  obtain ⟨h0, h1, h2⟩ := local_cohomology_dims h28 h23 p ((placeOf K p.2.ne_zero P hP).adicCompletion K)
  cases c with
  | oldKummer => simpa [placeEntry, condDimAt, LocalCondition.dim] using hkum rfl
  | unramified => simp [placeEntry, condDimAt, LocalCondition.dim, hUr_zero, hUr_one]
  | zero => simp [placeEntry, condDimAt, LocalCondition.dim]
  | full =>
    simp only [placeEntry, condDimAt, LocalCondition.dim]
    rw [show hLoc K (placeOf K p.2.ne_zero P hP) 0 = 2 from h0,
      show hLoc K (placeOf K p.2.ne_zero P hP) 1 = _ from h1,
      show hLoc K (placeOf K p.2.ne_zero P hP) 2 = 2 from h2]
    omega
  | derivStrict => simp [placeEntry, condDimAt, LocalCondition.dim, hLoc_zero]
  | derivFiniteOrSingular =>
    simp [placeEntry, condDimAt, LocalCondition.dim, hLoc_zero, hUr_one]
  | derivRelaxed =>
    have hp2 := hrel rfl
    simp only [placeEntry, condDimAt, LocalCondition.dim]
    rw [show hLoc K (placeOf K p.2.ne_zero P hP) 0 = 2 from h0,
      show hLoc K (placeOf K p.2.ne_zero P hP) 1 = _ from h1]
    simp [hp2]


/-- **`hcond` for the genuine conditions** (tex 4551–4573): with `condDim := condDimFun cond
kummerDim`, every place over every rational prime satisfies Elliot's table value, given that the
relaxed derivative condition is used only at odd primes (derivative primes are odd and inert,
tex 4579–4580) and that at old Kummer places `kummerDim = 4 + d_w` (`hkum`: the residual dimensions
`(2, 2 + d_w)` of the derived Kummer condition, tex 4551–4556 — not available in Lean). PROVED. -/
theorem hcond_genuine (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (cond : Ideal (𝓞 K) → LocalCondition) (kummerDim : Ideal (𝓞 K) → ℕ)
    (hrel : ∀ (p : ℕ), p.Prime → ∀ P ∈ primesAbove K p, cond P = .derivRelaxed → p ≠ 2)
    (hkum : ∀ (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p),
      cond P = .oldKummer → kummerDim P = 4 + (placeEntry K ⟨p, hp⟩ P hP (cond P) 0).deg) :
    ∀ p : ℕ, ∀ w ∈ placesList K cond (condDimFun K cond kummerDim) p,
      w.condDim = w.cond.dim w.deg := by
  intro p w hw
  by_cases hp : p.Prime
  · obtain ⟨P, hP, rfl⟩ := mem_placesList K hp hw
    have hne : P.IsPrime ∧ P ≠ ⊥ := ⟨hP.1, ne_bot_of_mem_primesAbove K hp.ne_zero hP⟩
    have hfun : condDimFun K cond kummerDim P =
        condDimAt K (placeOf K (⟨p, hp⟩ : Nat.Primes).2.ne_zero P hP) (cond P) (kummerDim P) := by
      unfold condDimFun; rw [dite_eq_left_of_eq_true (eq_true hne)]; rfl
    rw [hfun]
    exact placeEntry_condDim_table K h28 h23 ⟨p, hp⟩ P hP (cond P) (kummerDim P)
      (hrel p hp P hP) (hkum p hp P hP)
  · simp [placesList, hp] at hw

end ZInQ.Contrib.CloudB3RC53.RankCounts

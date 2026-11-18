import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.LocalModel
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.ConeInverse

/-!
# RC53 PairedFunctional: the three-term local model as a Mathlib cochain complex

Manuscript `diophantine_zq.tex`, the local free model (4.4) at a tame split prime (tex L3470–3480)
and its contractions in the proof of Proposition `ex:arith-paired-functional` (tex L3727–3765,
L3842–3849).

`LocalModel.lean` states the model and its two contractions as explicit linear-map identities.
This file places the model in Mathlib's homological algebra, so that it can be fed to the cone
and biproduct results of `ConeInverse.lean`:

* `threeTermComplex d0 d1 hd`: for `S`-linear maps `d0 : M → N`, `d1 : N → M'` with
  `d1 ∘ d0 = 0`, the cochain complex `… → 0 → M → N → M' → 0 → …` in `CochainComplex
  (ModuleCat S) ℤ`, concentrated in degrees `0, 1, 2`, with `X 0 = M`, `X 1 = N`, `X 2 = M'`,
  `d 0 1 = d0`, `d 1 2 = d1` definitionally (`threeTermComplex_X_zero`, …, `_d_one_two`).
* `contractible_of_isContraction` (PROVED): an `IsContraction d0 d1 h1 h2` gives a homotopy
  `𝟙 ≃ 0` of the complex (Mathlib `Homotopy`).
* `contractible_of_homotopyEquiv` (PROVED): contractibility is invariant under homotopy
  equivalence.
* `tameComplex`: the model (4.4) itself, for `DC = CA`; `TameComplexContractible` (PROVED, tex
  L3731–3735, L3762–3765): it is contractible when `A, D` are units or when `C` is a unit.
* `TameCommutingCriterion` (PROVED, tex L3472–3476): if `Φ g = g Φ`, then `DC = CA` iff
  `k (g² − 1) = 0` for `q = 2k + 1`. (Consumer note: at the moving prime `g = 1 + t`, this is the
  moving-character lane's check that `((r−1)/2)((1+t)² − 1) = 0` in `A_i` when
  `r ≡ 1 mod 2^{i+1}`.)
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits

universe u

section Bridge

variable {S : Type u} [CommRing S]
variable {M N M' : Type u} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [AddCommGroup M'] [Module S M']

/-- The objects of the three-term complex: `M, N, M'` in degrees `0, 1, 2`, zero elsewhere. -/
def threeTermX (S : Type u) [CommRing S] (M N M' : Type u) [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] [AddCommGroup M'] [Module S M'] : ℤ → ModuleCat.{u} S
  | .ofNat 0 => ModuleCat.of S M
  | .ofNat 1 => ModuleCat.of S N
  | .ofNat 2 => ModuleCat.of S M'
  | _ => ModuleCat.of S PUnit

/-- The differentials of the three-term complex. -/
def threeTermD (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M') :
    ∀ i j : ℤ, threeTermX S M N M' i ⟶ threeTermX S M N M' j
  | .ofNat 0, .ofNat 1 => ModuleCat.ofHom d0
  | .ofNat 1, .ofNat 2 => ModuleCat.ofHom d1
  | _, _ => 0

/-- The objects outside degrees `0, 1, 2` are zero. -/
theorem threeTermX_subsingleton (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    Subsingleton (threeTermX S M N M' i) := by
  rcases i with (_ | _ | _ | n) | n
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact (inferInstance : Subsingleton PUnit)
  · exact (inferInstance : Subsingleton PUnit)

theorem threeTermD_eq_zero (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M') (i j : ℤ)
    (h : ¬ (i = 0 ∧ j = 1)) (h' : ¬ (i = 1 ∧ j = 2)) : threeTermD d0 d1 i j = 0 := by
  rcases i with (_ | _ | _ | n) | n <;> rcases j with (_ | _ | _ | m) | m <;>
    first | rfl | exact absurd ⟨rfl, rfl⟩ h | exact absurd ⟨rfl, rfl⟩ h'

/-- **The three-term complex** `M --d0--> N --d1--> M'` in degrees `0, 1, 2`. -/
def threeTermComplex (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M') (hd : d1 ∘ₗ d0 = 0) :
    CochainComplex (ModuleCat.{u} S) ℤ where
  X := threeTermX S M N M'
  d := threeTermD d0 d1
  shape i j hij := by
    apply threeTermD_eq_zero
    · rintro ⟨rfl, rfl⟩; exact hij rfl
    · rintro ⟨rfl, rfl⟩; exact hij rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    subst hij hjk
    by_cases h0 : i = 0
    · subst h0
      ext x
      exact LinearMap.congr_fun hd x
    by_cases h1 : i = 1
    · subst h1
      rw [threeTermD_eq_zero d0 d1 (1 + 1) (1 + 1 + 1) (by omega) (by omega)]
      exact comp_zero
    · rw [threeTermD_eq_zero d0 d1 i (i + 1) (fun h => h0 h.1) (fun h => h1 h.1)]
      exact zero_comp

@[simp] theorem threeTermComplex_X_zero (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (hd : d1 ∘ₗ d0 = 0) : (threeTermComplex d0 d1 hd).X 0 = ModuleCat.of S M := rfl

@[simp] theorem threeTermComplex_X_one (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (hd : d1 ∘ₗ d0 = 0) : (threeTermComplex d0 d1 hd).X 1 = ModuleCat.of S N := rfl

@[simp] theorem threeTermComplex_X_two (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (hd : d1 ∘ₗ d0 = 0) : (threeTermComplex d0 d1 hd).X 2 = ModuleCat.of S M' := rfl

theorem threeTermComplex_d_zero_one (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (hd : d1 ∘ₗ d0 = 0) : (threeTermComplex d0 d1 hd).d 0 1 = ModuleCat.ofHom d0 := rfl

theorem threeTermComplex_d_one_two (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M')
    (hd : d1 ∘ₗ d0 = 0) : (threeTermComplex d0 d1 hd).d 1 2 = ModuleCat.ofHom d1 := rfl

/-- The homotopy maps `h¹ : N → M`, `h² : M' → N` in degrees `1 → 0`, `2 → 1`. -/
def threeTermH (h1 : N →ₗ[S] M) (h2 : M' →ₗ[S] N) :
    ∀ i j : ℤ, threeTermX S M N M' i ⟶ threeTermX S M N M' j
  | .ofNat 1, .ofNat 0 => ModuleCat.ofHom h1
  | .ofNat 2, .ofNat 1 => ModuleCat.ofHom h2
  | _, _ => 0

theorem threeTermH_eq_zero (h1 : N →ₗ[S] M) (h2 : M' →ₗ[S] N) (i j : ℤ)
    (h : ¬ (i = 1 ∧ j = 0)) (h' : ¬ (i = 2 ∧ j = 1)) : threeTermH h1 h2 i j = 0 := by
  rcases i with (_ | _ | _ | n) | n <;> rcases j with (_ | _ | _ | m) | m <;>
    first | rfl | exact absurd ⟨rfl, rfl⟩ h | exact absurd ⟨rfl, rfl⟩ h'

/-- **A contraction of the three-term model is a Mathlib contracting homotopy** (tex L3731–3735,
L3762–3765: "contract the complex"). PROVED. -/
theorem contractible_of_isContraction (d0 : M →ₗ[S] N) (d1 : N →ₗ[S] M') (hd : d1 ∘ₗ d0 = 0)
    (h1 : N →ₗ[S] M) (h2 : M' →ₗ[S] N) (hc : IsContraction d0 d1 h1 h2) :
    Nonempty (Homotopy (𝟙 (threeTermComplex d0 d1 hd)) 0) := by
  refine ⟨{ hom := fun i j => (show (threeTermComplex d0 d1 hd).X i ⟶
      (threeTermComplex d0 d1 hd).X j from threeTermH h1 h2 i j), zero := ?_, comm := ?_ }⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    apply threeTermH_eq_zero
    · rintro ⟨rfl, rfl⟩; exact hij rfl
    · rintro ⟨rfl, rfl⟩; exact hij rfl
  · intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from by simp)]
    simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero]
    rcases i with (_ | _ | _ | n) | n
    · -- degree 0: `h¹ d⁰ = 1`
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : M) => ?_)
      change x = h1 (d0 x) + (0 : M)
      rw [add_zero]; exact (LinearMap.congr_fun hc.deg0 x).symm
    · -- degree 1: `d⁰ h¹ + h² d¹ = 1`
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : N) => ?_)
      change x = h2 (d1 x) + d0 (h1 x)
      have := LinearMap.congr_fun hc.deg1 x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [add_comm]; exact this.symm
    · -- degree 2: `d¹ h² = 1`
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : M') => ?_)
      change x = (0 : M') + d1 (h2 x)
      rw [zero_add]; exact (LinearMap.congr_fun hc.deg2 x).symm
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _
    · ext x
      exact Subsingleton.elim (α := PUnit) _ _

end Bridge

/-- **Contractibility is invariant under homotopy equivalence.** PROVED. -/
theorem contractible_of_homotopyEquiv {V : Type*} [Category V] [Preadditive V]
    {c : ComplexShape ℤ} {K L : HomologicalComplex V c} (e : HomotopyEquiv K L)
    (hL : Nonempty (Homotopy (𝟙 L) 0)) : Nonempty (Homotopy (𝟙 K) 0) := by
  obtain ⟨h⟩ := hL
  exact ⟨(e.homotopyHomInvId.symm.trans (Homotopy.ofEq (by simp))).trans
    (((h.compLeft e.hom).compRight e.inv).trans (Homotopy.ofEq (by simp)))⟩

section Tame

variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M]

/-- **The tame local model (4.4) as a cochain complex** `M → M ⊕ M → M` (tex L3470–3476), for
`DC = CA`. -/
def tameComplex (A C D : Module.End S M) (hDC : D * C = C * A) :
    CochainComplex (ModuleCat.{0} S) ℤ :=
  threeTermComplex (tameD0 A C) (tameD1 C D)
    ((tameModelIsComplex_proof S M A C D).2 hDC)

/-- **The tame model is contractible at active and moving places** (tex L3731–3735 with
L3753–3754: `A, D` units over `𝒪[G]`; tex L3755–3765: inertia minus one `C` a unit). If
`DC = CA` and either `A, D` are units or `C` is a unit, the complex `tameComplex A C D` is
contractible (Mathlib `Homotopy (𝟙 _) 0`). Classification: PROVED. -/
def TameComplexContractible : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (A C D : Module.End S M)
    (hDC : D * C = C * A), (IsUnit A ∧ IsUnit D) ∨ IsUnit C →
      Nonempty (Homotopy (𝟙 (tameComplex A C D hDC)) 0)

theorem tameComplexContractible_proof : TameComplexContractible := by
  intro S M _ _ _ A C D hDC h
  rcases h with ⟨hA, hD⟩ | hC
  · exact contractible_of_isContraction _ _ _ _ _
      (frobeniusContraction_proof S M A C D hA hD hDC)
  · exact contractible_of_isContraction _ _ _ _ _
      (inertiaContraction_proof S M A C D hC hDC)

/-- **When `DC = CA` holds** (tex L3472–3476): for commuting `Φ, g` and `q = 2k + 1`,
`D C = C A` (with `A = Φ − 1`, `C = g − 1`, `D = Φ − N_q(g)`) iff `k (g² − 1) = 0`.
(At the moving prime `g = 1 + t`, this is `((r−1)/2)((1+t)² − 1) = 0`, which holds in `A_i` for
`r ≡ 1 mod 2^{i+1}`; at an active scalar prime `g = −1` it holds outright.) Classification:
PROVED. -/
def TameCommutingCriterion : Prop :=
  ∀ (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (k : ℕ) (Φ g : Module.End S M),
    Φ * g = g * Φ →
      ((Φ - normQ k g) * (g - 1) = (g - 1) * (Φ - 1) ↔ (k : ℕ) • (g * g - 1) = 0)

theorem tameCommutingCriterion_proof : TameCommutingCriterion := by
  intro S M _ _ _ k Φ g hc
  obtain ⟨e, hN, -⟩ := tameCommutator_proof S M k Φ g
  rw [← sub_eq_zero, e, hc, sub_self, zero_sub, neg_eq_zero, hN, smul_mul_assoc]
  have : (1 + g) * (g - 1) = g * g - 1 := by noncomm_ring
  rw [this]

end Tame

end ZInQ.Contrib.CloudB3RC53.PairedFunctional

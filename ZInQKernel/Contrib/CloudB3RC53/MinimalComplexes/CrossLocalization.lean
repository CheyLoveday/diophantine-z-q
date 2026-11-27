import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Lambda

/-!
# RC53 MinimalComplexes: the localized paired functionals have one generic value

Proposition `ex:arith-paired-functional`, tex L3715–3719 ("its paired functional has an integral
representative at every height-one prime `𝔭 ≠ (2)` of `Λ` [...]. These representatives have the
same generic value for that primitive constituent") and its proof, tex L3748–3758 ("The inverse is
unique in the derived category, so representatives built at distinct localizations define the same
generic functional"). This closes finding 11 of the independent review of `PairedFunctional`: the
existence of the integral representative at each single prime is `PairedFunctionalHeightOne`; here
is the comparison between two primes.

**Form (`DEPARTURE`, form only).** The retained bounded free models are complexes of finite free
modules, so they are written by their matrices: the comparison `j : C' → C` (`C' = C_{U^⊥}`,
`C = τ^* C_U`) in degrees `0, 1, 2`, the transported cocycle `c(z) ∈ C^1`, the differential
`C_U^2 → C_U^3`, and the duality components `PD₂ : C_U^2 × C'^1 → Λ`, `PD₃ : C_U^3 × C'^0 → Λ`
as matrices `P₂`, `P₃` with the Leibniz rule `P₂ d'⁰ = ε (d_U²)ᵀ P₃` (the shape of the
`PairedFunctional` Leibniz hypotheses). Base change along a ring map is entrywise. An integral
homotopy inverse over a ring `S` is recorded by the components the argument uses: `ψ⁰, ψ¹, ψ²`
with the chain identities, and the degree-one homotopy identities `j¹ψ¹ − 1 = d⁰h¹ + h²d¹`,
`ψ¹j¹ − 1 = d'⁰k¹ + k²d'¹`.

Nodes (PROVED):
* `GenericValueUnique`: over any commutative ring, two homotopy inverses of the same comparison give
  functionals `w ↦ w · P₂ ψ¹ c(z)` that agree on every `2`-cocycle `w` of `C_U`.
* `CrossLocalizationGenericValue` (tex L3715–3719, L3748–3758): for any two height-one primes
  `𝔭, 𝔮 ≠ (2)` of `Λ` (in particular `𝔭 ≠ 𝔮`), integral representatives over `Λ_𝔭` and over `Λ_𝔮`
  have the same image in the fraction field `Frac Λ` on every `2`-cocycle, and in particular on
  every integral `2`-cocycle.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open Matrix ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- The matrix data over a commutative ring `R` of the comparison `j : C' → C`, the transported
cocycle `c(z)`, the differential `d_U² : C_U^2 → C_U^3`, and the duality components `P₂`, `P₃`
(see the module docstring). -/
structure PairingData (R : Type*) [CommRing R] (p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ : ℕ) where
  dP0 : Matrix (Fin p₁) (Fin p₀) R
  dP1 : Matrix (Fin p₂) (Fin p₁) R
  dC0 : Matrix (Fin c₁) (Fin c₀) R
  dC1 : Matrix (Fin c₂) (Fin c₁) R
  j0 : Matrix (Fin c₀) (Fin p₀) R
  j1 : Matrix (Fin c₁) (Fin p₁) R
  j2 : Matrix (Fin c₂) (Fin p₂) R
  cz : Fin c₁ → R
  dU2 : Matrix (Fin u₃) (Fin u₂) R
  P2 : Matrix (Fin u₂) (Fin p₁) R
  P3 : Matrix (Fin u₃) (Fin p₀) R
  ε : R

variable {p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ : ℕ}

/-- Entrywise base change commutes with `mulVec`. -/
theorem map_mulVec_comp {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) (v : Fin n → R) :
    (M.map f *ᵥ fun i => f (v i)) = fun i => f ((M *ᵥ v) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum]

/-- The identities of the data: `j` is a chain map, `c(z)` is a cocycle, and the Leibniz rule
`PD₂(w, d'y) = ε PD₃(d_U w, y)`. -/
structure PairingData.Valid {R : Type*} [CommRing R] (X : PairingData R p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃) :
    Prop where
  chain0 : X.dC0 * X.j0 = X.j1 * X.dP0
  chain1 : X.dC1 * X.j1 = X.j2 * X.dP1
  cocycle : X.dC1 *ᵥ X.cz = 0
  leibniz : X.P2 * X.dP0 = X.ε • (X.dU2ᵀ * X.P3)

/-- Entrywise base change of the data along a ring map. -/
def PairingData.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (X : PairingData R p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃) : PairingData S p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ :=
  ⟨X.dP0.map f, X.dP1.map f, X.dC0.map f, X.dC1.map f, X.j0.map f, X.j1.map f, X.j2.map f,
    fun i => f (X.cz i), X.dU2.map f, X.P2.map f, X.P3.map f, f X.ε⟩

/-- An (integral) homotopy inverse of `j` over `S`, by the components used: `ψ` is a chain map
`C → C'` in degrees `0 → 1 → 2`, `h : jψ ≃ 1` and `k : ψj ≃ 1` in degree one. -/
structure HomotopyInverse {S : Type*} [CommRing S] (X : PairingData S p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃) where
  ψ0 : Matrix (Fin p₀) (Fin c₀) S
  ψ1 : Matrix (Fin p₁) (Fin c₁) S
  ψ2 : Matrix (Fin p₂) (Fin c₂) S
  h1 : Matrix (Fin c₀) (Fin c₁) S
  h2 : Matrix (Fin c₁) (Fin c₂) S
  k1 : Matrix (Fin p₀) (Fin p₁) S
  k2 : Matrix (Fin p₁) (Fin p₂) S
  chain0 : X.dP0 * ψ0 = ψ1 * X.dC0
  chain1 : X.dP1 * ψ1 = ψ2 * X.dC1
  homC : X.j1 * ψ1 - 1 = X.dC0 * h1 + h2 * X.dC1
  homP : ψ1 * X.j1 - 1 = X.dP0 * k1 + k2 * X.dP1

/-- The paired functional `λ(w) = PD₂(w, ψ¹ c(z)) = w · P₂ ψ¹ c(z)` (tex L3752–3754). -/
def HomotopyInverse.functional {S : Type*} [CommRing S]
    {X : PairingData S p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃} (H : HomotopyInverse X) (w : Fin u₂ → S) : S :=
  w ⬝ᵥ (X.P2 *ᵥ (H.ψ1 *ᵥ X.cz))

/-- Base change of a homotopy inverse along a ring map. -/
def HomotopyInverse.map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    {X : PairingData S p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃} (H : HomotopyInverse X) :
    HomotopyInverse (X.map f) where
  ψ0 := H.ψ0.map f
  ψ1 := H.ψ1.map f
  ψ2 := H.ψ2.map f
  h1 := H.h1.map f
  h2 := H.h2.map f
  k1 := H.k1.map f
  k2 := H.k2.map f
  chain0 := by simp only [PairingData.map]; rw [← Matrix.map_mul, ← Matrix.map_mul, H.chain0]
  chain1 := by simp only [PairingData.map]; rw [← Matrix.map_mul, ← Matrix.map_mul, H.chain1]
  homC := by
    simp only [PairingData.map]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_one f f.map_zero f.map_one,
      ← Matrix.map_sub _ (map_sub f), ← Matrix.map_add _ (map_add f), H.homC]
  homP := by
    simp only [PairingData.map]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_one f f.map_zero f.map_one,
      ← Matrix.map_sub _ (map_sub f), ← Matrix.map_add _ (map_add f), H.homP]

theorem PairingData.Valid.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {X : PairingData R p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃} (hX : X.Valid) : (X.map f).Valid where
  chain0 := by simp only [PairingData.map]; rw [← Matrix.map_mul, ← Matrix.map_mul, hX.chain0]
  chain1 := by simp only [PairingData.map]; rw [← Matrix.map_mul, ← Matrix.map_mul, hX.chain1]
  cocycle := by
    simp only [PairingData.map]
    rw [map_mulVec_comp, hX.cocycle]; ext i; simp
  leibniz := by
    simp only [PairingData.map]
    rw [← Matrix.map_mul, hX.leibniz]
    ext a b; simp [Matrix.mul_apply, map_sum, map_mul]

theorem HomotopyInverse.functional_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    {X : PairingData S p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃} (H : HomotopyInverse X) (w : Fin u₂ → S) :
    (H.map f).functional (fun i => f (w i)) = f (H.functional w) := by
  simp only [HomotopyInverse.functional, HomotopyInverse.map, PairingData.map]
  rw [map_mulVec_comp, map_mulVec_comp]
  simp [dotProduct, map_sum, map_mul]

/-- **Uniqueness of the generic value** (tex L3755–3758: "The inverse is unique in the derived
category"). Over any commutative ring, for valid data and two homotopy inverses `H, H'` of the same
comparison `j`, the functionals agree on every `2`-cocycle `w` of `C_U` (`d_U² w = 0`).
Classification: PROVED. -/
def GenericValueUnique : Prop :=
  ∀ (K : Type) [CommRing K] (p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ : ℕ)
    (X : PairingData K p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃), X.Valid →
    ∀ (H H' : HomotopyInverse X) (w : Fin u₂ → K), X.dU2 *ᵥ w = 0 →
      H.functional w = H'.functional w

theorem genericValueUnique_proof : GenericValueUnique := by
  intro K _ p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ X hX H H' w hw
  -- `ψ¹ c(z) − ψ'¹ c(z) = d'⁰ y` with `y = ψ'⁰ h¹ c(z) − k'¹ ψ¹ c(z)`
  set y : Fin p₀ → K := H'.ψ0 *ᵥ (H.h1 *ᵥ X.cz) - H'.k1 *ᵥ (H.ψ1 *ᵥ X.cz) with hy
  have hdP1 : X.dP1 *ᵥ (H.ψ1 *ᵥ X.cz) = 0 := by
    rw [Matrix.mulVec_mulVec, H.chain1, ← Matrix.mulVec_mulVec, hX.cocycle, Matrix.mulVec_zero]
  have hjψ : X.j1 *ᵥ (H.ψ1 *ᵥ X.cz) = X.cz + X.dC0 *ᵥ (H.h1 *ᵥ X.cz) := by
    have e := congrArg (fun M => M *ᵥ X.cz) H.homC
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at e
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX.cocycle,
      Matrix.mulVec_zero, add_zero] at e
    rw [← e]; abel
  have hψ'j : H'.ψ1 *ᵥ (X.j1 *ᵥ (H.ψ1 *ᵥ X.cz)) =
      H.ψ1 *ᵥ X.cz + X.dP0 *ᵥ (H'.k1 *ᵥ (H.ψ1 *ᵥ X.cz)) := by
    have e := congrArg (fun M => M *ᵥ (H.ψ1 *ᵥ X.cz)) H'.homP
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at e
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdP1,
      Matrix.mulVec_zero, add_zero] at e
    rw [← e]; abel
  have hdiff : H.ψ1 *ᵥ X.cz - H'.ψ1 *ᵥ X.cz = X.dP0 *ᵥ y := by
    have h2 : H'.ψ1 *ᵥ (X.dC0 *ᵥ (H.h1 *ᵥ X.cz)) = X.dP0 *ᵥ (H'.ψ0 *ᵥ (H.h1 *ᵥ X.cz)) := by
      simp only [Matrix.mulVec_mulVec]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, H'.chain0]
    rw [hjψ, Matrix.mulVec_add, h2] at hψ'j
    rw [hy, Matrix.mulVec_sub]
    linear_combination -hψ'j
  have hfun : H.functional w - H'.functional w = w ⬝ᵥ (X.P2 *ᵥ (X.dP0 *ᵥ y)) := by
    simp only [HomotopyInverse.functional]
    rw [← dotProduct_sub, ← Matrix.mulVec_sub, hdiff]
  rw [← sub_eq_zero, hfun, Matrix.mulVec_mulVec, hX.leibniz, Matrix.smul_mulVec,
    dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hw,
    zero_dotProduct, smul_zero]

/-- `GenericValueUnique` for homotopy inverses of data equal to `X` (used after base change,
where the two base-changed data are equal but not syntactically). PROVED. -/
theorem functional_eq_of_eq {K : Type} [CommRing K] (X Y Y' : PairingData K p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃)
    (hX : X.Valid) (hY : Y = X) (hY' : Y' = X) (H : HomotopyInverse Y) (H' : HomotopyInverse Y')
    (w : Fin u₂ → K) (hw : X.dU2 *ᵥ w = 0) : H.functional w = H'.functional w := by
  subst hY; subst hY'
  exact genericValueUnique_proof K p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ _ hX H H' w hw

/-- The map `Λ_𝔭 → Frac Λ`. -/
def toFrac (p : Ideal Lam) [p.IsPrime] : Localization.AtPrime p →+* FractionRing Lam :=
  IsLocalization.lift (M := p.primeCompl) (g := algebraMap Lam (FractionRing Lam)) fun y =>
    IsLocalization.map_units (FractionRing Lam) (⟨y, p.primeCompl_le_nonZeroDivisors y.2⟩ :
      nonZeroDivisors Lam)

theorem toFrac_comp (p : Ideal Lam) [p.IsPrime] :
    (toFrac p).comp (algebraMap Lam (Localization.AtPrime p)) = algebraMap Lam (FractionRing Lam) :=
  IsLocalization.lift_comp _

theorem toFrac_algebraMap (p : Ideal Lam) [p.IsPrime] (x : Lam) :
    toFrac p (algebraMap Lam (Localization.AtPrime p) x) = algebraMap Lam (FractionRing Lam) x := by
  rw [← RingHom.comp_apply, toFrac_comp]

/-- **The localized paired functionals have one generic value** (tex L3715–3719, L3748–3758;
review finding 11). Let `𝔭, 𝔮` be height-one primes of `Λ`, both different from `(2)` (in
particular `𝔭 ≠ 𝔮` is allowed). For valid data over `Λ` (the comparison, the transported cocycle and
the duality, see the module docstring) and integral homotopy inverses `H_𝔭` over `Λ_𝔭` and `H_𝔮` over
`Λ_𝔮` of its base changes (these exist by `PairedFunctionalHeightOne`), the two functionals have the
same image in `Frac Λ`: on every `2`-cocycle `w` over `Frac Λ` their base changes agree, and on every
integral `2`-cocycle `w` over `Λ`, `λ_𝔭(w)` and `λ_𝔮(w)` have the same image in `Frac Λ`.
Classification: PROVED. -/
def CrossLocalizationGenericValue : Prop :=
  ∀ (p q : Ideal Lam) [p.IsPrime] [q.IsPrime], p.height = 1 → q.height = 1 →
    p ≠ Ideal.span {(2 : Lam)} → q ≠ Ideal.span {(2 : Lam)} →
    ∀ (p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ : ℕ) (X : PairingData Lam p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃), X.Valid →
    ∀ (Hp : HomotopyInverse (X.map (algebraMap Lam (Localization.AtPrime p))))
      (Hq : HomotopyInverse (X.map (algebraMap Lam (Localization.AtPrime q)))),
      (∀ w : Fin u₂ → FractionRing Lam,
        (X.dU2.map (algebraMap Lam (FractionRing Lam))) *ᵥ w = 0 →
        (Hp.map (toFrac p)).functional w = (Hq.map (toFrac q)).functional w) ∧
      (∀ w : Fin u₂ → Lam, X.dU2 *ᵥ w = 0 →
        toFrac p (Hp.functional fun i => algebraMap Lam _ (w i)) =
          toFrac q (Hq.functional fun i => algebraMap Lam _ (w i)))

theorem crossLocalizationGenericValue_proof : CrossLocalizationGenericValue := by
  intro p q _ _ _ _ _ _ p₀ p₁ p₂ c₀ c₁ c₂ u₂ u₃ X hX Hp Hq
  -- both base changes are homotopy inverses of the same generic data
  have ep : (X.map (algebraMap Lam (Localization.AtPrime p))).map (toFrac p) =
      X.map (algebraMap Lam (FractionRing Lam)) := by
    simp only [PairingData.map, Matrix.map_map, ← RingHom.coe_comp, toFrac_comp, toFrac_algebraMap]
  have eq : (X.map (algebraMap Lam (Localization.AtPrime q))).map (toFrac q) =
      X.map (algebraMap Lam (FractionRing Lam)) := by
    simp only [PairingData.map, Matrix.map_map, ← RingHom.coe_comp, toFrac_comp, toFrac_algebraMap]
  have hK := hX.map (algebraMap Lam (FractionRing Lam))
  have key : ∀ w : Fin u₂ → FractionRing Lam,
      (X.dU2.map (algebraMap Lam (FractionRing Lam))) *ᵥ w = 0 →
      (Hp.map (toFrac p)).functional w = (Hq.map (toFrac q)).functional w := fun w hw =>
    functional_eq_of_eq _ _ _ hK ep eq _ _ w hw
  refine ⟨key, fun w hw => ?_⟩
  have hcomp : ∀ (r : Ideal Lam) [r.IsPrime] (i : Fin u₂),
      toFrac r (algebraMap Lam (Localization.AtPrime r) (w i)) =
        algebraMap Lam (FractionRing Lam) (w i) := fun r _ i => by
    rw [← RingHom.comp_apply, toFrac_comp]
  rw [← HomotopyInverse.functional_map, ← HomotopyInverse.functional_map]
  simp only [hcomp]
  apply key
  rw [map_mulVec_comp, hw]; ext i; simp

/-- A small instance of the data (`C'^1 = C^1 = C_U^2 = R`, other degrees zero, `j¹ = 1`,
`c(z) = 1`, `P₂ = 1`), for non-vacuity. -/
def exampleData (R : Type*) [CommRing R] : PairingData R 0 1 0 0 1 0 1 0 :=
  ⟨0, 0, 0, 0, 0, 1, 0, fun _ => 1, 0, 1, 0, 1⟩

/-- **Non-vacuity**: over every commutative ring the example data are valid and have the integral
homotopy inverse `ψ¹ = 1` (zero homotopies), whose functional is `w ↦ w 0`, nonzero when `R` is
nontrivial; so the hypotheses of `CrossLocalizationGenericValue` are satisfiable with a nonzero
functional. PROVED. -/
theorem exampleData_valid_inverse (R : Type*) [CommRing R] :
    (exampleData R).Valid ∧ ∃ H : HomotopyInverse (exampleData R),
      ∀ w : Fin 1 → R, H.functional w = w 0 := by
  refine ⟨⟨by ext i j; exact Fin.elim0 j, by ext i j; exact Fin.elim0 i,
    by ext i; exact Fin.elim0 i, by ext i j; exact Fin.elim0 j⟩,
    ⟨⟨0, 1, 0, 0, 0, 0, 0, by ext i j; exact Fin.elim0 j, by ext i j; exact Fin.elim0 i,
      by simp [exampleData], by simp [exampleData]⟩, fun w => ?_⟩⟩
  simp [HomotopyInverse.functional, exampleData, dotProduct]

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes

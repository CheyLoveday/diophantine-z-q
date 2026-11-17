import ZInQKernel.Contrib.OneProof.HeckePin

/-! hecke-pin: the three leaves and the definitions they depend on, copied verbatim from
`ZInQKernel/Contrib/OneProof/AfTateLambda.lean` (§§1–3, §5) and `R16CoreYDS965.lean` (l. 59), with
definitional checks against the originals. -/

noncomputable section

namespace HeckePinTarget

open scoped TensorProduct MatrixGroups
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open IsDedekindDomain NumberField
open AfTateLam (frobLam rhoLam vQ)

abbrev CPt (X : Over SpecQ) : Type := ptObj (K := ℚ) ℂ ⟶ X

def IsX1Gen (N : ℕ) (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField) : Prop :=
  Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), AfTateOr.ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (AfTateOr.toQ F) τ = 0

def RegAt {X : Over SpecQ} [IsIntegral X.left] (x : CPt X) (g : X.left.functionField) (c : ℂ) :
    Prop :=
  ∃ (U : X.left.Opens) (_ : Nonempty U) (s : Γ(X.left, U)) (h : ⊤ ≤ x.left ⁻¹ᵁ U),
    X.left.germToFunctionField U s = g ∧
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appLE U ⊤ h s) = c

def AtTau (N : ℕ) {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField) (x : CPt X)
    (τ : UpperHalfPlane) : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℤ)) (c : ℂ), AfTateOr.ev2 Q jX tX ≠ 0 →
    Filter.Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (nhdsWithin τ {τ}ᶜ) (nhds c) →
      RegAt x (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX) c

def shiftDiv (p j : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨((τ : ℂ) + j) / p, by
      have h := τ.coe_im_pos
      rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
      exact div_pos h (by exact_mod_cast hp)⟩
  else τ

def mulNat (p : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨(p : ℂ) * τ, by
      have h := τ.coe_im_pos
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      exact mul_pos (by exact_mod_cast hp) h⟩
  else τ

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}

abbrev ajC (aj : X ⟶ J.X) (x : CPt X) : J.Pt ℂ := x ≫ aj

abbrev endC (t : AbVar.End J) (y : J.Pt ℂ) : J.Pt ℂ := y ≫ t.hom

def IsHeckeT (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (p : ℕ) (t : AbVar.End J) :
    Prop :=
  ∀ (τ τ' : UpperHalfPlane) (x x' : CPt X) (y y' : Fin p → CPt X),
    AtTau N jX tX x τ → AtTau N jX tX x' τ' →
    (∀ i : Fin p, AtTau N jX tX (y i) (shiftDiv p i τ)) →
    (∀ i : Fin p, AtTau N jX tX (y' i) (shiftDiv p i τ')) →
    (p ∣ N → endC t (ajC aj x / ajC aj x') = ∏ i, ajC aj (y i) / ajC aj (y' i)) ∧
    (¬ p ∣ N → ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (p : ZMod N) →
      ∀ z z' : CPt X, AtTau N jX tX z (g • mulNat p τ) → AtTau N jX tX z' (g • mulNat p τ') →
        endC t (ajC aj x / ajC aj x') = (∏ i, ajC aj (y i) / ajC aj (y' i)) * (ajC aj z / ajC aj z'))

def IsDiamond (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (d : (ZMod N)ˣ)
    (δ : AbVar.End J) : Prop :=
  ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
    ∀ (τ τ' : UpperHalfPlane) (x x' z z' : CPt X),
      AtTau N jX tX x τ → AtTau N jX tX x' τ' → AtTau N jX tX z (g • τ) → AtTau N jX tX z' (g • τ') →
        endC δ (ajC aj x / ajC aj x') = ajC aj z / ajC aj z'

abbrev HeckeGen (N : ℕ) : Type := Nat.Primes ⊕ (ZMod N)ˣ

abbrev HeckeFree (N : ℕ) : Type := FreeAlgebra ℤ (HeckeGen N)

def evF {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) : HeckeFree N →ₐ[ℤ] ℂ :=
  FreeAlgebra.lift ℤ (Sum.elim (fun p => coeff f (p : ℕ)) (fun d => χ (d : ZMod N)))

def heckeJ {N : ℕ} (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    HeckeFree N →ₐ[ℤ] AbVar.End J :=
  FreeAlgebra.lift ℤ (Sum.elim tp δ)

def KillsIf {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {B : AbVar ℚ} (φ : AbVar.Hom J B) : Prop :=
  ∀ h : HeckeFree N, evF χ f h = 0 → (heckeJ tp δ h).hom ≫ φ.hom = (0 : AbVar.Hom J B).hom

def IsAfQuotient {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) (A : AbVar ℚ) (π : AbVar.Hom J A) : Prop :=
  AlgebraicGeometry.Surjective π.hom.left ∧ KillsIf χ f tp δ π ∧
    ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B), KillsIf χ f tp δ φ →
      ∃! ψ : AbVar.Hom A B, π.hom ≫ ψ.hom = φ.hom

def IsAfAction {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {A : AbVar ℚ} (π : AbVar.Hom J A)
    (θ : coeffField f →+* A.End0) : Prop :=
  (∀ p : Nat.Primes, ∃ e : AbVar.End A, (tp p).hom ≫ π.hom = π.hom ≫ e.hom ∧
      θ ⟨coeff f (p : ℕ), coeff_mem_coeffField f p⟩ = (1 : ℚ) ⊗ₜ e) ∧
  (∀ d : (ZMod N)ˣ, ∃ (c : coeffField f) (e : AbVar.End A), (c : ℂ) = χ (d : ZMod N) ∧
      (δ d).hom ≫ π.hom = π.hom ≫ e.hom ∧ θ c = (1 : ℚ) ⊗ₜ e)

def HeckeJ1DS : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
      ∃ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
        (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) ∧
        (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d))

def AfShimura : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          IsAfQuotient χ f tp δ A π ∧ IsAfAction χ f tp δ π θ

def AfCharpolyDS965 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime]
      (lam : HeightOneSpectrum (𝓞 (coeffField f))) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      letI := R16Used.tensorModule ℓ A θ
      letI := (rhoLam ℓ lam).toAlgebra
      letI : Module.Free (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) :=
        Module.Free.of_divisionRing (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)
      ∀ [Module.Finite (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)],
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
          LinearMap.charpoly (frobLam ℓ A θ lam σ) =
            ((Polynomial.X : Polynomial (lam.adicCompletion (coeffField f))) ^ 2 -
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * Polynomial.X +
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                (c * (p : coeffField f))) : Polynomial (lam.adicCompletion (coeffField f)))

end HeckePinTarget

open HeckePinTarget in
theorem heckePin_copy_iff :
    (HeckePinTarget.HeckeJ1DS ↔ AfTateLam.HeckeJ1DS) ∧ (HeckePinTarget.AfShimura ↔ AfTateLam.AfShimura) ∧
      (HeckePinTarget.AfCharpolyDS965 ↔ AfTateLam.AfCharpolyDS965) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

import ZInQKernel.Contrib.OneProof.AfTateOr
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

set_option linter.unusedSectionVars false

namespace AfTateLam

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct MatrixGroups

/-! ## 1. The uniformization `τ ↦ x_τ ∈ X(ℂ)` of a model of `X₁(N)_alg` -/

/-- `X(ℂ)`: the complex points of a `ℚ`-scheme. -/
abbrev CPt (X : Over SpecQ) : Type := ptObj (K := ℚ) ℂ ⟶ X

/-- Diamond–Shurman's `X₁(N)_alg` with chosen generators `j_X, t_X` of `K(X)` (the body of
`AfTateOr.IsX1AlgDS` with the generators named): `K(X) = ℚ(j_X, t_X)` and the integer relations of
`(j_X, t_X)` are those of `(j(τ), f₁(τ))` on `ℍ`. -/
def IsX1Gen (N : ℕ) (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField) : Prop :=
  Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), AfTateOr.ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (AfTateOr.toQ F) τ = 0

/-- The rational function `g ∈ K(X)` is regular at the complex point `x` with value `c`: it is the
germ of a section `s` over an open `U` containing (the image of) `x`, and `s(x) = c`. -/
def RegAt {X : Over SpecQ} [IsIntegral X.left] (x : CPt X) (g : X.left.functionField) (c : ℂ) :
    Prop :=
  ∃ (U : X.left.Opens) (_ : Nonempty U) (s : Γ(X.left, U)) (h : ⊤ ≤ x.left ⁻¹ᵁ U),
    X.left.germToFunctionField U s = g ∧
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appLE U ⊤ h s) = c

/-- **`x = x_τ`, the point of `X(ℂ)` at `τ ∈ ℍ`** (Diamond–Shurman §7.5–7.7: `X₁(N)(ℂ) ⊇ Γ₁(N)\ℍ`
through `ℂ(X₁(N)) = ℂ(j, f₁)`). Every `g = P(j_X, t_X)/Q(j_X, t_X) ∈ K(X)` whose meromorphic function
`P(j, f₁)/Q(j, f₁)` on `ℍ` has a limit `c` at `τ` is regular at `x` with value `c`. (Limits over the
punctured neighbourhood avoid the values of `T5Glue.weber` off Weber's generic branch. For every
`τ` exactly one complex point satisfies this: the uniformization `ℍ → X(ℂ)` is holomorphic and
non-constant, and the rational functions regular at a point determine it.) -/
def AtTau (N : ℕ) {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField) (x : CPt X)
    (τ : UpperHalfPlane) : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℤ)) (c : ℂ), AfTateOr.ev2 Q jX tX ≠ 0 →
    Filter.Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (nhdsWithin τ {τ}ᶜ) (nhds c) →
      RegAt x (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX) c

/-! ## 2. Hecke operators on `J₁(N)` (Diamond–Shurman §6.3, §7.9) -/

/-- `τ ↦ (τ + j)/p`. -/
def shiftDiv (p j : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨((τ : ℂ) + j) / p, by
      have h := τ.coe_im_pos
      rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
      exact div_pos h (by exact_mod_cast hp)⟩
  else τ

/-- `τ ↦ pτ`. -/
def mulNat (p : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨(p : ℂ) * τ, by
      have h := τ.coe_im_pos
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      exact mul_pos (by exact_mod_cast hp) h⟩
  else τ

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}

/-- The image `aj(x) ∈ J(ℂ)` of a complex point under the Abel–Jacobi map. -/
abbrev ajC (aj : X ⟶ J.X) (x : CPt X) : J.Pt ℂ := x ≫ aj

/-- An endomorphism acting on `J(ℂ)`. -/
abbrev endC (t : AbVar.End J) (y : J.Pt ℂ) : J.Pt ℂ := y ≫ t.hom

/-- **`t` is the Hecke operator `T_p` on `J₁(N) = Pic⁰(X₁(N))`** (Diamond–Shurman §6.3, with the coset
representatives of Prop. 5.2.1): on divisor classes of degree `0` supported on the points `x_τ`,
`T_p[x_τ] = Σ_{j<p} [x_{(τ+j)/p}] + [x_{γ(pτ)}]`, the last term only for `p ∤ N`, with
`γ = (a b; c d) ∈ SL₂(ℤ)`, `N ∣ c`, `d ≡ p (mod N)`. Classes `[x_τ] − [x_{τ'}]` are written
`aj(x_τ)/aj(x_{τ'})` in `J(ℂ)` (Abel–Jacobi). -/
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

/-- **`δ` is the diamond operator `⟨d⟩` on `J₁(N)`** (Diamond–Shurman §6.3): `⟨d⟩[x_τ] = [x_{γτ}]` for
`γ = (a b; c d') ∈ SL₂(ℤ)` with `N ∣ c`, `d' ≡ d (mod N)`. -/
def IsDiamond (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (d : (ZMod N)ˣ)
    (δ : AbVar.End J) : Prop :=
  ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
    ∀ (τ τ' : UpperHalfPlane) (x x' z z' : CPt X),
      AtTau N jX tX x τ → AtTau N jX tX x' τ' → AtTau N jX tX z (g • τ) → AtTau N jX tX z' (g • τ') →
        endC δ (ajC aj x / ajC aj x') = ajC aj z / ajC aj z'

/-! ## 3. The Hecke algebra, `I_f` and `A_f = J₁(N)/I_f J₁(N)` (Diamond–Shurman §6.6) -/

/-- Generators `T_p` (`p` prime) and `⟨d⟩` (`d ∈ (ℤ/N)^×`) of `𝕋_ℤ`. -/
abbrev HeckeGen (N : ℕ) : Type := Nat.Primes ⊕ (ZMod N)ˣ

/-- The free algebra on the generators; `𝕋_ℤ` is its image in `End(J₁(N))`. -/
abbrev HeckeFree (N : ℕ) : Type := FreeAlgebra ℤ (HeckeGen N)

/-- Eigenvalues of `f`: `T_p ↦ a_p(f)`, `⟨d⟩ ↦ χ(d)`. Its kernel maps onto `I_f = {T ∈ 𝕋_ℤ : Tf = 0}`. -/
def evF {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) : HeckeFree N →ₐ[ℤ] ℂ :=
  FreeAlgebra.lift ℤ (Sum.elim (fun p => coeff f (p : ℕ)) (fun d => χ (d : ZMod N)))

/-- The action on `J` through given `T_p`, `⟨d⟩`. -/
def heckeJ {N : ℕ} (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    HeckeFree N →ₐ[ℤ] AbVar.End J :=
  FreeAlgebra.lift ℤ (Sum.elim tp δ)

/-- `φ : J → B` kills `I_f J`. -/
def KillsIf {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {B : AbVar ℚ} (φ : AbVar.Hom J B) : Prop :=
  ∀ h : HeckeFree N, evF χ f h = 0 → (heckeJ tp δ h).hom ≫ φ.hom = (0 : AbVar.Hom J B).hom

/-- **`π : J → A` is `J ↠ J/I_f J = A_f`** (Diamond–Shurman Def. 6.6.3): surjective, kills `I_f J`,
and universal among homomorphisms to abelian varieties that kill `I_f J`. -/
def IsAfQuotient {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) (A : AbVar ℚ) (π : AbVar.Hom J A) : Prop :=
  AlgebraicGeometry.Surjective π.hom.left ∧ KillsIf χ f tp δ π ∧
    ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B), KillsIf χ f tp δ φ →
      ∃! ψ : AbVar.Hom A B, π.hom ≫ ψ.hom = φ.hom

/-- **`θ` is Diamond–Shurman's action of `K_f = (𝕋_ℤ/I_f) ⊗ ℚ` on `A_f`** (Prop. 6.6.4): `θ(a_p(f))` is
the endomorphism of `A_f` induced by `T_p`, and `θ(χ(d))` the one induced by `⟨d⟩`. -/
def IsAfAction {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {A : AbVar ℚ} (π : AbVar.Hom J A)
    (θ : coeffField f →+* A.End0) : Prop :=
  (∀ p : Nat.Primes, ∃ e : AbVar.End A, (tp p).hom ≫ π.hom = π.hom ≫ e.hom ∧
      θ ⟨coeff f (p : ℕ), coeff_mem_coeffField f p⟩ = (1 : ℚ) ⊗ₜ e) ∧
  (∀ d : (ZMod N)ˣ, ∃ (c : coeffField f) (e : AbVar.End A), (c : ℂ) = χ (d : ZMod N) ∧
      (δ d).hom ≫ π.hom = π.hom ≫ e.hom ∧ θ c = (1 : ℚ) ⊗ₜ e)

/-! ## 4. `K_{f,λ}`, `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` and `ρ_{f,λ}` (Diamond–Shurman §9.5) -/

section Lambda

open IsDedekindDomain NumberField

/-- The `ℓ`-adic place of `ℚ`. -/
def vQ (ℓ : ℕ) [Fact ℓ.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩

variable {K : Type} [Field K] [NumberField K]

/-- `ℚ_ℓ → K_λ` for a place `λ ∣ ℓ` (Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}`, then Tau Ceti's completion map). -/
def algQl (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] →+* lam.adicCompletion K :=
  ((vQ ℓ).adicCompletionExtension ℚ K lam).comp
    (RingHomClass.toRingHom (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ℓ, Fact.out⟩))

/-- `ℚ_ℓ ⊗_ℚ K → K_λ`, `x ⊗ a ↦ x · a`. -/
def rhoLam (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] ⊗[ℚ] K →+* lam.adicCompletion K :=
  letI : Algebra ℚ_[ℓ] (lam.adicCompletion K) := (algQl ℓ lam).toAlgebra
  R16Used.liftHom (algebraMap K (lam.adicCompletion K))

/-- `σ ∈ G_ℚ` on `V_ℓ(A)`, linear over `ℚ_ℓ ⊗ F` (endomorphisms are defined over `ℚ`). -/
def galR (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
    (θ : F →+* A.End0) (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ; A.V ℓ →ₗ[ℚ_[ℓ] ⊗[ℚ] F] A.V ℓ :=
  letI := R16Used.tensorModule ℓ A θ
  { toFun := A.galRep ℓ σ
    map_add' := map_add _
    map_smul' := fun r v => R16Used.galRep_tsmul ℓ A θ σ r v }

/-- **`ρ_{f,λ}(σ)`**: `σ` acting on `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K} V_ℓ(A)`. -/
def frobLam (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) (θ : K →+* A.End0) (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) →ₗ[lam.adicCompletion K]
      (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  (galR ℓ A θ σ).baseChange _

end Lambda

end AfTateLam

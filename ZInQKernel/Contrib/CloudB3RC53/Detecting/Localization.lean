import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition

/-!
# Detecting primes, part 1: localization at an unramified prime is evaluation at the Frobenius

Item (b) of the detecting-prime sizing. For the genuine Galois objects of RC/SelmerComplex/
(`G_{K,S}`, `G_{K_q}`, `locMap`, `urRes`) and the unramified complex `[W --(Φ−1)--> W]` with its
map `urToLocal` into the genuine local complex, all `PROVED`:

* `cocycle_zpow_eq_zero`: a cocycle (along a homomorphism `ι`) vanishing at the Frobenius of
  `H ≃ ℤ̂` vanishes on every power of it;
* `cocycle_comp_eq_urCocycle`: a continuous global `1`-cocycle restricted along `ι` equals
  `f ∘ c_x` with `f x = c(ι Frob)`. Here `c_x` is the `ℤ̂`-cocycle with `c_x(Frob) = x`; the
  powers of the Frobenius are dense;
* `localization_eq_frobValue`: at a prime `q ∉ S` with a factorization `ψ` of the localization
  through `Gal(K_q^ur/K_q)` (the GLUE `UnramifiedAtFactorization`), the localized cocycle is the
  degree-one image of `c(Frob_q)` under the unramified complex. In cohomology the localization is
  the class of `c(Frob_q)` in `W/(Φ−1)W`;
* `localization_eq_frobValue_quotient`: the same for a cocycle inflated from a finite quotient
  `Γ`; the controlling value is `c_Γ(Frob_q)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Detecting

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Generic

variable {Gg : Type} [Group Gg] [TopologicalSpace Gg] [IsTopologicalGroup Gg]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (ι : H →ₜ* Gg)
  {M : Type} [AddCommGroup M] [DistribMulAction Gg M]

/-- A cocycle along `ι` vanishing at the Frobenius vanishes on its powers. -/
theorem cocycle_zpow_eq_zero {d : H → M} (hd : ∀ a b, d (a * b) = ι a • d b + d a)
    (h0 : d (frobElt e) = 0) (n : ℤ) : d (frobElt e ^ n) = 0 := by
  have h1 : d 1 = 0 := by
    have := hd 1 1
    rw [mul_one, map_one, one_smul] at this
    exact left_eq_add.mp this
  have hinv : d (frobElt e)⁻¹ = 0 := by
    have := hd (frobElt e)⁻¹ (frobElt e)
    rw [inv_mul_cancel, h1, h0, smul_zero, zero_add] at this
    exact this.symm
  induction n using Int.induction_on with
  | zero => simpa using h1
  | succ n ih =>
    rw [zpow_add_one, hd, h0, smul_zero, zero_add]
    exact ih
  | pred n ih =>
    rw [zpow_sub_one, hd, hinv, smul_zero, zero_add]
    exact ih

variable {k : Type} [CommRing k] [TopologicalSpace k] (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  [TopologicalSpace M] [DiscreteTopology M] [Module k M]
  (f : X.V →ₗ[k] M) (hX : ∀ (h : H) (x : X.V), f (h • x) = ι h • f x)

include hX in
/-- **A global cocycle restricted along `ι` is the unramified cocycle of its Frobenius value**
(`PROVED`): if `c` is a continuous `1`-cocycle of `Gg` and `f x = c(ι(Frob))`, then
`c(ι h) = f(c_x(h))` for every `h`, where `c_x` is the cocycle of `ℤ̂` with `c_x(Frob) = x`.
Both sides are continuous cocycles along `ι` that agree at the Frobenius, hence on its powers,
which are dense. -/
theorem cocycle_comp_eq_urCocycle (c : Gg → M) (hc : Continuous c)
    (hcoc : ∀ a b, c (a * b) = a • c b + c a) (x : X.V) (hx : f x = c (ι (frobElt e))) (h : H) :
    c (ι h) = f (urCocycle e X x h) := by
  have hcont1 : Continuous fun h => c (ι h) := hc.comp (map_continuous ι)
  have hcont2 : Continuous fun h => f (urCocycle e X x h) :=
    (continuous_of_discreteTopology (f := f)).comp (urCocycle_continuous e X x)
  have hzpow : ∀ n : ℤ, c (ι (frobElt e ^ n)) = f (urCocycle e X x (frobElt e ^ n)) := by
    intro n
    have := cocycle_zpow_eq_zero e ι (d := fun h => c (ι h) - f (urCocycle e X x h))
      (fun a b => by
        simp only [map_mul, hcoc, urCocycle_cocycle, map_add, hX, smul_sub]
        abel)
      (by simp only [urCocycle_frob, hx, sub_self]) n
    exact sub_eq_zero.mp this
  exact congrFun (eq_of_eq_zpow e hcont1 hcont2 hzpow) h


end Generic

/-! ### At an unramified prime of a number field -/

section Galois

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (q : HeightOneSpectrum (𝓞 K)) {k : Type} [CommRing k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M] [TopologicalSpace M]
  [DiscreteTopology M]

/-- The image in `G_{K,S}` of the Frobenius at the unramified prime `q`, for a factorization
`ψ : Gal(K_q^ur/K_q) → G_{K,S}` of the localization map. -/
def frobGlobal (ψ : GUr K q →ₜ* GKS K S) : GKS K S := ψ (frobElt (eUr K q))

/-- **(b) Localization at an unramified prime is evaluation at the Frobenius** (`PROVED`). Let
`q ∉ S` and let `ψ` be a factorization of the localization `G_{K_q} → G_{K,S}` through
`Gal(K_q^ur/K_q) ≃ ℤ̂` (the GLUE `UnramifiedAtFactorization`). For a continuous `1`-cocycle `c` of
`G_{K,S}` with values in a discrete module `M` and `x` with `f x = c(Frob_q)`, the localization
`g ↦ c(p_q(g))` is, on the nose, the image `g ↦ f(c_x(res g))` of `x` under the unramified
complex `[W --(Φ−1)--> W] ⟶ C^•_cont(G_{K_q}, M)` in degree one (`urToLocal_galois`, component
`urLin₁`). In cohomology the localized class is therefore the image of the class of `c(Frob_q)` in
`W/(Φ−1)W = H¹(U^ur)` (`UnramifiedComplex.h1Iso`). -/
theorem localization_eq_frobValue (ψ : GUr K q →ₜ* GKS K S)
    (hψ : ∀ g, locMap K S q g = ψ (urRes K q g)) (X : TopRep.{0} k (GUr K q))
    [ContinuousSMul (GUr K q) X.V] [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hX : ∀ (h : GUr K q) (x : X.V), f (h • x) = ψ h • f x) (c : GKS K S → M) (hc : Continuous c)
    (hcoc : ∀ a b, c (a * b) = a • c b + c a) (x : X.V) (hx : f x = c (frobGlobal K S q ψ))
    (g : Gloc K q) : c (locMap K S q g) = f (urCocycle (eUr K q) X x (urRes K q g)) := by
  rw [hψ]
  exact cocycle_comp_eq_urCocycle (eUr K q) ψ X f hX c hc hcoc x hx _

/-- **(b) for a finite quotient** (`PROVED`): if the cocycle is inflated from a finite quotient
`p : G_{K,S} → Γ` (`c = c_Γ ∘ p`), the value that controls the localization at `q` is
`c_Γ(Frob_q)` with `Frob_q = p(ψ(Frob))` the Frobenius of `q` in `Γ`. -/
theorem localization_eq_frobValue_quotient {Γ : Type} [Group Γ] (p : GKS K S →* Γ)
    (ψ : GUr K q →ₜ* GKS K S) (hψ : ∀ g, locMap K S q g = ψ (urRes K q g))
    (X : TopRep.{0} k (GUr K q)) [ContinuousSMul (GUr K q) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M) (hX : ∀ (h : GUr K q) (x : X.V), f (h • x) = ψ h • f x)
    (cΓ : Γ → M) (hc : Continuous fun σ => cΓ (p σ))
    (hcoc : ∀ a b, cΓ (p (a * b)) = a • cΓ (p b) + cΓ (p a)) (x : X.V)
    (hx : f x = cΓ (p (frobGlobal K S q ψ))) (g : Gloc K q) :
    cΓ (p (locMap K S q g)) = f (urCocycle (eUr K q) X x (urRes K q g)) :=
  localization_eq_frobValue K S q ψ hψ X f hX (fun σ => cΓ (p σ)) hc hcoc x hx g

end Galois


end ZInQ.Contrib.CloudB3RC53.Detecting

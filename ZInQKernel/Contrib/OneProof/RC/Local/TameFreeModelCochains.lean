import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModel
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.RC53Assist.TameBijective.CoordinateInjectivity

/-!
# Lane RC31, round 5: the actual continuous local cochains and the tame free model (4.4)

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306 and 5026–5037.

Setting: a commutative ring `R`, a topological group `G`, an `R`-module `M` with continuous
`G`-action (the hypotheses of `contCochains`), elements `φ σ : G` with the EXACT relation
`φ σ φ⁻¹ = σ ^ q`, `q` odd, `Φ = (φ • ·)`, `g = (σ • ·)`, `g² = 1`, `Φ g = g Φ`.

* PART 1 (PROVED). `relator_expansion`: for every function `c : G → M` with defect
  `w x y = x • c y − c (x y) + c x`,
  `−g w(1,1) − g w(φ,φ⁻¹) + Φ w(σ,φ⁻¹) + w(φ,σφ⁻¹) − Σ_{i=1}^{q−1} w(σ^i,σ)
   = −(g − 1) c(φ) + (Φ − N_q(g)) c(σ)`.
  Hence `tameCochainMap : GHom (natCx (contCochains R G M)) (tameFreeModel Φ g q …)` with
  components `evalZero`, `tameOne = (c(φ), c(σ))`, `tameE` (the left side above), zero
  elsewhere; the chain-map property holds in every degree (`tameOne_d`, `tameE_d`,
  `tameF_comm`).
* PART 2 (PROVED). Naturality in the coefficients for a continuous equivariant `f : M → M'`
  (`evalZero_natural`, `tameOne_natural`, `tameE_natural`; all degrees at once:
  `tameCochainMap_natural`): the model map `modelCoefF f` is `f` in each slot.
  Coefficient change along a ring homomorphism is not treated.
* PART 3 (PROVED). `H⁰`: `tame_H0_iff` (and `tame_H0_iff_local` for the actual local Galois
  group), with `evalZero_injective`, `evalZero_surjective`. `H¹` at `g = 1` over a field:
  the induced map `tameH1 : Z¹ ⧸ d⁰C⁰ → H¹(model)` composed with the model coordinates
  `modelCoordH1` (bijective: `modelCoordH1_injective`, `modelCoordH1_surjective`) is
  `coordQUnr` (`modelCoordH1_comp_tameH1`); hence `tameH1_bijective_of_coordQUnr` and, for the
  actual local Galois group, `tameH1_bijective_local`.
* PART 4 (PRINT). `TameCochainQuasiIso`: `tameCochainMap` is a quasi-isomorphism for the actual
  local Galois group with Iwasawa generators, `M` finite of `2`-power exponent, and wild
  inertia acting trivially.

Kinds: definitions, PROVED, and one PRINT (`TameCochainQuasiIso`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.TameBijective

/-! ### The relator expansion for an arbitrary one-cochain -/

section Relator

variable {R : Type} [CommRing R] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M]

/-- Even powers of an involutive element act trivially (tex 3470–3480). Kind: PROVED. -/
theorem pow_two_mul_smul_of_invol (σ : G) (hσ : ∀ m : M, σ • σ • m = m) (j : ℕ) (m : M) :
    σ ^ (2 * j) • m = m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ, mul_smul, mul_smul, hσ, ih]

/-- Odd powers of an involutive element act as the element (tex 3470–3480). Kind: PROVED. -/
theorem pow_two_mul_add_one_smul_of_invol (σ : G) (hσ : ∀ m : M, σ • σ • m = m) (j : ℕ)
    (m : M) : σ ^ (2 * j + 1) • m = σ • m := by
  rw [pow_succ, mul_smul, pow_two_mul_smul_of_invol σ hσ]

/-- The geometric sum of an involution over an odd range is the tame norm (tex 3472). Kind:
PROVED. -/
theorem sum_range_smul_eq_tameNorm (σ : G) (g : M →ₗ[R] M) (hgσ : ∀ m, g m = σ • m)
    (hg : g ∘ₗ g = LinearMap.id) (q : ℕ) (hq : Odd q) (b : M) :
    ∑ i ∈ Finset.range q, σ ^ i • b = tameNorm q g b := by
  have hσ : ∀ m : M, σ • σ • m = m := fun m => by
    rw [← hgσ, ← hgσ]; exact LinearMap.congr_fun hg m
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  have key : ∀ k : ℕ, ∑ i ∈ Finset.range (2 * k + 1), σ ^ i • b = (k + 1) • b + k • g b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, pow_two_mul_add_one_smul_of_invol σ hσ,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_two_mul_smul_of_invol σ hσ, ← hgσ]
      simp only [add_smul, one_smul]
      abel
  rw [key k, tameNorm, h1, h2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply]

/-- Telescoping along powers: for any `c : G → M` with defect `w x y = x • c y − c (x y) + c x`,
`c(σ^(n+1)) = Σ_{i ≤ n} σ^i • c(σ) − Σ_{1 ≤ i ≤ n} w(σ^i, σ)` (tex 3470–3480). Kind: PROVED. -/
theorem cochain_pow_succ (c : G → M) (w : G → G → M)
    (hw : ∀ x y, w x y = x • c y - c (x * y) + c x) (σ : G) (n : ℕ) :
    c (σ ^ (n + 1)) = ∑ i ∈ Finset.range (n + 1), σ ^ i • c σ -
      ∑ i ∈ Finset.Ico 1 (n + 1), w (σ ^ i) σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := hw (σ ^ (n + 1)) σ
    rw [← pow_succ] at e
    rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega)]
    have e' : c (σ ^ (n + 1 + 1)) = σ ^ (n + 1) • c σ + c (σ ^ (n + 1)) - w (σ ^ (n + 1)) σ := by
      rw [e]; abel
    rw [e', ih]
    abel

/-- **The relator expansion** (tex 3470–3474): for `φ σ φ⁻¹ = σ ^ q` with `q` odd, `g = (σ • ·)`
an involution commuting with `Φ = (φ • ·)`, and any `c : G → M` with defect
`w x y = x • c y − c (x y) + c x` (the coboundary of `c`),
`−g w(1,1) − g w(φ,φ⁻¹) + Φ w(σ,φ⁻¹) + w(φ,σφ⁻¹) − Σ_{i=1}^{q−1} w(σ^i,σ)
  = −(g − 1) c(φ) + (Φ − N_q(g)) c(σ)`. Kind: PROVED. -/
theorem relator_expansion (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (c : G → M) (w : G → G → M)
    (hw : ∀ x y, w x y = x • c y - c (x * y) + c x) :
    -g (w 1 1) - g (w φ φ⁻¹) + Φ (w σ φ⁻¹) + w φ (σ * φ⁻¹) -
        ∑ i ∈ Finset.Ico 1 q, w (σ ^ i) σ =
      -(g (c φ) - c φ) + (Φ (c σ) - tameNorm q g (c σ)) := by
  have hmul : ∀ x y, c (x * y) = x • c y + c x - w x y := fun x y => by rw [hw]; abel
  have h1 : c 1 = w 1 1 := by rw [hw, one_mul, one_smul]; abel
  -- `φ • c(φ⁻¹)`
  have hinv : Φ (c φ⁻¹) = w 1 1 - c φ + w φ φ⁻¹ := by
    have e := hmul φ φ⁻¹
    rw [mul_inv_cancel, h1] at e
    rw [hΦ, e]; abel
  -- the conjugate
  have hconj : c (φ * σ * φ⁻¹) = g (w 1 1 - c φ + w φ φ⁻¹) + Φ (c σ) - Φ (w σ φ⁻¹) + c φ -
      w φ (σ * φ⁻¹) := by
    rw [mul_assoc, hmul φ (σ * φ⁻¹), hmul σ φ⁻¹, ← hinv, ← hgσ, ← hΦ, map_sub, map_add]
    have e : Φ (g (c φ⁻¹)) = g (Φ (c φ⁻¹)) := LinearMap.congr_fun hcomm _
    rw [e]
  -- the power
  obtain ⟨k, hk⟩ := hq
  have hpow : c (σ ^ q) = tameNorm q g (c σ) - ∑ i ∈ Finset.Ico 1 q, w (σ ^ i) σ := by
    have e := cochain_pow_succ c w hw σ (2 * k)
    rw [← hk] at e
    rw [e, sum_range_smul_eq_tameNorm σ g hgσ hg q ⟨k, hk⟩]
  have key := hconj.symm.trans ((congrArg c hrel).trans hpow)
  rw [map_add, map_sub] at key
  rw [← sub_eq_zero]
  have e2 : -g (w 1 1) - g (w φ φ⁻¹) + Φ (w σ φ⁻¹) + w φ (σ * φ⁻¹) -
        ∑ i ∈ Finset.Ico 1 q, w (σ ^ i) σ -
      (-(g (c φ) - c φ) + (Φ (c σ) - tameNorm q g (c σ))) =
      -((g (w 1 1) - g (c φ) + g (w φ φ⁻¹) + Φ (c σ) - Φ (w σ φ⁻¹) + c φ - w φ (σ * φ⁻¹)) -
        (tameNorm q g (c σ) - ∑ i ∈ Finset.Ico 1 q, w (σ ^ i) σ)) := by abel
  rw [e2, sub_eq_zero.mpr key, neg_zero]

end Relator

/-! ### The chain map from the actual continuous cochains -/

section ChainMap

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- The degree-one component `c ↦ (c(φ), c(σ))` (the tame coordinates of tex 3298–3306).
Kind: definition. -/
def tameOne (φ σ : G) : (contCochains R G M).X 1 →ₗ[R] M × M :=
  (evalOne R M φ).prod (evalOne R M σ)

/-- The degree-two component `E(w) = −g w(1,1) − g w(φ,φ⁻¹) + Φ w(σ,φ⁻¹) + w(φ,σφ⁻¹)
− Σ_{i=1}^{q−1} w(σ^i,σ)`, read off from the relator `φ σ φ⁻¹ σ^{−q}` (tex 3470–3474).
Kind: definition. -/
def tameE (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) : (contCochains R G M).X 2 →ₗ[R] M :=
  -(g ∘ₗ evalTwo R M 1 1) - g ∘ₗ evalTwo R M φ φ⁻¹ + Φ ∘ₗ evalTwo R M σ φ⁻¹ +
    evalTwo R M φ (σ * φ⁻¹) - ∑ i ∈ Finset.Ico 1 q, evalTwo R M (σ ^ i) σ

/-- The value of the degree-two component (tex 3470–3480). Kind: PROVED. -/
theorem tameE_apply (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) (w : (contCochains R G M).X 2) :
    tameE Φ g φ σ q w = -g (evalTwo R M 1 1 w) - g (evalTwo R M φ φ⁻¹ w) +
      Φ (evalTwo R M σ φ⁻¹ w) + evalTwo R M φ (σ * φ⁻¹) w -
        ∑ i ∈ Finset.Ico 1 q, evalTwo R M (σ ^ i) σ w := by
  simp only [tameE, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.sum_apply]

/-- The square in degrees `0 → 1` commutes: `(da(φ), da(σ)) = ((Φ − 1)a, (g − 1)a)`
(tex 3470–3474). Kind: PROVED. -/
theorem tameOne_d (Φ g : M →ₗ[R] M) (φ σ : G) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, g m = σ • m) (a : (contCochains R G M).X 0) :
    tameOne φ σ (((contCochains R G M).d 0 1).hom a) =
      freeD0 (Φ - LinearMap.id) (g - LinearMap.id) (evalZero R M a) := by
  change (evalOne R M φ (((contCochains R G M).d 0 1).hom a),
      evalOne R M σ (((contCochains R G M).d 0 1).hom a)) =
    ((Φ - LinearMap.id : M →ₗ[R] M) (evalZero R M a),
      (g - LinearMap.id : M →ₗ[R] M) (evalZero R M a))
  rw [evalOne_d_zero, evalOne_d_zero, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.id_apply, hΦ, hgσ]

/-- **The square in degrees `1 → 2` commutes** (tex 3470–3474): for every continuous
one-cochain `c`, `E(dc) = −(g − 1)c(φ) + (Φ − N_q(g))c(σ) = d¹(c(φ), c(σ))`, given the exact
relation `φ σ φ⁻¹ = σ ^ q`. Kind: PROVED. -/
theorem tameE_d (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (c : (contCochains R G M).X 1) :
    tameE Φ g φ σ q (((contCochains R G M).d 1 2).hom c) =
      freeD1 (g - LinearMap.id) (Φ - tameNorm q g) (tameOne φ σ c) := by
  rw [tameE_apply]
  change _ = -(g - LinearMap.id : M →ₗ[R] M) (evalOne R M φ c) +
    (Φ - tameNorm q g : M →ₗ[R] M) (evalOne R M σ c)
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply]
  exact relator_expansion Φ g φ σ q hq hΦ hgσ hg hcomm hrel (fun x => evalOne R M x c)
    (fun x y => evalTwo R M x y (((contCochains R G M).d 1 2).hom c))
    (fun x y => evalTwo_d c x y)

/-- The components of the comparison map, degree by degree: `evalZero`, `tameOne`, `tameE`,
and zero elsewhere (tex 3470–3480). Kind: definition. -/
def tameF (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) :
    ∀ i : ℤ, natX (contCochains R G M) i →ₗ[R] cx3X (A := R) M (M × M) M i
  | .ofNat 0 => evalZero R M
  | .ofNat 1 => tameOne φ σ
  | .ofNat 2 => tameE Φ g φ σ q
  | _ => 0

/-- The comparison components commute with the differentials in every degree (tex 3470–3480). Kind:
PROVED. -/
theorem tameF_comm (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (i i₁ : ℤ) (h : i + 1 = i₁)
    (x : natX (contCochains R G M) i) :
    tameF Φ g φ σ q i₁ (natD (contCochains R G M) i i₁ h x) =
      (tameFreeModel Φ g q hq hcomm hg).d i i₁ h (tameF Φ g φ σ q i x) := by
  subst h
  rcases i with (_ | _ | _ | n) | n
  · exact tameOne_d Φ g φ σ hΦ hgσ x
  · exact tameE_d Φ g φ σ q hq hΦ hgσ hg hcomm hrel x
  · rfl
  · rfl
  · change tameF Φ g φ σ q (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The comparison chain map** from the actual continuous local cochains
`natCx (contCochains R G M)` to Elliot's tame local free model (4.4) (tex 3470–3480), for
`φ σ φ⁻¹ = σ ^ q` with `q` odd, `Φ = (φ • ·)`, `g = (σ • ·)`, `g² = 1`, `Φ g = g Φ`:
degree `0`: `a ↦ a`; degree `1`: `c ↦ (c(φ), c(σ))`; degree `2`: `tameE`. Kind: definition
(the chain-map property PROVED in every degree, `tameF_comm`). -/
def tameCochainMap (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    GHom (natCx (contCochains R G M)) (tameFreeModel Φ g q hq hcomm hg) where
  f i j h := by subst h; exact tameF Φ g φ σ q i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact tameF_comm Φ g φ σ q hq hΦ hgσ hg hcomm hrel i i₁ h₁ x

end ChainMap

/-! ### Naturality in the coefficients -/

section Naturality

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]
  {M' : Type} [AddCommGroup M'] [Module R M'] [DistribMulAction G M'] [SMulCommClass G R M']
  [TopologicalSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [ContinuousSMul G M']

/-- The map of continuous cochains induced by a continuous `G`-equivariant `R`-linear map
`f : M → M'` (the identity on the group) (tex 3470–3480). Kind: definition. -/
abbrev coefCochainMap (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) :
    contCochains R G M ⟶ contCochains R G M' :=
  contCochainsMap (ContinuousMonoidHom.id G) f hfc hf

/-- Naturality in degree `0` (tex 3470–3480). Kind: PROVED. -/
theorem evalZero_natural (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) (a : (contCochains R G M).X 0) :
    evalZero R M' (((coefCochainMap f hfc hf).f 0).hom a) = f (evalZero R M a) :=
  rfl

/-- Naturality in degree `1`: the model map is `f` in each slot (tex 3470–3480). Kind:
PROVED. -/
theorem tameOne_natural (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) (φ σ : G) (c : (contCochains R G M).X 1) :
    tameOne φ σ (((coefCochainMap f hfc hf).f 1).hom c) = Prod.map f f (tameOne φ σ c) :=
  rfl

/-- Two-cochain values are natural (tex 3470–3480). Kind: PROVED. -/
theorem evalTwo_natural (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) (x y : G) (w : (contCochains R G M).X 2) :
    evalTwo R M' x y (((coefCochainMap f hfc hf).f 2).hom w) = f (evalTwo R M x y w) :=
  rfl

/-- Naturality in degree `2` (tex 3470–3480): `E' ∘ f_* = f ∘ E` for the actions
`Φ = (φ • ·)`, `g = (σ • ·)` on `M` and `Φ'`, `g'` on `M'`. Kind: PROVED. -/
theorem tameE_natural (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) (Φ g : M →ₗ[R] M) (Φ' g' : M' →ₗ[R] M')
    (φ σ : G) (q : ℕ) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m)
    (hΦ' : ∀ m, Φ' m = φ • m) (hgσ' : ∀ m, g' m = σ • m) (w : (contCochains R G M).X 2) :
    tameE Φ' g' φ σ q (((coefCochainMap f hfc hf).f 2).hom w) = f (tameE Φ g φ σ q w) := by
  rw [tameE_apply, tameE_apply]
  simp only [evalTwo_natural, map_sub, map_add, map_neg, map_sum, hΦ, hgσ, hΦ', hgσ', hf]

/-- The coefficient map of the model: `f` in each slot (`f`, `f × f`, `f` in degrees `0, 1, 2`)
(tex 3470–3480). Kind: definition. -/
def modelCoefF (f : M →ₗ[R] M') :
    ∀ i : ℤ, cx3X (A := R) M (M × M) M i →ₗ[R] cx3X (A := R) M' (M' × M') M' i
  | .ofNat 0 => f
  | .ofNat 1 => f.prodMap f
  | .ofNat 2 => f
  | _ => 0

/-- **Naturality of the comparison in every degree** (tex 3470–3480): the square formed by
the cochain map of `f`, the two comparison maps, and the model map `modelCoefF f` commutes,
component by component. Kind: PROVED. -/
theorem tameCochainMap_natural (f : M →ₗ[R] M') (hfc : Continuous f)
    (hf : ∀ (x : G) (m : M), f (x • m) = x • f m) (Φ g : M →ₗ[R] M) (Φ' g' : M' →ₗ[R] M')
    (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m)
    (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hΦ' : ∀ m, Φ' m = φ • m)
    (hgσ' : ∀ m, g' m = σ • m) (hg' : g' ∘ₗ g' = LinearMap.id) (hcomm' : Φ' ∘ₗ g' = g' ∘ₗ Φ')
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (i : ℤ) (x : natX (contCochains R G M) i) :
    (tameCochainMap Φ' g' φ σ q hq hΦ' hgσ' hg' hcomm' hrel).f i i rfl
        ((natHom (coefCochainMap f hfc hf)).f i i rfl x) =
      modelCoefF f i ((tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel).f i i rfl x) := by
  rcases i with (_ | _ | _ | n) | n
  · exact evalZero_natural f hfc hf x
  · exact tameOne_natural f hfc hf φ σ x
  · exact tameE_natural f hfc hf Φ g Φ' g' φ σ q hΦ hgσ hΦ' hgσ' x
  · rfl
  · rfl

end Naturality

/-! ### Degree zero: invariants -/

section DegreeZero

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- A continuous zero-cochain is determined by its value (tex 3470–3480). Kind: PROVED. -/
theorem evalZero_injective : Function.Injective (evalZero R M (G := G)) := by
  intro a b h
  apply Subtype.ext
  funext x
  have hx : x = Fin.elim0 := Subsingleton.elim _ _
  rw [hx]
  exact h

/-- Every element is the value of a (constant) continuous zero-cochain (tex 3470–3480).
Kind: PROVED. -/
theorem evalZero_surjective : Function.Surjective (evalZero R M (G := G)) := fun m =>
  ⟨⟨(fun _ => m : (groupCohomology.inhomogeneousCochains (rep R G M)).X 0),
    mem_contCochain.mpr continuous_const⟩, rfl⟩

/-- A continuous one-cochain is determined by its values (tex 3470–3480). Kind: PROVED. -/
theorem cochain_one_ext (c : (contCochains R G M).X 1) (h : ∀ x, evalOne R M x c = 0) :
    c = 0 := by
  apply Subtype.ext
  funext x
  have hx : x = fun _ => x 0 := by funext i; fin_cases i; rfl
  rw [hx]
  exact h (x 0)

omit [ContinuousAdd M] in
/-- If `G` is topologically generated by `φ`, `σ` and a subgroup `N` acting trivially, an
element fixed by `φ` and `σ` is fixed by `G` (separated coefficients) (tex 3470–3480).
Kind: PROVED. -/
theorem smul_eq_of_generators [T1Space M] (φ σ : G) (N : Subgroup G)
    (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤) (m : M) (hφ : φ • m = m)
    (hσ : σ • m = m) (x : G) : x • m = m := by
  have hS : IsClosed ((MulAction.stabilizer G m : Subgroup G) : Set G) :=
    isClosed_singleton.preimage (continuous_id.smul continuous_const)
  have hle : Subgroup.closure {φ, σ} ⊔ N ≤ MulAction.stabilizer G m := by
    refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro y (rfl | rfl)
      · exact MulAction.mem_stabilizer_iff.mpr hφ
      · exact MulAction.mem_stabilizer_iff.mpr hσ
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mpr (hN y hy m)
  have hcl := Subgroup.topologicalClosure_minimal _ hle hS
  rw [hgen] at hcl
  exact MulAction.mem_stabilizer_iff.mp (hcl (Subgroup.mem_top x))

/-- **Comparison on `H⁰`** (tex 3470–3480): if `G` is topologically generated by `φ`, `σ` and
a subgroup acting trivially, a continuous zero-cochain is a cocycle iff its value is a model
zero-cocycle, i.e. lies in `ker(Φ − 1) ∩ ker(g − 1)`; with `evalZero_injective` and
`evalZero_surjective` the degree-zero component is a bijection of zero-cocycles. Kind:
PROVED. -/
theorem tame_H0_iff [T1Space M] (Φ g : M →ₗ[R] M) (φ σ : G) (hΦ : ∀ m, Φ m = φ • m)
    (hgσ : ∀ m, g m = σ • m) (N : Subgroup G) (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤)
    (a : (contCochains R G M).X 0) :
    ((contCochains R G M).d 0 1).hom a = 0 ↔
      freeD0 (Φ - LinearMap.id) (g - LinearMap.id) (evalZero R M a) = 0 := by
  rw [← tameOne_d Φ g φ σ hΦ hgσ a]
  constructor
  · intro h
    rw [h]
    exact map_zero _
  · intro h
    have h1 : evalOne R M φ (((contCochains R G M).d 0 1).hom a) = 0 := congrArg Prod.fst h
    have h2 : evalOne R M σ (((contCochains R G M).d 0 1).hom a) = 0 := congrArg Prod.snd h
    rw [evalOne_d_zero, sub_eq_zero] at h1 h2
    apply cochain_one_ext
    intro x
    rw [evalOne_d_zero, smul_eq_of_generators φ σ N hN hgen _ h1 h2 x, sub_self]

omit [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M] in
/-- Topological generation by Iwasawa generators: if `G` is topologically generated by `φ` and
`I`, and `I` by `σ` and `P`, then `G` is topologically generated by `φ`, `σ` and `P` (NSW,
Thm 7.5.3) (tex 3470–3480). Kind: PROVED. -/
theorem topologicalClosure_closure_pair_sup (φ σ : G) (I P : Subgroup G)
    (hI : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (hIσ : (Subgroup.zpowers σ ⊔ P).topologicalClosure = I) :
    (Subgroup.closure {φ, σ} ⊔ P).topologicalClosure = ⊤ := by
  set H := Subgroup.closure ({φ, σ} : Set G) ⊔ P
  have hφH : φ ∈ H.topologicalClosure :=
    H.le_topologicalClosure (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
  have hσH : σ ∈ H.topologicalClosure :=
    H.le_topologicalClosure (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
  have hPH : P ≤ H.topologicalClosure :=
    le_sup_right.trans H.le_topologicalClosure
  have hIH : I ≤ H.topologicalClosure := by
    rw [← hIσ]
    exact Subgroup.topologicalClosure_minimal _
      (sup_le (Subgroup.zpowers_le.mpr hσH) hPH) H.isClosed_topologicalClosure
  have hle := Subgroup.topologicalClosure_minimal _
    (sup_le (Subgroup.zpowers_le.mpr hφH) hIH) H.isClosed_topologicalClosure
  rw [hI] at hle
  exact top_le_iff.mp hle

end DegreeZero

/-! ### Degree one at augmentation `g = 1`: comparison with the tame coordinates -/

section DegreeOne

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- The model one-cocycles at `g = 1`: `ker d¹ = {(v, w) | (Φ − N_q(1)) w = 0}` (tex 3474–3480).
Kind: definition. -/
abbrev modelZ1 (Φ : M →ₗ[k] M) (q : ℕ) : Submodule k (M × M) :=
  LinearMap.ker (freeD1 (LinearMap.id - LinearMap.id : M →ₗ[k] M)
    (Φ - tameNorm q (LinearMap.id : M →ₗ[k] M)))

/-- The model one-coboundaries at `g = 1`, inside the model one-cocycles (tex 3474–3480). Kind:
definition. -/
abbrev modelB1 (Φ : M →ₗ[k] M) (q : ℕ) : Submodule k (modelZ1 Φ q) :=
  (LinearMap.range (freeD0 (Φ - LinearMap.id) (LinearMap.id - LinearMap.id : M →ₗ[k] M))).comap
    (modelZ1 Φ q).subtype

/-- The first cohomology of the model at `g = 1` (tex 3474–3480). Kind: definition. -/
abbrev ModelH1 (Φ : M →ₗ[k] M) (q : ℕ) : Type := modelZ1 Φ q ⧸ modelB1 Φ q

/-- The degree-one component of the comparison map on one-cocycles, at `g = 1`
(tex 3470–3480). Kind: definition (cocycles go to model cocycles by `tameE_d`). -/
def tameZ1 (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    Z1K k G M →ₗ[k] modelZ1 Φ q :=
  (tameOne φ σ ∘ₗ (Z1K k G M).subtype).codRestrict (modelZ1 Φ q) fun z => by
    have e := tameE_d Φ LinearMap.id φ σ q hq hΦ (fun m => (hσ m).symm) (LinearMap.id_comp _)
      (by rw [LinearMap.comp_id, LinearMap.id_comp]) hrel (z : (contCochains k G M).X 1)
    have hz : ((contCochains k G M).d 1 2).hom (z : (contCochains k G M).X 1) = 0 := z.2
    rw [hz, map_zero] at e
    exact LinearMap.mem_ker.mpr e.symm

/-- The comparison map on first cohomology at `g = 1`:
`H¹_cont = Z¹ ⧸ d⁰C⁰ → H¹(model)`, induced by `tameCochainMap` (tex 3470–3480). Kind:
definition. -/
def tameH1 (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    H1WrelK k G M →ₗ[k] ModelH1 Φ q :=
  Submodule.mapQ _ _ (tameZ1 Φ φ σ q hq hΦ hσ hrel) (by
    rintro _ ⟨a, rfl⟩
    refine ⟨evalZero k M a, ?_⟩
    exact (tameOne_d Φ LinearMap.id φ σ hΦ (fun m => (hσ m).symm) a).symm)

/-- The model coordinates on model cocycles: `(v, w) ↦ (v mod (Φ − 1)M, w)` (tex 3470–3480). Kind:
definition. -/
def modelCoordZ (Φ : M →ₗ[k] M) (φ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) :
    modelZ1 Φ q →ₗ[k] CokerFrob k M φ × KerFrob k M φ q :=
  ((LinearMap.range (frobSub k M φ 1)).mkQ ∘ₗ LinearMap.fst k M M ∘ₗ (modelZ1 Φ q).subtype).prod
    (LinearMap.codRestrict (KerFrob k M φ q) (LinearMap.snd k M M ∘ₗ (modelZ1 Φ q).subtype)
      fun v => by
        have e : freeD1 (LinearMap.id - LinearMap.id : M →ₗ[k] M)
            (Φ - tameNorm q (LinearMap.id : M →ₗ[k] M)) (v : M × M) = 0 := v.2
        change -(LinearMap.id - LinearMap.id : M →ₗ[k] M) (v : M × M).1 +
          (Φ - tameNorm q (LinearMap.id : M →ₗ[k] M)) (v : M × M).2 = 0 at e
        rw [tameNorm_one q hq, sub_self, LinearMap.zero_apply, neg_zero, zero_add,
          LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΦ] at e
        exact LinearMap.mem_ker.mpr ((frobSub_apply φ (q : k) _).trans e))

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- The model coordinates kill model coboundaries (tex 3470–3480). Kind: PROVED. -/
theorem modelCoordZ_B1 (Φ : M →ₗ[k] M) (φ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) :
    modelB1 Φ q ≤ LinearMap.ker (modelCoordZ Φ φ q hq hΦ) := by
  rintro v ⟨a, ha0⟩
  have ha : freeD0 (Φ - LinearMap.id) (LinearMap.id - LinearMap.id : M →ₗ[k] M) a =
      (v : M × M) := ha0
  refine LinearMap.mem_ker.mpr (Prod.ext ?_ (Subtype.ext ?_))
  · change (Submodule.Quotient.mk (v : M × M).1 : CokerFrob k M φ) = 0
    rw [Submodule.Quotient.mk_eq_zero, ← ha]
    refine ⟨a, ?_⟩
    change _ = (Φ - LinearMap.id : M →ₗ[k] M) a
    rw [frobSub_apply, one_smul, LinearMap.sub_apply, LinearMap.id_apply, hΦ]
  · change (v : M × M).2 = 0
    rw [← ha]
    change (LinearMap.id - LinearMap.id : M →ₗ[k] M) a = 0
    rw [sub_self, LinearMap.zero_apply]

/-- **The model coordinates on `H¹`** at `g = 1`: `H¹(model) → M/(Φ − 1)M × ker(Φ − q)`
(tex 3474–3480). Kind: definition. -/
def modelCoordH1 (Φ : M →ₗ[k] M) (φ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) :
    ModelH1 Φ q →ₗ[k] CokerFrob k M φ × KerFrob k M φ q :=
  (modelB1 Φ q).liftQ (modelCoordZ Φ φ q hq hΦ) (modelCoordZ_B1 Φ φ q hq hΦ)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- The model coordinates on `H¹` are injective (tex 3470–3480). Kind: PROVED. -/
theorem modelCoordH1_injective (Φ : M →ₗ[k] M) (φ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) : Function.Injective (modelCoordH1 Φ φ q hq hΦ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    have h1 : (Submodule.Quotient.mk (v : M × M).1 : CokerFrob k M φ) = 0 :=
      congrArg Prod.fst hx
    have h2 : (v : M × M).2 = 0 :=
      congrArg (fun y : CokerFrob k M φ × KerFrob k M φ q => (y.2 : M)) hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, Prod.ext ?_ ?_⟩
    · change (Φ - LinearMap.id : M →ₗ[k] M) a = (v : M × M).1
      rw [← ha, frobSub_apply, one_smul, LinearMap.sub_apply, LinearMap.id_apply, hΦ]
    · change (LinearMap.id - LinearMap.id : M →ₗ[k] M) a = (v : M × M).2
      rw [h2, sub_self, LinearMap.zero_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M] in
/-- The model coordinates on `H¹` are surjective; with `modelCoordH1_injective`,
`H¹(model) ≅ M/(Φ − 1)M × ker(Φ − q)` at `g = 1` (tex 3474–3480). Kind: PROVED. -/
theorem modelCoordH1_surjective (Φ : M →ₗ[k] M) (φ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) : Function.Surjective (modelCoordH1 Φ φ q hq hΦ) := by
  rintro ⟨c, m⟩
  induction c using Submodule.Quotient.induction_on with
  | H b =>
    have hm : φ • (m : M) - (q : k) • (m : M) = 0 := m.2
    have hz : ((b, (m : M)) : M × M) ∈ modelZ1 Φ q := by
      refine LinearMap.mem_ker.mpr ?_
      change -(LinearMap.id - LinearMap.id : M →ₗ[k] M) b +
        (Φ - tameNorm q (LinearMap.id : M →ₗ[k] M)) (m : M) = 0
      rw [tameNorm_one q hq, sub_self, LinearMap.zero_apply, neg_zero, zero_add,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΦ]
      exact hm
    exact ⟨Submodule.Quotient.mk ⟨(b, (m : M)), hz⟩, rfl⟩

/-- **The comparison on `H¹` is the tame coordinate map** (tex 3298–3306, 5026–5037): the model
coordinates of the map induced by `tameCochainMap` on `H¹` are `coordQUnr`,
`[z] ↦ (z(φ) mod (Φ − 1)M, z(σ))`. Kind: PROVED. -/
theorem modelCoordH1_comp_tameH1 (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    modelCoordH1 Φ φ q hq hΦ ∘ₗ tameH1 Φ φ σ q hq hΦ hσ hrel = coordQUnr φ σ q hσ hrel := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

/-- **Bijectivity on `H¹`** (tex 3298–3306, 5026–5037): if the tame coordinate map `coordQUnr`
is bijective, so is the map induced by `tameCochainMap` on `H¹` at `g = 1`. Kind: PROVED. -/
theorem tameH1_bijective_of_coordQUnr (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hb : Function.Bijective (coordQUnr (k := k) (M := M) φ σ q hσ hrel)) :
    Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel) := by
  have hcomp := modelCoordH1_comp_tameH1 Φ φ σ q hq hΦ hσ hrel
  have hinj := modelCoordH1_injective Φ φ q hq hΦ
  refine ⟨fun x y hxy => hb.1 ?_, fun y => ?_⟩
  · rw [← hcomp, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  · obtain ⟨x, hx⟩ := hb.2 (modelCoordH1 Φ φ q hq hΦ y)
    refine ⟨x, hinj ?_⟩
    rw [← hx, ← hcomp, LinearMap.comp_apply]

end DegreeOne

/-! ### The actual local Galois group -/

section ActualLocal

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {K : Type} [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The comparison map is bijective on `H¹` at a tame place** (tex 3298–3306, 5026–5037,
3470–3480): for the actual local Galois group, with inertia acting trivially (`g = 1`), Iwasawa
generators `φ`, `σ` with the exact relation `φ σ φ⁻¹ = σ ^ q`, `q = |𝓀|` odd, and the hypotheses
of `coordQLocal_bijective`, the map induced by `tameCochainMap` on
`H¹ = Z¹ ⧸ d⁰C⁰ → H¹(model)` is bijective. Kind: PROVED (from `coordQLocal_bijective` and
`coordQLocal_eq_coordQUnr`). -/
theorem tameH1_bijective_local [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    Function.Bijective (tameH1 Φ φ σ (Nat.card 𝓀[K]) hq hΦ (hItriv σ hσI) hrel) := by
  apply tameH1_bijective_of_coordQUnr
  rw [← coordQLocal_eq_coordQUnr hn hβ hβ0 hφ hσI hζ hItriv hnM hrel]
  exact coordQLocal_bijective X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM

omit [PerfectField K] in
/-- **Comparison on `H⁰` for the actual local Galois group** (tex 3470–3480): with `φ` an
arithmetic Frobenius lift, inertia topologically generated by `σ` and a subgroup `P` acting
trivially (NSW, Thm 7.5.3), a continuous zero-cochain is a cocycle iff its value lies in
`ker(Φ − 1) ∩ ker(g − 1)`. Kind: PROVED. -/
theorem tame_H0_iff_local (Φ g : M →ₗ[k] M) (hφ : IsArithFrobeniusLift K φ)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (P : Subgroup (Field.absoluteGaloisGroup K))
    (hP : ∀ x ∈ P, ∀ m : M, x • m = m)
    (hIσ : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K)
    (c : (contCochains k (Field.absoluteGaloisGroup K) M).X 0) :
    ((contCochains k (Field.absoluteGaloisGroup K) M).d 0 1).hom c = 0 ↔
      freeD0 (Φ - LinearMap.id) (g - LinearMap.id) (evalZero k M c) = 0 :=
  tame_H0_iff Φ g φ σ hΦ hgσ P hP (topologicalClosure_closure_pair_sup φ σ _ P
    hφ.topologicalClosure_zpowers_sup_inertiaSubgroup hIσ) c

end ActualLocal

/-! ### The remaining step -/

open TauCeti ValuativeRel in
open ZInQ.Contrib.CloudB3RC53.SelmerDuality in
/-- **The tame comparison is a quasi-isomorphism** (tex 3470–3480; PRINT). For the actual local
Galois group `G_K` of a nonarchimedean local field `K` of odd residue characteristic `p`, with
`q = |𝓀|`, Iwasawa generators `φ` (an arithmetic Frobenius lift) and `σ ∈ I` with the exact
relation `φ σ φ⁻¹ = σ ^ q`, a closed normal pro-`p` subgroup `P ≤ I` (wild inertia) with
`I = closure(⟨σ⟩ P)`, and a finite discrete module `M` of `2`-power exponent on which `P` acts
trivially, `tameCochainMap` is a quasi-isomorphism. Sources: Iwasawa, and
Neukirch–Schmidt–Wingberg, Cohomology of Number Fields, Thm 7.5.3 (structure of the tame
Galois group, splitting of the wild inertia); Serre, Galois Cohomology, I.3.3 (or NSW 1.6.2)
(`H^i(P, M) = 0` for `i > 0`, pro-`p` `P`, `2`-primary `M`); Hochschild–Serre for
`P ⊴ G_K`; and the free resolution of the tame quotient `⟨φ, σ | φ σ φ⁻¹ = σ^q⟩`. Already
PROVED here: degree `0` (`tame_H0_iff` with `evalZero_injective`, `evalZero_surjective`, given
topological generation by `φ`, `σ` and a trivially acting subgroup) and degree `1` at `g = 1`
(`tameH1_bijective_local`). Kind: PRINT. -/
def TameCochainQuasiIso : Prop :=
  ∀ (K : Type) [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [DistribMulAction (Field.absoluteGaloisGroup K) M]
    [SMulCommClass (Field.absoluteGaloisGroup K) R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (Field.absoluteGaloisGroup K) M] [Finite M]
    (φ σ : Field.absoluteGaloisGroup K) (P : Subgroup (Field.absoluteGaloisGroup K))
    (Φ g : M →ₗ[R] M) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m)
    (hg : g ∘ₗ g = LinearMap.id) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q),
    IsArithFrobeniusLift K φ → σ ∈ inertiaSubgroup K → q = Nat.card 𝓀[K] →
    ringChar 𝓀[K] ≠ 2 → P.Normal → IsClosed (P : Set (Field.absoluteGaloisGroup K)) →
    TauCeti.IsProP (ringChar 𝓀[K]) P → P ≤ inertiaSubgroup K →
    (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K →
    (∀ x ∈ P, ∀ m : M, x • m = m) → (∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) →
    QuasiIso (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel))

end ZInQ.Manuscript.RC.Local

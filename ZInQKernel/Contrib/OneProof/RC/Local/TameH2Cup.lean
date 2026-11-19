import ZInQKernel.Contrib.OneProof.RC.Local.TameEulerField
import ZInQKernel.Contrib.OneProof.RC.Local.TameUnramifiedSquare
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.UnramifiedComparison

/-!
# Lane RC31, round 7: surjectivity of the comparison on `H²` by a cup product

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306 and 5026–5037.

For an additive locally constant character `ψ : G → R` and a continuous one-cocycle `c`, the cup
product `w(x, y) = ψ(x) • (x • c(y))` is a continuous two-cocycle (`cupChar`, `cupChar_d`). With
`σ` acting trivially, `ψ(σ) = 1` and `c(σ) = 0`, the relator component is `E(w) = −c(φ)`
(`tameE_cupChar`, `tameE_cupChar_of`), so `tameH2` is surjective as soon as every element is a
Frobenius value of such a cocycle (`tameH2_surjective_of_character`). In the inflation setting
the inflated unramified cocycles supply these (`exists_cocycle_of_unramified`,
`tameH2_surjective_of_unramified`).

The character comes from the Kummer data of the degree-one hypotheses: for `n` even and
`γ = β^{n/2}` (so `γ² ∈ K` and `σ γ = −γ`, `kummer_half_power`), the quadratic Kummer sign
`kummerSign` is additive in characteristic `2` and locally constant (`kummerSign_mul`,
`isLocallyConstant_kummerSign`). Hence `tameH2_surjective_kummer`, and the assemblies
`quasiIso_tameCochainMap_field'` (with an explicit character) and
`quasiIso_tameCochainMap_kummer` (from the Kummer data): for a finite extension of `ℚ_p`,
`p ≠ 2`, and every coefficient field, the tame comparison at `g = 1` is a quasi-isomorphism
from the tree PRINT `MilneADT_I_2_8` alone.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open IntermediateField

/-! ### The cup product with an additive character -/

section Cup

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The cup product of an additive character with a one-cochain** (tex 3470–3480): for a
locally constant `ψ : G → R` and a continuous one-cochain `c`, the continuous two-cochain
`w(x, y) = ψ(x) • (x • c(y))` (continuous because `M` is discrete). Kind: definition. -/
def cupChar (ψ : G → R) (hψlc : IsLocallyConstant ψ) (c : (contCochains R G M).X 1) :
    (contCochains R G M).X 2 :=
  (contSubCx R G M).ofSub ⟨(fun v : Fin 2 → G => ψ (v 0) • (v 0 • evalOne R M (v 1) c) :
    (groupCohomology.inhomogeneousCochains (rep R G M)).X 2), mem_contCochain.mpr
      ((IsLocallyConstant.comp₂ (hψlc.comp_continuous (continuous_apply 0))
        ((IsLocallyConstant.iff_continuous _).mpr ((continuous_apply 0).smul
          ((continuous_evalOne c).comp (continuous_apply 1)))) (fun r m => r • m)).continuous)⟩

/-- The value of the cup product: `w(x, y) = ψ(x) • (x • c(y))` (tex 3470–3480). Kind:
PROVED (definitional). -/
theorem evalTwo_cupChar (ψ : G → R) (hψlc : IsLocallyConstant ψ)
    (c : (contCochains R G M).X 1) (x y : G) :
    evalTwo R M x y (cupChar ψ hψlc c) = ψ x • (x • evalOne R M y c) :=
  rfl

/-- The cocycle relation of a continuous one-cocycle: `c(xy) = x • c(y) + c(x)`
(tex 3470–3480). Kind: PROVED. -/
theorem evalOne_mul_of_cocycle (c : (contCochains R G M).X 1)
    (hc : ((contCochains R G M).d 1 2).hom c = 0) (x y : G) :
    evalOne R M (x * y) c = x • evalOne R M y c + evalOne R M x c := by
  have e := evalTwo_d c x y
  rw [hc, map_zero] at e
  have e2 : evalOne R M (x * y) c - (x • evalOne R M y c + evalOne R M x c) =
      -(x • evalOne R M y c - evalOne R M (x * y) c + evalOne R M x c) := by abel
  rw [← sub_eq_zero, e2, ← e, neg_zero]

/-- **The cup product of an additive character with a one-cocycle is a two-cocycle**
(tex 3470–3480): `x w(y,z) − w(xy,z) + w(x,yz) − w(x,y) = 0`, using `ψ(xy) = ψ(x) + ψ(y)` and
`c(yz) = y • c(z) + c(y)`. Kind: PROVED. -/
theorem cupChar_d (ψ : G → R) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hψlc : IsLocallyConstant ψ) (c : (contCochains R G M).X 1)
    (hc : ((contCochains R G M).d 1 2).hom c = 0) :
    ((contCochains R G M).d 2 3).hom (cupChar ψ hψlc c) = 0 := by
  apply Subtype.ext
  funext v
  have h := contCochains_d_apply (k := R) (G := G) (M := M) 2 (cupChar ψ hψlc c) v
  refine h.trans ?_
  rw [Fin.sum_univ_three]
  change v 0 • (ψ (v 1) • (v 1 • evalOne R M (v 2) c)) +
    ((-1 : R) ^ (0 + 1) • (ψ (v 0 * v 1) • ((v 0 * v 1) • evalOne R M (v 2) c)) +
      (-1 : R) ^ (1 + 1) • (ψ (v 0) • (v 0 • evalOne R M (v 1 * v 2) c)) +
      (-1 : R) ^ (2 + 1) • (ψ (v 0) • (v 0 • evalOne R M (v 1) c))) = 0
  rw [evalOne_mul_of_cocycle c hc, hψ, smul_comm (v 0) (ψ (v 1)), mul_smul, smul_add]
  generalize v 0 • v 1 • evalOne R M (v 2) c = A
  generalize v 0 • evalOne R M (v 1) c = B
  module

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- Powers of an element acting trivially act trivially (tex 3470–3480). Kind: PROVED. -/
theorem pow_smul_of_trivial (σ : G) (hσ : ∀ m : M, σ • m = m) (i : ℕ) (m : M) :
    σ ^ i • m = m := by
  induction i with
  | zero => rw [pow_zero, one_smul]
  | succ i ih => rw [pow_succ, mul_smul, hσ, ih]

/-- **The relator component on a cup product** (tex 3470–3474): with `σ` acting trivially
and `g = 1`, `E(ψ ∪ c) = −ψ(σ) c(φ) + ψ(φ) Φ c(σ) − Σ_{i=1}^{q−1} ψ(σ^i) c(σ)`. Kind:
PROVED. -/
theorem tameE_cupChar (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (ψ : G → R) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hψlc : IsLocallyConstant ψ) (c : (contCochains R G M).X 1)
    (hc : ((contCochains R G M).d 1 2).hom c = 0) :
    tameE Φ LinearMap.id φ σ q (cupChar ψ hψlc c) =
      -(ψ σ • evalOne R M φ c) + ψ φ • Φ (evalOne R M σ c) -
        ∑ i ∈ Finset.Ico 1 q, ψ (σ ^ i) • evalOne R M σ c := by
  have hψ1 : ψ 1 = 0 := by
    have e := hψ 1 1
    rw [one_mul] at e
    exact left_eq_add.mp e
  have hc1 : evalOne R M 1 c = 0 := by
    have e := evalOne_mul_of_cocycle c hc 1 1
    rw [one_mul, one_smul] at e
    exact left_eq_add.mp e
  have hinv : φ • evalOne R M φ⁻¹ c = -evalOne R M φ c := by
    have e := evalOne_mul_of_cocycle c hc φ φ⁻¹
    rw [mul_inv_cancel, hc1] at e
    exact eq_neg_of_add_eq_zero_left e.symm
  have hsf : evalOne R M (σ * φ⁻¹) c = evalOne R M φ⁻¹ c + evalOne R M σ c := by
    rw [evalOne_mul_of_cocycle c hc, hσ]
  have t1 : evalTwo R M 1 1 (cupChar ψ hψlc c) = 0 := by
    rw [evalTwo_cupChar, hψ1, zero_smul]
  have t2 : evalTwo R M φ φ⁻¹ (cupChar ψ hψlc c) = ψ φ • -evalOne R M φ c := by
    rw [evalTwo_cupChar, hinv]
  have t3 : Φ (evalTwo R M σ φ⁻¹ (cupChar ψ hψlc c)) = ψ σ • -evalOne R M φ c := by
    rw [evalTwo_cupChar, hσ, map_smul, hΦ, hinv]
  have t4 : evalTwo R M φ (σ * φ⁻¹) (cupChar ψ hψlc c) =
      ψ φ • (-evalOne R M φ c + Φ (evalOne R M σ c)) := by
    rw [evalTwo_cupChar, hsf, smul_add, hinv, hΦ]
  have t5 : ∀ i : ℕ, evalTwo R M (σ ^ i) σ (cupChar ψ hψlc c) =
      ψ (σ ^ i) • evalOne R M σ c := fun i => by
    rw [evalTwo_cupChar, pow_smul_of_trivial σ hσ]
  rw [tameE_apply, LinearMap.id_apply, LinearMap.id_apply, t1, t2, t3, t4,
    Finset.sum_congr rfl (fun i _ => t5 i)]
  generalize ∑ i ∈ Finset.Ico 1 q, ψ (σ ^ i) • evalOne R M σ c = S
  generalize Φ (evalOne R M σ c) = B
  module

/-- **The relator component on a cup product, normalized case** (tex 3470–3474): if moreover
`ψ(σ) = 1` and `c(σ) = 0`, then `E(ψ ∪ c) = −c(φ)`. Kind: PROVED. -/
theorem tameE_cupChar_of (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (ψ : G → R) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hψlc : IsLocallyConstant ψ) (hψσ : ψ σ = 1) (c : (contCochains R G M).X 1)
    (hc : ((contCochains R G M).d 1 2).hom c = 0) (hcσ : evalOne R M σ c = 0) :
    tameE Φ LinearMap.id φ σ q (cupChar ψ hψlc c) = -evalOne R M φ c := by
  rw [tameE_cupChar Φ φ σ q hΦ hσ ψ hψ hψlc c hc, hcσ, hψσ, one_smul, map_zero, smul_zero]
  simp

/-- **Surjectivity on `H²` from a character** (tex 3470–3480): if `ψ : G → R` is additive,
locally constant, with `ψ(σ) = 1`, and every `a ∈ M` is the value `c(φ)` of a continuous
one-cocycle with `c(σ) = 0`, then `tameH2 : H² → coker(Φ − q)` is surjective
(`[ψ ∪ c] ↦ −c(φ)`). Kind: PROVED. -/
theorem tameH2_surjective_of_character (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (ψ : G → R) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y) (hψlc : IsLocallyConstant ψ)
    (hψσ : ψ σ = 1)
    (hcoc : ∀ a : M, ∃ c : (contCochains R G M).X 1, ((contCochains R G M).d 1 2).hom c = 0 ∧
      evalOne R M φ c = a ∧ evalOne R M σ c = 0) :
    Function.Surjective (tameH2 Φ φ σ q hq hΦ hσ hrel) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨c, hc, hcφ, hcσ⟩ := hcoc (-a)
  refine ⟨Submodule.Quotient.mk ⟨cupChar ψ hψlc c, cupChar_d ψ hψ hψlc c hc⟩, ?_⟩
  change (Submodule.Quotient.mk (tameE Φ LinearMap.id φ σ q (cupChar ψ hψlc c)) :
    M ⧸ LinearMap.range (frobQ Φ q)) = Submodule.Quotient.mk a
  rw [tameE_cupChar_of Φ φ σ q hΦ hσ ψ hψ hψlc hψσ c hc hcσ, hcφ, neg_neg]

end Cup

/-! ### Unramified cocycles -/

section Unramified

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **Frobenius values of inflated unramified cocycles** (tex 3478–3487): for a surjective
equivariant `f : X → M` from a representation of `H ≅ ℤ̂`, inflated along `π : G → H` with
`π φ = Frob` and `π σ = 1`, every `a ∈ M` is `c(φ)` for the continuous one-cocycle
`c = urLin₁ e π X f x` (`f x = a`), and `c(σ) = 0`. Kind: PROVED (from `urLin₁_d`,
`urCocycle_frob`, `urCocycle_one`). -/
theorem exists_cocycle_of_unramified (f : X.V →ₗ[k] M)
    (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x) (hfs : Function.Surjective f)
    (φ σ : G) (hφ : π φ = frobElt e) (hσ1 : π σ = 1) (a : M) :
    ∃ c : (contCochains k G M).X 1, ((contCochains k G M).d 1 2).hom c = 0 ∧
      evalOne k M φ c = a ∧ evalOne k M σ c = 0 := by
  obtain ⟨x, rfl⟩ := hfs a
  refine ⟨urLin₁ e π X f x, ZInQ.Contrib.CloudB3RC53.GenuineInst.urLin₁_d e π X f hf x, ?_, ?_⟩
  · change f (urCocycle e X x (π φ)) = f x
    rw [hφ, urCocycle_frob]
  · change f (urCocycle e X x (π σ)) = 0
    rw [hσ1, urCocycle_one, map_zero]

/-- **Surjectivity on `H²` in the inflation setting** (tex 3470–3487): under the hypotheses of
`exists_cocycle_of_unramified`, with `σ` acting trivially and an additive locally constant
`ψ : G → k` with `ψ(σ) = 1`, `tameH2` is surjective. Kind: PROVED. -/
theorem tameH2_surjective_of_unramified (f : X.V →ₗ[k] M)
    (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x) (hfs : Function.Surjective f)
    (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) (hφ : π φ = frobElt e)
    (hσ1 : π σ = 1) (ψ : G → k) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hψlc : IsLocallyConstant ψ) (hψσ : ψ σ = 1) :
    Function.Surjective (tameH2 Φ φ σ q hq hΦ hσ hrel) :=
  tameH2_surjective_of_character Φ φ σ q hq hΦ hσ hrel ψ hψ hψlc hψσ
    (exists_cocycle_of_unramified e π X f hf hfs φ σ hφ hσ1)

end Unramified

/-! ### The quadratic Kummer character -/

section KummerSign

open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.TameBijective

variable {K : Type} [Field K] {k : Type} [Field k]

open scoped Classical in
/-- **The quadratic Kummer sign** (tex 3470–3487): `ψ(g) = 0` if `g γ = γ` and `1` otherwise,
for `γ` with `γ² ∈ K` (so `g γ = ± γ`). Kind: definition. -/
def kummerSign (k : Type) [Field k] (γ : AlgebraicClosure K) (g : Field.absoluteGaloisGroup K) :
    k :=
  if algebraicGaloisEquiv K g γ = γ then 0 else 1

/-- The sign vanishes on elements fixing `γ` (tex 3470–3487). Kind: PROVED. -/
theorem kummerSign_of_fix {γ : AlgebraicClosure K} {g : Field.absoluteGaloisGroup K}
    (h : algebraicGaloisEquiv K g γ = γ) : kummerSign k γ g = 0 := by
  unfold kummerSign
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

/-- The sign is `1` on elements moving `γ` (tex 3470–3487). Kind: PROVED. -/
theorem kummerSign_of_neg {γ : AlgebraicClosure K} {g : Field.absoluteGaloisGroup K}
    (h : algebraicGaloisEquiv K g γ ≠ γ) : kummerSign k γ g = 1 := by
  unfold kummerSign
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

/-- A Galois element sends a square root `γ` of an element of `K` to `γ` or `−γ`
(tex 3470–3487). Kind: PROVED. -/
theorem apply_eq_or_eq_neg {c : K} {γ : AlgebraicClosure K}
    (hγ : γ ^ 2 = algebraMap K (AlgebraicClosure K) c) (τ : Gal(AlgebraicClosure K/K)) :
    τ γ = γ ∨ τ γ = -γ := by
  have h : (τ γ) ^ 2 = γ ^ 2 := by rw [← map_pow, hγ, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

/-- **The quadratic Kummer sign is additive** in characteristic `2` (tex 3470–3487). Kind:
PROVED. -/
theorem kummerSign_mul (h2k : (2 : k) = 0) {c : K} {γ : AlgebraicClosure K}
    (hγ : γ ^ 2 = algebraMap K (AlgebraicClosure K) c) (hne : -γ ≠ γ)
    (x y : Field.absoluteGaloisGroup K) :
    kummerSign k γ (x * y) = kummerSign k γ x + kummerSign k γ y := by
  have hxy : algebraicGaloisEquiv K (x * y) γ =
      algebraicGaloisEquiv K x (algebraicGaloisEquiv K y γ) := by
    rw [map_mul, AlgEquiv.mul_apply]
  rcases apply_eq_or_eq_neg hγ (algebraicGaloisEquiv K y) with hy | hy
  · rw [kummerSign_of_fix (k := k) hy, add_zero]
    rcases apply_eq_or_eq_neg hγ (algebraicGaloisEquiv K x) with hx | hx
    · rw [kummerSign_of_fix (k := k) (g := x * y) (by rw [hxy, hy, hx]),
        kummerSign_of_fix (k := k) hx]
    · have hx' : algebraicGaloisEquiv K x γ ≠ γ := by rw [hx]; exact hne
      rw [kummerSign_of_neg (k := k) (g := x * y) (by rw [hxy, hy]; exact hx'),
        kummerSign_of_neg (k := k) hx']
  · have hy' : algebraicGaloisEquiv K y γ ≠ γ := by rw [hy]; exact hne
    rw [kummerSign_of_neg (k := k) hy']
    rcases apply_eq_or_eq_neg hγ (algebraicGaloisEquiv K x) with hx | hx
    · rw [kummerSign_of_fix (k := k) hx, zero_add]
      refine kummerSign_of_neg (k := k) ?_
      rw [hxy, hy, map_neg, hx]
      exact hne
    · rw [kummerSign_of_neg (k := k) (show algebraicGaloisEquiv K x γ ≠ γ by rw [hx]; exact hne)]
      rw [kummerSign_of_fix (k := k) (by rw [hxy, hy, map_neg, hx, neg_neg])]
      rw [← h2k]
      norm_num

/-- **The quadratic Kummer sign is locally constant**: it is constant on the cosets of the
open fixing subgroup of `K(γ)` (Krull topology) (tex 3470–3487). Kind: PROVED. -/
theorem isLocallyConstant_kummerSign (h2k : (2 : k) = 0) {c : K} {γ : AlgebraicClosure K}
    (hγ : γ ^ 2 = algebraMap K (AlgebraicClosure K) c) (hne : -γ ≠ γ) :
    IsLocallyConstant (kummerSign k γ) := by
  have : FiniteDimensional K K⟮γ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral γ)
  have hopen := (IntermediateField.fixingSubgroup_isOpen K⟮γ⟯).preimage
    (algebraicGaloisEquiv K).continuous
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun s => x * s) '' ((algebraicGaloisEquiv K) ⁻¹'
    ((K⟮γ⟯).fixingSubgroup : Set Gal(AlgebraicClosure K/K))),
    isOpenMap_mul_left x _ hopen, ⟨1, by
      change algebraicGaloisEquiv K 1 ∈ (K⟮γ⟯).fixingSubgroup
      rw [map_one]
      exact (K⟮γ⟯).fixingSubgroup.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hsγ : algebraicGaloisEquiv K s γ = γ :=
    hs ⟨γ, IntermediateField.mem_adjoin_simple_self K γ⟩
  rw [kummerSign_mul h2k hγ hne, kummerSign_of_fix hsγ, add_zero]


/-- **The tame generator negates the square root** (tex 3470–3487, 5026–5037): if `β^n ∈ K`,
`n` even and `κ(σ) = σ β / β` is a primitive `n`-th root of unity, then `γ = β^{n/2}` satisfies
`γ² ∈ K`, `σ γ = −γ` and `−γ ≠ γ`. Kind: PROVED. -/
theorem kummer_half_power {n : ℕ} [NeZero n] {a : K} {β : AlgebraicClosure K}
    {σ : Field.absoluteGaloisGroup K} (hn2 : 2 ∣ n)
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n) :
    (β ^ (n / 2)) ^ 2 = algebraMap K (AlgebraicClosure K) a ∧
      algebraicGaloisEquiv K σ (β ^ (n / 2)) = -(β ^ (n / 2)) ∧ -(β ^ (n / 2)) ≠ β ^ (n / 2) := by
  set ζ := kummerVal β (algebraicGaloisEquiv K σ)
  have hn0 : n ≠ 0 := NeZero.ne n
  have hhalf : n / 2 * 2 = n := Nat.div_mul_cancel hn2
  have hz1 : ζ ^ (n / 2) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have hz2 : ζ ^ (n / 2) * ζ ^ (n / 2) = 1 := by
    rw [← pow_add, show n / 2 + n / 2 = n by omega, hζ.pow_eq_one]
  have hzneg : ζ ^ (n / 2) = -1 := (mul_self_eq_one_iff.mp hz2).resolve_left hz1
  have hγ0 : β ^ (n / 2) ≠ 0 := pow_ne_zero _ hβ0
  refine ⟨by rw [← pow_mul, hhalf, hβ], ?_, ?_⟩
  · rw [map_pow, apply_eq_kummerVal_mul hβ0, mul_pow, hzneg, neg_one_mul]
  · intro h
    apply hz1
    rw [hzneg]
    have h' : (-1 : AlgebraicClosure K) * β ^ (n / 2) = 1 * β ^ (n / 2) := by
      rw [neg_one_mul, one_mul, h]
    exact mul_right_cancel₀ hγ0 h'
end KummerSign

/-! ### Assembly with a character, for every coefficient field -/

section AssemblyCharacter

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.TameBijective
open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [PerfectField K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison is a quasi-isomorphism, from a character** (tex 3470–3487): for a
nonarchimedean local field `K` that is a finite extension of `ℚ_p`, `p ≠ 2`, any coefficient
field `k`, at `g = 1`, under the hypotheses of `quasiIsoAt_tameCochainMap_one`, `M` of
`2`-power exponent, and an additive locally constant `ψ : G_K → k` with `ψ(σ) = 1`,
`tameCochainMap` is a quasi-isomorphism, given only the tree PRINT `MilneADT_I_2_8`
(degrees `≥ 3` and the order of `H²`). Degree `2` is `tameH2_surjective_of_unramified` with
`card_contH2_eq`; degrees `≤ 1` are `quasiIso_tameCochainMap_of_two_le`. Kind: PROVED (from
the PRINT). -/
theorem quasiIso_tameCochainMap_field' (h28 : MilneADT_I_2_8) (hp : p ≠ 2) [TopologicalSpace k]
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
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0)
    (ψ : Field.absoluteGaloisGroup K → k) (hψ : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hψlc : IsLocallyConstant ψ) (hψσ : ψ σ = 1) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) := by
  have : Finite M := Finite.of_surjective f hfs
  have hσ1 : localUnramifiedProjection K σ = 1 := by
    have h : σ ∈ (localUnramifiedProjection K :
        Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker := by
      rw [localUnramifiedProjection_ker K]
      exact hσI
    exact h
  refine quasiIso_tameCochainMap_of_two_le X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
    hgσ hg hcomm hrel ?_
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    exact quasiIsoAt_tameCochainMap_two_of_surjective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm
      hrel (inertiaSubgroup K) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
      (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel)
      (euler_field p K M h28 hp hexp)
      (tameH2_surjective_of_unramified (maximalUnramifiedGaloisGroupEquivZHat K
        (AlgebraicClosure K)) (localUnramifiedProjection K) X f hf hfs Φ φ σ _ hq hΦ
        (hItriv σ hσI) hrel (localUnramifiedProjection_frob K hφ) hσ1 ψ hψ hψlc hψσ)
  · exact quasiIsoAt_tameCochainMap_of_ge_three Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel i h
      (subsingleton_homology_field p K M h28 hexp i h)

omit [PerfectField K] [Fact (1 < n)] in
/-- **Surjectivity on `H²` from the Kummer data** (tex 3470–3487, 5026–5037): under the
hypotheses of `quasiIsoAt_tameCochainMap_one` with `n` even and `M` of `2`-power exponent,
`tameH2` is surjective. If `2 = 0` in `k`, the quadratic Kummer sign of `γ = β^{n/2}` is an
additive locally constant character with value `1` at `σ` (`kummer_half_power`), and
`tameH2_surjective_of_unramified` applies; otherwise `M = 0`. Kind: PROVED. -/
theorem tameH2_surjective_kummer [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f) (hn2 : 2 ∣ n)
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m) (hq : Odd (Nat.card 𝓀[K]))
    (Φ : M →ₗ[k] M) (hΦ : ∀ m, Φ m = φ • m) (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K])
    (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    Function.Surjective (tameH2 Φ φ σ (Nat.card 𝓀[K]) hq hΦ (hItriv σ hσI) hrel) := by
  by_cases h2k : (2 : k) = 0
  · obtain ⟨hγ, hτ, hne⟩ := kummer_half_power hn2 hβ hβ0 hζ
    have hσ1 : localUnramifiedProjection K σ = 1 := by
      have h : σ ∈ (localUnramifiedProjection K :
          Field.absoluteGaloisGroup K →* UnramifiedGaloisGroup K).ker := by
        rw [localUnramifiedProjection_ker K]
        exact hσI
      exact h
    exact tameH2_surjective_of_unramified (maximalUnramifiedGaloisGroupEquivZHat K
      (AlgebraicClosure K)) (localUnramifiedProjection K) X f hf hfs Φ φ σ _ hq hΦ
      (hItriv σ hσI) hrel (localUnramifiedProjection_frob K hφ) hσ1
      (kummerSign k (β ^ (n / 2))) (kummerSign_mul h2k hγ hne)
      (isLocallyConstant_kummerSign h2k hγ hne)
      (kummerSign_of_neg (by rw [hτ]; exact hne))
  · have hM : ∀ m : M, m = 0 := fun m => by
      have h := two_nsmul_eq_zero_of_field (k := k) hexp m
      rw [← Nat.cast_smul_eq_nsmul k, Nat.cast_ofNat] at h
      exact (smul_eq_zero.mp h).resolve_left h2k
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨0, by rw [map_zero, hM m, Submodule.Quotient.mk_zero]⟩

/-- **The tame comparison is a quasi-isomorphism, without the degree-two print**
(tex 3470–3487): for a nonarchimedean local field `K` that is a finite extension of `ℚ_p`,
`p ≠ 2`, any coefficient field `k`, at `g = 1`, under the hypotheses of
`quasiIsoAt_tameCochainMap_one` with `n` even and `M` of `2`-power exponent, `tameCochainMap`
is a quasi-isomorphism, given only the tree PRINT `MilneADT_I_2_8`. Degree `2` is
`tameH2_surjective_kummer` with `card_contH2_eq` and `euler_field`; degrees `≥ 3` are
`subsingleton_homology_field`; degrees `≤ 1` are `quasiIso_tameCochainMap_of_two_le`. Kind:
PROVED (from the PRINT). -/
theorem quasiIso_tameCochainMap_kummer (h28 : MilneADT_I_2_8) (hp : p ≠ 2) [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K])) (hn2 : 2 ∣ n)
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) (hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) := by
  have : Finite M := Finite.of_surjective f hfs
  refine quasiIso_tameCochainMap_of_two_le X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
    hgσ hg hcomm hrel ?_
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    exact quasiIsoAt_tameCochainMap_two_of_surjective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm
      hrel (inertiaSubgroup K) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
      (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel)
      (euler_field p K M h28 hp hexp)
      (tameH2_surjective_kummer X f hf hfs hn2 hβ hβ0 hφ hσI hζ hItriv hq Φ hΦ hrel hexp)
  · exact quasiIsoAt_tameCochainMap_of_ge_three Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel i h
      (subsingleton_homology_field p K M h28 hexp i h)

end AssemblyCharacter

end ZInQ.Manuscript.RC.Local

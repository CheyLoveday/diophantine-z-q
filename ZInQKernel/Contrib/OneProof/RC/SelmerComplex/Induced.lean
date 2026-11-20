import Mathlib
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Homogeneous
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Corestriction

/-!
# Lane RC26 (round 3): the induced module and Shapiro's lemma on cochains

For a topological group `G`, a subgroup `U ≤ G` of finite index and a discrete `U`-module `M`
(over a commutative ring `k`), the **induced module** is
```text
Ind_U^G M = { f : G → M continuous | f (u y) = u • f y for all u ∈ U, y ∈ G },
```
with `G` acting by right translation, `(g • f)(y) = f (y g)`, and the discrete topology
(Nekovář, *Selmer complexes*, Astérisque 310, 8.1.1; Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, I §5). The finite index makes `Ind_U^G M` a discrete `G`-module: a function in it is
determined by its values on a finite right transversal, at each point of which it is locally
constant.

The cochain-level form of Shapiro's lemma identifies the complex of continuous inhomogeneous
cochains of `G` with values in `Ind_U^G M` with the complex of homogeneous continuous
`U`-equivariant cochains on `G`:
```text
C^•(G, Ind_U^G M) ≅ C^•_hom(U; G, M),
Θ_c(z₀, …, zₙ) = c(z₀⁻¹z₁, …, z_{n−1}⁻¹zₙ)(z₀),
c_Θ(g₁, …, gₙ)(y) = Θ(y, y g₁, y g₁g₂, …, y g₁⋯gₙ).
```

Main declarations:

* `indSub U k M`, `IndMod U k M` (with its `G`-action, discrete topology and
  `ContinuousSMul G (IndMod U k M)` for `U` of finite index);
* `indIso U k M : contCochains k G (IndMod U k M) ≅ homCx k U G M`, with the formulas
  `indIso_hom_apply`, `indIso_inv_apply`.

Openness of `U` is not needed for these statements (only the finite index is used); for a
profinite `G` an open subgroup has finite index.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory Topology Filter

universe u

section IndMod

variable {G : Type u} [Group G] [TopologicalSpace G] (U : Subgroup G) (k : Type u) [CommRing k]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction U M] [SMulCommClass U k M]
  [TopologicalSpace M] [DiscreteTopology M]

/-- **The functions underlying the induced module** (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): the `k`-submodule of `G → M` of continuous functions `f` with
`f (u y) = u • f y` for `u ∈ U`, `y ∈ G`. -/
def indSub : Submodule k (G → M) where
  carrier := {f | Continuous f ∧ ∀ (u : U) (y : G), f ((u : G) * y) = u • f y}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun u y => by
    change a ((u : G) * y) + b ((u : G) * y) = u • (a y + b y)
    rw [ha.2 u y, hb.2 u y, smul_add]⟩
  zero_mem' := ⟨continuous_const, fun u y => by
    change (0 : M) = u • (0 : M)
    rw [smul_zero]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun u y => by
    change c • a ((u : G) * y) = u • (c • a y)
    rw [ha.2 u y, smul_comm u c (a y)]⟩

/-- **The induced module** `Ind_U^G M` (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): continuous functions `f : G → M` with `f (u y) = u • f y`
(`u ∈ U`), as a type synonym of `indSub U k M`; it carries the discrete topology and the action
of `G` by right translation. -/
def IndMod : Type u := indSub U k M

namespace IndMod

/-- The additive group structure of `Ind_U^G M` (pointwise addition of functions). -/
instance instAddCommGroup : AddCommGroup (IndMod U k M) :=
  inferInstanceAs (AddCommGroup (indSub U k M))

/-- The `k`-module structure of `Ind_U^G M` (pointwise scalar multiplication). -/
instance instModule : Module k (IndMod U k M) := inferInstanceAs (Module k (indSub U k M))

/-- An element of the induced module is a function `G → M`. -/
instance instFunLike : FunLike (IndMod U k M) G M where
  coe φ := (show indSub U k M from φ).1
  coe_injective _ _ h := Subtype.ext h

variable {U k M}

/-- Elements of the induced module are equal if they agree as functions on `G`. -/
@[ext]
theorem ext {φ ψ : IndMod U k M} (h : ∀ y, φ y = ψ y) : φ = ψ :=
  DFunLike.ext _ _ h

/-- An element of the induced module is a continuous function on `G`. -/
theorem continuous (φ : IndMod U k M) : Continuous φ :=
  (show indSub U k M from φ).2.1

/-- An element of the induced module is `U`-equivariant: `φ (u y) = u • φ y`. -/
theorem map_mul_left (φ : IndMod U k M) (u : U) (y : G) : φ ((u : G) * y) = u • φ y :=
  (show indSub U k M from φ).2.2 u y

/-- The element of the induced module given by a continuous `U`-equivariant function. -/
def mk (f : G → M) (hf : Continuous f) (he : ∀ (u : U) (y : G), f ((u : G) * y) = u • f y) :
    IndMod U k M :=
  show indSub U k M from ⟨f, hf, he⟩

/-- The element `mk f hf he` of the induced module is the function `f`. -/
@[simp]
theorem mk_apply (f : G → M) (hf : Continuous f)
    (he : ∀ (u : U) (y : G), f ((u : G) * y) = u • f y) (y : G) :
    mk (k := k) f hf he y = f y :=
  rfl

/-- Addition in the induced module is pointwise. -/
@[simp]
theorem add_apply (φ ψ : IndMod U k M) (y : G) : (φ + ψ) y = φ y + ψ y :=
  rfl

/-- The zero of the induced module is the zero function. -/
@[simp]
theorem zero_apply (y : G) : (0 : IndMod U k M) y = 0 :=
  rfl

/-- Scalar multiplication by `k` on the induced module is pointwise. -/
@[simp]
theorem ksmul_apply (r : k) (φ : IndMod U k M) (y : G) : (r • φ) y = r • φ y :=
  rfl

variable (U k M) in
/-- Evaluation at `y : G`, a `k`-linear map `Ind_U^G M → M`. -/
def evalₗ (y : G) : IndMod U k M →ₗ[k] M where
  toFun φ := φ y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation at `y` sends `φ` to `φ y`. -/
@[simp]
theorem evalₗ_apply (y : G) (φ : IndMod U k M) : evalₗ U k M y φ = φ y :=
  rfl

/-- Evaluation commutes with finite sums. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (φ : ι → IndMod U k M) (y : G) :
    (∑ i ∈ s, φ i) y = ∑ i ∈ s, φ i y :=
  map_sum (evalₗ U k M y) φ s

omit [TopologicalSpace G] in
/-- Every point of `G` is `w(y) · ŷ` with `w(y) = y ŷ⁻¹ ∈ U` and `ŷ ∈ T`, for a right
transversal `T`. -/
theorem _root_.ZInQ.Manuscript.RC.SelmerComplex.RightTransversal.uPart_mul_hat
    (R : RightTransversal U) (y : G) : (R.uPart y : G) * R.hat y = y := by
  rw [RightTransversal.coe_uPart, inv_mul_cancel_right]

/-- **Two elements of the induced module agree once they agree on a right transversal**
(by `U`-equivariance, since `y = w(y) ŷ`). -/
theorem eq_of_eq_on_transversal (R : RightTransversal U) {φ ψ : IndMod U k M}
    (h : ∀ t ∈ R.T, φ t = ψ t) : φ = ψ := by
  ext y
  rw [← R.uPart_mul_hat y, map_mul_left, map_mul_left, h _ (R.hat_mem y)]

/-! ### The action of `G` by right translation -/

variable [ContinuousMul G]

/-- `G` acts on the induced module by right translation: `(g • φ)(y) = φ (y g)`. -/
instance instSMul : SMul G (IndMod U k M) where
  smul g φ := mk (fun y => φ (y * g)) ((IndMod.continuous φ).comp (continuous_id.mul continuous_const))
    (fun u y => by
      simp only [mul_assoc]
      exact map_mul_left φ u (y * g))

/-- The action of `g : G` on the induced module is right translation by `g`:
`(g • φ)(y) = φ (y g)`. -/
@[simp]
theorem smul_apply (g : G) (φ : IndMod U k M) (y : G) : (g • φ) y = φ (y * g) :=
  rfl

/-- Right translation is an action of `G` on the induced module. -/
instance instMulAction : MulAction G (IndMod U k M) where
  one_smul φ := ext fun y => by simp
  mul_smul g h φ := ext fun y => by simp [mul_assoc]

/-- Right translation is additive. -/
instance instDistribMulAction : DistribMulAction G (IndMod U k M) where
  smul_zero _ := ext fun _ => rfl
  smul_add _ _ _ := ext fun _ => rfl

/-- Right translation is `k`-linear. -/
instance instSMulCommClass : SMulCommClass G k (IndMod U k M) where
  smul_comm _ _ _ := ext fun _ => rfl

/-! ### Topology -/

/-- The induced module of a discrete module carries the discrete topology. -/
instance instTopologicalSpace : TopologicalSpace (IndMod U k M) := ⊥

/-- The topology of the induced module is discrete. -/
instance instDiscreteTopology : DiscreteTopology (IndMod U k M) := ⟨rfl⟩

/-- A continuous function into a discrete space is locally constant. -/
theorem eventually_eq_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f : X → Y} (hf : Continuous f) (x : X) : ∀ᶠ x' in 𝓝 x, f x' = f x := by
  have h : ∀ᶠ y in 𝓝 (f x), y = f x := by
    rw [nhds_discrete]
    exact Filter.eventually_pure.2 rfl
  exact (hf.tendsto x).eventually h

/-- **Stabilizers are neighbourhoods of `1`** for `U` of finite index: `g • φ = φ` for `g` near
`1`, since `φ` is locally constant at each of the finitely many points of a right transversal
(Neukirch–Schmidt–Wingberg I §5). -/
theorem eventually_smul_eq [U.FiniteIndex] (φ : IndMod U k M) :
    ∀ᶠ g in 𝓝 (1 : G), g • φ = φ := by
  classical
  let R := RightTransversal.ofFiniteIndex U
  have h : ∀ t ∈ R.T, ∀ᶠ g in 𝓝 (1 : G), φ (t * g) = φ t := fun t _ => by
    have := eventually_eq_of_continuous
      ((IndMod.continuous φ).comp
        (show Continuous fun g : G => t * g from continuous_const.mul continuous_id)) (1 : G)
    simpa only [Function.comp_apply, mul_one] using this
  filter_upwards [(Filter.eventually_all_finset R.T).2 h] with g hg
  exact eq_of_eq_on_transversal R fun t ht => by rw [smul_apply]; exact hg t ht

/-- **`Ind_U^G M` is a discrete `G`-module** for `U` of finite index: the action
`G × Ind_U^G M → Ind_U^G M` is continuous (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5). -/
instance continuousSMul [U.FiniteIndex] : ContinuousSMul G (IndMod U k M) := by
  refine ⟨continuous_prod_of_discrete_right.2 fun φ => ?_⟩
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine (continuousAt_const (y := g₀ • φ)).congr ?_
  have ht : Tendsto (fun g : G => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have := ((show Continuous fun g : G => g₀⁻¹ * g from
      continuous_const.mul continuous_id).tendsto g₀)
    rwa [inv_mul_cancel] at this
  filter_upwards [ht.eventually (eventually_smul_eq φ)] with g hg
  conv_rhs => rw [← mul_inv_cancel_left g₀ g, mul_smul, hg]

end IndMod

end IndMod

/-! ### Shapiro's lemma on cochains -/

section Shapiro

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
  (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction U M]
  [SMulCommClass U k M] [TopologicalSpace M] [DiscreteTopology M]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The successive quotients `(z₀⁻¹z₁, …, z_{n−1}⁻¹zₙ)` of `z ∈ G^{n+1}`: the passage from
homogeneous to inhomogeneous coordinates (Neukirch–Schmidt–Wingberg I §2). -/
def quots {n : ℕ} (z : Fin (n + 1) → G) : Fin n → G :=
  fun i => (z i.castSucc)⁻¹ * z i.succ

omit [IsTopologicalGroup G] in
/-- The successive quotients depend continuously on the tuple. -/
theorem continuous_quots [IsTopologicalGroup G] {n : ℕ} :
    Continuous (quots (G := G) (n := n)) :=
  continuous_pi fun _ => ((continuous_apply _).inv).mul (continuous_apply _)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The successive quotients are invariant under diagonal left multiplication by `U`. -/
theorem quots_smul {n : ℕ} (u : U) (z : Fin (n + 1) → G) : quots (u • z) = quots z := by
  funext i
  simp only [quots, Pi.smul_apply, Subgroup.smul_def, smul_eq_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The successive quotients of `(y, y g₁, y g₁g₂, …)` are `(g₁, …, gₙ)`. -/
theorem quots_partialProd {n : ℕ} (y : G) (g : Fin n → G) :
    quots (fun i => y * Fin.partialProd g i) = g := by
  funext i
  simp only [quots, mul_inv_rev, mul_assoc, inv_mul_cancel_left, Fin.partialProd_right_inv]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A tuple is recovered from its first entry and its successive quotients:
`z_i = z₀ · (z₀⁻¹z₁)⋯(z_{i−1}⁻¹z_i)`. -/
theorem mul_partialProd_quots {n : ℕ} (z : Fin (n + 1) → G) :
    (fun i => z 0 * Fin.partialProd (quots z) i) = z := by
  funext i
  exact congrFun (Fin.partialProd_left_inv z) i

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Deleting the `(j+1)`-st entry of `z` contracts the `j`-th and `(j+1)`-st successive quotients. -/
theorem quots_comp_succAbove_succ {n : ℕ} (z : Fin (n + 2) → G) (j : Fin (n + 1)) :
    quots (z ∘ Fin.succAbove j.succ) = Fin.contractNth j (· * ·) (quots z) := by
  funext l
  rw [show quots z = fun i => (z i.castSucc)⁻¹ * z i.succ from rfl,
    RightTransversal.contractNth_inv_mul z j l]
  rfl

variable {U k M}

/-- **Inhomogeneous to homogeneous cochains** (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): for `c : Gⁿ → Ind_U^G M`,
`Θ_c(z₀, …, zₙ) = c(z₀⁻¹z₁, …, z_{n−1}⁻¹zₙ)(z₀)`. -/
def toHomFun {n : ℕ} (c : (Fin n → G) → IndMod U k M) : (Fin (n + 1) → G) → M :=
  fun z => c (quots z) (z 0)

/-- For continuous `c`, the function `Θ_c` is a homogeneous continuous cochain: it is continuous
and `U`-equivariant (since `c(…)` lies in `Ind_U^G M`). -/
theorem toHomFun_mem {n : ℕ} {c : (Fin n → G) → IndMod U k M} (hc : Continuous c) :
    toHomFun c ∈ homCochain k U G M n := by
  refine ⟨?_, fun u z => ?_⟩
  · have h2 : Continuous fun p : IndMod U k M × G => p.1 p.2 :=
      continuous_prod_of_discrete_left.2 fun φ => IndMod.continuous φ
    exact h2.comp ((hc.comp continuous_quots).prodMk (continuous_apply 0))
  · change c (quots (u • z)) ((u : G) * z 0) = u • c (quots z) (z 0)
    rw [quots_smul]
    exact IndMod.map_mul_left _ u (z 0)

/-- **Homogeneous to inhomogeneous cochains** (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): for a homogeneous cochain `Θ`,
`c_Θ(g₁, …, gₙ)(y) = Θ(y, y g₁, y g₁g₂, …, y g₁⋯gₙ)`, an element of `Ind_U^G M` (continuous and
`U`-equivariant in `y`). -/
def ofHomFun {n : ℕ} (Θ : homCochain k U G M n) (g : Fin n → G) : IndMod U k M :=
  IndMod.mk (fun y => Θ.1 (fun i => y * Fin.partialProd g i))
    (Θ.2.1.comp (continuous_pi fun _ => continuous_id.mul continuous_const))
    (fun u y => by
      show Θ.1 (fun i => (u : G) * y * Fin.partialProd g i) =
        u • Θ.1 (fun i => y * Fin.partialProd g i)
      have e : (fun i => (u : G) * y * Fin.partialProd g i) =
          u • (fun i => y * Fin.partialProd g i) := by
        funext i
        simp only [Pi.smul_apply, Subgroup.smul_def, smul_eq_mul, mul_assoc]
      rw [e]
      exact Θ.2.2 u _)

/-- Unfolding `ofHomFun`. -/
theorem ofHomFun_apply {n : ℕ} (Θ : homCochain k U G M n) (g : Fin n → G) (y : G) :
    ofHomFun Θ g y = Θ.1 (fun i => y * Fin.partialProd g i) :=
  rfl

/-- **`c_Θ` is continuous** as a map into the discrete module `Ind_U^G M`, for `U` of finite index:
`c_Θ(g)` is determined by its values at the finitely many points `t` of a right transversal, and
`g ↦ Θ(t, t g₁, …)` is locally constant. -/
theorem continuous_ofHomFun [U.FiniteIndex] {n : ℕ} (Θ : homCochain k U G M n) :
    Continuous (ofHomFun Θ) := by
  classical
  let R := RightTransversal.ofFiniteIndex U
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine (continuousAt_const (y := ofHomFun Θ g₀)).congr ?_
  have h : ∀ t ∈ R.T, ∀ᶠ g in 𝓝 g₀, ofHomFun Θ g t = ofHomFun Θ g₀ t := fun t _ =>
    IndMod.eventually_eq_of_continuous (f := fun g => ofHomFun Θ g t)
      (Θ.2.1.comp (continuous_pi fun i => continuous_const.mul (continuous_partialProd i))) g₀
  filter_upwards [(Filter.eventually_all_finset R.T).2 h] with g hg
  exact (IndMod.eq_of_eq_on_transversal R hg).symm

variable (U k M)

/-- `c ↦ Θ_c` on continuous `n`-cochains, a `k`-linear map
`Cⁿ(G, Ind_U^G M) → Cⁿ_hom(U; G, M)`. -/
def toHomLin (n : ℕ) : contCochain k G (IndMod U k M) n →ₗ[k] homCochain k U G M n where
  toFun c := ⟨toHomFun (asFun k G (IndMod U k M) c.1), toHomFun_mem c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `Θ ↦ c_Θ` on homogeneous `n`-cochains, a `k`-linear map
`Cⁿ_hom(U; G, M) → Cⁿ(G, Ind_U^G M)`. -/
def ofHomLin [U.FiniteIndex] (n : ℕ) :
    homCochain k U G M n →ₗ[k] contCochain k G (IndMod U k M) n where
  toFun Θ := ⟨ofHomFun Θ, continuous_ofHomFun Θ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Shapiro's lemma in degree `n`, on cochains** (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): `c ↦ Θ_c` is a `k`-linear isomorphism
`Cⁿ(G, Ind_U^G M) ≃ Cⁿ_hom(U; G, M)` with inverse `Θ ↦ c_Θ`. -/
def indEquiv [U.FiniteIndex] (n : ℕ) :
    contCochain k G (IndMod U k M) n ≃ₗ[k] homCochain k U G M n :=
  { toHomLin U k M n with
    invFun := ofHomLin U k M n
    left_inv := fun c => by
      refine Subtype.ext ?_
      show ofHomFun (toHomLin U k M n c) = asFun k G (IndMod U k M) c.1
      funext g
      refine IndMod.ext fun y => ?_
      show asFun k G (IndMod U k M) c.1 (quots fun i => y * Fin.partialProd g i)
          (y * Fin.partialProd g 0) = asFun k G (IndMod U k M) c.1 g y
      rw [quots_partialProd, Fin.partialProd_zero, mul_one]
    right_inv := fun Θ => by
      refine Subtype.ext ?_
      funext z
      show Θ.1 (fun i => z 0 * Fin.partialProd (quots z) i) = Θ.1 z
      rw [mul_partialProd_quots] }

variable {U k M}

/-- **`Θ_{dc} = d Θ_c`**: the passage to homogeneous cochains commutes with the differentials.
The leading term `g₀ • c(g₁, …)` of the inhomogeneous differential (with
`(g₀ • φ)(y) = φ(y g₀)`) gives the face `i = 0` of the alternating sum, and the contraction of the
`j`-th and `(j+1)`-st arguments gives the face `j + 1`. -/
theorem toHomFun_d [U.FiniteIndex] (i : ℕ) (c : (contCochains k G (IndMod U k M)).X i)
    (z : Fin (i + 2) → G) :
    toHomFun (asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el
        (((contCochains k G (IndMod U k M)).d i (i + 1)).hom c) :
          contCochain k G (IndMod U k M) (i + 1))) z =
      ∑ j : Fin (i + 2), (-1 : k) ^ (j : ℕ) •
        toHomFun (asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el c :
          contCochain k G (IndMod U k M) i)) (z ∘ Fin.succAbove j) := by
  unfold toHomFun
  rw [contCochains_d_apply, IndMod.add_apply, IndMod.sum_apply, IndMod.smul_apply]
  conv_rhs => rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
    have e : z 0 * quots z 0 = z (Fin.succ 0) := mul_inv_cancel_left _ _
    rw [e]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [IndMod.ksmul_apply, Fin.val_succ, quots_comp_succAbove_succ, Function.comp_apply,
      Fin.succ_succAbove_zero]

variable (U k M)

/-- **Shapiro's lemma on cochains** (Nekovář, *Selmer complexes*, 8.1.1;
Neukirch–Schmidt–Wingberg I §5): for a subgroup `U` of finite index of a topological group `G`
and a discrete `U`-module `M`, the complex of continuous inhomogeneous cochains of `G` with values
in the induced module `Ind_U^G M` is isomorphic to the complex of homogeneous continuous
`U`-equivariant cochains on `G` (`U` acting on `G` by left multiplication), by
`Θ_c(z₀, …, zₙ) = c(z₀⁻¹z₁, …, z_{n−1}⁻¹zₙ)(z₀)` with inverse
`c_Θ(g₁, …, gₙ)(y) = Θ(y, y g₁, …, y g₁⋯gₙ)`. -/
def indIso [U.FiniteIndex] : contCochains k G (IndMod U k M) ≅ homCx k U G M :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (indEquiv U k M n).toModuleIso)
    (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      apply Subtype.ext
      funext z
      show (homEl k U G M (((homCx k U G M).d i (i + 1)).hom
          (homOf k U G M (toHomLin U k M i c)))).1 z =
        toHomFun (asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el
          (((contCochains k G (IndMod U k M)).d i (i + 1)).hom c) :
            contCochain k G (IndMod U k M) (i + 1))) z
      rw [homCx_d_apply', toHomFun_d]
      rfl)

variable {U k M}

/-- **The formula for `indIso`**: `Θ_c(z₀, …, zₙ) = c(z₀⁻¹z₁, …, z_{n−1}⁻¹zₙ)(z₀)`
(Nekovář, *Selmer complexes*, 8.1.1; Neukirch–Schmidt–Wingberg I §5). -/
theorem indIso_hom_apply [U.FiniteIndex] (n : ℕ) (c : (contCochains k G (IndMod U k M)).X n)
    (z : Fin (n + 1) → G) :
    (homEl k U G M (((indIso U k M).hom.f n).hom c)).1 z =
      asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el c :
        contCochain k G (IndMod U k M) n) (fun i => (z i.castSucc)⁻¹ * z i.succ) (z 0) :=
  rfl

/-- **The formula for the inverse of `indIso`**:
`c_Θ(g₁, …, gₙ)(y) = Θ(y, y g₁, y g₁g₂, …, y g₁⋯gₙ) = Θ(y · Fin.partialProd g)`
(Nekovář, *Selmer complexes*, 8.1.1; Neukirch–Schmidt–Wingberg I §5). -/
theorem indIso_inv_apply [U.FiniteIndex] (n : ℕ) (Θ : (homCx k U G M).X n) (g : Fin n → G)
    (y : G) :
    asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el (((indIso U k M).inv.f n).hom Θ) :
      contCochain k G (IndMod U k M) n) g y =
      (homEl k U G M Θ).1 (fun i => y * Fin.partialProd g i) :=
  rfl

variable (U k M) in
/-- **Shapiro's lemma on cohomology**: `Hⁿ_cont(G, Ind_U^G M)` is the `n`-th cohomology of the
complex of homogeneous continuous `U`-equivariant cochains on `G` (Nekovář, *Selmer complexes*,
8.1.1; Neukirch–Schmidt–Wingberg I §5), induced by `indIso`. -/
def indCohomologyIso [U.FiniteIndex] (n : ℕ) :
    contCohomology k G (IndMod U k M) n ≅ (homCx k U G M).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (indIso U k M)

end Shapiro

end ZInQ.Manuscript.RC.SelmerComplex

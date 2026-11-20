import ZInQKernel.Contrib.OneProof.RC.CoefModules.Torsion
import ZInQKernel.Contrib.CloudB3RC53.Duality.ConjugateWeil

/-!
# Lane RC28 (coefficient modules), part 4: the actual coefficient modules `M_i`

Manuscript `diophantine_zq.tex` (11/5), tex 2724–2727:

> `A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`,

and tex 2790–2796 (`α_i = χ_hΨ_i`; the coefficient ring `R_i = A_i`; the Galois action does not
act on `R_i`).

* `CoefMod A α T`: for a ring `A`, a group `G` acting on an abelian group `T` and a character
  `α : G → Aˣ`, the module `(A ⊗_ℤ T)(α)`: `A`-module `A ⊗_ℤ T`, with `g` acting by
  `α(g) · (id ⊗ g)` (the other group's `baseChangeAct`); discrete topology. Instances:
  `DistribMulAction G`, `SMulCommClass G A`, `DiscreteTopology`, `ContinuousAdd`,
  `ContinuousSMul G` (when `α` has open kernel and `T` has open stabilizers), `Finite`.
* `CharMod A χ`: the free rank-one module `A(χ)`: `A` with `g` acting by multiplication by
  `χ(g)` (used for `A_i(1)`, tex 2800).
* **`Mcoef K S W i α`: the actual coefficient module `M_i = (E[2^i] ⊗ A_i)(α_i)`** over the
  genuine `G_{K,S}`, with `E[2^i] = TorsS K S W (2^i)` the `2^i`-torsion of `W = E_K` over `K_S`
  (`T_2E ⊗ A_i = E[2^i] ⊗ A_i` since `2^iA_i = 0`; with `FullTorsion` this is the whole
  `E[2^i]`), and `α = α_i` (e.g. `alphaChar i χ_h ξ`). It is a finite discrete `A_i[G_{K,S}]`-module
  with continuous action: exactly the instance arguments of lane RC26's `galoisSelData` and of
  its Nekovář PRINTs.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain TensorProduct ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)

/-- A group acting on a type **with open stabilizers** (a discrete `G`-set with continuous
action). -/
class HasOpenStabilizers (G T : Type) [Group G] [TopologicalSpace G] [MulAction G T] : Prop where
  isOpen_stabilizer : ∀ t : T, IsOpen (MulAction.stabilizer G t : Set G)

instance hasOpenStabilizers_torsS (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) (N : ℤ) :
    HasOpenStabilizers (GKS K S) (TorsS K S W N) :=
  ⟨isOpen_stabilizer_torsS⟩

/-! ### Base change `A ⊗_ℤ T` twisted by a character -/

section CoefMod

variable {G : Type} [Group G] (A : Type) [CommRing A] (α : G →* Aˣ) (T : Type) [AddCommGroup T]
  [DistribMulAction G T]

/-- **`(A ⊗_ℤ T)(α)`**: the `A`-module `A ⊗_ℤ T` on which `g ∈ G` acts by `α(g) · (id ⊗ g)`. -/
@[nolint unusedArguments]
def CoefMod {G : Type} [Group G] (A : Type) [CommRing A] (_α : G →* Aˣ) (T : Type)
    [AddCommGroup T] : Type :=
  A ⊗[ℤ] T

instance : AddCommGroup (CoefMod A α T) := inferInstanceAs (AddCommGroup (A ⊗[ℤ] T))

instance : Module A (CoefMod A α T) := inferInstanceAs (Module A (A ⊗[ℤ] T))

/-- The identification of `CoefMod A α T` with `A ⊗_ℤ T` (the identity). -/
def CoefMod.equiv : (A ⊗[ℤ] T) ≃ₗ[A] CoefMod A α T := LinearEquiv.refl A _

/-- The `A`-linear action of `g`: `α(g) · (id ⊗ g)`. -/
def CoefMod.act (g : G) : CoefMod A α T →ₗ[A] CoefMod A α T :=
  ((α g : Aˣ) : A) • (baseChangeAct A T g : (A ⊗[ℤ] T) →ₗ[A] (A ⊗[ℤ] T))

theorem CoefMod.act_apply (g : G) (x : CoefMod A α T) :
    CoefMod.act A α T g x = ((α g : Aˣ) : A) • (baseChangeAct A T g (x : A ⊗[ℤ] T)) := rfl

theorem CoefMod.act_one : CoefMod.act A α T 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [CoefMod.act_apply, map_one, map_one, Units.val_one, one_smul]
  rfl

theorem CoefMod.act_mul (g h : G) :
    CoefMod.act A α T (g * h) = CoefMod.act A α T g ∘ₗ CoefMod.act A α T h := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, CoefMod.act_apply, CoefMod.act_apply, CoefMod.act_apply]
  change ((α (g * h) : Aˣ) : A) • (baseChangeAct A T (g * h)) (x : A ⊗[ℤ] T) =
    ((α g : Aˣ) : A) • (baseChangeAct A T g) (((α h : Aˣ) : A) • (baseChangeAct A T h) x)
  rw [map_smul, smul_smul, map_mul, map_mul, Units.val_mul]
  rfl

instance : DistribMulAction G (CoefMod A α T) where
  smul g x := CoefMod.act A α T g x
  one_smul x := by
    change CoefMod.act A α T 1 x = x
    rw [CoefMod.act_one]; rfl
  mul_smul g h x := by
    change CoefMod.act A α T (g * h) x = CoefMod.act A α T g (CoefMod.act A α T h x)
    rw [CoefMod.act_mul]; rfl
  smul_zero g := map_zero (CoefMod.act A α T g)
  smul_add g x y := map_add (CoefMod.act A α T g) x y

theorem CoefMod.smul_def (g : G) (x : CoefMod A α T) : g • x = CoefMod.act A α T g x := rfl

theorem CoefMod.smul_tmul (g : G) (a : A) (t : T) :
    g • ((CoefMod.equiv A α T) (a ⊗ₜ t)) =
      (CoefMod.equiv A α T) ((((α g : Aˣ) : A) * a) ⊗ₜ (g • t)) := by
  rw [CoefMod.smul_def, CoefMod.act_apply]
  change ((α g : Aˣ) : A) • (a ⊗ₜ[ℤ] (g • t)) = (((α g : Aˣ) : A) * a) ⊗ₜ (g • t)
  rw [TensorProduct.smul_tmul', smul_eq_mul]

instance : SMulCommClass G A (CoefMod A α T) where
  smul_comm g a x := by
    change CoefMod.act A α T g (a • x) = a • CoefMod.act A α T g x
    exact map_smul _ a x

instance : TopologicalSpace (CoefMod A α T) := ⊥

instance : DiscreteTopology (CoefMod A α T) := ⟨rfl⟩

instance : ContinuousAdd (CoefMod A α T) := ⟨continuous_of_discreteTopology⟩

/-- Every element of `A ⊗_ℤ T` is fixed by an open subgroup under `id ⊗ g` when stabilizers in `T`
are open. Kind: PROVED. -/
theorem exists_isOpen_baseChange_fix [TopologicalSpace G] [IsTopologicalGroup G]
    [HasOpenStabilizers G T] (x : A ⊗[ℤ] T) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g ∈ U, baseChangeAct A T g x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    refine ⟨MulAction.stabilizer G t, HasOpenStabilizers.isOpen_stabilizer t, fun g hg => ?_⟩
    rw [baseChangeAct_tmul, (MulAction.mem_stabilizer_iff).mp hg]
  | add x y hx hy =>
    obtain ⟨U, hU, hUx⟩ := hx
    obtain ⟨V, hV, hVy⟩ := hy
    refine ⟨U ⊓ V, by rw [Subgroup.coe_inf]; exact hU.inter hV, fun g hg => ?_⟩
    rw [map_add, hUx g hg.1, hVy g hg.2]

/-- **`(A ⊗_ℤ T)(α)` is a discrete `G`-module** (stabilizers open) when `α` has open kernel and
`T` is a discrete `G`-module. Kind: PROVED. -/
instance [TopologicalSpace G] [IsTopologicalGroup G] [HasOpenStabilizers G T] [hα : IsOpenKer α] :
    ContinuousSMul G (CoefMod A α T) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun x => ?_
  obtain ⟨U, hU, hUx⟩ := exists_isOpen_baseChange_fix (G := G) A T (x : A ⊗[ℤ] T)
  refine Subgroup.isOpen_mono (H₁ := U ⊓ α.ker) (fun g hg => ?_)
    (by rw [Subgroup.coe_inf]; exact hU.inter hα.isOpen_ker)
  rw [MulAction.mem_stabilizer_iff, CoefMod.smul_def, CoefMod.act_apply, hUx g hg.1,
    (MonoidHom.mem_ker).mp hg.2, Units.val_one]
  exact one_smul A (show A ⊗[ℤ] T from x)

/-- `A ⊗_ℤ T` is finite for finite `A`, `T` (finitely generated and killed by `|A|`).
Kind: PROVED. -/
theorem finite_tensor [Finite A] [Finite T] : Finite (A ⊗[ℤ] T) := by
  have : Module.Finite ℤ A := Module.Finite.of_finite
  have : Module.Finite ℤ T := Module.Finite.of_finite
  have hfin : Module.Finite ℤ (A ⊗[ℤ] T) := Module.Finite.tensorProduct ℤ A T
  have : AddGroup.FG (A ⊗[ℤ] T) := (Module.Finite.iff_addGroup_fg).mp hfin
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
  have hA : 0 < Nat.card A := Nat.card_pos
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨Nat.card A, hA, ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [show Nat.card A • (a ⊗ₜ[ℤ] t) = (Nat.card A • a) ⊗ₜ[ℤ] t from
      (map_nsmul ((TensorProduct.mk ℤ A T).flip t) _ a).symm, card_nsmul_eq_zero',
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

instance [Finite A] [Finite T] : Finite (CoefMod A α T) := finite_tensor A T

end CoefMod

/-! ### The rank-one module `A(χ)` -/

section CharMod

variable {G : Type} [Group G] (A : Type) [CommRing A] (χ : G →* Aˣ)

/-- **`A(χ)`**: the free rank-one `A`-module on which `g` acts by multiplication by `χ(g)`. -/
@[nolint unusedArguments]
def CharMod {G : Type} [Group G] (A : Type) [CommRing A] (_χ : G →* Aˣ) : Type := A

instance : AddCommGroup (CharMod A χ) := inferInstanceAs (AddCommGroup A)

instance : Module A (CharMod A χ) := inferInstanceAs (Module A A)

/-- The identification `A(χ) ≃ A` (the identity, `A`-linear). -/
def CharMod.equiv : CharMod A χ ≃ₗ[A] A := LinearEquiv.refl A A

instance : DistribMulAction G (CharMod A χ) where
  smul g a := show A from ((χ g : Aˣ) : A) * (show A from a)
  one_smul a := by
    change ((χ 1 : Aˣ) : A) * (show A from a) = a
    rw [map_one, Units.val_one, one_mul]
  mul_smul g h a := by
    change ((χ (g * h) : Aˣ) : A) * (show A from a) =
      ((χ g : Aˣ) : A) * (((χ h : Aˣ) : A) * (show A from a))
    rw [map_mul, Units.val_mul, mul_assoc]
  smul_zero g := mul_zero (((χ g : Aˣ) : A))
  smul_add g a b := mul_add (((χ g : Aˣ) : A)) (show A from a) (show A from b)

theorem CharMod.smul_def (g : G) (a : CharMod A χ) :
    CharMod.equiv A χ (g • a) = ((χ g : Aˣ) : A) * CharMod.equiv A χ a := rfl

instance : SMulCommClass G A (CharMod A χ) where
  smul_comm g a b := by
    change ((χ g : Aˣ) : A) * (a * (show A from b)) = a * (((χ g : Aˣ) : A) * (show A from b))
    ring

instance : TopologicalSpace (CharMod A χ) := ⊥

instance : DiscreteTopology (CharMod A χ) := ⟨rfl⟩

instance : ContinuousAdd (CharMod A χ) := ⟨continuous_of_discreteTopology⟩

instance [TopologicalSpace G] [IsTopologicalGroup G] [hχ : IsOpenKer χ] :
    ContinuousSMul G (CharMod A χ) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun a => ?_
  refine Subgroup.isOpen_mono (H₁ := χ.ker) (fun g hg => ?_) hχ.isOpen_ker
  rw [MulAction.mem_stabilizer_iff]
  change ((χ g : Aˣ) : A) * (show A from a) = a
  rw [(MonoidHom.mem_ker).mp hg, Units.val_one, one_mul]

instance [Finite A] : Finite (CharMod A χ) := inferInstanceAs (Finite A)

end CharMod

/-! ### The actual coefficient module `M_i` -/

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **The actual coefficient module `M_i = (T_2E ⊗ A_i)(α) = (E[2^i] ⊗ A_i)(α)`** (tex 2726) over
the genuine `G_{K,S}`: `E[2^i]` is the `2^i`-torsion of `W = E_K` over `K_S` (`TorsS`), `A_i` lane
RC10's `Acoef i`, `α` a character `G_{K,S} → A_i^×` (the text's `α_i = χ_hΨ_i`, `alphaChar`). -/
abbrev Mcoef (W : WeierstrassCurve K) (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) : Type :=
  CoefMod (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))

/-- **`M_i` is finite** (for `W` elliptic). Kind: PROVED. -/
instance mcoef_finite (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) :
    Finite (Mcoef K S W i α) := by
  have : Finite (TorsS K S W ((2 ^ i : ℕ) : ℤ)) :=
    finite_torsS (by exact_mod_cast (pow_ne_zero i two_ne_zero : (2 : ℕ) ^ i ≠ 0))
  exact inferInstanceAs (Finite (CoefMod (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ))))

/-- The instance arguments of lane RC26's `galoisSelData` and Nekovář PRINTs at `M_i`
(non-vacuity of the instance requirements). -/
example (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ)
    [IsOpenKer α] :
    ContinuousSMul (GKS K S) (Mcoef K S W i α) ∧ DiscreteTopology (Mcoef K S W i α) ∧
      Finite (Mcoef K S W i α) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end ZInQ.Manuscript.RC.CoefModules

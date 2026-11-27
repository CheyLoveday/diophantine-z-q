import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil

/-!
# Lane RC28 (coefficient modules), part 9: the dual module `M^*(1) = Hom_A(M, A(1))` and
`M_i(α⁻¹) ≃ M_i^*(1)`

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-conjugate-duality`, tex 2765 and 2805:
"`τ^*M_i ≃ M_i^*(1)`", with `M_i^*(1) = Hom_{R_i}(M_i, R_i(1))`.

* `DualMod G A M T`: `Hom_A(M, T)` with the contragredient action `(g f)(m) = g • f(g⁻¹ m)`; a
  discrete `G`-module (finite, continuous action) when `M` and `T` are;
* `weilDual`: `w ↦ e(·, w)`, the map `M(α⁻¹) → Hom_A(M(α), A(1))` from the Weil pairing;
  **`weilDual_smul`** (`G_{K,S}`-equivariant) and **`weilDualEquiv`** (an `A`-linear bijection
  under `FullTorsion`): `M(α⁻¹) ≃ M(α)^*(1)` **as discrete `G_{K,S}`-modules**.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex (GKS)

section DualMod

variable (G : Type) [Group G] (A : Type) [CommRing A] (M T : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction G M] [SMulCommClass G A M] [AddCommGroup T] [Module A T]
  [DistribMulAction G T] [SMulCommClass G A T]

/-- **`Hom_A(M, T)`** with the contragredient action of `G`. -/
@[nolint unusedArguments]
def DualMod (G : Type) [Group G] (A : Type) [CommRing A] (M T : Type) [AddCommGroup M]
    [Module A M] [AddCommGroup T] [Module A T] : Type :=
  M →ₗ[A] T

instance : AddCommGroup (DualMod G A M T) := inferInstanceAs (AddCommGroup (M →ₗ[A] T))

instance : Module A (DualMod G A M T) := inferInstanceAs (Module A (M →ₗ[A] T))

/-- `g` acting `A`-linearly. -/
def actLin {V : Type} [AddCommGroup V] [Module A V] [DistribMulAction G V] [SMulCommClass G A V]
    (g : G) : V →ₗ[A] V where
  toFun v := g • v
  map_add' := smul_add g
  map_smul' c v := smul_comm g c v

variable {G A M T}

/-- `(g f)(m) = g • f(g⁻¹ • m)`. -/
def DualMod.act (g : G) (f : DualMod G A M T) : DualMod G A M T :=
  show M →ₗ[A] T from actLin G A g ∘ₗ (show M →ₗ[A] T from f) ∘ₗ actLin G A g⁻¹

theorem DualMod.act_apply (g : G) (f : DualMod G A M T) (m : M) :
    (show M →ₗ[A] T from DualMod.act g f) m = g • (show M →ₗ[A] T from f) (g⁻¹ • m) := rfl

instance : DistribMulAction G (DualMod G A M T) where
  smul := DualMod.act
  one_smul f := by
    refine LinearMap.ext fun m => ?_
    change (1 : G) • (show M →ₗ[A] T from f) ((1 : G)⁻¹ • m) = (show M →ₗ[A] T from f) m
    rw [inv_one, one_smul, one_smul]
  mul_smul g h f := by
    refine LinearMap.ext fun m => ?_
    change (g * h) • (show M →ₗ[A] T from f) ((g * h)⁻¹ • m) =
      g • (h • (show M →ₗ[A] T from f) (h⁻¹ • (g⁻¹ • m)))
    rw [mul_inv_rev, mul_smul, mul_smul]
  smul_zero g := by
    refine LinearMap.ext fun m => ?_
    change g • (0 : M →ₗ[A] T) (g⁻¹ • m) = 0
    rw [LinearMap.zero_apply, smul_zero]
  smul_add g f f' := by
    refine LinearMap.ext fun m => ?_
    change g • ((show M →ₗ[A] T from f) + (show M →ₗ[A] T from f')) (g⁻¹ • m) =
      g • (show M →ₗ[A] T from f) (g⁻¹ • m) + g • (show M →ₗ[A] T from f') (g⁻¹ • m)
    rw [LinearMap.add_apply, smul_add]

theorem DualMod.smul_apply (g : G) (f : DualMod G A M T) (m : M) :
    (show M →ₗ[A] T from g • f) m = g • (show M →ₗ[A] T from f) (g⁻¹ • m) := rfl

instance : SMulCommClass G A (DualMod G A M T) where
  smul_comm g a f := by
    refine LinearMap.ext fun m => ?_
    change g • (a • (show M →ₗ[A] T from f)) (g⁻¹ • m) = a • (g • (show M →ₗ[A] T from f) (g⁻¹ • m))
    rw [LinearMap.smul_apply, smul_comm]

instance : TopologicalSpace (DualMod G A M T) := ⊥

instance : DiscreteTopology (DualMod G A M T) := ⟨rfl⟩

instance : ContinuousAdd (DualMod G A M T) := ⟨continuous_of_discreteTopology⟩

instance [Finite M] [Finite T] : Finite (DualMod G A M T) :=
  have : Finite (M →ₗ[A] T) :=
    Finite.of_injective (fun f : M →ₗ[A] T => (f : M → T)) DFunLike.coe_injective
  inferInstanceAs (Finite (M →ₗ[A] T))

/-- An open subgroup acting trivially on a finite discrete `G`-module. -/
theorem exists_isOpen_fix [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V]
    [DistribMulAction G V] [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul G V]
    [Finite V] : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g ∈ U, ∀ v : V, g • v = v := by
  refine ⟨⨅ v : V, MulAction.stabilizer G v, ?_, fun g hg v => ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun v =>
      continuousSMul_iff_stabilizer_isOpen.mp inferInstance v
  · exact (MulAction.mem_stabilizer_iff).mp (Subgroup.mem_iInf.mp hg v)

/-- **`Hom_A(M, T)` is a discrete `G`-module** for finite discrete `M`, `T`. Kind: PROVED. -/
instance [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul G M] [Finite M] [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T]
    [Finite T] : ContinuousSMul G (DualMod G A M T) := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun f => ?_
  obtain ⟨U, hU, hUM⟩ := exists_isOpen_fix (G := G) M
  obtain ⟨V, hV, hVT⟩ := exists_isOpen_fix (G := G) T
  refine Subgroup.isOpen_mono (H₁ := U ⊓ V) (fun g hg => ?_)
    (by rw [Subgroup.coe_inf]; exact hU.inter hV)
  rw [MulAction.mem_stabilizer_iff]
  refine LinearMap.ext fun m => ?_
  change g • (show M →ₗ[A] T from f) (g⁻¹ • m) = (show M →ₗ[A] T from f) m
  rw [hUM g⁻¹ (inv_mem hg.1) m, hVT g hg.2]

end DualMod

/-! ### `M(α⁻¹) ≃ M(α)^*(1)` from the Weil pairing -/

section WeilDual

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A] (α : GKS K S →* Aˣ)

/-- The dual module `M(α)^*(1) = Hom_A(M(α), A(1))`. -/
abbrev DualM : Type :=
  DualMod (GKS K S) A (CoefMod A α (TorsS K S W N)) (Tate1 A hμ)

/-- **`w ↦ e(·, w)`**, `M(α⁻¹) → M(α)^*(1)`. -/
def weilDual : CoefMod A (charInv α) (TorsS K S W N) →ₗ[A] DualM W hμ A α :=
  (weilPairingM W hμ A α).flip

theorem weilDual_apply (w : CoefMod A (charInv α) (TorsS K S W N))
    (v : CoefMod A α (TorsS K S W N)) :
    (show CoefMod A α (TorsS K S W N) →ₗ[A] Tate1 A hμ from weilDual W hμ A α w) v =
      weilPairingM W hμ A α v w := rfl

/-- **`w ↦ e(·, w)` is `G_{K,S}`-equivariant** (from the equivariance of the Weil pairing).
Kind: PROVED. -/
theorem weilDual_smul (g : GKS K S) (w : CoefMod A (charInv α) (TorsS K S W N)) :
    weilDual W hμ A α (g • w) = g • weilDual W hμ A α w := by
  refine LinearMap.ext fun v => ?_
  change weilPairingM W hμ A α v (g • w) = g • weilPairingM W hμ A α (g⁻¹ • v) w
  rw [← weilPairingM_smul, smul_inv_smul]

/-- **`M(α⁻¹) ≃ M(α)^*(1)` as discrete `G_{K,S}`-modules** (`A`-linear, `G_{K,S}`-equivariant
bijection), under `FullTorsion`. Kind: PROVED. -/
def weilDualEquiv (hW : FullTorsion K S W N) :
    CoefMod A (charInv α) (TorsS K S W N) ≃ₗ[A] DualM W hμ A α :=
  LinearEquiv.ofBijective (weilDual W hμ A α) (weilPairingM_flip_bijective W hμ A α hW)

theorem weilDualEquiv_smul (hW : FullTorsion K S W N) (g : GKS K S)
    (w : CoefMod A (charInv α) (TorsS K S W N)) :
    weilDualEquiv W hμ A α hW (g • w) = g • weilDualEquiv W hμ A α hW w :=
  weilDual_smul W hμ A α g w

end WeilDual

end ZInQ.Manuscript.RC.CoefModules

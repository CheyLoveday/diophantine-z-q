import ZInQKernel.Contrib.CloudB3E2Norm.H20AmbientS

/-!
# `htors` for the ambient module over a larger support

Manuscript `diophantine_zq.tex`, tex 3251–3270 (the coefficient module `E[2^i] ⊗ A`, `FullTorsion`).

The Shapiro-level identity `H20Assembly.h1_shapiro` (and `hnorm_pres_of_transferK`) takes the
hypothesis `htors`: every `2^i`-torsion element of the ambient module comes from the coefficient
module through `ι`. For the ambient module `ℤ[Δ] ⊗ E(K_{S₁})` of `H20AmbientS` and
`ι = 1 ⊗ incl` this is **proved** here from `FullTorsion` over `S₀`:

* `torsRes` (definition): `E(K_{S₀})[2^i] → E(K_{S₁})[2^i]`; `torsRes_surjective` (PROVED): all the
  `2^i`-torsion of `E(K_{S₁})` is already over `K_{S₀}` (both inject into `E(K̄_v)[2^i]`, which has
  `2^{2i}` points, at any place `v`);
* **`htors_ambientS`** (PROVED): `ℤ[Δ]` is flat, so the `2^i`-torsion of `ℤ[Δ] ⊗ E(K_{S₁})` is
  `ℤ[Δ] ⊗ E(K_{S₁})[2^i]`, the image of `ι`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve

attribute [local instance] ptSAction

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ W (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ)

/-- `E(K_{S₀})[2^i] → E(K_{S₁})[2^i]`. Kind: definition. -/
def torsRes : TorsT S₀ W i →+ TorsT S₁ W i where
  toFun t := ⟨ptMap h01 W (t : PtS K S₀ W), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 t.2,
      map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coe_torsRes (t : TorsT S₀ W i) :
    ((torsRes h01 W i t : TorsT S₁ W i) : PtS K S₁ W) = ptMap h01 W (t : PtS K S₀ W) := rfl

include hFull in
/-- **All the `2^i`-torsion of `E(K_{S₁})` is over `K_{S₀}`** under `FullTorsion` (PROVED; both
inject into `E(K̄_v)[2^i]` at a place `v`, the first bijectively). -/
theorem torsRes_surjective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (torsRes h01 W i) := by
  intro t₁
  have hbij := compTors_bijective W (2 ^ i) hFull v
  obtain ⟨t₀, ht₀⟩ := hbij.2 (compTors (S := S₁) W (2 ^ i) v t₁)
  refine ⟨t₀, compTors_injective (S := S₁) W (2 ^ i) v ?_⟩
  rw [← ht₀]
  apply Subtype.ext
  change compPt (S := S₁) W v (ptMap h01 W (t₀ : PtS K S₀ W)) = compPt (S := S₀) W v t₀
  exact compPt_ptMap h01 W v _

include hFull in
/-- **`htors` for the ambient module over `S₁`** (PROVED): every `2^i`-torsion element of
`ℤ[Δ] ⊗ E(K_{S₁})` is `ι(m)` for some `m` in the coefficient module. -/
theorem htors_ambientS (v : HeightOneSpectrum (𝓞 K)) (x : ambU h1 W Δ)
    (hx : ((2 ^ i : ℕ) : ℤ) • x = 0) :
    ∃ m : shapMod hS W i s hs hs0 π, ambIotaS hS h01 h1 W i s hs hs0 π m = x := by
  set A := MonoidAlgebra ℤ Δ
  let mul : PtS K S₁ W →ₗ[ℤ] PtS K S₁ W :=
    ((2 ^ i : ℕ) : ℤ) • (LinearMap.id : PtS K S₁ W →ₗ[ℤ] PtS K S₁ W)
  have hmul : ∀ y, mul y = ((2 ^ i : ℕ) : ℤ) • y := fun y => by
    simp only [mul, LinearMap.smul_apply, LinearMap.id_apply]
  have hex : Function.Exact (torsIncl K S₁ W i) mul := by
    intro y
    rw [hmul]
    constructor
    · intro hy
      exact ⟨⟨y, AddSubgroup.torsionBy.nsmul_iff.2 hy⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact AddSubgroup.torsionBy.nsmul_iff.1 t.2
  have hex' := Module.Flat.lTensor_exact A hex
  have hlt : ∀ z : A ⊗[ℤ] PtS K S₁ W, LinearMap.lTensor A mul z = ((2 ^ i : ℕ) : ℤ) • z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rw [LinearMap.lTensor_tmul, hmul, TensorProduct.tmul_smul]
    | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂, smul_add]
  have hmx : LinearMap.lTensor A mul (show A ⊗[ℤ] PtS K S₁ W from x) = 0 := by
    rw [hlt]
    exact hx
  obtain ⟨y, hy⟩ := (hex' _).1 hmx
  have hsurj : Function.Surjective (LinearMap.lTensor A (torsRes h01 W i).toIntLinearMap) :=
    LinearMap.lTensor_surjective A (torsRes_surjective h01 W i hFull v)
  obtain ⟨z, rfl⟩ := hsurj y
  refine ⟨z, ?_⟩
  have hcomp : torsInclS h01 W i =
      torsIncl K S₁ W i ∘ₗ (torsRes h01 W i).toIntLinearMap := by
    ext t
    rfl
  change LinearMap.baseChange A (torsInclS h01 W i) (show A ⊗[ℤ] TorsT S₀ W i from z) = x
  rw [hcomp, LinearMap.baseChange_eq_lTensor, LinearMap.lTensor_comp, LinearMap.comp_apply]
  exact hy

end ZInQ.Contrib.CloudB3E2.NormCochain

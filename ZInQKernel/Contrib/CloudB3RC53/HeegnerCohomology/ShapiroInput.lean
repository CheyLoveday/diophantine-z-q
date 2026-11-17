import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Shapiro
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.InterfacesTransfer

/-!
# HeegnerCohomology, part 8: RC10's `ShapiroTransferInput` from the explicit Shapiro map

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3202–3249.  RC10 records as a `PRINT` input (Nekovář, *Selmer complexes*, 8.1.1–8.1.6) the
interface `ZInQ.Manuscript.RC.HeegnerAlgebra.ShapiroTransferInput` (file
`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/InterfacesTransfer.lean`): on classes, the explicit
degree-one transfer (H21) computes Shapiro's isomorphism followed by the coefficient map (H20).

`shapiroTransferInputGenuine` (`PROVED`) constructs it with genuine `H¹ = Z¹/B¹` on both sides, so
the printed input is not needed:

* `shapiro` is the map on `H¹` induced by the explicit Shapiro cochain map into the induced module
  (`TwistedTransfer.Sh`, a section of Shapiro's restriction-and-evaluation map by
  `TwistedTransfer.shapiro_section`, hence inducing the inverse of Shapiro's isomorphism) followed
  by the coefficient map (H20) (`TwistedTransfer.coeff`, equivariant by
  `TwistedTransfer.coeff_equivariant`);
* `computes` is `TwistedTransfer.coeff_shapiro_eq_transfer` in degree one.

Cochains are arbitrary functions, as in RC10's interface; no continuity is involved.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology


namespace TwistedTransfer

open Finset
open ZInQ.Manuscript.RC.HeegnerAlgebra (ShapiroTransferInput cocyclesH cocyclesG T1 Rtw
  coboundary_mem_cocyclesG T1_mem_cocyclesG)

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

/-- RC10's degree-one transfer is the degree-one case of `T`. -/
theorem rc10_T1_eq (b : H → M) (g : G) :
    T1 H ρ θ r hr b g = T H r hr ρ θ 1 (fun x => b (x 0)) (fun _ => g) := by
  rw [T_one]
  rfl

/-- Coboundaries of a group `Γ` acting through `act`: `{g ↦ act g w - w}`. -/
def B1 {Γ : Type*} (act : Γ → Module.End A M) : AddSubgroup (Γ → M) :=
  AddMonoidHom.range
    { toFun := fun w g => act g w - w
      map_zero' := by funext g; simp
      map_add' := fun w w' => by funext g; simp only [map_add, Pi.add_apply]; abel }

/-- The degree-one cochain map "Shapiro, then (H20)", `c ↦ coeff ∘ Sh(c)`, on all cochains. -/
noncomputable def shapiroCoeff1 : (H → M) →+ (G → M) where
  toFun c g := coeff H θ (Sh H r hr ρ 1 (fun x => c (x 0)) (fun _ => g))
  map_zero' := by
    funext g
    simp [coeff_shapiro_eq_transfer, T]
  map_add' c c' := by
    funext g
    simp only [coeff_shapiro_eq_transfer, T, Pi.add_apply, map_add, sum_add_distrib]

theorem shapiroCoeff1_apply (c : H → M) (g : G) :
    shapiroCoeff1 H ρ θ r hr c g = T1 H ρ θ r hr c g := by
  show coeff H θ _ = _
  rw [coeff_shapiro_eq_transfer, rc10_T1_eq]

/-- "Shapiro, then (H20)" sends coboundaries to coboundaries (the weighted sum of `w` is a
primitive). -/
theorem shapiroCoeff1_B1 :
    B1 (A := A) (M := M) (fun x : H => ρ (x : G)) ≤
      (B1 (fun g : G => R H ρ θ g)).comap (shapiroCoeff1 H ρ θ r hr) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨∑ δ : G ⧸ H, R H ρ θ (r δ) w, ?_⟩
  funext g
  have h := (kummer_weighted_sum H r hr ρ θ 1 w w (one_smul _ _)).2 (fun _ => g)
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h ⊢
  rw [shapiroCoeff1_apply, rc10_T1_eq, ← h]

/-- "Shapiro, then (H20)" on cocycles. -/
noncomputable def shapiroCoeffZ : cocyclesH H ρ →+ cocyclesG H ρ θ :=
  AddMonoidHom.codRestrict ((shapiroCoeff1 H ρ θ r hr).comp (cocyclesH H ρ).subtype)
    (cocyclesG H ρ θ) (fun b => by
      have : shapiroCoeff1 H ρ θ r hr b = T1 H ρ θ r hr b := funext (shapiroCoeff1_apply H ρ θ r hr b)
      show shapiroCoeff1 H ρ θ r hr b ∈ cocyclesG H ρ θ
      rw [this]
      exact T1_mem_cocyclesG H ρ θ r hr b b.2)

/-- `H¹(H, M) = Z¹/B¹`. -/
abbrev H1H := cocyclesH H ρ ⧸ (B1 (A := A) (M := M) (fun x : H => ρ (x : G))).addSubgroupOf
  (cocyclesH H ρ)

/-- `H¹(G, M(θ)) = Z¹/B¹`. -/
abbrev H1G := cocyclesG H ρ θ ⧸ (B1 (fun g : G => R H ρ θ g)).addSubgroupOf (cocyclesG H ρ θ)

/-- **RC10's `ShapiroTransferInput`, constructed** (tex 3202–3249), `PROVED`, with genuine
`H¹ = Z¹/B¹` on both sides, the classes the quotient maps, `shapiro` induced by "Shapiro, then
(H20)", and any section `r₀ = r`. -/
noncomputable def shapiroTransferInputGenuine :
    ShapiroTransferInput H ρ θ (H1H H ρ) (H1G H ρ θ) where
  clsH := QuotientAddGroup.mk
  clsG := QuotientAddGroup.mk' _
  shapiro := QuotientAddGroup.map _ _ (shapiroCoeffZ H ρ θ r hr) (fun x hx => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.mem_addSubgroupOf] at hx
    exact shapiroCoeff1_B1 H ρ θ r hr hx)
  clsG_cob w := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨w, rfl⟩
  r₀ := r
  hr₀ := hr
  computes b := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.map_mk]
    congr 1
    apply Subtype.ext
    funext g
    exact (shapiroCoeff1_apply H ρ θ r hr b g).symm

end TwistedTransfer

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

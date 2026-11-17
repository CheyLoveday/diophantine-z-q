import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Shapiro

/-!
# HeegnerCohomology, part 8: RC10's `ShapiroTransferInput` from the explicit Shapiro map

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3202–3249.  RC10 records as a `PRINT` input (Nekovář, *Selmer complexes*, 8.1.1–8.1.6) the
interface `ShapiroTransferInput` (file
`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/InterfacesTransfer.lean`, snapshot commit
79c2699a5): on classes, the explicit degree-one transfer (H21) computes Shapiro's isomorphism
followed by the coefficient map (H20).  It is copied verbatim below (namespace `RC10`, together
with the RC10 definitions it mentions: `Rtw`, `hc`, `hc_mem`, `hH`, `T1`).

`shapiroTransferInputGenuine` (`PROVED`) constructs it, so the printed input is not needed:

* `shapiro` is the map on classes induced by the explicit Shapiro cochain map into the induced
  module (`TwistedTransfer.Sh`, a section of Shapiro's restriction-and-evaluation map by
  `TwistedTransfer.shapiro_section`, hence inducing the inverse of Shapiro's isomorphism) followed
  by the coefficient map (H20) (`TwistedTransfer.coeff`, equivariant by
  `TwistedTransfer.coeff_equivariant`);
* `computes` is `TwistedTransfer.coeff_shapiro_eq_transfer` in degree one.

Classes.  The interface asks for `clsG : (G → M) → H1G` additive on *all* cochains and killing
coboundaries.  We take `H1G = C¹(G, M(θ)) / B¹(G, M(θ))` (cochains modulo coboundaries) and
`clsG` the quotient map; `H¹(G, M(θ)) = Z¹/B¹` is the subgroup of classes of cocycles, and two
cocycles have the same class in `H¹` exactly when they have the same image in `C¹/B¹`.  Likewise
`H1H = C¹(H, M)/B¹(H, M)`.  (A genuine `H¹` cannot receive an additive map defined on all
cochains that restricts to the class map on cocycles unless `Z¹` is a direct summand of `C¹`; the
interface would read more naturally with `clsG` defined on cocycles.  This is recorded in the lane
notes for RC10.)  Cochains here are arbitrary functions, as in RC10's interface; no continuity
is involved.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace RC10

open Finset

section H21

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Verbatim copy of RC10's `Rtw` (snapshot 79c2699a5): `R(g) = θ(g) ρ_T(g)`. -/
def Rtw (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (g : G) : Module.End A M :=
  (θ (QuotientGroup.mk g) : A) • ρ g

/-- Verbatim copy of RC10's `hc`: `h(g,δ) = r_{gδ}⁻¹ g r_δ`. -/
def hc (r : G ⧸ H → G) (g : G) (δ : G ⧸ H) : G := (r (QuotientGroup.mk g * δ))⁻¹ * g * r δ

omit [Fintype (G ⧸ H)] in
/-- Verbatim copy of RC10's `hc_mem`. -/
theorem hc_mem (r : G ⧸ H → G) (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (g : G)
    (δ : G ⧸ H) : hc H r g δ ∈ H := by
  unfold hc
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, hr, hr]
  group

/-- Verbatim copy of RC10's `hH`. -/
def hH (r : G ⧸ H → G) (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ) (g : G) (δ : G ⧸ H) :
    H :=
  ⟨hc H r g δ, hc_mem H r hr g δ⟩

variable (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (r : G ⧸ H → G)
  (hr : ∀ δ, (QuotientGroup.mk (r δ) : G ⧸ H) = δ)

/-- Verbatim copy of RC10's `T1`: `(𝒯_θ b)(g) = ∑_δ θ(r_{gδ}) ρ_T(r_{gδ}) b(h(g,δ))`. -/
def T1 (b : H → M) : G → M :=
  fun g => ∑ δ, Rtw H ρ θ (r (QuotientGroup.mk g * δ)) (b (hH H r hr g δ))

end H21

section Shapiro

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Verbatim copy of RC10's `ShapiroTransferInput` (snapshot 79c2699a5).  `PRINT` there
(Nekovář, Selmer complexes, 8.1.1–8.1.6): for one chosen section `r₀`, the explicit transfer
(H21) of a cocycle represents `shapiro` of its class. -/
structure ShapiroTransferInput (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (H1H H1G : Type*)
    [AddCommGroup H1H] [AddCommGroup H1G] where
  clsH : (H → M) → H1H
  clsG : (G → M) → H1G
  shapiro : H1H →+ H1G
  clsG_add : ∀ c c' : G → M, clsG (c + c') = clsG c + clsG c'
  clsG_cob : ∀ w : M, clsG (fun g => Rtw H ρ θ g w - w) = 0
  r₀ : G ⧸ H → G
  hr₀ : ∀ δ, (QuotientGroup.mk (r₀ δ) : G ⧸ H) = δ
  computes : ∀ b : H → M, (∀ x y : H, b (x * y) = b x + ρ x (b y)) →
    clsG (T1 H ρ θ r₀ hr₀ b) = shapiro (clsH b)

end Shapiro

end RC10

namespace TwistedTransfer

open Finset

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)

/-- RC10's degree-one transfer is the degree-one case of `T`. -/
theorem rc10_T1_eq (b : H → M) (g : G) :
    RC10.T1 H ρ θ r hr b g = T H r hr ρ θ 1 (fun x => b (x 0)) (fun _ => g) := by
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
    shapiroCoeff1 H ρ θ r hr c g = RC10.T1 H ρ θ r hr c g := by
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

/-- **RC10's `ShapiroTransferInput`, constructed** (tex 3202–3249), `PROVED`: with
`H1H = C¹(H, M)/B¹`, `H1G = C¹(G, M(θ))/B¹` (see the module docstring), the classes the
quotient maps, `shapiro` induced by "Shapiro, then (H20)", and any section `r₀`. -/
noncomputable def shapiroTransferInputGenuine :
    RC10.ShapiroTransferInput H ρ θ ((H → M) ⧸ B1 (A := A) (M := M) (fun x : H => ρ (x : G)))
      ((G → M) ⧸ B1 (fun g : G => R H ρ θ g)) where
  clsH := QuotientAddGroup.mk
  clsG := QuotientAddGroup.mk
  shapiro := QuotientAddGroup.map _ _ (shapiroCoeff1 H ρ θ r hr) (shapiroCoeff1_B1 H ρ θ r hr)
  clsG_add c c' := QuotientAddGroup.mk_add _ _ _
  clsG_cob w := (QuotientAddGroup.eq_zero_iff _).mpr ⟨w, rfl⟩
  r₀ := r
  hr₀ := hr
  computes b _ := by
    rw [QuotientAddGroup.map_mk]
    congr 1
    funext g
    rw [shapiroCoeff1_apply]

end TwistedTransfer

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ConeVanishing
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeCoords

/-!
# Genuine instantiations, part 17: the finite-plane coordinates from the plane equation

Manuscript `diophantine_zq.tex`, tex L5027–5037 (the coordinates of `H¹(W_rel) ≃ F_v ⊕ S_v` at the
switch place and the finite plane).

The switching author's plane equation (`SwitchInputs/DerivativeCoords.lean`: the coordinates
`eRAt` from the tame coordinates at `q`, and `range_H1i_eRAt`: the image of `H¹(W₁)` is the side
plane) discharges the hypothesis `hι` of `cone_dims_finite_derived`:

* `exists_finBasis`: for a derivative family switched at `q` with the finite side condition, there
  is a basis `e_j` of `H¹(W₁)` with `eRAt (H¹(i) e_j) = (e_j, 0)` (the finite plane is `F_v ⊕ 0` by
  `finite_side_iff`, and `H¹(i)` is injective by `DerivFamily.quasiFacts`);
* **`cone_dims_finite_switched`**: the generic dimensions `(1, 1)` of the genuine finite-side cone
  over `𝔽₂`, for a derivative family of the genuine local complexes switched at `q` with the
  finite side, with the coordinates `eRAt` — no coordinate hypothesis left.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open scoped Matrix

open Module CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

section Generic

variable {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module (ZMod 2) (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) (ZMod 2) (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, DiscreteTopology (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]
  {q : ι} (φ σ : Gv q) (eM : Mv q ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
  {F : DerivFamily (locCx Gv Mv)} {I : Subgroup (Gv q)}

/-- **A basis of `H¹(W₁)` on the finite plane**: for a family switched at `q` with the finite side,
`eRAt (H¹(i) e_j) = (e_j, 0)`. PROVED. -/
theorem exists_finBasis (hF : SwitchedAt F q (sideOfSet (I : Set (Gv q))))
    (T : TameCoordinates (M := Mv q) I φ σ) :
    ∃ bF : Basis (Fin 2) (ZMod 2) (F.W₁.toCC.homology 1),
      ∀ j, eRAt (fun v n => derivHsr F v n) hF.rel φ σ eM T (H1 F.i (bF j)) =
        (Pi.single j 1, 0) := by
  set ψ := (eRAt (fun v n => derivHsr F v n) hF.rel φ σ eM T).toLinearMap ∘ₗ H1 F.i with hψ
  have hrange : LinearMap.range ψ = finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) := by
    rw [hψ, LinearMap.range_comp]
    exact range_H1i_eRAt φ σ eM hF (fun v n => derivHsr F v n) hF.rel T _
      (finite_side_iff φ σ eM T)
  have hinj : Function.Injective ψ :=
    (eRAt (fun v n => derivHsr F v n) hF.rel φ σ eM T).injective.comp F.quasiFacts.2.1
  have hsnd : ∀ x, (ψ x).2 = 0 := fun x => by
    have : ψ x ∈ finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) := hrange ▸ ⟨x, rfl⟩
    exact mem_finPlane.mp this
  let E := LinearEquiv.ofBijective (LinearMap.fst _ _ _ ∘ₗ ψ) ⟨fun x y h => hinj (by
      refine Prod.ext h ?_
      rw [hsnd x, hsnd y]), fun a => by
      have : ((a, 0) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ∈ LinearMap.range ψ := by
        rw [hrange]; exact mem_finPlane.mpr rfl
      obtain ⟨x, hx⟩ := this
      exact ⟨x, by rw [LinearMap.comp_apply, hx]; rfl⟩⟩
  refine ⟨(Pi.basisFun (ZMod 2) (Fin 2)).map E.symm, fun j => ?_⟩
  have h1 : (ψ ((Pi.basisFun (ZMod 2) (Fin 2)).map E.symm j)).1 = Pi.single j 1 := by
    have := E.apply_symm_apply (Pi.basisFun (ZMod 2) (Fin 2) j)
    rw [Pi.basisFun_apply] at this
    rw [Basis.map_apply, Pi.basisFun_apply]
    exact this
  exact Prod.ext h1 (hsnd _)

end Generic

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- The local groups and coefficients of the genuine local complexes. -/
abbrev genGv : Places K S → Type := fun v => Gloc K v.1

/-- The local coefficients `M` restricted to `G_{K_v}`. -/
abbrev genMv : Places K S → Type := fun v => ResMod (locMap K S v.1) M

variable (F : DerivFamily (galLv (k := ZMod 2) K S M))

open Classical in
/-- The coordinates `eRAt` of a genuine family switched at `q` with the finite side. -/
def switchedER {q : Places K S} {I : Subgroup (Gloc K q.1)}
    (hF : SwitchedAt (Gv := genGv (K := K) (S := S)) (Mv := genMv (K := K) (S := S) (M := M)) F q
      (sideOfSet (I : Set (Gloc K q.1))))
    (φ σ : Gloc K q.1) (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (T : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ) :
    F.Wrel.toCC.homology 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) :=
  eRAt (fun v n => derivHsr F v n) hF.rel φ σ eM T

open Classical in
/-- **The generic dimensions of the genuine finite-side cone over `𝔽₂`, with the switching author's
coordinates** (tex L4835–4906, L5027–5037): for a derivative family of the genuine local
complexes switched at `q` with the finite side (inertia `I`, Frobenius and tame generator `φ, σ`,
tame coordinates `T`), with the coordinates `eRAt`, the duality data, the classes `A, B`, the old
class spanning `H¹(C_F)` with nonzero finite localization, and side and strict agreeing in degree
two: `dim H¹(C_F) = dim H²(C_F) = 1`. The finite-plane coordinates are DERIVED
(`exists_finBasis`). PROVED. -/
theorem cone_dims_finite_switched {q : Places K S} {I : Subgroup (Gloc K q.1)}
    (hF : SwitchedAt (Gv := genGv (K := K) (S := S)) (Mv := genMv (K := K) (S := S) (M := M)) F q
      (sideOfSet (I : Set (Gloc K q.1))))
    (φ σ : Gloc K q.1) (eM : ResMod (locMap K S q.1) M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    (T : TameCoordinates (M := ResMod (locMap K S q.1) M) I φ σ)
    {ε σ' : ZMod 2} {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hε : ε ≠ 0) (hσ : σ' ≠ 0)
    (hJ2 : J * J = 1)
    (Q : SelPairData (derivSwitch F (switchedER F hF φ σ eM T)).Dstr
      (derivSwitch F (switchedER F hF φ σ eM T)).toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[ZMod 2] ZMod 2)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : (derivSwitch F (switchedER F hF φ σ eM T)).SwitchCoordinates Q tr ε σ' J)
    (bR : Basis (Fin 2) (ZMod 2)
      ((selCx (derivSwitch F (switchedER F hF φ σ eM T)).toQuasi.D).toCC.homology 1))
    {v : Fin 2 → ZMod 2} (hv : v ≠ 0)
    (hA : genLam (derivSwitch F (switchedER F hF φ σ eM T)) (bR 0) = (v, 0))
    (hB : genLam (derivSwitch F (switchedER F hF φ σ eM T)) (bR 1) = (0, J *ᵥ v))
    (a : (derivFiniteSES F (switchedER F hF φ σ eM T)).X₂.homology 1)
    (hspan : ∀ y : (derivFiniteSES F (switchedER F hF φ σ eM T)).X₂.homology 1,
      ∃ c : ZMod 2, y = c • a)
    (ha : (HomologicalComplex.homologyMap (derivFiniteSES F (switchedER F hF φ σ eM T)).g 1).hom a
      ≠ 0)
    (hside2 : ∀ w, (F.side w).S 2 ≤ (F.str w).S 2) :
    finrank (ZMod 2) ((derivFiniteSES F (switchedER F hF φ σ eM T)).X₂.homology 1) = 1 ∧
      finrank (ZMod 2) ((derivFiniteSES F (switchedER F hF φ σ eM T)).X₂.homology 2) = 1 := by
  obtain ⟨bF, hι⟩ := exists_finBasis (Gv := genGv (K := K) (S := S))
    (Mv := genMv (K := K) (S := S) (M := M)) φ σ eM hF T
  exact cone_dims_finite_derived F (switchedER F hF φ σ eM T) hε hσ hJ2 Q tr htr hγ hsw bR hv hA
    hB a hspan ha hside2 bF hι

end ZInQ.Contrib.CloudB3RC53.GenuineInst

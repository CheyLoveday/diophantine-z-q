import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ConeMatrix
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeTransport

/-!
# Genuine instantiations, part 13: the genuine finite-side cone `C_F`

Manuscript `diophantine_zq.tex`, tex L4876–4906 (the cone triangles
`C_str → C_F → F_v[−1] → C_str[1]` of the derivative conditions) and tex L5068–5083.

From the switching author's derivative families (`DerivFamily`, `SwitchInputs/DerivativeTransport`:
at each place subcomplexes `strict ≤ side ≤ relaxed` of the genuine local complexes, the side
being the finite condition `D⁰ ⊕ F[−1]`):

* `derivSwitch`: the other team's `GenuineSwitch` (relaxed conditions
  `galCond F.rel`, strict maps the inclusions `str ≤ rel`, switch quotient
  `W_rel = ⊕ rel/str`);
* `derivFiniteSES`, `derivFiniteSES_shortExact`: the genuine finite-side sequence
  `0 → C_str → C_F → W₁ → 0` (`C_F` the Selmer complex of the side conditions, `W₁ = ⊕ side/str`);
* `derivFiniteToRelaxed`: the morphism of short exact sequences into the genuine relaxed
  sequence `0 → C_str → C_rel → W_rel → 0` (identity on `C_str`, the change-of-condition map
  `C_F → C_rel`, and `F.i : W₁ → W_rel`);
* **`cone_dims_finite`**: the generic dimensions of the genuine `C_F` are `(1, 1)` from the duality
  adjunction, the localization data of `A`, `B` (tex L4892–4894), `dim H²(C_str) = 2`, the generic
  vanishing, and the coordinates of the finite plane (`eR (H¹(i) e_j) = (e_j, 0)`, the finite-side
  case of the switching author's `hP`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open scoped Matrix

open Module CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

variable (F : DerivFamily (galLv (k := k) K S M))

theorem derivFr_injective (n : ℤ) : Function.Injective (F.fr.f n n rfl) := by
  intro x y h
  funext v
  exact SubFam.inclLe_injective (fun n => (F.hss v n).trans (F.hsr v n)) n (congrFun h v)

/-- **The genuine switch data of a derivative family.** -/
def derivSwitch (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) :
    GenuineSwitch K S k M where
  ΔR := galCond K S M F.rel
  US v := (F.str v).cx
  φ v := SubFam.inclLe fun n => (F.hss v n).trans (F.hsr v n)
  W := F.Wrel
  g := quotMk F.fr
  hfg n u := quotMk_comp_apply F.fr n u
  φ_inj := (derivFr_injective F)
  g_surj := quotMk_surjective F.fr
  ex n u hu := (quotMk_eq_zero_iff F.fr n u).1 hu
  eR := eR

variable (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))

/-- The Selmer data of the side (finite) conditions, as the restriction of the relaxed data. -/
abbrev derivFinData : SelData k :=
  restrictData (derivSwitch F eR).toQuasi.D F.f₁

/-- **The genuine finite-side sequence** `0 → C_str → C_F → W₁ → 0`. -/
def derivFiniteSES : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  changeSES (derivFinData F eR) F.fs (quotMk F.fs) (fun n u => quotMk_comp_apply F.fs n u)

theorem derivFiniteSES_shortExact : (derivFiniteSES F eR).ShortExact :=
  relaxedQuotientNode_proof k (derivFinData F eR) F.Ustr F.W₁ F.fs (quotMk F.fs)
    (fun n u => quotMk_comp_apply F.fs n u) F.fs_injective (quotMk_surjective F.fs)
    (fun n u hu => (quotMk_eq_zero_iff F.fs n u).1 hu)

/-- The strict condition maps into the local complexes agree: `ι_side ∘ fs = ι_rel ∘ fr`. -/
theorem ghomComp_fs_f₁ :
    ghomComp F.fs (ghomComp F.f₁ (derivSwitch F eR).toQuasi.D.ι) =
      ghomComp (piMap (derivSwitch F eR).φ) (derivSwitch F eR).toQuasi.D.ι :=
  ghom_ext fun _ _ => rfl

/-- The identity of `C_str` between its two presentations (as the restriction of the side data
along `fs`, and of the relaxed data along `fr = f₁ ∘ fs`). -/
def strictId :
    GHom (selCx (restrictData (derivFinData F eR) F.fs))
      (selCx (restrictData (derivSwitch F eR).toQuasi.D (piMap (derivSwitch F eR).φ))) where
  f i j h := by subst h; exact LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change _ - (ghomComp F.fs (ghomComp F.f₁ (derivSwitch F eR).toQuasi.D.ι)).f i (i₁ - 1) _ u - _ =
      _ - (ghomComp (piMap (derivSwitch F eR).φ) (derivSwitch F eR).toQuasi.D.ι).f i (i₁ - 1) _ u -
        _
    rw [ghomComp_fs_f₁ F eR]
    rfl

/-- Its inverse. -/
def strictIdInv :
    GHom (selCx (restrictData (derivSwitch F eR).toQuasi.D (piMap (derivSwitch F eR).φ)))
      (selCx (restrictData (derivFinData F eR) F.fs)) where
  f i j h := by subst h; exact LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change
      _ - (ghomComp (piMap (derivSwitch F eR).φ) (derivSwitch F eR).toQuasi.D.ι).f i (i₁ - 1) _ u -
        _ =
      _ - (ghomComp F.fs (ghomComp F.f₁ (derivSwitch F eR).toQuasi.D.ι)).f i (i₁ - 1) _ u - _
    rw [ghomComp_fs_f₁ F eR]
    rfl

instance isIso_strictId : IsIso (GHom.toCC (strictId F eR)) :=
  ⟨⟨GHom.toCC (strictIdInv F eR), by ext n x; rfl, by ext n x; rfl⟩⟩

/-- **The morphism from the finite-side sequence to the relaxed sequence**: the identity of
`C_str`, the change-of-condition map `C_F → C_rel` and `i : W₁ → W_rel`. -/
def derivFiniteToRelaxed :
    (derivFiniteSES F eR) ⟶ changeSES (derivSwitch F eR).toQuasi.D
      (piMap (derivSwitch F eR).φ) (derivSwitch F eR).toQuasi.gR
      (derivSwitch F eR).hfg where
  τ₁ := GHom.toCC (strictId F eR)
  τ₂ := GHom.toCC (changeMap (derivSwitch F eR).toQuasi.D F.f₁)
  τ₃ := GHom.toCC F.i
  comm₁₂ := by
    refine (GHom.toCC_comp _ _).trans (Eq.trans ?_ (GHom.toCC_comp _ _).symm)
    refine GHom.toCC_ext fun i x => ?_
    obtain ⟨a, u, y⟩ := x
    rfl
  comm₂₃ := by
    refine (GHom.toCC_comp _ _).trans (Eq.trans ?_ (GHom.toCC_comp _ _).symm)
    refine GHom.toCC_ext fun i x => ?_
    obtain ⟨a, u, y⟩ := x
    rfl

instance isIso_derivFiniteToRelaxed_τ₁ :
    IsIso (HomologicalComplex.homologyMap (derivFiniteToRelaxed F eR).τ₁ 2) := by
  change IsIso (HomologicalComplex.homologyMap (GHom.toCC (strictId F eR)) 2)
  infer_instance

/-- **The generic dimensions of the genuine finite-side cone `C_F` are `(1, 1)`** (tex L4888–4906):
for a derivative family of subcomplexes of the genuine local complexes (side = the finite
condition), given the duality adjunction for its genuine switch data (Nekovář 6.3.3–6.3.4,
`GenuineSwitch.adjunction`), a basis `A, B` of `H¹(C_rel)` with `λ A = (v, 0)`, `λ B = (0, J v)`
(tex L4892–4894), `dim H²(C_str) = 2`, the generic vanishing `H^n(W₁) = 0` (`n ≠ 1`) and
`H^n(C_str) = 0` (`n ≠ 2`), finite-dimensionality, and a basis `e_j` of `H¹(W₁)` with
`eR (H¹(i) e_j) = (e_j, 0)` (the finite plane): `dim H¹(C_F) = dim H²(C_F) = 1`. PROVED. -/
theorem cone_dims_finite {ε σ : k} {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1)
    (hadj : SwitchDualityAdjunction (derivSwitch F eR).toQuasi (derivSwitch F eR).Dstr
      ε σ J hε hσ hJ2 (derivSwitch F eR).δ (derivSwitch F eR).hex)
    (bR : Basis (Fin 2) k ((selCx (derivSwitch F eR).toQuasi.D).toCC.homology 1))
    {v : Fin 2 → k} (hv : v ≠ 0)
    (hA : genLam (derivSwitch F eR) (bR 0) = (v, 0))
    (hB : genLam (derivSwitch F eR) (bR 1) = (0, J *ᵥ v))
    (hH2 : finrank k ((selCx (derivSwitch F eR).Dstr).toCC.homology 2) = 2)
    (h3 : ∀ n, n ≠ 1 → Subsingleton ((derivFiniteSES F eR).X₃.homology n))
    (h1 : ∀ n, n ≠ 2 → Subsingleton ((derivFiniteSES F eR).X₁.homology n))
    [FiniteDimensional k ((derivFiniteSES F eR).X₁.homology 2)]
    [FiniteDimensional k ((derivFiniteSES F eR).X₂.homology 1)]
    [FiniteDimensional k ((derivFiniteSES F eR).X₂.homology 2)]
    [FiniteDimensional k ((derivFiniteSES F eR).X₃.homology 1)]
    (bF : Basis (Fin 2) k ((derivFiniteSES F eR).X₃.homology 1))
    (hι : ∀ j, eR (H1 F.i (bF j)) = (Pi.single j 1, 0)) :
    finrank k ((derivFiniteSES F eR).X₂.homology 1) = 1 ∧
      finrank k ((derivFiniteSES F eR).X₂.homology 2) = 1 :=
  cone_dims_genuine_of_hom (derivSwitch F eR) hε hσ hJ2 hadj bR hv hA hB hH2
    (derivFiniteSES F eR) (derivFiniteSES_shortExact F eR) h3 h1 (derivFiniteToRelaxed F eR) bF
    hι

end ZInQ.Contrib.CloudB3RC53.GenuineInst

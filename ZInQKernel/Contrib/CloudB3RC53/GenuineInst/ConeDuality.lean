import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ConeFinite
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.DualHomology

/-!
# Genuine instantiations, part 15: `dim H²(C_str) = 2` from the Selmer duality

Manuscript `diophantine_zq.tex`, tex L4888–4906 ("`H²(C_str) = ⟨A, B⟩^∨`"; the transported duality
of Nekovář 6.3.4).

The hypothesis `dim H²(C_str) = 2` of `cone_dims_finite` follows from the Selmer duality
quasi-isomorphism `γ : C_str → Hom(C_rel, k)[−3]` (Nekovář 6.3.4; for genuine data from the PRINT
`NekovarProp543`, `genuineSelmerDuality`) and the basis `A, B` of `H¹(C_rel)`:
`H²(C_str) ≅ H²(Hom(C_rel, k)[−3]) ≅ H¹(C_rel)^∨` (`finrank_homology_dualCx`).

* `finrank_h2_strict_of_duality`: `dim H²(C_str) = dim H¹(C_rel)` under `γ`;
* **`cone_dims_finite_of_duality`**: `cone_dims_finite` with the adjunction and `dim H²(C_str) = 2`
  both derived from the duality data (`γ` and the switch coordinates, the inputs of
  `GenuineSwitch.adjunction`).

The generic vanishing (`H¹(C_str) = 0`, …) is not a consequence of the local counts: by the same
duality it is equivalent to vanishing of the relaxed cohomology in complementary degrees
(`finrank_homology_dualCx`), a global fact of the text ("The strict `H¹` vanishes", tex L4895).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open scoped Matrix

open Module CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k]

/-- **`dim Hⁿ(C) = dim H^{3−n}(C')` under a duality quasi-isomorphism `C → Hom(C', k)[−3]`.** -/
theorem finrank_homology_of_duality {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr))) (n : ℤ)
    [FiniteDimensional k ((selCx D').toCC.homology (3 - n))] :
    finrank k ((selCx D).toCC.homology n) = finrank k ((selCx D').toCC.homology (3 - n)) := by
  have : IsIso (HomologicalComplex.homologyMap (GHom.toCC (selmerDualityMap Q tr htr)) n) :=
    inferInstance
  rw [(asIso (HomologicalComplex.homologyMap (GHom.toCC (selmerDualityMap Q tr htr)) n)
    ).toLinearEquiv.finrank_eq]
  exact finrank_homology_dualCx (selCx D') 3 n

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **`dim H²(C_str) = 2`** from the duality quasi-isomorphism and a basis of `H¹(C_rel)`. -/
theorem finrank_h2_strict_of_duality (X : GenuineSwitch K S k M)
    (Q : SelPairData X.Dstr X.toQuasi.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (bR : Basis (Fin 2) k ((selCx X.toQuasi.D).toCC.homology 1)) :
    finrank k ((selCx X.Dstr).toCC.homology 2) = 2 := by
  have : FiniteDimensional k ((selCx X.toQuasi.D).toCC.homology (3 - 2)) :=
    bR.finiteDimensional_of_finite
  rw [finrank_homology_of_duality Q tr htr hγ 2]
  change finrank k ((selCx X.toQuasi.D).toCC.homology 1) = 2
  rw [finrank_eq_card_basis bR, Fintype.card_fin]

variable (F : DerivFamily (galLv (k := k) K S M))
  (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))

/-- **The generic dimensions of the genuine finite-side cone from the duality data** (tex
L4888–4906): `cone_dims_finite` with the adjunction (`GenuineSwitch.adjunction`) and
`dim H²(C_str) = 2` (`finrank_h2_strict_of_duality`) derived from the Selmer duality
quasi-isomorphism `γ` (Nekovář 6.3.4) and the switch coordinates (tex 2816–2818). Remaining: the
localization data of `A`, `B` (tex L4892–4894), the generic vanishing, finite-dimensionality and
the finite-plane coordinates. PROVED. -/
theorem cone_dims_finite_of_duality {ε σ : k} {J : Matrix (Fin 2) (Fin 2) k} (hε : ε ≠ 0)
    (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (Q : SelPairData (derivSwitch F eR).Dstr (derivSwitch F eR).toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : (derivSwitch F eR).SwitchCoordinates Q tr ε σ J)
    (bR : Basis (Fin 2) k ((selCx (derivSwitch F eR).toQuasi.D).toCC.homology 1))
    {v : Fin 2 → k} (hv : v ≠ 0)
    (hA : genLam (derivSwitch F eR) (bR 0) = (v, 0))
    (hB : genLam (derivSwitch F eR) (bR 1) = (0, J *ᵥ v))
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
  cone_dims_finite F eR hε hσ hJ2
    ((derivSwitch F eR).adjunction Q tr htr ε σ J hε hσ hJ2 hγ hsw) bR hv hA hB
    (finrank_h2_strict_of_duality (derivSwitch F eR) Q tr htr hγ bR) h3 h1 bF hι

end ZInQ.Contrib.CloudB3RC53.GenuineInst

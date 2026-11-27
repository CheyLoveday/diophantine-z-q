import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeUnramified
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# RC53 `hsw` shape: cocycles vanishing on inertia are unramified at the switch place

The tie `hUrRep` of `ShapeUnramified.lean` asks for finite-plane representatives that are
inflated from `Gal(K_q^ur/K_q)` at the switch place `q`. The derivative coordinates describe the
finite side differently, as the cocycles vanishing on inertia (`finite_side_iff`). This file
proves that the two descriptions agree for coefficients on which `G_{K_q}` acts trivially. The
argument works over any coefficient field and uses no tame structure.

* `exists_infl_of_vanish`: with trivial action a local `1`-cocycle is a continuous homomorphism.
  If it vanishes on `ker(urRes)` it factors through `urRes`, which is a quotient map because
  `G_{K_q}` is compact and `Gal(K_q^ur/K_q)` is Hausdorff. So it is the inflation of a continuous
  cocycle of `Gal(K_q^ur/K_q)`.
* `urCompat_one`, `urCompat_one_T`: with trivial action the trivial homomorphism
  `Gal(K_q^ur/K_q) → G_{K,S}` is compatible with the actions.
* `urAt_of_vanish`, `hUrRep_of_vanish`: the tie `hUrRep`, with `ψ = 1`, from finite-plane
  representatives supported at `q` that vanish on `ker(urRes)` there.
* `genuine_switchCoordinates_char2_vanish`: `SwitchCoordinates` for the genuine switch in
  characteristic two, with the tie in the vanishing-on-inertia form. Nondegeneracy (local Tate
  duality) is the only other input.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open CategoryTheory NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.RankCounts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

omit [Module k M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M] in
/-- With coefficients on which `G_{K_q}` acts trivially, the trivial homomorphism
`Gal(K_q^ur/K_q) → G_{K,S}` is compatible with the actions (`PROVED`). -/
theorem urCompat_one (q : Places K S) (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (g : Gloc K q.1) (m : M) :
    (1 : GUr K q.1 →ₜ* GKS K S) (urRes K q.1 g) • m = locMap K S q.1 g • m := by
  rw [htriv]
  exact one_smul _ m

/-- **A local `1`-cocycle at `q` vanishing on the inertia kernel `ker(urRes)` is inflated from
`Gal(K_q^ur/K_q)`** (`PROVED`, any coefficient field), when `G_{K_q}` acts trivially on `M`. For
trivial action the cocycle is a continuous homomorphism. It factors continuously through the
quotient map `urRes` (`exists_continuousMonoidHom_factor`: `G_{K_q}` is compact and
`Gal(K_q^ur/K_q)` is Hausdorff). -/
theorem exists_infl_of_vanish (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (z : (contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).X 1)
    (hzd : ((contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom z = 0)
    (hzI : ∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) :
    ∃ a' : (contCochains k (GUr K q.1) (ResMod (1 : GUr K q.1 →ₜ* GKS K S) M)).X 1,
      ((contCochains k (GUr K q.1) (ResMod (1 : GUr K q.1 →ₜ* GKS K S) M)).d 1 2).hom a' = 0 ∧
        z = ((urInfl (k := k) M q 1 (urCompat_one q htriv)).f 1).hom a' := by
  let z₁ : Gloc K q.1 → ResMod (locMap K S q.1) M := fun g => cFun z (fun _ => g)
  -- the cocycle identity with trivial action: `z₁` is additive
  have hdz : ∀ g h : Gloc K q.1, z₁ (g * h) = z₁ g + z₁ h := by
    intro g h
    have e := congrFun (congrArg (fun c : (contCochains k (Gloc K q.1)
      (ResMod (locMap K S q.1) M)).X (1 + 1) =>
        asFun k (Gloc K q.1) (ResMod (locMap K S q.1) M)
          (((contSubCx k (Gloc K q.1) (ResMod (locMap K S q.1) M)).el c :
            contCochain k (Gloc K q.1) (ResMod (locMap K S q.1) M) (1 + 1)) :
            (groupCohomology.inhomogeneousCochains (rep k (Gloc K q.1)
              (ResMod (locMap K S q.1) M))).X (1 + 1))) hzd) ![g, h]
    simp only at e
    rw [contCochains_d_coe] at e
    change dFun k 1 (cFun z) ![g, h] = 0 at e
    rw [dFun_one] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have hg : (g • z₁ h : ResMod (locMap K S q.1) M) = z₁ h := htriv g _
    change g • z₁ h - z₁ (g * h) + z₁ g = 0 at e
    rw [hg, sub_add_eq_add_sub, sub_eq_zero] at e
    exact e.symm.trans (add_comm _ _)
  have hz1 : z₁ 1 = 0 := by
    have := hdz 1 1
    rw [one_mul] at this
    exact left_eq_add.mp this
  have hzc : Continuous z₁ := by
    have h1 := ((contSubCx k (Gloc K q.1) (ResMod (locMap K S q.1) M)).el z).2
    exact h1.comp (continuous_pi fun _ => continuous_id :
      Continuous fun (g : Gloc K q.1) (_ : Fin 1) => g)
  have : CompactSpace (Gloc K q.1) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure (q.1.adicCompletion K) ≃ₐ[q.1.adicCompletion K]
      AlgebraicClosure (q.1.adicCompletion K)))
  have : T2Space (GUr K q.1) := krullTopology_t2
  have hq : Topology.IsQuotientMap (urRes K q.1) :=
    ((urRes K q.1).continuous.isClosedMap).isQuotientMap (urRes K q.1).continuous
      (urRes_surjective K q.1)
  let lift : GUr K q.1 → Gloc K q.1 := Function.surjInv (urRes_surjective K q.1)
  have hlift : ∀ h, urRes K q.1 (lift h) = h := Function.surjInv_eq (urRes_surjective K q.1)
  have hneg : ∀ g, z₁ g⁻¹ = -z₁ g := fun g => by
    have := hdz g⁻¹ g
    rw [inv_mul_cancel, hz1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have key : ∀ g, z₁ (lift (urRes K q.1 g)) = z₁ g := by
    intro g
    have h0 : z₁ ((lift (urRes K q.1 g))⁻¹ * g) = 0 :=
      hzI _ (by rw [map_mul, map_inv, hlift, inv_mul_cancel])
    rw [hdz, hneg] at h0
    exact (neg_add_eq_zero.mp h0)
  let z₂ : GUr K q.1 → ResMod (locMap K S q.1) M := fun h => z₁ (lift h)
  have hz₂c : Continuous z₂ := by
    rw [hq.continuous_iff]
    have : z₂ ∘ urRes K q.1 = z₁ := funext key
    rw [this]
    exact hzc
  have hz₂ : ∀ h₁ h₂, z₂ (h₁ * h₂) = z₂ h₁ + z₂ h₂ := by
    intro h₁ h₂
    obtain ⟨g₁, rfl⟩ := urRes_surjective K q.1 h₁
    obtain ⟨g₂, rfl⟩ := urRes_surjective K q.1 h₂
    show z₁ (lift (urRes K q.1 g₁ * urRes K q.1 g₂)) = z₁ (lift (urRes K q.1 g₁)) +
      z₁ (lift (urRes K q.1 g₂))
    rw [← map_mul, key, key, key, hdz]
  let e₁ := resModId (k := k) (locMap K S q.1) (1 : GUr K q.1 →ₜ* GKS K S) M
  let a₀ : (Fin 1 → GUr K q.1) → ResMod (1 : GUr K q.1 →ₜ* GKS K S) M :=
    fun y => e₁ (z₂ (y 0))
  have ha₀ : Continuous a₀ :=
    continuous_of_discreteTopology.comp (hz₂c.comp (continuous_apply 0))
  let a' : (contCochains k (GUr K q.1) (ResMod (1 : GUr K q.1 →ₜ* GKS K S) M)).X 1 :=
    (contSubCx k (GUr K q.1) (ResMod (1 : GUr K q.1 →ₜ* GKS K S) M)).ofSub ⟨a₀, ha₀⟩
  refine ⟨a', ?_, ?_⟩
  · apply Subtype.ext
    funext y
    have hd := contCochains_d_coe (k := k) (G := GUr K q.1)
      (M := ResMod (1 : GUr K q.1 →ₜ* GKS K S) M) 1 a'
    refine (congrFun hd y).trans ?_
    change dFun k 1 a₀ y = 0
    rw [dFun_one]
    have h1 : ∀ m : ResMod (1 : GUr K q.1 →ₜ* GKS K S) M, y 0 • m = m :=
      fun m => one_smul (GKS K S) (show M from m)
    rw [h1]
    change e₁ (z₂ (y 1)) - e₁ (z₂ (y 0 * y 1)) + e₁ (z₂ (y 0)) = 0
    rw [hz₂, map_add]
    abel
  · apply Subtype.ext
    funext y
    change cFun z y = z₁ (lift (urRes K q.1 (y 0)))
    rw [key, fin1_eta y]

/-- **A local cochain supported at `q`, there a cocycle vanishing on `ker(urRes)`, is unramified
at `q`** (`UrAt` with `ψ = 1`; `PROVED`, any coefficient field, trivial action at `q`). -/
theorem urAt_of_vanish (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (x : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      M).X 1) (hx0 : ∀ v, v ≠ q → x v = 0)
    (hxd : ((contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom (x q) = 0)
    (hxI : ∀ g, urRes K q.1 g = 1 → cFun (x q) (fun _ => g) = 0) :
    UrAt q 1 (urCompat_one q htriv) x :=
  ⟨exists_infl_of_vanish q htriv (x q) hxd hxI, hx0⟩

variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T]

/-- **The tie from cocycles vanishing on inertia** (`PROVED`, any coefficient field). Let `G_{K_q}`
act trivially on `M`. Suppose every vector of the finite plane is `eR[g t]` for a relaxed cocycle
`t` whose local image is supported at `q`, where it vanishes on `ker(urRes)`. Then the tie
`hUrRep` of `genuine_finIso_of_ur` holds with `ψ = 1`. -/
theorem hUrRep_of_vanish (X : GenuineSwitch K S k M) (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (hrep : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ (∀ v, v ≠ q → X.toQuasi.D.ι.f 1 1 rfl t v = 0) ∧
          ∀ g, urRes K q.1 g = 1 → cFun (X.toQuasi.D.ι.f 1 1 rfl t q) (fun _ => g) = 0) :
    ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧
          UrAt q 1 (urCompat_one q htriv) (X.toQuasi.D.ι.f 1 1 rfl t) := by
  intro a ha
  obtain ⟨t, ht, hta, h0, hI⟩ := hrep a ha
  refine ⟨t, ht, hta, urAt_of_vanish q htriv _ h0 ?_ hI⟩
  have hd : X.toQuasi.D.L.d 1 2 rfl (X.toQuasi.D.ι.f 1 1 rfl t) = 0 := by
    rw [← X.toQuasi.D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  exact congrFun hd q

omit [Module k T] [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] [Finite T] in
/-- The compatibility for the target module. -/
theorem urCompat_one_T (q : Places K S)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m) (g : Gloc K q.1) (m : T) :
    (1 : GUr K q.1 →ₜ* GKS K S) (urRes K q.1 g) • m = locMap K S q.1 g • m := by
  rw [htrivT]
  exact one_smul _ m

/-- **`SwitchCoordinates` for the genuine switch in characteristic two, with the tie from
inertia** (`PROVED` from the inputs; any coefficient field of characteristic two). Assume:
* `G_{K_q}` acts trivially on `M` and `T`;
* every finite-plane vector is the class of a relaxed cocycle supported at `q`, where it vanishes
  on inertia (supplied at the switch place by the derivative coordinates: the finite side is the
  cocycles vanishing on inertia).

Then nondegeneracy of the residue form (local Tate duality) is the only remaining input. -/
theorem genuine_switchCoordinates_char2_vanish (h2 : (2 : k) = 0) (X : GenuineSwitch K S k M)
    (β γ : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
    (hγ : ∀ (g : GKS K S) (x y : M), γ (g • x) (g • y) = g • γ x y)
    (hpol : ∀ x y, β x y = γ x y - γ y x) (I : GaloisIsotropyData K S k β hβ X.ΔS X.ΔR)
    (tr : (coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (galoisPairData K S k β hβ X.ΔS X.ΔR I).resE).d 2 3 rfl z) = 0)
    (hUS2 : ∀ v (x : (X.US v).X 2), x = 0) {ε : k} (hε : ε ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) k} (hJ2 : J * J = 1) (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : M), locMap K S q.1 g • m = m)
    (htrivT : ∀ (g : Gloc K q.1) (m : T), locMap K S q.1 g • m = m)
    (hrep : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ (∀ v, v ≠ q → X.toQuasi.D.ι.f 1 1 rfl t v = 0) ∧
          ∀ g, urRes K q.1 g = 1 → cFun (X.toQuasi.D.ι.f 1 1 rfl t q) (fun _ => g) = 0)
    (hnd : ∀ t (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
      (∀ u (_hu : X.toQuasi.D.U.d 1 2 rfl u = 0),
        resForm X.toQuasi (piCx X.US) (piMap X.φ) (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr t u =
          0) → gClass X.toQuasi t ht = 0) :
    ∃ Φ : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)),
      (finPlane k (Fin 2 → k) (Fin 2 → k)).map Φ.toLinearMap =
        finPlane k (Fin 2 → k) (Fin 2 → k) ∧
      ({ X with eR := X.eR.trans Φ } : GenuineSwitch K S k M).SwitchCoordinates
        (galoisPairData K S k β hβ X.ΔS X.ΔR I) tr ε (-(-1)) J :=
  genuine_switchCoordinates_char2_ur h2 X β γ hβ hγ hpol I tr htr hUS2 hε hJ2 q 1
    (urCompat_one q htriv) (urCompat_one_T q htrivT) (hUrRep_of_vanish X q htriv hrep) hnd

end ZInQ.Contrib.CloudB3RC53.Hsw

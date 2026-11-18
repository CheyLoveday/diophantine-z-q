import ZInQKernel.Contrib.CloudB3RC53.Hsw.ShapeUrTie

/-!
# RC53 `hsw` shape: inflation for unramified (not necessarily trivial) actions

`ShapeUrTie.lean` assumed that `G_{K_q}` acts trivially on the coefficients. At the switching
primes the coefficient module is unramified at `q`, but Frobenius acts nontrivially. This file
removes the triviality assumption. Let `ψ : Gal(K_q^ur/K_q) → G_{K,S}` be a continuous homomorphism
with `ψ (urRes g) • m = loc_q g • m`, i.e. the action of `G_{K_q}` factors through `urRes`. For
example, `ψ = loc_q ∘ s` for a continuous section `s` of `urRes` through a Frobenius lift, when
inertia acts trivially. Then a local `1`-cocycle at `q` vanishing on `ker(urRes)` is inflated
from `Gal(K_q^ur/K_q)` along `ψ`. Inertia acts trivially by the compatibility, and the cocycle is
constant on the cosets of `ker(urRes)`.

* `exists_infl_of_vanish_gen`, `urAt_of_vanish_gen`, `hUrRep_of_vanish_gen`: the generalizations of
  `exists_infl_of_vanish`, `urAt_of_vanish`, `hUrRep_of_vanish` (any coefficient field).

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

/-- **A local `1`-cocycle at `q` vanishing on `ker(urRes)` is inflated from `Gal(K_q^ur/K_q)`**
along any `ψ` through which the action factors (`PROVED`, any coefficient field). -/
theorem exists_infl_of_vanish_gen (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (z : (contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).X 1)
    (hzd : ((contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom z = 0)
    (hzI : ∀ g, urRes K q.1 g = 1 → cFun z (fun _ => g) = 0) :
    ∃ a' : (contCochains k (GUr K q.1) (ResMod ψ M)).X 1,
      ((contCochains k (GUr K q.1) (ResMod ψ M)).d 1 2).hom a' = 0 ∧
        z = ((urInfl (k := k) M q ψ hψ).f 1).hom a' := by
  let z₁ : Gloc K q.1 → ResMod (locMap K S q.1) M := fun g => cFun z (fun _ => g)
  -- the cocycle identity
  have hdz : ∀ g h : Gloc K q.1, z₁ (g * h) = z₁ g + g • z₁ h := by
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
    change g • z₁ h - z₁ (g * h) + z₁ g = 0 at e
    rw [sub_add_eq_add_sub, sub_eq_zero] at e
    exact e.symm.trans (add_comm _ _)
  have hz1 : z₁ 1 = 0 := by
    have := hdz 1 1
    rw [one_mul, one_smul] at this
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
  -- the action through `ψ`
  have hact : ∀ g (m : ResMod (locMap K S q.1) M),
      g • m = (show ResMod (locMap K S q.1) M from ψ (urRes K q.1 g) • (show M from m)) :=
    fun g m => (hψ g m).symm
  have key : ∀ g, z₁ (lift (urRes K q.1 g)) = z₁ g := by
    intro g
    have h0 : z₁ ((lift (urRes K q.1 g))⁻¹ * g) = 0 :=
      hzI _ (by rw [map_mul, map_inv, hlift, inv_mul_cancel])
    have e := hdz (lift (urRes K q.1 g)) ((lift (urRes K q.1 g))⁻¹ * g)
    rw [mul_inv_cancel_left, h0, smul_zero, add_zero] at e
    exact e.symm
  let z₂ : GUr K q.1 → ResMod (locMap K S q.1) M := fun h => z₁ (lift h)
  have hz₂c : Continuous z₂ := by
    rw [hq.continuous_iff]
    have : z₂ ∘ urRes K q.1 = z₁ := funext key
    rw [this]
    exact hzc
  let e₁ := resModId (k := k) (locMap K S q.1) ψ M
  let a₀ : (Fin 1 → GUr K q.1) → ResMod ψ M := fun y => e₁ (z₂ (y 0))
  have ha₀ : Continuous a₀ :=
    continuous_of_discreteTopology.comp (hz₂c.comp (continuous_apply 0))
  have hz₂ : ∀ h₁ h₂ : GUr K q.1, e₁ (z₂ (h₁ * h₂)) = e₁ (z₂ h₁) + h₁ • e₁ (z₂ h₂) := by
    intro h₁ h₂
    obtain ⟨g₁, rfl⟩ := urRes_surjective K q.1 h₁
    obtain ⟨g₂, rfl⟩ := urRes_surjective K q.1 h₂
    change e₁ (z₁ (lift (urRes K q.1 g₁ * urRes K q.1 g₂))) = e₁ (z₁ (lift (urRes K q.1 g₁))) +
      (show ResMod ψ M from ψ (urRes K q.1 g₁) • (show M from e₁ (z₁ (lift (urRes K q.1 g₂)))))
    rw [← map_mul, key, key, key, hdz, map_add]
    congr 1
    exact hact g₁ _
  let a' : (contCochains k (GUr K q.1) (ResMod ψ M)).X 1 :=
    (contSubCx k (GUr K q.1) (ResMod ψ M)).ofSub ⟨a₀, ha₀⟩
  refine ⟨a', ?_, ?_⟩
  · apply Subtype.ext
    funext y
    have hd := contCochains_d_coe (k := k) (G := GUr K q.1) (M := ResMod ψ M) 1 a'
    refine (congrFun hd y).trans ?_
    change dFun k 1 a₀ y = 0
    rw [dFun_one]
    change y 0 • e₁ (z₂ (y 1)) - e₁ (z₂ (y 0 * y 1)) + e₁ (z₂ (y 0)) = 0
    rw [hz₂]
    abel
  · apply Subtype.ext
    funext y
    change cFun z y = z₁ (lift (urRes K q.1 (y 0)))
    rw [key, fin1_eta y]

/-- **A local cochain supported at `q`, there a cocycle vanishing on `ker(urRes)`, is unramified
at `q`** along any compatible `ψ` (`PROVED`, any coefficient field). -/
theorem urAt_of_vanish_gen (q : Places K S) (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (x : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      M).X 1) (hx0 : ∀ v, v ≠ q → x v = 0)
    (hxd : ((contCochains k (Gloc K q.1) (ResMod (locMap K S q.1) M)).d 1 2).hom (x q) = 0)
    (hxI : ∀ g, urRes K q.1 g = 1 → cFun (x q) (fun _ => g) = 0) :
    UrAt q ψ hψ x :=
  ⟨exists_infl_of_vanish_gen q ψ hψ (x q) hxd hxI, hx0⟩

/-- **The tie from cocycles vanishing on inertia, for unramified actions** (`PROVED`, any
coefficient field): `hUrRep` with any compatible `ψ`. -/
theorem hUrRep_of_vanish_gen (X : GenuineSwitch K S k M) (q : Places K S)
    (ψ : GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ g (m : M), ψ (urRes K q.1 g) • m = locMap K S q.1 g • m)
    (hrep : ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ (∀ v, v ≠ q → X.toQuasi.D.ι.f 1 1 rfl t v = 0) ∧
          ∀ g, urRes K q.1 g = 1 → cFun (X.toQuasi.D.ι.f 1 1 rfl t q) (fun _ => g) = 0) :
    ∀ a, a ∈ finPlane k (Fin 2 → k) (Fin 2 → k) →
      ∃ (t : X.toQuasi.D.U.X 1) (ht : X.toQuasi.D.U.d 1 2 rfl t = 0),
        gClass X.toQuasi t ht = a ∧ UrAt q ψ hψ (X.toQuasi.D.ι.f 1 1 rfl t) := by
  intro a ha
  obtain ⟨t, ht, hta, h0, hI⟩ := hrep a ha
  refine ⟨t, ht, hta, urAt_of_vanish_gen q ψ hψ _ h0 ?_ hI⟩
  have hd : X.toQuasi.D.L.d 1 2 rfl (X.toQuasi.D.ι.f 1 1 rfl t) = 0 := by
    rw [← X.toQuasi.D.ι.comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  exact congrFun hd q

end ZInQ.Contrib.CloudB3RC53.Hsw

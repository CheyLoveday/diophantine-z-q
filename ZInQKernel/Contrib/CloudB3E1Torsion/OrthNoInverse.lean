import ZInQKernel.Contrib.CloudB3E2Norm.DualPres
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition

/-!
# The orthogonal comparison has no inverse at a finite stage

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-paired-functional`, tex 3736–3753: "at a
localization where the full local complexes at active and moving primes are acyclic, the
comparison from the orthogonal condition to the transported condition is a quasi-isomorphism.
Apply its inverse in the derived category to the transported class."

Lane E2's `DualPres.OrthComparisonInverse` asks for this inverse at the finite stage itself: maps
`ψ_T : C'_T → C_{T⊥}` commuting with `d`, inverse to the comparison `c_T` on `H¹`. This file
proves that no such inverse exists once the comparison passes from zero to full at two places
and the full condition there has a nonzero invariant.

* **`condMap_not_injective_H1`** (PROVED, generic): let `Δ₁ → Δ₂` be a morphism of local
  conditions (`condMap`). Suppose there are two places `v₁ ≠ v₂` where `Δ₁` has zero terms in
  degree `0`, and a degree-`0` cocycle `u₁` of `Δ₂` at `v₁` with nonzero image in the local
  cochains. Then some `H¹` class of `C_{Δ₁}` is nonzero but maps to `0` in `H¹(C_{Δ₂})`: it is
  `z = (0, 0, −δ_{v₁} ι(u₁))`, the boundary of `(0, δ_{v₁} u₁, 0)` in `C_{Δ₂}`. If `z = d(a, u, ·)`,
  then the restrictions of the global `0`-cochain `a` to `v₂` and to `v₁` would be `0` and
  `−ι(u₁)`. They are the same constant, a contradiction.
* **`no_H1_inverse`** (PROVED): hence no `ψ` commuting with `d` is a left inverse of `c` on `H¹`.
* **`not_orthComparisonInverse`** (PROVED): lane E2's `OrthComparisonInverse` is uninhabited as
  soon as there is an index `p` and a nonzero `m ∈ M` fixed by `G_{K_w}` at the place
  `w = place (p, false)`. With `T = {p}`, both places above `p` pass from zero to full, and
  `u₁ = m` (a constant `0`-cochain) is a cocycle of the full condition. No property of `φo` is
  used. For the actual coefficient modules `M_i = (E[2^i] ⊗ A_i)(α)`, `i ≥ 1`, such an `m` exists
  (argued here, not formalized): `m = c ⊗ Q` with `c = 2^{i−1} t^{i−1}` spanning the socle of
  `A_i` and `Q ∈ E[2^i] ∖ 2E[2^i]`, so `m ≠ 0`. For `g ∈ G_{K_w}`, `α(g) ∈ A_i^× = 1 + 𝔪` fixes
  `c`. Also `gQ − Q ∈ 2E[2^i]`, because `G` acts trivially on `E[2^i]/2E[2^i] ≅ E[2]`
  (`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` has full rational `2`-torsion). Since `2c = 0`, `g • m = m`.

**The corrected form** (the text's, tex 3736–3753). The inverse exists only after a localization at
which the cones of the zero → full comparisons are acyclic. Those cones are the full local complexes
`C^•_cont(G_{K_v}, M)` at the places passing from zero to full. Concretely, replace the stage
coefficients by the generic fibre: `Λ[1/t]`, or the fraction field `Frac Λ`, of the Iwasawa
algebra. There the local cohomology `H^•(K_v, T ⊗ Λ)` at the active and moving primes is
`Λ`-torsion and dies, and the comparison is a quasi-isomorphism. The named input should therefore
be stated over that localization, e.g. as `ψ_T : C'_T ⊗ Frac Λ → C_{T⊥} ⊗ Frac Λ` inverse to
`c_T ⊗ Frac Λ` on `H¹`. The lifted classes then come back to the stage only up to the denominators
of `Frac Λ`, as in the text's "lift … at the generic point" (tex 3708–3711).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex

universe u

section Generic

variable {k : Type u} [CommRing k] {GS : Type u} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type u} [DecidableEq ι] {Gv : ι → Type u} [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

omit [DecidableEq ι] in
/-- Restrictions of a global `0`-cochain to two places vanish together. Kind: PROVED. -/
theorem res_zero_of_res_zero (a : (globalCx k GS M).X 0) (v w : ι)
    (h : (resS k GS Gv loc M).f 0 0 rfl a v = 0) : (resS k GS Gv loc M).f 0 0 rfl a w = 0 := by
  have hv : ∀ y : Fin 0 → Gv v,
      asFun k (Gv v) (ResMod (loc v) M) ((resS k GS Gv loc M).f 0 0 rfl a v).1 y = 0 :=
    fun y => congrArg (fun c : (localCx k GS Gv loc M v).X 0 => asFun k _ _ c.1 y) h
  apply Subtype.ext
  funext y
  have e : (fun i => loc w (y i)) = (fun i => loc v ((default : Fin 0 → Gv v) i)) :=
    funext fun i => Fin.elim0 i
  change asFun k GS M a.1 (fun i => loc w (y i)) = 0
  rw [e]
  exact hv default

variable (Δ₁ Δ₂ : LocalConditions k GS Gv loc M) (F : ∀ v, GHom (Δ₁.U v) (Δ₂.U v))
  (hF : ∀ v (i : ℤ) (u : (Δ₁.U v).X i), (Δ₂.i v).f i i rfl ((F v).f i i rfl u) = (Δ₁.i v).f i i rfl u)

/-- **The `H¹` comparison is not injective** (PROVED): two places where `Δ₁` is zero in degree `0`
and a degree-`0` cocycle of `Δ₂` at the first with nonzero local image give a non-coboundary
cocycle of `C_{Δ₁}` whose image is a coboundary of `C_{Δ₂}`. -/
theorem condMap_not_injective_H1 (v₁ v₂ : ι) (hne : v₁ ≠ v₂)
    (h₁ : Subsingleton ((Δ₁.U v₁).X 0)) (h₂ : Subsingleton ((Δ₁.U v₂).X 0))
    (u₁ : (Δ₂.U v₁).X 0) (hdu : (Δ₂.U v₁).d 0 1 rfl u₁ = 0)
    (hιu : (Δ₂.i v₁).f 0 0 rfl u₁ ≠ 0) :
    ∃ z : (selCx (selData k GS Gv loc M Δ₁)).X 1,
      (selCx (selData k GS Gv loc M Δ₁)).d 1 2 rfl z = 0 ∧
      (∃ y : (selCx (selData k GS Gv loc M Δ₂)).X 0,
        (condMap Δ₁ Δ₂ F hF).f 1 1 rfl z = (selCx (selData k GS Gv loc M Δ₂)).d 0 1 rfl y) ∧
      ¬ ∃ w : (selCx (selData k GS Gv loc M Δ₁)).X 0,
        z = (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl w := by
  set w₁ : (localCx k GS Gv loc M v₁).X 0 := (Δ₂.i v₁).f 0 0 rfl u₁ with hw₁
  set x : (localSumCx k GS Gv loc M).X 0 :=
    -(Pi.single (M := fun v => (localCx k GS Gv loc M v).X 0) v₁ w₁) with hx
  have hdw : (localCx k GS Gv loc M v₁).d 0 1 rfl w₁ = 0 := by
    rw [hw₁, ← (Δ₂.i v₁).comm 0 1 0 1 rfl rfl rfl rfl u₁, hdu, map_zero]
  have hdx : (localSumCx k GS Gv loc M).d 0 1 rfl x = 0 := by
    funext v
    rw [piCx_d_apply, hx]
    by_cases hv : v = v₁
    · subst hv
      rw [Pi.neg_apply, Pi.single_eq_same, map_neg, hdw, neg_zero]
      rfl
    · rw [Pi.neg_apply, Pi.single_eq_of_ne hv, neg_zero, map_zero]
      rfl
  refine ⟨((0, 0, x) : selT (selData k GS Gv loc M Δ₁) 1), ?_, ?_, ?_⟩
  · refine Prod.ext (map_zero _) (Prod.ext (map_zero _) ?_)
    change (selData k GS Gv loc M Δ₁).res.f 1 (2 - 1) (by omega) 0 -
        (selData k GS Gv loc M Δ₁).ι.f 1 (2 - 1) (by omega) 0 -
        (selData k GS Gv loc M Δ₁).L.d (1 - 1) (2 - 1) (by omega) x = 0
    rw [map_zero, map_zero, sub_zero, zero_sub, neg_eq_zero]
    exact hdx
  · refine ⟨((0, Pi.single (M := fun v => (Δ₂.U v).X 0) v₁ u₁, 0) :
      selT (selData k GS Gv loc M Δ₂) 0), ?_⟩
    refine Prod.ext (map_zero _).symm (Prod.ext ?_ ?_)
    · change (piMap F).f 1 1 rfl 0 =
        (piCx Δ₂.U).d 0 1 rfl (Pi.single (M := fun v => (Δ₂.U v).X 0) v₁ u₁)
      rw [map_zero]
      funext v
      change (0 : (Δ₂.U v).X 1) =
        (Δ₂.U v).d 0 1 rfl (Pi.single (M := fun v => (Δ₂.U v).X 0) v₁ u₁ v)
      by_cases hv : v = v₁
      · subst hv
        rw [Pi.single_eq_same, hdu]
      · rw [Pi.single_eq_of_ne hv, map_zero]
    · change x = (selData k GS Gv loc M Δ₂).res.f 0 (1 - 1) (by omega) 0 -
          (selData k GS Gv loc M Δ₂).ι.f 0 (1 - 1) (by omega)
            (Pi.single (M := fun v => (Δ₂.U v).X 0) v₁ u₁) -
          (selData k GS Gv loc M Δ₂).L.d (0 - 1) (1 - 1) (by omega) 0
      rw [map_zero, map_zero, zero_sub, sub_zero, hx]
      congr 1
      funext v
      change _ = (Δ₂.i v).f 0 0 rfl (Pi.single (M := fun v => (Δ₂.U v).X 0) v₁ u₁ v)
      by_cases hv : v = v₁
      · subst hv
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, map_zero]
  · rintro ⟨⟨a, u, t⟩, hw⟩
    have h3 := congrArg (fun c : selT (selData k GS Gv loc M Δ₁) 1 => c.2.2) hw
    have hu1 : (piMap Δ₁.i).f 0 0 rfl u v₁ = 0 := by
      change (Δ₁.i v₁).f 0 0 rfl (u v₁) = 0
      rw [Subsingleton.elim (u v₁) 0, map_zero]
    have hu2 : (piMap Δ₁.i).f 0 0 rfl u v₂ = 0 := by
      change (Δ₁.i v₂).f 0 0 rfl (u v₂) = 0
      rw [Subsingleton.elim (u v₂) 0, map_zero]
    have e₂ := congrFun h3 v₂
    change x v₂ = (resS k GS Gv loc M).f 0 0 rfl a v₂ - (piMap Δ₁.i).f 0 0 rfl u v₂ -
      (localCx k GS Gv loc M v₂).d (-1) 0 rfl (t v₂) at e₂
    have e₁ := congrFun h3 v₁
    change x v₁ = (resS k GS Gv loc M).f 0 0 rfl a v₁ - (piMap Δ₁.i).f 0 0 rfl u v₁ -
      (localCx k GS Gv loc M v₁).d (-1) 0 rfl (t v₁) at e₁
    have ht : ∀ v, (localCx k GS Gv loc M v).d (-1) 0 rfl (t v) = 0 := fun v => rfl
    rw [ht, sub_zero] at e₁ e₂
    have hx₂ : x v₂ = 0 := by
      rw [hx]
      change -(Pi.single (M := fun v => (localCx k GS Gv loc M v).X 0) v₁ w₁ v₂) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hne), neg_zero]
    have hx₁ : x v₁ = -w₁ := by
      rw [hx]
      change -(Pi.single (M := fun v => (localCx k GS Gv loc M v).X 0) v₁ w₁ v₁) = -w₁
      rw [Pi.single_eq_same]
    rw [hu2, sub_zero, hx₂] at e₂
    rw [hu1, sub_zero, hx₁] at e₁
    have h0 := res_zero_of_res_zero (Gv := Gv) (loc := loc) a v₂ v₁ e₂.symm
    rw [← e₁, neg_eq_zero] at h0
    exact hιu h0

/-- **No `H¹` left inverse of the comparison** (PROVED): under the hypotheses of
`condMap_not_injective_H1`, no maps `ψ : C_{Δ₂} → C_{Δ₁}` commuting with `d⁰` are a left inverse
of `condMap` on degree-one cohomology. -/
theorem no_H1_inverse (v₁ v₂ : ι) (hne : v₁ ≠ v₂)
    (h₁ : Subsingleton ((Δ₁.U v₁).X 0)) (h₂ : Subsingleton ((Δ₁.U v₂).X 0))
    (u₁ : (Δ₂.U v₁).X 0) (hdu : (Δ₂.U v₁).d 0 1 rfl u₁ = 0)
    (hιu : (Δ₂.i v₁).f 0 0 rfl u₁ ≠ 0)
    (ψ : ∀ n, (selCx (selData k GS Gv loc M Δ₂)).X n →ₗ[k] (selCx (selData k GS Gv loc M Δ₁)).X n)
    (hd : ∀ x, ψ 1 ((selCx (selData k GS Gv loc M Δ₂)).d 0 1 rfl x) =
      (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl (ψ 0 x))
    (hleft : ∀ z : (selCx (selData k GS Gv loc M Δ₁)).X 1,
      (selCx (selData k GS Gv loc M Δ₁)).d 1 2 rfl z = 0 →
        ∃ y, ψ 1 ((condMap Δ₁ Δ₂ F hF).f 1 1 rfl z) =
          z + (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl y) : False := by
  obtain ⟨z, hz, ⟨y, hy⟩, hnot⟩ := condMap_not_injective_H1 Δ₁ Δ₂ F hF v₁ v₂ hne h₁ h₂ u₁ hdu hιu
  obtain ⟨y', hy'⟩ := hleft z hz
  rw [hy, hd] at hy'
  exact hnot ⟨ψ 0 y - y', by rw [map_sub, hy', add_sub_cancel_right]⟩

end Generic

/-! ### Lane E2's `OrthComparisonInverse` -/

section Dual

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3E2.DualPres
open ZInQ.Manuscript.RC.Limits (SplitInclusion)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {Δ' Δ'' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1)}
  {EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j))}

/-- **Lane E2's `OrthComparisonInverse` is uninhabited** (PROVED; the GLUE asks for the inverse at
the finite stage, which the text takes only at the localization of tex 3736–3753): for any index
`p` and any nonzero `m ∈ M` fixed by `G_{K_w}` at `w = place (p, false)`, there is no
`OrthComparisonInverse` (whatever `φo`). With `T = {p}`, the comparison passes from zero to full
at both places above `p`, and the constant cochain `m` is a nonzero cocycle of the full
condition; `no_H1_inverse` applies to `ψ_T`, `hd`, `hleft`. -/
theorem not_orthComparisonInverse (p : ι) (m : M) (hm : m ≠ 0)
    (hinv : ∀ g : Gloc K (place (p, false)).1, locMap K S (place (p, false)).1 g • m = m) :
    ¬ Nonempty (OrthComparisonInverse K S₀ S k M Δ' Δ'' place X EU) := by
  classical
  rintro ⟨Ψ⟩
  have hb : decide ((p, false).1 ∈ ({p} : Finset ι)) = true := by simp
  have key₁ : ∀ b : Bool, b = true → ∀ j, Subsingleton ((dcondCxS K S k place X j b).X 0) := by
    rintro b rfl j
    exact (inferInstance : Subsingleton PUnit)
  have hb' : decide ((p, true).1 ∈ ({p} : Finset ι)) = true := by simp
  have key₂ : ∀ b : Bool, b = true →
      ∃ u : (condCxS K S k M place X (p, false) b).X 0,
        (condCxS K S k M place X (p, false) b).d 0 1 rfl u = 0 ∧
          (condιS K S k M place X EU (p, false) b).f 0 0 rfl u ≠ 0 := by
    rintro b rfl
    refine ⟨constCochain (G := Gloc K (place (p, false)).1) (k := k)
      (M := ResMod (locMap K S (place (p, false)).1) M) m, ?_, ?_⟩
    · exact (contD_zero_eq_zero_iff _).2 fun g => hinv g
    · intro h
      apply hm
      change constCochain (G := Gloc K (place (p, false)).1) (k := k)
        (M := ResMod (locMap K S (place (p, false)).1) M) m = 0 at h
      have := congrArg (fun c : contCochain k (Gloc K (place (p, false)).1)
        (ResMod (locMap K S (place (p, false)).1) M) 0 =>
          cfun (k := k) (G := Gloc K (place (p, false)).1)
            (M := ResMod (locMap K S (place (p, false)).1) M) c default) h
      exact this
  obtain ⟨u₁, hdu, hιu⟩ := key₂ _ hb
  exact no_H1_inverse (dpresCondS K S₀ S k M Δ' place X EU {p})
    (ZInQ.Manuscript.RC.Wiring.presCondS K S₀ S k M Δ'' place X EU {p})
    (presComparison K S₀ S k M Δ' Δ'' place X EU Ψ.φo {p})
    (presComparison_compat K S₀ S k M Δ' Δ'' place X EU Ψ.φo Ψ.φo_compat {p})
    (.inr (p, false)) (.inr (p, true)) (by simp) (key₁ _ hb _) (key₁ _ hb' _) u₁ hdu hιu
    (Ψ.ψ {p}) (Ψ.hd {p}) (Ψ.hleft {p})

end Dual

end ZInQ.Contrib.CloudB3E1Torsion

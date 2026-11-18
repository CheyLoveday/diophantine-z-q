import ZInQKernel.Contrib.RC53Assist.StrictSymm.DegreeTwo
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerCone
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericWiring

/-!
# Retained full local conditions

The strict and relaxed conditions at every old place are the same retained
condition. At the new derivative place the strict condition is the actual
bounded subcomplex. This gives a compatible reverse isotropy homotopy: at an old
place use the retained identification without swapping the arguments of the
given homotopy; at the new place the relevant strict terms are zero. For genuine
truncated continuous-cochain isotropy data this proves strict orthogonality and
descent of the original traced cup formula, including non-discrete coefficients.
No old-place degree bound or contraction is needed for this descent statement.

The authorized contraction reduction is proved separately. Replace specified
full old conditions by zero only with a specified contracting homotopy. The
forward comparison retains the global and local components, pulls back the given
isotropy homotopy, and preserves the traced cup product exactly. The corrected
projection is (a,u,x) ↦ (a,p u,x + ι h u); the lifted homotopy is (0,h u,0).
These give homotopy equivalences of the actual Selmer complexes. The reduced
actual switch has zero strict degree-two term, so both strict-symmetry conventions
hold for the pullback datum.

The remaining arithmetic input to this reduction is the retained all-degree
comparison from the actual full continuous cochains to the actual tame model.
The displayed contraction is transported from that comparison, using the actual
Frobenius and inertia actions. Primitive quadratic inertia gives the unit
inertia-minus-one operator when two is nonzero in the test field. Literal
all-cochain strict symmetry of the original chosen homotopy is not asserted.

Manuscript support: 5055–5061 for retention, 2813–2815 for the authorized
replacement, 3731–3735 and 3776–3779 for the two contraction formulas.
No external arithmetic fact or new printed premise is introduced.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

open Classical

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull

open CategoryTheory NumberField IsDedekindDomain
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.RC53Assist.StrictLocal

section LocalAlgebra

variable {k : Type} [Field k]

/-- A contracting homotopy, written with the degree relations explicit. -/
structure Contraction (U : GCx k) where
  h : ∀ i j : ℤ, j + 1 = i → U.X i →ₗ[k] U.X j
  identity : ∀ (i j l : ℤ) (hj : j + 1 = i) (hl : i + 1 = l) (x : U.X i),
    U.d j i hj (h i j hj x) + h l i hl (U.d i l hl x) = x

/-- A contracting homotopy of cochain complexes gives the relation-indexed contraction. -/
def Contraction.ofHomotopy {U : GCx k} (H : Homotopy (𝟙 U.toCC) 0) : Contraction U where
  h i j _ := (H.hom i j).hom
  identity i j l hj hl x := by
    have e := congrArg (fun f => f.hom x) (H.comm i)
    rw [dNext_eq _ hl, prevD_eq _ hj] at e
    change x = (show U.X i from (H.hom l i).hom ((U.toCC.d i l).hom x)) +
      (show U.X i from (U.toCC.d j i).hom ((H.hom i j).hom x)) + 0 at e
    rw [GCx.toCC_d_hom U i l hl x,
      GCx.toCC_d_hom U j i hj ((H.hom i j).hom x), add_zero] at e
    exact (add_comm _ _).trans e.symm

end LocalAlgebra

section GenuineFamily

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- The actual switch family on the genuine local continuous cochains. -/
abbrev localSwitch (q : Places K S)
    (old : ∀ v, SubFam (galLv (k := k) K S M v)) (side : ∀ v : Places K S, Set (Gloc K v.1)) :=
  switchFamK k (gGvK K S) (gMvK K S M) q old side

/-- The genuine strict/relaxed switch, with its actual quotient and coordinates. -/
def actualSwitch (q : Places K S)
    (old : ∀ v, SubFam (galLv (k := k) K S M v)) (side : ∀ v : Places K S, Set (Gloc K v.1))
    (eR : (localSwitch q old side).Wrel.toCC.homology 1 ≃ₗ[k]
      ((Fin 2 → k) × (Fin 2 → k))) : GenuineSwitch K S k M where
  ΔR := galCond K S M (localSwitch q old side).rel
  US v := ((localSwitch q old side).str v).cx
  φ v := SubFam.inclLe (derivHsrK (localSwitch q old side) v)
  W := (localSwitch q old side).Wrel
  g := quotMk (localSwitch q old side).fr
  hfg n u := quotMk_comp_apply (localSwitch q old side).fr n u
  φ_inj n := by
    intro x y h
    funext v
    exact SubFam.inclLe_injective (derivHsrK (localSwitch q old side) v) n (congrFun h v)
  g_surj := quotMk_surjective (localSwitch q old side).fr
  ex n u hu := (quotMk_eq_zero_iff (localSwitch q old side).fr n u).1 hu
  eR := eR

/-- The precise data permitting removal of retained full conditions. -/
structure RetainedFullReduction (q : Places K S)
    (old : ∀ v, SubFam (galLv (k := k) K S M v)) (F : Set (Places K S)) where
  new_not_removed : q ∉ F
  full : ∀ v, v ∈ F → old v = SubFam.top (galLv (k := k) K S M v)
  contraction : ∀ v, v ∈ F → Contraction (old v).cx
  bounded : ∀ v, v ≠ q → v ∉ F → DegreeTwoZero (old v).cx

variable (q : Places K S)
  (old : ∀ v, SubFam (galLv (k := k) K S M v))
  (side : ∀ v : Places K S, Set (Gloc K v.1))
  (eR : (localSwitch q old side).Wrel.toCC.homology 1 ≃ₗ[k]
    ((Fin 2 → k) × (Fin 2 → k)))
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)

/-- The forward isotropy datum is for the actual strict and relaxed switch conditions. -/
abbrev ActualIsotropy := GaloisTruncIsotropyData K S k β hβ
  (actualSwitch q old side eR).ΔS (actualSwitch q old side eR).ΔR

/-- The original homotopy with its strict domain written explicitly. -/
def forwardH (I : ActualIsotropy q old side eR β hβ) (v : Places K S)
    (i j l : ℤ) (h : i + j = l + 1) :
    ((actualSwitch q old side eR).US v).X i →ₗ[k]
      ((actualSwitch q old side eR).ΔR.U v).X j →ₗ[k] (galLv (k := k) K S T v).X l :=
  I.h v i j l h

/-- The retained composite strict-to-local map, with the strict domain explicit. -/
def strictLocalMap (v : Places K S) :
    GHom ((actualSwitch q old side eR).US v) (galLv (k := k) K S M v) :=
  (actualSwitch q old side eR).ΔS.i v

/-- The strict-symmetry deficit in the local cup-one convention. -/
def strictDeficit (I : ActualIsotropy q old side eR β hβ) (c : k) (v : Places K S)
    (s : ((actualSwitch q old side eR).US v).X 2)
    (t : ((actualSwitch q old side eR).US v).X 1) :
    (galLv (k := k) K S T v).X 2 :=
  forwardH q old side eR β hβ I v 2 1 2 rfl s (((actualSwitch q old side eR).φ v).f 1 1 rfl t) -
    c • forwardH q old side eR β hβ I v 1 2 2 rfl t (((actualSwitch q old side eR).φ v).f 2 2 rfl s) -
    localCupOne21 k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β (continuous_pairing β) v
      ((strictLocalMap q old side eR v).f 2 2 rfl s)
      ((strictLocalMap q old side eR v).f 1 1 rfl t)

/-- Cyclic strict symmetry uses closed cochains in both slots, not arbitrary cochains. -/
def CyclicStrictSymm (I : ActualIsotropy q old side eR β hβ) (c : k) : Prop :=
  ∀ (v : Places K S) (s : ((actualSwitch q old side eR).US v).X 2)
    (t : ((actualSwitch q old side eR).US v).X 1),
    ((actualSwitch q old side eR).US v).d 2 3 rfl s = 0 →
    ((actualSwitch q old side eR).US v).d 1 2 rfl t = 0 →
    strictDeficit q old side eR β hβ I c v s t ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl)

/-- A boundary in the strict degree-two slot has the required cup-one symmetry
against any strict cocycle, for the given genuine isotropy datum. -/
theorem strictSymmetry_of_boundary (I : ActualIsotropy q old side eR β hβ) (c : k)
    (hc : ∀ a b : M, β a b = c • β b a) (v : Places K S)
    (s : ((actualSwitch q old side eR).US v).X 2)
    (t r : ((actualSwitch q old side eR).US v).X 1)
    (hr : ((actualSwitch q old side eR).US v).d 1 2 rfl r = s)
    (ht : ((actualSwitch q old side eR).US v).d 1 2 rfl t = 0) :
    strictDeficit q old side eR β hβ I c v s t ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) := by
  let X := actualSwitch q old side eR
  have hφt : (X.ΔR.U v).d 1 2 rfl ((X.φ v).f 1 1 rfl t) = 0 := by
    rw [← (X.φ v).comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  have hφr : (X.ΔR.U v).d 1 2 rfl ((X.φ v).f 1 1 rfl r) =
      (X.φ v).f 2 2 rfl s := by
    rw [← (X.φ v).comm 1 2 1 2 rfl rfl rfl rfl, hr]
  have h₁ := I.isotropy₂ v 1 2 1 2 rfl rfl rfl r ((X.φ v).f 1 1 rfl t)
  have h₂ := I.isotropy₂ v 1 2 1 2 rfl rfl rfl t ((X.φ v).f 1 1 rfl r)
  change forwardH q old side eR β hβ I v 2 1 2 rfl ((X.US v).d 1 2 rfl r) ((X.φ v).f 1 1 rfl t) +
    sgn 1 • forwardH q old side eR β hβ I v 1 2 2 rfl r ((X.ΔR.U v).d 1 2 rfl ((X.φ v).f 1 1 rfl t)) -
    (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
      ((strictLocalMap q old side eR v).f 1 1 rfl r) ((strictLocalMap q old side eR v).f 1 1 rfl t) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) at h₁
  change forwardH q old side eR β hβ I v 2 1 2 rfl ((X.US v).d 1 2 rfl t) ((X.φ v).f 1 1 rfl r) +
    sgn 1 • forwardH q old side eR β hβ I v 1 2 2 rfl t ((X.ΔR.U v).d 1 2 rfl ((X.φ v).f 1 1 rfl r)) -
    (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
      ((strictLocalMap q old side eR v).f 1 1 rfl t) ((strictLocalMap q old side eR v).f 1 1 rfl r) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) at h₂
  rw [hr, hφt, map_zero, smul_zero, add_zero] at h₁
  rw [ht, hφr, LinearMap.map_zero₂, zero_add, sgn_one, neg_one_zsmul] at h₂
  have hsum := (LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl)).add_mem h₁
    ((LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl)).smul_mem c h₂)
  have hcup := localPair_comm_homotopy k (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    β hβ (continuous_pairing β) c hc v
    ((strictLocalMap q old side eR v).f 1 1 rfl r) ((strictLocalMap q old side eR v).f 1 1 rfl t)
  have hιr : (galLv (k := k) K S M v).d 1 2 rfl ((strictLocalMap q old side eR v).f 1 1 rfl r) =
      (strictLocalMap q old side eR v).f 2 2 rfl s := by
    rw [← (strictLocalMap q old side eR v).comm 1 2 1 2 rfl rfl rfl rfl, hr]
  have hιt : (galLv (k := k) K S M v).d 1 2 rfl ((strictLocalMap q old side eR v).f 1 1 rfl t) = 0 := by
    rw [← (strictLocalMap q old side eR v).comm 1 2 1 2 rfl rfl rfl rfl, ht, map_zero]
  rw [hιr, hιt, map_zero, add_zero] at hcup
  have hd : (galLv (k := k) K S T v).d 1 2 rfl
      (localCupOne11 k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β (continuous_pairing β) v
        ((strictLocalMap q old side eR v).f 1 1 rfl r) ((strictLocalMap q old side eR v).f 1 1 rfl t)) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) := ⟨_, rfl⟩
  have htotal := (LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl)).add_mem hsum hd
  have he :
      (forwardH q old side eR β hβ I v 2 1 2 rfl s ((X.φ v).f 1 1 rfl t) -
        (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
          ((strictLocalMap q old side eR v).f 1 1 rfl r) ((strictLocalMap q old side eR v).f 1 1 rfl t)) +
      c • (-forwardH q old side eR β hβ I v 1 2 2 rfl t ((X.φ v).f 2 2 rfl s) -
        (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
          ((strictLocalMap q old side eR v).f 1 1 rfl t) ((strictLocalMap q old side eR v).f 1 1 rfl r)) +
      (galLv (k := k) K S T v).d 1 2 rfl
        (localCupOne11 k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β (continuous_pairing β) v
          ((strictLocalMap q old side eR v).f 1 1 rfl r) ((strictLocalMap q old side eR v).f 1 1 rfl t)) =
      strictDeficit q old side eR β hβ I c v s t := by
    dsimp only [strictDeficit]
    simp only [smul_sub, smul_neg]
    linear_combination (norm := module) -hcup
  exact he ▸ htotal

/-- The authorized contractions give cyclic symmetry for the original switch,
without changing its full complexes or its forward isotropy homotopy. -/
theorem actual_cyclicStrictSymm {F : Set (Places K S)}
    (R : RetainedFullReduction q old F) (I : ActualIsotropy q old side eR β hβ)
    (c : k) (hc : ∀ a b : M, β a b = c • β b a) :
    CyclicStrictSymm q old side eR β hβ I c := by
  intro v s t hs ht
  by_cases hv : v = q
  · subst v
    have hz : DegreeTwoZero ((actualSwitch q old side eR).US q) := by
      change DegreeTwoZero ((switchStrK k (gGvK K S) (gMvK K S M) q old q).cx)
      rw [switchStr_qK]
      change ∀ x : (⊥ : Submodule k ((galLv (k := k) K S M q).X 2)), x = 0
      exact fun x => Subtype.ext ((Submodule.mem_bot k).1 x.2)
    rw [hz s]
    simp only [strictDeficit, map_zero, LinearMap.zero_apply, smul_zero, sub_zero]
    exact Submodule.zero_mem _
  · have hU : (actualSwitch q old side eR).US v = (old v).cx := by
      change (switchStrK k (gGvK K S) (gMvK K S M) q old v).cx = (old v).cx
      rw [switchStr_neK q old hv]
    by_cases hF : v ∈ F
    · have H : Contraction ((actualSwitch q old side eR).US v) := hU.symm ▸ R.contraction v hF
      have hr := H.identity 2 1 3 rfl rfl s
      rw [hs, map_zero, add_zero] at hr
      exact strictSymmetry_of_boundary q old side eR β hβ I c hc v s t (H.h 2 1 rfl s) hr ht
    · have hz : DegreeTwoZero ((actualSwitch q old side eR).US v) := hU.symm ▸ R.bounded v hv hF
      rw [hz s]
      simp only [strictDeficit, map_zero, LinearMap.zero_apply, smul_zero, sub_zero]
      exact Submodule.zero_mem _

end GenuineFamily

section RetainedReverse

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (q : Places K S) (old : ∀ v, SubFam (galLv (k := k) K S M v))
  (side : ∀ v : Places K S, Set (Gloc K v.1))
  (eR : (localSwitch q old side).Wrel.toCC.homology 1 ≃ₗ[k]
    ((Fin 2 → k) × (Fin 2 → k)))

/-- The inverse of strict-to-relaxed at a retained place: both are the same old condition. -/
def oldBackMap (v : Places K S) (hv : v ≠ q) :
    GHom ((actualSwitch q old side eR).ΔR.U v) ((actualSwitch q old side eR).US v) :=
  SubFam.inclLe (by
    intro n
    change (switchRelK k (gGvK K S) (gMvK K S M) q old v).S n ≤
      (switchStrK k (gGvK K S) (gMvK K S M) q old v).S n
    rw [switchRel_neK q old hv, switchStr_neK q old hv])

/-- The retained inverse is literally inverse to the retained inclusion. -/
theorem oldBackMap_leftInv (v : Places K S) (hv : v ≠ q) (n : ℤ)
    (x : ((actualSwitch q old side eR).US v).X n) :
    (oldBackMap q old side eR v hv).f n n rfl
      (((actualSwitch q old side eR).φ v).f n n rfl x) = x :=
  Subtype.ext rfl

/-- The new strict derivative condition has no degree-one cochains. -/
theorem actual_strict_one_zero (x : ((actualSwitch q old side eR).US q).X 1) : x = 0 := by
  apply Subtype.ext
  have hx := x.2
  change (x.1 : (galLv (k := k) K S M q).X 1) ∈
    (switchStrK k (gGvK K S) (gMvK K S M) q old q).S 1 at hx
  rw [switchStr_qK] at hx
  exact (Submodule.mem_bot k).1 hx

/-- The new strict derivative condition has no degree-two cochains. -/
theorem actual_strict_two_zero (x : ((actualSwitch q old side eR).US q).X 2) : x = 0 := by
  apply Subtype.ext
  have hx := x.2
  change (x.1 : (galLv (k := k) K S M q).X 2) ∈
    (switchStrK k (gGvK K S) (gMvK K S M) q old q).S 2 at hx
  rw [switchStr_qK] at hx
  exact (Submodule.mem_bot k).1 hx

variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)

/-- Reverse the order of the condition complexes by their retained identification.
This keeps the given homotopy in its original argument order. -/
def retainedReverse (I : ActualIsotropy q old side eR β hβ)
    (v : Places K S) (i j l : ℤ) (h : i + j = l + 1) :
    ((actualSwitch q old side eR).ΔR.U v).X i →ₗ[k]
      ((actualSwitch q old side eR).US v).X j →ₗ[k] (galLv (k := k) K S T v).X l :=
  if hv : v = q then 0 else
    (forwardH q old side eR β hβ I v i j l h).compl₁₂ ((oldBackMap q old side eR v hv).f i i rfl)
      (((actualSwitch q old side eR).φ v).f j j rfl)

/-- At the new place the retained reverse homotopy is zero in every bidegree. -/
theorem retainedReverse_at_new (I : ActualIsotropy q old side eR β hβ)
    (i j l : ℤ) (h : i + j = l + 1) :
    retainedReverse q old side eR β hβ I q i j l h = 0 :=
  dite_eq_left rfl

/-- The product of the retained reverse homotopies. -/
def retainedReversePi (I : ActualIsotropy q old side eR β hβ)
    (i j l : ℤ) (h : i + j = l + 1) :
    (piCx (actualSwitch q old side eR).ΔR.U).X i →ₗ[k]
      (piCx (actualSwitch q old side eR).US).X j →ₗ[k]
      (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T).X l :=
  LinearMap.mk₂ k (fun u t v => retainedReverse q old side eR β hβ I v i j l h (u v) (t v))
    (fun u u' t => by
      funext v
      exact LinearMap.map_add₂ (retainedReverse q old side eR β hβ I v i j l h) (u v) (u' v) (t v))
    (fun c u t => by
      funext v
      exact LinearMap.map_smul₂ (retainedReverse q old side eR β hβ I v i j l h) c (u v) (t v))
    (fun u t t' => by
      funext v
      exact map_add (retainedReverse q old side eR β hβ I v i j l h (u v)) (t v) (t' v))
    (fun c u t => by
      funext v
      exact map_smul (retainedReverse q old side eR β hβ I v i j l h (u v)) c (t v))

/-- Compatibility on strict cochains is exact for the retained reverse construction. -/
theorem retainedReverse_compat (I : ActualIsotropy q old side eR β hβ) (v : Places K S)
    (s : ((actualSwitch q old side eR).US v).X 2)
    (t : ((actualSwitch q old side eR).US v).X 1) :
    forwardH q old side eR β hβ I v 2 1 2 rfl s (((actualSwitch q old side eR).φ v).f 1 1 rfl t) =
      retainedReverse q old side eR β hβ I v 2 1 2 rfl
        (((actualSwitch q old side eR).φ v).f 2 2 rfl s) t := by
  by_cases hv : v = q
  · subst v
    rw [actual_strict_two_zero q old side eR s]
    simp only [retainedReverse_at_new, LinearMap.zero_apply, LinearMap.map_zero₂]
  · rw [retainedReverse, dite_eq_right hv, LinearMap.compl₁₂_apply,
      oldBackMap_leftInv q old side eR v hv 2 s]

/-- The given forward isotropy identity is the reverse identity at every retained place.
At the new place the strict degree-one cochain is zero. -/
theorem retainedReverse_isotropy (I : ActualIsotropy q old side eR β hβ) (v : Places K S)
    (u : ((actualSwitch q old side eR).ΔR.U v).X 1)
    (t : ((actualSwitch q old side eR).US v).X 1) :
    retainedReverse q old side eR β hβ I v 2 1 2 rfl
        (((actualSwitch q old side eR).ΔR.U v).d 1 2 rfl u) t +
      sgn 1 • retainedReverse q old side eR β hβ I v 1 2 2 rfl u
        (((actualSwitch q old side eR).US v).d 1 2 rfl t) -
      (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
        (((actualSwitch q old side eR).ΔR.i v).f 1 1 rfl u)
        ((strictLocalMap q old side eR v).f 1 1 rfl t) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) := by
  let X := actualSwitch q old side eR
  by_cases hv : v = q
  · subst v
    rw [actual_strict_one_zero q old side eR t]
    simp only [retainedReverse_at_new, LinearMap.zero_apply, map_zero,
      smul_zero, zero_add, sub_zero]
    exact Submodule.zero_mem _
  · have hiso := I.isotropy₂ v 1 2 1 2 rfl rfl rfl
      ((oldBackMap q old side eR v hv).f 1 1 rfl u) ((X.φ v).f 1 1 rfl t)
    change forwardH q old side eR β hβ I v 2 1 2 rfl ((X.US v).d 1 2 rfl
        ((oldBackMap q old side eR v hv).f 1 1 rfl u)) ((X.φ v).f 1 1 rfl t) +
      sgn 1 • forwardH q old side eR β hβ I v 1 2 2 rfl ((oldBackMap q old side eR v hv).f 1 1 rfl u)
        ((X.ΔR.U v).d 1 2 rfl ((X.φ v).f 1 1 rfl t)) -
      (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
        ((X.ΔR.i v).f 1 1 rfl u) ((strictLocalMap q old side eR v).f 1 1 rfl t) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) at hiso
    rw [← (oldBackMap q old side eR v hv).comm 1 2 1 2 rfl rfl rfl rfl,
      ← (X.φ v).comm 1 2 1 2 rfl rfl rfl rfl] at hiso
    simpa only [retainedReverse, dite_eq_right hv, LinearMap.compl₁₂_apply] using hiso

/-- The actual retained switch admits a compatible reverse isotropy datum.
No contraction, coefficient symmetry or vanishing at old places is required. -/
def actual_reverseIsotropy (I : ActualIsotropy q old side eR β hβ) :
    ZInQ.Contrib.CloudB3RC53.Hsw.ReverseIsotropy (actualSwitch q old side eR).toQuasi.D
      (piCx (actualSwitch q old side eR).US) (piMap (actualSwitch q old side eR).φ)
      (galoisPairDataT K S k β hβ (actualSwitch q old side eR).ΔS
        (actualSwitch q old side eR).ΔR I) where
  h11 := 0
  h21 := (retainedReversePi q old side eR β hβ I 2 1 2 rfl).compr₂
    (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) 2).mkQ
  h12 := (retainedReversePi q old side eR β hβ I 1 2 2 rfl).compr₂
    (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) 2).mkQ
  iso u t := by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero, zero_add]
    exact mkQ_add_sgn_one _
      (retainedReversePi q old side eR β hβ I 2 1 2 rfl
        ((piCx (actualSwitch q old side eR).ΔR.U).d 1 2 rfl u) t)
      (retainedReversePi q old side eR β hβ I 1 2 2 rfl u
        ((piCx (actualSwitch q old side eR).US).d 1 2 rfl t))
      ((localSumPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ (continuous_pairing β)).P 1 1 2 rfl
        ((piMap (actualSwitch q old side eR).ΔR.i).f 1 1 rfl u)
        ((piMap (actualSwitch q old side eR).ΔR.i).f 1 1 rfl
          ((piMap (actualSwitch q old side eR).φ).f 1 1 rfl t)))
      (mem_range_localSum _ fun v => by
        change retainedReverse q old side eR β hβ I v 2 1 2 rfl
            (((actualSwitch q old side eR).ΔR.U v).d 1 2 rfl (u v)) (t v) -
          retainedReverse q old side eR β hβ I v 1 2 2 rfl (u v)
            (((actualSwitch q old side eR).US v).d 1 2 rfl (t v)) -
          (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P 1 1 2 rfl
            (((actualSwitch q old side eR).ΔR.i v).f 1 1 rfl (u v))
            ((strictLocalMap q old side eR v).f 1 1 rfl (t v)) ∈
          LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl)
        have h := retainedReverse_isotropy q old side eR β hβ I v (u v) (t v)
        simpa only [sgn_one, neg_one_zsmul, sub_eq_add_neg] using h)
  compat s t := by
    change (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) 2).mkQ
        (fun v => forwardH q old side eR β hβ I v 2 1 2 rfl (s v)
          (((actualSwitch q old side eR).φ v).f 1 1 rfl (t v))) =
      (truncSub (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T) 2).mkQ
        (retainedReversePi q old side eR β hβ I 2 1 2 rfl
          ((piMap (actualSwitch q old side eR).φ).f 2 2 rfl s) t)
    congr 1
    funext v
    exact retainedReverse_compat q old side eR β hβ I v (s v) (t v)

/-- Strict orthogonality of the original traced pairing, with full conditions retained. -/
theorem actual_strictOrth (I : ActualIsotropy q old side eR β hβ)
    (tr : (galoisCompactTT K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).d 2 3 rfl z) = 0) :
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictOrth (actualSwitch q old side eR).toQuasi.D
      (piCx (actualSwitch q old side eR).US) (piMap (actualSwitch q old side eR).φ)
      (galoisPairDataT K S k β hβ (actualSwitch q old side eR).ΔS
        (actualSwitch q old side eR).ΔR I) tr :=
  ZInQ.Contrib.CloudB3RC53.Hsw.strictOrth_of_reverseIsotropy _ _ _ _ tr htr
    (actual_reverseIsotropy q old side eR β hβ I)

/-- The original switch cup product descends to its retained quotient coordinates. -/
theorem actual_exists_residuePairing (I : ActualIsotropy q old side eR β hβ)
    (tr : (galoisCompactTT K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galoisCompactTT K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).d 2 3 rfl z) = 0) :
    ∃ P, ZInQ.Contrib.CloudB3RC53.Hsw.ResiduePairing (actualSwitch q old side eR).toQuasi
      (piCx (actualSwitch q old side eR).US) (piMap (actualSwitch q old side eR).φ)
      (galoisPairDataT K S k β hβ (actualSwitch q old side eR).ΔS
        (actualSwitch q old side eR).ΔR I) tr P :=
  ZInQ.Contrib.CloudB3RC53.Hsw.exists_residuePairing_of_reverseIsotropy _ _ _ _ tr
    (actualSwitch q old side eR).hfg (actualSwitch q old side eR).φ_inj
    (actualSwitch q old side eR).g_surj (actualSwitch q old side eR).ex htr
    (actual_reverseIsotropy q old side eR β hβ I)

/-- Descent for the manuscript's original, unprojected cup formula and its given trace. -/
theorem actual_original_residuePairing (I : ActualIsotropy q old side eR β hβ)
    (tr0 : (coneCx (galoisPairDataTrunc K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).resE).X 3 →ₗ[k] k)
    (htr0 : ∀ z, tr0 ((coneCx (galoisPairDataTrunc K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).resE).d 2 3 rfl z) = 0) :
    let X := actualSwitch q old side eR
    let Q := galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I
    ∃ P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : X.toQuasi.D.U.X 1) (s : (piCx X.US).X 2)
        (_ht : X.toQuasi.D.U.d 1 2 rfl t = 0)
        (_hu : X.toQuasi.D.U.d 1 2 rfl u = (piMap X.φ).f 2 2 rfl s)
        (ct cu : LinearMap.ker (X.W.d 1 2 rfl))
        (_hct : ct.1 = X.g.f 1 1 rfl t) (_hcu : cu.1 = X.g.f 1 1 rfl u),
        tr0 (selCupFunT Q 2 1 3 rfl ((0 : X.toQuasi.D.G.X 2), s,
            -(X.toQuasi.D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : X.toQuasi.D.G.X 1), t, (0 : X.toQuasi.D.L.X (1 - 1)))) =
          P (X.eR (cls1 X.W ct)) (X.eR (cls1 X.W cu)) := by
  dsimp only
  let X := actualSwitch q old side eR
  let Q := galoisPairDataTrunc K S k β hβ X.ΔS X.ΔR I
  exact ZInQ.Contrib.CloudB3RC53.Hsw.exists_residuePairing_trunc X.toQuasi
    (piCx X.US) (piMap X.φ) Q tr0 htr0 X.hfg X.φ_inj X.g_surj X.ex
    (actual_strictOrth q old side eR β hβ I (Q.trT tr0 htr0) (Q.trT_kills tr0 htr0))

end RetainedReverse

section ErasureAlgebra

variable {k : Type} [Field k] {V : Type} {Lv : V → GCx k}

/-- The zero subcomplex of a given ambient complex. -/
def zeroSub (L : GCx k) : SubFam L where
  S _ := ⊥
  hd i j h x hx := by
    change L.d i j h x ∈ (⊥ : Submodule k (L.X j))
    rw [(Submodule.mem_bot k).1 hx, map_zero]
    exact Submodule.zero_mem _

/-- Erase just the specified conditions, retaining every other condition literally. -/
def eraseFull (F : Set V) (A : ∀ v, SubFam (Lv v)) (v : V) : SubFam (Lv v) :=
  if v ∈ F then zeroSub (Lv v) else A v

/-- The forward comparison from the reduced conditions to the original ones. -/
def eraseInclusion (F : Set V) (A : ∀ v, SubFam (Lv v)) :
    GHom (piCx fun v => (eraseFull F A v).cx) (piCx fun v => (A v).cx) :=
  piMap fun v => SubFam.inclLe (by
    intro n
    unfold eraseFull
    split_ifs
    · exact bot_le
    · exact le_rfl)

/-- The projection which forgets the specified conditions. -/
def eraseProjectionLin (F : Set V) (A : ∀ v, SubFam (Lv v)) (n : ℤ) :
    (piCx fun v => (A v).cx).X n →ₗ[k] (piCx fun v => (eraseFull F A v).cx).X n where
  toFun x v := ⟨if v ∈ F then 0 else (x v).1, by
    by_cases hv : v ∈ F
    · simp only [eraseFull, ite_eq_left hv]
      exact Submodule.zero_mem _
    · simp only [eraseFull, ite_eq_right hv]
      exact (x v).2⟩
  map_add' x y := by
    funext v
    apply Subtype.ext
    change (if v ∈ F then 0 else (x v).1 + (y v).1) =
      (if v ∈ F then 0 else (x v).1) + (if v ∈ F then 0 else (y v).1)
    by_cases hv : v ∈ F
    · simp only [ite_eq_left hv, add_zero]
    · simp only [ite_eq_right hv]
  map_smul' c x := by
    funext v
    apply Subtype.ext
    change (if v ∈ F then 0 else c • (x v).1) = c • (if v ∈ F then 0 else (x v).1)
    by_cases hv : v ∈ F
    · simp only [ite_eq_left hv, smul_zero]
    · simp only [ite_eq_right hv]

/-- The projection is a chain map. -/
def eraseProjection (F : Set V) (A : ∀ v, SubFam (Lv v)) :
    GHom (piCx fun v => (A v).cx) (piCx fun v => (eraseFull F A v).cx) where
  f i j h := by subst h; exact eraseProjectionLin F A i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    funext v
    apply Subtype.ext
    change (if v ∈ F then 0 else (Lv v).d i i₁ h₁ (x v).1) =
      (Lv v).d i i₁ h₂ (if v ∈ F then 0 else (x v).1)
    by_cases hv : v ∈ F
    · rw [ite_eq_left hv, ite_eq_left hv, map_zero]
    · rw [ite_eq_right hv, ite_eq_right hv]

/-- The reduced complex is a strict retract of the original complex. -/
theorem eraseProjection_inclusion (F : Set V) (A : ∀ v, SubFam (Lv v)) (n : ℤ)
    (x : (piCx fun v => (eraseFull F A v).cx).X n) :
    (eraseProjection F A).f n n rfl ((eraseInclusion F A).f n n rfl x) = x := by
  funext v
  apply Subtype.ext
  change (if v ∈ F then 0 else (x v).1) = (x v).1
  by_cases hv : v ∈ F
  · rw [ite_eq_left hv]
    have hx : (x v).1 = 0 := by
      have hh := (x v).2
      simpa only [eraseFull, ite_eq_left hv, zeroSub, Submodule.mem_bot] using hh
    exact hx.symm
  · rw [ite_eq_right hv]

/-- The contracting homotopy on the removed summands, zero elsewhere. -/
def eraseHomotopyLin (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) (i j : ℤ) (h : j + 1 = i) :
    (piCx fun v => (A v).cx).X i →ₗ[k] (piCx fun v => (A v).cx).X j where
  toFun x v := if hv : v ∈ F then (C v hv).h i j h (x v) else 0
  map_add' x y := by
    funext v
    change (if hv : v ∈ F then (C v hv).h i j h (x v + y v) else 0) =
      (if hv : v ∈ F then (C v hv).h i j h (x v) else 0) +
      (if hv : v ∈ F then (C v hv).h i j h (y v) else 0)
    by_cases hv : v ∈ F
    · simp only [dite_eq_left hv, map_add]
    · simp only [dite_eq_right hv, add_zero]
  map_smul' c x := by
    funext v
    change (if hv : v ∈ F then (C v hv).h i j h (c • x v) else 0) =
      c • (if hv : v ∈ F then (C v hv).h i j h (x v) else 0)
    by_cases hv : v ∈ F
    · simp only [dite_eq_left hv, map_smul]
    · simp only [dite_eq_right hv, smul_zero]

/-- The specified contraction, not acyclicity alone, gives the retraction identity. -/
theorem eraseHomotopy_identity (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) (i j l : ℤ)
    (hj : j + 1 = i) (hl : i + 1 = l) (x : (piCx fun v => (A v).cx).X i) :
    (piCx fun v => (A v).cx).d j i hj (eraseHomotopyLin F A C i j hj x) +
      eraseHomotopyLin F A C l i hl ((piCx fun v => (A v).cx).d i l hl x) =
      x - (eraseInclusion F A).f i i rfl ((eraseProjection F A).f i i rfl x) := by
  funext v
  apply Subtype.ext
  by_cases hv : v ∈ F
  · have he := congrArg Subtype.val ((C v hv).identity i j l hj hl (x v))
    change (Lv v).d j i hj ((eraseHomotopyLin F A C i j hj x v).1) +
      (eraseHomotopyLin F A C l i hl ((piCx fun v => (A v).cx).d i l hl x) v).1 =
      (x v).1 - (if v ∈ F then 0 else (x v).1)
    have h₁ : eraseHomotopyLin F A C i j hj x v = (C v hv).h i j hj (x v) := dite_eq_left hv
    have h₂ : eraseHomotopyLin F A C l i hl ((piCx fun v => (A v).cx).d i l hl x) v =
        (C v hv).h l i hl ((A v).cx.d i l hl (x v)) := dite_eq_left hv
    rw [h₁, h₂, ite_eq_left hv, sub_zero]
    exact he
  · change (Lv v).d j i hj ((eraseHomotopyLin F A C i j hj x v).1) +
      (eraseHomotopyLin F A C l i hl ((piCx fun v => (A v).cx).d i l hl x) v).1 =
      (x v).1 - (if v ∈ F then 0 else (x v).1)
    have h₁ : eraseHomotopyLin F A C i j hj x v = 0 := dite_eq_right hv
    have h₂ : eraseHomotopyLin F A C l i hl ((piCx fun v => (A v).cx).d i l hl x) v = 0 :=
      dite_eq_right hv
    rw [h₁, h₂]
    change (Lv v).d j i hj (0 : (Lv v).X j) + 0 =
      (x v).1 - (if v ∈ F then 0 else (x v).1)
    rw [map_zero, ite_eq_right hv, sub_self, add_zero]

/-- The same contraction as maps of cochain complexes. -/
def eraseHomotopyMaps (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) (i j : ℤ) :
    (piCx fun v => (A v).cx).toCC.X i ⟶ (piCx fun v => (A v).cx).toCC.X j :=
  if h : j + 1 = i then ModuleCat.ofHom (eraseHomotopyLin F A C i j h) else 0

/-- The contraction component in its supported degree. -/
theorem eraseHomotopyMaps_apply (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) (i j : ℤ) (h : j + 1 = i)
    (x : (piCx fun v => (A v).cx).X i) :
    (eraseHomotopyMaps F A C i j).hom x = eraseHomotopyLin F A C i j h x := by
  have he : eraseHomotopyMaps F A C i j = ModuleCat.ofHom (eraseHomotopyLin F A C i j h) :=
    dite_eq_left h
  exact congrArg (fun f => f.hom x) he

/-- A specified local contraction gives a homotopy from the identity to the
inclusion followed by the projection. -/
def eraseHomotopy (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) :
    Homotopy (𝟙 (piCx fun v => (A v).cx).toCC)
      (GHom.toCC (eraseProjection F A) ≫ GHom.toCC (eraseInclusion F A)) where
  hom := eraseHomotopyMaps F A C
  zero i j hij := by
    change ¬ j + 1 = i at hij
    exact dite_eq_right hij
  comm i := by
    have hi : i - 1 + 1 = i := by omega
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from hi)]
    ext x
    let U := piCx fun v => (A v).cx
    change U.X i at x
    change (x : U.X i) =
      (show U.X i from (eraseHomotopyMaps F A C (i + 1) i).hom ((U.toCC.d i (i + 1)).hom x)) +
      (show U.X i from (U.toCC.d (i - 1) i).hom ((eraseHomotopyMaps F A C i (i - 1)).hom x)) +
      (eraseInclusion F A).f i i rfl ((eraseProjection F A).f i i rfl x)
    rw [GCx.toCC_d_hom U i (i + 1) rfl x,
      eraseHomotopyMaps_apply F A C (i + 1) i rfl,
      eraseHomotopyMaps_apply F A C i (i - 1) hi,
      GCx.toCC_d_hom U (i - 1) i hi]
    have he := eraseHomotopy_identity F A C i (i - 1) (i + 1) hi rfl x
    linear_combination (norm := module) -he

/-- Removal is a homotopy equivalence with the prescribed forward comparison,
not merely an isomorphism of cohomology groups. -/
def erasureEquiv (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) :
    HomotopyEquiv (piCx fun v => (eraseFull F A v).cx).toCC (piCx fun v => (A v).cx).toCC where
  hom := GHom.toCC (eraseInclusion F A)
  inv := GHom.toCC (eraseProjection F A)
  homotopyHomInvId := Homotopy.ofEq (by
    ext i x
    exact eraseProjection_inclusion F A i x)
  homotopyInvHomId := (eraseHomotopy F A C).symm

/-- A literal family identification retains any prescribed inclusion with the
same underlying cochain maps. -/
theorem erasureEquiv_prescribed (F : Set V) (A A' : ∀ v, SubFam (Lv v))
    (hA : A' = eraseFull F A) (inc : ∀ v, GHom (A' v).cx (A v).cx)
    (hinc : ∀ (v : V) (n : ℤ) (x : (A' v).cx.X n), ((inc v).f n n rfl x).1 = x.1)
    (C : ∀ v, v ∈ F → Contraction (A v).cx) :
    ∃ e : HomotopyEquiv (piCx fun v => (A' v).cx).toCC (piCx fun v => (A v).cx).toCC,
      e.hom = GHom.toCC (piMap inc) := by
  subst A'
  refine ⟨erasureEquiv F A C, ?_⟩
  ext n x
  funext v
  apply Subtype.ext
  change (x v).1 = ((inc v).f n n rfl (x v)).1
  exact (hinc v n (x v)).symm

end ErasureAlgebra

section SelmerRetractions

variable {k : Type} [Field k]

/-- A specified deformation retract of local-condition complexes. -/
structure ConditionRetraction (U' U : GCx k) where
  inc : GHom U' U
  proj : GHom U U'
  h : ∀ i j : ℤ, j + 1 = i → U.X i →ₗ[k] U.X j
  left_inv : ∀ (i : ℤ) (x : U'.X i), proj.f i i rfl (inc.f i i rfl x) = x
  identity : ∀ (i j l : ℤ) (hj : j + 1 = i) (hl : i + 1 = l) (x : U.X i),
    U.d j i hj (h i j hj x) + h l i hl (U.d i l hl x) =
      x - inc.f i i rfl (proj.f i i rfl x)
  h_inc : ∀ (i j : ℤ) (hj : j + 1 = i) (x : U'.X i), h i j hj (inc.f i i rfl x) = 0

variable {V : Type} {Lv : V → GCx k}

/-- The specified contraction is zero on the retained inclusion. -/
theorem eraseHomotopyLin_inclusion_zero (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) (i j : ℤ) (h : j + 1 = i)
    (x : (piCx fun v => (eraseFull F A v).cx).X i) :
    eraseHomotopyLin F A C i j h ((eraseInclusion F A).f i i rfl x) = 0 := by
  funext v
  by_cases hv : v ∈ F
  · have hx : (x v).1 = 0 := by
      have hh := (x v).2
      simpa only [eraseFull, ite_eq_left hv, zeroSub, Submodule.mem_bot] using hh
    have hu : ((eraseInclusion F A).f i i rfl x) v = 0 := Subtype.ext hx
    have he : eraseHomotopyLin F A C i j h ((eraseInclusion F A).f i i rfl x) v =
        (C v hv).h i j h (((eraseInclusion F A).f i i rfl x) v) := dite_eq_left hv
    rw [he, hu, map_zero]
    rfl
  · exact dite_eq_right hv

/-- The actual inclusion, projection and contracting homotopy form a deformation retract. -/
def erasureRetraction (F : Set V) (A : ∀ v, SubFam (Lv v))
    (C : ∀ v, v ∈ F → Contraction (A v).cx) :
    ConditionRetraction (piCx fun v => (eraseFull F A v).cx) (piCx fun v => (A v).cx) where
  inc := eraseInclusion F A
  proj := eraseProjection F A
  h := eraseHomotopyLin F A C
  left_inv := eraseProjection_inclusion F A
  identity := eraseHomotopy_identity F A C
  h_inc := eraseHomotopyLin_inclusion_zero F A C

/-- A prescribed retained inclusion has the specified erasure deformation retract. -/
theorem erasureRetraction_prescribed (F : Set V) (A A' : ∀ v, SubFam (Lv v))
    (hA : A' = eraseFull F A) (inc : ∀ v, GHom (A' v).cx (A v).cx)
    (hinc : ∀ (v : V) (n : ℤ) (x : (A' v).cx.X n), ((inc v).f n n rfl x).1 = x.1)
    (C : ∀ v, v ∈ F → Contraction (A v).cx) :
    ∃ R : ConditionRetraction (piCx fun v => (A' v).cx) (piCx fun v => (A v).cx),
      R.inc = piMap inc := by
  subst A'
  refine ⟨erasureRetraction F A C, ?_⟩
  apply ghom_ext
  intro n x
  funext v
  apply Subtype.ext
  change (x v).1 = ((inc v).f n n rfl (x v)).1
  exact (hinc v n (x v)).symm

variable {U' : GCx k} (D : SelData k) (R : ConditionRetraction U' D.U)

/-- The projection of Selmer cochains includes the necessary local correction
`(a,u,x) ↦ (a,p u,x + ι h u)`. -/
def selmerProjectionLin (i : ℤ) :
    (selCx D).X i →ₗ[k] (selCx (restrictData D R.inc)).X i :=
  let u : selT D i →ₗ[k] D.U.X i :=
    LinearMap.fst k (D.U.X i) (D.L.X (i - 1)) ∘ₗ
      LinearMap.snd k (D.G.X i) (D.U.X i × D.L.X (i - 1))
  let x : selT D i →ₗ[k] D.L.X (i - 1) :=
    LinearMap.snd k (D.U.X i) (D.L.X (i - 1)) ∘ₗ
      LinearMap.snd k (D.G.X i) (D.U.X i × D.L.X (i - 1))
  (LinearMap.fst k (D.G.X i) (D.U.X i × D.L.X (i - 1))).prod
    ((R.proj.f i i rfl ∘ₗ u).prod
      (x + D.ι.f (i - 1) (i - 1) rfl ∘ₗ R.h i (i - 1) (by omega) ∘ₗ u))

/-- The corrected projection is a cochain map. -/
def selmerProjection : GHom (selCx D) (selCx (restrictData D R.inc)) where
  f i j h := by subst h; exact selmerProjectionLin D R i
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, y⟩ := c
    refine Prod.ext rfl (Prod.ext (R.proj.comm i i₁ i i₁ rfl h₁ h₂ rfl u) ?_)
    have hp : i₁ - 1 = i := by omega
    change D.res.f i (i₁ - 1) (by omega) a - D.ι.f i (i₁ - 1) (by omega) u -
        D.L.d (i - 1) (i₁ - 1) (by omega) y +
        D.ι.f (i₁ - 1) (i₁ - 1) rfl
          (R.h i₁ (i₁ - 1) (by omega) (D.U.d i i₁ h₁ u)) =
      D.res.f i (i₁ - 1) (by omega) a -
        D.ι.f (i₁ - 1) (i₁ - 1) rfl
          (R.inc.f i (i₁ - 1) (by omega) (R.proj.f i i rfl u)) -
        D.L.d (i - 1) (i₁ - 1) (by omega)
          (y + D.ι.f (i - 1) (i - 1) rfl (R.h i (i - 1) (by omega) u))
    have hinc (n m : ℤ) (hm : n = m) (z : U'.X n) :
        D.ι.f n m hm (R.inc.f n n rfl z) =
          D.ι.f m m rfl (R.inc.f n m hm z) := by
      subst hm
      rfl
    have hhom (n p p' : ℤ) (hpn : p + 1 = n) (hp'n : p' + 1 = n)
        (hpp' : p = p') (z : D.U.X n) :
        D.ι.f p p' hpp' (R.h n p hpn z) = D.ι.f p' p' rfl (R.h n p' hp'n z) := by
      subst hpp'
      rfl
    have he := congrArg (D.ι.f i (i₁ - 1) hp.symm)
      (R.identity i (i - 1) i₁ (by omega) h₁ u)
    simp only [map_add, map_sub] at he
    rw [D.ι.comm (i - 1) i (i - 1) (i₁ - 1) rfl (by omega) (by omega) hp.symm,
      hhom i₁ i (i₁ - 1) h₁ (by omega) hp.symm,
      hinc i (i₁ - 1) hp.symm] at he
    rw [map_add]
    linear_combination (norm := module) he

/-- The lifted Selmer homotopy is `(a,u,x) ↦ (0,h u,0)`. -/
def selmerHomotopyLin (i j : ℤ) (h : j + 1 = i) :
    (selCx D).X i →ₗ[k] (selCx D).X j :=
  (0 : selT D i →ₗ[k] D.G.X j).prod
    ((R.h i j h ∘ₗ LinearMap.fst k (D.U.X i) (D.L.X (i - 1)) ∘ₗ
      LinearMap.snd k (D.G.X i) (D.U.X i × D.L.X (i - 1))).prod
      (0 : selT D i →ₗ[k] D.L.X (j - 1)))

/-- The lifted homotopy as maps of cochain complexes. -/
def selmerHomotopyMaps (i j : ℤ) : (selCx D).toCC.X i ⟶ (selCx D).toCC.X j :=
  if h : j + 1 = i then ModuleCat.ofHom (selmerHomotopyLin D R i j h) else 0

/-- Evaluation in the supported degree of the lifted homotopy. -/
theorem selmerHomotopyMaps_apply (i j : ℤ) (h : j + 1 = i) (x : (selCx D).X i) :
    (selmerHomotopyMaps D R i j).hom x = selmerHomotopyLin D R i j h x := by
  have he : selmerHomotopyMaps D R i j = ModuleCat.ofHom (selmerHomotopyLin D R i j h) :=
    dite_eq_left h
  exact congrArg (fun f => f.hom x) he

/-- The contraction lifts to the Selmer complex, retaining the actual forward comparison. -/
def selmerRetractionHomotopy :
    Homotopy (𝟙 (selCx D).toCC)
      (GHom.toCC (selmerProjection D R) ≫ GHom.toCC (changeMap D R.inc)) where
  hom := selmerHomotopyMaps D R
  zero i j hij := by
    change ¬ j + 1 = i at hij
    exact dite_eq_right hij
  comm i := by
    have hi : i - 1 + 1 = i := by omega
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from hi)]
    ext c
    let W := selCx D
    change W.X i at c
    change (c : W.X i) =
      (show W.X i from (selmerHomotopyMaps D R (i + 1) i).hom ((W.toCC.d i (i + 1)).hom c)) +
      (show W.X i from (W.toCC.d (i - 1) i).hom ((selmerHomotopyMaps D R i (i - 1)).hom c)) +
      (changeMap D R.inc).f i i rfl ((selmerProjection D R).f i i rfl c)
    rw [GCx.toCC_d_hom W i (i + 1) rfl c,
      selmerHomotopyMaps_apply D R (i + 1) i rfl,
      selmerHomotopyMaps_apply D R i (i - 1) hi,
      GCx.toCC_d_hom W (i - 1) i hi]
    obtain ⟨a, u, y⟩ := c
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change a = 0 + D.G.d (i - 1) i hi (0 : D.G.X (i - 1)) + a
      simp only [map_zero, zero_add]
    · change u = R.h (i + 1) i rfl (D.U.d i (i + 1) rfl u) +
        D.U.d (i - 1) i hi (R.h i (i - 1) hi u) + R.inc.f i i rfl (R.proj.f i i rfl u)
      have he := R.identity i (i - 1) (i + 1) hi rfl u
      linear_combination (norm := module) -he
    · change y = 0 +
        (D.res.f (i - 1) (i - 1) rfl (0 : D.G.X (i - 1)) -
          D.ι.f (i - 1) (i - 1) rfl (R.h i (i - 1) hi u) -
          D.L.d (i - 1 - 1) (i - 1) (by omega) (0 : D.L.X (i - 1 - 1))) +
        (y + D.ι.f (i - 1) (i - 1) rfl (R.h i (i - 1) hi u))
      rw [map_zero, map_zero, zero_sub, sub_zero, zero_add]
      abel

/-- A specified local deformation retract gives a Selmer homotopy equivalence. -/
def selmerRetractionEquiv :
    HomotopyEquiv (selCx (restrictData D R.inc)).toCC (selCx D).toCC where
  hom := GHom.toCC (changeMap D R.inc)
  inv := GHom.toCC (selmerProjection D R)
  homotopyHomInvId := Homotopy.ofEq (by
    ext i c
    obtain ⟨a, u, y⟩ := c
    change U'.X i at u
    change D.L.X (i - 1) at y
    refine Prod.ext rfl (Prod.ext (R.left_inv i u) ?_)
    change y + D.ι.f (i - 1) (i - 1) rfl
      (R.h i (i - 1) (by omega) (R.inc.f i i rfl u)) = y
    rw [R.h_inc i (i - 1) (by omega) u, map_zero, add_zero])
  homotopyInvHomId := (selmerRetractionHomotopy D R).symm

/-- Equality of the complexes and their component maps identifies their cochain morphisms. -/
theorem ghomHEq_of_components {A A' B : GCx k} (hA : A = A')
    {f : GHom A B} {g : GHom A' B} (hf : HEq f.f g.f) : HEq f g := by
  subst A'
  obtain ⟨ff, pf⟩ := f
  obtain ⟨fg, pg⟩ := g
  have hfg : ff = fg := eq_of_heq hf
  subst fg
  rfl

/-- A prescribed morphism remains prescribed under an equality of its source complex. -/
theorem homotopyEquiv_prescribed_of_heq {A A' B : GCx k} (hA : A = A')
    (f : GHom A B) (g : GHom A' B) (hf : HEq f g)
    (e : HomotopyEquiv A'.toCC B.toCC) (he : e.hom = GHom.toCC g) :
    ∃ e' : HomotopyEquiv A.toCC B.toCC, e'.hom = GHom.toCC f := by
  subst A'
  have hfg : f = g := eq_of_heq hf
  exact ⟨e, he.trans (congrArg GHom.toCC hfg.symm)⟩

end SelmerRetractions

section ActualErasure

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (q : Places K S) (old : ∀ v, SubFam (galLv (k := k) K S M v))
  (F : Set (Places K S))

/-- Erasure commutes with the strict switch when the new place is retained. -/
theorem erase_switchStr (hq : q ∉ F) :
    eraseFull F (switchStrK k (gGvK K S) (gMvK K S M) q old) =
      switchStrK k (gGvK K S) (gMvK K S M) q (eraseFull F old) := by
  funext v
  by_cases hv : v = q
  · subst v
    simp only [eraseFull, switchStrK, ite_eq_right hq]
  · simp only [eraseFull, switchStrK, ite_eq_right hv]

/-- Erasure commutes with the relaxed switch when the new place is retained. -/
theorem erase_switchRel (hq : q ∉ F) :
    eraseFull F (switchRelK k (gGvK K S) (gMvK K S M) q old) =
      switchRelK k (gGvK K S) (gMvK K S M) q (eraseFull F old) := by
  funext v
  by_cases hv : v = q
  · subst v
    simp only [eraseFull, switchRelK, ite_eq_right hq]
  · simp only [eraseFull, switchRelK, ite_eq_right hv]

/-- The strict forward comparison is the actual inclusion of subcomplexes. -/
def strictReductionMap (hq : q ∉ F) (v : Places K S) :
    GHom (switchStrK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx
      (switchStrK k (gGvK K S) (gMvK K S M) q old v).cx :=
  SubFam.inclLe (by
    intro n
    rw [← erase_switchStr q old F hq]
    unfold eraseFull
    split_ifs
    · exact bot_le
    · exact le_rfl)

/-- The relaxed forward comparison is the actual inclusion of subcomplexes. -/
def relaxedReductionMap (hq : q ∉ F) (v : Places K S) :
    GHom (switchRelK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx
      (switchRelK k (gGvK K S) (gMvK K S M) q old v).cx :=
  SubFam.inclLe (by
    intro n
    rw [← erase_switchRel q old F hq]
    unfold eraseFull
    split_ifs
    · exact bot_le
    · exact le_rfl)

/-- The strict conditions are homotopy equivalent by the prescribed retained comparison. -/
theorem actual_strictConditions_reduction (R : RetainedFullReduction q old F) :
    ∃ e : HomotopyEquiv
      (piCx fun v => (switchStrK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx).toCC
      (piCx fun v => (switchStrK k (gGvK K S) (gMvK K S M) q old v).cx).toCC,
      e.hom = GHom.toCC (piMap (strictReductionMap q old F R.new_not_removed)) := by
  apply erasureEquiv_prescribed F _ _ (erase_switchStr q old F R.new_not_removed).symm
    (strictReductionMap q old F R.new_not_removed) (fun _ _ _ => rfl)
  intro v hv
  have hvq : v ≠ q := by
    intro h
    subst v
    exact R.new_not_removed hv
  rw [switchStr_neK q old hvq]
  exact R.contraction v hv

/-- The relaxed conditions are homotopy equivalent by the same retained comparison. -/
theorem actual_relaxedConditions_reduction (R : RetainedFullReduction q old F) :
    ∃ e : HomotopyEquiv
      (piCx fun v => (switchRelK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx).toCC
      (piCx fun v => (switchRelK k (gGvK K S) (gMvK K S M) q old v).cx).toCC,
      e.hom = GHom.toCC (piMap (relaxedReductionMap q old F R.new_not_removed)) := by
  apply erasureEquiv_prescribed F _ _ (erase_switchRel q old F R.new_not_removed).symm
    (relaxedReductionMap q old F R.new_not_removed) (fun _ _ _ => rfl)
  intro v hv
  have hvq : v ≠ q := by
    intro h
    subst v
    exact R.new_not_removed hv
  rw [switchRel_neK q old hvq]
  exact R.contraction v hv

/-- The reduced actual switch has no degree-two strict cochains. -/
theorem erased_switch_degreeTwoZero (R : RetainedFullReduction q old F)
    (side : ∀ v : Places K S, Set (Gloc K v.1)) :
    DegreeTwoZero (localSwitch q (eraseFull F old) side).Ustr := by
  apply (switch_degreeTwoZero_iff (gGvK K S) (gMvK K S M) q (eraseFull F old) side).2
  intro v hvq
  by_cases hv : v ∈ F
  · change DegreeTwoZero (eraseFull F old v).cx
    rw [eraseFull, ite_eq_left hv]
    intro x
    exact Subtype.ext ((Submodule.mem_bot k).1 x.2)
  · simpa only [eraseFull, ite_eq_right hv] using R.bounded v hvq hv

variable (side : ∀ v : Places K S, Set (Gloc K v.1))
  (eR : (localSwitch q old side).Wrel.toCC.homology 1 ≃ₗ[k]
    ((Fin 2 → k) × (Fin 2 → k)))
  (eR' : (localSwitch q (eraseFull F old) side).Wrel.toCC.homology 1 ≃ₗ[k]
    ((Fin 2 → k) × (Fin 2 → k)))
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) k T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)

/-- Pull back the given genuine isotropy homotopy along the retained comparisons.
It is not replaced by an unrelated choice of null-homotopy. -/
def reducedIsotropy (hq : q ∉ F) (I : ActualIsotropy q old side eR β hβ) :
    ActualIsotropy q (eraseFull F old) side eR' β hβ where
  h v i j l h := (forwardH q old side eR β hβ I v i j l h).compl₁₂
    ((strictReductionMap q old F hq v).f i i rfl)
    ((relaxedReductionMap q old F hq v).f j j rfl)
  isotropy₂ v i i₁ j j₁ hh hi hj x y := by
    let X := actualSwitch q old side eR
    let X' := actualSwitch q (eraseFull F old) side eR'
    let a := strictReductionMap q old F hq v
    let b := relaxedReductionMap q old F hq v
    have ha : (X.US v).d i i₁ hi (a.f i i rfl x) =
        a.f i₁ i₁ rfl ((X'.US v).d i i₁ hi x) := (a.comm i i₁ i i₁ rfl hi hi rfl x).symm
    have hb : (X.ΔR.U v).d j j₁ hj (b.f j j rfl y) =
        b.f j₁ j₁ rfl ((X'.ΔR.U v).d j j₁ hj y) := (b.comm j j₁ j j₁ rfl hj hj rfl y).symm
    have he := I.isotropy₂ v i i₁ j j₁ hh hi hj (a.f i i rfl x) (b.f j j rfl y)
    change forwardH q old side eR β hβ I v i₁ j 2 (by omega)
        ((X.US v).d i i₁ hi (a.f i i rfl x)) (b.f j j rfl y) +
      sgn i • forwardH q old side eR β hβ I v i j₁ 2 (by omega)
        (a.f i i rfl x) ((X.ΔR.U v).d j j₁ hj (b.f j j rfl y)) -
      (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P i j 2 hh
        ((strictLocalMap q (eraseFull F old) side eR' v).f i i rfl x)
        ((X'.ΔR.i v).f j j rfl y) ∈
      LinearMap.range ((galLv (k := k) K S T v).d 1 2 rfl) at he
    rw [ha, hb] at he
    exact he
  isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl h3 x y := by
    let X := actualSwitch q old side eR
    let X' := actualSwitch q (eraseFull F old) side eR'
    let a := strictReductionMap q old F hq v
    let b := relaxedReductionMap q old F hq v
    have ha : (X.US v).d i i₁ hi (a.f i i rfl x) =
        a.f i₁ i₁ rfl ((X'.US v).d i i₁ hi x) := (a.comm i i₁ i i₁ rfl hi hi rfl x).symm
    have hb : (X.ΔR.U v).d j j₁ hj (b.f j j rfl y) =
        b.f j₁ j₁ rfl ((X'.ΔR.U v).d j j₁ hj y) := (b.comm j j₁ j j₁ rfl hj hj rfl y).symm
    have he := I.isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl h3 (a.f i i rfl x) (b.f j j rfl y)
    change (galLv (k := k) K S T v).d l l₁ hl
        (forwardH q old side eR β hβ I v i j l hh (a.f i i rfl x) (b.f j j rfl y)) +
      forwardH q old side eR β hβ I v i₁ j l₁ (by omega)
        ((X.US v).d i i₁ hi (a.f i i rfl x)) (b.f j j rfl y) +
      sgn i • forwardH q old side eR β hβ I v i j₁ l₁ (by omega)
        (a.f i i rfl x) ((X.ΔR.U v).d j j₁ hj (b.f j j rfl y)) =
      (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) β hβ (continuous_pairing β) v).P i j l₁ (by omega)
        ((strictLocalMap q (eraseFull F old) side eR' v).f i i rfl x)
        ((X'.ΔR.i v).f j j rfl y) at he
    rw [ha, hb] at he
    exact he

/-- The isotropy homotopies are retained exactly under pullback, in every bidegree. -/
theorem reducedIsotropy_h (hq : q ∉ F) (I : ActualIsotropy q old side eR β hβ)
    (v : Places K S) (i j l : ℤ) (h : i + j = l + 1)
    (x : ((actualSwitch q (eraseFull F old) side eR').US v).X i)
    (y : ((actualSwitch q (eraseFull F old) side eR').ΔR.U v).X j) :
    forwardH q (eraseFull F old) side eR' β hβ
      (reducedIsotropy q old F side eR eR' β hβ hq I) v i j l h x y =
      forwardH q old side eR β hβ I v i j l h
        ((strictReductionMap q old F hq v).f i i rfl x)
        ((relaxedReductionMap q old F hq v).f j j rfl y) := rfl

/-- Both strict-symmetry conventions hold for the actual reduced switch, with the
pullback of the original genuine isotropy homotopy. -/
theorem reduced_strictSymmetry (R : RetainedFullReduction q old F)
    (I : ActualIsotropy q old side eR β hβ) (c : k)
    (hc : ∀ a b : M, β a b = c • β b a) :
    let X' := actualSwitch q (eraseFull F old) side eR'
    let I' := reducedIsotropy q old F side eR eR' β hβ R.new_not_removed I
    let Q' := galoisPairDataTrunc K S k β hβ X'.ΔS X'.ΔR I'
    let Cd := ZInQ.Contrib.CloudB3RC53.Hsw.localPairCupOneGen (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      β hβ (continuous_pairing β) c hc
    ZInQ.Manuscript.RC.SelmerComplex.StrictSymm X' β hβ I' c ∧
      ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc X'.toQuasi.D (piCx X'.US) (piMap X'.φ) Q' Cd ∧
      ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymm X'.toQuasi.D (piCx X'.US) (piMap X'.φ)
        Q'.toSelPairData Cd.trunc := by
  dsimp only
  let X' := actualSwitch q (eraseFull F old) side eR'
  let I' := reducedIsotropy q old F side eR eR' β hβ R.new_not_removed I
  let Q' := galoisPairDataTrunc K S k β hβ X'.ΔS X'.ΔR I'
  let Cd := ZInQ.Contrib.CloudB3RC53.Hsw.localPairCupOneGen (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    β hβ (continuous_pairing β) c hc
  have h2 : ∀ v, DegreeTwoZero (X'.US v) :=
    (degreeTwoZero_pi_iff X'.US).1 (erased_switch_degreeTwoZero q old F R side)
  have hs := genuine_strictSymmTrunc_of_degreeTwoZero X' β hβ I' c hc h2
  exact ⟨genuine_strictSymm_of_degreeTwoZero X' β hβ I' c h2, hs,
    ZInQ.Contrib.CloudB3RC53.Hsw.strictSymm_trunc X'.toQuasi.D (piCx X'.US) (piMap X'.φ) Q' Cd hs⟩

/-- Both retained local-condition maps commute exactly with the reduction comparisons. -/
theorem reduced_condition_maps (hq : q ∉ F) (i j : ℤ) (h : i = j) :
    (∀ x : (actualSwitch q (eraseFull F old) side eR').Dstr.U.X i,
      (actualSwitch q (eraseFull F old) side eR').Dstr.ι.f i j h x =
        (actualSwitch q old side eR).Dstr.ι.f i j h
          ((piMap (strictReductionMap q old F hq)).f i i rfl x)) ∧
    (∀ x : (actualSwitch q (eraseFull F old) side eR').toQuasi.D.U.X i,
      (actualSwitch q (eraseFull F old) side eR').toQuasi.D.ι.f i j h x =
        (actualSwitch q old side eR).toQuasi.D.ι.f i j h
          ((piMap (relaxedReductionMap q old F hq)).f i i rfl x)) := by
  subst h
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The comparison of the actual strict Selmer complexes retains the global and
ambient local components. -/
def strictSelmerComparison (hq : q ∉ F) :
    GHom (selCx (actualSwitch q (eraseFull F old) side eR').Dstr)
      (selCx (actualSwitch q old side eR).Dstr) where
  f i j h := by
    subst h
    exact (changeMap (actualSwitch q old side eR).Dstr
      (piMap (strictReductionMap q old F hq))).f i i rfl
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    obtain ⟨a, u, y⟩ := x
    refine Prod.ext rfl (Prod.ext
      ((piMap (strictReductionMap q old F hq)).comm i i₁ i i₁ rfl h₁ h₂ rfl u) ?_)
    change (actualSwitch q (eraseFull F old) side eR').Dstr.res.f i (i₁ - 1) (by omega) a -
        (actualSwitch q (eraseFull F old) side eR').Dstr.ι.f i (i₁ - 1) (by omega) u -
        (actualSwitch q (eraseFull F old) side eR').Dstr.L.d (i - 1) (i₁ - 1) (by omega) y =
      (actualSwitch q old side eR).Dstr.res.f i (i₁ - 1) (by omega) a -
        (actualSwitch q old side eR).Dstr.ι.f i (i₁ - 1) (by omega)
          ((piMap (strictReductionMap q old F hq)).f i i rfl u) -
        (actualSwitch q old side eR).Dstr.L.d (i - 1) (i₁ - 1) (by omega) y
    rw [(reduced_condition_maps q old F side eR eR' hq i (i₁ - 1) (by omega)).1 u]
    rfl

/-- The comparison of the actual relaxed Selmer complexes has the same retained components. -/
def relaxedSelmerComparison (hq : q ∉ F) :
    GHom (selCx (actualSwitch q (eraseFull F old) side eR').toQuasi.D)
      (selCx (actualSwitch q old side eR).toQuasi.D) where
  f i j h := by
    subst h
    exact (changeMap (actualSwitch q old side eR).toQuasi.D
      (piMap (relaxedReductionMap q old F hq))).f i i rfl
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    obtain ⟨a, u, y⟩ := x
    refine Prod.ext rfl (Prod.ext
      ((piMap (relaxedReductionMap q old F hq)).comm i i₁ i i₁ rfl h₁ h₂ rfl u) ?_)
    change (actualSwitch q (eraseFull F old) side eR').toQuasi.D.res.f i (i₁ - 1) (by omega) a -
        (actualSwitch q (eraseFull F old) side eR').toQuasi.D.ι.f i (i₁ - 1) (by omega) u -
        (actualSwitch q (eraseFull F old) side eR').toQuasi.D.L.d (i - 1) (i₁ - 1) (by omega) y =
      (actualSwitch q old side eR).toQuasi.D.res.f i (i₁ - 1) (by omega) a -
        (actualSwitch q old side eR).toQuasi.D.ι.f i (i₁ - 1) (by omega)
          ((piMap (relaxedReductionMap q old F hq)).f i i rfl u) -
        (actualSwitch q old side eR).toQuasi.D.L.d (i - 1) (i₁ - 1) (by omega) y
    rw [(reduced_condition_maps q old F side eR eR' hq i (i₁ - 1) (by omega)).2 u]
    rfl

/-- Naturality of the original Selmer cup formula, with the given isotropy homotopy retained. -/
theorem reduction_cup_naturality (hq : q ∉ F) (I : ActualIsotropy q old side eR β hβ)
    (i j : ℤ) (h : i + j = 3)
    (x : (selCx (actualSwitch q (eraseFull F old) side eR').Dstr).X i)
    (y : (selCx (actualSwitch q (eraseFull F old) side eR').toQuasi.D).X j) :
    selCupFunT (galoisPairDataTrunc K S k β hβ
        (actualSwitch q (eraseFull F old) side eR').ΔS
        (actualSwitch q (eraseFull F old) side eR').ΔR
        (reducedIsotropy q old F side eR eR' β hβ hq I)) i j 3 h x y =
      selCupFunT (galoisPairDataTrunc K S k β hβ (actualSwitch q old side eR).ΔS
        (actualSwitch q old side eR).ΔR I) i j 3 h
        ((strictSelmerComparison q old F side eR eR' hq).f i i rfl x)
        ((relaxedSelmerComparison q old F side eR eR' hq).f j j rfl y) := rfl

/-- Every trace of the retained cup product is preserved exactly on the forward comparison. -/
theorem reduction_traced_pairing (hq : q ∉ F) (I : ActualIsotropy q old side eR β hβ)
    (tr0 : (coneCx (galoisPairDataTrunc K S k β hβ (actualSwitch q old side eR).ΔS
      (actualSwitch q old side eR).ΔR I).resE).X 3 →ₗ[k] k)
    (i j : ℤ) (h : i + j = 3)
    (x : (selCx (actualSwitch q (eraseFull F old) side eR').Dstr).X i)
    (y : (selCx (actualSwitch q (eraseFull F old) side eR').toQuasi.D).X j) :
    tr0 (selCupFunT (galoisPairDataTrunc K S k β hβ
        (actualSwitch q (eraseFull F old) side eR').ΔS
        (actualSwitch q (eraseFull F old) side eR').ΔR
        (reducedIsotropy q old F side eR eR' β hβ hq I)) i j 3 h x y) =
      tr0 (selCupFunT (galoisPairDataTrunc K S k β hβ (actualSwitch q old side eR).ΔS
        (actualSwitch q old side eR).ΔR I) i j 3 h
        ((strictSelmerComparison q old F side eR eR' hq).f i i rfl x)
        ((relaxedSelmerComparison q old F side eR eR' hq).f j j rfl y)) :=
  congrArg tr0 (reduction_cup_naturality q old F side eR eR' β hβ hq I i j h x y)

/-- The authorized full-condition contractions give actual strict and relaxed
condition deformation retracts with the prescribed inclusion maps. -/
theorem actual_condition_retractions (R : RetainedFullReduction q old F) :
    (∃ C : ConditionRetraction
      (piCx fun v => (switchStrK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx)
      (piCx fun v => (switchStrK k (gGvK K S) (gMvK K S M) q old v).cx),
      C.inc = piMap (strictReductionMap q old F R.new_not_removed)) ∧
    (∃ C : ConditionRetraction
      (piCx fun v => (switchRelK k (gGvK K S) (gMvK K S M) q (eraseFull F old) v).cx)
      (piCx fun v => (switchRelK k (gGvK K S) (gMvK K S M) q old v).cx),
      C.inc = piMap (relaxedReductionMap q old F R.new_not_removed)) := by
  constructor
  · apply erasureRetraction_prescribed F _ _ (erase_switchStr q old F R.new_not_removed).symm
      (strictReductionMap q old F R.new_not_removed) (fun _ _ _ => rfl)
    intro v hv
    have hvq : v ≠ q := by
      intro h
      subst v
      exact R.new_not_removed hv
    rw [switchStr_neK q old hvq]
    exact R.contraction v hv
  · apply erasureRetraction_prescribed F _ _ (erase_switchRel q old F R.new_not_removed).symm
      (relaxedReductionMap q old F R.new_not_removed) (fun _ _ _ => rfl)
    intro v hv
    have hvq : v ≠ q := by
      intro h
      subst v
      exact R.new_not_removed hv
    rw [switchRel_neK q old hvq]
    exact R.contraction v hv

/-- Removing the authorized full conditions gives homotopy equivalences of the
actual strict and relaxed Selmer complexes, with the prescribed forward maps. -/
theorem actual_selmer_reduction (R : RetainedFullReduction q old F) :
    let X := actualSwitch q old side eR
    let js := piMap (strictReductionMap q old F R.new_not_removed)
    let jr := piMap (relaxedReductionMap q old F R.new_not_removed)
    (∃ e : HomotopyEquiv (selCx (restrictData X.Dstr js)).toCC (selCx X.Dstr).toCC,
      e.hom = GHom.toCC (changeMap X.Dstr js)) ∧
    (∃ e : HomotopyEquiv (selCx (restrictData X.toQuasi.D jr)).toCC (selCx X.toQuasi.D).toCC,
      e.hom = GHom.toCC (changeMap X.toQuasi.D jr)) := by
  dsimp only
  obtain ⟨⟨Cs, hs⟩, ⟨Cr, hr⟩⟩ := actual_condition_retractions q old F R
  constructor
  · rw [← hs]
    exact ⟨selmerRetractionEquiv (actualSwitch q old side eR).Dstr Cs, rfl⟩
  · rw [← hr]
    exact ⟨selmerRetractionEquiv (actualSwitch q old side eR).toQuasi.D Cr, rfl⟩

/-- The reduced genuine Selmer data are exactly restriction along the retained comparisons. -/
theorem reduced_SelmerData_eq (hq : q ∉ F) :
    (actualSwitch q (eraseFull F old) side eR').Dstr =
        restrictData (actualSwitch q old side eR).Dstr (piMap (strictReductionMap q old F hq)) ∧
    (actualSwitch q (eraseFull F old) side eR').toQuasi.D =
        restrictData (actualSwitch q old side eR).toQuasi.D (piMap (relaxedReductionMap q old F hq)) := by
  constructor
  · have hi : (actualSwitch q (eraseFull F old) side eR').Dstr.ι =
        ghomComp (piMap (strictReductionMap q old F hq)) (actualSwitch q old side eR).Dstr.ι :=
      ghom_ext fun n x => (reduced_condition_maps q old F side eR eR' hq n n rfl).1 x
    exact congrArg (fun i : GHom (actualSwitch q (eraseFull F old) side eR').Dstr.U
        (actualSwitch q old side eR).Dstr.L =>
      (⟨(actualSwitch q old side eR).Dstr.G,
        (actualSwitch q (eraseFull F old) side eR').Dstr.U,
        (actualSwitch q old side eR).Dstr.L, (actualSwitch q old side eR).Dstr.res, i⟩ : SelData k)) hi
  · have hi : (actualSwitch q (eraseFull F old) side eR').toQuasi.D.ι =
        ghomComp (piMap (relaxedReductionMap q old F hq)) (actualSwitch q old side eR).toQuasi.D.ι :=
      ghom_ext fun n x => (reduced_condition_maps q old F side eR eR' hq n n rfl).2 x
    exact congrArg (fun i : GHom (actualSwitch q (eraseFull F old) side eR').toQuasi.D.U
        (actualSwitch q old side eR).toQuasi.D.L =>
      (⟨(actualSwitch q old side eR).toQuasi.D.G,
        (actualSwitch q (eraseFull F old) side eR').toQuasi.D.U,
        (actualSwitch q old side eR).toQuasi.D.L, (actualSwitch q old side eR).toQuasi.D.res, i⟩ : SelData k)) hi

/-- The comparisons used by the traced cup formula are homotopy equivalences of
the actual reduced and original Selmer complexes. -/
theorem actual_erasedSelmer_equivalences (R : RetainedFullReduction q old F) :
    (∃ e : HomotopyEquiv (selCx (actualSwitch q (eraseFull F old) side eR').Dstr).toCC
        (selCx (actualSwitch q old side eR).Dstr).toCC,
      e.hom = GHom.toCC (strictSelmerComparison q old F side eR eR' R.new_not_removed)) ∧
    (∃ e : HomotopyEquiv (selCx (actualSwitch q (eraseFull F old) side eR').toQuasi.D).toCC
        (selCx (actualSwitch q old side eR).toQuasi.D).toCC,
      e.hom = GHom.toCC (relaxedSelmerComparison q old F side eR eR' R.new_not_removed)) := by
  obtain ⟨⟨es, hs⟩, ⟨er, hr⟩⟩ := actual_selmer_reduction q old F side eR R
  have hDs := (reduced_SelmerData_eq q old F side eR eR' R.new_not_removed).1
  have hDr := (reduced_SelmerData_eq q old F side eR eR' R.new_not_removed).2
  constructor
  · have hA := congrArg selCx hDs
    have hmap : HEq (strictSelmerComparison q old F side eR eR' R.new_not_removed)
        (changeMap (actualSwitch q old side eR).Dstr
          (piMap (strictReductionMap q old F R.new_not_removed))) :=
      ghomHEq_of_components hA (heq_of_eq (by funext i j h; subst h; rfl))
    exact homotopyEquiv_prescribed_of_heq hA _ _ hmap es hs
  · have hA := congrArg selCx hDr
    have hmap : HEq (relaxedSelmerComparison q old F side eR eR' R.new_not_removed)
        (changeMap (actualSwitch q old side eR).toQuasi.D
          (piMap (relaxedReductionMap q old F R.new_not_removed))) :=
      ghomHEq_of_components hA (heq_of_eq (by funext i j h; subst h; rfl))
    exact homotopyEquiv_prescribed_of_heq hA _ _ hmap er hr

/-- Retained cochain arrows and their original homotopies transfer through the
actual full-condition comparisons. The inclusion square is homotopy commutative. -/
theorem actual_retained_arrows (R : RetainedFullReduction q old F) :
    let Cs := (selCx (actualSwitch q old side eR).Dstr).toCC
    let Cr := (selCx (actualSwitch q old side eR).toQuasi.D).toCC
    let Cs' := (selCx (actualSwitch q (eraseFull F old) side eR').Dstr).toCC
    let Cr' := (selCx (actualSwitch q (eraseFull F old) side eR').toQuasi.D).toCC
    ∃ (es : HomotopyEquiv Cs' Cs) (er : HomotopyEquiv Cr' Cr),
      es.hom = GHom.toCC (strictSelmerComparison q old F side eR eR' R.new_not_removed) ∧
      er.hom = GHom.toCC (relaxedSelmerComparison q old F side eR eR' R.new_not_removed) ∧
      (∀ f : Cs ⟶ Cr, Nonempty (Homotopy (es.hom ≫ f)
        ((es.hom ≫ f ≫ er.inv) ≫ er.hom))) ∧
      (∀ f g : Cs ⟶ Cr, Homotopy f g →
        Nonempty (Homotopy (es.hom ≫ f ≫ er.inv) (es.hom ≫ g ≫ er.inv))) := by
  dsimp only
  obtain ⟨⟨es, hs⟩, ⟨er, hr⟩⟩ := actual_erasedSelmer_equivalences q old F side eR eR' R
  refine ⟨es, er, hs, hr, ?_, ?_⟩
  · intro f
    refine ⟨?_⟩
    simpa only [Category.comp_id, Category.assoc] using
      (er.homotopyInvHomId.symm.compLeft (es.hom ≫ f))
  · intro f g H
    exact ⟨(H.compLeft es.hom).compRight er.inv⟩

end ActualErasure

section ContinuousRetainedSwitch

variable {k : Type} [Field k] {GS : Type} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {V : Type} [DecidableEq V]
  {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]

/-- The actual derivative switch on continuous cochains; coefficients need not be discrete. -/
abbrev continuousSwitch (q : V) (old : ∀ v, SubFam (localCx k GS Gv loc M v))
    (side : ∀ v, Set (Gv v)) : DerivFamily (localCx k GS Gv loc M) :=
  switchFamK k Gv (fun v => ResMod (loc v) M) q old side

/-- Local conditions given by the specified subcomplexes of continuous cochains. -/
def continuousConditions (A : ∀ v, SubFam (localCx k GS Gv loc M v)) :
    LocalConditions k GS Gv loc M := ⟨fun v => (A v).cx, fun v => (A v).incl⟩

variable (q : V) (old : ∀ v, SubFam (localCx k GS Gv loc M v)) (side : ∀ v, Set (Gv v))

/-- The relaxed Selmer data of the actual continuous switch. -/
abbrev continuousRelaxedData : SelData k :=
  (continuousSwitch q old side).relaxedData (globalCx k GS M) (resS k GS Gv loc M)

/-- The actual strict local conditions inside the relaxed data. -/
abbrev continuousStrictData : SelData k :=
  restrictData (continuousRelaxedData q old side) (continuousSwitch q old side).fr

variable (β : M →ₗ[k] M →ₗ[k] T)
  (hβ : ∀ (g : GS) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- The genuine truncated isotropy datum for the continuous switch. -/
abbrev ContinuousIsotropy := TruncIsotropyData k GS Gv loc β hβ hβc
  (continuousConditions (continuousSwitch q old side).str)
  (continuousConditions (continuousSwitch q old side).rel)

/-- The pairing data are the genuine continuous cup products and the given homotopy. -/
def continuousPairData (I : ContinuousIsotropy q old side β hβ hβc) :
    SelPairDataTrunc (continuousStrictData q old side) (continuousRelaxedData q old side) :=
  let Q := genuinePairDataTrunc k GS Gv loc β hβ hβc
    (continuousConditions (continuousSwitch q old side).str)
    (continuousConditions (continuousSwitch q old side).rel) I
  { E := Q.E
    EL := Q.EL
    resE := Q.resE
    cupG := Q.cupG
    cupL := Q.cupL
    compat := Q.compat
    hU := Q.hU
    isotropy₂ := fun i i₁ j j₁ hh hi hj x y => Q.isotropy₂ i i₁ j j₁ hh hi hj x y
    isotropy₃ := fun i i₁ j j₁ l l₁ hh hi hj hl h3 x y => Q.isotropy₃ i i₁ j j₁ l l₁ hh hi hj hl h3 x y }

/-- The given homotopy with its strict and relaxed domains explicit. -/
def continuousForward (I : ContinuousIsotropy q old side β hβ hβc)
    (v : V) (i j l : ℤ) (h : i + j = l + 1) :
    ((continuousSwitch q old side).str v).cx.X i →ₗ[k]
      ((continuousSwitch q old side).rel v).cx.X j →ₗ[k] (localCx k GS Gv loc T v).X l :=
  I.h v i j l h

/-- The retained strict-to-relaxed map at a place. -/
def continuousLocalInclusion (v : V) :
    GHom ((continuousSwitch q old side).str v).cx ((continuousSwitch q old side).rel v).cx :=
  SubFam.inclLe (derivHsrK (continuousSwitch q old side) v)

/-- The retained inverse at every place other than the new derivative place. -/
def continuousOldBack (v : V) (hv : v ≠ q) :
    GHom ((continuousSwitch q old side).rel v).cx ((continuousSwitch q old side).str v).cx :=
  SubFam.inclLe (by
    intro n
    change (switchRelK k Gv (fun v => ResMod (loc v) M) q old v).S n ≤
      (switchStrK k Gv (fun v => ResMod (loc v) M) q old v).S n
    rw [switchRel_neK q old hv, switchStr_neK q old hv])

omit [IsTopologicalGroup GS] in
/-- The actual new strict condition has zero degree-one and degree-two terms. -/
theorem continuous_new_strict_zero :
    DegreeTwoZero ((continuousSwitch q old side).str q).cx ∧
      ∀ x : ((continuousSwitch q old side).str q).cx.X 1, x = 0 := by
  constructor
  · change DegreeTwoZero (switchStrK k Gv (fun v => ResMod (loc v) M) q old q).cx
    rw [switchStr_qK]
    intro x
    exact Subtype.ext ((Submodule.mem_bot k).1 x.2)
  · intro x
    apply Subtype.ext
    have hx := x.2
    change x.1 ∈ (switchStrK k Gv (fun v => ResMod (loc v) M) q old q).S 1 at hx
    rw [switchStr_qK] at hx
    exact (Submodule.mem_bot k).1 hx

/-- The retained reverse homotopy on the actual continuous local conditions. -/
def continuousReverse (I : ContinuousIsotropy q old side β hβ hβc)
    (v : V) (i j l : ℤ) (h : i + j = l + 1) :
    ((continuousSwitch q old side).rel v).cx.X i →ₗ[k]
      ((continuousSwitch q old side).str v).cx.X j →ₗ[k] (localCx k GS Gv loc T v).X l :=
  if hv : v = q then 0 else
    (continuousForward q old side β hβ hβc I v i j l h).compl₁₂
      ((continuousOldBack q old side v hv).f i i rfl)
      ((continuousLocalInclusion q old side v).f j j rfl)

/-- Assembly of the retained reverse homotopy over the places. -/
def continuousReversePi (I : ContinuousIsotropy q old side β hβ hβc)
    (i j l : ℤ) (h : i + j = l + 1) :
    (continuousSwitch q old side).Urel.X i →ₗ[k] (continuousSwitch q old side).Ustr.X j →ₗ[k]
      (localSumCx k GS Gv loc T).X l :=
  LinearMap.mk₂ k (fun u t v => continuousReverse q old side β hβ hβc I v i j l h (u v) (t v))
    (fun u u' t => by
      funext v
      exact LinearMap.map_add₂ (continuousReverse q old side β hβ hβc I v i j l h) (u v) (u' v) (t v))
    (fun c u t => by
      funext v
      exact LinearMap.map_smul₂ (continuousReverse q old side β hβ hβc I v i j l h) c (u v) (t v))
    (fun u t t' => by
      funext v
      exact map_add (continuousReverse q old side β hβ hβc I v i j l h (u v)) (t v) (t' v))
    (fun c u t => by
      funext v
      exact map_smul (continuousReverse q old side β hβ hβc I v i j l h (u v)) c (t v))

omit [IsTopologicalGroup GS] in
/-- Exact agreement on strict cochains for the continuous retained reverse homotopy. -/
theorem continuousReverse_compat (I : ContinuousIsotropy q old side β hβ hβc) (v : V)
    (s : ((continuousSwitch q old side).str v).cx.X 2)
    (t : ((continuousSwitch q old side).str v).cx.X 1) :
    continuousForward q old side β hβ hβc I v 2 1 2 rfl s
        ((continuousLocalInclusion q old side v).f 1 1 rfl t) =
      continuousReverse q old side β hβ hβc I v 2 1 2 rfl
        ((continuousLocalInclusion q old side v).f 2 2 rfl s) t := by
  by_cases hv : v = q
  · subst v
    rw [(continuous_new_strict_zero q old side).1 s]
    have hr : continuousReverse q old side β hβ hβc I q 2 1 2 rfl = 0 := dite_eq_left rfl
    rw [hr]
    simp only [map_zero, LinearMap.zero_apply]
  · have hb : (continuousOldBack q old side v hv).f 2 2 rfl
        ((continuousLocalInclusion q old side v).f 2 2 rfl s) = s := Subtype.ext rfl
    rw [continuousReverse, dite_eq_right hv, LinearMap.compl₁₂_apply, hb]

omit [IsTopologicalGroup GS] in
/-- Reverse isotropy modulo local coboundaries for the genuine continuous switch. -/
theorem continuousReverse_isotropy (I : ContinuousIsotropy q old side β hβ hβc) (v : V)
    (u : ((continuousSwitch q old side).rel v).cx.X 1)
    (t : ((continuousSwitch q old side).str v).cx.X 1) :
    continuousReverse q old side β hβ hβc I v 2 1 2 rfl
        (((continuousSwitch q old side).rel v).cx.d 1 2 rfl u) t +
      sgn 1 • continuousReverse q old side β hβ hβc I v 1 2 2 rfl u
        (((continuousSwitch q old side).str v).cx.d 1 2 rfl t) -
      (localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl
        (((continuousSwitch q old side).rel v).incl.f 1 1 rfl u)
        (((continuousSwitch q old side).str v).incl.f 1 1 rfl t) ∈
      LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl) := by
  by_cases hv : v = q
  · subst v
    rw [(continuous_new_strict_zero q old side).2 t]
    have h21 : continuousReverse q old side β hβ hβc I q 2 1 2 rfl = 0 := dite_eq_left rfl
    have h12 : continuousReverse q old side β hβ hβc I q 1 2 2 rfl = 0 := dite_eq_left rfl
    rw [h21, h12]
    simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, sub_zero]
    exact Submodule.zero_mem _
  · let a := continuousOldBack q old side v hv
    let b := continuousLocalInclusion q old side v
    have he := I.isotropy₂ v 1 2 1 2 rfl rfl rfl (a.f 1 1 rfl u) (b.f 1 1 rfl t)
    change continuousForward q old side β hβ hβc I v 2 1 2 rfl
        (((continuousSwitch q old side).str v).cx.d 1 2 rfl (a.f 1 1 rfl u)) (b.f 1 1 rfl t) +
      sgn 1 • continuousForward q old side β hβ hβc I v 1 2 2 rfl (a.f 1 1 rfl u)
        (((continuousSwitch q old side).rel v).cx.d 1 2 rfl (b.f 1 1 rfl t)) -
      (localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl
        (((continuousSwitch q old side).rel v).incl.f 1 1 rfl u)
        (((continuousSwitch q old side).str v).incl.f 1 1 rfl t) ∈
      LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl) at he
    rw [← a.comm 1 2 1 2 rfl rfl rfl rfl, ← b.comm 1 2 1 2 rfl rfl rfl rfl] at he
    simpa only [continuousReverse, dite_eq_right hv, LinearMap.compl₁₂_apply] using he

/-- Compatible reverse isotropy for the actual continuous switch, including
non-discrete coefficients and retained full conditions. -/
def continuous_retainedReverseIsotropy (I : ContinuousIsotropy q old side β hβ hβc) :
    ZInQ.Contrib.CloudB3RC53.Hsw.ReverseIsotropy (continuousRelaxedData q old side)
      (continuousSwitch q old side).Ustr (continuousSwitch q old side).fr
      (continuousPairData q old side β hβ hβc I).toSelPairData where
  h11 := 0
  h21 := (continuousReversePi q old side β hβ hβc I 2 1 2 rfl).compr₂
    (truncSub (localSumCx k GS Gv loc T) 2).mkQ
  h12 := (continuousReversePi q old side β hβ hβc I 1 2 2 rfl).compr₂
    (truncSub (localSumCx k GS Gv loc T) 2).mkQ
  iso u t := by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero, zero_add]
    have hmem : ∀ v,
        continuousReverse q old side β hβ hβc I v 2 1 2 rfl
            (((continuousSwitch q old side).rel v).cx.d 1 2 rfl (u v)) (t v) -
          continuousReverse q old side β hβ hβc I v 1 2 2 rfl (u v)
            (((continuousSwitch q old side).str v).cx.d 1 2 rfl (t v)) -
          (localPair k GS Gv loc β hβ hβc v).P 1 1 2 rfl
            (((continuousSwitch q old side).rel v).incl.f 1 1 rfl (u v))
            (((continuousSwitch q old side).str v).incl.f 1 1 rfl (t v)) ∈
          LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl) := fun v => by
      simpa only [sgn_one, neg_one_zsmul, sub_eq_add_neg] using
        continuousReverse_isotropy q old side β hβ hβc I v (u v) (t v)
    exact mkQ_add_sgn_one _
      (continuousReversePi q old side β hβ hβc I 2 1 2 rfl
        ((continuousSwitch q old side).Urel.d 1 2 rfl u) t)
      (continuousReversePi q old side β hβ hβc I 1 2 2 rfl u
        ((continuousSwitch q old side).Ustr.d 1 2 rfl t))
      ((localSumPair k GS Gv loc β hβ hβc).P 1 1 2 rfl
        ((piMap fun v => ((continuousSwitch q old side).rel v).incl).f 1 1 rfl u)
        ((piMap fun v => ((continuousSwitch q old side).str v).incl).f 1 1 rfl t))
      (by
        choose w hw using hmem
        exact ⟨fun v => w v, funext fun v => hw v⟩)
  compat s t := by
    change (truncSub (localSumCx k GS Gv loc T) 2).mkQ
        (fun v => continuousForward q old side β hβ hβc I v 2 1 2 rfl (s v)
          ((continuousLocalInclusion q old side v).f 1 1 rfl (t v))) =
      (truncSub (localSumCx k GS Gv loc T) 2).mkQ
        (continuousReversePi q old side β hβ hβc I 2 1 2 rfl
          ((continuousSwitch q old side).fr.f 2 2 rfl s) t)
    congr 1
    funext v
    exact continuousReverse_compat q old side β hβ hβc I v (s v) (t v)

/-- The original traced cup product descends on the actual continuous switch.
No old-place degree bound, contraction or coefficient symmetry is needed. -/
theorem continuous_original_residuePairing (I : ContinuousIsotropy q old side β hβ hβc)
    (eR : (continuousSwitch q old side).Wrel.toCC.homology 1 ≃ₗ[k]
      ((Fin 2 → k) × (Fin 2 → k)))
    (tr0 : (coneCx (continuousPairData q old side β hβ hβc I).resE).X 3 →ₗ[k] k)
    (htr0 : ∀ z, tr0 ((coneCx (continuousPairData q old side β hβ hβc I).resE).d 2 3 rfl z) = 0) :
    let F := continuousSwitch q old side
    let D := continuousRelaxedData q old side
    let Q := continuousPairData q old side β hβ hβc I
    ∃ P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : F.Urel.X 1) (s : F.Ustr.X 2) (_ht : F.Urel.d 1 2 rfl t = 0)
        (_hu : F.Urel.d 1 2 rfl u = F.fr.f 2 2 rfl s)
        (ct cu : LinearMap.ker (F.Wrel.d 1 2 rfl))
        (_hct : ct.1 = (quotMk F.fr).f 1 1 rfl t) (_hcu : cu.1 = (quotMk F.fr).f 1 1 rfl u),
        tr0 (selCupFunT Q 2 1 3 rfl ((0 : D.G.X 2), s, -(D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : D.G.X 1), t, (0 : D.L.X (1 - 1)))) =
          P (eR (cls1 F.Wrel ct)) (eR (cls1 F.Wrel cu)) := by
  dsimp only
  let F := continuousSwitch q old side
  let D := continuousRelaxedData q old side
  let Q := continuousPairData q old side β hβ hβc I
  let R := F.toQuasiRelaxed (globalCx k GS M) (resS k GS Gv loc M) eR
  have hinj : ∀ n, Function.Injective (F.fr.f n n rfl) := by
    intro n x y h
    funext v
    exact SubFam.inclLe_injective (derivHsrK F v) n (congrFun h v)
  exact ZInQ.Contrib.CloudB3RC53.Hsw.exists_residuePairing_trunc R F.Ustr F.fr Q tr0 htr0
    (quotMk_comp_apply F.fr) hinj (quotMk_surjective F.fr)
    (fun n u hu => (quotMk_eq_zero_iff F.fr n u).1 hu)
    (ZInQ.Contrib.CloudB3RC53.Hsw.strictOrth_of_reverseIsotropy D F.Ustr F.fr Q.toSelPairData
      (Q.trT tr0 htr0) (Q.trT_kills tr0 htr0)
      (continuous_retainedReverseIsotropy q old side β hβ hβc I))

/-- The action of an actual local group element as a coefficient endomorphism. -/
def localActionEnd (v : V) (g : Gv v) : Module.End k (ResMod (loc v) M) where
  toFun m := g • m
  map_add' := smul_add g
  map_smul' c m := smul_comm g c m

omit [IsTopologicalGroup GS] [DecidableEq V] [∀ v, IsTopologicalGroup (Gv v)]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M] in
/-- Primitive quadratic inertia acts as minus the identity on the actual restricted module. -/
theorem primitive_localAction (v : V) (σ : Gv v)
    (hσ : ∀ m : ResMod (loc v) M, σ • m = -m) :
    localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ = -1 := by
  ext m
  change σ • m = -m
  exact hσ m

omit [IsTopologicalGroup GS] [DecidableEq V] [∀ v, IsTopologicalGroup (Gv v)]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M] in
/-- At a test field where two is invertible, the actual primitive inertia-minus-one
operator is a unit. No unused unramified full condition is covered by this statement. -/
theorem primitive_inertia_isUnit (v : V) (σ : Gv v)
    (hσ : ∀ m : ResMod (loc v) M, σ • m = -m) (h2 : (2 : k) ≠ 0) :
    IsUnit (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) := by
  rw [primitive_localAction (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ hσ]
  have he : (-1 : Module.End k (ResMod (loc v) M)) - 1 =
      algebraMap k (Module.End k (ResMod (loc v) M)) (-2) := by
    ext m
    simp
    module
  rw [he]
  exact (isUnit_iff_ne_zero.mpr h2).neg.map _

omit [IsTopologicalGroup GS] [DecidableEq V] [∀ v, IsTopologicalGroup (Gv v)]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M] in
/-- The actual primitive Frobenius and inertia operators satisfy the tame model relation. -/
theorem primitive_tame_relation (v : V) (φ σ : Gv v) (r : ℕ)
    (hσ : ∀ m : ResMod (loc v) M, σ • m = -m) :
    (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)) *
        (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) =
      (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) * (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1) := by
  apply (tameCommutator_proof k (ResMod (loc v) M) r
    (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ) (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)).2.2
  · rw [primitive_localAction (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ hσ]
    noncomm_ring
  · rw [primitive_localAction (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ hσ]
    noncomm_ring

/-- The manuscript's tame model with actual Frobenius and inertia actions. -/
def actualTameComplex (v : V) (φ σ : Gv v) (r : ℕ)
    (hDC : (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)) *
        (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) =
      (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) * (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1)) :
    CochainComplex (ModuleCat k) ℤ :=
  tameComplex (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1) (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1)
    (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)) hDC

omit [IsTopologicalGroup GS] [DecidableEq V] in
/-- A retained homotopy comparison with the actual tame model transports either
displayed contraction to the actual full continuous-cochain condition. -/
theorem full_contraction_of_tame_comparison (v : V) (φ σ : Gv v) (r : ℕ)
    (hDC : (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)) *
        (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) =
      (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1) * (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1))
    (hunit : (IsUnit (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1) ∧
        IsUnit (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ))) ∨
      IsUnit (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1))
    (e : HomotopyEquiv (SubFam.top (localCx k GS Gv loc M v)).cx.toCC
      (actualTameComplex (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ σ r hDC)) :
    Nonempty (Contraction (SubFam.top (localCx k GS Gv loc M v)).cx) := by
  have hmodel := tameComplexContractible_proof k (ResMod (loc v) M)
    (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - 1) (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ - 1)
    (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ - normQ r (localActionEnd (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ)) hDC hunit
  obtain ⟨H⟩ := contractible_of_homotopyEquiv e hmodel
  exact ⟨Contraction.ofHomotopy H⟩

omit [IsTopologicalGroup GS] [DecidableEq V] in
/-- For primitive ramified inertia the only model input remaining is the retained
comparison from the genuine full cochains to the actual tame model. -/
theorem full_contraction_of_primitive_tame_comparison (v : V) (φ σ : Gv v) (r : ℕ)
    (hσ : ∀ m : ResMod (loc v) M, σ • m = -m) (h2 : (2 : k) ≠ 0)
    (e : HomotopyEquiv (SubFam.top (localCx k GS Gv loc M v)).cx.toCC
      (actualTameComplex (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ σ r (primitive_tame_relation (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ σ r hσ))) :
    Nonempty (Contraction (SubFam.top (localCx k GS Gv loc M v)).cx) :=
  full_contraction_of_tame_comparison (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ σ r (primitive_tame_relation (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v φ σ r hσ)
    (Or.inr (primitive_inertia_isUnit (k := k) (GS := GS) (Gv := Gv) (loc := loc) (M := M) v σ hσ h2)) e

end ContinuousRetainedSwitch

end ZInQ.Contrib.RC53Assist.StrictSymmFull

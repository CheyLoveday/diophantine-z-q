import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Retention

/-!
# The dual chain of the presentation and the paired strict lift

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4157–4175) and
Proposition `ex:arith-paired-functional` (tex 3736–3753).

**The dual chain (`DPp`, `fS`).** At the switch `C_T ⊂ C_{T ∪ {p}}` the text uses the orthogonal
side: `j : C_S → C_{P⊥}` is "the paired strict-to-primitive map … at `q` … from zero to the
unramified condition", all old orthogonal conditions retained (tex 4160–4164). Here, on a
coefficient module `M` (for the paired side: the module of the inverse character `π⁻¹`):

* `dcondCxS j b`: the zero condition (`b = true`, the place is in the support) or the genuine
  unramified condition `[W --(Φ_w − 1)--> W]` (`b = false`); `dpresCondS T`: the old orthogonal
  conditions `Δ'` at `S₀` and these at the new places; `dsuppDataS T`: its Selmer data
  `C_{T⊥}` (definitions). These are lane RC30's `DPp` (`dsuppDataS T`).
* `dfS T p` (definition): the strict-to-orthogonal map `U_{(T ∪ {p})⊥} → U_{T⊥}` (zero to
  unramified at the two places above `p`, the identity elsewhere); lane RC30's `fS`.
* `dpPp`, `dpS`, `dqPp` (definitions), `dret_S`, `dq_S` (PROVED): the components of `U_{T⊥}` and
  `U_{(T ∪ {p})⊥}` at the old places and at `p`, and lane RC30's retention inputs `ret_S`, `q_S`
  for them (with `Uo' = dpresCondS T`, `Uq' = switchUq p`).
* **`selRestrict_dsuppDataS`** (PROVED): `selRestrict (dsuppDataS T) (dfS T p) =
  dsuppDataS (insert p T)` — the strict side of a step is the orthogonal side of the next
  (`R_{i+1}.DPp = selRestrict R_i.DPp R_i.fS`).

**The paired classes.** The text's paired class `z^⊥` is generic: "transport `z` by conjugation,
lift it through the orthogonal comparison at the generic point" (tex 3708–3711); "at a
localization where the full local complexes at active and moving primes are acyclic, the
comparison from the orthogonal condition to the transported condition is a quasi-isomorphism.
Apply its inverse in the derived category to the transported class" (tex 3740–3745). The inverse
exists only where those full local complexes are acyclic (tex 3736–3753); it does not exist
literally at a finite stage ring. It is therefore the one named input here:

* `orthComparison T` (definition): the comparison `c_T : C_{T⊥} → C'_T` from the orthogonal
  conditions to the transported ones (zero to full at `T`, the identity of the unramified condition
  off `T`, a given comparison `φo` at the old places).
* `OrthComparisonInverse` (GLUE, tex 3740–3745): chain-level maps `ψ_T : C'_T → C_{T⊥}` commuting
  with the differential in degrees `0 → 1 → 2`, inverse to `c_T` on degree-one cohomology, and
  compatible with the switches: `j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T`.
* **`hlift_of_transport`** (PROVED): from the transported norm identity
  `z'_R = e · i'(z'_P) + d b'` in `C'_{T ∪ {p}}` (lane E2's `gxClass_step` for `π⁻¹`, with
  `e^c = e`: `H20Paired.eq_paired`), the paired strict lift
  `j z_S = e z_{P⊥} + d b` for `z_S = ψ_{T ∪ {p}}(z'_R)`, `z_{P⊥} = ψ_T(z'_P)` — the field
  `hlift` of lane RC32's `StepRetention`.

Kinds: definitions, GLUE (`OrthComparisonInverse`; uninhabited at a finite stage ring, see its
docstring), PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.DualPres

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom zeroGHom ghomComp changeMap restrictData)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Dual

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

omit [TopologicalSpace k] in
/-- Two chain maps with the same components are equal. Kind: PROVED. -/
theorem ghom_ext {A B : GCx k} (g₁ g₂ : GHom A B) (h : ∀ i j hij, g₁.f i j hij = g₂.f i j hij) :
    g₁ = g₂ := by
  cases g₁
  cases g₂
  congr
  funext i j hij
  exact h i j hij

/-- **The orthogonal condition at a new place** (tex 4160–4164): zero (`true`, the place is in
the support, orthogonal to the full condition) or the genuine unramified condition (`false`).
Kind: definition. -/
def dcondCxS (j : ι × Bool) : Bool → GCx k
  | true => zeroCx k
  | false => genuineUq K S k (place j) (X j)

/-- Its map to the local complex. Kind: definition. -/
def dcondιS (j : ι × Bool) : (b : Bool) → GHom (dcondCxS K S k place X j b)
    (genuineLq K S k M (place j))
  | true => zeroGHom _ _
  | false => (EU j).i

/-- **The orthogonal local conditions of the support `T`** (tex 4160–4164): the old orthogonal
conditions `Δ'` at `S₀`, zero at the places above `p ∈ T`, unramified above `p ∉ T`.
Kind: definition. -/
def dpresCondS (T : Finset ι) :
    LocalConditions k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M where
  U v := match v with
    | .inl v₀ => Δ'.U v₀
    | .inr j => dcondCxS K S k place X j (decide (j.1 ∈ T))
  i v := match v with
    | .inl v₀ => Δ'.i v₀
    | .inr j => dcondιS K S k M place X EU j (decide (j.1 ∈ T))

/-- **The dual Selmer data `C_{T⊥}`** (lane RC30's `DPp`). Kind: definition. -/
abbrev dsuppDataS (T : Finset ι) : SelData k :=
  selData k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M
    (dpresCondS K S₀ S k M Δ' place X EU T)

/-- The map of orthogonal conditions at a new place from the stricter to the less strict one.
Kind: definition. -/
def dcondSplit (j : ι × Bool) : (b b' : Bool) → (b = true → b' = true) →
    GHom (dcondCxS K S k place X j b') (dcondCxS K S k place X j b)
  | _, true, _ => zeroGHom _ _
  | false, false, _ => idGHom _
  | true, false, h => absurd (h rfl) (by decide)

omit [DecidableEq ι] in
theorem dcondSplit_compat (j : ι × Bool) (b b' : Bool) (h : b = true → b' = true) (n : ℤ)
    (x : (dcondCxS K S k place X j b').X n) :
    (dcondιS K S k M place X EU j b).f n n rfl ((dcondSplit K S k place X j b b' h).f n n rfl x) =
      (dcondιS K S k M place X EU j b').f n n rfl x := by
  match b, b', h with
  | b, true, _ =>
    cases b <;> simp [dcondSplit, dcondιS, zeroGHom]
  | false, false, _ => rfl
  | true, false, h => exact absurd (h rfl) (by decide)

/-- The strict-to-orthogonal maps at each place. Kind: definition. -/
def dpresSplit (T : Finset ι) (p : ι) : ∀ v : Places K S₀ ⊕ (ι × Bool),
    GHom ((dpresCondS K S₀ S k M Δ' place X EU (insert p T)).U v)
      ((dpresCondS K S₀ S k M Δ' place X EU T).U v)
  | .inl v₀ => idGHom (Δ'.U v₀)
  | .inr j => dcondSplit K S k place X j (decide (j.1 ∈ T)) (decide (j.1 ∈ insert p T))
      (fun h => by
        rw [decide_eq_true_iff] at h ⊢
        exact Finset.mem_insert_of_mem h)

/-- **The strict-to-orthogonal map `U_{(T ∪ {p})⊥} → U_{T⊥}`** (lane RC30's `fS`; tex 4160–4164).
Kind: definition. -/
def dfS (T : Finset ι) (p : ι) :
    GHom (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).U
      (dsuppDataS K S₀ S k M Δ' place X EU T).U :=
  piMap (dpresSplit K S₀ S k M Δ' place X EU T p)

/-- The strict-to-orthogonal map is compatible with the maps to the local complexes.
Kind: PROVED. -/
theorem dfS_compat (T : Finset ι) (p : ι) (n : ℤ)
    (x : (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).U.X n) :
    (dsuppDataS K S₀ S k M Δ' place X EU T).ι.f n n rfl
        ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl x) =
      (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).ι.f n n rfl x := by
  funext v
  match v with
  | .inl v₀ => rfl
  | .inr j => exact dcondSplit_compat K S k M place X EU j _ _ _ n (x (.inr j))

/-- **The strict side of a step is the orthogonal side of the next** (PROVED):
`selRestrict (dsuppDataS T) (dfS T p) = dsuppDataS (insert p T)`. -/
theorem selRestrict_dsuppDataS (T : Finset ι) (p : ι) :
    selRestrict (dsuppDataS K S₀ S k M Δ' place X EU T) (dfS K S₀ S k M Δ' place X EU T p) =
      dsuppDataS K S₀ S k M Δ' place X EU (insert p T) := by
  change (⟨_, _, _, _, ghomComp (dfS K S₀ S k M Δ' place X EU T p)
    (dsuppDataS K S₀ S k M Δ' place X EU T).ι⟩ : SelData k) = ⟨_, _, _, _, _⟩
  congr 1
  exact ghom_ext k _ _ fun i j h => by
    subst h
    exact LinearMap.ext fun x => dfS_compat K S₀ S k M Δ' place X EU T p i x

/-- The differential of the strict side agrees with that of the next orthogonal side in
degree `0` (PROVED; `dfS_compat`). -/
theorem selD_restrict (T : Finset ι) (p : ι)
    (y : (selCx (dsuppDataS K S₀ S k M Δ' place X EU (insert p T))).X 0) :
    (selCx (selRestrict (dsuppDataS K S₀ S k M Δ' place X EU T)
        (dfS K S₀ S k M Δ' place X EU T p))).d 0 1 rfl y =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU (insert p T))).d 0 1 rfl y := by
  obtain ⟨a, u, x⟩ := y
  change (_, _, _ - (dsuppDataS K S₀ S k M Δ' place X EU T).ι.f 0 0 rfl
      ((dfS K S₀ S k M Δ' place X EU T p).f 0 0 rfl u) - _) = (_, _, _ - _ - _)
  rw [dfS_compat]
  rfl

/-! ### The components of the dual chain for lane RC30's retention inputs -/

/-- An orthogonal condition off the support is the genuine unramified condition. Kind: definition.
-/
def dToUr (j : ι × Bool) : (b : Bool) → b = false →
    GHom (dcondCxS K S k place X j b) (genuineUq K S k (place j) (X j))
  | false, _ => idGHom _
  | true, h => Bool.noConfusion h

omit [DecidableEq ι] in
/-- The strict map out of a zero condition is zero. Kind: PROVED. -/
theorem dcondSplit_of_true (j : ι × Bool) (b b' : Bool) (hb' : b' = true)
    (h : b = true → b' = true) (n : ℤ) (y : (dcondCxS K S k place X j b').X n) :
    (dcondSplit K S k place X j b b' h).f n n rfl y = 0 := by
  subst hb'
  cases b <;> rfl

/-- **The old orthogonal components `p_{P⊥,v}`** (lane RC30's `pPp`): the projections of
`U_{T⊥}` onto its factors. Kind: definition. -/
def dpPp (T : Finset ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ) :
    (dsuppDataS K S₀ S k M Δ' place X EU T).U.X n →ₗ[k]
      ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X n :=
  LinearMap.proj v

/-- **The old strict components `p_{S,v}`** (lane RC30's `pS`): `p_{P⊥,v} ∘ j`.
Kind: definition. -/
def dpS (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ) :
    (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).U.X n →ₗ[k]
      ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X n :=
  (dpPp K S₀ S k M Δ' place X EU T v n).comp ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl)

/-- **Every old orthogonal condition is retained by `j`** (lane RC30's `ret_S`; PROVED, by
definition). -/
theorem dret_S (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ)
    (x : (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).U.X n) :
    dpPp K S₀ S k M Δ' place X EU T v n ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl x) =
      dpS K S₀ S k M Δ' place X EU T p v n x :=
  rfl

/-- **The `q`-component of `U_{T⊥}`** (lane RC30's `qPp`): the projection onto the two
unramified conditions above `p ∉ T`, in lane RC32's `switchUq p`. Kind: definition. -/
def dqPp (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ) :
    (dsuppDataS K S₀ S k M Δ' place X EU T).U.X n →ₗ[k] (switchUq K S k place X p).X n :=
  LinearMap.prod
    (((dToUr K S k place X (p, false) (decide (p ∈ T)) (decide_eq_false hp)).f n n rfl).comp
      (LinearMap.proj (R := k) (φ := fun v => ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X n)
        (Sum.inr (p, false))))
    (((dToUr K S k place X (p, true) (decide (p ∈ T)) (decide_eq_false hp)).f n n rfl).comp
      (LinearMap.proj (R := k) (φ := fun v => ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X n)
        (Sum.inr (p, true))))

/-- **At `q`, `j` is the map from zero to the unramified condition** (lane RC30's `q_S`;
tex 4163–4164; PROVED). -/
theorem dq_S (T : Finset ι) (p : ι) (hp : p ∉ T) (n : ℤ)
    (x : (dsuppDataS K S₀ S k M Δ' place X EU (insert p T)).U.X n) :
    dqPp K S₀ S k M Δ' place X EU T p hp n
      ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl x) = 0 := by
  have h0 : ∀ b : Bool, (dfS K S₀ S k M Δ' place X EU T p).f n n rfl x (.inr (p, b)) = 0 :=
    fun b => dcondSplit_of_true K S k place X (p, b) _ _
      (decide_eq_true (Finset.mem_insert_self p T)) _ n _
  refine Prod.ext ?_ ?_
  · change (dToUr K S k place X (p, false) (decide (p ∈ T)) (decide_eq_false hp)).f n n rfl
      ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl x (Sum.inr (p, false))) = 0
    rw [h0 false]
    exact map_zero _
  · change (dToUr K S k place X (p, true) (decide (p ∈ T)) (decide_eq_false hp)).f n n rfl
      ((dfS K S₀ S k M Δ' place X EU T p).f n n rfl x (Sum.inr (p, true))) = 0
    rw [h0 true]
    exact map_zero _

end Dual

/-! ### The inverse of the orthogonal comparison and the paired strict lift -/

section Lift

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ' Δ'' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- The comparison from an orthogonal condition at a new place to the transported condition:
zero to full (`true`), the identity of the unramified condition (`false`). Kind: definition. -/
def dcomp (j : ι × Bool) : (b : Bool) →
    GHom (dcondCxS K S k place X j b) (condCxS K S k M place X j b)
  | true => zeroGHom _ _
  | false => idGHom _

omit [DecidableEq ι] in
theorem dcomp_compat (j : ι × Bool) (b : Bool) (n : ℤ) (x : (dcondCxS K S k place X j b).X n) :
    (condιS K S k M place X EU j b).f n n rfl ((dcomp K S k M place X j b).f n n rfl x) =
      (dcondιS K S k M place X EU j b).f n n rfl x := by
  cases b <;> rfl

/-- **The orthogonal comparison at each place** (tex 3740–3745): the given comparison `φo` of the
old orthogonal conditions with the transported ones, and `dcomp` at the new places.
Kind: definition. -/
def presComparison (φo : ∀ v₀ : Places K S₀, GHom (Δ'.U v₀) (Δ''.U v₀)) (T : Finset ι) :
    ∀ v : Places K S₀ ⊕ (ι × Bool), GHom ((dpresCondS K S₀ S k M Δ' place X EU T).U v)
      ((presCondS K S₀ S k M Δ'' place X EU T).U v)
  | .inl v₀ => φo v₀
  | .inr j => dcomp K S k M place X j (decide (j.1 ∈ T))

theorem presComparison_compat (φo : ∀ v₀ : Places K S₀, GHom (Δ'.U v₀) (Δ''.U v₀))
    (hφo : ∀ v₀ (n : ℤ) (x : (Δ'.U v₀).X n),
      (Δ''.i v₀).f n n rfl ((φo v₀).f n n rfl x) = (Δ'.i v₀).f n n rfl x) (T : Finset ι)
    (v : Places K S₀ ⊕ (ι × Bool)) (n : ℤ)
    (x : ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X n) :
    ((presCondS K S₀ S k M Δ'' place X EU T).i v).f n n rfl
        ((presComparison K S₀ S k M Δ' Δ'' place X EU φo T v).f n n rfl x) =
      ((dpresCondS K S₀ S k M Δ' place X EU T).i v).f n n rfl x := by
  match v with
  | .inl v₀ => exact hφo v₀ n x
  | .inr j => exact dcomp_compat K S k M place X EU j _ n x

/-- **The orthogonal comparison `c_T : C_{T⊥} → C'_T`** (tex 3740–3745): from the orthogonal
conditions to the transported conditions (lane RC26's `condMap`). Kind: definition. -/
def orthComparison (φo : ∀ v₀ : Places K S₀, GHom (Δ'.U v₀) (Δ''.U v₀))
    (hφo : ∀ v₀ (n : ℤ) (x : (Δ'.U v₀).X n),
      (Δ''.i v₀).f n n rfl ((φo v₀).f n n rfl x) = (Δ'.i v₀).f n n rfl x) (T : Finset ι) :
    GHom (selCx (dsuppDataS K S₀ S k M Δ' place X EU T))
      (suppCxS K S₀ S k M Δ'' place X EU T) :=
  condMap _ _ (presComparison K S₀ S k M Δ' Δ'' place X EU φo T)
    (presComparison_compat K S₀ S k M Δ' Δ'' place X EU φo hφo T)

/-- **The chain-level inverse of the orthogonal comparison** (GLUE, tex 3740–3745): with the
comparison `c_T : C_{T⊥} → C'_T` (`orthComparison`, from the given comparison `φo` of the old
orthogonal conditions `Δ'` with the transported ones `Δ''`), maps `ψ_T : C'_T → C_{T⊥}` commuting
with the differential in degrees `0 → 1 → 2` (`hd`, `hd₁`; so `ψ_T` induces a map on `H¹`), mutually
inverse to `c_T` on degree-one cohomology (`hright`, `hleft`: up to coboundaries on cocycles), and
commuting with the switches (`j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T`). The text's comparison from the
orthogonal condition to the transported condition is a quasi-isomorphism only at a localization
where the full local complexes at the active and moving primes are acyclic (tex 3736–3753): its
inverse is taken in the derived category there, so it does not exist literally at a finite stage
ring. This structure is that inverse, as the one named input; `hright` already fails for `ψ = 0`
unless every degree-one cocycle of `C'_T` is a coboundary. CAVEAT: at a finite stage ring with
`ι ≠ ∅` and a nonzero `G_{K_w}`-invariant at a place `w = place (p, false)`, it is uninhabited for
any `φo` (lane E1's `not_orthComparisonInverse`, `CloudB3E1Torsion/OrthNoInverse.lean`, from
`no_H1_inverse`). Results taking it (`hlift_of_transport`, `hlift_stepRetention`, `hlift_actual`)
are conditional on an unsatisfiable input there, and nothing in the headline uses them. The text's
inverse lives after the inner limit, over the generic coefficient ring (`Frac Λ`, or `𝒪[G]` with
`𝒪` the completion of `ℤ₂[[t]]_(2)`), with the retained old-place lattice comparison
(tex 3704–3790); a localized restatement `OrthComparisonInverseLoc` is planned for lane RC32's
round 17. Of the fields only `ψ`, `hd` and `hsw` are used (`hlift_of_transport`).
Kind: definition (GLUE; not satisfiable at a finite stage ring). -/
structure OrthComparisonInverse where
  /-- the comparison of the old orthogonal conditions with the transported ones -/
  φo : ∀ v₀ : Places K S₀, GHom (Δ'.U v₀) (Δ''.U v₀)
  /-- it is compatible with the maps to the local complexes -/
  φo_compat : ∀ v₀ (n : ℤ) (x : (Δ'.U v₀).X n),
    (Δ''.i v₀).f n n rfl ((φo v₀).f n n rfl x) = (Δ'.i v₀).f n n rfl x
  /-- the inverse of the comparison, degreewise -/
  ψ : ∀ (T : Finset ι) (n : ℤ), (suppCxS K S₀ S k M Δ'' place X EU T).X n →ₗ[k]
    (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X n
  /-- it commutes with the differential -/
  hd : ∀ (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 0),
    ψ T 1 ((suppCxS K S₀ S k M Δ'' place X EU T).d 0 1 rfl x) =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl (ψ T 0 x)
  /-- it commutes with the differential in degree one (so it sends cocycles to cocycles) -/
  hd₁ : ∀ (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1),
    ψ T 2 ((suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl x) =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 1 2 rfl (ψ T 1 x)
  /-- it commutes with the switches: `j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T` -/
  hsw : ∀ (T : Finset ι) (p : ι), p ∉ T → ∀ x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1,
    (changeMap (dsuppDataS K S₀ S k M Δ' place X EU T) (dfS K S₀ S k M Δ' place X EU T p)).f 1 1
        rfl (ψ (insert p T) 1 ((suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl x)) =
      ψ T 1 x
  /-- `c_T ∘ ψ_T` is the identity on degree-one cohomology -/
  hright : ∀ (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1),
    (suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl x = 0 →
      ∃ y : (suppCxS K S₀ S k M Δ'' place X EU T).X 0,
        (orthComparison K S₀ S k M Δ' Δ'' place X EU φo φo_compat T).f 1 1 rfl (ψ T 1 x) =
          x + (suppCxS K S₀ S k M Δ'' place X EU T).d 0 1 rfl y
  /-- `ψ_T ∘ c_T` is the identity on degree-one cohomology -/
  hleft : ∀ (T : Finset ι) (z : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 1),
    (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 1 2 rfl z = 0 →
      ∃ y : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 0,
        ψ T 1 ((orthComparison K S₀ S k M Δ' Δ'' place X EU φo φo_compat T).f 1 1 rfl z) =
          z + (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl y

variable {K S₀ S k M Δ' Δ'' place X EU}

/-- `j : C_{(T ∪ {p})⊥} → C_{T⊥}`, lane RC26's `changeMap` read on the next orthogonal side
(`selRestrict_dsuppDataS`). Kind: definition. -/
def jmap (T : Finset ι) (p : ι) (n : ℤ) :
    (selCx (dsuppDataS K S₀ S k M Δ' place X EU (insert p T))).X n →ₗ[k]
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X n :=
  (changeMap (dsuppDataS K S₀ S k M Δ' place X EU T) (dfS K S₀ S k M Δ' place X EU T p)).f n n rfl

/-- `j` commutes with the differential in degree `0` (PROVED). -/
theorem jmap_d (T : Finset ι) (p : ι)
    (y : (selCx (dsuppDataS K S₀ S k M Δ' place X EU (insert p T))).X 0) :
    jmap T p 1 ((selCx (dsuppDataS K S₀ S k M Δ' place X EU (insert p T))).d 0 1 rfl y) =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl (jmap T p 0 y) :=
  (congrArg ((changeMap (dsuppDataS K S₀ S k M Δ' place X EU T)
      (dfS K S₀ S k M Δ' place X EU T p)).f 1 1 rfl)
    (selD_restrict K S₀ S k M Δ' place X EU T p y)).symm.trans
    ((changeMap (dsuppDataS K S₀ S k M Δ' place X EU T)
      (dfS K S₀ S k M Δ' place X EU T p)).comm 0 1 0 1 rfl rfl rfl rfl y)

/-- **The paired strict lift `j z_S = e z_{P⊥} + d b`** (PROVED, conditional on `Ψ`, which is
uninhabited at a finite stage ring: see the caveat at `OrthComparisonInverse`; tex 4169–4171): from
the
transported norm identity `z'_R = e · i'(z'_P) + d b'` in `C'_{T ∪ {p}}` and the inverse `Ψ` of
the orthogonal comparison, with `z_S = ψ_{T ∪ {p}}(z'_R)`, `z_{P⊥} = ψ_T(z'_P)` and
`b = j(ψ_{T ∪ {p}}(b'))`. -/
theorem hlift_of_transport
    (Ψ : OrthComparisonInverse K S₀ S k M Δ' Δ'' place X EU) {T : Finset ι} {p : ι} (hp : p ∉ T)
    (zR : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 1)
    (zP : (suppCxS K S₀ S k M Δ'' place X EU T).X 1) (e : k)
    (b' : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl zP +
      (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).d 0 1 rfl b') :
    jmap T p 1 (Ψ.ψ (insert p T) 1 zR) =
      e • Ψ.ψ T 1 zP + (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl
        (jmap T p 0 (Ψ.ψ (insert p T) 0 b')) := by
  have hsw : jmap T p 1 (Ψ.ψ (insert p T) 1 ((suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1
      rfl zP)) = Ψ.ψ T 1 zP := Ψ.hsw T p hp zP
  rw [hnorm, map_add, map_smul, Ψ.hd, map_add, map_smul, hsw, jmap_d]

/-- **The paired strict lift in the form of lane RC32's `StepRetention.hlift`** (PROVED): for
`DPp = dsuppDataS T`, `fS = dfS T p`, `z_S = ψ_{T ∪ {p}}(z'_R)` (a class of
`selRestrict DPp fS = dsuppDataS (insert p T)`). -/
theorem hlift_stepRetention
    (Ψ : OrthComparisonInverse K S₀ S k M Δ' Δ'' place X EU) {T : Finset ι} {p : ι} (hp : p ∉ T)
    (zR : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 1)
    (zP : (suppCxS K S₀ S k M Δ'' place X EU T).X 1) (e : k)
    (b' : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl zP +
      (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).d 0 1 rfl b') :
    (changeMap (dsuppDataS K S₀ S k M Δ' place X EU T) (dfS K S₀ S k M Δ' place X EU T p)).f 1 1
        rfl (Ψ.ψ (insert p T) 1 zR) =
      e • Ψ.ψ T 1 zP + (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl
        (jmap T p 0 (Ψ.ψ (insert p T) 0 b')) :=
  hlift_of_transport Ψ hp zR zP e b' hnorm

end Lift

end ZInQ.Contrib.CloudB3E2.DualPres

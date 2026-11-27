import ZInQKernel.Contrib.OneProof.RC.Uniform.QuadraticCase

/-!
# RC53 SwitchInputs: the sign splitting at the quadratic primes `(t)` and `(t+2)`

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, quadratic case, tex
L5003–5054 and L5083–5115 (Elliot's own step):

> The action `c^τ(g) = J c(τ⁻¹ g τ)`, `J = ρ_T(τ)`, on cocycles gives a `k`-linear involution on
> cohomology. [...] We write `V = V_+ ⊕ V_-` for the resulting cohomology signs. At a new inert
> derivative prime write `F, S` for the finite and singular planes. The action on `F` is `J`, and
> that on `S` is `-J`. [...] Choose nonzero `J`-eigenvectors `e_+, e_-`. They form a basis and
> `e₂(e_+, e_-) ≠ 0`. The two local cohomology signs are therefore `H_+ = F(e_+) ⊕ S(e_-)`,
> `H_- = F(e_-) ⊕ S(e_+)`. [...] The space `U` is stable under signs. Each `U_± ⊂ H_±` is its own
> annihilator in `H_±`, hence is one of that plane's two isotropic axes. We also need one prime
> detecting prescribed classes of opposite signs.

This file derives, over a field `k` with `2 ≠ 0`, the sign fields of the quadratic switch data
(`ep, em, hp, hm, he, Up, Um, hUp, hUm, hdetp, hdetm` of the switching data of the uniform-switch
area) from the cohomological inputs, using the planar algebra of the uniform lane
(`QuadraticCase.lean`).

Nodes (PROVED unless marked):
* `InvolutionSplitting`: a linear involution of a vector space (`2 ≠ 0`) splits it as the direct sum
  of its `±1`-eigenspaces, `dim V = dim V_+ + dim V_-`.
* `CohomologySignSplitting` (tex L5009–5013, L5026): an involutive chain endomorphism `σ` of a
  cochain complex over `k` (the action `c ↦ J c(τ⁻¹ · τ)`; GLUE that it is the actual action on
  the Galois cochains, not stated) induces an involution of `H¹`, and `H¹ = V_+ ⊕ V_-` with
  `dim H¹ = dim V_+ + dim V_-`.
* `LocalSignPlanes` (tex L5026–5054): for `J² = 1`, `det J = −1`, there are eigenvectors
  `e_+, e_-` with `e₂(e_+, e_-) ≠ 0`; `H_±` are the `±1`-eigenspaces of the local involution
  `(x, y) ↦ (Jx, −Jy)`, complementary, mutually orthogonal and nondegenerate for the local pairing.
* `SelfAnnihilatingSigns` (tex L5065–5085): if `U ⊆ F ⊕ S` is stable under the local involution and
  `U = U^⊥` (GLUE input: the localization duality, Nekovář 6.3.3–6.3.4, as a hypothesis), then
  `U = U_+ ⊔ U_-` with `U_± = U ∩ H_±` its own annihilator in `H_±`, hence an axis.
* `DetectionFields` (tex L5086–5115): `hdetp`, `hdetm` from equivariant localization of classes
  `c_± ∈ V_±` whose localizations lie in `U ∩ F` (the exact sequence (5.5a)) and are nonzero (the
  detecting prime: GLUE input `DetectingPrime`, Chebotarev/kernel detection, as hypotheses).
* `QuadSignFields`: all sign fields at once, in the order of the switching data.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module ZInQ.Manuscript.RC.Uniform.QuadraticCase CategoryTheory

/-! ### Involutions -/

section Involution

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The `+1`-eigenspace `{v | T v = v}`. -/
def plusPart (T : V →ₗ[k] V) : Submodule k V := LinearMap.ker (T - LinearMap.id)

/-- The `−1`-eigenspace `{v | T v = −v}`. -/
def minusPart (T : V →ₗ[k] V) : Submodule k V := LinearMap.ker (T + LinearMap.id)

theorem mem_plusPart {T : V →ₗ[k] V} {v : V} : v ∈ plusPart T ↔ T v = v := by
  simp [plusPart, sub_eq_zero]

theorem mem_minusPart {T : V →ₗ[k] V} {v : V} : v ∈ minusPart T ↔ T v = -v := by
  simp [minusPart, add_eq_zero_iff_eq_neg]

/-- **Involution splitting.** For a linear involution `T` (`T ∘ T = 1`) of a vector space over a
field with `2 ≠ 0`: `V_+ ⊓ V_- = 0`, `V_+ ⊔ V_- = V`, and, if `V` is finite dimensional,
`dim V = dim V_+ + dim V_-`. Classification: PROVED. -/
def InvolutionSplitting : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] (T : V →ₗ[k] V),
    (2 : k) ≠ 0 → T ∘ₗ T = LinearMap.id →
      plusPart T ⊓ minusPart T = ⊥ ∧ plusPart T ⊔ minusPart T = ⊤ ∧
      (FiniteDimensional k V →
        finrank k V = finrank k (plusPart T) + finrank k (minusPart T))

theorem involutionSplitting_proof : InvolutionSplitting := by
  intro k V _ _ _ T h2 hT
  have hTT : ∀ v, T (T v) = v := fun v => LinearMap.congr_fun hT v
  have hinf : plusPart T ⊓ minusPart T = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hp, hm⟩ := Submodule.mem_inf.1 hv
    rw [mem_plusPart] at hp
    rw [mem_minusPart] at hm
    have h : (2 : k) • v = 0 := by
      rw [two_smul]; nth_rewrite 1 [← hp]; rw [hm, neg_add_cancel]
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.1 h).resolve_left h2
  have hsup : plusPart T ⊔ minusPart T = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (2⁻¹ : k) • (v + T v) + (2⁻¹ : k) • (v - T v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul k v, smul_smul, inv_mul_cancel₀ h2,
        one_smul]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_plusPart, map_smul, map_add, hTT, add_comm]
    · rw [mem_minusPart, map_smul, map_sub, hTT, ← smul_neg, neg_sub]
  refine ⟨hinf, hsup, fun hfin => ?_⟩
  have := Submodule.finrank_sup_add_finrank_inf_eq (plusPart T) (minusPart T)
  rw [hsup, hinf, finrank_bot, add_zero, finrank_top] at this
  exact this

end Involution

/-! ### The cohomology signs -/

/-- **The cohomology signs** (tex L5009–5013, L5026: "The action `c^τ(g) = J c(τ⁻¹ g τ)` on
cocycles gives a `k`-linear involution on cohomology. [...] We write `V = V_+ ⊕ V_-`"). Let `K`
be a cochain complex of `k`-vector spaces (the fibre Selmer complex `C ⊗_R k`) and `σ : K ⟶ K` an
involutive chain map (`σ ≫ σ = 𝟙`; the cocycle action, GLUE that it is the actual action on the
Galois cochains). Then `T = H¹(σ)` is an involution of `V = H¹(K)`, `V = V_+ ⊕ V_-`, and
`dim V = dim V_+ + dim V_-` when `V` is finite dimensional. Classification: PROVED. -/
def CohomologySignSplitting : Prop :=
  ∀ (k : Type) [Field k] (K : CochainComplex (ModuleCat.{0} k) ℤ) (σ : K ⟶ K),
    (2 : k) ≠ 0 → σ ≫ σ = 𝟙 K →
      let T : K.homology 1 →ₗ[k] K.homology 1 := (HomologicalComplex.homologyMap σ 1).hom
      T ∘ₗ T = LinearMap.id ∧
      plusPart T ⊓ minusPart T = ⊥ ∧ plusPart T ⊔ minusPart T = ⊤ ∧
      (FiniteDimensional k (K.homology 1) →
        finrank k (K.homology 1) = finrank k (plusPart T) + finrank k (minusPart T))

theorem cohomologySignSplitting_proof : CohomologySignSplitting := by
  intro k _ K σ h2 hσ T
  have hT : T ∘ₗ T = LinearMap.id := by
    have h := congrArg (fun f => ModuleCat.Hom.hom f)
      (HomologicalComplex.homologyMap_comp σ σ 1)
    simp only [hσ, HomologicalComplex.homologyMap_id, ModuleCat.hom_id, ModuleCat.hom_comp] at h
    exact h.symm
  exact ⟨hT, involutionSplitting_proof k _ T h2 hT⟩

/-! ### The local sign planes -/

section Local

variable {k : Type*} [Field k]

/-- The local involution `(x, y) ↦ (Jx, −Jy)` on `F ⊕ S` (tex L5026–5027: "The action on `F` is
`J`, and that on `S` is `−J`"). -/
def localInv (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  LinearMap.prodMap J (-J)

@[simp] theorem localInv_apply (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (u : (Fin 2 → k) × (Fin 2 → k)) :
    localInv J u = (J u.1, -J u.2) := by
  simp [localInv]

/-- **The local sign planes** (tex L5026–5054). For `J² = 1`, `det J = −1`, `2 ≠ 0`, `ε ≠ 0`:
there are eigenvectors `e_+, e_-` (`J e_± = ±e_±`) with `e₂(e_+, e_-) ≠ 0`, such that
`H_+ = F(e_+) ⊕ S(e_-)` and `H_- = F(e_-) ⊕ S(e_+)` are exactly the `+1`- and `−1`-eigenspaces of
the local involution, `H_+ ⊓ H_- = 0`, `H_+ ⊔ H_- = F ⊕ S`, `H_+ ⊥ H_-` for the local pairing, and
both are nondegenerate. Classification: PROVED. -/
def LocalSignPlanes : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ε : k), (2 : k) ≠ 0 → ε ≠ 0 →
    J ∘ₗ J = LinearMap.id → LinearMap.det J = -1 →
    ∃ ep em : Fin 2 → k, J ep = ep ∧ J em = -em ∧ e₂ ep em ≠ 0 ∧
      signPlane ep em = plusPart (localInv J) ∧ signPlane em ep = minusPart (localInv J) ∧
      signPlane ep em ⊓ signPlane em ep = ⊥ ∧ signPlane ep em ⊔ signPlane em ep = ⊤ ∧
      (∀ u ∈ signPlane ep em, ∀ w ∈ signPlane em ep, localPair ε J u w = 0) ∧
      (∀ u ∈ signPlane ep em, (∀ w ∈ signPlane ep em, localPair ε J u w = 0) → u = 0) ∧
      (∀ u ∈ signPlane em ep, (∀ w ∈ signPlane em ep, localPair ε J u w = 0) → u = 0)

theorem localInv_involutive (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id) :
    localInv J ∘ₗ localInv J = LinearMap.id := by
  have hJJ : ∀ z, J (J z) = z := fun z => LinearMap.congr_fun hJ2 z
  ext u <;> simp [hJJ]

theorem plus_eq_signPlane {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)} (h2 : (2 : k) ≠ 0)
    {ep em : Fin 2 → k} (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    signPlane ep em = plusPart (localInv J) := by
  ext u
  rw [mem_signPlane_plus_iff h2 hp hm he, mem_plusPart, localInv_apply, Prod.ext_iff]
  dsimp only
  rw [neg_eq_iff_eq_neg]

theorem minus_eq_signPlane {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)} (h2 : (2 : k) ≠ 0)
    {ep em : Fin 2 → k} (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    signPlane em ep = minusPart (localInv J) := by
  ext u
  rw [mem_signPlane_minus_iff h2 hp hm he, mem_minusPart, localInv_apply, Prod.ext_iff]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_inj]

theorem localSignPlanes_proof : LocalSignPlanes := by
  intro k _ J ε h2 hε hJ2 hdet
  obtain ⟨ep, em, -, -, hp, hm, he, -, -⟩ := exists_J_eigenbasis h2 J hJ2 hdet
  obtain ⟨-, horth, hnp, hnm, -⟩ := sign_planes_hyperbolic ε hε J ep em hp hm he
  obtain ⟨hinf, hsup, -⟩ := involutionSplitting_proof k _ (localInv J) h2 (localInv_involutive J hJ2)
  have e1 := plus_eq_signPlane h2 hp hm he
  have e2 := minus_eq_signPlane h2 hp hm he
  refine ⟨ep, em, hp, hm, he, e1, e2, ?_, ?_, horth, hnp, hnm⟩
  · rw [e1, e2]; exact hinf
  · rw [e1, e2]; exact hsup

/-! ### The self-annihilating sign parts -/

/-- **The sign parts of `U` are axes** (tex L5065–5085). Let `J² = 1`, `det J = −1`, `2 ≠ 0`,
`ε ≠ 0`, `e_±` eigenvectors with `e₂(e_+, e_-) ≠ 0`, and `U ⊆ F ⊕ S` stable under the local
involution with `U = U^⊥` for the local pairing (the GLUE input `hU`: the localization duality,
Nekovář 6.3.3–6.3.4, "its kernel is both `U` and `U^⊥`", as a hypothesis). Then `U = U_+ ⊔ U_-`
for `U_± = U ⊓ H_±`, each `U_±` is its own annihilator in `H_±` (the fields `hUp`, `hUm`), and is
one of the two axes of `H_±`. Classification: PROVED (from the stated duality hypothesis). -/
def SelfAnnihilatingSigns : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ε : k) (ep em : Fin 2 → k),
    (2 : k) ≠ 0 → ε ≠ 0 → J ∘ₗ J = LinearMap.id → J ep = ep → J em = -em → e₂ ep em ≠ 0 →
    ∀ U : Submodule k ((Fin 2 → k) × (Fin 2 → k)),
      (∀ u ∈ U, localInv J u ∈ U) → (∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε J u w = 0) →
      U = (U ⊓ signPlane ep em) ⊔ (U ⊓ signPlane em ep) ∧
      IsSelfAnnihilatingIn ε J (signPlane ep em) (U ⊓ signPlane ep em) ∧
      IsSelfAnnihilatingIn ε J (signPlane em ep) (U ⊓ signPlane em ep) ∧
      (U ⊓ signPlane ep em = finAxis ep ∨ U ⊓ signPlane ep em = singAxis em) ∧
      (U ⊓ signPlane em ep = finAxis em ∨ U ⊓ signPlane em ep = singAxis ep)

theorem selfAnnihilatingSigns_proof : SelfAnnihilatingSigns := by
  intro k _ J ε ep em h2 hε hJ2 hp hm he U hσ hU
  have hσ' : ∀ u ∈ U, ((J u.1, -J u.2) : (Fin 2 → k) × (Fin 2 → k)) ∈ U := fun u hu => by
    simpa using hσ u hu
  obtain ⟨hUp, hUm⟩ := selfAnnihilating_sign_parts h2 ε J hJ2 ep em hp hm he U hσ' hU
  obtain ⟨ax1, -⟩ := selfAnnihilating_eq_axis h2 ε hε J ep em hp hm he (U ⊓ signPlane ep em)
  obtain ⟨-, ax2⟩ := selfAnnihilating_eq_axis h2 ε hε J ep em hp hm he (U ⊓ signPlane em ep)
  refine ⟨?_, hUp, hUm, ax1.1 hUp, ax2.1 hUm⟩
  apply le_antisymm
  · intro w hw
    have hLL : ∀ v, localInv J (localInv J v) = v := fun v =>
      LinearMap.congr_fun (localInv_involutive J hJ2) v
    have hv : w = (2⁻¹ : k) • (w + localInv J w) + (2⁻¹ : k) • (w - localInv J w) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul k w, smul_smul, inv_mul_cancel₀ h2,
        one_smul]
    rw [hv]
    refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨?_, ?_⟩) (Submodule.mem_inf.2 ⟨?_, ?_⟩)
    · exact U.smul_mem _ (U.add_mem hw (hσ w hw))
    · rw [plus_eq_signPlane h2 hp hm he, mem_plusPart, map_smul, map_add, hLL, add_comm]
    · exact U.smul_mem _ (U.sub_mem hw (hσ w hw))
    · rw [minus_eq_signPlane h2 hp hm he, mem_minusPart, map_smul, map_sub, hLL, ← smul_neg,
        neg_sub]
  · exact sup_le inf_le_left inf_le_left

/-! ### Detection -/

/-- **GLUE input: a detecting prime** (tex L5086–5115: "We also need one prime detecting
prescribed classes of opposite signs. Choose nonzero `c_+ ∈ V_+` and `c_- ∈ V_-`. [...]"). For the
fibre cohomology `V` with its sign involution `T`, a localization map `loc : V → F ⊕ S` at the new
prime and classes `c_± ∈ V_±`: the localizations are nonzero. This is the conclusion of the
kernel-detection/Chebotarev argument of tex L5086–5115 (Lemma `ex:limits-kernel-detection`), which
needs the Galois representation; its stateable hypotheses (the signs of `c_±`) are in the type.
Classification: GLUE (assumed input). -/
def DetectingPrime {V : Type*} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V)
    (loc : V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (cp cm : V) : Prop :=
  T cp = cp → T cm = -cm → loc cp ≠ 0 ∧ loc cm ≠ 0

/-- **The detection fields** (tex L5086–5120). Let `J² = 1`, `2 ≠ 0`, `e_±` eigenvectors with
`e₂(e_+, e_-) ≠ 0`, `V` the fibre cohomology with sign involution `T`, `loc : V → F ⊕ S` the
localization at the new prime, equivariant for `T` and the local involution (tex L5065–5069: "All
old conditions are stable under this involution"), and `c_± ∈ V_±` whose localizations lie in `U`
and in the finite plane `F` (the exact sequence (5.5a): classes of `V = H¹(C_F ⊗ k)` localize into
`U ∩ F`) and are nonzero (`DetectingPrime`). Then `U_± = U ⊓ H_±` contains a nonzero vector of its
finite axis `F(e_±)`: the fields `hdetp`, `hdetm`. Classification: PROVED (from the inputs). -/
def DetectionFields : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k),
    (2 : k) ≠ 0 → J ep = ep → J em = -em → e₂ ep em ≠ 0 →
    ∀ (V : Type) [AddCommGroup V] [Module k V] (T : V →ₗ[k] V)
      (loc : V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
      (cp cm : V),
      (∀ v, loc (T v) = localInv J (loc v)) →
      T cp = cp → T cm = -cm →
      loc cp ∈ U → loc cm ∈ U → (loc cp).2 = 0 → (loc cm).2 = 0 →
      DetectingPrime T loc cp cm →
      (∃ x ∈ U ⊓ signPlane ep em, x ∈ finAxis ep ∧ x ≠ 0) ∧
      (∃ x ∈ U ⊓ signPlane em ep, x ∈ finAxis em ∧ x ≠ 0)

theorem detectionFields_proof : DetectionFields := by
  intro k _ J ep em h2 hp hm he V _ _ T loc U cp cm hloc hcp hcm hUp hUm hFp hFm hdet
  obtain ⟨hp0, hm0⟩ := hdet hcp hcm
  have hplus : loc cp ∈ signPlane ep em := by
    rw [plus_eq_signPlane h2 hp hm he, mem_plusPart, ← hloc, hcp]
  have hminus : loc cm ∈ signPlane em ep := by
    rw [minus_eq_signPlane h2 hp hm he, mem_minusPart, ← hloc, hcm, map_neg]
  have fin_of : ∀ {f s : Fin 2 → k} {x : (Fin 2 → k) × (Fin 2 → k)},
      x ∈ signPlane f s → x.2 = 0 → x ∈ finAxis f := by
    intro f s x hx h0
    obtain ⟨a, b, rfl⟩ := mem_signPlane.1 hx
    exact mem_finAxis.2 ⟨a, Prod.ext rfl h0⟩
  exact ⟨⟨loc cp, Submodule.mem_inf.2 ⟨hUp, hplus⟩, fin_of hplus hFp, hp0⟩,
    ⟨loc cm, Submodule.mem_inf.2 ⟨hUm, hminus⟩, fin_of hminus hFm, hm0⟩⟩

/-! ### All sign fields -/

/-- **The sign fields of the quadratic switch data** (tex L5003–5120), in the order of the
switching data (`ep em hp hm he Up Um hUp hUm hdetp hdetm`). From `J² = 1`, `det J = −1`,
`2 ≠ 0`, `ε ≠ 0`, the localization image `U ⊆ F ⊕ S` stable under the local involution with
`U = U^⊥` (GLUE input, localization duality), and equivariant localizations of detected classes of
both signs in `U ∩ F` (`DetectingPrime`, GLUE input), there are eigenvectors and self-annihilating
sign parts with the detection property. Classification: PROVED (from the inputs). -/
def QuadSignFields : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ε : k),
    (2 : k) ≠ 0 → ε ≠ 0 → J ∘ₗ J = LinearMap.id → LinearMap.det J = -1 →
    ∀ (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))),
      (∀ u ∈ U, localInv J u ∈ U) → (∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε J u w = 0) →
    ∀ (V : Type) [AddCommGroup V] [Module k V] (T : V →ₗ[k] V)
      (loc : V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (cp cm : V),
      (∀ v, loc (T v) = localInv J (loc v)) → T cp = cp → T cm = -cm →
      loc cp ∈ U → loc cm ∈ U → (loc cp).2 = 0 → (loc cm).2 = 0 →
      DetectingPrime T loc cp cm →
      ∃ (ep em : Fin 2 → k) (Up Um : Submodule k ((Fin 2 → k) × (Fin 2 → k))),
        J ep = ep ∧ J em = -em ∧ e₂ ep em ≠ 0 ∧
        IsSelfAnnihilatingIn ε J (signPlane ep em) Up ∧
        IsSelfAnnihilatingIn ε J (signPlane em ep) Um ∧
        (∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0) ∧ (∃ x ∈ Um, x ∈ finAxis em ∧ x ≠ 0) ∧
        U = Up ⊔ Um

theorem quadSignFields_proof : QuadSignFields := by
  intro k _ J ε h2 hε hJ2 hdet U hσ hU V _ _ T loc cp cm hloc hcp hcm hUp hUm hFp hFm hD
  obtain ⟨ep, em, -, -, hp, hm, he, -, -⟩ := exists_J_eigenbasis h2 J hJ2 hdet
  obtain ⟨hsum, hAp, hAm, -, -⟩ := selfAnnihilatingSigns_proof k J ε ep em h2 hε hJ2 hp hm he U hσ hU
  obtain ⟨d1, d2⟩ := detectionFields_proof k J ep em h2 hp hm he V T loc U cp cm hloc hcp hcm
    hUp hUm hFp hFm hD
  exact ⟨ep, em, _, _, hp, hm, he, hAp, hAm, d1, d2, hsum⟩

end Local

/-- **Non-vacuity** over `ℚ`: `J = diag(1, −1)` satisfies the hypotheses `J² = 1`, `det J = −1` of
`LocalSignPlanes` and `QuadSignFields`. PROVED. -/
theorem localInv_example :
    let J : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 0; 0, -1]
    J ∘ₗ J = LinearMap.id ∧ LinearMap.det J = -1 := by
  intro J
  refine ⟨?_, ?_⟩
  · rw [← Matrix.toLin'_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [LinearMap.det_toLin', Matrix.det_fin_two_of]; norm_num

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

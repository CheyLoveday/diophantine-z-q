import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.Plug
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois

/-!
# RC53 SwitchInputs: the Galois cocycle involution on the genuine Selmer complexes

Proposition `ex:limits-uniform-lower-bound`, proof, tex L5009–5037:

> The action `c^τ(g) = J c(τ⁻¹ g τ)`, `J = ρ_T(τ)`, on cocycles gives a `k`-linear involution on
> cohomology. [...] All old conditions are stable under this involution. Conjugate old Kummer
> conditions are transported into each other; [...] both `F` and `S` at a previous derivative prime
> are stable under the actions just computed.

Part A (generic). A *Selmer involution* of Selmer data `G --res--> L <--ι-- U` is a triple of chain
maps `g, λ, μ` on `G, L, U` with `res ∘ g = λ ∘ res` and `ι ∘ μ = λ ∘ ι`; it induces a chain map
`σ = (g, μ, λ)` of the Selmer complex (SelmerDuality's `supportMap` with `r = 0`), hence a map `H¹(σ)`
on `H¹`. If `g, λ, μ` are involutions, so is `σ` (and `H¹(σ)`). Selmer involutions restrict along a
change of local conditions `f : U' → U` commuting with the `μ`'s, and `H¹(σ)` then commutes with
`H¹` of the comparison `C(U') → C(U)`: this is how one involution of the global and local cochains
gives the compatible involutions of the whole change-of-condition diagram.

Part B (genuine). On the genuine continuous cochains (`RC/SelmerComplex/`), a compatible pair
`(α, T)` — a continuous endomorphism `α` of `G_S` (conjugation `g ↦ τ⁻¹ g τ`) and a continuous
`k`-linear `T` on `M` (the action of `τ`) with `T (α g • m) = g • T m` — gives the cochain map
`c ↦ T ∘ c ∘ αⁿ` (`contCochainsMap α T`), i.e. `c(g₁,…,gₙ) ↦ ρ(τ)(c(τ⁻¹g₁τ, …, τ⁻¹gₙτ))`. With a
permutation `π` of the places (`v ↦ τv`) and continuous maps `β_v : G_v → G_{π v}` of the local
groups with `α ∘ loc_v = loc_{π v} ∘ β_v` (conjugation maps decomposition groups to each other), the
local maps `c ↦ T ∘ c ∘ β_vⁿ` commute with the restrictions. Together with maps of the local
conditions commuting with the `i_v` (the stability of the local conditions, tex L5065–5069), this is
a Selmer involution of the genuine Selmer data `selData Δ` (`galoisSelData`).

Part C. The degree-one component, read on functions, is SignAxes' `cocycleAct`; so the genuine
involution discharges the GLUE input `GaloisCocycleInvolution` for the genuine complex, up to its
local clause (`J` on `F`, `−J` on `S` at the derivative prime, tex L5027–5037), which stays a
stated hypothesis.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.Uniform

/-! ### Part A: Selmer involutions -/

section PartA

variable {S : Type} [CommRing S]

/-- Extensionality of relation-indexed chain maps over a commutative ring. -/
theorem ghom_ext' {A B : GCx S} {f g : GHom A B} (h : ∀ n x, f.f n n rfl x = g.f n n rfl x) :
    f = g := by
  cases f with
  | mk f fc =>
    cases g with
    | mk g gc =>
      have : f = g := by
        funext i j hij
        subst hij
        exact LinearMap.ext (h i)
      subst this
      rfl

/-- **A Selmer involution datum** (tex L5009–5013, L5065–5069): chain maps `g, λ, μ` of the global
complex, the local complexes and the local conditions, compatible with `res` and `ι`. -/
structure SelEndo (D : SelData S) where
  g : GHom D.G D.G
  lam : GHom D.L D.L
  mu : GHom D.U D.U
  hres : ∀ i (a : D.G.X i), D.res.f i i rfl (g.f i i rfl a) = lam.f i i rfl (D.res.f i i rfl a)
  hι : ∀ i (u : D.U.X i), D.ι.f i i rfl (mu.f i i rfl u) = lam.f i i rfl (D.ι.f i i rfl u)

/-- The support-change data of a Selmer endomorphism (`D = D⁺`, `r = 0`). -/
def SelEndo.toSupport {D : SelData S} (X : SelEndo D) : SupportChangeData S where
  D := D
  Dp := D
  g := X.g
  lam := X.lam
  mu := X.mu
  r := zeroGHom D.G D.U
  hres i j h a := by
    subst h
    rw [X.hres]
    change _ = _ + D.ι.f i i rfl 0
    rw [map_zero, add_zero]
  hι i j h u := by
    subst h
    exact X.hι i u

/-- **The induced chain map** `σ = (g, μ, λ)` of the Selmer complex. -/
def SelEndo.sigma {D : SelData S} (X : SelEndo D) : GHom (selCx D) (selCx D) :=
  supportMap X.toSupport

theorem SelEndo.sigma_apply {D : SelData S} (X : SelEndo D) (i : ℤ) (a : D.G.X i) (u : D.U.X i)
    (x : D.L.X (i - 1)) :
    X.sigma.f i i rfl (a, u, x) = (X.g.f i i rfl a, X.mu.f i i rfl u, X.lam.f (i - 1) (i - 1) rfl x) := by
  change (X.g.f i i rfl a, X.mu.f i i rfl u + (0 : D.U.X i), X.lam.f (i - 1) (i - 1) rfl x) = _
  rw [add_zero]

/-- The composite of two Selmer endomorphisms. -/
def SelEndo.comp {D : SelData S} (X Y : SelEndo D) : SelEndo D where
  g := ghomComp X.g Y.g
  lam := ghomComp X.lam Y.lam
  mu := ghomComp X.mu Y.mu
  hres i a := by
    change D.res.f i i rfl (Y.g.f i i rfl (X.g.f i i rfl a)) =
      Y.lam.f i i rfl (X.lam.f i i rfl (D.res.f i i rfl a))
    rw [Y.hres, X.hres]
  hι i u := by
    change D.ι.f i i rfl (Y.mu.f i i rfl (X.mu.f i i rfl u)) =
      Y.lam.f i i rfl (X.lam.f i i rfl (D.ι.f i i rfl u))
    rw [Y.hι, X.hι]

/-- `σ` of a composite is the composite of the `σ`'s. -/
theorem SelEndo.sigma_comp {D : SelData S} (X Y : SelEndo D) :
    ghomComp X.sigma Y.sigma = (X.comp Y).sigma := by
  apply ghom_ext'
  intro n c
  obtain ⟨a, u, x⟩ := c
  change Y.sigma.f n n rfl (X.sigma.f n n rfl (a, u, x)) = (X.comp Y).sigma.f n n rfl (a, u, x)
  rw [X.sigma_apply, Y.sigma_apply, (X.comp Y).sigma_apply]
  rfl

/-- A Selmer endomorphism is an involution when its three components are. -/
def SelEndo.IsInvolution {D : SelData S} (X : SelEndo D) : Prop :=
  (∀ i (a : D.G.X i), X.g.f i i rfl (X.g.f i i rfl a) = a) ∧
  (∀ i (x : D.L.X i), X.lam.f i i rfl (X.lam.f i i rfl x) = x) ∧
  (∀ i (u : D.U.X i), X.mu.f i i rfl (X.mu.f i i rfl u) = u)

/-- **`σ` is an involution of the Selmer complex** when `g, λ, μ` are (tex L5009–5013). PROVED. -/
theorem SelEndo.sigma_sigma {D : SelData S} (X : SelEndo D) (hX : X.IsInvolution) (n : ℤ)
    (c : (selCx D).X n) : X.sigma.f n n rfl (X.sigma.f n n rfl c) = c := by
  obtain ⟨a, u, x⟩ := c
  rw [X.sigma_apply, X.sigma_apply, hX.1, hX.2.1, hX.2.2]

/-- The identity of a relation-indexed complex induces the identity on `H¹`. -/
theorem H1_idGHom {k : Type} [Field k] (A : GCx k) : H1 (idGHom A) = LinearMap.id := by
  have h : GHom.toCC (idGHom A) = 𝟙 A.toCC := by
    ext i x
    rfl
  simp only [H1, h, HomologicalComplex.homologyMap_id]
  rfl

theorem H1_ghomComp {k : Type} [Field k] {A B C : GCx k} (f : GHom A B) (g : GHom B C) :
    H1 (ghomComp f g) = H1 g ∘ₗ H1 f := by
  simp only [H1, ← GHom.toCC_comp, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]

/-- **`H¹(σ)` is an involution** when the Selmer endomorphism is (tex L5009–5013: "gives a
`k`-linear involution on cohomology"). PROVED. -/
theorem SelEndo.H1_sigma_sigma {k : Type} [Field k] {D : SelData k} (X : SelEndo D)
    (hX : X.IsInvolution) : H1 X.sigma ∘ₗ H1 X.sigma = LinearMap.id := by
  rw [← H1_ghomComp]
  have : ghomComp X.sigma X.sigma = idGHom (selCx D) := by
    apply ghom_ext
    intro n c
    exact X.sigma_sigma hX n c
  rw [this, H1_idGHom]

/-- **Restriction of a Selmer endomorphism along a change of local conditions** `f : U' → U`, with
an endomorphism `μ'` of `U'` commuting with `f` (the old condition inside the new one is stable,
tex L5065–5069). -/
def SelEndo.restrict {D : SelData S} {U' : GCx S} (X : SelEndo D) (f : GHom U' D.U)
    (mu' : GHom U' U') (hf : ∀ i (u : U'.X i), f.f i i rfl (mu'.f i i rfl u) = X.mu.f i i rfl (f.f i i rfl u)) :
    SelEndo (restrictData D f) where
  g := X.g
  lam := X.lam
  mu := mu'
  hres := X.hres
  hι i u := by
    have e := hf i u
    have e2 := X.hι i (f.f i i rfl u)
    change D.ι.f i i rfl (f.f i i rfl (mu'.f i i rfl u)) = X.lam.f i i rfl (D.ι.f i i rfl (f.f i i rfl u))
    rw [e, e2]

/-- **The involutions commute with the comparison** `C(U') → C(U)` (tex L5065–5086: the change-of-
condition diagram is equivariant). PROVED. -/
theorem SelEndo.changeMap_sigma {D : SelData S} {U' : GCx S} (X : SelEndo D) (f : GHom U' D.U)
    (mu' : GHom U' U') (hf : ∀ i (u : U'.X i), f.f i i rfl (mu'.f i i rfl u) = X.mu.f i i rfl (f.f i i rfl u)) :
    ghomComp (changeMap D f) X.sigma = ghomComp (X.restrict f mu' hf).sigma (changeMap D f) := by
  apply ghom_ext'
  intro n c
  obtain ⟨a, u, x⟩ := c
  have e1 := X.sigma_apply n (show D.G.X n from a) (f.f n n rfl u) (show D.L.X (n - 1) from x)
  have e3 := (X.restrict f mu' hf).sigma_apply n a u x
  change X.sigma.f n n rfl (show (selCx D).X n from (a, f.f n n rfl u, x)) =
    (changeMap D f).f n n rfl ((X.restrict f mu' hf).sigma.f n n rfl (a, u, x))
  rw [e3, e1]
  exact Prod.ext rfl (Prod.ext (hf n u).symm rfl)

theorem SelEndo.H1_changeMap_sigma {k : Type} [Field k] {D : SelData k} {U' : GCx k}
    (X : SelEndo D) (f : GHom U' D.U) (mu' : GHom U' U')
    (hf : ∀ i (u : U'.X i), f.f i i rfl (mu'.f i i rfl u) = X.mu.f i i rfl (f.f i i rfl u)) :
    H1 X.sigma ∘ₗ H1 (changeMap D f) = H1 (changeMap D f) ∘ₗ H1 (X.restrict f mu' hf).sigma := by
  rw [← H1_ghomComp, ← H1_ghomComp, X.changeMap_sigma f mu' hf]

theorem SelEndo.restrict_isInvolution {D : SelData S} {U' : GCx S} (X : SelEndo D)
    (f : GHom U' D.U) (mu' : GHom U' U')
    (hf : ∀ i (u : U'.X i), f.f i i rfl (mu'.f i i rfl u) = X.mu.f i i rfl (f.f i i rfl u))
    (hX : X.IsInvolution) (hmu' : ∀ i (u : U'.X i), mu'.f i i rfl (mu'.f i i rfl u) = u) :
    (X.restrict f mu' hf).IsInvolution :=
  ⟨hX.1, hX.2.1, hmu'⟩

end PartA

/-! ### Part A′: the involutions of the change-of-condition diagram -/

section Diagram

variable {k : Type} [Field k]

/-- **One involution for the whole change-of-condition diagram** (tex L5065–5086): a Selmer
involution `X` of the relaxed data `C(U_rel)`, with involutions `μ_F, μ_S` of the side conditions and
`μ_{F,str}, μ_{S,str}` of the strict conditions, commuting with the inclusions
`U_str ⊂ U_F, U_S ⊂ U_rel`. -/
structure DiagramInvolution (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) where
  X : SelEndo R.D
  hX : X.IsInvolution
  μF : GHom SF.U₁ SF.U₁
  hμF : ∀ i (u : SF.U₁.X i), SF.f₁.f i i rfl (μF.f i i rfl u) = X.mu.f i i rfl (SF.f₁.f i i rfl u)
  hμF2 : ∀ i (u : SF.U₁.X i), μF.f i i rfl (μF.f i i rfl u) = u
  μFs : GHom SF.Ustr SF.Ustr
  hμFs : ∀ i (u : SF.Ustr.X i), SF.fs.f i i rfl (μFs.f i i rfl u) = μF.f i i rfl (SF.fs.f i i rfl u)
  hμFs2 : ∀ i (u : SF.Ustr.X i), μFs.f i i rfl (μFs.f i i rfl u) = u
  μS : GHom SS.U₁ SS.U₁
  hμS : ∀ i (u : SS.U₁.X i), SS.f₁.f i i rfl (μS.f i i rfl u) = X.mu.f i i rfl (SS.f₁.f i i rfl u)
  hμS2 : ∀ i (u : SS.U₁.X i), μS.f i i rfl (μS.f i i rfl u) = u

namespace DiagramInvolution

variable {R : RelaxedLocalization k} {SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))}
  {SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))} (Y : DiagramInvolution R SF SS)

/-- The induced Selmer involution of the finite side `C(U_F)`. -/
def XF : SelEndo SF.Dside := Y.X.restrict SF.f₁ Y.μF Y.hμF

/-- The induced Selmer involution of the singular side `C(U_S)`. -/
def XS : SelEndo SS.Dside := Y.X.restrict SS.f₁ Y.μS Y.hμS

/-- The induced Selmer involution of the strict data `C(U_str)` (finite side). -/
def XK : SelEndo SF.Dstr := Y.XF.restrict SF.fs Y.μFs Y.hμFs

/-- `σ_r = H¹(σ)` on `H¹(C(U_rel))`. -/
def σr : (selCx R.D).toCC.homology 1 →ₗ[k] (selCx R.D).toCC.homology 1 := H1 Y.X.sigma
/-- `σ_V` on `V = H¹(C(U_F))`. -/
def σV : (selCx SF.Dside).toCC.homology 1 →ₗ[k] (selCx SF.Dside).toCC.homology 1 := H1 Y.XF.sigma
/-- `σ_{V′}` on `V′ = H¹(C(U_S))`. -/
def σV' : (selCx SS.Dside).toCC.homology 1 →ₗ[k] (selCx SS.Dside).toCC.homology 1 := H1 Y.XS.sigma
/-- `σ_K` on `K₀ = H¹(C(U_str))`. -/
def σK : (selCx SF.Dstr).toCC.homology 1 →ₗ[k] (selCx SF.Dstr).toCC.homology 1 := H1 Y.XK.sigma

/-- **The four involutions and the three diagram compatibilities** `hr, hV, hV', hK, hα', hγ', hγ''`
of `SelmerQuadSwitch`, from one diagram involution (tex L5065–5086). PROVED. -/
theorem fields :
    Y.σr ∘ₗ Y.σr = LinearMap.id ∧ Y.σV ∘ₗ Y.σV = LinearMap.id ∧ Y.σV' ∘ₗ Y.σV' = LinearMap.id ∧
    Y.σK ∘ₗ Y.σK = LinearMap.id ∧
    H1 (changeMap SF.Dside SF.fs) ∘ₗ Y.σK = Y.σV ∘ₗ H1 (changeMap SF.Dside SF.fs) ∧
    H1 (changeMap R.D SF.f₁) ∘ₗ Y.σV = Y.σr ∘ₗ H1 (changeMap R.D SF.f₁) ∧
    H1 (changeMap R.D SS.f₁) ∘ₗ Y.σV' = Y.σr ∘ₗ H1 (changeMap R.D SS.f₁) := by
  have hF := Y.X.restrict_isInvolution SF.f₁ Y.μF Y.hμF Y.hX Y.hμF2
  have hS := Y.X.restrict_isInvolution SS.f₁ Y.μS Y.hμS Y.hX Y.hμS2
  have hK := Y.XF.restrict_isInvolution SF.fs Y.μFs Y.hμFs hF Y.hμFs2
  refine ⟨Y.X.H1_sigma_sigma Y.hX, Y.XF.H1_sigma_sigma hF, Y.XS.H1_sigma_sigma hS,
    Y.XK.H1_sigma_sigma hK, ?_, ?_, ?_⟩
  · exact (Y.XF.H1_changeMap_sigma SF.fs Y.μFs Y.hμFs).symm
  · exact (Y.X.H1_changeMap_sigma SF.f₁ Y.μF Y.hμF).symm
  · exact (Y.X.H1_changeMap_sigma SS.f₁ Y.μS Y.hμS).symm

/-- **`SelmerQuadSwitch` from one diagram involution** (tex L5009–5086): the involutions `σK, σV,
σV′, σr` and the fields `hK, hV, hV′, hr, hα′, hγ′, hγ″` come from `Y`; in the type remain the
strict identification `eK` with its compatibility `hα″`, the finite-dimensionality, and the local
clauses `hβ′, hβ″, hl` (`J` on `F`, `−J` on `S` at the derivative prime, tex L5027–5037). -/
def toSelmerQuadSwitch (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (fG : FiniteDimensional k (R.D.G.X 1))
    (fL : FiniteDimensional k (R.D.L.X 0)) (fF : FiniteDimensional k (SF.U₁.X 1))
    (fS : FiniteDimensional k (SS.U₁.X 1))
    (eK : (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1)
    (hα'' : (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) ∘ₗ Y.σK =
      Y.σV' ∘ₗ (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap))
    (hβ' : SF.βF ∘ₗ Y.σV = J ∘ₗ SF.βF) (hβ'' : SS.βS ∘ₗ Y.σV' = (-J) ∘ₗ SS.βS)
    (hl : R.lam ∘ₗ Y.σr = localInv J ∘ₗ R.lam) : SelmerQuadSwitch k J :=
  have h := Y.fields
  { R := R, SF := SF, SS := SS, fG := fG, fL := fL, fF := fF, fS := fS, eK := eK,
    σK := Y.σK, σV := Y.σV, σV' := Y.σV', σr := Y.σr,
    hK := h.2.2.2.1, hV := h.2.1, hV' := h.2.2.1, hr := h.1,
    hα' := h.2.2.2.2.1, hβ' := hβ', hγ' := h.2.2.2.2.2.1, hα'' := hα'', hβ'' := hβ'',
    hγ'' := h.2.2.2.2.2.2, hl := hl }

end DiagramInvolution

end Diagram

/-! ### Part B: the genuine involution on continuous cochains -/

section PartB

open ZInQ.Manuscript.RC.SelmerComplex

variable (k : Type) [CommRing k] {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- **Conjugation data** (tex L5009–5013, L5026–5037): a continuous endomorphism `α` of `G_S`
(conjugation `g ↦ τ⁻¹ g τ`), a continuous `k`-linear `T` on `M` (the action `ρ(τ)`) forming a
compatible pair (`T (α g • m) = g • T m`), a map `π` of the places (`v ↦ τv`) and continuous maps
`β_v : G_v → G_{π v}` of the local groups with `α ∘ loc_v = loc_{π v} ∘ β_v` (conjugation carries
the decomposition group at `v` to that at `τv`). -/
structure ConjData where
  α : GS →ₜ* GS
  T : M →ₗ[k] M
  hTc : Continuous T
  hT : ∀ (g : GS) (m : M), T (α g • m) = g • T m
  π : ι → ι
  β : ∀ v, Gv v →ₜ* Gv (π v)
  hβ : ∀ v (h : Gv v), α (loc v h) = loc (π v) (β v h)

variable {k M}

/-- **The global involution** `c ↦ T ∘ c ∘ αⁿ` on `C^•_cont(G_S, M)` (tex L5009–5011:
`c^τ(g) = J c(τ⁻¹ g τ)`), a cochain map (`contCochainsMap`). -/
def ConjData.globalMap (C : ConjData k M (loc := loc)) : contCochains k GS M ⟶ contCochains k GS M :=
  contCochainsMap C.α C.T C.hTc C.hT

/-- `T`, read between the restricted modules at `π v` and at `v`. -/
def ConjData.tRes (C : ConjData k M (loc := loc)) (v : ι) :
    ResMod (loc (C.π v)) M →ₗ[k] ResMod (loc v) M := C.T

theorem ConjData.tRes_compat (C : ConjData k M (loc := loc)) (v : ι) (h : Gv v)
    (m : ResMod (loc (C.π v)) M) : C.tRes v (C.β v h • m) = h • C.tRes v m := by
  change C.T (loc (C.π v) (C.β v h) • (show M from m)) = loc v h • C.T (show M from m)
  rw [← C.hβ, C.hT]

/-- **The local map** `C^•_cont(G_{π v}, M) → C^•_cont(G_v, M)`, `c ↦ T ∘ c ∘ β_vⁿ`, a cochain map. -/
def ConjData.localMap (C : ConjData k M (loc := loc)) (v : ι) :
    contCochains k (Gv (C.π v)) (ResMod (loc (C.π v)) M) ⟶ contCochains k (Gv v) (ResMod (loc v) M) :=
  contCochainsMap (C.β v) (C.tRes v) C.hTc (C.tRes_compat v)

/-- Equal compatible pairs give equal cochain maps. -/
theorem contCochainsMap_congr {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {M N : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
    [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
    [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N]
    {φ φ' : H →ₜ* G} {f f' : M →ₗ[k] N} (hφ : φ = φ') (hf : f = f') (hfc : Continuous f)
    (hfc' : Continuous f') (h : ∀ (x : H) (m : M), f (φ x • m) = x • f m)
    (h' : ∀ (x : H) (m : M), f' (φ' x • m) = x • f' m) :
    contCochainsMap φ f hfc h = contCochainsMap φ' f' hfc' h' := by
  subst hφ hf
  rfl

/-- **Restriction commutes with the involutions** (tex L5065–5069): `res_v ∘ c^τ = (local map) ∘
res_{π v}`, both equal to the cochain map of the pair `(α ∘ loc_v, T) = (loc_{π v} ∘ β_v, T)`.
PROVED. -/
theorem ConjData.res_comm (C : ConjData k M (loc := loc)) (v : ι) :
    C.globalMap ≫ resCochains (k := k) (M := M) (loc v) =
      resCochains (k := k) (M := M) (loc (C.π v)) ≫ C.localMap v := by
  unfold ConjData.globalMap ConjData.localMap resCochains
  refine (contCochainsMap_comp _ _ _ _ _ _ _ _).symm.trans
    ((contCochainsMap_congr ?_ ?_ _ _ _ _).trans (contCochainsMap_comp _ _ _ _ _ _ _ _))
  · ext h
    exact C.hβ v h
  · rfl

variable (k GS Gv loc M) in
/-- The global complex as a relation-indexed complex (re-export). -/
abbrev gCx := globalCx k GS M

/-- **The global involution as a relation-indexed chain map.** -/
def ConjData.gHom (C : ConjData k M (loc := loc)) : GHom (globalCx k GS M) (globalCx k GS M) :=
  natHom C.globalMap

/-- **The involution of `⊕_v C^•_cont(G_v, M)`**: `(x_v)_v ↦ (localMap_v (x_{π v}))_v`. -/
def ConjData.lamHom (C : ConjData k M (loc := loc)) :
    GHom (localSumCx k GS Gv loc M) (localSumCx k GS Gv loc M) where
  f i j h := LinearMap.pi fun v => ((natHom (C.localMap v)).f i j h).comp (LinearMap.proj (C.π v))
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    funext v
    exact (natHom (C.localMap v)).comm i i₁ j j₁ hij h₁ h₂ hj (x (C.π v))

/-- **Compatibility with the restriction** `res_S` (tex L5065–5069). PROVED. -/
theorem ConjData.hres (C : ConjData k M (loc := loc)) (i : ℤ) (a : (globalCx k GS M).X i) :
    (resS k GS Gv loc M).f i i rfl (C.gHom.f i i rfl a) =
      C.lamHom.f i i rfl ((resS k GS Gv loc M).f i i rfl a) := by
  funext v
  change (natHom (resCochains (k := k) (M := M) (loc v))).f i i rfl ((natHom C.globalMap).f i i rfl a) =
    (natHom (C.localMap v)).f i i rfl
      ((natHom (resCochains (k := k) (M := M) (loc (C.π v)))).f i i rfl a)
  have e1 := natHom_comp_apply C.globalMap (resCochains (k := k) (M := M) (loc v)) i a
  have e2 := natHom_comp_apply (resCochains (k := k) (M := M) (loc (C.π v))) (C.localMap v) i a
  rw [C.res_comm v] at e1
  exact e1.symm.trans e2

/-- **Stability of the local conditions** (tex L5065–5069: "All old conditions are stable under
this involution"): maps `μ_v : U_{π v} → U_v` with `i_v ∘ μ_v = (local map) ∘ i_{π v}`. -/
structure CondConj (C : ConjData k M (loc := loc)) (Δ : LocalConditions k GS Gv loc M) where
  μ : ∀ v, GHom (Δ.U (C.π v)) (Δ.U v)
  hμ : ∀ v (i : ℤ) (u : (Δ.U (C.π v)).X i),
    (Δ.i v).f i i rfl ((μ v).f i i rfl u) = (natHom (C.localMap v)).f i i rfl ((Δ.i (C.π v)).f i i rfl u)

/-- The involution of `⊕_v U_v`. -/
def CondConj.muHom {C : ConjData k M (loc := loc)} {Δ : LocalConditions k GS Gv loc M}
    (Q : CondConj C Δ) : GHom (piCx Δ.U) (piCx Δ.U) where
  f i j h := LinearMap.pi fun v => ((Q.μ v).f i j h).comp (LinearMap.proj (C.π v))
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    funext v
    exact (Q.μ v).comm i i₁ j j₁ hij h₁ h₂ hj (x (C.π v))

/-- **The genuine Selmer involution** of `selData Δ` (Nekovář's `C^•_f(G_{K,S}, M; Δ)`, (4.3)):
`(c^τ, μ, local maps)`. PROVED (a Selmer endomorphism). -/
def CondConj.selEndo {C : ConjData k M (loc := loc)} {Δ : LocalConditions k GS Gv loc M}
    (Q : CondConj C Δ) : SelEndo (selData k GS Gv loc M Δ) where
  g := C.gHom
  lam := C.lamHom
  mu := Q.muHom
  hres := C.hres
  hι i u := by
    funext v
    exact Q.hμ v i (u (C.π v))

/-- **The global involution is an involution** when `α² = 1` and `T² = 1` (`τ² = 1`: the actual
complex conjugation, tex L5013–5015). PROVED. -/
theorem ConjData.gHom_gHom (C : ConjData k M (loc := loc)) (hα : ∀ g, C.α (C.α g) = g)
    (hT : ∀ m, C.T (C.T m) = m) (i : ℤ) (a : (globalCx k GS M).X i) :
    C.gHom.f i i rfl (C.gHom.f i i rfl a) = a := by
  have h : C.globalMap ≫ C.globalMap = 𝟙 _ := by
    unfold ConjData.globalMap
    refine (contCochainsMap_comp _ _ _ _ _ _ _ _).symm.trans
      ((contCochainsMap_congr ?_ ?_ _ _ _ _).trans (contCochainsMap_id k GS M))
    · ext g; exact hα g
    · ext m; exact hT m
  have e := natHom_comp_apply C.globalMap C.globalMap i a
  rw [h] at e
  change (natHom C.globalMap).f i i rfl ((natHom C.globalMap).f i i rfl a) = a
  rw [← e]
  match i with
  | Int.ofNat n => rfl
  | Int.negSucc _ => rfl

/-- **The genuine Selmer involution is an involution** (tex L5009–5013), given that the global part
is (`α² = 1`, `T² = 1`) and that the local parts are (`hlam`, `hmu`; for places fixed by `τ`, e.g.
the derivative primes, these follow from `β_v² = 1`, `ConjData.ofFixed`). PROVED. -/
theorem CondConj.selEndo_isInvolution {C : ConjData k M (loc := loc)}
    {Δ : LocalConditions k GS Gv loc M} (Q : CondConj C Δ) (hα : ∀ g, C.α (C.α g) = g)
    (hT : ∀ m, C.T (C.T m) = m)
    (hlam : ∀ i (x : (localSumCx k GS Gv loc M).X i), C.lamHom.f i i rfl (C.lamHom.f i i rfl x) = x)
    (hmu : ∀ i (u : (piCx Δ.U).X i), Q.muHom.f i i rfl (Q.muHom.f i i rfl u) = u) :
    Q.selEndo.IsInvolution :=
  ⟨C.gHom_gHom hα hT, hlam, hmu⟩

/-- Conjugation data in which every place is fixed (`π = id`; e.g. the derivative primes, where
`τ` lies in the decomposition group, tex L5027–5029). -/
def ConjData.ofFixed (α : GS →ₜ* GS) (T : M →ₗ[k] M) (hTc : Continuous T)
    (hT : ∀ (g : GS) (m : M), T (α g • m) = g • T m) (β : ∀ v, Gv v →ₜ* Gv v)
    (hβ : ∀ v (h : Gv v), α (loc v h) = loc v (β v h)) : ConjData k M (loc := loc) :=
  ⟨α, T, hTc, hT, fun v => v, β, hβ⟩

/-- **At fixed places the local involution is an involution** when `β_v² = 1` and `T² = 1`. PROVED. -/
theorem ConjData.lamHom_lamHom_ofFixed (α : GS →ₜ* GS) (T : M →ₗ[k] M) (hTc : Continuous T)
    (hT : ∀ (g : GS) (m : M), T (α g • m) = g • T m) (β : ∀ v, Gv v →ₜ* Gv v)
    (hβ : ∀ v (h : Gv v), α (loc v h) = loc v (β v h)) (hβ2 : ∀ v h, β v (β v h) = h)
    (hT2 : ∀ m, T (T m) = m) (i : ℤ) (x : (localSumCx k GS Gv loc M).X i) :
    (ConjData.ofFixed α T hTc hT β hβ).lamHom.f i i rfl
      ((ConjData.ofFixed α T hTc hT β hβ).lamHom.f i i rfl x) = x := by
  set C := ConjData.ofFixed α T hTc hT β hβ
  funext v
  have h : C.localMap v ≫ C.localMap v = 𝟙 _ := by
    unfold ConjData.localMap
    refine (contCochainsMap_comp _ _ _ _ _ _ _ _).symm.trans
      ((contCochainsMap_congr ?_ ?_ _ _ _ _).trans (contCochainsMap_id k (Gv v) (ResMod (loc v) M)))
    · ext g; exact hβ2 v g
    · ext m; exact hT2 m
  have e := natHom_comp_apply (C.localMap v) (C.localMap v) i (x v)
  rw [h] at e
  refine e.symm.trans ?_
  match i with
  | Int.ofNat n => rfl
  | Int.negSucc _ => rfl

end PartB

/-! ### Part C: the GLUE input `GaloisCocycleInvolution` for the genuine complex -/

section PartC

open ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k] {Γ : Type} [Group Γ] {T : Type} [AddCommGroup T] [Module k T]
  {Δ : Subgroup Γ} [TopologicalSpace Δ] [IsTopologicalGroup Δ] [DistribMulAction Δ T]
  [SMulCommClass Δ k T] [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T]
  [ContinuousSMul Δ T]
  {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* Δ}

variable (k Δ T) in
/-- **Evaluation of degree-one continuous cochains** `c ↦ (g ↦ c(g))`, the model `ev : K¹ → (Δ → T)`
of `GaloisCocycleInvolution` on the global component. -/
def evG : (contCochains k Δ T).X 1 →ₗ[k] (Δ → T) where
  toFun a g := asFun k Δ T (((contSubCx k Δ T).el a : contCochain k Δ T 1) :
    (groupCohomology.inhomogeneousCochains (rep k Δ T)).X 1) (fun _ => g)
  map_add' a b := rfl
  map_smul' c a := rfl

/-- The model `ev` on the genuine Selmer complex: evaluation of the global component. -/
def evSel (LC : LocalConditions k Δ Gv loc T) :
    (selCx (selData k Δ Gv loc T LC)).toCC.X 1 →ₗ[k] (Δ → T) where
  toFun c := evG k T Δ (show (contCochains k Δ T).X 1 from
    (show selT (selData k Δ Gv loc T LC) 1 from c).1)
  map_add' c d := map_add (evG k T Δ) _ _
  map_smul' r c := map_smul (evG k T Δ) r _

/-- **The degree-one component of the genuine involution is the cocycle action** (tex
L5009–5011): on the global component, `ev (σ¹ c) = J c(τ⁻¹ g τ)` when `α` is conjugation by `τ`
and `T = ρ(τ)`. PROVED. -/
theorem evSel_sigma {C : ConjData k T (loc := loc)} {LC : LocalConditions k Δ Gv loc T}
    (Q : CondConj C LC) (hidx : Δ.index = 2) (τ : Γ) (ρ : Γ →* (T →ₗ[k] T))
    (hCα : ∀ g, C.α g = conjSub Δ hidx τ g) (hCT : ∀ m, C.T m = ρ τ m)
    (c : (selCx (selData k Δ Gv loc T LC)).toCC.X 1) :
    evSel LC ((GHom.toCC Q.selEndo.sigma).f 1 |>.hom c) = cocycleAct Δ hidx τ ρ (evSel LC c) := by
  obtain ⟨a, u, x⟩ := c
  funext g
  change evG k T Δ (Q.selEndo.sigma.f 1 1 rfl (a, u, x)).1 g = ρ τ (evG k T Δ a (conjSub Δ hidx τ g))
  rw [SelEndo.sigma_apply]
  change C.T (asFun k Δ T (((contSubCx k Δ T).el a : contCochain k Δ T 1) :
    (groupCohomology.inhomogeneousCochains (rep k Δ T)).X 1) (C.α ∘ fun _ => g)) = _
  rw [hCT]
  congr 2
  funext i
  exact hCα g

/-- `σ ≫ σ = 𝟙` for an involutive Selmer endomorphism. -/
theorem SelEndo.toCC_sigma_sigma {D : SelData k} (X : SelEndo D) (hX : X.IsInvolution) :
    GHom.toCC X.sigma ≫ GHom.toCC X.sigma = 𝟙 _ := by
  rw [GHom.toCC_comp]
  have : ghomComp X.sigma X.sigma = idGHom (selCx D) := by
    apply ghom_ext'
    intro n c
    exact X.sigma_sigma hX n c
  rw [this]
  ext i x
  rfl

/-- **`GaloisCocycleInvolution` holds for the genuine Selmer complex** (tex L5009–5037), with
`σ` the genuine involution: `σ² = 1` and `ev ∘ σ¹ = cocycleAct ∘ ev` are PROVED; in the type remain
the identification of `α, T` with conjugation by `τ` and `ρ(τ)`, the involutivity of the local parts
(automatic at fixed places, `ConjData.lamHom_lamHom_ofFixed`), and the local clause `hloc`
(`J` on `F`, `−J` on `S` at the derivative prime, tex L5027–5037; GLUE, the local computation). -/
theorem galoisCocycleInvolution_genuine {C : ConjData k T (loc := loc)}
    {LC : LocalConditions k Δ Gv loc T} (Q : CondConj C LC) (hidx : Δ.index = 2) (τ : Γ)
    (hτ : τ ∉ Δ) (hττ : τ * τ = 1) (ρ : Γ →* (T →ₗ[k] T))
    (hCα : ∀ g, C.α g = conjSub Δ hidx τ g) (hCT : ∀ m, C.T m = ρ τ m)
    (hlam : ∀ i (x : (localSumCx k Δ Gv loc T).X i), C.lamHom.f i i rfl (C.lamHom.f i i rfl x) = x)
    (hmu : ∀ i (u : (piCx LC.U).X i), Q.muHom.f i i rfl (Q.muHom.f i i rfl u) = u)
    (Jl : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJl2 : Jl ∘ₗ Jl = LinearMap.id)
    (hJldet : LinearMap.det Jl = -1)
    (locH : (selCx (selData k Δ Gv loc T LC)).toCC.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (hloc : ∀ v, locH (H1 Q.selEndo.sigma v) = localInv Jl (locH v)) :
    GaloisCocycleInvolution Δ hidx τ hτ hττ ρ (selCx (selData k Δ Gv loc T LC)).toCC (evSel LC) Jl
      hJl2 hJldet locH := by
  have hτ' : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hα : ∀ g, C.α (C.α g) = g := fun g => by
    rw [hCα, hCα]
    apply Subtype.ext
    simp only [conjSub, hτ']
    rw [← mul_assoc, ← mul_assoc, hττ, one_mul, mul_assoc, hττ, mul_one]
  have hT : ∀ m, C.T (C.T m) = m := fun m => by
    rw [hCT, hCT]
    change (ρ τ * ρ τ) m = m
    rw [← map_mul, hττ, map_one]
    rfl
  have hX := Q.selEndo_isInvolution hα hT hlam hmu
  exact ⟨GHom.toCC Q.selEndo.sigma, Q.selEndo.toCC_sigma_sigma hX,
    fun c => evSel_sigma Q hidx τ ρ hCα hCT c, hloc⟩

end PartC

/-! ### Part D: non-vacuity -/

section Example

open ZInQ.Manuscript.RC.SelmerComplex

/-- The group `ℤ/2` (written multiplicatively), with the discrete topology. -/
def ExΓ : Type := Multiplicative (ZMod 2)

instance : CommGroup ExΓ := inferInstanceAs (CommGroup (Multiplicative (ZMod 2)))
instance : Fintype ExΓ := inferInstanceAs (Fintype (Multiplicative (ZMod 2)))
instance : DecidableEq ExΓ := inferInstanceAs (DecidableEq (Multiplicative (ZMod 2)))
instance : TopologicalSpace ExΓ := ⊥
instance : DiscreteTopology ExΓ := ⟨rfl⟩

/-- The generator `τ` (an element of order two outside the trivial index-two subgroup). -/
def exτ : ExΓ := Multiplicative.ofAdd (1 : ZMod 2)

theorem exτ_sq : exτ * exτ = 1 := by decide

theorem exτ_ne_one : exτ ≠ 1 := by decide

theorem exΓ_cases (x : ExΓ) : x = 1 ∨ x = exτ := by
  revert x; decide

theorem exτ_ne : exτ ∉ (⊥ : Subgroup ExΓ) := by
  rw [Subgroup.mem_bot]; decide

theorem exIndex : (⊥ : Subgroup ExΓ).index = 2 := by
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card]; rfl

/-- The coefficient module `ℚ`, discrete, with the trivial action of the trivial group. -/
def ExT : Type := ℚ

instance : AddCommGroup ExT := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ ExT := inferInstanceAs (Module ℚ ℚ)
instance : TopologicalSpace ExT := ⊥
instance : DiscreteTopology ExT := ⟨rfl⟩
instance : DistribMulAction (⊥ : Subgroup ExΓ) ExT where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
instance : SMulCommClass (⊥ : Subgroup ExΓ) ℚ ExT := ⟨fun _ _ _ => rfl⟩
instance : ContinuousAdd ExT := ⟨continuous_of_discreteTopology⟩
instance : ContinuousConstSMul ℚ ExT := ⟨fun _ => continuous_of_discreteTopology⟩
instance : ContinuousSMul (⊥ : Subgroup ExΓ) ExT := ⟨continuous_of_discreteTopology⟩

/-- The sign character `ρ : ℤ/2 → End(ℚ)`, `ρ(τ) = −1` (so `J = ρ(τ)` is a genuine involution). -/
def exρ : ExΓ →* (ExT →ₗ[ℚ] ExT) where
  toFun x := if x = 1 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    rcases exΓ_cases x with rfl | rfl <;> rcases exΓ_cases y with rfl | rfl <;>
      simp [exτ_sq, exτ_ne_one]

/-- The conjugation data (no places): `α = id` (conjugation is trivial on the trivial group),
`T = ρ(τ) = −1`. -/
def exConj : ConjData ℚ ExT (GS := (⊥ : Subgroup ExΓ)) (Gv := fun _ : Empty => Unit)
    (loc := fun v => v.elim) :=
  ConjData.ofFixed (ContinuousMonoidHom.id _) (-LinearMap.id) continuous_of_discreteTopology
    (fun _ m => by change -m = -m; rfl) (fun v => v.elim) (fun v => v.elim)

/-- The strict local conditions (no places) are stable. -/
def exCond : CondConj exConj (strictConditions ℚ (⊥ : Subgroup ExΓ) (fun _ : Empty => Unit)
    (fun v => v.elim) ExT) where
  μ v := v.elim
  hμ v := v.elim

/-- `J = diag(1, −1)` on `ℚ²`. -/
def exJl : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 0; 0, -1]

theorem exJl2 : exJl ∘ₗ exJl = LinearMap.id := by
  rw [exJl, ← Matrix.toLin'_mul]
  convert Matrix.toLin'_one (R := ℚ) (n := Fin 2)
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exJldet : LinearMap.det exJl = -1 := by
  rw [exJl, LinearMap.det_toLin', Matrix.det_fin_two_of]; norm_num

/-- **Non-vacuity of `GaloisCocycleInvolution` on a genuine Selmer complex** (non-vacuity): for the
group `ℤ/2` with the trivial index-two subgroup, `τ` the generator, `ρ` the sign character, and the
genuine Selmer complex `selCx (selData …)` of continuous cochains (strict conditions, no places), the
GLUE input holds with the genuine involution (`σ² = 1`, `ev ∘ σ¹ = cocycleAct ∘ ev`), for the zero
localization. PROVED. -/
theorem exGaloisCocycleInvolution_genuine :
    GaloisCocycleInvolution (⊥ : Subgroup ExΓ) exIndex exτ exτ_ne exτ_sq exρ
      (selCx (selData ℚ (⊥ : Subgroup ExΓ) (fun _ : Empty => Unit) (fun v => v.elim) ExT
        (strictConditions ℚ _ _ _ ExT))).toCC (evSel _) exJl exJl2 exJldet 0 := by
  refine galoisCocycleInvolution_genuine exCond exIndex exτ exτ_ne exτ_sq exρ ?_ ?_ ?_ ?_ exJl exJl2
    exJldet 0 ?_
  · intro g
    apply Subtype.ext
    have hg : (g : ExΓ) = 1 := Subgroup.mem_bot.mp g.2
    change (g : ExΓ) = exτ⁻¹ * g * exτ⁻¹⁻¹
    rw [hg, mul_one, inv_inv, inv_mul_cancel]
  · intro m
    change -m = (if exτ = 1 then (1 : ExT →ₗ[ℚ] ExT) else -1) m
    rw [if_neg (by decide)]
    rfl
  · intro i x
    funext v
    exact v.elim
  · intro i u
    funext v
    exact v.elim
  · intro v
    simp only [LinearMap.zero_apply, map_zero]

end Example

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

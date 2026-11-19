import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois

/-!
# Selmer complexes along a ring isomorphism

Manuscript `diophantine_zq.tex`, tex 4385–4414: the residual cohomology of the genuine `C_∅` over
`StageRing s` against the standard-old stage family over `A_s = Acoef s`.

Lane E2's `genCxResidualIso_of_ringChange` (and the generic `residualFinrank_eq_of_ringEquiv`)
needs two Selmer complexes over isomorphic rings `e : k ≃+* k'` to be related by degreewise
additive isomorphisms. The isomorphisms must be semilinear along `e` and commute with the
differentials. This file builds them for the genuine Selmer data `selData` (Nekovář 6.1.2,
continuous cochains, (4.3)), from:
* a `G_S`-equivariant additive isomorphism `f : M ≃+ M'` of the coefficient modules, semilinear
  along `e` and a homeomorphism; and
* at every place, a degreewise semilinear isomorphism of the local-condition complexes commuting
  with the differentials and with the condition maps.

The carriers are functions `Gⁿ → M`, transported by `f ∘ −`. The differentials use the ring
scalars `(−1)^{j+1}`, and `f((−1)^{j+1} • m) = e((−1)^{j+1}) • f m = (−1)^{j+1} • f m`
(`cochainSEquiv_d`).

* `GCxSEquiv e C C'` (structure): degreewise additive isomorphisms, semilinear along `e`,
  commuting with `d`. Its fields are exactly the `fR`, `hfR`, `hdR` of
  `genCxResidualIso_of_ringChange`.
* `cochainSEquiv`: `C^n_cont(G, M) ≃ C^n_cont(G, M')`, `c ↦ f ∘ c`; `cochainSEquiv_d` (PROVED).
* `natSEquiv`, `piSEquiv`: extension by zero, and products.
* `selSEquiv` (PROVED fields): `selCx D ≃ selCx D'` from the three components and their
  compatibility with `res` and `ι`.
* **`selDataSEquiv`** (definition, PROVED fields): `selCx (selData k GS Gv loc M Δ) ≃
  selCx (selData k' GS Gv loc M' Δ')`. For the genuine Galois data, `galoisSelData` is the case
  `GS = G_{K,S}`, `Gv = G_{K_v}`, `loc = locMap`.
* **`galoisSel_ringChange`** (PROVED): the `fR`, `hfR`, `hdR` of `genCxResidualIso_of_ringChange`
  for `galoisSelData`. For the actual presentation (`M_i` over `StageRing s` through
  `stageEquiv s`) take `f = AddEquiv.refl _`; the place-by-place condition isomorphisms
  `EU`, `hι` are lane E2's pieces (1)–(2).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex

universe u

/-! ### Semilinear isomorphisms of complexes -/

section GCx

variable {k k' : Type u} [CommRing k] [CommRing k'] (e : k ≃+* k')

/-- **Degreewise additive isomorphisms of complexes, semilinear along `e` and commuting with the
differentials.** Kind: definition (structure). -/
structure GCxSEquiv (C : GCx k) (C' : GCx k') where
  /-- the degreewise isomorphisms -/
  f : ∀ n, C.X n ≃+ C'.X n
  /-- they are semilinear along `e` -/
  smul : ∀ n (r : k) (x : C.X n), f n (r • x) = e r • f n x
  /-- they commute with the differentials -/
  comm : ∀ i j (h : i + 1 = j) (x : C.X i), f j (C.d i j h x) = C'.d i j h (f i x)

end GCx

/-! ### Selmer data -/

section Sel

variable {k k' : Type u} [CommRing k] [CommRing k'] {e : k ≃+* k'} {D : SelData k}
  {D' : SelData k'}

/-- **The Selmer complexes of two Selmer data with semilinear component isomorphisms compatible
with `res` and `ι`.** Kind: definition (PROVED fields). -/
def selSEquiv (EG : GCxSEquiv e D.G D'.G) (EU : GCxSEquiv e D.U D'.U)
    (EL : GCxSEquiv e D.L D'.L)
    (hres : ∀ i j (h : i = j) (x : D.G.X i), EL.f j (D.res.f i j h x) = D'.res.f i j h (EG.f i x))
    (hι : ∀ i j (h : i = j) (x : D.U.X i), EL.f j (D.ι.f i j h x) = D'.ι.f i j h (EU.f i x)) :
    GCxSEquiv e (selCx D) (selCx D') where
  f n := show selT D n ≃+ selT D' n from
    (EG.f n).prodCongr ((EU.f n).prodCongr (EL.f (n - 1)))
  smul n r x := by
    obtain ⟨a, u, z⟩ := x
    change (EG.f n (r • a), EU.f n (r • u), EL.f (n - 1) (r • z)) =
      (e r • EG.f n a, e r • EU.f n u, e r • EL.f (n - 1) z)
    rw [EG.smul, EU.smul, EL.smul]
  comm i j h x := by
    obtain ⟨a, u, z⟩ := x
    change (EG.f j (D.G.d i j h a), EU.f j (D.U.d i j h u),
        EL.f (j - 1) (D.res.f i (j - 1) (by omega) a - D.ι.f i (j - 1) (by omega) u -
          D.L.d (i - 1) (j - 1) (by omega) z)) =
      (D'.G.d i j h (EG.f i a), D'.U.d i j h (EU.f i u),
        D'.res.f i (j - 1) (by omega) (EG.f i a) - D'.ι.f i (j - 1) (by omega) (EU.f i u) -
          D'.L.d (i - 1) (j - 1) (by omega) (EL.f (i - 1) z))
    rw [EG.comm, EU.comm, map_sub, map_sub, hres, hι, EL.comm]

end Sel

/-! ### Continuous cochains -/

section Cochains

variable {k k' : Type u} [CommRing k] [CommRing k']
  {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M M' : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [AddCommGroup M'] [Module k' M'] [DistribMulAction G M'] [SMulCommClass G k' M']
  [TopologicalSpace M'] [ContinuousAdd M'] [ContinuousConstSMul k' M'] [ContinuousSMul G M']
  (f : M ≃+ M') (hfc : Continuous f) (hfc' : Continuous f.symm)

/-- `c ↦ f ∘ c` on continuous cochains. Kind: definition. -/
def cochainFun (n : ℕ) (c : (contCochains k G M).X n) : (contCochains k' G M').X n :=
  ⟨(fun x => f (asFun k G M ((contSubCx k G M).el c).1 x) :
      (groupCohomology.inhomogeneousCochains (rep k' G M')).X n),
    by
      have hc : Continuous (asFun k G M ((contSubCx k G M).el c).1) :=
        ((contSubCx k G M).el c).2
      exact hfc.comp hc⟩

theorem cochainFun_apply (n : ℕ) (c : (contCochains k G M).X n) (x : Fin n → G) :
    asFun k' G M' ((contSubCx k' G M').el (cochainFun (k := k) (k' := k') f hfc n c)).1 x =
      f (asFun k G M ((contSubCx k G M).el c).1 x) := rfl

/-- **`C^n_cont(G, M) ≃ C^n_cont(G, M')`**, `c ↦ f ∘ c`. Kind: definition. -/
def cochainSEquiv (n : ℕ) : (contCochains k G M).X n ≃+ (contCochains k' G M').X n where
  toFun := cochainFun (k := k) (k' := k') f hfc n
  invFun := cochainFun (k := k') (k' := k) f.symm hfc' n
  left_inv _ := Subtype.ext (funext fun _ => f.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => f.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add f _ _)

variable {f hfc hfc'}

theorem cochainSEquiv_smul {e : k ≃+* k'} (hfk : ∀ (r : k) (m : M), f (r • m) = e r • f m)
    (n : ℕ) (r : k) (c : (contCochains k G M).X n) :
    cochainSEquiv (k := k) (k' := k') f hfc hfc' n (r • c) =
      e r • cochainSEquiv (k := k) (k' := k') f hfc hfc' n c :=
  Subtype.ext (funext fun _ => hfk r _)

/-- **`f ∘ −` commutes with the inhomogeneous differential** (the signs `(−1)^{j+1}` are ring
scalars, carried by `e`). Kind: PROVED. -/
theorem cochainSEquiv_d {e : k ≃+* k'} (hfk : ∀ (r : k) (m : M), f (r • m) = e r • f m)
    (hfg : ∀ (g : G) (m : M), f (g • m) = g • f m) (n : ℕ) (c : (contCochains k G M).X n) :
    cochainSEquiv (k := k) (k' := k') f hfc hfc' (n + 1)
        (((contCochains k G M).d n (n + 1)).hom c) =
      ((contCochains k' G M').d n (n + 1)).hom (cochainSEquiv (k := k) (k' := k') f hfc hfc' n c) := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := G) (M := M) n c g
  have h2 := contCochains_d_apply (k := k') (G := G) (M := M') n
    (cochainFun (k := k) (k' := k') f hfc n c) g
  change f (asFun k G M ((contSubCx k G M).el (((contCochains k G M).d n (n + 1)).hom c) :
      contCochain k G M (n + 1)) g) = _
  rw [h1]
  refine Eq.trans ?_ h2.symm
  rw [map_add, map_sum, hfg]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hfk, map_pow, map_neg, map_one]
  rfl

end Cochains

/-! ### Extension by zero and products -/

section NatPi

variable {k k' : Type u} [CommRing k] [CommRing k'] {e : k ≃+* k'}

/-- The degreewise isomorphisms of the extensions by zero. Kind: definition. -/
def natXEquiv {K : CochainComplex (ModuleCat.{u} k) ℕ} {K' : CochainComplex (ModuleCat.{u} k') ℕ}
    (φ : ∀ n, K.X n ≃+ K'.X n) : ∀ i : ℤ, natX K i ≃+ natX K' i
  | Int.ofNat n => φ n
  | Int.negSucc _ => AddEquiv.refl PUnit

/-- **Extension by zero of semilinear isomorphisms commuting with `d`.** Kind: definition
(PROVED fields). -/
def natSEquiv {K : CochainComplex (ModuleCat.{u} k) ℕ} {K' : CochainComplex (ModuleCat.{u} k') ℕ}
    (φ : ∀ n, K.X n ≃+ K'.X n) (hs : ∀ n (r : k) (x : K.X n), φ n (r • x) = e r • φ n x)
    (hd : ∀ n (x : K.X n), φ (n + 1) ((K.d n (n + 1)).hom x) = (K'.d n (n + 1)).hom (φ n x)) :
    GCxSEquiv e (natCx K) (natCx K') where
  f := natXEquiv φ
  smul
    | Int.ofNat n, r, x => hs n r x
    | Int.negSucc _, _, _ => rfl
  comm
    | Int.ofNat n, Int.ofNat m, h, x => by
      have hm : m = n + 1 := by
        have := h; simp only [Int.ofNat_eq_natCast] at this; omega
      subst hm
      exact hd n x
    | Int.negSucc _, _, _, _ => by
      change natXEquiv φ _ 0 = 0
      exact map_zero _
    | Int.ofNat n, Int.negSucc m, h, _ => absurd h (ofNat_add_one_ne_negSucc n m)

/-- **Products of semilinear isomorphisms commuting with `d`.** Kind: definition (PROVED
fields). -/
def piSEquiv {ι : Type u} {A : ι → GCx k} {A' : ι → GCx k'} (E : ∀ v, GCxSEquiv e (A v) (A' v)) :
    GCxSEquiv e (piCx A) (piCx A') where
  f n := show (∀ v, (A v).X n) ≃+ (∀ v, (A' v).X n) from AddEquiv.piCongrRight fun v => (E v).f n
  smul n r x := funext fun v => (E v).smul n r (x v)
  comm i j h x := funext fun v => (E v).comm i j h (x v)

end NatPi

/-! ### The genuine Selmer data -/

section Genuine

variable {k k' : Type u} [CommRing k] [CommRing k'] (e : k ≃+* k')
  (GS : Type u) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {M M' : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  [AddCommGroup M'] [Module k' M'] [DistribMulAction GS M'] [SMulCommClass GS k' M']
  [TopologicalSpace M'] [ContinuousAdd M'] [ContinuousConstSMul k' M'] [ContinuousSMul GS M']
  (f : M ≃+ M') (hfc : Continuous f) (hfc' : Continuous f.symm)
  (hfk : ∀ (r : k) (m : M), f (r • m) = e r • f m)
  (hfg : ∀ (g : GS) (m : M), f (g • m) = g • f m)

/-- `f` on the restricted modules. Kind: definition. -/
def resModEquiv (v : ι) : ResMod (loc v) M ≃+ ResMod (loc v) M' := f

/-- **The global cochains along `f`.** Kind: definition. -/
def globalSEquiv : GCxSEquiv e (globalCx k GS M) (globalCx k' GS M') :=
  natSEquiv (cochainSEquiv (k := k) (k' := k') f hfc hfc') (cochainSEquiv_smul hfk)
    (cochainSEquiv_d hfk hfg)

/-- **The local cochains at `v` along `f`.** Kind: definition. -/
def localSEquiv (v : ι) :
    GCxSEquiv e (localCx k GS Gv loc M v) (localCx k' GS Gv loc M' v) :=
  natSEquiv (cochainSEquiv (k := k) (k' := k') (resModEquiv GS Gv loc f v) hfc hfc')
    (cochainSEquiv_smul (f := resModEquiv GS Gv loc f v) hfk)
    (cochainSEquiv_d (f := resModEquiv GS Gv loc f v) hfk (fun g m => hfg (loc v g) m))

/-- **`f ∘ −` commutes with restriction.** Kind: PROVED. -/
theorem localSEquiv_res (v : ι) (i j : ℤ) (h : i = j) (x : (globalCx k GS M).X i) :
    (localSEquiv e GS Gv loc f hfc hfc' hfk hfg v).f j
        ((natHom (resCochains (k := k) (M := M) (loc v))).f i j h x) =
      (natHom (resCochains (k := k') (M := M') (loc v))).f i j h
        ((globalSEquiv e GS f hfc hfc' hfk hfg).f i x) := by
  subst h
  rcases i with n | n
  · rfl
  · rfl

variable {GS Gv loc}

/-- **The Selmer complexes of the genuine data along `f`**, given at every place a semilinear
isomorphism `EU v` of the condition complexes, commuting with `d` and with the condition maps.
Kind: definition (PROVED fields). -/
def selDataSEquiv (Δ : LocalConditions k GS Gv loc M) (Δ' : LocalConditions k' GS Gv loc M')
    (EU : ∀ v, GCxSEquiv e (Δ.U v) (Δ'.U v))
    (hι : ∀ v i j (h : i = j) (x : (Δ.U v).X i),
      (localSEquiv e GS Gv loc f hfc hfc' hfk hfg v).f j ((Δ.i v).f i j h x) =
        (Δ'.i v).f i j h ((EU v).f i x)) :
    GCxSEquiv e (selCx (selData k GS Gv loc M Δ)) (selCx (selData k' GS Gv loc M' Δ')) :=
  selSEquiv (globalSEquiv e GS f hfc hfc' hfk hfg) (piSEquiv EU)
    (piSEquiv (localSEquiv e GS Gv loc f hfc hfc' hfk hfg))
    (fun i j h x => funext fun v => localSEquiv_res e GS Gv loc f hfc hfc' hfk hfg v i j h x)
    (fun i j h x => funext fun v => hι v i j h (x v))

end Genuine

/-! ### The genuine Galois Selmer data, in the shape of `genCxResidualIso_of_ringChange` -/

section Galois

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k')
  {M M' : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module k' M'] [DistribMulAction (GKS K S) M']
  [SMulCommClass (GKS K S) k' M'] [TopologicalSpace M'] [ContinuousAdd M']
  [ContinuousConstSMul k' M'] [ContinuousSMul (GKS K S) M']
  (f : M ≃+ M') (hfc : Continuous f) (hfc' : Continuous f.symm)
  (hfk : ∀ (r : k) (m : M), f (r • m) = e r • f m)
  (hfg : ∀ (g : GKS K S) (m : M), f (g • m) = g • f m)

/-- **The degreewise identification of the genuine Galois Selmer complexes along a ring
isomorphism** (tex 4385–4414): the `fR`, `hfR`, `hdR` inputs of lane E2's
`genCxResidualIso_of_ringChange`. The inputs are an equivariant semilinear homeomorphic
`f : M ≃+ M'` and, at every place `v ∈ S`, semilinear isomorphisms of the condition complexes
commuting with `d` and the condition maps.

For the actual presentation, `M = M' = MinS` (the module `M_i` over `k = StageRing s` through
`e = stageEquiv s`: `mcoefModuleK`, `c • m = e c • m` by `rfl`), `f = AddEquiv.refl _`,
`hfc = hfc' = continuous_id`, `hfk = fun _ _ => rfl` and `hfg = fun _ _ => rfl`. What remains is
the place-by-place `EU`, `hι`: lane E2's pieces (1)–(2). Kind: PROVED. -/
theorem galoisSel_ringChange (Δ : GaloisLocalConditions K S k M)
    (Δ' : GaloisLocalConditions K S k' M') (EU : ∀ v, GCxSEquiv e (Δ.U v) (Δ'.U v))
    (hι : ∀ v i j (h : i = j) (x : (Δ.U v).X i),
      (localSEquiv e (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
        f hfc hfc' hfk hfg v).f j ((Δ.i v).f i j h x) = (Δ'.i v).f i j h ((EU v).f i x)) :
    ∃ fR : ∀ n, (selCx (galoisSelData K S k M Δ)).X n ≃+ (selCx (galoisSelData K S k' M' Δ')).X n,
      (∀ n (r : k) x, fR n (r • x) = e r • fR n x) ∧
      ∀ i j (h : i + 1 = j) x, fR j ((selCx (galoisSelData K S k M Δ)).d i j h x) =
        (selCx (galoisSelData K S k' M' Δ')).d i j h (fR i x) :=
  let E := selDataSEquiv e f hfc hfc' hfk hfg Δ Δ' EU hι
  ⟨E.f, E.smul, E.comm⟩

end Galois

end ZInQ.Contrib.CloudB3E1Torsion

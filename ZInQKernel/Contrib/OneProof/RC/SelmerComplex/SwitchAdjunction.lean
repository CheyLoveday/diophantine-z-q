import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuasiSide

/-!
# Lane RC26 (round 2): the switch duality adjunction from Selmer duality

Manuscript `diophantine_zq.tex`, tex 5068–5075 ("localization's connecting map is its dual under
the strict/relaxed duality, so its kernel is both `U` and `U^⊥`"); Nekovář, *Selmer complexes*
(Astérisque 310, 2006), Proposition 6.3.3 (p. 142: the duality maps are compatible with the cone
triangles, by the explicit cup-product formulas) and Theorem 6.3.4 (p. 143).

For the change-of-condition sequence `0 → C_str → C_rel → W_rel → 0` (strict condition
`f : U_str → U_rel`, quotient `g : U_rel → W_rel`) with connecting map `δ : H¹(W_rel) → H²(C_str)`,
and the Selmer duality map `γ : C_str → Hom(C_rel, k)[−3]`, `c ↦ (c' ↦ tr(c ∪ c'))`, this file
proves `SwitchAdjunctionFromDuality` by a cochain computation:

* `clsAt`: the class map `Z^i → H^i` of a relation-indexed complex in any degree; it is surjective
  (`clsAt_surjective`), its kernel is the coboundaries (`clsAt_boundary`, `clsAt_eq_zero`), and it
  is natural (`homologyMap_clsAt`).
* `exists_selTracePairing`: the trace pairing `H²(C_str) × H¹(C_rel) → k`,
  `⟨[c], [c']⟩ = tr(c ∪ c')`, well defined by the Leibniz rule of the cup product.
* `selTracePairing_separating`: the pairing separates in the first variable when `γ` is a
  quasi-isomorphism (over a field, a linear form on `C_rel¹` vanishing on the cocycles is a
  coboundary of the dual complex).
* `switchDelta_clsAt`: the element-level connecting map `δ[g u] = [(0, s, −ι u)]` when `du = f s`.
* `switchAdjunctionFromDuality_proof`: `⟨δ w, v⟩ = β(λ v, w)` for the switch pairing `β`, by
  `tr((0, s, −ι u) ∪ (b, t, y)) = tr((0, s, −ι u) ∪ (0, t, 0))`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.Uniform

section Cls

variable {k : Type} [Field k]

/-- The degree-one cycles of `K`, from the kernel of `d¹`. -/
def liftCyc1 (K : CochainComplex (ModuleCat.{0} k) ℤ) :
    ModuleCat.of k (LinearMap.ker (K.d 1 2).hom) ⟶ K.cycles 1 :=
  K.liftCycles (ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype) 2 (by simp) (by
    ext x; exact x.2)

/-- **The class of a degree-one cocycle** of a relation-indexed complex `W`. -/
def cls1 (W : GCx k) : LinearMap.ker (W.d 1 2 rfl) →ₗ[k] W.toCC.homology 1 :=
  (W.toCC.homologyπ 1).hom ∘ₗ (liftCyc1 W.toCC).hom ∘ₗ
    (LinearMap.ker (W.d 1 2 rfl)).subtype.codRestrict (LinearMap.ker (W.toCC.d 1 2).hom)
      (fun x => LinearMap.mem_ker.2 ((GCx.toCC_d_hom W 1 2 rfl x.1).trans x.2))

end Cls

section Switch

variable {k : Type} [Field k] (R : QuasiRelaxedLocalization k) {Ustr : GCx k} (f : GHom Ustr R.D.U)
  (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
  (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
  (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)

include hf hg hex in
/-- The change-of-condition short exact sequence `0 → C_str → C_rel → W_rel → 0`. -/
theorem switchSES_shortExact : (changeSES R.D f R.gR hfg).ShortExact :=
  relaxedQuotientNode_proof k R.D Ustr R.Wrel f R.gR hfg hf hg hex

/-- **The connecting map** `δ : H¹(W_rel) → H²(C_str)` of the change-of-condition sequence. -/
def switchDelta :
    R.Wrel.toCC.homology 1 →ₗ[k] (selCx (restrictData R.D f)).toCC.homology 2 :=
  ((switchSES_shortExact R f hfg hf hg hex).δ 1 2 (by simp)).hom

/-- Exactness at `H¹(W_rel)`: `im H¹(λ) = ker δ`. -/
theorem switchDelta_exact :
    LinearMap.range (H1 (quotMap R.D R.gR)) = LinearMap.ker (switchDelta R f hfg hf hg hex) := by
  have h := (switchSES_shortExact R f hfg hf hg hex).homology_exact₃ 1 2 (by simp)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact h

end Switch

/-! ### Classes of cocycles in any degree -/

section Classes

variable {k : Type} [Field k]

/-- The cycles of `K` in degree `i`, from the kernel of `dⁱ : Kⁱ → K^j` (`i + 1 = j`). -/
def liftCycAt (K : CochainComplex (ModuleCat.{0} k) ℤ) (i j : ℤ) (hij : i + 1 = j) :
    ModuleCat.of k (LinearMap.ker (K.d i j).hom) ⟶ K.cycles i :=
  K.liftCycles (ModuleCat.ofHom (LinearMap.ker (K.d i j).hom).subtype) j (by simpa using hij)
    (by ext x; exact x.2)

/-- The cycle attached to a cocycle `x ∈ ker dⁱ` has underlying cochain `x` (the cocycle
bookkeeping behind the cochain formulas of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142). -/
theorem iCycles_liftCycAt (K : CochainComplex (ModuleCat.{0} k) ℤ) (i j : ℤ) (hij : i + 1 = j)
    (x : LinearMap.ker (K.d i j).hom) :
    (K.iCycles i).hom ((liftCycAt K i j hij).hom x) = x.1 := by
  have := congrArg (fun f => ModuleCat.Hom.hom f x) (K.liftCycles_i
    (ModuleCat.ofHom (LinearMap.ker (K.d i j).hom).subtype) j (by simpa using hij)
      (by ext x; exact x.2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

/-- The inclusion of the cycles `Zⁱ(K) → Kⁱ` is injective (used to identify cycles by their
cochains in the computations of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142). -/
theorem iCycles_hom_injective (K : CochainComplex (ModuleCat.{0} k) ℤ) (i : ℤ) :
    Function.Injective (K.iCycles i).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- A cocycle of the relation-indexed complex `A` as a cocycle of the cochain complex `A.toCC`. -/
def kerToCC (A : GCx k) (i j : ℤ) (h : i + 1 = j) :
    LinearMap.ker (A.d i j h) →ₗ[k] LinearMap.ker (A.toCC.d i j).hom :=
  (LinearMap.ker (A.d i j h)).subtype.codRestrict (LinearMap.ker (A.toCC.d i j).hom)
    (fun x => LinearMap.mem_ker.2 ((GCx.toCC_d_hom A i j h x.1).trans x.2))

/-- **The class of a cocycle** of a relation-indexed complex in degree `i`:
`clsAt A i j h : ker (dⁱ : Aⁱ → A^j) → Hⁱ(A)`, `x ↦ [x]`. -/
def clsAt (A : GCx k) (i j : ℤ) (h : i + 1 = j) :
    LinearMap.ker (A.d i j h) →ₗ[k] A.toCC.homology i :=
  (A.toCC.homologyπ i).hom ∘ₗ (liftCycAt A.toCC i j h).hom ∘ₗ kerToCC A i j h

/-- The cycle underlying `clsAt A i j h x` has cochain `x` (bookkeeping for the cochain-level
duality computations of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142). -/
theorem iCycles_clsAt (A : GCx k) (i j : ℤ) (h : i + 1 = j) (x : LinearMap.ker (A.d i j h)) :
    (A.toCC.iCycles i).hom ((liftCycAt A.toCC i j h).hom (kerToCC A i j h x)) = x.1 :=
  iCycles_liftCycAt _ _ _ _ _

/-- The degree-one class map `cls1` (in which the switch hypothesis of tex 5068–5075 is stated)
is the class map `clsAt` in degree one. -/
theorem cls1_eq_clsAt (W : GCx k) (x : LinearMap.ker (W.d 1 2 rfl)) :
    cls1 W x = clsAt W 1 2 rfl x :=
  rfl

/-- **Every cohomology class is the class of a cocycle**: `clsAt : Zⁱ(A) → Hⁱ(A)` is surjective
(used to evaluate the pairings of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142, on cocycle
representatives). -/
theorem clsAt_surjective (A : GCx k) (i j : ℤ) (h : i + 1 = j) :
    Function.Surjective (clsAt A i j h) := by
  intro v
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (A.toCC.homologyπ i)).mp inferInstance v
  have hz : A.d i j h ((A.toCC.iCycles i).hom z) = 0 := by
    have := congrArg (fun f => ModuleCat.Hom.hom f z) (A.toCC.iCycles_d i j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at this
    exact (GCx.toCC_d_hom A i j h _).symm.trans this
  refine ⟨⟨_, hz⟩, ?_⟩
  change (A.toCC.homologyπ i).hom ((liftCycAt A.toCC i j h).hom _) = _
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_clsAt]

/-- **Coboundaries have trivial class**: `[d y] = 0` (one half of the description of the kernel
of the class map, used for the well-definedness of the pairing of Nekovář, *Selmer complexes*,
Prop. 6.3.3, p. 142). -/
theorem clsAt_boundary (A : GCx k) (i' i j : ℤ) (hi : i' + 1 = i) (h : i + 1 = j) (y : A.X i') :
    clsAt A i j h ⟨A.d i' i hi y, LinearMap.mem_ker.2 (A.d_d i' i j hi h y)⟩ = 0 := by
  have e : (liftCycAt A.toCC i j h).hom (kerToCC A i j h
      ⟨A.d i' i hi y, LinearMap.mem_ker.2 (A.d_d i' i j hi h y)⟩) =
      (A.toCC.toCycles i' i).hom y := by
    apply iCycles_hom_injective
    have h1 := iCycles_clsAt A i j h ⟨A.d i' i hi y, LinearMap.mem_ker.2 (A.d_d i' i j hi h y)⟩
    have h2 := congrArg (fun f => ModuleCat.Hom.hom f y) (A.toCC.toCycles_i i' i)
    have h3 := GCx.toCC_d_hom A i' i hi y
    exact h1.trans (h3.symm.trans h2.symm)
  change (A.toCC.homologyπ i).hom ((liftCycAt A.toCC i j h).hom _) = 0
  rw [e]
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (A.toCC.toCycles_comp_homologyπ i' i)
  exact this

/-- **Cocycles with trivial class are coboundaries**: if `[x] = 0` then `x = d y` (the other half
of the description of the kernel of the class map, used for the well-definedness of the pairing
of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142). -/
theorem clsAt_eq_zero (A : GCx k) (i' i j : ℤ) (hi : i' + 1 = i) (h : i + 1 = j)
    (x : LinearMap.ker (A.d i j h)) (hx : clsAt A i j h x = 0) :
    ∃ y : A.X i', A.d i' i hi y = x.1 := by
  let T := ShortComplex.mk (A.toCC.toCycles i' i) (A.toCC.homologyπ i)
    (A.toCC.toCycles_comp_homologyπ i' i)
  have hT : T.Exact := T.exact_of_g_is_cokernel
    (A.toCC.homologyIsCokernel i' i (by simp; omega))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT
    ((liftCycAt A.toCC i j h).hom (kerToCC A i j h x)) hx
  refine ⟨y, ?_⟩
  have h1 := congrArg (A.toCC.iCycles i).hom hy
  rw [iCycles_clsAt] at h1
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (A.toCC.toCycles_i i' i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact (GCx.toCC_d_hom A i' i hi y).symm.trans (this.symm.trans h1)

/-- **Naturality of classes**: for a chain map `φ`, `Hⁱ(φ) [x] = [φ x]` (used to compute
`H²(γ)` for the duality map `γ` of Nekovář, *Selmer complexes*, Thm. 6.3.4, p. 143, and the
localization `H¹(λ)` of tex 5068–5075 on cocycles). -/
theorem homologyMap_clsAt {A B : GCx k} (φ : GHom A B) (i j : ℤ) (h : i + 1 = j)
    (x : LinearMap.ker (A.d i j h)) (hx : φ.f i i rfl x.1 ∈ LinearMap.ker (B.d i j h)) :
    (HomologicalComplex.homologyMap (GHom.toCC φ) i).hom (clsAt A i j h x) =
      clsAt B i j h ⟨_, hx⟩ := by
  change (HomologicalComplex.homologyMap (GHom.toCC φ) i).hom
      ((A.toCC.homologyπ i).hom ((liftCycAt A.toCC i j h).hom (kerToCC A i j h x))) =
    (B.toCC.homologyπ i).hom ((liftCycAt B.toCC i j h).hom (kerToCC B i j h ⟨_, hx⟩))
  have hn := congrArg (fun g => ModuleCat.Hom.hom g
      ((liftCycAt A.toCC i j h).hom (kerToCC A i j h x)))
    (HomologicalComplex.homologyπ_naturality (GHom.toCC φ) i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [hn]
  congr 1
  apply iCycles_hom_injective
  have hi := congrArg (fun g => ModuleCat.Hom.hom g
      ((liftCycAt A.toCC i j h).hom (kerToCC A i j h x)))
    (HomologicalComplex.cyclesMap_i (GHom.toCC φ) i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi, iCycles_clsAt, iCycles_clsAt]
  rfl

end Classes

/-! ### Linear algebra over a field -/

section Linear

variable {k : Type} [Field k]

/-- **Descent along a surjection**: a linear map `φ : M → P` vanishing on the kernel of a
surjective linear map `π : M → N` factors as `φ = ψ ∘ π` (used to descend the cochain pairing
`tr(c ∪ c')` of Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142, to cohomology). -/
theorem exists_factor_of_surjective {M N P : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] (π : M →ₗ[k] N)
    (hπ : Function.Surjective π) (φ : M →ₗ[k] P) (h : ∀ m, π m = 0 → φ m = 0) :
    ∃ ψ : N →ₗ[k] P, ∀ m, ψ (π m) = φ m := by
  refine ⟨(LinearMap.ker π).liftQ φ (fun m hm => h m hm) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- **Linear forms killing a kernel factor through the map** (over a field): if `φ : V → k`
vanishes on `ker d` for a linear map `d : V → W`, then `φ = ψ ∘ d` for some `ψ : W → k` (the
injectivity of `k` as a `k`-module; it shows that the evaluation `H²(Hom(C_rel, k)[−3]) →
Hom(H¹(C_rel), k)` is injective, the field case of the duality of Nekovář, *Selmer complexes*,
Thm. 6.3.4, p. 143). -/
theorem exists_dual_factor_of_ker {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (d : V →ₗ[k] W) (φ : V →ₗ[k] k) (h : ∀ x, d x = 0 → φ x = 0) :
    ∃ ψ : W →ₗ[k] k, ∀ x, φ x = ψ (d x) := by
  obtain ⟨φ', hφ'⟩ := exists_factor_of_surjective d.rangeRestrict d.surjective_rangeRestrict φ
    (fun m hm => by
      apply h
      have := congrArg Subtype.val hm
      simpa using this)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ'
  refine ⟨g, fun x => ?_⟩
  rw [← hφ' x, ← hg]
  rfl

end Linear

/-! ### The trace pairing on Selmer cohomology -/

section Pairing

variable {k : Type} [Field k]

/-- **Coboundaries in the first variable pair to zero**: `tr(d c₀ ∪ c') = 0` for a cocycle
`c' ∈ C'¹` (the Leibniz rule of the Selmer cup product and `tr ∘ d = 0`; Nekovář, *Selmer
complexes*, Prop. 6.3.3, p. 142). -/
theorem selTrace_boundary_left {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (c₀ : (selCx D).X 1) (c' : (selCx D').X 1) (hc' : (selCx D').d 1 2 rfl c' = 0) :
    traceComp (selPair Q) tr 2 1 rfl ((selCx D).d 1 2 rfl c₀) c' = 0 := by
  have h := (selmerDualityComponents_proof k D D' Q tr htr).1 c₀ c'
  have e1 : ((selCx D).toCC.d 1 2).hom c₀ = (selCx D).d 1 2 rfl c₀ := GCx.toCC_d_hom _ 1 2 rfl c₀
  have e2 : ((selCx D').toCC.d 1 2).hom c' = 0 := (GCx.toCC_d_hom _ 1 2 rfl c').trans hc'
  calc traceComp (selPair Q) tr 2 1 rfl ((selCx D).d 1 2 rfl c₀) c'
      = traceComp (selPair Q) tr 2 1 rfl (((selCx D).toCC.d 1 2).hom c₀) c' := by rw [e1]
    _ = 1 * traceComp (selPair Q) tr 1 2 rfl c₀ (((selCx D').toCC.d 1 2).hom c') := h
    _ = 0 := by
      rw [e2, one_mul]
      exact map_zero (traceComp (selPair Q) tr 1 2 rfl c₀)

/-- **Coboundaries in the second variable pair to zero**: `tr(c ∪ d c'₀) = 0` for a cocycle
`c ∈ C²` (the Leibniz rule of the Selmer cup product and `tr ∘ d = 0`; Nekovář, *Selmer
complexes*, Prop. 6.3.3, p. 142). -/
theorem selTrace_boundary_right {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (c : (selCx D).X 2) (hc : (selCx D).d 2 3 rfl c = 0) (c₀ : (selCx D').X 0) :
    traceComp (selPair Q) tr 2 1 rfl c ((selCx D').d 0 1 rfl c₀) = 0 := by
  have h := (selmerDualityComponents_proof k D D' Q tr htr).2 c c₀
  have e1 : ((selCx D').toCC.d 0 1).hom c₀ = (selCx D').d 0 1 rfl c₀ := GCx.toCC_d_hom _ 0 1 rfl c₀
  have e2 : ((selCx D).toCC.d 2 3).hom c = 0 := (GCx.toCC_d_hom _ 2 3 rfl c).trans hc
  calc traceComp (selPair Q) tr 2 1 rfl c ((selCx D').d 0 1 rfl c₀)
      = traceComp (selPair Q) tr 2 1 rfl c (((selCx D').toCC.d 0 1).hom c₀) := by rw [e1]
    _ = (-1) * traceComp (selPair Q) tr 3 0 rfl (((selCx D).toCC.d 2 3).hom c) c₀ := h
    _ = 0 := by
      rw [e2]
      have h0 : traceComp (selPair Q) tr 3 0 rfl (0 : (selCx D).X 3) c₀ = 0 := by
        rw [map_zero, LinearMap.zero_apply]
      exact (congrArg (fun z => (-1 : k) * z) h0).trans (mul_zero _)

/-- **The trace pairing on cohomology** (Nekovář, *Selmer complexes*, Prop. 6.3.3, p. 142, in
degrees `(2, 1)`): there is a bilinear pairing `H²(C(D)) × H¹(C(D')) → k` with
`⟨[c], [c']⟩ = tr(c ∪ c')` for all cocycles `c ∈ C(D)²`, `c' ∈ C(D')¹`. -/
theorem exists_selTracePairing {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    ∃ pair : (selCx D).toCC.homology 2 →ₗ[k] (selCx D').toCC.homology 1 →ₗ[k] k,
      ∀ (c : LinearMap.ker ((selCx D).d 2 3 rfl)) (c' : LinearMap.ker ((selCx D').d 1 2 rfl)),
        pair (clsAt (selCx D) 2 3 rfl c) (clsAt (selCx D') 1 2 rfl c') =
          traceComp (selPair Q) tr 2 1 rfl c.1 c'.1 := by
  let B₀ := (traceComp (selPair Q) tr 2 1 rfl).compl₁₂
    (LinearMap.ker ((selCx D).d 2 3 rfl)).subtype (LinearMap.ker ((selCx D').d 1 2 rfl)).subtype
  obtain ⟨B₁, hB₁⟩ := exists_factor_of_surjective (clsAt (selCx D) 2 3 rfl)
    (clsAt_surjective _ 2 3 rfl) B₀ (by
      intro c hc
      obtain ⟨c₀, hc₀⟩ := clsAt_eq_zero (selCx D) 1 2 3 rfl rfl c hc
      refine LinearMap.ext fun c' => ?_
      change traceComp (selPair Q) tr 2 1 rfl c.1 c'.1 = 0
      rw [← hc₀]
      exact selTrace_boundary_left Q tr htr c₀ c'.1 (LinearMap.mem_ker.1 c'.2))
  obtain ⟨B₂, hB₂⟩ := exists_factor_of_surjective (clsAt (selCx D') 1 2 rfl)
    (clsAt_surjective _ 1 2 rfl) B₁.flip (by
      intro c' hc'
      obtain ⟨c₀, hc₀⟩ := clsAt_eq_zero (selCx D') 0 1 2 rfl rfl c' hc'
      refine LinearMap.ext fun x => ?_
      obtain ⟨c, rfl⟩ := clsAt_surjective (selCx D) 2 3 rfl x
      change B₁ (clsAt _ 2 3 rfl c) c' = 0
      rw [hB₁]
      change traceComp (selPair Q) tr 2 1 rfl c.1 c'.1 = 0
      rw [← hc₀]
      exact selTrace_boundary_right Q tr htr c.1 (LinearMap.mem_ker.1 c.2) c₀)
  refine ⟨B₂.flip, fun c c' => ?_⟩
  change B₂ (clsAt _ 1 2 rfl c') (clsAt _ 2 3 rfl c) = _
  rw [hB₂]
  change B₁ (clsAt _ 2 3 rfl c) c' = _
  rw [hB₁]
  rfl

/-- **Separation of the trace pairing** (Nekovář, *Selmer complexes*, Thm. 6.3.4, p. 143, over a
field): if the Selmer duality map `γ : C(D) → Hom(C(D'), k)[−3]` is a quasi-isomorphism and a
cocycle `c ∈ C(D)²` satisfies `tr(c ∪ c') = 0` for every cocycle `c' ∈ C(D')¹`, then `[c] = 0`.
Indeed `γ c` vanishes on the cocycles of `C(D')¹`, hence is `ψ ∘ d¹` for a linear form `ψ` on
`C(D')²`, i.e. a coboundary of the dual complex; so `H²(γ)[c] = 0` and `[c] = 0`. -/
theorem selTracePairing_separating {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hqi : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (c : LinearMap.ker ((selCx D).d 2 3 rfl))
    (h0 : ∀ c' : LinearMap.ker ((selCx D').d 1 2 rfl),
      traceComp (selPair Q) tr 2 1 rfl c.1 c'.1 = 0) :
    clsAt (selCx D) 2 3 rfl c = 0 := by
  have hφ : ∀ x : (selCx D').X 1, (selCx D').d 1 2 rfl x = 0 →
      asDual ((selmerDualityMap Q tr htr).f 2 2 rfl c.1) x = 0 := fun x hx => h0 ⟨x, hx⟩
  obtain ⟨ψ, hψ⟩ := exists_dual_factor_of_ker ((selCx D').d 1 2 rfl)
    (asDual ((selmerDualityMap Q tr htr).f 2 2 rfl c.1)) hφ
  have hb : (selmerDualityMap Q tr htr).f 2 2 rfl c.1 = (dualCx (selCx D') 3).d 1 2 rfl ψ := by
    refine dualCx_ext fun x => ?_
    have hs : (-(sgn 1) : ℤ) = 1 := by rw [sgn_one, neg_neg]
    have e2 : (-(sgn 1)) • asDual (A := selCx D') (m := 3) (n := 1) ψ
          ((selCx D').d (3 - 2) (3 - 1) (by omega) x) =
        asDual (A := selCx D') (m := 3) (n := 1) ψ ((selCx D').d (3 - 2) (3 - 1) (by omega) x) := by
      rw [hs, one_smul]
    exact (hψ x).trans ((dualCx_d_apply (selCx D') 3 1 2 rfl ψ x).trans e2).symm
  have hz : (selmerDualityMap Q tr htr).f 2 2 rfl c.1 ∈
      LinearMap.ker ((dualCx (selCx D') 3).d 2 3 rfl) := by
    rw [hb]; exact LinearMap.mem_ker.2 ((dualCx (selCx D') 3).d_d 1 2 3 rfl rfl ψ)
  have h1 := homologyMap_clsAt (selmerDualityMap Q tr htr) 2 3 rfl c hz
  have h2 : clsAt (dualCx (selCx D') 3) 2 3 rfl ⟨_, hz⟩ = 0 := by
    have e : (⟨_, hz⟩ : LinearMap.ker ((dualCx (selCx D') 3).d 2 3 rfl)) =
        ⟨(dualCx (selCx D') 3).d 1 2 rfl ψ,
          LinearMap.mem_ker.2 ((dualCx (selCx D') 3).d_d 1 2 3 rfl rfl ψ)⟩ := Subtype.ext hb
    rw [e]
    exact clsAt_boundary (dualCx (selCx D') 3) 1 2 3 rfl rfl ψ
  have : IsIso (HomologicalComplex.homologyMap (GHom.toCC (selmerDualityMap Q tr htr)) 2) :=
    (quasiIsoAt_iff_isIso_homologyMap (GHom.toCC (selmerDualityMap Q tr htr)) 2).mp inferInstance
  have hinj := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (GHom.toCC (selmerDualityMap Q tr htr)) 2)).1
  apply hinj
  refine h1.trans (h2.trans ?_)
  exact (map_zero _).symm

end Pairing

/-! ### The connecting map on cocycles -/

section Delta

variable {k : Type} [Field k]

/-- **The connecting map on cocycles** (the cone triangle of Nekovář, *Selmer complexes*,
Prop. 6.3.3, p. 142, for the change of local condition at the switch, tex 5068–5075): for
`u ∈ U_rel¹` with `g u` a cocycle of `W_rel` and `du = f s` (`s ∈ U_str²`), the cochain
`(0, s, −ι u) ∈ C_str²` is a cocycle and `δ [g u] = [(0, s, −ι u)]`: it is the preimage under
`C_str → C_rel` of `d(0, u, 0) = (0, du, −ι u)`, and `(0, u, 0)` lifts `g u`. -/
theorem switchDelta_clsAt (R : QuasiRelaxedLocalization k) {Ustr : GCx k} (f : GHom Ustr R.D.U)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (u : R.D.U.X 1) (s : Ustr.X 2) (hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s)
    (hcu : R.gR.f 1 1 rfl u ∈ LinearMap.ker (R.Wrel.d 1 2 rfl)) :
    ∃ hc : (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
        (selCx (restrictData R.D f)).X 2) ∈ LinearMap.ker ((selCx (restrictData R.D f)).d 2 3 rfl),
    switchDelta R f hfg hf hg hex (clsAt R.Wrel 1 2 rfl ⟨_, hcu⟩) =
      clsAt (selCx (restrictData R.D f)) 2 3 rfl ⟨_, hc⟩ := by
  have hS := switchSES_shortExact R f hfg hf hg hex
  have hx₃ : ((forget₂ (ModuleCat k) Ab).map ((changeSES R.D f R.gR hfg).X₃.d 1 2))
      (R.gR.f 1 1 rfl u) = 0 :=
    (GCx.toCC_d_hom R.Wrel 1 2 rfl _).trans hcu
  have hx₂ : ((forget₂ (ModuleCat k) Ab).map ((changeSES R.D f R.gR hfg).g.f 1))
      (((0 : R.D.G.X 1), u, (0 : R.D.L.X (1 - 1))) : (selCx R.D).X 1) = R.gR.f 1 1 rfl u := rfl
  have hx₁ : ((forget₂ (ModuleCat k) Ab).map ((changeSES R.D f R.gR hfg).f.f 2))
      (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
        (selCx (restrictData R.D f)).X 2) =
      ((forget₂ (ModuleCat k) Ab).map ((changeSES R.D f R.gR hfg).X₂.d 1 2))
      (((0 : R.D.G.X 1), u, (0 : R.D.L.X (1 - 1))) : (selCx R.D).X 1) := by
    refine Eq.trans ?_ (GCx.toCC_d_hom (selCx R.D) 1 2 rfl _).symm
    change (((0 : R.D.G.X 2), f.f 2 2 rfl s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) : selT R.D 2) =
      ((R.D.G.d 1 2 rfl 0, R.D.U.d 1 2 rfl u, R.D.res.f 1 (2 - 1) (by omega) 0 -
        R.D.ι.f 1 (2 - 1) (by omega) u - R.D.L.d (1 - 1) (2 - 1) (by omega) 0) : selT R.D 2)
    rw [hu, map_zero, map_zero, map_zero, zero_sub, sub_zero]
  have hc0 : (selCx (restrictData R.D f)).d 2 3 rfl
      (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
        (selCx (restrictData R.D f)).X 2) = 0 := by
    have := hS.d_eq_zero_of_f_eq_d_apply 1 2 _ _ hx₁ 3
    exact (GCx.toCC_d_hom (selCx (restrictData R.D f)) 2 3 rfl _).symm.trans this
  have hc : (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
      (selCx (restrictData R.D f)).X 2) ∈ LinearMap.ker ((selCx (restrictData R.D f)).d 2 3 rfl) :=
    hc0
  refine ⟨hc, ?_⟩
  have key := hS.δ_apply 1 2 (by simp) _ hx₃ _ hx₂ _ hx₁ 3 (by simp)
  have e3 : (changeSES R.D f R.gR hfg).X₃.cyclesMk (R.gR.f 1 1 rfl u) 2 (by simp) hx₃ =
      (liftCycAt R.Wrel.toCC 1 2 rfl).hom (kerToCC R.Wrel 1 2 rfl ⟨_, hcu⟩) := by
    apply iCycles_hom_injective R.Wrel.toCC 1
    have h1 : (R.Wrel.toCC.iCycles 1).hom ((changeSES R.D f R.gR hfg).X₃.cyclesMk
        (R.gR.f 1 1 rfl u) 2 (by simp) hx₃) = R.gR.f 1 1 rfl u :=
      HomologicalComplex.i_cyclesMk (changeSES R.D f R.gR hfg).X₃ (R.gR.f 1 1 rfl u) 2
        (by simp) hx₃
    exact h1.trans (iCycles_clsAt R.Wrel 1 2 rfl ⟨_, hcu⟩).symm
  have e1 : (changeSES R.D f R.gR hfg).X₁.cyclesMk
      (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
        (selCx (restrictData R.D f)).X 2) 3
        (by simp) (hS.d_eq_zero_of_f_eq_d_apply 1 2 _ _ hx₁ 3) =
      (liftCycAt (selCx (restrictData R.D f)).toCC 2 3 rfl).hom
        (kerToCC (selCx (restrictData R.D f)) 2 3 rfl ⟨_, hc⟩) := by
    apply iCycles_hom_injective (selCx (restrictData R.D f)).toCC 2
    have h1 : ((selCx (restrictData R.D f)).toCC.iCycles 2).hom
        ((changeSES R.D f R.gR hfg).X₁.cyclesMk
          (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
            (selCx (restrictData R.D f)).X 2) 3
          (by simp) (hS.d_eq_zero_of_f_eq_d_apply 1 2 _ _ hx₁ 3)) =
        (((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u)) :
          (selCx (restrictData R.D f)).X 2) :=
      HomologicalComplex.i_cyclesMk (changeSES R.D f R.gR hfg).X₁ _ 3 (by simp) _
    exact h1.trans (iCycles_clsAt (selCx (restrictData R.D f)) 2 3 rfl ⟨_, hc⟩).symm
  have e3' := congrArg (fun z => (hS.δ 1 2 (by simp)).hom
    (((changeSES R.D f R.gR hfg).X₃.homologyπ 1).hom z)) e3
  have e1' := congrArg (fun z => (((changeSES R.D f R.gR hfg).X₁.homologyπ 2).hom z)) e1
  exact e3'.symm.trans (key.trans e1')

end Delta

/-- **The switch duality adjunction from Selmer duality** (target statement): for the relaxed
localization `R`, a strict condition `f : U_str → U_rel` with quotient `W_rel`, and Selmer pairing data
`Q` between `C_str` and `C_rel` with trace `tr`, if the Selmer duality map is a quasi-isomorphism
and the local residue pairing on `H¹(W_rel)` is the switch pairing in the coordinates `R.eR`, then
`SwitchDualityAdjunction` holds for the genuine connecting map. -/
def SwitchAdjunctionFromDuality : Prop :=
  ∀ (k : Type) [Field k] (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1),
    QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)) →
    (∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
      tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
          ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
        switchPairing ε σ J (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu))) →
    SwitchDualityAdjunction R (restrictData R.D f) ε σ J hε hσ hJ2
      (switchDelta R f hfg hf hg hex) (switchDelta_exact R f hfg hf hg hex)

/-- **The switch duality adjunction from Selmer duality** (tex 5068–5075; Nekovář, *Selmer
complexes*, Astérisque 310, Prop. 6.3.3, p. 142, explicit cup-product formulas, and Thm. 6.3.4,
p. 143). The pairing `H²(C_str) × H¹(C_rel) → k` is `⟨[c], [c']⟩ = tr(c ∪ c')`
(`exists_selTracePairing`); it separates in the first variable because the Selmer duality map is a
quasi-isomorphism (`selTracePairing_separating`). For `w = [g u] ∈ H¹(W_rel)` with `du = f s` and
`v = [(b, t, y)] ∈ H¹(C_rel)`, `δ w = [(0, s, −ι u)]` (`switchDelta_clsAt`) and
`H¹(λ) v = [g t]`, so `⟨δ w, v⟩ = tr((0, s, −ι u) ∪ (b, t, y)) = tr((0, s, −ι u) ∪ (0, t, 0))`,
which is the switch pairing `β(eR [g t], eR [g u]) = β(eR (H¹(λ) v), eR w)` by hypothesis. -/
theorem switchAdjunctionFromDuality_proof : SwitchAdjunctionFromDuality := by
  intro k _ R Ustr f hfg hf hg hex Q tr htr ε σ J hε hσ hJ2 hqi hsw
  obtain ⟨pair, hpair⟩ := exists_selTracePairing Q tr htr
  refine ⟨pair, fun x hx => ?_, fun w v => ?_⟩
  · obtain ⟨c, rfl⟩ := clsAt_surjective _ 2 3 rfl x
    exact selTracePairing_separating Q tr htr hqi c (fun c' => (hpair c c').symm.trans (hx _))
  · obtain ⟨cw, rfl⟩ := clsAt_surjective R.Wrel 1 2 rfl w
    obtain ⟨⟨⟨b, t, y⟩, hc'⟩, rfl⟩ := clsAt_surjective (selCx R.D) 1 2 rfl v
    obtain ⟨u, hu⟩ := hg 1 cw.1
    have hcu : R.gR.f 1 1 rfl u ∈ LinearMap.ker (R.Wrel.d 1 2 rfl) := hu ▸ cw.2
    have hdu : R.gR.f 2 2 rfl (R.D.U.d 1 2 rfl u) = 0 :=
      (R.gR.comm 1 2 1 2 rfl rfl rfl rfl u).trans (LinearMap.mem_ker.1 hcu)
    obtain ⟨s, hs⟩ := hex 2 _ hdu
    obtain ⟨hc, hδ⟩ := switchDelta_clsAt R f hfg hf hg hex u s hs.symm hcu
    have ht : R.D.U.d 1 2 rfl t = 0 := by
      have h := LinearMap.mem_ker.1 hc'
      exact congrArg (fun z : selT R.D 2 => z.2.1) h
    have hgt : R.gR.f 1 1 rfl t ∈ LinearMap.ker (R.Wrel.d 1 2 rfl) :=
      LinearMap.mem_ker.2 ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl t).symm.trans
        (by rw [ht, map_zero]))
    have hH1 : H1 (quotMap R.D R.gR) (clsAt (selCx R.D) 1 2 rfl ⟨(b, t, y), hc'⟩) =
        clsAt R.Wrel 1 2 rfl ⟨_, hgt⟩ :=
      homologyMap_clsAt (quotMap R.D R.gR) 1 2 rfl ⟨(b, t, y), hc'⟩ hgt
    have hw : cw = ⟨R.gR.f 1 1 rfl u, hcu⟩ := Subtype.ext hu.symm
    rw [hw, hδ, hpair, hH1]
    have h1 := tr_selCup_loc Q tr 2 s (-(R.D.ι.f 1 (2 - 1) (by omega) u)) b t y
    have h2 := hsw t u s ht hs.symm ⟨_, hgt⟩ ⟨_, hcu⟩ rfl rfl
    exact h1.trans h2

end ZInQ.Manuscript.RC.SelmerComplex

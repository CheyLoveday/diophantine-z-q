import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition

/-!
# Lane RC26: change of local conditions, `0 → C(Δ) → C(Δ') → ⊕_v Δ'_v / Δ_v → 0`

Manuscript `diophantine_zq.tex`, "Actual support comparisons", tex 3494–3498: "Replacing the
unramified condition by the full condition then gives the singular quotient by a cone of Selmer
cones." Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.1.3 (p. 136: the exact sequences
of a Selmer complex) and 6.4.2(i) (functoriality of `C_f` in morphisms of local conditions).

For local conditions `Δ = (U_v → C^•_cont(G_v, M))_v` and `Δ' = (U'_v → C^•_cont(G_v, M))_v` on
the genuine Selmer data of `Selmer.lean` and a termwise injective morphism of local conditions
`φ_v : U_v → U'_v` over the local complexes (`i'_v ∘ φ_v = i_v`), this file constructs

* `quotCx φ`, `quotMk φ`: the degreewise quotient complex `B^n / φ(A^n)` of a chain map
  `φ : A → B`, with the induced differential, and the (surjective) quotient map `B → B/φ(A)`
  with kernel `φ(A)`; `quotSES_shortExact`: `0 → A → B → B/φ(A) → 0` is short exact for `φ`
  termwise injective;
* `CondInclusion Δ Δ'`: termwise injective morphisms of local conditions (non-vacuity:
  `CondInclusion.refl`, `CondInclusion.ofStrict`; the case of the text: `CondInclusion.toRelaxed`,
  a local condition inside the full condition);
* `changeCondSES F`: the short complex `0 → C(Δ) → C(Δ') → ⊕_v U'_v / U_v → 0` (first map
  `(a, u, x) ↦ (a, φ u, x)`, Nekovář 6.4.2(i) with `λ = id`; second map `(a, u', x) ↦ [u']`), and
  its **short exactness** `changeCondSES_shortExact` (PROVED), with the long exact cohomology
  sequence `changeCond_les`;
* the comparison with the abstract support-change node of the Selmer-duality files: the abstract
  `changeSES` for `restrictData (selData Δ') (piMap φ)` is short exact by
  `relaxedQuotientNode_proof` (`changeSES_selData_shortExact`) and is isomorphic to
  `changeCondSES F` through the identity of `C(Δ)` (`changeSESIso`), which gives a second proof
  `changeCondSES_shortExact'`;
* the Galois specialization for `GaloisLocalConditions` (`galoisChangeCondSES_shortExact`,
  `galoisRelaxedSES_shortExact`);
* the case of the text: the unramified condition `[W --(Φ−1)--> W] → C^•_cont(G_{K_w}, M)` of
  `UnramifiedCondition.lean` is termwise injective for an injective `f : W → M`
  (`urToLocal_injective`, `urToLocal_galois_injective`, using the surjectivity of
  `G_{K_w} → Gal(K_w^{ur}/K_w)`), so the unramified conditions lie in the full conditions
  (`unramifiedInRelaxed`) and `0 → C(ur) → C(rel) → ⊕_w C^•_cont(G_{K_w}, M) / U^{ur}_w → 0` is
  short exact (`unramifiedToRelaxed_shortExact`); non-vacuity: the residual module `𝔽₂²`
  (`unramifiedW2Conditions`, `unramifiedInRelaxedW2`, `unramifiedToRelaxedW2_shortExact`).

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

/-! ### The quotient complex of a chain map -/

section Quot

variable {k : Type u} [CommRing k] {A B : GCx k} (φ : GHom A B)

/-- The image `φ(A^n) ⊆ B^n` of a chain map in degree `n` (the subcomplex of `B` by which the
change-of-condition quotient of `diophantine_zq.tex`, tex 3494–3498, is taken). -/
def quotSub (n : ℤ) : Submodule k (B.X n) :=
  LinearMap.range (φ.f n n rfl)

/-- The image of a chain map is a subcomplex: `d(φ(A^i)) ⊆ φ(A^j)` (the differential of the
quotient complex of `diophantine_zq.tex`, tex 3494–3498, is well defined). PROVED. -/
theorem quotSub_le_comap (i j : ℤ) (h : i + 1 = j) :
    quotSub φ i ≤ (quotSub φ j).comap (B.d i j h) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.d i j h a, φ.comm i j i j rfl h h rfl a⟩

/-- **The quotient complex** `B / φ(A)`: terms `B^n / φ(A^n)` with the differential induced by
that of `B` (for `φ` the inclusion of the unramified condition into the full condition, the
singular quotient of `diophantine_zq.tex`, tex 3494–3498; the cokernel term of Nekovář,
*Selmer complexes*, 6.1.3, for a change of local conditions). -/
def quotCx : GCx k where
  X n := ModuleCat.of k (B.X n ⧸ quotSub φ n)
  d i j h := (quotSub φ i).mapQ (quotSub φ j) (B.d i j h) (quotSub_le_comap φ i j h)
  d_d i j l hij hjl x := by
    obtain ⟨b, rfl⟩ := (quotSub φ i).mkQ_surjective x
    change Submodule.Quotient.mk (B.d j l hjl (B.d i j hij b)) = 0
    rw [B.d_d, Submodule.Quotient.mk_zero]

/-- **The quotient map** `B → B / φ(A)`, `b ↦ [b]`, a chain map (the projection onto the
singular quotient, `diophantine_zq.tex`, tex 3494–3498). -/
def quotMk : GHom B (quotCx φ) where
  f i j h := by
    subst h
    exact (quotSub φ i).mkQ
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- The quotient map sends `b` to its class `[b]` (`diophantine_zq.tex`, tex 3494–3498). -/
theorem quotMk_f_apply (n : ℤ) (b : B.X n) :
    (quotMk φ).f n n rfl b = (Submodule.Quotient.mk b : B.X n ⧸ quotSub φ n) :=
  rfl

/-- The quotient map is surjective in every degree (`diophantine_zq.tex`, tex 3494–3498). PROVED. -/
theorem quotMk_surjective (n : ℤ) : Function.Surjective ((quotMk φ).f n n rfl) :=
  (quotSub φ n).mkQ_surjective

/-- The kernel of the quotient map is the image of `φ` (`diophantine_zq.tex`, tex 3494–3498).
PROVED. -/
theorem quotMk_eq_zero_iff (n : ℤ) (b : B.X n) :
    (quotMk φ).f n n rfl b = 0 ↔ ∃ a, φ.f n n rfl a = b :=
  (Submodule.Quotient.mk_eq_zero _).trans LinearMap.mem_range

/-- The composite `A → B → B / φ(A)` vanishes (`diophantine_zq.tex`, tex 3494–3498). PROVED. -/
theorem quotMk_comp_apply (n : ℤ) (a : A.X n) : (quotMk φ).f n n rfl (φ.f n n rfl a) = 0 :=
  (quotMk_eq_zero_iff φ n _).2 ⟨a, rfl⟩

/-- The short complex `0 → A → B → B / φ(A) → 0` of cochain complexes (Nekovář, *Selmer
complexes*, 6.1.3, for the condition complexes; `diophantine_zq.tex`, tex 3494–3498). -/
def quotSES : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  ShortComplex.mk (GHom.toCC φ) (GHom.toCC (quotMk φ)) (by
    rw [GHom.toCC_comp]
    ext i a
    exact quotMk_comp_apply φ i a)

/-- **`0 → A → B → B / φ(A) → 0` is short exact** for a termwise injective chain map `φ`
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3). PROVED. -/
theorem quotSES_shortExact (hφ : ∀ n, Function.Injective (φ.f n n rfl)) :
    (quotSES φ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro b hb
    exact (quotMk_eq_zero_iff φ i b).1 hb
  · rw [ModuleCat.mono_iff_injective]
    exact hφ i
  · rw [ModuleCat.epi_iff_surjective]
    exact quotMk_surjective φ i

/-- The quotient of a complex by itself (along the identity) is zero in every degree: the change
of condition `Δ ⊆ Δ` has zero singular quotient (`diophantine_zq.tex`, tex 3494–3498). PROVED. -/
theorem quotCx_idGHom_subsingleton (A : GCx k) (n : ℤ) :
    Subsingleton ((quotCx (idGHom A)).X n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := (quotSub (idGHom A) n).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (quotSub (idGHom A) n).mkQ_surjective y
  exact ((quotMk_eq_zero_iff (idGHom A) n a).2 ⟨a, rfl⟩).trans
    ((quotMk_eq_zero_iff (idGHom A) n b).2 ⟨b, rfl⟩).symm

end Quot

/-! ### Change of local conditions on the genuine Selmer complexes -/

section Change

variable {k : Type u} [CommRing k]
  {GS : Type u} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- **A termwise injective morphism of local conditions** `Δ → Δ'` over the local complexes
(Nekovář, *Selmer complexes*, 6.4.2(i), with `λ = id` and zero homotopies): chain maps
`φ_v : U_v → U'_v` with `i'_v ∘ φ_v = i_v` and every `φ_v` injective in every degree. For
`Δ` the unramified and `Δ'` the full condition this is the situation of `diophantine_zq.tex`,
tex 3494–3498. Non-vacuity: `CondInclusion.refl`, `CondInclusion.ofStrict`. -/
structure CondInclusion (Δ Δ' : LocalConditions k GS Gv loc M) where
  /-- The chain maps `φ_v : U_v → U'_v`. -/
  φ : ∀ v, GHom (Δ.U v) (Δ'.U v)
  /-- Compatibility with the maps to the local complexes: `i'_v ∘ φ_v = i_v`. -/
  compat : ∀ v (n : ℤ) (x : (Δ.U v).X n),
    (Δ'.i v).f n n rfl ((φ v).f n n rfl x) = (Δ.i v).f n n rfl x
  /-- Every `φ_v` is injective in every degree. -/
  inj : ∀ v (n : ℤ), Function.Injective ((φ v).f n n rfl)

/-- **Non-vacuity of `CondInclusion`**: the identity inclusion `Δ ⊆ Δ` (its singular quotient is
zero, `quotCx_idGHom_subsingleton`; `diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer
complexes*, 6.4.2(i)). -/
def CondInclusion.refl (Δ : LocalConditions k GS Gv loc M) : CondInclusion Δ Δ where
  φ v := idGHom (Δ.U v)
  compat _ _ _ := rfl
  inj _ _ := fun _ _ h => h

/-- **Non-vacuity of `CondInclusion`**: the strict conditions `U_v = 0` lie in any local
conditions (the change of condition then recovers the shape of `strictSES_shortExact`, Nekovář,
*Selmer complexes*, 6.1.3; `diophantine_zq.tex`, tex 3494–3498). -/
def CondInclusion.ofStrict (Δ : LocalConditions k GS Gv loc M) :
    CondInclusion (strictConditions k GS Gv loc M) Δ where
  φ _ := zeroGHom _ _
  compat v n _ := by
    change (Δ.i v).f n n rfl 0 = 0
    exact map_zero _
  inj _ _ := fun _ _ _ => rfl

/-- **A local condition inside the full condition** (`diophantine_zq.tex`, tex 3494–3498:
"replacing the unramified condition by the full condition"): if every `i_v : U_v → C(G_v, M)` is
injective in every degree, `i_v` itself is an inclusion of `Δ` into the relaxed conditions
`U'_v = C^•_cont(G_v, M)` (Nekovář, *Selmer complexes*, 6.4.2(i)). -/
def CondInclusion.toRelaxed (Δ : LocalConditions k GS Gv loc M)
    (hinj : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    CondInclusion Δ (relaxedConditions k GS Gv loc M) where
  φ := Δ.i
  compat _ _ _ := rfl
  inj := hinj

variable {Δ Δ' : LocalConditions k GS Gv loc M}

/-- **The singular quotient** `⊕_v U'_v / φ_v(U_v)` of a change of local conditions (for the
unramified condition inside the full condition, the singular quotient of `diophantine_zq.tex`,
tex 3494–3498; `⊕_v` as the product `piCx`, the direct sum for finitely many places). -/
def singQuot (F : CondInclusion Δ Δ') : GCx k :=
  piCx fun v => quotCx (F.φ v)

/-- **The comparison `C(Δ) → C(Δ')`**, `(a, u, x) ↦ (a, φ u, x)` (Nekovář, *Selmer complexes*,
6.4.2(i) with `λ = id`; `diophantine_zq.tex`, tex 3494–3498). A chain map. -/
def changeIncl (F : CondInclusion Δ Δ') :
    GHom (selCx (selData k GS Gv loc M Δ)) (selCx (selData k GS Gv loc M Δ')) :=
  condMap Δ Δ' F.φ F.compat

/-- **The projection `C(Δ') → ⊕_v U'_v / U_v`**, `(a, u', x) ↦ [u']` onto the singular quotient
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3). A chain map. -/
def changeProj (F : CondInclusion Δ Δ') : GHom (selCx (selData k GS Gv loc M Δ')) (singQuot F) :=
  quotMap (selData k GS Gv loc M Δ') (W := singQuot F) (piMap fun v => quotMk (F.φ v))

omit [IsTopologicalGroup GS] in
/-- The quotient maps kill the image of `φ`: `[φ u] = 0` (`diophantine_zq.tex`, tex 3494–3498).
PROVED. -/
theorem changeCond_hfg (F : CondInclusion Δ Δ') (i : ℤ) (u : (piCx Δ.U).X i) :
    (piMap fun v => quotMk (F.φ v)).f i i rfl ((piMap F.φ).f i i rfl u) = 0 :=
  funext fun v => quotMk_comp_apply (F.φ v) i (u v)

/-- **The change-of-condition sequence** `0 → C(Δ) → C(Δ') → ⊕_v U'_v / U_v → 0` of cochain
complexes (`diophantine_zq.tex`, tex 3494–3498: "replacing the unramified condition by the full
condition then gives the singular quotient by a cone of Selmer cones"; Nekovář, *Selmer
complexes*, 6.1.3 and 6.4.2(i)). -/
def changeCondSES (F : CondInclusion Δ Δ') : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ) :=
  ShortComplex.mk (GHom.toCC (changeIncl F)) (GHom.toCC (changeProj F)) (by
    rw [GHom.toCC_comp]
    ext i c
    obtain ⟨a, u, x⟩ := c
    exact changeCond_hfg F i u)

/-- **The change-of-condition sequence is short exact**: for a termwise injective morphism of
local conditions `Δ → Δ'`, `0 → C(Δ) → C(Δ') → ⊕_v U'_v / U_v → 0` is a short exact sequence of
cochain complexes, so `C(Δ)` is an actual subcomplex of `C(Δ')` with cokernel the singular
quotient (`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)).
PROVED. -/
theorem changeCondSES_shortExact (F : CondInclusion Δ Δ') : (changeCondSES F).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, u, x⟩ := c
    have hu : ∀ v, ∃ y, (F.φ v).f i i rfl y = u v := fun v =>
      (quotMk_eq_zero_iff (F.φ v) i (u v)).1 (congrFun hc v)
    choose y hy using hu
    exact ⟨(a, y, x), Prod.ext rfl (Prod.ext (funext hy) rfl)⟩
  · rw [ModuleCat.mono_iff_injective]
    intro c c' h
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    have h1 : a = a' := congrArg Prod.fst h
    have h2 : (piMap F.φ).f i i rfl u = (piMap F.φ).f i i rfl u' :=
      congrArg (fun c => c.2.1) h
    have h3 : x = x' := congrArg (fun c => c.2.2) h
    have hu : u = u' := funext fun v => F.inj v i (congrFun h2 v)
    rw [h1, hu, h3]
  · rw [ModuleCat.epi_iff_surjective]
    intro w
    have hw : ∀ v, ∃ y, (quotMk (F.φ v)).f i i rfl y = w v := fun v =>
      quotMk_surjective (F.φ v) i (w v)
    choose y hy using hw
    exact ⟨(0, y, 0), funext hy⟩

/-- **The long exact cohomology sequence of a change of local conditions** (Nekovář, *Selmer
complexes*, 6.1.3.2 for the triangle `C(Δ) → C(Δ') → ⊕_v U'_v / U_v →`; `diophantine_zq.tex`,
tex 3494–3498): exactness of `H^i(⊕ U'/U) → H^j(C(Δ)) → H^j(C(Δ'))` (`j = i + 1`), of
`H^i(C(Δ)) → H^i(C(Δ')) → H^i(⊕ U'/U)` and of `H^i(C(Δ')) → H^i(⊕ U'/U) → H^j(C(Δ))`. PROVED. -/
theorem changeCond_les (F : CondInclusion Δ Δ') (i j : ℤ) (hij : i + 1 = j) :
    (ShortComplex.mk _ _ ((changeCondSES_shortExact F).δ_comp i j hij)).Exact ∧
    (ShortComplex.mk (HomologicalComplex.homologyMap (changeCondSES F).f i)
      (HomologicalComplex.homologyMap (changeCondSES F).g i) (by
        rw [← HomologicalComplex.homologyMap_comp, (changeCondSES F).zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ ((changeCondSES_shortExact F).comp_δ i j hij)).Exact :=
  ⟨(changeCondSES_shortExact F).homology_exact₁ i j hij,
    (changeCondSES_shortExact F).homology_exact₂ i,
    (changeCondSES_shortExact F).homology_exact₃ i j hij⟩

/-! ### Comparison with the abstract change-of-condition node -/

omit [IsTopologicalGroup GS] in
/-- The local condition map of `restrictData (selData Δ') (piMap φ)` is that of `Δ`:
`i'_S ∘ φ = i_S` (`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.4.2(i)).
PROVED. -/
theorem restrict_ι_eq (F : CondInclusion Δ Δ') (i j : ℤ) (h : i = j) (u : (piCx Δ.U).X i) :
    (ghomComp (piMap F.φ) (piMap Δ'.i)).f i j h u = (piMap Δ.i).f i j h u := by
  subst h
  funext v
  exact F.compat v i (u v)

/-- The identity `C(Δ) → C(Δ)` from the restricted data `restrictData (selData Δ') (piMap φ)` of
the abstract node to the genuine Selmer complex of `Δ` (they differ only in the condition map,
which agrees pointwise by `restrict_ι_eq`; `diophantine_zq.tex`, tex 3494–3498). A chain map. -/
def restrictToSel (F : CondInclusion Δ Δ') :
    GHom (selCx (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData
        (selData k GS Gv loc M Δ') (piMap F.φ)))
      (selCx (selData k GS Gv loc M Δ)) where
  f i j h := by
    subst h
    exact LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext rfl ?_)
    exact congrArg (fun y => (resS k GS Gv loc M).f i (i₁ - 1) (by omega) a - y -
        (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) (by omega) x)
      (restrict_ι_eq F i (i₁ - 1) (by omega) u)

/-- The identity `C(Δ) → C(Δ)` from the genuine Selmer complex of `Δ` to the restricted data of
the abstract node (`diophantine_zq.tex`, tex 3494–3498). A chain map. -/
def selToRestrict (F : CondInclusion Δ Δ') :
    GHom (selCx (selData k GS Gv loc M Δ))
      (selCx (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData
        (selData k GS Gv loc M Δ') (piMap F.φ))) where
  f i j h := by
    subst h
    exact LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext rfl ?_)
    exact congrArg (fun y => (resS k GS Gv loc M).f i (i₁ - 1) (by omega) a - y -
        (localSumCx k GS Gv loc M).d (i - 1) (i₁ - 1) (by omega) x)
      (restrict_ι_eq F i (i₁ - 1) (by omega) u).symm

/-- **The restricted Selmer complex of the abstract node is the Selmer complex of `Δ`**: the
identity isomorphism `C(restrictData (selData Δ') φ) ≅ C(Δ)` (`diophantine_zq.tex`,
tex 3494–3498; Nekovář, *Selmer complexes*, 6.4.2(i)). PROVED. -/
def restrictIso (F : CondInclusion Δ Δ') :
    (selCx (ZInQ.Contrib.CloudB3RC53.SelmerDuality.restrictData
        (selData k GS Gv loc M Δ') (piMap F.φ))).toCC ≅
      (selCx (selData k GS Gv loc M Δ)).toCC where
  hom := GHom.toCC (restrictToSel F)
  inv := GHom.toCC (selToRestrict F)
  hom_inv_id := by
    ext i c
    rfl
  inv_hom_id := by
    ext i c
    rfl

/-- **The abstract change-of-condition node applies to the genuine data**: the abstract sequence
`changeSES (selData Δ') (piMap φ) (piMap quotMk)` is short exact, by `relaxedQuotientNode_proof`
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3). PROVED. -/
theorem changeSES_selData_shortExact (F : CondInclusion Δ Δ') :
    (changeSES (selData k GS Gv loc M Δ') (W := singQuot F) (piMap F.φ)
      (piMap fun v => quotMk (F.φ v)) (changeCond_hfg F)).ShortExact :=
  relaxedQuotientNode_proof k (selData k GS Gv loc M Δ') (piCx Δ.U) (singQuot F) (piMap F.φ)
    (piMap fun v => quotMk (F.φ v)) (changeCond_hfg F)
    (fun i _ _ h => funext fun v => F.inj v i (congrFun h v))
    (fun i w => by
      have hw : ∀ v, ∃ y, (quotMk (F.φ v)).f i i rfl y = w v := fun v =>
        quotMk_surjective (F.φ v) i (w v)
      choose y hy using hw
      exact ⟨y, funext hy⟩)
    (fun i u hu => by
      have hu' : ∀ v, ∃ y, (F.φ v).f i i rfl y = u v := fun v =>
        (quotMk_eq_zero_iff (F.φ v) i (u v)).1 (congrFun hu v)
      choose y hy using hu'
      exact ⟨y, funext hy⟩)

/-- **The abstract node's sequence is the change-of-condition sequence**: the isomorphism of
short complexes `changeSES (selData Δ') φ quotMk ≅ changeCondSES F` (identity of `C(Δ)` by
`restrictIso`, identities on `C(Δ')` and on the singular quotient; `diophantine_zq.tex`,
tex 3494–3498). PROVED. -/
def changeSESIso (F : CondInclusion Δ Δ') :
    changeSES (selData k GS Gv loc M Δ') (W := singQuot F) (piMap F.φ)
      (piMap fun v => quotMk (F.φ v)) (changeCond_hfg F) ≅ changeCondSES F :=
  ShortComplex.isoMk (restrictIso F) (Iso.refl _) (Iso.refl _)
    (by
      ext i c
      rfl)
    (by
      ext i c
      rfl)

/-- **Second proof of `changeCondSES_shortExact`**, through the abstract node
`relaxedQuotientNode_proof` and the isomorphism `changeSESIso` (`diophantine_zq.tex`,
tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)). PROVED. -/
theorem changeCondSES_shortExact' (F : CondInclusion Δ Δ') : (changeCondSES F).ShortExact :=
  ShortComplex.shortExact_of_iso (changeSESIso F) (changeSES_selData_shortExact F)

/-- **Non-vacuity / sanity check**: the change of condition from the strict conditions has the
shape of `strictSES_shortExact`, `0 → C_str → C(Δ) → ⊕_v U_v / 0 → 0` short exact (Nekovář,
*Selmer complexes*, 6.1.3; `diophantine_zq.tex`, tex 3494–3498). PROVED. -/
theorem changeCondSES_ofStrict_shortExact (Δ : LocalConditions k GS Gv loc M) :
    (changeCondSES (CondInclusion.ofStrict Δ)).ShortExact :=
  changeCondSES_shortExact _

/-- **Non-vacuity / sanity check**: the identity change of condition `Δ ⊆ Δ`,
`0 → C(Δ) → C(Δ) → 0 → 0`, is short exact (`diophantine_zq.tex`, tex 3494–3498; Nekovář,
*Selmer complexes*, 6.1.3). PROVED. -/
theorem changeCondSES_refl_shortExact (Δ : LocalConditions k GS Gv loc M) :
    (changeCondSES (CondInclusion.refl Δ)).ShortExact :=
  changeCondSES_shortExact _

/-- **Replacing a local condition by the full condition** (`diophantine_zq.tex`, tex 3494–3498):
for local conditions with injective `i_v`, `0 → C(Δ) → C_rel → ⊕_v C(G_v, M) / U_v → 0` is short
exact (Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)). PROVED. -/
theorem relaxedSES_shortExact (Δ : LocalConditions k GS Gv loc M)
    (hinj : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    (changeCondSES (CondInclusion.toRelaxed Δ hinj)).ShortExact :=
  changeCondSES_shortExact _

end Change

/-! ### The genuine Galois groups -/

section Galois

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type)
  [CommRing k] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- Termwise injective morphisms of genuine Galois local conditions at the places of `S`
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.4.2(i)). -/
abbrev GaloisCondInclusion (Δ Δ' : GaloisLocalConditions K S k M) :=
  CondInclusion Δ Δ'

/-- **The change-of-condition sequence for the genuine Galois Selmer complexes**
`0 → C_f(G_{K,S}, M; Δ) → C_f(G_{K,S}, M; Δ') → ⊕_{v∈S} U'_v / U_v → 0` (`diophantine_zq.tex`,
tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)). -/
abbrev galoisChangeCondSES {Δ Δ' : GaloisLocalConditions K S k M}
    (F : GaloisCondInclusion K S k M Δ Δ') : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  changeCondSES F

/-- **The Galois change-of-condition sequence is short exact** (`diophantine_zq.tex`,
tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)). PROVED. -/
theorem galoisChangeCondSES_shortExact {Δ Δ' : GaloisLocalConditions K S k M}
    (F : GaloisCondInclusion K S k M Δ Δ') : (galoisChangeCondSES K S k M F).ShortExact :=
  changeCondSES_shortExact F

/-- **Replacing a Galois local condition by the full condition** (`diophantine_zq.tex`,
tex 3494–3498): for injective `i_v : U_v → C^•_cont(G_{K_v}, M)`,
`0 → C_f(Δ) → C_f(rel) → ⊕_{v∈S} C^•_cont(G_{K_v}, M) / U_v → 0` is short exact (Nekovář,
*Selmer complexes*, 6.1.3 and 6.4.2(i)). PROVED. -/
theorem galoisRelaxedSES_shortExact (Δ : GaloisLocalConditions K S k M)
    (hinj : ∀ v (n : ℤ), Function.Injective ((Δ.i v).f n n rfl)) :
    (galoisChangeCondSES K S k M (CondInclusion.toRelaxed Δ hinj)).ShortExact :=
  changeCondSES_shortExact _

/-- **Non-vacuity of `GaloisCondInclusion`**: the strict conditions inside any genuine Galois
local conditions (`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3). -/
def galoisCondInclusion_ofStrict (Δ : GaloisLocalConditions K S k M) :
    GaloisCondInclusion K S k M (strictConditions k _ _ _ M) Δ :=
  CondInclusion.ofStrict Δ

end Galois

/-! ### The case of the text: the unramified condition inside the full condition -/

section UnramifiedGeneric

open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- **The unramified condition is termwise injective**: for an injective `G`-equivariant
`f : W → M` and a Frobenius in the image of `π : G → H`, every component of the cochain map
`[W --(Φ−1)--> W] → C^•_cont(G, M)` is injective (degree `0`: `x ↦` the constant cochain `f x`;
degree `1`: the inflated cocycle takes the value `f x` at a lift of the Frobenius; other degrees:
the source is zero). This makes the unramified condition a sub-condition of the full condition, as
needed for `diophantine_zq.tex`, tex 3494–3498 (Nekovář, *Selmer complexes*, 6.4.2(i)). PROVED. -/
theorem urToLocal_injective (hfinj : Function.Injective f) (hπ : ∃ g, π g = frobElt e) (n : ℤ) :
    Function.Injective ((urToLocal e π X f hf).f n).hom := by
  by_cases h0 : n = 0
  · subst h0
    rw [urToLocal_f₀]
    change Function.Injective ((urLin₀ (G := G) X f) ∘
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).hom.hom)
    refine Function.Injective.comp ?_ ((ModuleCat.mono_iff_injective _).1 inferInstance)
    intro x y hxy
    apply hfinj
    have h' := congrArg Subtype.val hxy
    exact congrFun h' Fin.elim0
  by_cases h1 : n = 1
  · subst h1
    rw [urToLocal_f₁]
    change Function.Injective ((urLin₁ e π X f) ∘
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob e X - 1)) rel01 (by decide)).hom.hom)
    refine Function.Injective.comp ?_ ((ModuleCat.mono_iff_injective _).1 inferInstance)
    obtain ⟨g, hg⟩ := hπ
    intro x y hxy
    have h' := congrFun (congrArg Subtype.val hxy) (fun _ => g)
    change f (urCocycle e X x (π g)) = f (urCocycle e X y (π g)) at h'
    rw [hg, urCocycle_frob, urCocycle_frob] at h'
    exact hfinj h'
  · have hz := HomologicalComplex.isZero_double_X (ModuleCat.ofHom (frob e X - 1)) rel01 n h0 h1
    intro x y _
    exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hz) x y

end UnramifiedGeneric

section GaloisUnramified

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The genuine unramified condition at `w ∈ S` is termwise injective** for an injective
equivariant `f : W → M` (the restriction `G_{K_w} → Gal(K_w^{ur}/K_w)` is surjective, so the
Frobenius lifts; `diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.4.2(i)).
PROVED. -/
theorem urToLocal_galois_injective (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hfinj : Function.Injective f) (n : ℤ) :
    Function.Injective ((urToLocal_galois K S w X f hf).f n).hom :=
  @urToLocal_injective k _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1) (resUr K w.1) X _ _ _
    (ResMod (locMap K S w.1) M) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance f hf hfinj (resUr_surjective K w.1 _) n

/-- **The unramified conditions inside the full conditions** (`diophantine_zq.tex`,
tex 3494–3498: "replacing the unramified condition by the full condition"): for unramified data
`f_w : W_w → M` with every `f_w` injective, the unramified local conditions
`[W_w --(Φ_w−1)--> W_w] → C^•_cont(G_{K_w}, M)` form a termwise injective morphism of local
conditions into the relaxed (full) conditions (Nekovář, *Selmer complexes*, 6.4.2(i)). -/
def unramifiedInRelaxed (X : ∀ w : Places K S, TopRep.{0} k (GUr K w.1))
    [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V]
    [∀ w, Finite (X w).V] (f : ∀ w, (X w).V →ₗ[k] M)
    (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x)
    (hfinj : ∀ w, Function.Injective (f w)) :
    GaloisCondInclusion K S k M (allUnramifiedLocalConditions K S X f hf)
      (relaxedConditions k _ _ _ M) :=
  CondInclusion.toRelaxed _ fun w n =>
    urToLocal_galois_injective K S w (X w) (f w) (hf w) (hfinj w) n

/-- **Replacing the unramified condition by the full condition gives the singular quotient**
(`diophantine_zq.tex`, tex 3494–3498): for unramified data with injective `f_w`, the sequence
`0 → C_f(G_{K,S}, M; ur) → C_f(G_{K,S}, M; rel) → ⊕_{w∈S} C^•_cont(G_{K_w}, M) / U^{ur}_w → 0` of
genuine Selmer complexes is short exact (Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)).
PROVED. -/
theorem unramifiedToRelaxed_shortExact (X : ∀ w : Places K S, TopRep.{0} k (GUr K w.1))
    [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V]
    [∀ w, Finite (X w).V] (f : ∀ w, (X w).V →ₗ[k] M)
    (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x)
    (hfinj : ∀ w, Function.Injective (f w)) :
    (galoisChangeCondSES K S k M (unramifiedInRelaxed K S X f hf hfinj)).ShortExact :=
  changeCondSES_shortExact _

/-- **The unramified conditions for the residual module `W = 𝔽₂²`** (trivial actions, `f = id`):
genuine Galois local conditions that are the unramified complex `[W --(Φ−1)--> W]` at every place
of `S` (as in `UnramifiedCondition.lean`; the singular quotient of `diophantine_zq.tex`,
tex 3494–3498, is taken with respect to these). -/
def unramifiedW2Conditions :
    GaloisLocalConditions K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2)) :=
  haveI := fun w : Places K S => continuousSMul_W2 K w.1
  allUnramifiedLocalConditions K S (fun w => W2 K w.1)
    (fun _ => (LinearMap.id : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)))
    (fun _ _ _ => rfl)

/-- **Non-vacuity of `unramifiedInRelaxed`**: for the residual module `W = 𝔽₂²` (trivial
actions, `f = id`) the unramified conditions lie in the full conditions at every place of `S`
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.4.2(i)). -/
def unramifiedInRelaxedW2 :
    GaloisCondInclusion K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2))
      (unramifiedW2Conditions K S)
      (relaxedConditions (ZMod 2) _ _ _ (TrivMod (GKS K S) (Fin 2 → ZMod 2))) :=
  haveI := fun w : Places K S => continuousSMul_W2 K w.1
  @unramifiedInRelaxed K _ _ S (ZMod 2) _ _ (TrivMod (GKS K S) (Fin 2 → ZMod 2)) inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun w => W2 K w.1) _ _ _
    (fun _ => (LinearMap.id : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)))
    (fun _ _ _ => rfl) (fun _ _ _ h => h)

/-- **Replacing the unramified condition by the full condition, for `W = 𝔽₂²`**: the sequence
`0 → C_f(ur) → C_f(rel) → ⊕_{w∈S} C^•_cont(G_{K_w}, 𝔽₂²) / [Φ_w − 1] → 0` is short exact
(`diophantine_zq.tex`, tex 3494–3498; Nekovář, *Selmer complexes*, 6.1.3 and 6.4.2(i)). PROVED. -/
theorem unramifiedToRelaxedW2_shortExact :
    (galoisChangeCondSES K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2))
      (unramifiedInRelaxedW2 K S)).ShortExact :=
  changeCondSES_shortExact _

end GaloisUnramified

end ZInQ.Manuscript.RC.SelmerComplex

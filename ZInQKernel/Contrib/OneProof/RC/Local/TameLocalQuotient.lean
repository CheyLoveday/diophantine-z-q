import ZInQKernel.Contrib.OneProof.RC.Local.TwoPlaceCaveat
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition

/-!
# Lane RC31, round 7: the local quotient retracts onto the singular block

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4) at augmentation: "the direct sum of the
unramified complex `[Φ − 1]` in degrees zero and one and the singular quotient `[Φ − q]` in
degrees one and two"), consumed at tex 4176–4184 (the two quotient blocks at the conjugate places
of an unused split prime) and 5317–5322.

For a split inclusion `E : U ⊂ L` (the unramified condition inside the genuine local complex,
with chosen complements; `SplitInclusion`), the quotient complex `E.quotientCx` (the cokernel of
the unramified condition, `quotientEquivCokernel`) is compared with the singular block of the
tame model:

* `quotMap E j π' c`: for a comparison `c : L → T_L` with a strict square `c ∘ ι = j ∘ u`
  (`u : U → T_U`), the induced map of quotients `E.quotientCx → S` (`S` the cokernel of
  `j : T_U → T_L`), a chain map;
* `quasiIso_quotMap` (PROVED, the five lemma for the homology sequence): if `u` and `c` are
  quasi-isomorphisms, so is `quotMap`;
* `quotMap_surjective` (PROVED): `quotMap` is surjective when `c` and `π'` are;
* `exists_retract_quotient_field` (PROVED): over a field, a retract of `E.quotientCx` onto `S`
  with projection `quotMap`;
* **`exists_retract_localQuotient`** (PROVED): for the genuine local complex at a tame place and
  the genuine unramified condition, every split inclusion `E` of the unramified condition (over a
  coefficient field) has a retract of its quotient onto the singular block `singCx Φ_X q`, with
  projection the comparison, given that `tameCochainMap` is a quasi-isomorphism and surjective;
* `GRetract.prod`, `singCx_basisEquiv`, **`exists_retract_twoPlaces`** (PROVED): at the two
  conjugate places `w`, `w̄`, with bases of the coefficients in which Frobenius is `z F` and
  `z⁻¹ F`, the sum of the two quotients retracts onto `twoSingCx F q z z⁻¹`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### The induced map of quotients -/

section Quotient

variable {k : Type} [CommRing k] {U L TU TL S : GCx k} (E : SplitInclusion U L)
  (j : GHom TU TL) (π' : GHom TL S)
  (hjπ : ∀ n (y : TU.X n), π'.f n n rfl (j.f n n rfl y) = 0)
  (c : GHom L TL) (u : GHom U TU)
  (hsq : ∀ n (y : U.X n), c.f n n rfl (E.i.f n n rfl y) = j.f n n rfl (u.f n n rfl y))

include hjπ hsq in
/-- The quotient differential through the comparison (tex 3478–3480). Kind: PROVED. -/
theorem quotMap_comm_aux (i : ℤ) (x : E.Qc i) :
    π'.f (i + 1) (i + 1) rfl (c.f (i + 1) (i + 1) rfl ((E.dQ i (i + 1) rfl x : E.Qc (i + 1)) :
        L.X (i + 1))) = S.d i (i + 1) rfl (π'.f i i rfl (c.f i i rfl (x : L.X i))) := by
  have e1 : ((E.dQ i (i + 1) rfl x : E.Qc (i + 1)) : L.X (i + 1)) =
      L.d i (i + 1) rfl (x : L.X i) - E.i.f (i + 1) (i + 1) rfl (E.offDiag i (i + 1) rfl x) := by
    rw [E.d_Q i (i + 1) rfl x]
    abel
  rw [e1, map_sub, map_sub, hsq, hjπ, sub_zero, c.comm i (i + 1) i (i + 1) rfl rfl rfl rfl,
    π'.comm i (i + 1) i (i + 1) rfl rfl rfl rfl]

/-- **The induced map of quotients** `E.quotientCx → S`, `x ↦ π'(c x)` on the complement of the
unramified condition (tex 3478–3480). Kind: definition (PROVED chain property). -/
def quotMap : GHom E.quotientCx S where
  f a b h := by
    subst h
    exact π'.f a a rfl ∘ₗ c.f a a rfl ∘ₗ (E.Qc a).subtype
  comm := by
    rintro i _ j' _ rfl rfl h rfl x
    exact quotMap_comm_aux E j π' hjπ c u hsq i x

omit [CommRing k] in
/-- The components of `quotMap`. Kind: PROVED (definitional). -/
theorem quotMap_f {k : Type} [CommRing k] {U L TU TL S : GCx k} (E : SplitInclusion U L)
    (j : GHom TU TL) (π' : GHom TL S)
    (hjπ : ∀ n (y : TU.X n), π'.f n n rfl (j.f n n rfl y) = 0)
    (c : GHom L TL) (u : GHom U TU)
    (hsq : ∀ n (y : U.X n), c.f n n rfl (E.i.f n n rfl y) = j.f n n rfl (u.f n n rfl y))
    (n : ℤ) (x : E.Qc n) :
    (quotMap E j π' hjπ c u hsq).f n n rfl x = π'.f n n rfl (c.f n n rfl (x : L.X n)) :=
  rfl

include hjπ hsq in
/-- `π' ∘ c` kills the unramified condition (tex 3478–3480). Kind: PROVED. -/
theorem quot_kills (n : ℤ) (y : U.X n) : π'.f n n rfl (c.f n n rfl (E.i.f n n rfl y)) = 0 := by
  rw [hsq, hjπ]

include hjπ hsq in
/-- `π' ∘ c` factors through the projection onto the complement (tex 3478–3480). Kind:
PROVED. -/
theorem quot_factor (n : ℤ) (x : L.X n) :
    π'.f n n rfl (c.f n n rfl x) =
      π'.f n n rfl (c.f n n rfl ((E.coordQ n x : E.Qc n) : L.X n)) := by
  conv_lhs => rw [← E.decompose n x]
  rw [map_add, map_add, quot_kills E j π' hjπ c u hsq, zero_add]

include hjπ hsq in
/-- **`quotMap` is surjective when `c` and `π'` are** (tex 3478–3480). Kind: PROVED. -/
theorem quotMap_surjective (hc : ∀ n, Function.Surjective (c.f n n rfl))
    (hπ : ∀ n, Function.Surjective (π'.f n n rfl)) (n : ℤ) :
    Function.Surjective ((quotMap E j π' hjπ c u hsq).f n n rfl) := by
  intro s
  obtain ⟨t, rfl⟩ := hπ n s
  obtain ⟨x, rfl⟩ := hc n t
  exact ⟨E.coordQ n x, (quot_factor E j π' hjπ c u hsq n x).symm⟩

/-- The short complex of complexes `U → L → E.quotientCx` (tex 3478–3480). Kind:
definition. -/
def quotSC₁ : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  ShortComplex.mk (GHom.toCC E.i) (GHom.toCC E.toQuotient) (by
    ext n x
    exact E.coordQ_i n x)

/-- The short complex of complexes `T_U → T_L → S` (tex 3478–3480). Kind: definition. -/
def quotSC₂ : ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  ShortComplex.mk (GHom.toCC j) (GHom.toCC π') (by
    ext n x
    exact hjπ n x)

/-- The split inclusion gives a short exact sequence of complexes (tex 5398–5403). Kind:
PROVED. -/
theorem quotSC₁_shortExact : (quotSC₁ E).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨E.coordP n x, ?_⟩
    have h0 : ((E.coordQ n x : E.Qc n) : L.X n) = 0 := congrArg Subtype.val hx
    have h := E.decompose n x
    rw [h0, add_zero] at h
    exact h
  · exact (ModuleCat.mono_iff_injective _).2 (E.inj n)
  · exact (ModuleCat.epi_iff_surjective _).2
      (fun q => ⟨((show E.Qc n from q) : L.X n), E.coordQ_Q n (show E.Qc n from q)⟩)

/-- A degreewise short exact model sequence (tex 3478–3480). Kind: PROVED. -/
theorem quotSC₂_shortExact (hj : ∀ n, Function.Injective (j.f n n rfl))
    (hπ : ∀ n, Function.Surjective (π'.f n n rfl))
    (hex : ∀ n (x : TL.X n), π'.f n n rfl x = 0 → ∃ y, j.f n n rfl y = x) :
    (quotSC₂ j π' hjπ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    exact hex n
  · exact (ModuleCat.mono_iff_injective _).2 (hj n)
  · exact (ModuleCat.epi_iff_surjective _).2 (hπ n)

/-- The morphism of the two short complexes (tex 3478–3480). Kind: definition. -/
def quotSCMap : quotSC₁ E ⟶ quotSC₂ j π' hjπ where
  τ₁ := GHom.toCC u
  τ₂ := GHom.toCC c
  τ₃ := GHom.toCC (quotMap E j π' hjπ c u hsq)
  comm₁₂ := by
    ext n y
    exact (hsq n y).symm
  comm₂₃ := by
    ext n x
    exact quot_factor E j π' hjπ c u hsq n x

/-- **The induced map of quotients is a quasi-isomorphism** (tex 3478–3480; the five lemma for
the homology sequences): if `u` and `c` are quasi-isomorphisms and the model sequence is
degreewise short exact, `quotMap` is a quasi-isomorphism. Kind: PROVED. -/
theorem quasiIso_quotMap (hj : ∀ n, Function.Injective (j.f n n rfl))
    (hπ : ∀ n, Function.Surjective (π'.f n n rfl))
    (hex : ∀ n (x : TL.X n), π'.f n n rfl x = 0 → ∃ y, j.f n n rfl y = x)
    (hu : QuasiIso (GHom.toCC u)) (hc : QuasiIso (GHom.toCC c)) :
    QuasiIso (GHom.toCC (quotMap E j π' hjπ c u hsq)) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (quotSCMap E j π' hjπ c u hsq)
    (quotSC₁_shortExact E) (quotSC₂_shortExact j π' hjπ hj hπ hex) hu hc

end Quotient

/-! ### Over a field: the retract of the quotient -/

section QuotientField

variable {k : Type} [Field k] {U L TU TL S : GCx k} (E : SplitInclusion U L)
  (j : GHom TU TL) (π' : GHom TL S)
  (hjπ : ∀ n (y : TU.X n), π'.f n n rfl (j.f n n rfl y) = 0)
  (c : GHom L TL) (u : GHom U TU)
  (hsq : ∀ n (y : U.X n), c.f n n rfl (E.i.f n n rfl y) = j.f n n rfl (u.f n n rfl y))

/-- The quotient of a complex vanishing in negative degrees vanishes in negative degrees
(tex 5398–5403). Kind: PROVED. -/
theorem quotientCx_isStrictlyGE (hL : ∀ n : ℤ, n < 0 → Subsingleton (L.X n)) :
    E.quotientCx.toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have := hL n hn
  have : Subsingleton (E.Qc n) := inferInstance
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k (E.Qc n))

/-- **A retract of the quotient onto the cokernel of the model, over a field**
(tex 3478–3480, 4423–4437): if `u` and `c` are quasi-isomorphisms, `c` and `π'` surjective, the
model sequence degreewise short exact and all complexes vanish in negative degrees, the quotient
complex retracts onto `S` with projection `quotMap`. Kind: PROVED. -/
theorem exists_retract_quotient_field (hL : ∀ n : ℤ, n < 0 → Subsingleton (L.X n))
    [S.toCC.IsStrictlyGE 0] (hj : ∀ n, Function.Injective (j.f n n rfl))
    (hπ : ∀ n, Function.Surjective (π'.f n n rfl))
    (hex : ∀ n (x : TL.X n), π'.f n n rfl x = 0 → ∃ y, j.f n n rfl y = x)
    (hu : QuasiIso (GHom.toCC u)) (hc : QuasiIso (GHom.toCC c))
    (hcs : ∀ n, Function.Surjective (c.f n n rfl)) :
    ∃ R : GRetract E.quotientCx S, ∀ n x,
      R.p.f n n rfl x = (quotMap E j π' hjπ c u hsq).f n n rfl x := by
  have := quotientCx_isStrictlyGE E hL
  have := quasiIso_quotMap E j π' hjπ c u hsq hj hπ hex hu hc
  exact exists_retract_of_surjective_quasiIso_field 0 _
    (quotMap_surjective E j π' hjπ c u hsq hcs hπ)

end QuotientField

/-! ### The tame model sequence at augmentation -/

section ModelSequence

variable {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M] (Φ : M →ₗ[k] M)
  (q : ℕ) (hq : Odd q)

/-- `π ∘ ι = 0` for the unramified summand and the singular block (tex 3478–3480). Kind:
PROVED. -/
theorem singProj_unrIncl (n : ℤ) (y : (unrCx Φ).X n) :
    (singProj Φ q hq).f n n rfl ((unrIncl Φ q hq).f n n rfl y) = 0 := by
  rcases n with (_ | _ | _ | n) | n
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The inclusion of the unramified summand is injective in every degree (tex 3478–3480).
Kind: PROVED. -/
theorem unrIncl_injective (n : ℤ) : Function.Injective ((unrIncl Φ q hq).f n n rfl) := by
  rcases n with (_ | _ | _ | n) | n
  · exact fun x y h => h
  · exact (tame_split_exact_one Φ q hq).1
  · exact fun _ _ _ => Subsingleton.elim (α := PUnit) _ _
  · exact fun _ _ _ => Subsingleton.elim (α := PUnit) _ _
  · exact fun _ _ _ => Subsingleton.elim (α := PUnit) _ _

/-- The projection onto the singular block is surjective in every degree (tex 3478–3480).
Kind: PROVED. -/
theorem singProj_surjective (n : ℤ) : Function.Surjective ((singProj Φ q hq).f n n rfl) := by
  rcases n with (_ | _ | _ | n) | n
  · exact fun _ => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  · exact (tame_split_exact_one Φ q hq).2.1
  · exact fun w => ⟨w, rfl⟩
  · exact fun _ => ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩
  · exact fun _ => ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩

/-- Exactness of the tame model sequence in every degree (tex 3478–3480). Kind: PROVED. -/
theorem singProj_exact (n : ℤ) (x : (tameFreeModel1 Φ q hq).X n)
    (hx : (singProj Φ q hq).f n n rfl x = 0) : ∃ y, (unrIncl Φ q hq).f n n rfl y = x := by
  rcases n with (_ | _ | _ | n) | n
  · exact ⟨x, rfl⟩
  · exact ((tame_split_exact_one Φ q hq).2.2 x).1 hx
  · refine ⟨PUnit.unit, ?_⟩
    have hx' : (x : M) = 0 := hx
    exact hx'.symm
  · exact ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩
  · exact ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩

/-- The singular block vanishes in negative degrees (tex 3478–3480). Kind: PROVED. -/
theorem singCx_isStrictlyGE : (singCx Φ q).toCC.IsStrictlyGE 0 :=
  cx3_toCC_isStrictlyGE (0 : PUnit →ₗ[k] M) (frobQ Φ q) (fun _ => by simp)

end ModelSequence

/-! ### The genuine local quotient at a tame place -/

/-- The extension by zero of an `ℕ`-indexed complex vanishes in negative degrees
(tex 3455–3463). Kind: PROVED. -/
theorem natCx_neg_subsingleton {k : Type} [CommRing k] (K : CochainComplex (ModuleCat.{0} k) ℕ)
    (n : ℤ) (hn : n < 0) : Subsingleton ((natCx K).X n) := by
  rcases n with n | m
  · rw [Int.ofNat_eq_natCast] at hn
    omega
  · exact inferInstanceAs (Subsingleton PUnit)

section Genuine

/-- The relation-indexed form of a Mathlib cochain map, read back (tex 3478–3481). Kind:
PROVED. -/
theorem toCC_ofCCHom {k : Type} [CommRing k] {C : CochainComplex (ModuleCat.{0} k) ℤ} {B : GCx k}
    (g : C ⟶ B.toCC) : GHom.toCC (ofCCHom g) = (ofCCToCCIso C).hom ≫ g := by
  ext n x
  rfl

/-- The model map along a linear equivalence is surjective in every degree (tex 3470–3480).
Kind: PROVED. -/
theorem unrModelMap_surjective {k : Type} [CommRing k] {M V : Type} [AddCommGroup M] [Module k M]
    [AddCommGroup V] [Module k V] (ΦM : M →ₗ[k] M) (ΦV : V →ₗ[k] V) (q : ℕ) (hq : Odd q)
    (f : V ≃ₗ[k] M) (hfΦ : ∀ v, f (ΦV v) = ΦM (f v)) (n : ℤ) :
    Function.Surjective ((unrModelMap ΦM ΦV q hq f hfΦ).f n n rfl) := by
  rcases n with (_ | _ | _ | n) | n
  · exact f.symm.surjective
  · exact (LinearEquiv.prodCongr f.symm f.symm).surjective
  · exact f.symm.surjective
  · exact fun _ => ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩
  · exact fun _ => ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- **The comparison of the genuine local complex with the tame model over `X`**, as a
relation-indexed chain map: `tameCochainMap` followed by the model map along `f⁻¹`
(tex 3470–3480). Kind: definition. -/
def unrLG (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    GHom (natCx (contCochains k G M)) (tameFreeModel1 (frob e X) q hq) :=
  ghomComp (tameCochainMap Φ LinearMap.id φ σ q hq hΦ (smul_eq_of_res_one π X f hbij hf σ hσ)
      id_invol (comm_id Φ) hrel)
    (unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ))

/-- **The induced comparison of the local quotient with the singular block**: for a split
inclusion `E` of the genuine unramified condition into the genuine local complex, the map
`E.quotientCx → singCx Φ_X q`, `x ↦ π(c x)` (tex 3478–3480). Kind: definition. -/
def localQuotMap (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (E : SplitInclusion (ofCC (frobCx (frob e X))) (natCx (contCochains k G M)))
    (hE : E.i = ofCCHom (urToLocal e π X f hf)) :
    GHom E.quotientCx (singCx (frob e X) q) :=
  quotMap E (unrIncl (frob e X) q hq) (singProj (frob e X) q hq)
    (singProj_unrIncl (frob e X) q hq) (unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel)
    (ofCCHom (frobToUnr (frob e X))) (by
      intro n y
      rw [hE]
      exact congrArg (fun χ => ModuleCat.Hom.hom (χ.f n) y)
        (unr_square e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel))

/-- The components of the local quotient map (tex 3478–3480). Kind: PROVED (definitional). -/
theorem localQuotMap_f (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (E : SplitInclusion (ofCC (frobCx (frob e X))) (natCx (contCochains k G M)))
    (hE : E.i = ofCCHom (urToLocal e π X f hf)) (n : ℤ) (x : E.Qc n) :
    (localQuotMap e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE).f n n rfl x =
      (singProj (frob e X) q hq).f n n rfl
        ((unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel).f n n rfl (x : _)) :=
  rfl

omit [IsTopologicalGroup H] [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V] in
/-- The unramified identification is a quasi-isomorphism (tex 3478–3481). Kind: PROVED. -/
theorem quasiIso_toCC_frobToUnr :
    QuasiIso (GHom.toCC (ofCCHom (frobToUnr (frob e X)))) := by
  rw [toCC_ofCCHom]
  have : IsIso (frobToUnr (frob e X)) := isIso_frobToUnr _
  have : IsIso (ofCCToCCIso (frobCx (frob e X))).hom := (ofCCToCCIso _).isIso_hom
  exact quasiIso_of_isIso _

omit [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V] in
/-- The comparison is a quasi-isomorphism when `tameCochainMap` is (tex 3470–3480). Kind:
PROVED. -/
theorem quasiIso_unrLG (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel))) :
    QuasiIso (GHom.toCC (unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel)) := by
  have hM : QuasiIso (GHom.toCC (unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ))) := by
    have := isIso_toCC_unrModelMap Φ (frob e X) q hq (LinearEquiv.ofBijective f hbij)
      (frob_intertwine e π X f hf Φ φ hΦ hφ)
    exact quasiIso_of_isIso _
  unfold unrLG
  rw [← GHom.toCC_comp]
  exact quasiIso_comp _ _

end Genuine

section GenuineField

variable {k : Type} [Field k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- **The local quotient retracts onto the singular block, over a field** (tex 3470–3480,
4423–4437): at a tame place (`π φ = Frob`, `π σ = 1`, `φ σ φ⁻¹ = σ^q`), for every split
inclusion `E` of the genuine unramified condition into the genuine local complex, if
`tameCochainMap` is a quasi-isomorphism and surjective in every degree, the quotient complex
`E.quotientCx` retracts onto the singular block `singCx Φ_X q = [X --Φ−q--> X]` (degrees one and
two), with projection the induced comparison `localQuotMap`. Kind: PROVED. -/
theorem exists_retract_localQuotient (hφ : π φ = frobElt e) (hσ : π σ = 1)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (E : SplitInclusion (ofCC (frobCx (frob e X))) (natCx (contCochains k G M)))
    (hE : E.i = ofCCHom (urToLocal e π X f hf))
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel)))
    (hsurj : ∀ n, Function.Surjective ((tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel).f n n rfl)) :
    ∃ R : GRetract E.quotientCx (singCx (frob e X) q), ∀ n x,
      R.p.f n n rfl x =
        (localQuotMap e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE).f n n rfl x := by
  have : (singCx (frob e X) q).toCC.IsStrictlyGE 0 := singCx_isStrictlyGE _ q
  exact exists_retract_quotient_field E _ _ _ _ _ _ (natCx_neg_subsingleton _)
    (unrIncl_injective _ q hq) (singProj_surjective _ q hq) (singProj_exact _ q hq)
    (quasiIso_toCC_frobToUnr e X) (quasiIso_unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel hQ)
    (fun n => (unrModelMap_surjective _ _ q hq _ _ n).comp (hsurj n))

end GenuineField

/-! ### Two places -/

section TwoPlaces

variable {A : Type} [CommRing A]

/-- **The sum of two retracts** (tex 4176–4184): retracts `X₁ → Y₁` and `X₂ → Y₂` give a retract
`X₁ ⊕ X₂ → Y₁ ⊕ Y₂`, componentwise. Kind: definition (PROVED identities). -/
def GRetract.prod {X₁ Y₁ X₂ Y₂ : GCx A} (R₁ : GRetract X₁ Y₁) (R₂ : GRetract X₂ Y₂) :
    GRetract (prodGCx X₁ X₂) (prodGCx Y₁ Y₂) where
  i :=
    { f := fun a b h => (R₁.i.f a b h).prodMap (R₂.i.f a b h)
      comm := fun i i₁ j j₁ hij h₁ h₂ hj x =>
        Prod.ext (R₁.i.comm i i₁ j j₁ hij h₁ h₂ hj x.1) (R₂.i.comm i i₁ j j₁ hij h₁ h₂ hj x.2) }
  p :=
    { f := fun a b h => (R₁.p.f a b h).prodMap (R₂.p.f a b h)
      comm := fun i i₁ j j₁ hij h₁ h₂ hj x =>
        Prod.ext (R₁.p.comm i i₁ j j₁ hij h₁ h₂ hj x.1) (R₂.p.comm i i₁ j j₁ hij h₁ h₂ hj x.2) }
  h a b hab := (R₁.h a b hab).prodMap (R₂.h a b hab)
  p_i n y := Prod.ext (R₁.p_i n y.1) (R₂.p_i n y.2)
  homotopy n x := Prod.ext (R₁.homotopy n x.1) (R₂.homotopy n x.2)
  h_h a b c hab hbc x := Prod.ext (R₁.h_h a b c hab hbc x.1) (R₂.h_h a b c hab hbc x.2)
  h_i a b hab y := Prod.ext (R₁.h_i a b hab y.1) (R₂.h_i a b hab y.2)
  p_h a b hab x := Prod.ext (R₁.p_h a b hab x.1) (R₂.p_h a b hab x.2)

/-- The projection of the sum of two retracts (tex 4176–4184). Kind: PROVED (definitional). -/
theorem GRetract.prod_p {X₁ Y₁ X₂ Y₂ : GCx A} (R₁ : GRetract X₁ Y₁) (R₂ : GRetract X₂ Y₂)
    (n : ℤ) (x : X₁.X n) (y : X₂.X n) :
    (GRetract.prod R₁ R₂).p.f n n rfl ((x, y) : X₁.X n × X₂.X n) =
      (R₁.p.f n n rfl x, R₂.p.f n n rfl y) :=
  rfl

variable {V W : Type} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]

/-- The degreewise equivalence of two block complexes given by `b` in degrees one and two
(tex 3478–3480). Kind: definition. -/
def blockEquivHet (b : V ≃ₗ[A] W) :
    ∀ n : ℤ, cx3X (A := A) PUnit V V n ≃ₗ[A] cx3X (A := A) PUnit W W n
  | .ofNat 0 => LinearEquiv.refl A PUnit
  | .ofNat 1 => b
  | .ofNat 2 => b
  | .ofNat (_ + 3) => LinearEquiv.refl A PUnit
  | .negSucc _ => LinearEquiv.refl A PUnit

/-- **A change of coordinates of a singular block** (tex 3478–3480): if `b` intertwines `Ψ` with
`Ψ'`, then `b` in degrees one and two is an equivalence `singCx Ψ q ≅ singCx Ψ' q`. Kind:
PROVED. -/
theorem blockEquivHet_comm (Ψ : V →ₗ[A] V) (Ψ' : W →ₗ[A] W) (q : ℕ) (b : V ≃ₗ[A] W)
    (hb : ∀ v, b (Ψ v) = Ψ' (b v)) (a c : ℤ) (h : a + 1 = c) (y : (singCx Ψ q).X a) :
    (singCx Ψ' q).d a c h (blockEquivHet b a y) = blockEquivHet b c ((singCx Ψ q).d a c h y) := by
  by_cases h0 : a = 0
  · subst h0
    obtain rfl : c = 1 := by omega
    change (0 : W) = b 0
    rw [map_zero]
  · by_cases h1 : a = 1
    · subst h1
      obtain rfl : c = 2 := by omega
      change Ψ' (b (show V from y)) - (q : A) • b (show V from y) =
        b (Ψ (show V from y) - (q : A) • (show V from y))
      rw [map_sub, map_smul, hb]
    · have z1 : cx3D (0 : PUnit →ₗ[A] W) (frobQ Ψ' q) a c h = 0 := cx3D_eq_zero _ _ a c h h0 h1
      have z2 : cx3D (0 : PUnit →ₗ[A] V) (frobQ Ψ q) a c h = 0 := cx3D_eq_zero _ _ a c h h0 h1
      change cx3D (0 : PUnit →ₗ[A] W) (frobQ Ψ' q) a c h (blockEquivHet b a y) =
        blockEquivHet b c (cx3D (0 : PUnit →ₗ[A] V) (frobQ Ψ q) a c h y)
      rw [z1, z2]
      exact (map_zero (blockEquivHet b c)).symm

/-- **A retract onto a singular block in coordinates** (tex 3478–3480, 4176–4184): a retract
onto `singCx Ψ q` and a basis `b : V ≃ A²` in which `Ψ` has the matrix `N` give a retract onto
`singCx (toLin' N) q`. Kind: definition. -/
def GRetract.toCoords {X : GCx A} (Ψ : V →ₗ[A] V) (N : Matrix (Fin 2) (Fin 2) A) (q : ℕ)
    (b : V ≃ₗ[A] (Fin 2 → A)) (hb : ∀ v, b (Ψ v) = Matrix.toLin' N (b v))
    (R : GRetract X (singCx Ψ q)) : GRetract X (singCx (Matrix.toLin' N) q) :=
  GRetract.ofEquivTarget R (blockEquivHet b) (blockEquivHet_comm Ψ (Matrix.toLin' N) q b hb)

/-- **The two quotients retract onto the two singular blocks** (tex 4176–4184): retracts of the
local quotients `Q₁`, `Q₂` at the conjugate places `w`, `w̄` onto `singCx Ψ₁ q`, `singCx Ψ₂ q`,
and bases in which `Ψ₁ = z F`, `Ψ₂ = z⁻¹ F` give a retract of `Q₁ ⊕ Q₂` onto
`twoSingCx F q z z⁻¹`, whose differential is `twoPlaceBlock F q z z⁻¹` in the coordinates of the
two places (`twoSing_matrix`). Kind: definition. -/
def GRetract.twoPlaces {Q₁ Q₂ : GCx A} {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] (Ψ₁ : V₁ →ₗ[A] V₁) (Ψ₂ : V₂ →ₗ[A] V₂)
    (F : Matrix (Fin 2) (Fin 2) A) (q : ℕ) (z zi : A) (b₁ : V₁ ≃ₗ[A] (Fin 2 → A))
    (hb₁ : ∀ v, b₁ (Ψ₁ v) = Matrix.toLin' (z • F) (b₁ v)) (b₂ : V₂ ≃ₗ[A] (Fin 2 → A))
    (hb₂ : ∀ v, b₂ (Ψ₂ v) = Matrix.toLin' (zi • F) (b₂ v))
    (R₁ : GRetract Q₁ (singCx Ψ₁ q)) (R₂ : GRetract Q₂ (singCx Ψ₂ q)) :
    GRetract (prodGCx Q₁ Q₂) (twoSingCx F q z zi) :=
  GRetract.prod (GRetract.toCoords Ψ₁ (z • F) q b₁ hb₁ R₁)
    (GRetract.toCoords Ψ₂ (zi • F) q b₂ hb₂ R₂)

end TwoPlaces

end ZInQ.Manuscript.RC.Local

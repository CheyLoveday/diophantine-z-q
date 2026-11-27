import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.SelmerPairing

/-!
# Selmer duality, part 1: dual complexes, adjoints of pairings, and the five lemma

Generic tools for the finite Selmer duality of Lemma `ex:arith-conjugate-duality`
(`diophantine_zq.tex`, tex L2806–2830), over the relation-indexed complexes `GCx` of
`PairedFunctional/SelmerPairing.lean`.

* `dualCx A m`: the complex `Hom_S(A, S)[−m]`, `X n = Hom_S(A^{m−n}, S)`, with differential
  `d φ = −(−1)^n φ ∘ d_A`. For a complex `A` of `S`-modules with `S` self-injective (as are the
  finite Frobenius coefficient rings `A_i`, `A_i[G]`), or with `A` bounded with finite projective
  terms, this is `RHom_S(A, S)[−m]`.
* `adjHom P m tr`: the adjoint `A → Hom_S(B, S)[−m]`, `x ↦ (y ↦ tr(x ∪ y))`, of a pairing of
  complexes `P : A × B → T` and a trace `tr : T^m → S` killing coboundaries; it is a chain map
  (`GHom`) by the Leibniz rule.
* `GHom.toCC`: a `GHom` as a morphism of Mathlib cochain complexes.
* `quasiIso_τ₂`: for a morphism of short exact sequences of cochain complexes in an abelian
  category, if the outer components are quasi-isomorphisms so is the middle one (Mathlib proves
  the `τ₃` case; this is the `τ₂` case, by the same four-lemma argument on the long exact
  homology sequences).

**Classification.** GLUE, PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

variable {S : Type u} [CommRing S]

/-! ### The dual complex -/

/-- The dual complex `Hom_S(A, S)[−m]`: `X n = Hom_S(A^{m−n}, S)`,
`d φ = −(−1)^n φ ∘ d_A`. -/
def dualCx (A : GCx S) (m : ℤ) : GCx S where
  X n := ModuleCat.of S (Module.Dual S (A.X (m - n)))
  d i j h := (-(sgn i)) • (A.d (m - j) (m - i) (by omega)).dualMap
  d_d i j k hij hjk φ := by
    refine LinearMap.ext fun x => ?_
    change (-(sgn j)) • ((-(sgn i)) • (show Module.Dual S (A.X (m - i)) from φ)
      (A.d (m - j) (m - i) _ (A.d (m - k) (m - j) _ x))) = 0
    rw [A.d_d, map_zero, smul_zero, smul_zero]

/-- Read an element of `(dualCx A m).X n` as a linear form. -/
def asDual {A : GCx S} {m n : ℤ} (φ : (dualCx A m).X n) : Module.Dual S (A.X (m - n)) := φ

theorem dualCx_ext {A : GCx S} {m n : ℤ} {φ ψ : (dualCx A m).X n}
    (h : ∀ x, asDual φ x = asDual ψ x) : φ = ψ :=
  LinearMap.ext h

theorem dualCx_d_apply (A : GCx S) (m i j : ℤ) (h : i + 1 = j) (φ : (dualCx A m).X i)
    (x : A.X (m - j)) :
    asDual ((dualCx A m).d i j h φ) x = (-(sgn i)) • asDual φ (A.d (m - j) (m - i) (by omega) x) :=
  rfl

/-- The dual of a chain map, `Hom(B, S)[−m] → Hom(A, S)[−m]`. -/
def dualHom {A B : GCx S} (f : GHom A B) (m : ℤ) : GHom (dualCx B m) (dualCx A m) where
  f i j h := (f.f (m - j) (m - i) (by omega)).dualMap
  comm i i₁ j j₁ hij h₁ h₂ hj φ := by
    refine dualCx_ext fun x => ?_
    subst hij hj
    change (-(sgn i)) • asDual φ (B.d (m - i₁) (m - i) _ (f.f (m - i₁) (m - i₁) _ x)) =
      (-(sgn i)) • asDual φ (f.f (m - i) (m - i) _ (A.d (m - i₁) (m - i) _ x))
    rw [f.comm (m - i₁) (m - i) (m - i₁) (m - i) rfl (by omega) (by omega) rfl x]

/-! ### Adjoints of pairings -/

/-- The adjoint `A → Hom_S(B, S)[−m]`, `x ↦ (y ↦ tr(x ∪ y))`. -/
def adjFun {A B T : GCx S} (P : GPair A B T) (m : ℤ) (tr : T.X m →ₗ[S] S) (i j : ℤ) (h : i = j) :
    A.X i →ₗ[S] (dualCx B m).X j :=
  (P.P i (m - j) m (by omega)).compr₂ tr

/-- **The adjoint of a pairing is a chain map** `A → Hom_S(B, S)[−m]` when the trace kills
coboundaries. -/
def adjHom {A B T : GCx S} (P : GPair A B T) (m : ℤ) (tr : T.X m →ₗ[S] S)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0) : GHom A (dualCx B m) where
  f := adjFun P m tr
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    refine dualCx_ext fun y => ?_
    subst hij
    have hl := P.leib i i₁ (m - j₁) (m - i) (m - 1) m (by omega) h₁ (by omega) (by omega) x y
    have h0 := htr (P.P i (m - j₁) (m - 1) (by omega) x y)
    rw [hl, map_add, map_zsmul] at h0
    change tr (P.P i₁ (m - j₁) m _ (A.d i i₁ h₁ x) y) =
      (-(sgn i)) • tr (P.P i (m - i) m _ x (B.d (m - j₁) (m - i) _ y))
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h0

/-! ### Mathlib bridge for chain maps -/

/-- A `GHom` as a morphism of Mathlib cochain complexes. -/
def GHom.toCC {A B : GCx S} (f : GHom A B) : A.toCC ⟶ B.toCC where
  f n := ModuleCat.ofHom (f.f n n rfl)
  comm' i j hij := by
    have h : i + 1 = j := hij
    ext x
    change (B.toCC.d i j).hom (f.f i i rfl x) = f.f j j rfl ((A.toCC.d i j).hom x)
    rw [GCx.toCC_d_hom _ _ _ h]
    erw [GCx.toCC_d_hom _ _ _ h]
    exact (f.comm i j i j rfl h h rfl x).symm

theorem GHom.toCC_f_apply {A B : GCx S} (f : GHom A B) (n : ℤ) (x : A.X n) :
    ((GHom.toCC f).f n).hom x = f.f n n rfl x :=
  rfl

/-! ### The five lemma for the middle term -/

open HomologicalComplex HomologySequence ComposableArrows Abelian in
/-- **Two-out-of-three for the middle term**: for a morphism `φ` of short exact sequences of
cochain complexes in an abelian category, if `φ.τ₁` and `φ.τ₃` are quasi-isomorphisms, so is
`φ.τ₂`. -/
theorem quasiIso_τ₂ {C : Type*} [Category C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have i₁ : ∀ n, IsIso (homologyMap φ.τ₁ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have i₃ : ∀ n, IsIso (homologyMap φ.τ₃ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hrel : ∀ k : ℤ, (ComplexShape.up ℤ).Rel (k - 1) k := fun k => by simp
  have hrel' : ∀ k : ℤ, (ComplexShape.up ℤ).Rel k (k + 1) := fun k => by simp
  have hm : Mono (homologyMap φ.τ₂ n) := by
    have := i₃ (n - 1)
    have := i₁ n
    have := i₃ n
    exact mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ (n - 1) n (hrel n)))
      (composableArrows₅_exact hS₁ (n - 1) n (hrel n)).δ₀.δ₀
      (composableArrows₅_exact hS₂ (n - 1) n (hrel n)).δ₀.δ₀
      (inferInstanceAs (Epi (homologyMap φ.τ₃ (n - 1))))
      (inferInstanceAs (Mono (homologyMap φ.τ₁ n)))
      (inferInstanceAs (Mono (homologyMap φ.τ₃ n)))
  have he : Epi (homologyMap φ.τ₂ n) := by
    have := i₁ n
    have := i₃ n
    have := i₁ (n + 1)
    exact epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ n (n + 1) (hrel' n)))
      (composableArrows₅_exact hS₁ n (n + 1) (hrel' n)).δlast.δlast
      (composableArrows₅_exact hS₂ n (n + 1) (hrel' n)).δlast.δlast
      (inferInstanceAs (Epi (homologyMap φ.τ₁ n)))
      (inferInstanceAs (Epi (homologyMap φ.τ₃ n)))
      (inferInstanceAs (Mono (homologyMap φ.τ₁ (n + 1))))
  exact isIso_of_mono_of_epi _

end ZInQ.Contrib.CloudB3RC53.SelmerDuality

import ZInQKernel.Contrib.OneProof.RC.Limits.SDRRetract
import ZInQKernel.Contrib.OneProof.RC.Limits.FieldModel

/-!
# Lane RC31, round 7: normalized retracts over a ring (K-injective complexes)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), with the
normalized deformation retract data of tex 4423–4437 and the splitting of tex 5398–5403.

* `exists_retract_of_surjective_quasiIso_kInj`: over a commutative ring, a quasi-isomorphism
  `p : X → Y` of K-injective complexes with degreewise linear right inverses admits a
  `GRetract X Y` with projection `p`. The proof is that of the field version: a homotopy
  inverse `g` (`CochainComplex.IsKInjective.quasiIso_iff`), the strict section
  `i = g − d H − H d` (`rsectHom`) and the Lambe–Stasheff normalization
  (`GRetract.ofDeformation`) of the homotopy `H p − K` (`rsect_retract_homotopy`).
* `exists_rightInverse_of_projective`: degreewise right inverses exist when `p` is degreewise
  surjective and the terms of `Y` are projective (for instance free).
* `injective_of_isCompl`: a complement submodule of an injective module is injective.
* `quotientCx_isKInjective`: for a split inclusion `E : C_P ⊂ C_R` with injective terms `C_Rⁿ`,
  `C_R` strictly concentrated in degrees `≥ a`, the quotient complex `E.quotientCx` is
  K-injective.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section RingRetract


variable {k : Type} [CommRing k] {X Y : GCx k}

/-- The corrected section `g − d H − H d` in degree `n`, with arbitrary neighbouring indices
(tex 4391–4451). Kind: definition. -/
def rsectCompGen (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (n b c : ℤ) (hbn : b + 1 = n) (hnc : n + 1 = c) : Y.X n →ₗ[k] X.X n :=
  g n - X.d b n hbn ∘ₗ H n b hbn - H c n hnc ∘ₗ Y.d n c hnc

/-- The corrected section `g − d H − H d` in degree `n` (tex 4391–4451). Kind: definition. -/
def rsectComp (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (n : ℤ) : Y.X n →ₗ[k] X.X n :=
  rsectCompGen g H n (n - 1) (n + 1) (by omega) rfl

/-- The corrected section does not depend on the index expressions (tex 4391–4451).
Kind: PROVED. -/
theorem rsectComp_eq_gen (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b) (n b c : ℤ) (hbn : b + 1 = n)
    (hnc : n + 1 = c) : rsectComp g H n = rsectCompGen g H n b c hbn hnc := by
  obtain rfl : b = n - 1 := by omega
  subst hnc
  rfl

/-- The corrected section as a chain map, for a chain map `g` (tex 4391–4451).
Kind: definition. -/
def rsectHom (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y)) :
    GHom Y X where
  f i j hij := by subst hij; exact rsectComp g H i
  comm i i₁ j j₁ hij h₁ h₂ hj y := by
    subst hij h₁ hj
    change rsectComp g H (i + 1) (Y.d i (i + 1) h₂ y) = X.d i (i + 1) h₂ (rsectComp g H i y)
    rw [rsectComp_eq_gen g H (i + 1) i (i + 1 + 1) h₂ rfl,
      rsectComp_eq_gen g H i (i - 1) (i + 1) (by omega) h₂]
    simp only [rsectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, Y.d_d, X.d_d,
      map_zero, sub_zero, hg]

/-- The components of `rsectHom` (tex 4391–4451). Kind: PROVED. -/
theorem rsectHom_f (g : ∀ n, Y.X n →ₗ[k] X.X n) (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y))
    (n : ℤ) (y : Y.X n) : (rsectHom g H hg).f n n rfl y = rsectComp g H n y := rfl

/-- If `p g − 1 = d H₀ + H₀ d` and `p H = H₀`, then `p (g − d H − H d) = 1`
(tex 4391–4451). Kind: PROVED. -/
theorem p_rsectComp (p : GHom X Y) (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b) (H₀ : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] Y.X b)
    (hpH : ∀ a b (hab : b + 1 = a) (y : Y.X a), p.f b b rfl (H a b hab y) = H₀ a b hab y)
    (hhom : ∀ n (y : Y.X n), p.f n n rfl (g n y) =
      H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) + Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
        + y)
    (n : ℤ) (y : Y.X n) : p.f n n rfl (rsectComp g H n y) = y := by
  simp only [rsectComp, rsectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [p.comm (n - 1) n (n - 1) n rfl (by omega) (by omega) rfl, hpH, hpH, hhom]
  abel

/-- If `g p − 1 = d K + K d`, then for `i = g − d H − H d` one has
`1 − i p = d (H p − K) + (H p − K) d` (tex 4423–4437). Kind: PROVED. -/
theorem rsect_retract_homotopy (p : GHom X Y) (g : ∀ n, Y.X n →ₗ[k] X.X n)
    (H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b)
    (hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y))
    (K : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[k] X.X b)
    (hK : ∀ n (x : X.X n), g n (p.f n n rfl x) =
      K (n + 1) n rfl (X.d n (n + 1) rfl x) + X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x)
        + x)
    (n : ℤ) (x : X.X n) :
    x - (rsectHom g H hg).f n n rfl (p.f n n rfl x) =
      X.d (n - 1) n (by omega) ((H n (n - 1) (by omega) ∘ₗ p.f n n rfl - K n (n - 1) (by omega)) x)
        + (H (n + 1) n rfl ∘ₗ p.f (n + 1) (n + 1) rfl - K (n + 1) n rfl) (X.d n (n + 1) rfl x) := by
  rw [rsectHom_f]
  simp only [rsectComp, rsectCompGen, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [p.comm n (n + 1) n (n + 1) rfl rfl rfl rfl x, hK]
  abel

/-- **A normalized retract onto the target of a split quasi-isomorphism of K-injective
complexes** (tex 4391–4451, 4423–4437). Over a commutative ring, for K-injective complexes `X`,
`Y` and a quasi-isomorphism `p : X → Y` with degreewise linear right inverses, there is a
`GRetract X Y` whose projection is `p`. Kind: PROVED. -/
theorem exists_retract_of_surjective_quasiIso_kInj (p : GHom X Y)
    (hsplit : ∀ n, ∃ s : Y.X n →ₗ[k] X.X n, ∀ y, p.f n n rfl (s y) = y)
    [X.toCC.IsKInjective] [Y.toCC.IsKInjective] [QuasiIso (GHom.toCC p)] :
    ∃ R : GRetract X Y, ∀ n (x : X.X n), R.p.f n n rfl x = p.f n n rfl x := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (GHom.toCC p)).1 inferInstance
  let g : ∀ n, Y.X n →ₗ[k] X.X n := fun n => (e.inv.f n).hom
  let H₀ : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] Y.X b := fun a b _ =>
    (e.homotopyInvHomId.hom a b).hom
  choose s hs using hsplit
  let H : ∀ a b : ℤ, b + 1 = a → Y.X a →ₗ[k] X.X b := fun a b hab => s b ∘ₗ H₀ a b hab
  have hg : ∀ i j (hij : i + 1 = j) (y : Y.X i), g j (Y.d i j hij y) = X.d i j hij (g i y) := by
    intro i j hij y
    have h1 : (X.toCC.d i j).hom ((e.inv.f i).hom y) = (e.inv.f j).hom ((Y.toCC.d i j).hom y) :=
      congrArg (fun φ => φ.hom y) (e.inv.comm i j)
    have e1 := GCx.toCC_d_hom X i j hij ((e.inv.f i).hom y)
    have e2 := GCx.toCC_d_hom Y i j hij y
    exact (congrArg (fun z => (e.inv.f j).hom z) e2.symm).trans (h1.symm.trans e1)
  have hpH : ∀ a b (hab : b + 1 = a) (y : Y.X a), p.f b b rfl (H a b hab y) = H₀ a b hab y :=
    fun a b _ y => hs b _
  have hhom : ∀ n (y : Y.X n), p.f n n rfl (g n y) =
      H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) + Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
        + y := by
    intro n y
    have h1 := congrArg (fun φ => φ.hom y) (e.homotopyInvHomId.comm n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at h1
    have hp : ∀ x : X.X n, (e.hom.f n).hom x = p.f n n rfl x := fun x => by rw [he]; rfl
    have h2 : (e.hom.f n).hom (g n y) = H₀ (n + 1) n rfl (Y.d n (n + 1) rfl y) +
        Y.d (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y) + y := by
      have e2 := GCx.toCC_d_hom Y n (n + 1) rfl y
      have e3 := GCx.toCC_d_hom Y (n - 1) n (by omega) (H₀ n (n - 1) (by omega) y)
      rw [← e2, ← e3]
      exact h1
    rw [hp] at h2
    exact h2
  let K : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[k] X.X b := fun a b _ =>
    (e.homotopyHomInvId.hom a b).hom
  have hK : ∀ n (x : X.X n), g n (p.f n n rfl x) =
      K (n + 1) n rfl (X.d n (n + 1) rfl x) + X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x)
        + x := by
    intro n x
    have h1 := congrArg (fun φ => φ.hom x) (e.homotopyHomInvId.comm n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at h1
    have hp : ∀ x : X.X n, (e.hom.f n).hom x = p.f n n rfl x := fun x => by rw [he]; rfl
    have h2 : g n ((e.hom.f n).hom x) = K (n + 1) n rfl (X.d n (n + 1) rfl x) +
        X.d (n - 1) n (by omega) (K n (n - 1) (by omega) x) + x := by
      have e2 := GCx.toCC_d_hom X n (n + 1) rfl x
      have e3 := GCx.toCC_d_hom X (n - 1) n (by omega) (K n (n - 1) (by omega) x)
      rw [← e2, ← e3]
      exact h1
    rw [hp] at h2
    exact h2
  exact ⟨GRetract.ofDeformation (rsectHom g H hg) p
    (fun a b hab => H a b hab ∘ₗ p.f a a rfl - K a b hab) (p_rsectComp p g H H₀ hpH hhom)
    (rsect_retract_homotopy p g H hg K hK), fun _ _ => rfl⟩

/-! ### Right inverses, injective summands and K-injective quotients -/

/-- **Degreewise right inverses from projectivity** (tex 4391–4451): if `p` is degreewise
surjective and the terms of `Y` are projective modules (for instance free), each component of
`p` has a linear right inverse. Kind: PROVED. -/
theorem exists_rightInverse_of_projective {k : Type} [CommRing k] {X Y : GCx k} (p : GHom X Y)
    (hsurj : ∀ n, Function.Surjective (p.f n n rfl)) [∀ n, Module.Projective k (Y.X n)] :
    ∀ n, ∃ s : Y.X n →ₗ[k] X.X n, ∀ y, p.f n n rfl (s y) = y := fun n => by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (p.f n n rfl) LinearMap.id (hsurj n)
  exact ⟨s, fun y => LinearMap.congr_fun hs y⟩

/-- **A direct summand of an injective module is injective** (tex 5398–5403): a submodule `N`
with a complement `N'` in an injective module `M` is injective, through the projection
`M → N` along `N'`. Kind: PROVED. -/
theorem injective_of_isCompl {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Injective R M] {N N' : Submodule R M} (h : IsCompl N N') : Module.Injective R N :=
  ⟨fun _ _ _ _ _ _ f hf g => by
    obtain ⟨h', hh'⟩ := Module.Injective.out f hf (N.subtype ∘ₗ g)
    refine ⟨N.projectionOnto N' h ∘ₗ h', fun x => ?_⟩
    rw [LinearMap.comp_apply, hh', LinearMap.comp_apply]
    exact Submodule.projectionOnto_apply_left h (g x)⟩

/-- **The quotient of a split inclusion of injective complexes is K-injective**
(tex 5398–5403, 4391–4451): for a split inclusion `E : C_P ⊂ C_R` whose terms `C_Rⁿ` are
injective modules, with `C_R` strictly concentrated in degrees `≥ a`, the quotient complex
`E.quotientCx` (terms the complements `Qⁿ`) is K-injective. Kind: PROVED. -/
theorem quotientCx_isKInjective {S : Type} [CommRing S] {CP CR : GCx S}
    (E : SplitInclusion CP CR) (a : ℤ) [∀ n, Module.Injective S (CR.X n)]
    [CR.toCC.IsStrictlyGE a] : E.quotientCx.toCC.IsKInjective := by
  have hinj : ∀ n, Injective (E.quotientCx.toCC.X n) := fun n => by
    have : Module.Injective S (E.Qc n) := injective_of_isCompl (E.compl n).symm
    exact Module.injective_object_of_injective_module (R := S) (M := E.Qc n)
  have : E.quotientCx.toCC.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hz := CR.toCC.isZero_of_isStrictlyGE a i hi
    rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
    change Subsingleton (E.Qc i)
    exact ⟨fun x y => Subtype.ext (@Subsingleton.elim (CR.X i) hz _ _)⟩
  exact CochainComplex.isKInjective_of_injective _ a

end RingRetract

end ZInQ.Manuscript.RC.Limits

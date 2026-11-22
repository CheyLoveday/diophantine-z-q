import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricRightIdeal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TateIdealRead
import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal

/-! Transfer the Tate calculation to the quaternion completion in any
rational frame where the endomorphisms of the reference act by their
geometric Tate maps. The comparison of a CM generator is on torsion
in that same frame. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A B : PkgI3.AbVar k} {a b : ℚ}

private theorem image_span {S M N : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (s : Set M) :
    f '' (Submodule.span S s : Set M) = (Submodule.span S (f '' s) : Set N) :=
  (Submodule.map_coe f (Submodule.span S s)).symm.trans
    (congrArg SetLike.coe (Submodule.map_span f s))

/-- The completed quotient right ideal is principal in quaternion
coordinates. At a prime dividing the quotient degree, the generator
acts on the rational Tate module as the scalar (m/\alpha), with
(\alpha) tested against the actual geometric kernel. -/
theorem localLattice_quotientRightIdeal_eq_localRight
    (R : Order a b) (embed : A.End →+* Eichler.B a b)
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (p : Adelic.Prime) (n N : ℕ)
    (c : ℤ_[p.val]ˣ) (hm_p : (m : ℤ_[p.val]) = (p.val : ℤ_[p.val]) ^ n * c)
    (hCN : ∀ x ∈ C, x ^ N = 1) (hN : IsUnit (N : ℤ_[p.val]))
    (e : Bp p.val a b ≃ₐ[ℚ_[p.val]] Module.End ℚ_[p.val] (A.V p.val))
    (he : ∀ x : A.End, e (toLocal p.val (embed x)) =
      (homT (ℓ := p.val) x).baseChange ℚ_[p.val])
    (hTv : Function.Injective (homT (ℓ := p.val) v))
    (hfullA : Submodule.span ℤ_[p.val] (Set.range (tateHom p.val A A)) = ⊤)
    (hfullAB : Submodule.span ℤ_[p.val] (Set.range (tateHom p.val A B)) = ⊤)
    (α β : Module.End ℤ_[p.val] (A.T p.val))
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : ∀ x, α (β x) = (m : ℤ_[p.val]) • x)
    (hker : ∀ x : A.T p.val, (α x).1 n = 0 ↔
      Additive.toMul (x.1 n) ∈ geometricKernel (L := AlgebraicClosure k) u)
    (z : (Bp p.val a b)ˣ) (hz : e (z : Bp p.val a b) = β.baseChange ℚ_[p.val]) :
    localLattice p.val (quotientRightIdeal R embed u v m hm hu hv C hC hR).lattice =
      localRight R p z := by
  let ρ : Bp p.val a b →ₗ[ℤ_[p.val]] Module.End ℚ_[p.val] (A.V p.val) :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r x => by
        change e ((r : ℚ_[p.val]) • x) = (r : ℚ_[p.val]) • e x
        exact map_smul e _ _ }
  let τ := Module.End.baseChangeHom ℤ_[p.val] ℚ_[p.val] (A.T p.val)
  let φ := ((toLocal p.val : Eichler.B a b →+* Bp p.val a b).comp embed).toAddMonoidHom
  have hρ (x : A.End) : ρ (φ x) = τ (tateHom p.val A A x) := he x
  have hsource : ρ '' (R.completion p.val : Set (Bp p.val a b)) = Set.range τ := by
    change ρ '' (((R.completion p.val).toSubmodule : Submodule ℤ_[p.val] (Bp p.val a b)) :
      Set (Bp p.val a b)) = _
    rw [R.completion_toSubmodule, localLattice]
    erw [image_span ρ]
    change ((Submodule.span ℤ_[p.val] (ρ '' (toLocal p.val '' (R.ring : Set (Eichler.B a b))))) :
      Set (Module.End ℚ_[p.val] (A.V p.val))) = _
    rw [← hR, Set.image_image, Set.image_image]
    change ((Submodule.span ℤ_[p.val]
      ((fun x : A.End => ρ (φ x)) '' (levelEnd A C : Set A.End))) :
        Set (Module.End ℚ_[p.val] (A.V p.val))) = _
    rw [show (fun x : A.End => ρ (φ x)) = (fun x => τ (tateHom p.val A A x)) from funext hρ,
      ← Set.image_image]
    change ((Submodule.span ℤ_[p.val] (τ.toLinearMap '' (tateHom p.val A A ''
      (levelEnd A C : Set A.End)))) : Set (Module.End ℚ_[p.val] (A.V p.val))) = _
    rw [← Submodule.map_span, span_levelEnd_eq_span_end A C N hCN hN, hfullA,
      Submodule.map_top]
    rfl
  apply SetLike.coe_injective
  apply (Set.image_injective.mpr e.injective : Function.Injective (Set.image ρ))
  rw [localLattice_quotientRightIdeal_eq_span, image_span ρ,
    localRight_set, Set.image_image, Set.image_image]
  have hcomp : (fun x : Hom A B => ρ (φ (postcomposeToEnd v x))) =
      (fun x => τ ((tateHom p.val A A).comp (postcomposeToEnd v) x)) :=
    funext fun x => hρ (postcomposeToEnd v x)
  change ((Submodule.span ℤ_[p.val] ((fun x : Hom A B => ρ (φ (postcomposeToEnd v x))) ''
    (levelHom C (C.map (ptMap u)) : Set (Hom A B)))) :
      Set (Module.End ℚ_[p.val] (A.V p.val))) = _
  rw [hcomp, ← Set.image_image]
  change ((Submodule.span ℤ_[p.val] (τ.toLinearMap '' (((tateHom p.val A A).comp
    (postcomposeToEnd v)) '' (levelHom C (C.map (ptMap u)) : Set (Hom A B))))) :
      Set (Module.End ℚ_[p.val] (A.V p.val))) = _
  rw [← image_span τ.toLinearMap]
  have hprincipal :
      (fun x : Bp p.val a b => ρ ((z : Bp p.val a b) * x)) = (fun x => τ β * ρ x) := by
    funext x
    change e ((z : Bp p.val a b) * x) = τ β * e x
    rw [map_mul, hz]
    rfl
  rw [hprincipal, ← Set.image_image (fun y => τ β * y) ρ
    (R.completion p.val : Set (Bp p.val a b)), hsource]
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_span_postcompose_levelHom_iff_local_factor p.val u v m n c hm_p hu hv
      hTv α β hα hβ hαβ hker C (C.map (ptMap u)) N hCN hN hfullAB x).mp hx
    exact ⟨τ g, Set.mem_range_self g, (map_mul τ β g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨β * g, ?_, map_mul τ β g⟩
    exact (mem_span_postcompose_levelHom_iff_local_factor p.val u v m n c hm_p hu hv
      hTv α β hα hβ hαβ hker C (C.map (ptMap u)) N hCN hN hfullAB _).mpr ⟨g, rfl⟩

/-- Only the primes supporting the quotient degree need a nontrivial
local factor. The actual rational Hom ideal is obtained from an
adelic generator whose completions are principal. -/
theorem exists_adelic_quotientRightIdeal_of_localFactors
    (R : Order a b) (embed : A.End →+* Eichler.B a b)
    (u : Hom A B) (v : Hom B A) (m : ℕ) (hm : (m : k) ≠ 0)
    (hu : u.hom ≫ v.hom = ((m : ℤ) : A.End).hom)
    (hv : v.hom ≫ u.hom = ((m : ℤ) : B.End).hom)
    (C : Subgroup (A.Pt k)) (hC : (Nat.card C).Coprime m)
    (hR : embed '' (levelEnd A C : Set A.End) = (R.ring : Set (Eichler.B a b)))
    (h : ∀ p : Adelic.Prime, ¬ IsUnit (m : ℤ_[p.val]) → ∃ z : (Bp p.val a b)ˣ,
      localLattice p.val (quotientRightIdeal R embed u v m hm hu hv C hC hR).lattice =
        localRight R p z) :
    ∃ z : FiniteUnits R, (fromAdelic z).val = quotientRightIdeal R embed u v m hm hu hv C hC hR := by
  classical
  let I := quotientRightIdeal R embed u v m hm hu hv C hC hR
  have hI : I.LocallyPrincipal := by
    intro p hp
    let q : Adelic.Prime := ⟨p, hp.out⟩
    by_cases hmp : IsUnit (m : ℤ_[p])
    · refine ⟨1, ?_⟩
      rw [localLattice_quotientRightIdeal_eq_completion R embed u v m hm hu hv C hC hR p hmp]
      simp
      rfl
    · obtain ⟨z, hz⟩ := h q hmp
      refine ⟨z, ?_⟩
      exact (congrArg SetLike.coe hz).trans (localRight_set q z)
  obtain ⟨z, hz⟩ := exists_adelic_representative (⟨I, hI⟩ : LPIdeal R)
  exact ⟨z, congrArg Subtype.val hz⟩

end ZInQ.Manuscript.RC.HCMV21

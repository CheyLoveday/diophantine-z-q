import ZInQKernel.OneProof.H.TailY

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit

namespace GaRigidity

variable {k : Type} [Field k]

/-! ## §0. `𝔾_a` and its homomorphisms, in the functor of points -/

/-- `k[X] → k[X, Y]`, `X ↦ X + Y`: the comultiplication of `𝔾_a = Spec k[X]`. -/
def addMap (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.X 1)

/-- `X ↦ X` (first projection `𝔾_a × 𝔾_a → 𝔾_a`). -/
def pr1 (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k := Polynomial.aeval (MvPolynomial.X 0)

/-- `X ↦ Y` (second projection `𝔾_a × 𝔾_a → 𝔾_a`). -/
def pr2 (k : Type) [Field k] : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k := Polynomial.aeval (MvPolynomial.X 1)

/-- A morphism `g : 𝔾_a = Spec k[X] → G` of `k`-schemes is a **homomorphism of group schemes**: `g(x + y) = g(x) g(y)`,
i.e. `g ∘ add = (g ∘ pr₁) · (g ∘ pr₂)` as morphisms `Spec k[X, Y] → G` (product in the group `Hom(Spec k[X,Y], G)`). -/
def IsGaHom (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (g : algPt k (Polynomial k) ⟶ G) : Prop :=
  algPtMap (addMap k) ≫ g = (algPtMap (pr1 k) ≫ g) * (algPtMap (pr2 k) ≫ g)

/-- **`G` contains no subgroup scheme isomorphic to `𝔾_a`**: no homomorphism `𝔾_a → G` of `k`-group schemes is a closed
immersion. (The condition of SGA 7 I Exp. IX Déf. 3.4 / 2.1.5 on the identity component of the geometric special fibre,
per the queue11 reviewer verdict; locators UNVERIFIED.) -/
def NoGaSubgroup (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∀ g : algPt k (Polynomial k) ⟶ G, IsGaHom G g → IsClosedImmersion g.left → False

/-! ## §1. `algPt` calculus -/

theorem algPtMap_comp {R S T : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] [CommRing T]
    [Algebra k T] (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    algPtMap (g.comp f) = algPtMap g ≫ algPtMap f := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem algPtMap_id {R : Type} [CommRing R] [Algebra k R] : algPtMap (AlgHom.id k R) = 𝟙 (algPt k R) := by
  ext1
  change Spec.map _ = 𝟙 _
  exact Spec.map_id _

theorem algPtMap_left {R S : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S) :
    (algPtMap f).left = Spec.map (CommRingCat.ofHom (f : R →+* S)) := rfl

instance (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] : LocallyOfFiniteType (algPt k R).hom :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-! ## §2. Step (1): every homomorphism `𝔾_a → 𝔾_m^r` is trivial -/

/-- **Step (1), ring form**: a unit `u ∈ k[X]ˣ = 𝔾_m(k[X])` with `u(X + Y) = u(X) u(Y)` (a homomorphism `𝔾_a → 𝔾_m`,
by Yoneda) is `1`. Over a field `k[X]ˣ = kˣ`, and `c = c²` with `c` a unit forces `c = 1`. -/
theorem unit_additive_eq_one (u : (Polynomial k)ˣ)
    (h : Units.map (addMap k : Polynomial k →* MvPolynomial (Fin 2) k) u =
      Units.map (pr1 k : Polynomial k →* MvPolynomial (Fin 2) k) u *
        Units.map (pr2 k : Polynomial k →* MvPolynomial (Fin 2) k) u) : u = 1 := by
  obtain ⟨r, hr, hC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have h' := congrArg Units.val h
  simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_ofClass] at h'
  rw [← hC] at h'
  simp only [addMap, pr1, pr2, Polynomial.aeval_C] at h'
  rw [← map_mul] at h'
  have hrr : r = r * r := (algebraMap k (MvPolynomial (Fin 2) k)).injective h'
  have hr1 : r = 1 := by
    have h0 : r ≠ 0 := hr.ne_zero
    have := mul_left_cancel₀ h0 (hrr.symm.trans (mul_one r).symm)
    exact this
  apply Units.ext
  rw [← hC, hr1, Polynomial.C_1, Units.val_one]

/-- **Step (1), group-scheme form**: let `e` identify `𝔾_m^r` with a subgroup functor of `U` (injective, multiplicative,
natural in the `k`-algebra, as in `HasSemiAbelianIdentityComponent`). A homomorphism `𝔾_a → U` of the form `e(t)` is
trivial. -/
theorem gaHom_torus_trivial (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (hinj : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hnat : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (t : Fin r → (Polynomial k)ˣ) (h : IsGaHom U (e _ t)) : e _ t = 1 := by
  unfold IsGaHom at h
  rw [← hnat, ← hnat, ← hnat, ← map_mul] at h
  have ht := hinj _ h
  have : t = 1 := by
    funext i
    exact unit_additive_eq_one (t i) (congrFun ht i)
  rw [this, map_one]

end GaRigidity

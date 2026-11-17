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

/-! ## §3. The local ring of `ℙ¹` at `∞`: `R = k[s]_(s)` with `s = 1/x`, its translations and its residue map -/

/-- The prime `(s) ⊆ k[s]`. -/
abbrev P0 (k : Type) [Field k] : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance P0.isPrime : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `K = k(s) = Frac k[s]`. -/
abbrev Kl (k : Type) [Field k] : Type := FractionRing (Polynomial k)

theorem P0_le : (P0 k).primeCompl ≤ nonZeroDivisors (Polynomial k) :=
  le_nonZeroDivisors_of_noZeroDivisors (fun h0 => h0 (Ideal.zero_mem _))

/-- `R = k[s]_(s) ⊆ K`, a discrete valuation ring (the local ring of `ℙ¹` at `∞`, with `s = 1/x`). -/
abbrev Rl (k : Type) [Field k] : Type :=
  ↥(Localization.subalgebra.ofField (Kl k) (P0 k).primeCompl P0_le)

instance : IsLocalization.AtPrime (Rl k) (P0 k) :=
  Localization.subalgebra.isLocalization_ofField (Kl k) (P0 k).primeCompl P0_le

instance : IsDiscreteValuationRing (Rl k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero) (Rl k)

example : IsFractionRing (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Rl k) (Kl k) := inferInstance
example : IsScalarTower k (Polynomial k) (Rl k) := inferInstance

/-- The uniformizer `s ∈ R`. -/
abbrev sR (k : Type) [Field k] : Rl k := algebraMap (Polynomial k) (Rl k) Polynomial.X

theorem not_mem_P0 {y : Polynomial k} (hy : y ∈ (P0 k).primeCompl) : y.eval 0 ≠ 0 := by
  intro h
  apply hy
  show y ∈ P0 k
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, h]

/-- The residue map `ρ : R → k`, `f ↦ f(0)` (value at `∞`). -/
def rho (k : Type) [Field k] : Rl k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (0 : k)) (fun y => by
    rw [isUnit_iff_ne_zero, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem rho_algebraMap (p : Polynomial k) : rho k (algebraMap (Polynomial k) (Rl k) p) = p.eval 0 := by
  rw [rho, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]

theorem rho_s : rho k (sR k) = 0 := by
  rw [rho_algebraMap]; simp

theorem rho_surjective : Function.Surjective (rho k) := fun c => ⟨algebraMap k _ c, by simp⟩

/-- An element of the local ring `R` with nonzero residue is a unit. -/
theorem isUnit_of_rho_ne_zero {x : Rl k} (hx : rho k x ≠ 0) : IsUnit x := by
  by_contra hu
  have hm : x ∈ IsLocalRing.maximalIdeal (Rl k) := (IsLocalRing.mem_maximalIdeal x).mpr hu
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (rho k) rho_surjective)] at hm
  exact hx (RingHom.mem_ker.mp hm)

/-- `1 + c s` is a unit of `R`. -/
theorem isUnit_u (c : k) : IsUnit (1 + algebraMap k (Rl k) c * sR k) :=
  isUnit_of_rho_ne_zero (by simp [rho_s])

/-- `s/(1 + c s)`. -/
def sT (c : k) : Rl k := sR k * ↑(isUnit_u c).unit⁻¹

theorem rho_sT (c : k) : rho k (sT c) = 0 := by
  rw [sT, map_mul, rho_s, zero_mul]

/-- **The translation `x ↦ x + c` at `∞`**: `τ_c : R → R`, `s ↦ s/(1 + c s)`. -/
def tau (c : k) : Rl k →ₐ[k] Rl k :=
  IsLocalization.liftAlgHom (M := (P0 k).primeCompl) (f := Polynomial.aeval (sT c)) (fun y => by
    apply isUnit_of_rho_ne_zero
    rw [← Polynomial.aeval_algHom_apply, rho_sT, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using not_mem_P0 y.2)

theorem tau_algebraMap (c : k) (p : Polynomial k) :
    tau c (algebraMap (Polynomial k) (Rl k) p) = Polynomial.aeval (sT c) p := by
  rw [tau, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem tau_s (c : k) : tau c (sR k) = sT c := by
  rw [tau_algebraMap, Polynomial.aeval_X]

/-- `ρ ∘ τ_c = ρ`: the translation fixes the point at `∞`. -/
theorem rho_comp_tau (c : k) : (rho k).comp (tau c) = rho k := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change rho k (tau c (algebraMap _ _ Polynomial.X)) = rho k (algebraMap _ _ Polynomial.X)
  rw [tau_algebraMap, Polynomial.aeval_X, rho_sT, rho_algebraMap]
  simp

/-- `τ_{-c} ∘ τ_c = id`. -/
theorem tau_neg_comp_tau (c : k) : (tau (-c)).comp (tau c) = AlgHom.id k (Rl k) := by
  apply IsLocalization.algHom_ext (P0 k).primeCompl
  apply Polynomial.algHom_ext
  change tau (-c) (tau c (algebraMap _ _ Polynomial.X)) = algebraMap _ _ Polynomial.X
  rw [tau_algebraMap, Polynomial.aeval_X, sT, map_mul, tau_s]
  set a : Rl k := ↑(isUnit_u c).unit⁻¹
  set b : Rl k := ↑(isUnit_u (-c)).unit⁻¹
  have ha : a * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have hb : b * (1 + algebraMap k (Rl k) (-c) * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u (-c))
  have h1 := congrArg (tau (-c)) ha
  rw [map_mul, map_one, map_add, map_one, map_mul, AlgHom.commutes, tau_s, sT] at h1
  change sR k * b * tau (-c) a = sR k
  rw [map_neg] at hb
  linear_combination (sR k * tau (-c) a) * hb + sR k * h1

theorem tau_injective (c : k) : Function.Injective (tau c) := by
  intro x y h
  have := congrArg (tau (-c)) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, tau_neg_comp_tau] at this

theorem sR_ne_zero : sR k ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap (Polynomial k) (Rl k)) :=
    IsLocalization.injective (Rl k) P0_le
  exact Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))

/-- `j : R → K`. -/
abbrev jR (k : Type) [Field k] : Rl k →ₐ[k] Kl k := IsScalarTower.toAlgHom k (Rl k) (Kl k)

/-- `τ_c` on `K`. -/
theorem jtau_injective (c : k) : Function.Injective ((jR k).comp (tau c)) :=
  (IsFractionRing.injective (Rl k) (Kl k)).comp (tau_injective c)

def tauK (c : k) : Kl k →ₐ[k] Kl k :=
  IsFractionRing.liftAlgHom (g := (jR k).comp (tau c)) (jtau_injective c)

theorem tauK_comp_jR (c : k) : (tauK c).comp (jR k) = (jR k).comp (tau c) := by
  apply AlgHom.ext; intro x
  show tauK c (algebraMap (Rl k) (Kl k) x) = algebraMap (Rl k) (Kl k) (tau c x)
  rw [tauK, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]; rfl

/-- `x = 1/s ∈ K`. -/
abbrev xK (k : Type) [Field k] : Kl k := (algebraMap (Rl k) (Kl k) (sR k))⁻¹

/-- `τ_c(1/s) = 1/s + c`. -/
theorem tauK_xK (c : k) : tauK c (xK k) = xK k + algebraMap k (Kl k) c := by
  have h1 : tauK c (algebraMap (Rl k) (Kl k) (sR k)) = algebraMap (Rl k) (Kl k) (sT c) := by
    have := congrArg (fun f => f (sR k)) (tauK_comp_jR c)
    simpa [tau_s] using this
  rw [map_inv₀, h1, sT, RingHom.map_mul]
  have hs : algebraMap (Rl k) (Kl k) (sR k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Rl k) (Kl k))).mpr sR_ne_zero
  have ha : (↑(isUnit_u c).unit⁻¹ : Rl k) * (1 + algebraMap k (Rl k) c * sR k) = 1 := IsUnit.val_inv_mul (isUnit_u c)
  have ha' := congrArg (algebraMap (Rl k) (Kl k)) ha
  rw [RingHom.map_mul, RingHom.map_one, RingHom.map_add, RingHom.map_one, RingHom.map_mul,
    ← IsScalarTower.algebraMap_apply] at ha'
  set A := algebraMap (Rl k) (Kl k) ↑(isUnit_u c).unit⁻¹
  set S := algebraMap (Rl k) (Kl k) (sR k)
  have hA : A = (1 + algebraMap k (Kl k) c * S)⁻¹ := eq_inv_of_mul_eq_one_left ha'
  have hu : 1 + algebraMap k (Kl k) c * S ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ha'; exact zero_ne_one ha'
  rw [hA, xK]
  field_simp
  ring


/-! ## §4. Step (2), the valuative argument: a homomorphism `𝔾_a → B` to a proper group scheme kills `k`-points

For `g : 𝔾_a → B` and the `K`-point `x = 1/s` of `𝔾_a`, the `K`-point `g(x)` of the proper `B` extends to an
`R`-point `Q` (valuative criterion, existence). The translation `τ_c` of `R` (`x ↦ x + c`) gives the extension
`Q ∘ τ_c` of `g(x + c) = g(x) g(c)`; so does `Q · g(c)`; by uniqueness (separatedness) they agree. At the closed point
(`ρ ∘ τ_c = ρ`) this reads `Q(∞) = Q(∞) g(c)`, so `g(c) = 1`. -/

section Valuative

variable (B : Over (Spec (CommRingCat.of k))) [IsProper B.hom]

/-- The valuative square of a `K`-point of `B` over `Spec R → Spec k`. -/
def vsq (T : algPt k (Kl k) ⟶ B) : ValuativeCommSq B.hom where
  R := Rl k
  K := Kl k
  i₁ := T.left
  i₂ := (algPt k (Rl k)).hom
  commSq := ⟨(Over.w T).trans (by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])⟩

/-- Existence of the extension of a `K`-point to an `R`-point (properness). -/
theorem lift_exists (T : algPt k (Kl k) ⟶ B) : ∃ Q : algPt k (Rl k) ⟶ B, algPtMap (jR k) ≫ Q = T := by
  have hE : (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨l⟩ := (hE.1 (vsq B T)).exists_lift
  refine ⟨Over.homMk l.l l.fac_right, ?_⟩
  ext1
  exact l.fac_left

/-- Uniqueness of the extension (separatedness). -/
theorem lift_unique (Q Q' : algPt k (Rl k) ⟶ B) (h : algPtMap (jR k) ≫ Q = algPtMap (jR k) ≫ Q') : Q = Q' := by
  have hU := IsSeparated.valuativeCriterion B.hom (vsq B (algPtMap (jR k) ≫ Q))
  have := hU.elim ⟨Q.left, rfl, Over.w Q⟩ ⟨Q'.left, by rw [h]; rfl, Over.w Q'⟩
  ext1
  exact congrArg CategoryTheory.CommSq.LiftStruct.l this

variable [GrpObj B]

/-- **Step (2), pointwise**: a homomorphism `g : 𝔾_a → B` to a proper group scheme over a field `k` sends every
`k`-point `c` of `𝔾_a` to the unit. -/
theorem gaHom_proper_point (g : algPt k (Polynomial k) ⟶ B) (h : IsGaHom B g) (c : k) :
    algPtMap (Polynomial.aeval c) ≫ g = 1 := by
  set xc := algPtMap (Polynomial.aeval c) ≫ g
  let P : Polynomial k →ₐ[k] Kl k := Polynomial.aeval (xK k)
  let φ : MvPolynomial (Fin 2) k →ₐ[k] Kl k := MvPolynomial.aeval ![xK k, algebraMap k (Kl k) c]
  have hadd : φ.comp (addMap k) = (tauK c).comp P := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, addMap, Polynomial.aeval_X, map_add, MvPolynomial.aeval_X, φ, P]
    rw [tauK_xK]
    simp
  have hp1 : φ.comp (pr1 k) = P := by
    apply Polynomial.algHom_ext
    simp [pr1, φ, P]
  have hp2 : φ.comp (pr2 k) = (Algebra.ofId k (Kl k)).comp (Polynomial.aeval c) := by
    apply Polynomial.algHom_ext
    simp [pr2, φ]
  have hhom : algPtMap ((tauK c).comp P) ≫ g =
      (algPtMap P ≫ g) * (algPtMap (Algebra.ofId k (Kl k)) ≫ xc) := by
    have := congrArg (algPtMap φ ≫ ·) h
    simp only [comp_mul, ← Category.assoc, ← algPtMap_comp, hadd, hp1, hp2] at this
    rw [this, algPtMap_comp, Category.assoc]
  obtain ⟨Q, hQ⟩ := lift_exists B (algPtMap P ≫ g)
  have hjo : (jR k).comp (Algebra.ofId k (Rl k)) = Algebra.ofId k (Kl k) := Subsingleton.elim _ _
  have key : algPtMap (tau c) ≫ Q = Q * (algPtMap (Algebra.ofId k (Rl k)) ≫ xc) := by
    apply lift_unique B
    rw [comp_mul, ← Category.assoc, ← algPtMap_comp, ← tauK_comp_jR, algPtMap_comp, Category.assoc, hQ,
      ← Category.assoc, ← algPtMap_comp, ← Category.assoc (algPtMap (jR k)), ← algPtMap_comp, hjo]
    exact hhom
  have hro : (rho k).comp (Algebra.ofId k (Rl k)) = AlgHom.id k k := Subsingleton.elim _ _
  have key2 := congrArg (algPtMap (rho k) ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ← algPtMap_comp, rho_comp_tau, hro, algPtMap_id, Category.id_comp] at key2
  exact left_eq_mul.mp key2

end Valuative

end GaRigidity

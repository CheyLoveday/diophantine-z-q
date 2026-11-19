import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointCentral

/-!
# Theorem 5.3, Lane RC34: the central functional from the integral self-duality

Proposition `ex:arith-paired-functional` (`diophantine_zq.tex`, tex 3736–3750, 3840–3856:
"`z^⊥ = j⁻¹ c(z)`, `λ_z = PD(−, j⁻¹ c(z))` are integral cochains, and the second is closed"),
Lemma `ex:arith-central-specialization` (tex 3902, 3976: `(λ_z)₀(i x) = PD_K(x, c_K(LmP))`) and
the proof of Proposition `ex:arith-central-calibration` (tex 4015–4017: "Self-duality …
gives a unimodular pairing of the free degree-one and degree-two parts").

The RC53 group's integral central Kummer duality `IntegralCentralKummerDuality G hfinite` (a
homotopy equivalence `e` of the retained central model `C` with its dual `Hom(C, ℤ₂)[−3]`,
whose map is the traced Selmer cup product; it follows from the nine book statements,
`integralCentralKummerDuality_of_literature_with_finiteness`) turns a degree-one cycle `y` of
`C` into the closed degree-two functional `e(y)`: the cochain form of `PD(−, y)`.

* `asForm2`: a dual degree-one cochain read as a linear form on degree two.
* `evalE2`, `evD`: evaluation at the degree-two free generator `e2`, on dual cochains and on the
  first cohomology of the dual complex (it kills dual coboundaries since `e2` is a cycle);
  `freeCoord2Dual` (the free coordinate as a dual cocycle) with `evD` value one, hence
  **`isUnit_evD`**: `evD` is a unit on every free-line generator of the dual first cohomology.
  This is the unimodularity of the free-line pairing, proved from the self-duality (no
  universal coefficient theorem is needed).
* `kummerTransportCycle`: a degree-one cycle whose class is `c_K(κ(L m P))`;
  `kummerCentralFunctional e D m := e(kummerTransportCycle D m)`, the central functional
  `λ₀ = PD(−, c_K z₀)` (tex 3902, 3976); `kummerCentralFunctional_closed`.
* **`kummerCentralFunctional_e2`** and **`v2_centralB0_selfDual`**: its value `b₀` on the
  degree-two free generator has valuation `j + vL + v₂ m` (tex 3977–3982, 4061–4062).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open CategoryTheory
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GCx.toCC_d_hom sgn)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (dualCx)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve
  centralFullTorsion)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape retainedCentralComplex
  retainedCentralCoordinates)
open ZInQ.Contrib.RC53Assist.CalibrationShape (centralRetainedGCx IntegralCentralKummerDuality)
open ZInQ.Manuscript.RC53Assist.CentralKummer (compactKummerComplex)
open ZInQ.Contrib.CloudB3RC53.Calibration (v2_mul)

attribute [local instance] Nat.fact_prime_two

section SelfDual

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

/-- **A dual degree-one cochain read as a linear form on degree two** (`Hom(C², ℤ₂)` is the
degree-one term of `Hom(C, ℤ₂)[−3]`). Kind: definition. -/
def asForm2 (φ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1) :
    (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2] := φ

/-- `asForm2` is additive and `ℤ₂`-linear. Kind: definition. -/
def asForm2Hom :
    (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1 →ₗ[ℤ_[2]]
      ((retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) where
  toFun := asForm2 G hfinite
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Evaluation at the degree-two free generator**, on dual degree-one cochains.
Kind: definition. -/
def evalE2 : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1 →ₗ[ℤ_[2]] ℤ_[2] :=
  (LinearMap.applyₗ (e2 G hfinite H)).comp (asForm2Hom G hfinite)

/-- `evalE2 φ = φ (e2)`. PROVED. -/
theorem evalE2_apply (φ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1) :
    evalE2 G hfinite H φ = asForm2 G hfinite φ (e2 G hfinite H) := rfl

/-- A dual degree-zero cochain read as a linear form on degree three. Kind: definition. -/
def asForm3 (ψ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X (1 - 1)) :
    (centralRetainedGCx G hfinite).X 3 →ₗ[ℤ_[2]] ℤ_[2] := ψ

/-- `e2` is a cycle of the relation-indexed retained model. PROVED. -/
theorem e2_closed' :
    (centralRetainedGCx G hfinite).d 2 (2 + 1) rfl (e2 G hfinite H) = 0 :=
  (GCx.toCC_d_hom (centralRetainedGCx G hfinite) 2 (2 + 1) rfl (e2 G hfinite H)).symm.trans
    (e2_closed G hfinite H)

/-- **Dual coboundaries vanish at `e2`** (`e2` is a cycle). PROVED. -/
theorem evalE2_boundary (ψ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X (1 - 1)) :
    evalE2 G hfinite H (((dualCx (centralRetainedGCx G hfinite) 3).toCC.d (1 - 1) 1).hom ψ) =
      0 := by
  change (-(sgn (1 - 1))) • asForm3 G hfinite ψ
    ((centralRetainedGCx G hfinite).d 2 (2 + 1) rfl (e2 G hfinite H)) = 0
  rw [e2_closed' G hfinite H, map_zero, smul_zero]

/-- **The functional `[φ] ↦ φ(e2)` on the first cohomology of the dual complex.**
Kind: definition. -/
def evD : (dualCx (centralRetainedGCx G hfinite) 3).toCC.homology 1 →ₗ[ℤ_[2]] ℤ_[2] :=
  homologyFunctional _ 1 (evalE2 G hfinite H) (evalE2_boundary G hfinite H)

/-- The free coordinate of degree two, as a dual degree-one cochain. Kind: definition. -/
def freeCoord2Dual : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1 :=
  (freeCoord2 G hfinite H : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2])

/-- A dual degree-two cochain read as a linear form on degree one. Kind: definition. -/
def asForm1 (φ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X (1 + 1)) :
    (centralRetainedGCx G hfinite).X 1 →ₗ[ℤ_[2]] ℤ_[2] := φ

/-- **The dual differential from degree one**: `(d φ)(y) = −(−1)¹ φ(d y)`. PROVED. -/
theorem dual_d12_apply (φ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1)
    (y : (centralRetainedGCx G hfinite).X 1) :
    asForm1 G hfinite (((dualCx (centralRetainedGCx G hfinite) 3).toCC.d 1 (1 + 1)).hom φ) y =
      (-(sgn 1)) • asForm2 G hfinite φ ((centralRetainedGCx G hfinite).d 1 2 rfl y) := rfl

/-- `−(−1)¹ = 1`. PROVED. -/
theorem neg_sgn_one : (-(sgn 1) : ℤ) = 1 := by decide

/-- **A dual degree-one cochain is a cocycle exactly when it vanishes on boundaries.**
PROVED. -/
theorem dual_closed_iff (φ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.X 1) :
    ((dualCx (centralRetainedGCx G hfinite) 3).toCC.d 1 (1 + 1)).hom φ = 0 ↔
      ∀ y, asForm2 G hfinite φ ((centralRetainedGCx G hfinite).d 1 2 rfl y) = 0 := by
  constructor
  · intro h y
    have hy := dual_d12_apply G hfinite φ y
    rw [h, neg_sgn_one, one_smul] at hy
    exact hy.symm
  · intro h
    apply LinearMap.ext
    intro y
    have hy := dual_d12_apply G hfinite φ y
    rw [neg_sgn_one, one_smul, h y] at hy
    exact hy

/-- **The free coordinate of degree two is a dual cocycle.** PROVED. -/
theorem freeCoord2Dual_closed :
    ((dualCx (centralRetainedGCx G hfinite) 3).toCC.d 1 (1 + 1)).hom
      (freeCoord2Dual G hfinite H) = 0 :=
  (dual_closed_iff G hfinite _).2 fun y =>
    (freeCoord2_boundary G hfinite H y :
      freeCoord2 G hfinite H (((retainedCentralComplex G hfinite).d 1 2).hom y) = 0)

/-- `evD` of the class of the free coordinate is one. PROVED. -/
theorem evD_freeCoord2Dual :
    evD G hfinite H (cls _ 1 (freeCoord2Dual G hfinite H) (freeCoord2Dual_closed G hfinite H)) =
      1 := by
  unfold evD
  rw [homologyFunctional_cls, evalE2_apply]
  exact freeCoord2_e2 G hfinite H

/-- **Unimodularity of the free-line pairing** (tex 4015–4017): `evD` is a unit on every
free-line generator of the first cohomology of the dual complex. PROVED. -/
theorem isUnit_evD {ψ : (dualCx (centralRetainedGCx G hfinite) 3).toCC.homology 1}
    (hψ : IsFreeLineGenerator ℤ_[2] ψ) : IsUnit (evD G hfinite H ψ) := by
  have h := functional_apply (evD G hfinite H) hψ
    (cls _ 1 (freeCoord2Dual G hfinite H) (freeCoord2Dual_closed G hfinite H))
  rw [evD_freeCoord2Dual] at h
  exact isUnit_iff_exists_inv'.mpr ⟨_, h.symm⟩

/-- **The free coefficient is preserved by a linear isomorphism.** PROVED. -/
theorem freeCoeff_linearEquiv {M N : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup N]
    [Module ℤ_[2] N] (f : M ≃ₗ[ℤ_[2]] N) {g : M} (hg : IsFreeLineGenerator ℤ_[2] g) (y : M) :
    freeCoeff (hg.map_linearEquiv f) (f y) = freeCoeff hg y := by
  apply freeCoeff_eq_of
  have h := map_mem_torsion f.toLinearMap (freeCoeff_spec hg y)
  simpa using h

end SelfDual

/-! ### The central functional -/

section CentralFunctional

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} {G : GenuineKummerData K E₀ hZ}
  {hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n)}
  (H : CalibrationCohomologyShape (compactCentralComplex G))
  {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1} {j vL : ℤ}

/-- **The transported class** `c_K(κ(L m P))` as a degree-one cycle of the retained model.
Kind: definition. -/
def kummerTransportCycle (D : RetainedPointData G κ j vL) (m : ℤ) :
    (retainedCentralComplex G hfinite).X 1 :=
  Classical.choose (cls_surjective (retainedCentralComplex G hfinite) 1
    ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P)))))

/-- The transported class is a cycle. PROVED. -/
theorem kummerTransportCycle_closed (D : RetainedPointData G κ j vL) (m : ℤ) :
    ((retainedCentralComplex G hfinite).d 1 (1 + 1)).hom (kummerTransportCycle D m) = 0 :=
  Classical.choose (Classical.choose_spec (cls_surjective (retainedCentralComplex G hfinite) 1
    ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))))))

/-- The class of the transported cycle is `c_K(κ(L m P))`. PROVED. -/
theorem cls_kummerTransportCycle (D : RetainedPointData G κ j vL) (m : ℤ) :
    cls (retainedCentralComplex G hfinite) 1 (kummerTransportCycle D m)
      (kummerTransportCycle_closed D m) =
        (compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))) :=
  Classical.choose_spec (Classical.choose_spec (cls_surjective (retainedCentralComplex G hfinite)
    1 ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))))))

/-- **The central functional** `λ₀ = PD(−, c_K z₀)` (tex 3902, 3976): the image under the
duality homotopy equivalence `e` of the transported cycle, read as a form on degree two.
Kind: definition. -/
def kummerCentralFunctional
    (e : HomotopyEquiv (retainedCentralComplex G hfinite)
      (dualCx (centralRetainedGCx G hfinite) 3).toCC)
    (D : RetainedPointData G κ j vL) (m : ℤ) :
    (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  asForm2 G hfinite ((e.hom.f 1).hom (kummerTransportCycle D m))

/-- **The central functional is closed** (`λ₀ ∘ d = 0`). PROVED. -/
theorem kummerCentralFunctional_closed
    (e : HomotopyEquiv (retainedCentralComplex G hfinite)
      (dualCx (centralRetainedGCx G hfinite) 3).toCC)
    (D : RetainedPointData G κ j vL) (m : ℤ) :
    kummerCentralFunctional e D m ∘ₗ ((retainedCentralComplex G hfinite).d 1 2).hom = 0 := by
  have hc := map_closed _ e.hom 1 (kummerTransportCycle_closed D m)
  have h := (dual_closed_iff G hfinite _).1 hc
  apply LinearMap.ext
  intro y
  exact h y

/-- **The value of the central functional on the free generator** is `evD` of the image of the
transported class. PROVED. -/
theorem kummerCentralFunctional_e2
    (e : HomotopyEquiv (retainedCentralComplex G hfinite)
      (dualCx (centralRetainedGCx G hfinite) 3).toCC)
    (D : RetainedPointData G κ j vL) (m : ℤ) :
    kummerCentralFunctional e D m (e2 G hfinite H) =
      evD G hfinite H ((HomologicalComplex.homologyMap e.hom 1).hom
        ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))))) := by
  have h1 := cls_naturality (retainedCentralComplex G hfinite) e.hom 1
    (kummerTransportCycle D m) (kummerTransportCycle_closed D m)
  have h2 := homologyFunctional_cls (dualCx (centralRetainedGCx G hfinite) 3).toCC 1
    (evalE2 G hfinite H) (evalE2_boundary G hfinite H) _
    (map_closed _ e.hom 1 (kummerTransportCycle_closed D m))
  have h3 : cls (retainedCentralComplex G hfinite) 1 (kummerTransportCycle D m)
      (kummerTransportCycle_closed D m) =
        (compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))) :=
    cls_kummerTransportCycle D m
  rw [← h3]
  change _ = homologyFunctional _ 1 (evalE2 G hfinite H) (evalE2_boundary G hfinite H)
    ((HomologicalComplex.homologyMap e.hom 1).hom (cls _ 1 _ (kummerTransportCycle_closed D m)))
  rw [h1, h2]
  rfl

/-- **The valuation of the functional coefficient, from the integral self-duality**
(tex 3977–3982, 4015–4017, 4061–4062): `v₂ b₀ = j + vL + v₂ m` for
`b₀ = λ₀(e2)`, `λ₀ = kummerCentralFunctional e D m`. PROVED. -/
theorem v2_centralB0_selfDual
    (e : HomotopyEquiv (retainedCentralComplex G hfinite)
      (dualCx (centralRetainedGCx G hfinite) 3).toCC)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    v2 ((kummerCentralFunctional e D m (e2 G hfinite H) : ℤ_[2]) : ℚ_[2]) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have := e.quasiIso_hom
  -- the cohomology isomorphism of `e` in degree one
  let φ : (retainedCentralComplex G hfinite).homology 1 ≃ₗ[ℤ_[2]]
      (dualCx (centralRetainedGCx G hfinite) 3).toCC.homology 1 :=
    (asIso (HomologicalComplex.homologyMap e.hom 1)).toLinearEquiv
  have hg : IsFreeLineGenerator ℤ_[2] (retainedKummer (hfinite := hfinite) κ D.gen) :=
    D.hκ.map_linearEquiv (compEquiv1 G hfinite).symm
  have hψ : IsFreeLineGenerator ℤ_[2] (φ (retainedKummer (hfinite := hfinite) κ D.gen)) :=
    hg.map_linearEquiv φ
  obtain ⟨y, hy⟩ : ∃ y, (compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))) = y :=
    ⟨_, rfl⟩
  have hval := functional_apply (evD G hfinite H) hψ (φ y)
  have hφy : (HomologicalComplex.homologyMap e.hom 1).hom y = φ y := rfl
  rw [kummerCentralFunctional_e2, hy, hφy, hval, freeCoeff_linearEquiv φ hg y]
  -- the free coefficient of the transported class
  let cKr : (retainedCentralComplex G hfinite).homology 1 →ₗ[ℤ_[2]]
      (retainedCentralComplex G hfinite).homology 1 :=
    (compEquiv1 G hfinite).symm.toLinearMap ∘ₗ D.cK ∘ₗ (compEquiv1 G hfinite).toLinearMap
  have hyc : y = cKr (retainedKummer (hfinite := hfinite) κ ((D.L * m) • D.P)) := by
    rw [← hy]
    change _ = (compEquiv1 G hfinite).symm (D.cK ((compEquiv1 G hfinite)
      ((compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P)))))
    rw [LinearEquiv.apply_symm_apply]
  have hcKr : ∀ z, cKr (cKr z) = z := fun z => by simp [cKr, D.hcK]
  have hkey : freeCoeff hg y = ((D.L * m * D.nP : ℤ) : ℤ_[2]) *
      freeCoeff hg (cKr (retainedKummer (hfinite := hfinite) κ D.gen)) := by
    rw [hyc]
    exact (freeCoeff_map_endo hg cKr _).trans
      (by rw [freeCoeff_map_zsmul _ hg D.hnP (D.L * m)])
  have hsgn : IsUnit (freeCoeff hg (cKr (retainedKummer (hfinite := hfinite) κ D.gen))) := by
    rcases freeCoeff_involution hg cKr hcKr with h | h <;> rw [h]
    · exact isUnit_one
    · exact isUnit_one.neg
  rw [hkey, PadicInt.coe_mul, PadicInt.coe_mul, v2_mul, v2_mul,
    v2_isUnit (isUnit_evD G hfinite H hψ), add_zero, v2_isUnit hsgn, add_zero,
    v2_three D.hL hm D.hnP0, D.hvL, D.hj]
  congr 1
  ring

end CentralFunctional

end ZInQ.Manuscript.RC.CalPoint

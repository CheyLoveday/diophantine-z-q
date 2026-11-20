import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointRetained

/-!
# Theorem 5.3, Lane RC34: the point half of the calibration on the retained central model

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, tex 3895–3986), Definition
`ex:arith-coordinate` (tex 3877–3892) and the proof of Proposition
`ex:arith-central-calibration` (tex 4005–4021, 4057–4064):

> "the actual central Kummer comparison `i` satisfies `z₀ = i(LmP)`,
> `(λ_z)₀(i x) = PD_K(x, c_K(LmP))` … On a rank-one Mordell–Weil free lattice, both free-line
> coefficients consequently have valuation `j_rc(h,k) + v₂(Lm)`." (tex 3899–3907)
>
> "The central class `Lm_i P_{h,k}^{rc}` and its paired functional each have free-coordinate
> valuation `j_rc(h,k) + v₂(Lm_i)`." (tex 4061–4062)

Lane RC35's Knudsen–Mumford identification of the calibration block is built from a degree-one
cycle `z₀` and a closed degree-two functional `λ₀` of the RC53 group's retained central model,
with class coefficient `a₀ = retainedA0 z₀` (the free-line coordinate of `z₀`) and functional
coefficient `b₀ = retainedB0 λ₀` (the value of `λ₀` on the degree-two free generator), and
`central (a b u₀) = a₀ b₀`. This file supplies the central class and the valuations.

* `compEquiv1`, `compEquiv2`: the cohomology isomorphisms of the retained comparison.
* `RetainedPointData G hfinite H κ j vL`: the point data at an address over the compact central
  complex (the fixed multiplier `L` with `v₂L = vL`, the point `P` with index valuation `j`, the
  Kummer identification of the free lattice for the Kummer map `κ`, the conjugate-dual
  transport `c_K`); `RetainedPointData.toFreeLine`: its transport to the retained model, a
  `FreeLinePointData` for any unimodular pairing `PDr` of the retained free lines.
* `kummerCentralCycle`: a degree-one cycle of the retained model whose class maps to `κ(L m P)`
  (`cls_kummerCentralCycle`); `kummerCentralCycle_closed`.
* `retainedA0_kummerCentralCycle` and **`v2_centralA0`**: the free-line coordinate of the central
  class has valuation `j + vL + v₂ m` (tex 3905–3907, 4061–4062).
* **`v2_centralB0`**: for any closed functional `λ₀` on degree two whose value on the free
  generator is the pairing of its class with `c_K(κ(LmP))` (the cochain form of
  `λ₀ = PD(−, c_K z₀)`), the functional coefficient has valuation `j + vL + v₂ m`; the pairing is
  any pairing of the retained free lines that is unimodular (tex 4015–4017).
* `v2_centralA0_mul_B0`: `v₂ (a₀ b₀) = 2 (j + vL + v₂ m)` — the point half of the Kummer
  valuation (tex 4063–4064).

Kinds: definitions and PROVED (conditional on the fields of `RetainedPointData`, each with its
kind; the unimodularity of the pairing is a hypothesis here, discharged in
`CalPointKummer`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open CategoryTheory
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Height (IsFreeGenerator)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve
  centralFullTorsion)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape retainedCentralComplex
  retainedCentralComparison retainedCentralComparison_quasiIso retainedCentralCoordinates)
open ZInQ.Manuscript.RC53Assist.CentralKummer (compactKummerComplex)
open ZInQ.Contrib.CloudB3RC53.Calibration (v2_mul v2_intCast)

attribute [local instance] Nat.fact_prime_two

/-! ### Valuations of `2`-adic integers -/

section Valuations

/-- A unit of `ℤ₂` has valuation zero in `ℚ₂`. PROVED. -/
theorem v2_isUnit {u : ℤ_[2]} (hu : IsUnit u) : v2 (u : ℚ_[2]) = 0 := by
  obtain ⟨u, rfl⟩ := hu
  rw [ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ u.ne_zero,
    ZInQ.Contrib.RC53Assist.Calibration.valuation_unit_padicInt u]
  rfl

/-- The valuation of an integer read in `ℤ₂ ⊆ ℚ₂`. PROVED. -/
theorem v2_intCast_padicInt {n : ℤ} (hn : n ≠ 0) :
    v2 (((n : ℤ_[2]) : ℚ_[2])) = (((padicValInt 2 n : ℕ) : ℤ) : WithTop ℤ) := by
  rw [PadicInt.coe_intCast]
  exact v2_intCast hn

/-- `v₂ (L m n) = v₂ L + v₂ m + v₂ n` for nonzero integers. PROVED. -/
theorem v2_three {L m n : ℤ} (hL : L ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    v2 ((((L * m * n : ℤ) : ℤ_[2]) : ℚ_[2])) =
      ((((padicValInt 2 L : ℕ) : ℤ) + ((padicValInt 2 m : ℕ) : ℤ) +
        ((padicValInt 2 n : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [v2_intCast_padicInt (mul_ne_zero (mul_ne_zero hL hm) hn),
    padicValInt.mul (mul_ne_zero hL hm) hn, padicValInt.mul hL hm]
  push_cast
  rfl

end Valuations

/-! ### The point data at an address, transported to the retained model -/

section Transport

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

/-- **The first cohomology of the retained model is that of the compact central complex**
(the retained comparison is a quasi-isomorphism). Kind: definition. -/
def compEquiv1 :
    (retainedCentralComplex G hfinite).homology 1 ≃ₗ[ℤ_[2]] (compactCentralComplex G).homology 1 :=
  haveI := retainedCentralComparison_quasiIso G hfinite
  (asIso (HomologicalComplex.homologyMap (retainedCentralComparison G hfinite) 1)).toLinearEquiv

/-- The same in degree two. Kind: definition. -/
def compEquiv2 :
    (retainedCentralComplex G hfinite).homology 2 ≃ₗ[ℤ_[2]] (compactCentralComplex G).homology 2 :=
  haveI := retainedCentralComparison_quasiIso G hfinite
  (asIso (HomologicalComplex.homologyMap (retainedCentralComparison G hfinite) 2)).toLinearEquiv

/-- **The point data of the calibration at an address, over the compact central complex**
(tex 2411–2416, 3073–3085, 3895–3986, 4005–4021), for a Kummer map
`κ : E^{(h)}(K) → H¹(C_K)`:

* `L`, `hL`, `hvL`: the fixed multiplier of (H11), `v₂L = vL` (3073–3085, 3897; definition).
* `P`: the point; for the text the `χ_h`-weighted conductor-`|h|` ring-class point in
  `E^{(h)}(K)` (2411–2416, 3904; data).
* `gen`, `hgen`: a free generator of `E^{(h)}(K)` modulo torsion (4020–4021; input, rank one).
* `nP`, `hnP`, `hnP0`, `hj`: `P ≡ nP · gen`, `nP ≠ 0`, `v₂ nP = j`; `j_rc` is the index
  valuation (2416; definition).
* `hκ`: `κ(gen)` generates `H¹(C_K)` modulo torsion (3905, 4007–4014; GLUE, Kummer sequence and
  finite `Ш`).
* `cK`, `hcK`: the conjugate-dual transport on `H¹(C_K)`, involutive (3904, 3977–3979; data,
  named).

Kind: definition (hypothesis structure); non-vacuity: `RetainedPointData.ofGenerator`
(`CalPointKmIdent`). -/
structure RetainedPointData (κ : (centralCurve G).toAffine.Point →+
    (compactCentralComplex G).homology 1) (j vL : ℤ) where
  /-- the fixed multiplier `L` -/
  L : ℤ
  /-- `L ≠ 0` -/
  hL : L ≠ 0
  /-- `v₂ L = vL` -/
  hvL : ((padicValInt 2 L : ℕ) : ℤ) = vL
  /-- the point -/
  P : (centralCurve G).toAffine.Point
  /-- a free generator of the rank-one lattice -/
  gen : (centralCurve G).toAffine.Point
  /-- it is a free generator -/
  hgen : IsFreeGenerator gen
  /-- the coefficient of the point -/
  nP : ℤ
  /-- `P ≡ nP · gen` modulo torsion -/
  hnP : IsOfFinAddOrder (P - nP • gen)
  /-- the point is not torsion -/
  hnP0 : nP ≠ 0
  /-- `j` is the index valuation of the point -/
  hj : ((padicValInt 2 nP : ℕ) : ℤ) = j
  /-- the Kummer map carries the free generator to a free-line generator -/
  hκ : IsFreeLineGenerator ℤ_[2] (κ gen)
  /-- the conjugate-dual transport -/
  cK : (compactCentralComplex G).homology 1 →ₗ[ℤ_[2]] (compactCentralComplex G).homology 1
  /-- it is involutive -/
  hcK : ∀ y, cK (cK y) = y

variable {G hfinite H}

/-- The Kummer map read in the retained model. Kind: definition. -/
def retainedKummer (κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1) :
    (centralCurve G).toAffine.Point →+ (retainedCentralComplex G hfinite).homology 1 :=
  (compEquiv1 G hfinite).symm.toLinearMap.toAddMonoidHom.comp κ

/-- **The point data transported to the retained model**: for any pairing `PDr` of the retained
free lines and any free-line generator `g₂` of the second cohomology with `PDr g₂` unimodular on
the image of the free generator, a `FreeLinePointData`. Kind: definition. -/
def RetainedPointData.toFreeLine
    {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1} {j vL : ℤ}
    (D : RetainedPointData G κ j vL)
    (PDr : (retainedCentralComplex G hfinite).homology 2 →ₗ[ℤ_[2]]
      (retainedCentralComplex G hfinite).homology 1 →ₗ[ℤ_[2]] ℤ_[2])
    (g₂ : (retainedCentralComplex G hfinite).homology 2) (hg₂ : IsFreeLineGenerator ℤ_[2] g₂)
    (hPD : IsUnit (PDr g₂ (retainedKummer (hfinite := hfinite) κ D.gen))) :
    FreeLinePointData ((retainedCentralComplex G hfinite).homology 1)
      ((retainedCentralComplex G hfinite).homology 2) (centralCurve G).toAffine.Point
      (retainedKummer (hfinite := hfinite) κ) PDr j vL where
  L := D.L
  hL := D.hL
  hvL := D.hvL
  P := D.P
  gen := D.gen
  hgen := D.hgen
  nP := D.nP
  hnP := D.hnP
  hnP0 := D.hnP0
  hj := D.hj
  hκ := D.hκ.map_linearEquiv (compEquiv1 G hfinite).symm
  cK := (compEquiv1 G hfinite).symm.toLinearMap ∘ₗ D.cK ∘ₗ (compEquiv1 G hfinite).toLinearMap
  hcK := fun y => by simp [D.hcK]
  g₂ := g₂
  hg₂ := hg₂
  hPD := hPD

end Transport

/-! ### The central class and the class coefficient `a₀` -/

section ClassSide

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} {G : GenuineKummerData K E₀ hZ}
  {hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n)}
  (H : CalibrationCohomologyShape (compactCentralComplex G))
  {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1} {j vL : ℤ}

/-- **The central class** (tex 3901: `z₀ = i(LmP)`): a degree-one cycle of the retained model
whose class is the preimage of `κ(L m P)`. Kind: definition. -/
def kummerCentralCycle (D : RetainedPointData G κ j vL) (m : ℤ) :
    (retainedCentralComplex G hfinite).X 1 :=
  Classical.choose (cls_surjective (retainedCentralComplex G hfinite) 1
    ((compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P))))

/-- **The central class is a cycle.** PROVED. -/
theorem kummerCentralCycle_closed (D : RetainedPointData G κ j vL) (m : ℤ) :
    ((retainedCentralComplex G hfinite).d 1 (1 + 1)).hom (kummerCentralCycle D m) = 0 :=
  Classical.choose (Classical.choose_spec (cls_surjective (retainedCentralComplex G hfinite) 1
    ((compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P)))))

/-- **The class of the central cycle is `κ(L m P)`** (read in the retained model). PROVED. -/
theorem cls_kummerCentralCycle (D : RetainedPointData G κ j vL) (m : ℤ) :
    cls (retainedCentralComplex G hfinite) 1 (kummerCentralCycle D m)
      (kummerCentralCycle_closed D m) = (compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P)) :=
  Classical.choose_spec (Classical.choose_spec (cls_surjective (retainedCentralComplex G hfinite)
    1 ((compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P)))))

/-- **The class coefficient `a₀` is the free coefficient of the central class up to a unit**:
`a₀ = (L m nP) · ev1 (κ gen)`, with `ev1 (κ gen)` a unit. PROVED. -/
theorem freeCoord1_kummerCentralCycle (D : RetainedPointData G κ j vL) (m : ℤ) :
    freeCoord1 G hfinite H (kummerCentralCycle D m) =
      ((D.L * m * D.nP : ℤ) : ℤ_[2]) *
        ev1 G hfinite H (retainedKummer (hfinite := hfinite) κ D.gen) := by
  have hg : IsFreeLineGenerator ℤ_[2] (retainedKummer (hfinite := hfinite) κ D.gen) :=
    D.hκ.map_linearEquiv (compEquiv1 G hfinite).symm
  rw [freeCoord1_eq_freeCoeff G hfinite H hg _ (kummerCentralCycle_closed D m),
    cls_kummerCentralCycle]
  congr 1
  exact freeCoeff_map_zsmul (retainedKummer (hfinite := hfinite) κ) hg D.hnP (D.L * m)

/-- **The valuation of the class coefficient** (tex 3905–3907, 4061–4062):
`v₂ a₀ = j + vL + v₂ m`. PROVED. -/
theorem v2_centralA0 (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    v2 ((freeCoord1 G hfinite H (kummerCentralCycle D m) : ℤ_[2]) : ℚ_[2]) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hg : IsFreeLineGenerator ℤ_[2] (retainedKummer (hfinite := hfinite) κ D.gen) :=
    D.hκ.map_linearEquiv (compEquiv1 G hfinite).symm
  rw [freeCoord1_kummerCentralCycle H D m, PadicInt.coe_mul, v2_mul,
    v2_isUnit (isUnit_ev1 G hfinite H hg), add_zero, v2_three D.hL hm D.hnP0, D.hvL, D.hj]
  congr 1
  ring

end ClassSide

/-! ### The functional coefficient `b₀` -/

section FunctionalSide

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} {G : GenuineKummerData K E₀ hZ}
  {hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactCentralComplex G).homology n)}
  (H : CalibrationCohomologyShape (compactCentralComplex G))
  {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1} {j vL : ℤ}

/-- **The valuation of the functional coefficient** (tex 3902, 3976–3982, 4015–4017, 4061–4062).
For a pairing `PDr` of the retained cohomology that is unimodular on the free lines and a closed
functional `λ₀` on degree two whose value on the free generator `e2` is the pairing of the class
of `e2` with the transported class `c_K(κ(L m P))` (the cochain form of
`λ₀ = PD(−, c_K z₀)`), `v₂ b₀ = j + vL + v₂ m`. PROVED. -/
theorem v2_centralB0 (D : RetainedPointData G κ j vL)
    (PDr : (retainedCentralComplex G hfinite).homology 2 →ₗ[ℤ_[2]]
      (retainedCentralComplex G hfinite).homology 1 →ₗ[ℤ_[2]] ℤ_[2])
    (g₂ : (retainedCentralComplex G hfinite).homology 2) (hg₂ : IsFreeLineGenerator ℤ_[2] g₂)
    (hPD : IsUnit (PDr g₂ (retainedKummer (hfinite := hfinite) κ D.gen)))
    (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) {m : ℤ} (hm : m ≠ 0)
    (hlam : lam0 (e2 G hfinite H) =
      PDr (cls _ 2 (e2 G hfinite H) (e2_closed G hfinite H))
        ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))))) :
    v2 ((lam0 (e2 G hfinite H) : ℤ_[2]) : ℚ_[2]) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  let F := D.toFreeLine PDr g₂ hg₂ hPD
  have hF : (compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))) = F.cK (F.zc m) := by
    change _ = (compEquiv1 G hfinite).symm (D.cK ((compEquiv1 G hfinite)
      ((compEquiv1 G hfinite).symm (κ ((D.L * m) • D.P)))))
    rw [LinearEquiv.apply_symm_apply]
  have h1 : lam0 (e2 G hfinite H) =
      freeCoeff hg₂ (cls _ 2 (e2 G hfinite H) (e2_closed G hfinite H)) * F.funCoeff m := by
    rw [hlam, hF]
    exact functional_apply (PDr.flip (F.cK (F.zc m))) hg₂ _
  obtain ⟨ε, hε⟩ := F.funCoeff_associated m
  rw [h1, hε, F.classCoeff_eq, PadicInt.coe_mul, PadicInt.coe_mul, v2_mul, v2_mul,
    v2_isUnit (isUnit_freeCoeff_e2 G hfinite H hg₂), v2_isUnit ε.isUnit, zero_add, zero_add]
  change v2 ((((D.L * m * D.nP : ℤ) : ℤ_[2]) : ℚ_[2])) = _
  rw [v2_three D.hL hm D.hnP0, D.hvL, D.hj]
  congr 1
  ring

/-- **The point half of the Kummer valuation** (tex 4063–4064): `v₂ (a₀ b₀) = 2 (j + vL + v₂m)`.
PROVED. -/
theorem v2_centralA0_mul_B0 (D : RetainedPointData G κ j vL)
    (PDr : (retainedCentralComplex G hfinite).homology 2 →ₗ[ℤ_[2]]
      (retainedCentralComplex G hfinite).homology 1 →ₗ[ℤ_[2]] ℤ_[2])
    (g₂ : (retainedCentralComplex G hfinite).homology 2) (hg₂ : IsFreeLineGenerator ℤ_[2] g₂)
    (hPD : IsUnit (PDr g₂ (retainedKummer (hfinite := hfinite) κ D.gen)))
    (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) {m : ℤ} (hm : m ≠ 0)
    (hlam : lam0 (e2 G hfinite H) =
      PDr (cls _ 2 (e2 G hfinite H) (e2_closed G hfinite H))
        ((compEquiv1 G hfinite).symm (D.cK (κ ((D.L * m) • D.P))))) :
    v2 (((freeCoord1 G hfinite H (kummerCentralCycle D m) * lam0 (e2 G hfinite H) : ℤ_[2]) :
      ℚ_[2])) = ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [PadicInt.coe_mul, v2_mul, v2_centralA0 H D hm,
    v2_centralB0 H D PDr g₂ hg₂ hPD lam0 hm hlam, ← WithTop.coe_add]
  congr 1
  ring

end FunctionalSide

end ZInQ.Manuscript.RC.CalPoint

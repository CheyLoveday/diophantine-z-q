import ZInQKernel.Contrib.OneProof.RC.Local.TameQuasiIsoLow
import ZInQKernel.Contrib.RC53Assist.ResidualBounds.StageBounds
import ZInQKernel.Contrib.OneProof.RC.Limits.LocalPrints

/-!
# Lane RC31, round 6: the tame comparison in degrees two and higher

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306 and 5026–5037.

* Degrees `≥ 3` (PROVED): `quasiIsoAt_toCC_of_subsingleton` (a chain map is a quasi-isomorphism
  in a degree where the source cohomology and the target term vanish);
  `quasiIsoAt_tameCochainMap_of_ge_three` (the model is zero there, so `QuasiIsoAt` follows from
  the vanishing of the continuous cohomology); `quasiIsoAt_tameCochainMap_of_ge_three_milne` for
  the local Galois group `Gloc F v` of a number field at a finite place, from the tree PRINT
  `MilneLocalDimensionTwo` (Milne, ADT I, Remark 1.12).
* Degree `2` at `g = 1` (definitions and PROVED reduction): the explicit second cohomology
  `ContH2 = Z² ⧸ d¹C¹` of the continuous cochains, the map `tameH2 : ContH2 → coker(Φ − q)`
  induced by `tameE` (well defined by `tameE_d_one`), and
  `quasiIsoAt_tameCochainMap_two_of_bijective`: bijectivity of `tameH2` gives `QuasiIsoAt 2`.
* Degree `2` by counting (PROVED): `card_coker_eq_card_ker`, `card_contZ0` (`|H⁰| = |ker(Φ − 1)|`),
  `card_H1WrelK` (`|H¹| = |coker(Φ − 1)| · |ker(Φ − q)|`), `card_contH2_eq` (an Euler
  characteristic identity `|H⁰| · |H²| = |H¹|` gives `|H²| = |coker(Φ − q)|`), and
  `quasiIsoAt_tameCochainMap_two_of_surjective`: with that identity, surjectivity of `tameH2`
  suffices.
* Cohomology comparison (PROVED): `card_homology_eq_subquot`, `card_contZ0_homology`,
  `card_contH1_homology`, `card_contH2_homology` (orders of `Hⁿ` of the continuous cochains in
  degrees `0, 1, 2` are those of the explicit groups).
* From the tree PRINT `MilneADT_I_2_8` (Milne, ADT I.2.8; finite extensions of `ℚ_p`,
  `𝔽₂`-coefficients), PROVED: `euler_of_milne` (`|H⁰| · |H²| = |H¹|` for `p ≠ 2`) and
  `subsingleton_homology_of_milne` (`Hⁿ = 0` for `n > 2`).
* GLUE `TameH2Surjective`: for the actual local Galois group at an odd place, with inertia
  acting trivially on a finite module of `2`-power exponent, the explicit map `tameH2` is
  surjective (a compatibility claim about the explicit degree-two component, not a printed
  statement).
* Assembly (PROVED): `quasiIso_tameCochainMap_of_prints` (finite extension of `ℚ_p`, `p ≠ 2`,
  coefficients `ZMod 2`; from `MilneADT_I_2_8` and `TameH2Surjective`), and
  `quasiIso_tameCochainMap_of_euler` (completion of a number field at a finite place, any
  coefficient field; from `MilneLocalDimensionTwo`, with the Euler identity and the
  surjectivity of `tameH2` as hypotheses).

Kinds: definitions, PROVED, and one GLUE statement (`TameH2Surjective`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.TameBijective
open ZInQ.Contrib.RC53Assist.ResidualBounds (MilneLocalDimensionTwo)

/-! ### Degrees at least three -/

section VanishingDegrees

variable {R : Type} [CommRing R] {A B : GCx R}

/-- **A chain map is a quasi-isomorphism where both sides vanish** (tex 3470–3480): if the
source cohomology in degree `n` and the target term in degree `n` are subsingletons, then
`GHom.toCC f` is a quasi-isomorphism in degree `n`. Kind: PROVED. -/
theorem quasiIsoAt_toCC_of_subsingleton (f : GHom A B) (n : ℤ)
    (hA : Subsingleton (A.toCC.homology n)) (hB : Subsingleton (B.X n)) :
    QuasiIsoAt (GHom.toCC f) n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hB' : Subsingleton (B.toCC.homology n) :=
    ZInQ.Contrib.RC53Assist.ResidualBounds.homology_subsingleton_of_term B n hB
  exact Limits.isIso_of_source_target_iso_zero _
    (@ModuleCat.isZero_of_subsingleton R _ _ hA).isoZero
    (@ModuleCat.isZero_of_subsingleton R _ _ hB').isoZero

end VanishingDegrees

section HighDegrees

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- **Degrees `≥ 3`** (tex 3470–3480): the tame model vanishes in degrees `≥ 3`, so
`tameCochainMap` is a quasi-isomorphism in a degree `n > 2` as soon as the continuous
cohomology `Hⁿ(G, M)` (the cohomology of `natCx (contCochains R G M)`) vanishes. Any `g`.
Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_of_ge_three (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (n : ℤ) (hn : 2 < n)
    (hH : Subsingleton ((natCx (contCochains R G M)).toCC.homology n)) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel)) n :=
  quasiIsoAt_toCC_of_subsingleton _ n hH
    (cx3X_subsingleton (A := R) (X0 := M) (X1 := M × M) (X2 := M) n (by omega) (by omega)
      (by omega))

end HighDegrees

section HighDegreesLocal

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction (Gloc F v) M] [SMulCommClass (Gloc F v) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc F v) M]

/-- **Degrees `≥ 3` for the local Galois group of a number field at a finite place**
(tex 3470–3480): from the tree PRINT `MilneLocalDimensionTwo` (Milne, ADT I, Remark 1.12:
`Hⁿ(G_v, M) = 0` for `n > 2` and finite discrete `M`), `tameCochainMap` is a
quasi-isomorphism in every degree `n > 2`, for any `g`. Kind: PROVED (from the PRINT). -/
theorem quasiIsoAt_tameCochainMap_of_ge_three_milne (hlcd : MilneLocalDimensionTwo)
    [Finite M] (Φ g : M →ₗ[R] M) (φ σ : Gloc F v) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (n : ℤ) (hn : 2 < n) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel)) n :=
  quasiIsoAt_tameCochainMap_of_ge_three Φ g φ σ q hq hΦ hgσ hg hcomm hrel n hn
    (hlcd F v R M inferInstance n hn)

end HighDegreesLocal

/-! ### Degree two at `g = 1` -/

section DegreeTwo

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

variable (R G M) in
/-- The continuous two-cocycles `Z² = ker d²` (tex 3470–3480). Kind: definition. -/
abbrev contZ2 : Submodule R ((contCochains R G M).X 2) :=
  LinearMap.ker ((contCochains R G M).d 2 3).hom

variable (R G M) in
/-- The continuous two-coboundaries `d¹C¹`, inside the two-cocycles (tex 3470–3480). Kind:
definition. -/
abbrev contB2 : Submodule R (contZ2 R G M) :=
  (LinearMap.range ((contCochains R G M).d 1 2).hom).comap (contZ2 R G M).subtype

variable (R G M) in
/-- The explicit second continuous cohomology `H² = Z² ⧸ d¹C¹` (tex 3470–3480). Kind:
definition. -/
abbrev ContH2 : Type := contZ2 R G M ⧸ contB2 R G M

/-- **`tameE` on coboundaries at `g = 1`** (tex 3470–3480): for `σ` acting trivially,
`E(dc) = (Φ − q) c(σ)`. Kind: PROVED (from `tameE_d` and `tameNorm_one`). -/
theorem tameE_d_one (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) (c : (contCochains R G M).X 1) :
    tameE Φ LinearMap.id φ σ q (((contCochains R G M).d 1 2).hom c) =
      frobQ Φ q (evalOne R M σ c) := by
  have e := tameE_d Φ LinearMap.id φ σ q hq hΦ (fun m => (hσ m).symm) (LinearMap.id_comp _)
    (comm_id Φ) hrel c
  rw [e]
  change -(LinearMap.id - LinearMap.id : M →ₗ[R] M) (evalOne R M φ c) +
    (Φ - tameNorm q (LinearMap.id : M →ₗ[R] M)) (evalOne R M σ c) = _
  rw [tameNorm_one q hq, sub_self, LinearMap.zero_apply, neg_zero, zero_add]

/-- The degree-two component on two-cocycles, at `g = 1` (tex 3470–3480). Kind:
definition. -/
def tameZ2 (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) : contZ2 R G M →ₗ[R] M :=
  tameE Φ LinearMap.id φ σ q ∘ₗ (contZ2 R G M).subtype

/-- **The comparison map on second cohomology at `g = 1`** (tex 3470–3480):
`H²_cont = Z² ⧸ d¹C¹ → coker(Φ − q) = H²(model)` (`cohD1_range`), induced by `tameE`.
Kind: definition (well defined by `tameE_d_one`). -/
def tameH2 (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    ContH2 R G M →ₗ[R] M ⧸ LinearMap.range (frobQ Φ q) :=
  Submodule.mapQ _ _ (tameZ2 Φ φ σ q) (by
    intro z hz
    obtain ⟨c, hc⟩ := hz
    refine ⟨evalOne R M σ c, ?_⟩
    exact (tameE_d_one Φ φ σ q hq hΦ hσ hrel c).symm.trans
      (congrArg (tameE Φ LinearMap.id φ σ q) hc))

/-- **Degree `2` at `g = 1`** (tex 3470–3480): if the map `tameH2` induced by `tameE` on
`H² = Z² ⧸ d¹C¹ → coker(Φ − q)` is bijective, then `tameCochainMap` is a quasi-isomorphism in
degree `2`. Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_two_of_bijective (Φ : M →ₗ[R] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m)
    (hgσ : ∀ m, (LinearMap.id : M →ₗ[R] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[R] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hb : Function.Bijective (tameH2 Φ φ σ q hq hΦ hσ hrel)) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ hg hcomm hrel)) 2 := by
  apply quasiIsoAt_toCC_of_elementwise _ 1 2 3 rfl rfl
  · intro z hz y hy
    let zc : contZ2 R G M := ⟨z, hz⟩
    let y' : M × M := y
    have hy' : frobQ Φ q y'.2 = tameE Φ LinearMap.id φ σ q z :=
      (tameFreeModel1_d1 Φ q hq y'.1 y'.2).symm.trans hy
    have h0 : tameH2 Φ φ σ q hq hΦ hσ hrel (Submodule.Quotient.mk zc) = 0 := by
      change (Submodule.Quotient.mk (tameZ2 Φ φ σ q zc) : M ⧸ LinearMap.range (frobQ Φ q)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨y'.2, hy'⟩
    have h1 := hb.1 (h0.trans (map_zero _).symm)
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, hx⟩
  · intro w _
    let w' : M := w
    obtain ⟨c, hc⟩ := hb.2 (Submodule.Quotient.mk w')
    induction c using Submodule.Quotient.induction_on with
    | H zc =>
      have hc' : (Submodule.Quotient.mk (tameZ2 Φ φ σ q zc) :
          M ⧸ LinearMap.range (frobQ Φ q)) = Submodule.Quotient.mk w' := hc
      rw [Submodule.Quotient.eq] at hc'
      obtain ⟨m, hm⟩ := hc'
      refine ⟨zc.1, zc.2, ((0 : M), m), ?_⟩
      exact hm.symm.trans (tameFreeModel1_d1 Φ q hq 0 m).symm

end DegreeTwo

/-! ### Degree two by counting -/

section CountingAlgebra

/-- For an endomorphism of a finite module, `|coker T| = |ker T|` (tex 3478–3480). Kind:
PROVED. -/
theorem card_coker_eq_card_ker {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    [Finite M] (T : M →ₗ[R] M) :
    Nat.card (M ⧸ LinearMap.range T) = Nat.card (LinearMap.ker T) := by
  have h1 := (LinearMap.range T).card_eq_card_quotient_mul_card
  have h2 := (LinearMap.ker T).card_eq_card_quotient_mul_card
  have h3 : Nat.card (M ⧸ LinearMap.ker T) = Nat.card (LinearMap.range T) :=
    Nat.card_congr T.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range T) := Nat.card_pos
  rw [h3] at h2
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h1, h2, mul_comm]

end CountingAlgebra

section EulerCount

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

variable (k G M) in
/-- The continuous zero-cocycles `H⁰ = ker d⁰` (tex 3470–3480). Kind: definition. -/
abbrev contZ0 : Submodule k ((contCochains k G M).X 0) :=
  LinearMap.ker ((contCochains k G M).d 0 1).hom

/-- **The order of `H⁰`** (tex 3470–3480): if `G` is topologically generated by `φ`, `σ` and a
subgroup acting trivially, and `σ` acts trivially, then `|H⁰(G, M)| = |ker(Φ − 1)|`. Kind:
PROVED (from `tame_H0_iff`). -/
theorem card_contZ0 [T1Space M] (Φ : M →ₗ[k] M) (φ σ : G) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (N : Subgroup G) (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤) :
    Nat.card (contZ0 k G M) = Nat.card (LinearMap.ker (frobOne Φ)) := by
  have key : ∀ a : (contCochains k G M).X 0,
      a ∈ contZ0 k G M ↔ evalZero k M a ∈ LinearMap.ker (frobOne Φ) := by
    intro a
    rw [LinearMap.mem_ker, LinearMap.mem_ker,
      tame_H0_iff Φ LinearMap.id φ σ hΦ (fun m => (hσ m).symm) N hN hgen a]
    change ((frobOne Φ) (evalZero k M a),
      (LinearMap.id - LinearMap.id : M →ₗ[k] M) (evalZero k M a)) = 0 ↔ _
    rw [sub_self, LinearMap.zero_apply]
    exact ⟨fun h => congrArg Prod.fst h, fun h => by rw [h]; rfl⟩
  refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨evalZero k M z.1, (key z.1).mp z.2⟩)
    ⟨?_, ?_⟩)
  · intro z z' h
    exact Subtype.ext (evalZero_injective (congrArg Subtype.val h))
  · rintro ⟨m, hm⟩
    obtain ⟨a, rfl⟩ := evalZero_surjective (R := k) (G := G) (M := M) m
    exact ⟨⟨a, (key a).mpr hm⟩, rfl⟩

/-- **The order of `H¹` at `g = 1`** (tex 3298–3306, 3470–3480): if the map `tameH1` induced by
`tameCochainMap` on `H¹` is bijective, then `|H¹(G, M)| = |coker(Φ − 1)| · |ker(Φ − q)|`.
Kind: PROVED (from `modelCoordH1_injective`, `modelCoordH1_surjective`). -/
theorem card_H1WrelK (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)
    (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hb1 : Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel)) :
    Nat.card (H1WrelK k G M) =
      Nat.card (M ⧸ LinearMap.range (frobOne Φ)) * Nat.card (LinearMap.ker (frobQ Φ q)) := by
  rw [Nat.card_congr (Equiv.ofBijective _ hb1), Nat.card_congr (Equiv.ofBijective _
    ⟨modelCoordH1_injective Φ φ q hq hΦ, modelCoordH1_surjective Φ φ q hq hΦ⟩), Nat.card_prod]
  have e1 : frobSub k M φ 1 = frobOne Φ := LinearMap.ext fun m => by
    rw [frobSub_apply, one_smul, LinearMap.sub_apply, LinearMap.id_apply, hΦ]
  have e2 : frobSub k M φ (q : k) = frobQ Φ q := LinearMap.ext fun m => by
    rw [frobSub_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hΦ]
  change Nat.card (M ⧸ LinearMap.range (frobSub k M φ 1)) *
    Nat.card (LinearMap.ker (frobSub k M φ (q : k))) = _
  rw [e1, e2]

/-- **The order of `H²` from the Euler characteristic** (tex 3470–3480; Tate's local Euler
characteristic, Milne ADT I.2.8, for `M` of order prime to `p`): if
`|H⁰| · |H²| = |H¹|` for the explicit continuous cohomology, then
`|H²(G, M)| = |coker(Φ − q)|`, given degrees `0` and `1` (`card_contZ0`, `card_H1WrelK`).
Kind: PROVED. -/
theorem card_contH2_eq [Finite M] [T1Space M] (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (N : Subgroup G) (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤)
    (hb1 : Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel))
    (heuler : Nat.card (contZ0 k G M) * Nat.card (ContH2 k G M) = Nat.card (H1WrelK k G M)) :
    Nat.card (ContH2 k G M) = Nat.card (M ⧸ LinearMap.range (frobQ Φ q)) := by
  rw [card_contZ0 Φ φ σ hΦ hσ N hN hgen, card_H1WrelK Φ φ σ q hq hΦ hσ hrel hb1,
    card_coker_eq_card_ker (frobOne Φ)] at heuler
  rw [card_coker_eq_card_ker (frobQ Φ q)]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos heuler

/-- **Surjectivity suffices in degree `2`, given the Euler characteristic** (tex 3470–3480):
under the hypotheses of `card_contH2_eq`, a surjective `tameH2` is bijective (equal finite
orders). Kind: PROVED. -/
theorem tameH2_bijective_of_surjective [Finite M] [T1Space M] (Φ : M →ₗ[k] M) (φ σ : G)
    (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (N : Subgroup G) (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤)
    (hb1 : Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel))
    (heuler : Nat.card (contZ0 k G M) * Nat.card (ContH2 k G M) = Nat.card (H1WrelK k G M))
    (hs : Function.Surjective (tameH2 Φ φ σ q hq hΦ hσ hrel)) :
    Function.Bijective (tameH2 Φ φ σ q hq hΦ hσ hrel) := by
  have hc := card_contH2_eq Φ φ σ q hq hΦ hσ hrel N hN hgen hb1 heuler
  have : Finite (ContH2 k G M) := Nat.finite_of_card_ne_zero (by
    rw [hc, card_coker_eq_card_ker]
    exact Nat.card_pos.ne')
  exact hs.bijective_of_nat_card_le hc.le

/-- **Degree `2` at `g = 1` from surjectivity and the Euler characteristic** (tex 3470–3480):
under the hypotheses of `card_contH2_eq`, if `tameH2` is surjective then `tameCochainMap` is a
quasi-isomorphism in degree `2`. Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_two_of_surjective [Finite M] [T1Space M] (Φ : M →ₗ[k] M)
    (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m)
    (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (N : Subgroup G) (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤)
    (hb1 : Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel))
    (heuler : Nat.card (contZ0 k G M) * Nat.card (ContH2 k G M) = Nat.card (H1WrelK k G M))
    (hs : Function.Surjective (tameH2 Φ φ σ q hq hΦ hσ hrel)) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ hg hcomm hrel)) 2 :=
  quasiIsoAt_tameCochainMap_two_of_bijective Φ φ σ q hq hΦ hσ hgσ hg hcomm hrel
    (tameH2_bijective_of_surjective Φ φ σ q hq hΦ hσ hrel N hN hgen hb1 heuler hs)

end EulerCount


/-! ### Cohomology comparison and the local Euler characteristic -/

section HomologyCards

/-- The order of the cohomology of an `ℕ`-indexed complex of modules in degree `j` is the order
of `ker d ⧸ im d` (tex 3470–3480). Kind: PROVED. -/
theorem card_homology_eq_subquot {k : Type} [CommRing k]
    (C : CochainComplex (ModuleCat.{0} k) ℕ) (i j l : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l) :
    Nat.card (C.homology j) = Nat.card (LinearMap.ker (C.d j l).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j l).hom).subtype) := by
  have e1 := (C.homologyIsoSc' i j l hi hl).toLinearEquiv
  have e2 := ((C.sc' i j l).moduleCatHomologyIso).toLinearEquiv
  have hr : LinearMap.range (C.sc' i j l).moduleCatToCycles =
      (LinearMap.range (C.sc' i j l).f.hom).comap
        (LinearMap.ker (C.sc' i j l).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  exact Nat.card_congr ((e1.trans e2).trans (Submodule.quotEquivOfEq _ _ hr)).toEquiv

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- `|H⁰|` of the continuous cochains is the order of the explicit zero-cocycles
(tex 3470–3480). Kind: PROVED. -/
theorem card_contZ0_homology :
    Nat.card ((contCochains k G M).homology 0) = Nat.card (contZ0 k G M) := by
  rw [card_homology_eq_subquot _ 0 0 1 (by simp) (by simp)]
  have hz : (contCochains k G M).d 0 0 = 0 := (contCochains k G M).shape 0 0 (by simp)
  have hb : (LinearMap.range ((contCochains k G M).d 0 0).hom).comap
      (LinearMap.ker ((contCochains k G M).d 0 1).hom).subtype = ⊥ := by
    rw [hz]
    ext x
    simp
  exact Nat.card_congr (Submodule.quotEquivOfEqBot _ hb).toEquiv

/-- `|H¹|` of the continuous cochains is the order of `H1WrelK = Z¹ ⧸ d⁰C⁰` (tex 3470–3480).
Kind: PROVED. -/
theorem card_contH1_homology :
    Nat.card ((contCochains k G M).homology 1) = Nat.card (H1WrelK k G M) := by
  rw [card_homology_eq_subquot _ 0 1 2 (by simp) (by simp)]
  have h : (LinearMap.range ((contCochains k G M).d 0 1).hom).comap
      (Z1K k G M).subtype = LinearMap.range (relaxedDK k G M) :=
    (LinearMap.range_codRestrict _ _ _).symm
  exact Nat.card_congr (Submodule.quotEquivOfEq _ _ h).toEquiv

/-- `|H²|` of the continuous cochains is the order of `ContH2 = Z² ⧸ d¹C¹` (tex 3470–3480).
Kind: PROVED. -/
theorem card_contH2_homology :
    Nat.card ((contCochains k G M).homology 2) = Nat.card (ContH2 k G M) := by
  rw [card_homology_eq_subquot _ 1 2 3 (by simp) (by simp)]

end HomologyCards

section MilneEuler

open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.ContBridge (continuousSMul_of_discrete hcontDisc
  contCohomologyLinearEquiv)

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]
  [FiniteDimensional ℚ_[p] F] (M : Type) [AddCommGroup M] [Module (ZMod 2) M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) (ZMod 2) M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M] [Finite M]

/-- **The local Euler characteristic for the explicit continuous cohomology** (tex 3470–3480):
from the tree PRINT `MilneADT_I_2_8` (Milne, ADT I.2.8, Tate), for a finite extension `F` of
`ℚ_p` with `p ≠ 2` and a finite discrete `𝔽₂[G_F]`-module `M`, `|H⁰| · |H²| = |H¹|`, through
`contCohomologyLinearEquiv` (Mathlib's `continuousCohomology` of a discrete module is the
cohomology of the continuous cochains). Kind: PROVED (from the PRINT). -/
theorem euler_of_milne (h28 : MilneADT_I_2_8) (hp : p ≠ 2) :
    Nat.card (contZ0 (ZMod 2) (Field.absoluteGaloisGroup F) M) *
        Nat.card (ContH2 (ZMod 2) (Field.absoluteGaloisGroup F) M) =
      Nat.card (H1WrelK (ZMod 2) (Field.absoluteGaloisGroup F) M) := by
  have : ContinuousSMul (ZMod 2) M := continuousSMul_of_discrete (ZMod 2) M
  obtain ⟨hfin, -, heu⟩ := h28 p F
    (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)
    (inferInstanceAs (Finite M)) (inferInstanceAs (DiscreteTopology M))
    (hcontDisc (ZMod 2) _ M)
  simp only [hp, ↓reduceIte, neg_zero] at heu
  have hc : ∀ n : ℕ,
      Nat.card ((contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M).homology n) =
        2 ^ Module.finrank (ZMod 2) (continuousCohomology n
          (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)) := by
    intro n
    have e := contCohomologyLinearEquiv (ZMod 2) (Field.absoluteGaloisGroup F) M n
    have : Module.Finite (ZMod 2) (continuousCohomology n
        (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)) := hfin n
    have : Finite (continuousCohomology n
        (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)) :=
      Module.finite_of_finite (ZMod 2)
    let _ := Fintype.ofFinite (continuousCohomology n
        (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M))
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank
      (K := ZMod 2) (V := continuousCohomology n
        (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)), ZMod.card]
  rw [← card_contZ0_homology, ← card_contH2_homology, ← card_contH1_homology, hc, hc, hc,
    ← pow_add]
  congr 1
  omega

include p in
/-- **Cohomological dimension two from Milne I.2.8** (tex 3470–3480): for a finite extension
`F` of `ℚ_p` and a finite discrete `𝔽₂[G_F]`-module `M`, the cohomology of
`natCx (contCochains (ZMod 2) G_F M)` vanishes in degrees `n > 2` (tree PRINT
`MilneADT_I_2_8`, through `contCohomologyLinearEquiv` and `natPositiveHomologyIso`). Kind:
PROVED (from the PRINT). -/
theorem subsingleton_homology_of_milne (h28 : MilneADT_I_2_8) (n : ℤ) (hn : 2 < n) :
    Subsingleton ((natCx (contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M)).toCC.homology
      n) := by
  have : ContinuousSMul (ZMod 2) M := continuousSMul_of_discrete (ZMod 2) M
  obtain ⟨-, hvan, -⟩ := h28 p F
    (TauCeti.ofDiscreteModule (ZMod 2) (Field.absoluteGaloisGroup F) M)
    (inferInstanceAs (Finite M)) (inferInstanceAs (DiscreteTopology M))
    (hcontDisc (ZMod 2) _ M)
  cases n with
  | negSucc n => omega
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hn
    cases n with
    | zero => norm_num at hn
    | succ n =>
      have hH := hvan (n + 1) (by omega)
      have : Subsingleton ((contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M).homology
          (n + 1)) :=
        (contCohomologyLinearEquiv (ZMod 2) (Field.absoluteGaloisGroup F) M
          (n + 1)).symm.injective.subsingleton
      exact (ZInQ.Contrib.RC53Assist.ResidualBounds.natPositiveHomologyIso
        (contCochains (ZMod 2) (Field.absoluteGaloisGroup F) M)
          n).toLinearEquiv.injective.subsingleton

end MilneEuler

/-! ### The remaining compatibility in degree two -/

open TauCeti ValuativeRel in
open ZInQ.Contrib.CloudB3RC53.TameQuotient in
/-- **The comparison is surjective on `H²` at a tame place** (tex 3470–3480; GLUE). For the
actual local Galois group `G_K` of a nonarchimedean local field `K` of odd residue
characteristic `p`, with `q = |𝓀|`, Iwasawa generators `φ` (an arithmetic Frobenius lift) and
`σ ∈ I` with the exact relation `φ σ φ⁻¹ = σ ^ q`, a closed normal pro-`p` subgroup `P ≤ I`
with `I = closure(⟨σ⟩ P)`, and a finite discrete module `M` of `2`-power exponent on which
inertia acts trivially (`g = 1`), the map `tameH2 : H²(G_K, M) → coker(Φ − q)` induced by the
relator component `tameE` is surjective. Sources: Neukirch–Schmidt–Wingberg, Cohomology of
Number Fields, Thm 7.5.3 and §7.3 (structure of the tame Galois group; local duality),
Serre, Galois Cohomology, II.5 (and I.3.3: `H^i(P, M) = 0` for `i > 0`), Serre, Local Fields,
XIII: by Hochschild–Serre for `P ⊴ G_K` and then for the tame inertia `I/P`,
`H²(G_K, M) ≅ H¹(G_K/I, Hom(I/P, M)) ≅ coker(Φ − q)`, the last map being evaluation of a
two-cocycle along the relator `φ σ φ⁻¹ σ^{−q}` (the free resolution of the tame quotient).
With equal finite orders (`card_contH2_eq`, from the Euler characteristic `euler_of_milne`),
surjectivity gives bijectivity. Mathematically implied by the degree-two part of
`TameCochainQuasiIso`. This is a claim about the explicit map `tameH2` (induced by the degree-two
formula of `tameCochainMap`), not printed as stated: the compatibility of the explicit
degree-two component with the literature's identification `H²(G_K, M) ≅ M ⧸ (Φ − q) M` for the
tame quotient (sources above; local duality as in the tree's Milne ADT I.2.3 statements).
Kind: GLUE. -/
def TameH2Surjective : Prop :=
  ∀ (K : Type) [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [DistribMulAction (Field.absoluteGaloisGroup K) M]
    [SMulCommClass (Field.absoluteGaloisGroup K) R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (Field.absoluteGaloisGroup K) M] [Finite M]
    (φ σ : Field.absoluteGaloisGroup K) (P : Subgroup (Field.absoluteGaloisGroup K))
    (Φ : M →ₗ[R] M) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q),
    IsArithFrobeniusLift K φ → σ ∈ inertiaSubgroup K → q = Nat.card 𝓀[K] →
    ringChar 𝓀[K] ≠ 2 → P.Normal → IsClosed (P : Set (Field.absoluteGaloisGroup K)) →
    TauCeti.IsProP (ringChar 𝓀[K]) P → P ≤ inertiaSubgroup K →
    (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K →
    (∀ x ∈ inertiaSubgroup K, ∀ m : M, x • m = m) → (∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) →
    Function.Surjective (tameH2 Φ φ σ q hq hΦ hσ hrel)

/-! ### Assembly over a finite extension of `ℚ_p` with `𝔽₂`-coefficients -/

section AssemblyPadic

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [PerfectField K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) (ZMod 2) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison is a quasi-isomorphism, from the prints** (tex 3470–3480): for a
nonarchimedean local field `K` that is a finite extension of `ℚ_p`, `p ≠ 2`, with
`𝔽₂`-coefficients, at `g = 1`, under the hypotheses of `quasiIsoAt_tameCochainMap_one`
together with a closed normal pro-`p` subgroup `P ≤ I` with `I = closure(⟨σ⟩ P)` and odd
residue characteristic, `tameCochainMap` is a quasi-isomorphism, given the tree PRINT
`MilneADT_I_2_8` (degrees `≥ 3`: `subsingleton_homology_of_milne`; the order of `H²`:
`euler_of_milne`, `card_contH2_eq`) and the GLUE statement `TameH2Surjective` (degree `2`).
Degrees `≤ 1` are PROVED in `quasiIso_tameCochainMap_of_two_le`. The coefficients are `ZMod 2`
(the restriction of `MilneADT_I_2_8`). Kind: PROVED (from the tree PRINT `MilneADT_I_2_8` and
the GLUE statement `TameH2Surjective`). -/
theorem quasiIso_tameCochainMap_of_prints (h28 : MilneADT_I_2_8) (h2 : TameH2Surjective)
    (hp : p ≠ 2) (X : TopRep.{0} (ZMod 2) (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[ZMod 2] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[ZMod 2] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[ZMod 2] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[ZMod 2] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K])
    (P : Subgroup (Field.absoluteGaloisGroup K)) (hPn : P.Normal)
    (hPc : IsClosed (P : Set (Field.absoluteGaloisGroup K)))
    (hPp : TauCeti.IsProP (ringChar 𝓀[K]) P) (hPI : P ≤ inertiaSubgroup K)
    (hIσ : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K)
    (hp2 : ringChar 𝓀[K] ≠ 2) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) := by
  have : Finite M := Finite.of_surjective f hfs
  have hexp : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0 := ⟨1, fun m => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 from rfl,
      zero_smul]⟩
  refine quasiIso_tameCochainMap_of_two_le X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
    hgσ hg hcomm hrel ?_
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    exact quasiIsoAt_tameCochainMap_two_of_surjective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm
      hrel (inertiaSubgroup K) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
      (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel)
      (euler_of_milne p K M h28 hp)
      (h2 K (ZMod 2) M φ σ P Φ _ hq hΦ (hItriv σ hσI) hrel hφ hσI rfl hp2 hPn hPc hPp hPI hIσ
        hItriv hexp)
  · exact quasiIsoAt_tameCochainMap_of_ge_three Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel i h
      (subsingleton_homology_of_milne p K M h28 i h)

end AssemblyPadic

/-! ### Assembly at a finite place of a number field, any coefficient field -/

section AssemblyPlace

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup (v.adicCompletion F)) M]
  [SMulCommClass (Field.absoluteGaloisGroup (v.adicCompletion F)) k M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup (v.adicCompletion F)) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : v.adicCompletion F}
  {β : AlgebraicClosure (v.adicCompletion F)}
  {φ σ : Field.absoluteGaloisGroup (v.adicCompletion F)}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison is a quasi-isomorphism, counting variant** (tex 3470–3480): under the
hypotheses of `quasiIsoAt_tameCochainMap_one` at the completion `K = F_v`, given the tree PRINT
`MilneLocalDimensionTwo` (degrees `≥ 3`), the Euler characteristic identity
`|H⁰| · |H²| = |H¹|` for the explicit continuous cohomology (Tate; Milne ADT I.2.8 for `M` of
order prime to `p`), and surjectivity of `tameH2 : H² → coker(Φ − q)`, `tameCochainMap` is a
quasi-isomorphism. Kind: PROVED (from the PRINT and the two displayed hypotheses). -/
theorem quasiIso_tameCochainMap_of_euler (hlcd : MilneLocalDimensionTwo) [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup (v.adicCompletion F)))
    [ContinuousSMul (UnramifiedGaloisGroup (v.adicCompletion F)) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup (v.adicCompletion F)) (x : X.V),
      f (localUnramifiedProjection (v.adicCompletion F) g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[v.adicCompletion F]))
    (hβ : β ^ n = algebraMap (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) a)
    (hβ0 : β ≠ 0) (hφ : IsArithFrobeniusLift (v.adicCompletion F) φ)
    (hσI : σ ∈ inertiaSubgroup (v.adicCompletion F))
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv (v.adicCompletion F) σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup (v.adicCompletion F), ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[v.adicCompletion F])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[v.adicCompletion F])
    (heuler : Nat.card (contZ0 k (Field.absoluteGaloisGroup (v.adicCompletion F)) M) *
        Nat.card (ContH2 k (Field.absoluteGaloisGroup (v.adicCompletion F)) M) =
      Nat.card (H1WrelK k (Field.absoluteGaloisGroup (v.adicCompletion F)) M))
    (hs : Function.Surjective (tameH2 Φ φ σ (Nat.card 𝓀[v.adicCompletion F]) hq hΦ
      (hItriv σ hσI) hrel)) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[v.adicCompletion F]) hq
      hΦ hgσ hg hcomm hrel)) := by
  have : Finite M := Finite.of_surjective f hfs
  refine quasiIso_tameCochainMap_of_two_le X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
    hgσ hg hcomm hrel ?_
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    exact quasiIsoAt_tameCochainMap_two_of_surjective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm
      hrel (inertiaSubgroup (v.adicCompletion F)) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
      (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel) heuler hs
  · exact quasiIsoAt_tameCochainMap_of_ge_three_milne v hlcd Φ LinearMap.id φ σ _ hq hΦ hgσ hg
      hcomm hrel i h

end AssemblyPlace

end ZInQ.Manuscript.RC.Local

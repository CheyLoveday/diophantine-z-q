import ZInQKernel.Contrib.OneProof.RC.Moving.MovingCharacter
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Bundle
import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Lane RC17 (Tate wiring): the genuine `2`-adic Tate image as the moving-character `TateImage`

Manuscript (11/5 version), Proposition `ex:arith-moving-character` (tex 3500–3702), proof,
tex 3597–3605:

> Let `J = ρ_T(G_{ℚ(μ_{2^∞})})`. The determinant is the cyclotomic character, so `J` is the
> determinant-one part of the fixed Tate image. Non-CM open image [Serre] gives a fixed `d ≥ 2`
> with `Γ_d := ker(SL₂(ℤ₂) → SL₂(ℤ/2^d ℤ)) ⊂ J`.

Lane RC4 proved the proposition (`ZInQ.Manuscript.RC.Moving.moving_character`) from an abstract
interface whose first part, `ZInQ.Manuscript.RC.Moving.TateImage`, holds a group `G` (standing for
`G_{ℚ(μ_{2^∞})}`), a homomorphism `ρ : G →* SL₂(ℤ₂)` (standing for `ρ_T` in a basis), Serre's level
`d ≥ 2` and the field `serre : Γ_d ≤ ρ(G)`.  Lane RC9 stated over genuine objects (`G_ℚ = Aut(ℚ̄/ℚ)`,
the vendored `2`-adic Tate module `T₂E` and its Galois representation `ρ_T`) Serre's theorem
(`SerreThm3`, PRINT) and its two-adic forms; the direction "`det ρ_T(σ) = 1` implies that `σ` fixes
`μ_{2^∞}`" (`DetTateTwoCyclotomic`) is PROVED in the tree for every elliptic `E/ℚ`
(`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic`, from the Weil pairing).

This file builds the `TateImage` from those genuine objects.

* `Qmu2`, `GalQmu2`: the subfield `ℚ(μ_{2^∞})` of `ℚ̄` and its absolute Galois group, the subgroup
  of `G_ℚ` fixing it (genuine; `mem_GalQmu2_iff`: the automorphisms fixing every `2`-power root of
  unity; `mem_GalQmu2_iff_cyclotomicCharacter`: those with trivial `2`-adic cyclotomic character,
  Mathlib's `cyclotomicCharacter`).
* `tateBasis E` (lane RC9): a `ℤ₂`-basis of `T₂E`; `tateMatrix E σ`: the matrix of `ρ_T(σ)` in that
  basis; `rhoGL E : G_ℚ →* GL₂(ℤ₂)`: the image of `G_ℚ` in `GL₂(ℤ₂)`.
* `DetTateTwoEqCyclotomic E` (GLUE here, the hypothesis of the final statements;
  proved in `Discharge.lean`): the identity `det ρ_T = χ_cyc` over Mathlib's
  `cyclotomicCharacter` (Weil pairing).  Its converse direction
  `DetTateTwoCyclotomicConverse E` (an automorphism fixing `μ_{2^∞}` has `det ρ_T = 1`) is the
  direction this file uses (`DetTateTwoEqCyclotomic.converse`, PROVED); the other direction gives
  lane RC9's `DetTateTwoCyclotomic` back (`DetTateTwoEqCyclotomic.forward`, PROVED).
* `rhoSL E : G_{ℚ(μ_{2^∞})} →* SL₂(ℤ₂)` (from the converse direction).
* `serre_Γ_le_range` (PROVED from `SerreThm3` and the proved `DetTateTwoCyclotomic`):
  `Γ_d ⊂ ρ_T(G_{ℚ(μ_{2^∞})})` for some `d ≥ 2`.
* `tateImage E …` (the construction): the `TateImage` with `G = G_{ℚ(μ_{2^∞})}`, `ρ = rhoSL E`;
  `moving_character_tate` and `moving_character_ecurve`: lane RC4's proposition over it.
* `mem_range_rhoSL_iff` (PROVED): `J` is the determinant-one part of `ρ_T(G_ℚ)` (tex 3598–3600).
* `tr_tateImage_ρ` (PROVED): the trace used in the interface (`cheb`, tex 3686) is the basis-free
  trace of `ρ_T(σ)`.

Kinds: `PROVED` (a Lean proof), `PRINT` (a printed theorem taken as a leaf),
`GLUE` (a textbook fact not proved here).  The PRINT and GLUE statements are `Prop`s taken as
hypotheses, never assumed globally.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TateWiring

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Moving
open scoped WeierstrassCurve MatrixGroups

/-! ### `ℚ(μ_{2^∞})` and its absolute Galois group -/

/-- `ℚ(μ_{2^∞}) ⊂ ℚ̄`: the subfield of `ℚ̄` generated over `ℚ` by all `2`-power roots of unity. -/
def Qmu2 : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {ζ : Qbar | ∃ k : ℕ, ζ ^ 2 ^ k = 1}

/-- **`G_{ℚ(μ_{2^∞})}`** (tex 3598), as the subgroup of `G_ℚ = Aut(ℚ̄/ℚ)` fixing `ℚ(μ_{2^∞})`
pointwise. -/
def GalQmu2 : Subgroup GalQ :=
  Qmu2.fixingSubgroup

/-- `σ ∈ G_{ℚ(μ_{2^∞})}` iff the `2`-adic cyclotomic character of `σ` is trivial (PROVED, vendored
Tau Ceti). -/
theorem mem_GalQmu2_iff_cyclotomicCharacter {σ : GalQ} :
    σ ∈ GalQmu2 ↔ cyclotomicCharacter Qbar 2 σ.toRingEquiv = 1 :=
  TauCeti.mem_fixingSubgroup_adjoin_iff_cyclotomicCharacter_eq_one 2

/-- `σ ∈ G_{ℚ(μ_{2^∞})}` iff `σ` fixes every `2`-power root of unity of `ℚ̄` (PROVED). -/
theorem mem_GalQmu2_iff {σ : GalQ} :
    σ ∈ GalQmu2 ↔ ∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ :=
  mem_GalQmu2_iff_cyclotomicCharacter.trans (TauCeti.cyclotomicCharacter_eq_one_iff 2)

/-! ### The determinant of `ρ_T` -/

/-- **GLUE (not proved here): `det ρ_T = χ_cyc`.**  For every `σ ∈ G_ℚ`, the determinant of
`ρ_T(σ)` on `T₂E` is the `2`-adic cyclotomic character of `σ` (Mathlib's `cyclotomicCharacter`).
Tex 3598–3599: "The determinant is the cyclotomic character".  Printed: J.-P. Serre, *Propriétés
galoisiennes des points d'ordre fini des courbes elliptiques*, Invent. Math. 15 (1972), 259–331,
p. 300, the paragraph after Corollaire 2 (read from the published scan): the composite of
`ρ_ℓ : G → GL(T_ℓ)` and `det` is the `ℓ`-adic character `χ_ℓ` giving the action of `G` on the
`ℓ^n`-th roots of unity, citing Serre's McGill notes, pp. I-3, I-4 (not read).  It comes from the
Weil pairing (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., §III.8: `UNVERIFIED`, not
read for this lane).  This is the hypothesis of the final statements of this lane.  Used through
its converse direction (`DetTateTwoEqCyclotomic.converse`): `ρ_T` maps `G_{ℚ(μ_{2^∞})}` into
`SL₂(ℤ₂)`. It holds for every elliptic `E/ℚ`: `detTateTwoEqCyclotomic_holds` (`Discharge.lean`). -/
def DetTateTwoEqCyclotomic (E : WeierstrassCurve ℚ) : Prop :=
  ∀ σ : GalQ, LinearMap.det (tateRep E 2 σ) = (cyclotomicCharacter Qbar 2 σ.toRingEquiv : ℤ_[2])

/-- **The converse direction of `det ρ_T = χ_cyc`**: if `σ ∈ G_ℚ` fixes every `2`-power root of
unity, then `det ρ_T(σ) = 1` on `T₂E`.  (Lane RC9's `DetTateTwoCyclotomic` is the other
direction.)  It follows from `DetTateTwoEqCyclotomic` (`DetTateTwoEqCyclotomic.converse`). -/
def DetTateTwoCyclotomicConverse (E : WeierstrassCurve ℚ) : Prop :=
  ∀ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) →
    LinearMap.det (tateRep E 2 σ) = 1

/-- `det ρ_T = χ_cyc` gives lane RC9's `DetTateTwoCyclotomic` (PROVED; for elliptic `E` that
direction is also proved outright in the tree). -/
theorem DetTateTwoEqCyclotomic.forward {E : WeierstrassCurve ℚ} (h : DetTateTwoEqCyclotomic E) :
    DetTateTwoCyclotomic E := by
  intro σ hσ
  have h1 : cyclotomicCharacter Qbar 2 σ.toRingEquiv = 1 :=
    Units.ext (by rw [← h σ, hσ, Units.val_one])
  exact (TauCeti.cyclotomicCharacter_eq_one_iff 2).1 h1

/-- `det ρ_T = χ_cyc` gives the converse direction `DetTateTwoCyclotomicConverse` (PROVED). -/
theorem DetTateTwoEqCyclotomic.converse {E : WeierstrassCurve ℚ} (h : DetTateTwoEqCyclotomic E) :
    DetTateTwoCyclotomicConverse E := by
  intro σ hσ
  rw [h σ, (TauCeti.cyclotomicCharacter_eq_one_iff 2).2 hσ, Units.val_one]

/-! ### The matrices of `ρ_T` in a basis of `T₂E`, and the image of `G_ℚ` in `GL₂(ℤ₂)` -/

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The matrix of `ρ_T(σ)` in the fixed `ℤ₂`-basis `tateBasis E` of `T₂E` (lane RC9). -/
def tateMatrix (σ : GalQ) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  LinearMap.toMatrix (tateBasis E) (tateBasis E) (tateRep E 2 σ)

theorem tateMatrix_mul (σ τ : GalQ) : tateMatrix E (σ * τ) = tateMatrix E σ * tateMatrix E τ := by
  rw [tateMatrix, map_mul, LinearMap.toMatrix_mul]
  rfl

theorem tateMatrix_one : tateMatrix E 1 = 1 := by
  rw [tateMatrix, map_one, LinearMap.toMatrix_one]

theorem det_tateMatrix (σ : GalQ) : (tateMatrix E σ).det = LinearMap.det (tateRep E 2 σ) :=
  LinearMap.det_toMatrix _ _

/-- The trace of the matrix is the basis-free trace of `ρ_T(σ)`. -/
theorem trace_tateMatrix (σ : GalQ) :
    (tateMatrix E σ).trace = LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) :=
  (LinearMap.trace_eq_matrix_trace ℤ_[2] (tateBasis E) _).symm

/-- **The image of `G_ℚ` in `GL₂(ℤ₂)`** (tex 2882–2883, 3599–3600 "the fixed Tate image"): the
`2`-adic Tate representation of `E` in the basis `tateBasis E`. -/
def rhoGL : GalQ →* GL (Fin 2) ℤ_[2] where
  toFun σ := ⟨tateMatrix E σ, tateMatrix E σ⁻¹,
    by rw [← tateMatrix_mul, mul_inv_cancel, tateMatrix_one],
    by rw [← tateMatrix_mul, inv_mul_cancel, tateMatrix_one]⟩
  map_one' := Units.ext (tateMatrix_one E)
  map_mul' σ τ := Units.ext (tateMatrix_mul E σ τ)

@[simp]
theorem coe_rhoGL (σ : GalQ) :
    ((rhoGL E σ : GL (Fin 2) ℤ_[2]) : Matrix (Fin 2) (Fin 2) ℤ_[2]) = tateMatrix E σ :=
  rfl

/-- The automorphism of `T₂E` whose matrix in `tateBasis E` is an invertible matrix `A`. -/
def autOfMatrix (A B : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hAB : A * B = 1) (hBA : B * A = 1) :
    TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2 :=
  LinearEquiv.ofLinearMap (Matrix.toLin (tateBasis E) (tateBasis E) A)
    (Matrix.toLin (tateBasis E) (tateBasis E) B)
    (by rw [← Matrix.toLin_mul, hAB, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hBA, Matrix.toLin_one])

theorem autOfMatrix_apply (A B : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hAB : A * B = 1)
    (hBA : B * A = 1) (x : TateMod E 2) :
    autOfMatrix E A B hAB hBA x = Matrix.toLin (tateBasis E) (tateBasis E) A x :=
  rfl

theorem toMatrix_autOfMatrix (A B : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hAB : A * B = 1)
    (hBA : B * A = 1) :
    LinearMap.toMatrix (tateBasis E) (tateBasis E) (autOfMatrix E A B hAB hBA).toLinearMap = A :=
  LinearMap.toMatrix_toLin _ _ _

/-- A matrix `1 + 2^c X` acts on `T₂E` as `x ↦ x + 2^c y` with `y` the image of `x` under `X`. -/
theorem toLin_one_add_smul (c : ℕ) (X : Matrix (Fin 2) (Fin 2) ℤ_[2]) (x : TateMod E 2) :
    Matrix.toLin (tateBasis E) (tateBasis E) (1 + (2 : ℤ_[2]) ^ c • X) x =
      x + (2 : ℤ_[2]) ^ c • Matrix.toLin (tateBasis E) (tateBasis E) X x := by
  rw [map_add, map_smul, Matrix.toLin_one, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply]

/-! ### `ρ_T` on `G_{ℚ(μ_{2^∞})}`, with values in `SL₂(ℤ₂)` -/

/-- On `G_{ℚ(μ_{2^∞})}` the matrix of `ρ_T` has determinant one (from the converse direction of
`det ρ_T = χ_cyc`). -/
theorem det_tateMatrix_eq_one (hconv : DetTateTwoCyclotomicConverse E) {σ : GalQ}
    (hσ : σ ∈ GalQmu2) : (tateMatrix E σ).det = 1 := by
  rw [det_tateMatrix]
  exact hconv σ (mem_GalQmu2_iff.1 hσ)

/-- **`ρ_T` restricted to `G_{ℚ(μ_{2^∞})}`, with values in `SL₂(ℤ₂)`** (tex 3597–3599). -/
def rhoSL (hconv : DetTateTwoCyclotomicConverse E) : GalQmu2 →* SL(2, ℤ_[2]) where
  toFun σ := ⟨tateMatrix E σ, det_tateMatrix_eq_one E hconv σ.2⟩
  map_one' := Subtype.ext (tateMatrix_one E)
  map_mul' σ τ := Subtype.ext (tateMatrix_mul E σ τ)

@[simp]
theorem coe_rhoSL (hconv : DetTateTwoCyclotomicConverse E) (σ : GalQmu2) :
    ((rhoSL E hconv σ : SL(2, ℤ_[2])) : Matrix (Fin 2) (Fin 2) ℤ_[2]) = tateMatrix E σ :=
  rfl

/-- **`J` is the determinant-one part of the fixed Tate image** (tex 3598–3600; PROVED from the
two directions of `det ρ_T = χ_cyc`, the forward one being the tree's proved
`detTateTwoCyclotomic`): a matrix of `SL₂(ℤ₂)` lies in `J = ρ_T(G_{ℚ(μ_{2^∞})})` iff it is the
matrix of `ρ_T(σ)` for some `σ ∈ G_ℚ`.  This is the `2`-adic case of the step in Serre's proof
of Corollaire 2 (Invent. Math. 15 (1972), p. 300): the image of the kernel of the cyclotomic
character is the intersection of `ρ(G)` with `SL`. -/
theorem mem_range_rhoSL_iff (hconv : DetTateTwoCyclotomicConverse E) (M : SL(2, ℤ_[2])) :
    M ∈ (rhoSL E hconv).range ↔ ∃ σ : GalQ, tateMatrix E σ = M := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, congrArg Subtype.val hσ⟩
  · rintro ⟨σ, hσ⟩
    have h1 : LinearMap.det (tateRep E 2 σ) = 1 := by
      rw [← det_tateMatrix, hσ]
      exact M.2
    exact ⟨⟨σ, mem_GalQmu2_iff.2
      (ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic E σ h1)⟩, Subtype.ext hσ⟩

/-! ### Serre's open image: `Γ_d ⊂ J` -/

/-- **`Γ_d ⊂ J = ρ_T(G_{ℚ(μ_{2^∞})})`** (tex 3600–3605; PROVED from Serre's theorem `SerreThm3`
(PRINT: Serre, Invent. Math. 15 (1972), §4.4, Théorème 3, p. 299, and Corollaire 2, p. 300, both
read from the published scan),
through lane RC9's `serre_SL2_part` with the tree's proved `detTateTwoCyclotomic`): there is
`d ≥ 2` such that every matrix of `SL₂(ℤ₂)` congruent to `1` modulo `2^d` is the matrix of
`ρ_T(σ)` for some `σ ∈ G_{ℚ(μ_{2^∞})}`. -/
theorem serre_Γ_le_range (hS : SerreThm3) (hE : HasNoCM E)
    (hconv : DetTateTwoCyclotomicConverse E) :
    ∃ d : ℕ, 2 ≤ d ∧ Γ d ≤ (rhoSL E hconv).range := by
  obtain ⟨d, hd, h⟩ := serre_SL2_part hS E hE
    (ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoCyclotomic E)
  refine ⟨d, hd, fun M hM => ?_⟩
  choose N hN using (mem_Γ_iff d M).1 hM
  have hM' : (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) = 1 + (2 : ℤ_[2]) ^ d • Matrix.of N := by
    refine Matrix.ext fun i j => ?_
    have h1 := hN i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination h1
  have hMinv : (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) * ((M⁻¹ : SL(2, ℤ_[2])) : Matrix _ _ _) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvM : ((M⁻¹ : SL(2, ℤ_[2])) : Matrix _ _ _) * (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨σ, hσμ, hσ⟩ := h (autOfMatrix E M _ hMinv hinvM)
    (by rw [← LinearMap.det_toMatrix (tateBasis E), toMatrix_autOfMatrix]; exact M.2)
    (fun x => ⟨Matrix.toLin (tateBasis E) (tateBasis E) (Matrix.of N) x, by
      rw [autOfMatrix_apply, hM', toLin_one_add_smul]⟩)
  refine ⟨⟨σ, mem_GalQmu2_iff.2 hσμ⟩, Subtype.ext ?_⟩
  change tateMatrix E σ = M
  rw [tateMatrix, hσ, toMatrix_autOfMatrix]

/-! ### The `TateImage` of lane RC4, built from the genuine objects -/

/-- **The fixed Tate image of `E` as lane RC4's `TateImage`** (tex 3597–3605): `G = G_{ℚ(μ_{2^∞})}`
(genuine, `GalQmu2`), `ρ = ρ_T` in the basis `tateBasis E` (genuine, with values in `SL₂(ℤ₂)` by
the converse direction of `det ρ_T = χ_cyc`), `d` a level given by Serre's theorem, and the field
`serre : Γ_d ≤ ρ(G)` discharged by `serre_Γ_le_range` from the PRINT `SerreThm3`.  The hypotheses
are exactly: the print, non-CM, and `det ρ_T = χ_cyc` (GLUE). -/
def tateImage (hS : SerreThm3) (hE : HasNoCM E) (hdetEq : DetTateTwoEqCyclotomic E) :
    TateImage where
  G := GalQmu2
  ρ := rhoSL E hdetEq.converse
  d := Classical.choose (serre_Γ_le_range E hS hE hdetEq.converse)
  two_le_d := (Classical.choose_spec (serre_Γ_le_range E hS hE hdetEq.converse)).1
  serre := (Classical.choose_spec (serre_Γ_le_range E hS hE hdetEq.converse)).2

section TateImage

variable {E} (hS : SerreThm3) (hE : HasNoCM E) (hdetEq : DetTateTwoEqCyclotomic E)

/-- The group of `tateImage` is `G_{ℚ(μ_{2^∞})}`. -/
theorem tateImage_G : (tateImage E hS hE hdetEq).G = GalQmu2 :=
  rfl

/-- The homomorphism of `tateImage` is `ρ_T` in the basis `tateBasis E`. -/
theorem coe_tateImage_ρ (σ : GalQmu2) :
    (((tateImage E hS hE hdetEq).ρ σ : SL(2, ℤ_[2])) : Matrix (Fin 2) (Fin 2) ℤ_[2]) =
      tateMatrix E σ :=
  rfl

/-- **The trace in the interface is the genuine trace** (tex 3686): for `σ ∈ G_{ℚ(μ_{2^∞})}`, the
trace `tr (T.ρ σ)` used by lane RC4 (in `cheb` and in (4.4d)) is the basis-free trace of `ρ_T(σ)`
on `T₂E`. -/
theorem tr_tateImage_ρ (σ : GalQmu2) :
    tr ((tateImage E hS hE hdetEq).ρ σ) =
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 (σ : GalQ)) :=
  trace_tateMatrix E σ

/-- `J = ρ(G)` for `tateImage` is the determinant-one part of `ρ_T(G_ℚ)` (tex 3598–3600). -/
theorem mem_range_tateImage_ρ_iff (M : SL(2, ℤ_[2])) :
    M ∈ (tateImage E hS hE hdetEq).ρ.range ↔ ∃ σ : GalQ, tateMatrix E σ = M :=
  mem_range_rhoSL_iff E hdetEq.converse M

/-- **Proposition `ex:arith-moving-character` for the genuine Tate image** (tex 3500–3702;
PROVED from lane RC4's `moving_character` with `T = tateImage E …`): for every moving-character
setting over the genuine Tate image, the conclusion of lane RC4's proposition holds, with
`c_E = 16 d + 21` for Serre's level `d` of `E` (depending only on `E`, not on `K`, `n`, `B`, the
avoidance set or the active list). -/
theorem moving_character_tate {n : ℕ} (M : MovingSetting (tateImage E hS hE hdetEq) n)
    (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImage E hS hE hdetEq).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character M B S

end TateImage

/-! ### The curves `E_ℓ` -/

/-- **The GLUE of this lane, bundled** (in the manner of lane RC9's `GlueArith`): `det ρ_T = χ_cyc`
for every elliptic curve over `ℚ`. -/
structure GlueTate : Prop where
  /-- `det ρ_T = χ_cyc` (Weil pairing), for every elliptic `E/ℚ`. -/
  detEq : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], DetTateTwoEqCyclotomic E

/-- **The fixed Tate image of `E_ℓ`** (tex 3597–3605), for `ℓ > 0`, built from Serre's print
(lane RC9's `ArithPrints`), the GLUE `CMjInteger` (non-CM of `E_ℓ`, lane RC9) and this lane's
`GlueTate`. -/
def tateImageEcurve (P : ArithPrints) (hcm : CMjInteger) (H : GlueTate) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    TateImage :=
  @tateImage (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) P.serre
    (curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')) (@H.detEq _ (ecurve_isElliptic hℓ))

/-- The group of `tateImageEcurve` is `G_{ℚ(μ_{2^∞})}`. -/
theorem tateImageEcurve_G (P : ArithPrints) (hcm : CMjInteger) (H : GlueTate) {ℓ : ℕ}
    (hℓ : 0 < ℓ) : (tateImageEcurve P hcm H hℓ).G = GalQmu2 :=
  rfl

/-- **Proposition `ex:arith-moving-character` for `E_ℓ`** (tex 3500–3702; PROVED from lane RC4's
`moving_character` over `tateImageEcurve`). -/
theorem moving_character_ecurve (P : ArithPrints) (hcm : CMjInteger) (H : GlueTate) {ℓ : ℕ}
    (hℓ : 0 < ℓ) {n : ℕ} (M : MovingSetting (tateImageEcurve P hcm H hℓ) n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurve P hcm H hℓ).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character M B S

end ZInQ.Manuscript.RC.TateWiring

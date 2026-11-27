import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Limit
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Change
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate12Order

/-!
# Retained homotopy inverses through the inner limit

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4401–4405, 4444–4450): "One
fixed nonprincipal ultrafilter gives a diagram over `Λ` at all coefficient precisions, preserving
its matrix identities and retained homotopy inverses … Retained homotopy inverses remain homotopy
inverses"; and the source of the unit of (4.7) in Lemma `ex:arith-common-coordinate`
(tex 4189–4193: the cone bases versus "the retained homotopy equivalent free models").

The limit of the cone models of a chain (`ChainMat`, `CommonCoordinate14Limit.lean`) carries the
matrices of the models only. This file adds the comparison of two finite free models of one
complex as matrix data, and passes it through the limit.

* (a) `HEMat R A₀ … A₃ B₀ … B₃`: homotopy-equivalence data between two four-term finite free
  models, as matrices: the differentials `dA`, `dB`, the chain maps `f : A → B`, `g : B → A`, the
  homotopies `hA`, `hB`; `HEMat.Holds J`: the identities modulo an ideal (`d² = 0`, `f d = d f`,
  `g d = d g`, `g f − 1 = d hA + hA d`, `f g − 1 = d hB + hB d`); `HEMat.map`,
  **`HEMat.holds_map_iff`**; `prodHE`, `holds_prodHE`, **`limitHE`**, **`HEMat.limit_holds`**:
  identities modulo the stage ideals at `U`-many stages give the exact identities over `Λ` for the
  entrywise ultralimit ("retained homotopy inverses remain homotopy inverses").
* (b) `FourFree Y ι₀ ι₁ ι₂ ι₃`: bases of a complex `Y` in degrees `0, …, 3`, zero in degrees `−1`
  and `4` (`FourFree.ofMatCx` for lane RC31's graded models, `FourFree.ofBlock` for block-complex
  models such as the cone models); `heF`, `heH`: for two retracts `R₁ : X → Y₁`, `R₂ : X → Y₂`
  of one complex, the comparisons `p₂ i₁`, `p₁ i₂` and the homotopies `−p₁ h₂ i₁`, `−p₂ h₁ i₂`,
  with `heF_d`, `heF_heF`; `matIn`, **`modelEquiv_of_retracts`** (the matrices in the bases) and
  **`modelEquiv_of_retracts_holds`** (the identities hold exactly). Through the stages:
  `HEMat.liftAlong`, `stageLiftHE`, `stageLiftHE_holds`, `heStagesOn`,
  `limit_holds_of_stagesOn`, and **`limit_holds_of_retracts`**: two retracts of the stage
  complexes onto models with bases of fixed index types, at the stages of a `U`-large set, give
  exact homotopy-equivalence data over `Λ` in the limit.
* (c) `HEMat.cxA`, `HEMat.cxB`: the two models as four-term complexes;
  **`kmCoord_comparison_iso`**: when the comparison is an isomorphism (`f g = 1` in every degree,
  same index types), the Knudsen–Mumford coordinates at the transported class `f z` and functional
  `λ g` differ by the unit `det f₁ det f₃ det g₀ det g₂` (`comparison_det_isUnit`). The general
  case, a homotopy equivalence between models of different ranks, is NOT proved here: it is the
  statement `KmCoordComparisonUnit`.
* (d) `RetainedMapsToCochains`: the remaining item of tex 4438–4439, 4449–4450, the maps of the
  limit models to the original cochains over `Λ`, as one statement (not proved here). It does NOT
  hold as stated: nothing ties `XΛ` to the stage complexes, and it fails for `XΛ = 0`
  (`not_retainedMapsToCochains`, `CloudB3E1Torsion/RetainedModels.lean`). No theorem uses it; a
  correct form needs the original cochains over `Λ` whose stage reductions are the stage complexes,
  with the stage retracts carried through the limit. The end field no longer needs it
  (`htildeE_of_retained'`).

Kinds: definitions and PROVED; `KmCoordComparisonUnit` and `RetainedMapsToCochains` are
statements (definitions of propositions), not proved.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Filter
open scoped PowerSeries.WithPiTopology
open ZInQ.Manuscript.RC.Limits (ulimHom stageIdeal GRetract matCx GRetract.p_d GRetract.i_d)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.Torsion (FourCx kmCoord)
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (BlockComplex)

/-! ### (a) Homotopy-equivalence data as matrices -/

section MatIn

variable {R : Type} [CommRing R] {m n : Type}

/-- All entries of a matrix lie in an ideal (tex 4444–4448: identities modulo the stage
ideals). Kind: definition. -/
def MatIn (J : Ideal R) (M : Matrix m n R) : Prop := ∀ i j, M i j ∈ J

/-- The entries of the push-forward lie in `J'` iff the entries lie in `φ⁻¹(J')`
(tex 4444–4448). Kind: PROVED (definitional). -/
theorem matIn_map_iff {R' : Type} [CommRing R'] (φ : R →+* R') (J' : Ideal R')
    (M : Matrix m n R) : MatIn J' (M.map φ) ↔ MatIn (J'.comap φ) M :=
  Iff.rfl

/-- Entries in the zero ideal: the matrix vanishes (tex 4444–4448). Kind: PROVED. -/
theorem matIn_bot_iff (M : Matrix m n R) : MatIn ⊥ M ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    exact (Ideal.mem_bot).1 (h i j)
  · rintro rfl i j
    exact (Ideal.mem_bot).2 rfl

end MatIn

/-- **Homotopy-equivalence data between two four-term finite free models, as matrices**
(tex 4401–4405, 4423–4437, 4444–4450): models `A` (differentials `dA₀, dA₁, dA₂` on
`A₀ → A₁ → A₂ → A₃`) and `B`, chain maps `f : A → B` and `g : B → A` (components `f₀, …, f₃`,
`g₀, …, g₃`), and homotopies `hA : Aᵏ → Aᵏ⁻¹`, `hB : Bᵏ → Bᵏ⁻¹` (`k = 1, 2, 3`).
Kind: definition (data). -/
structure HEMat (R : Type) [CommRing R] (A0 A1 A2 A3 B0 B1 B2 B3 : Type) where
  /-- `A₀ → A₁` -/
  dA0 : Matrix A1 A0 R
  /-- `A₁ → A₂` -/
  dA1 : Matrix A2 A1 R
  /-- `A₂ → A₃` -/
  dA2 : Matrix A3 A2 R
  /-- `B₀ → B₁` -/
  dB0 : Matrix B1 B0 R
  /-- `B₁ → B₂` -/
  dB1 : Matrix B2 B1 R
  /-- `B₂ → B₃` -/
  dB2 : Matrix B3 B2 R
  /-- `f` in degree `0` -/
  f0 : Matrix B0 A0 R
  /-- `f` in degree `1` -/
  f1 : Matrix B1 A1 R
  /-- `f` in degree `2` -/
  f2 : Matrix B2 A2 R
  /-- `f` in degree `3` -/
  f3 : Matrix B3 A3 R
  /-- `g` in degree `0` -/
  g0 : Matrix A0 B0 R
  /-- `g` in degree `1` -/
  g1 : Matrix A1 B1 R
  /-- `g` in degree `2` -/
  g2 : Matrix A2 B2 R
  /-- `g` in degree `3` -/
  g3 : Matrix A3 B3 R
  /-- the homotopy of `A` from degree `1` -/
  hA1 : Matrix A0 A1 R
  /-- the homotopy of `A` from degree `2` -/
  hA2 : Matrix A1 A2 R
  /-- the homotopy of `A` from degree `3` -/
  hA3 : Matrix A2 A3 R
  /-- the homotopy of `B` from degree `1` -/
  hB1 : Matrix B0 B1 R
  /-- the homotopy of `B` from degree `2` -/
  hB2 : Matrix B1 B2 R
  /-- the homotopy of `B` from degree `3` -/
  hB3 : Matrix B2 B3 R

namespace HEMat

variable {R : Type} [CommRing R] {A0 A1 A2 A3 B0 B1 B2 B3 : Type}

/-- **The push-forward along a ring homomorphism** (tex 4444–4448). Kind: definition. -/
def map {R' : Type} [CommRing R'] (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (φ : R →+* R') :
    HEMat R' A0 A1 A2 A3 B0 B1 B2 B3 where
  dA0 := E.dA0.map φ
  dA1 := E.dA1.map φ
  dA2 := E.dA2.map φ
  dB0 := E.dB0.map φ
  dB1 := E.dB1.map φ
  dB2 := E.dB2.map φ
  f0 := E.f0.map φ
  f1 := E.f1.map φ
  f2 := E.f2.map φ
  f3 := E.f3.map φ
  g0 := E.g0.map φ
  g1 := E.g1.map φ
  g2 := E.g2.map φ
  g3 := E.g3.map φ
  hA1 := E.hA1.map φ
  hA2 := E.hA2.map φ
  hA3 := E.hA3.map φ
  hB1 := E.hB1.map φ
  hB2 := E.hB2.map φ
  hB3 := E.hB3.map φ

variable [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1]
  [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1] [DecidableEq A2] [DecidableEq A3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]

/-- **The identities of the homotopy equivalence modulo an ideal `J`** (tex 4423–4437,
4444–4450): both models are complexes, `f` and `g` are chain maps, and `g f − 1 = d hA + hA d`,
`f g − 1 = d hB + hB d` in every degree (the models vanish in degrees `−1` and `4`).
Kind: definition. -/
structure Holds (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (J : Ideal R) : Prop where
  /-- `dA₁ dA₀ = 0` -/
  cA1 : MatIn J (E.dA1 * E.dA0)
  /-- `dA₂ dA₁ = 0` -/
  cA2 : MatIn J (E.dA2 * E.dA1)
  /-- `dB₁ dB₀ = 0` -/
  cB1 : MatIn J (E.dB1 * E.dB0)
  /-- `dB₂ dB₁ = 0` -/
  cB2 : MatIn J (E.dB2 * E.dB1)
  /-- `f d = d f` from degree `0` -/
  hf0 : MatIn J (E.f1 * E.dA0 - E.dB0 * E.f0)
  /-- `f d = d f` from degree `1` -/
  hf1 : MatIn J (E.f2 * E.dA1 - E.dB1 * E.f1)
  /-- `f d = d f` from degree `2` -/
  hf2 : MatIn J (E.f3 * E.dA2 - E.dB2 * E.f2)
  /-- `g d = d g` from degree `0` -/
  hg0 : MatIn J (E.g1 * E.dB0 - E.dA0 * E.g0)
  /-- `g d = d g` from degree `1` -/
  hg1 : MatIn J (E.g2 * E.dB1 - E.dA1 * E.g1)
  /-- `g d = d g` from degree `2` -/
  hg2 : MatIn J (E.g3 * E.dB2 - E.dA2 * E.g2)
  /-- `g f − 1 = hA d` in degree `0` -/
  hhA0 : MatIn J (E.g0 * E.f0 - 1 - E.hA1 * E.dA0)
  /-- `g f − 1 = d hA + hA d` in degree `1` -/
  hhA1 : MatIn J (E.g1 * E.f1 - 1 - (E.dA0 * E.hA1 + E.hA2 * E.dA1))
  /-- `g f − 1 = d hA + hA d` in degree `2` -/
  hhA2 : MatIn J (E.g2 * E.f2 - 1 - (E.dA1 * E.hA2 + E.hA3 * E.dA2))
  /-- `g f − 1 = d hA` in degree `3` -/
  hhA3 : MatIn J (E.g3 * E.f3 - 1 - E.dA2 * E.hA3)
  /-- `f g − 1 = hB d` in degree `0` -/
  hhB0 : MatIn J (E.f0 * E.g0 - 1 - E.hB1 * E.dB0)
  /-- `f g − 1 = d hB + hB d` in degree `1` -/
  hhB1 : MatIn J (E.f1 * E.g1 - 1 - (E.dB0 * E.hB1 + E.hB2 * E.dB1))
  /-- `f g − 1 = d hB + hB d` in degree `2` -/
  hhB2 : MatIn J (E.f2 * E.g2 - 1 - (E.dB1 * E.hB2 + E.hB3 * E.dB2))
  /-- `f g − 1 = d hB` in degree `3` -/
  hhB3 : MatIn J (E.f3 * E.g3 - 1 - E.dB2 * E.hB3)

/-- An identity of matrices pushed forward: entries of `N = M.map φ` in `J'` iff entries of `M`
in `φ⁻¹(J')` (tex 4444–4448). Kind: PROVED. -/
theorem matIn_iff_of_eq {R' : Type} [CommRing R'] (φ : R →+* R') (J' : Ideal R')
    {m n : Type} {M : Matrix m n R} {N : Matrix m n R'} (hN : N = M.map φ) :
    MatIn J' N ↔ MatIn (J'.comap φ) M := by
  rw [hN]
  exact matIn_map_iff φ J' M

/-- **The identities of the push-forward modulo `J'` are the identities modulo `φ⁻¹(J')`**
(tex 4444–4448: "every polynomial identity between the matrices survives"). Kind: PROVED. -/
theorem holds_map_iff {R' : Type} [CommRing R'] (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3)
    (φ : R →+* R') (J' : Ideal R') : (E.map φ).Holds J' ↔ E.Holds (J'.comap φ) := by
  have k : ∀ {m n : Type} {M : Matrix m n R} {N : Matrix m n R'}, N = M.map φ →
      (MatIn J' N ↔ MatIn (J'.comap φ) M) := fun hN => matIn_iff_of_eq φ J' hN
  constructor
  · intro h
    exact ⟨
      (k (by simp only [map, Matrix.map_mul])).1 h.cA1,
      (k (by simp only [map, Matrix.map_mul])).1 h.cA2,
      (k (by simp only [map, Matrix.map_mul])).1 h.cB1,
      (k (by simp only [map, Matrix.map_mul])).1 h.cB2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hf0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hf1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hf2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hg0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hg1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).1 h.hg2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhA0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhA1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhA2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhA3,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhB0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhB1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhB2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).1 h.hhB3⟩
  · intro h
    exact ⟨
      (k (by simp only [map, Matrix.map_mul])).2 h.cA1,
      (k (by simp only [map, Matrix.map_mul])).2 h.cA2,
      (k (by simp only [map, Matrix.map_mul])).2 h.cB1,
      (k (by simp only [map, Matrix.map_mul])).2 h.cB2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hf0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hf1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hf2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hg0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hg1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul])).2 h.hg2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhA0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhA1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhA2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhA3,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhB0,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhB1,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ),
        Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhB2,
      (k (by simp only [map, Matrix.map_sub _ (map_sub φ), Matrix.map_mul,
        Matrix.map_one _ (map_zero φ) (map_one φ)])).2 h.hhB3⟩

/-- **Identities at many indices give the identities modulo the ideal of the eventual members**
(tex 4444–4448). Kind: PROVED. -/
theorem Holds.of_eventually (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (U : Ultrafilter ℕ)
    {I : ℕ → Ideal R} {J : Ideal R} (hJ : ∀ x, (∀ᶠ s in (U : Filter ℕ), x ∈ I s) → x ∈ J)
    (h : ∀ᶠ s in (U : Filter ℕ), E.Holds (I s)) : E.Holds J :=
  ⟨fun a b => hJ _ (h.mono fun _ hs => hs.cA1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.cA2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.cB1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.cB2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hf0 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hf1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hf2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hg0 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hg1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hg2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhA0 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhA1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhA2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhA3 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhB0 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhB1 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhB2 a b),
    fun a b => hJ _ (h.mono fun _ hs => hs.hhB3 a b)⟩

/-- The identities modulo `J` hold modulo every larger ideal (tex 4444–4448). Kind: PROVED. -/
theorem Holds.mono {E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3} {J J' : Ideal R} (h : E.Holds J)
    (hJ : J ≤ J') : E.Holds J' :=
  ⟨fun a b => hJ (h.cA1 a b), fun a b => hJ (h.cA2 a b), fun a b => hJ (h.cB1 a b),
    fun a b => hJ (h.cB2 a b), fun a b => hJ (h.hf0 a b), fun a b => hJ (h.hf1 a b),
    fun a b => hJ (h.hf2 a b), fun a b => hJ (h.hg0 a b), fun a b => hJ (h.hg1 a b),
    fun a b => hJ (h.hg2 a b), fun a b => hJ (h.hhA0 a b), fun a b => hJ (h.hhA1 a b),
    fun a b => hJ (h.hhA2 a b), fun a b => hJ (h.hhA3 a b), fun a b => hJ (h.hhB0 a b),
    fun a b => hJ (h.hhB1 a b), fun a b => hJ (h.hhB2 a b), fun a b => hJ (h.hhB3 a b)⟩

end HEMat

/-! ### The inner limit of the homotopy-equivalence data -/

section LimitHE

variable {A0 A1 A2 A3 B0 B1 B2 B3 : Type}

/-- **The stage data as one datum over the product ring** `ℕ → Λ` (tex 4444–4448).
Kind: definition. -/
def prodHE (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) :
    HEMat (ℕ → LamI) A0 A1 A2 A3 B0 B1 B2 B3 where
  dA0 := Matrix.of fun a b s => (c s).dA0 a b
  dA1 := Matrix.of fun a b s => (c s).dA1 a b
  dA2 := Matrix.of fun a b s => (c s).dA2 a b
  dB0 := Matrix.of fun a b s => (c s).dB0 a b
  dB1 := Matrix.of fun a b s => (c s).dB1 a b
  dB2 := Matrix.of fun a b s => (c s).dB2 a b
  f0 := Matrix.of fun a b s => (c s).f0 a b
  f1 := Matrix.of fun a b s => (c s).f1 a b
  f2 := Matrix.of fun a b s => (c s).f2 a b
  f3 := Matrix.of fun a b s => (c s).f3 a b
  g0 := Matrix.of fun a b s => (c s).g0 a b
  g1 := Matrix.of fun a b s => (c s).g1 a b
  g2 := Matrix.of fun a b s => (c s).g2 a b
  g3 := Matrix.of fun a b s => (c s).g3 a b
  hA1 := Matrix.of fun a b s => (c s).hA1 a b
  hA2 := Matrix.of fun a b s => (c s).hA2 a b
  hA3 := Matrix.of fun a b s => (c s).hA3 a b
  hB1 := Matrix.of fun a b s => (c s).hB1 a b
  hB2 := Matrix.of fun a b s => (c s).hB2 a b
  hB3 := Matrix.of fun a b s => (c s).hB3 a b

/-- **The product datum evaluated at a stage is the stage datum** (tex 4444–4448).
Kind: PROVED (definitional). -/
theorem prodHE_eval (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) (s : ℕ) :
    (prodHE c).map (evalAt s) = c s :=
  rfl

/-- **The limit homotopy-equivalence data over `Λ`** (tex 4444–4450): the entrywise ultralimits
of the stage data. Kind: definition. -/
def limitHE (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) (U : Ultrafilter ℕ) :
    HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3 :=
  (prodHE c).map (ulimHom U)

variable [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1]
  [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1] [DecidableEq A2] [DecidableEq A3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]

/-- **The identities at `U`-many stages are the identities of the product datum modulo
`ultraIdeal U`** (tex 4444–4448). Kind: PROVED. -/
theorem holds_prodHE (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) (U : Ultrafilter ℕ)
    (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s)) :
    (prodHE c).Holds (ultraIdeal U) := by
  refine HEMat.Holds.of_eventually (prodHE c) U (I := fun s =>
    (stageIdeal s).comap (evalAt s)) (fun x hx => hx) ?_
  filter_upwards [hs] with s h
  have h' : ((prodHE c).map (evalAt s)).Holds (stageIdeal s) := h
  exact ((prodHE c).holds_map_iff (evalAt s) (stageIdeal s)).1 h'

/-- **Retained homotopy inverses remain homotopy inverses** (tex 4447–4450): if the identities
of the homotopy-equivalence data hold modulo the stage ideals at `U`-many stages, along a
nonprincipal ultrafilter, they hold exactly for the limit data over `Λ`. Kind: PROVED. -/
theorem HEMat.limit_holds (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (hs : ∀ᶠ s in (U : Filter ℕ), (c s).Holds (stageIdeal s)) :
    (limitHE c U).Holds ⊥ := by
  have h := (holds_prodHE c U hs).mono (J' := (⊥ : Ideal LamI).comap (ulimHom U)) fun x hx => by
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact ulimHom_ultraIdeal hU hx
  exact ((prodHE c).holds_map_iff (ulimHom U) ⊥).2 h

end LimitHE

/-! ### (b) The comparison of two retracts of one complex -/

section Retracts

variable {A : Type} [CommRing A] {X Y₁ Y₂ : GCx A}

/-- **Bases of a complex in degrees `0, …, 3`**, the complex vanishing in degrees `−1` and `4`
(tex 4391–4399: a bounded finite free model). Kind: definition (data). -/
structure FourFree (Y : GCx A) (ι0 ι1 ι2 ι3 : Type) where
  /-- the basis in degree `0` -/
  e0 : Y.X 0 ≃ₗ[A] (ι0 → A)
  /-- the basis in degree `1` -/
  e1 : Y.X 1 ≃ₗ[A] (ι1 → A)
  /-- the basis in degree `2` -/
  e2 : Y.X 2 ≃ₗ[A] (ι2 → A)
  /-- the basis in degree `3` -/
  e3 : Y.X 3 ≃ₗ[A] (ι3 → A)
  /-- the complex vanishes in degree `−1` -/
  lo : ∀ y : Y.X (-1), y = 0
  /-- the complex vanishes in degree `4` -/
  hi : ∀ y : Y.X 4, y = 0

/-- **The bases of a graded model** (lane RC31's `matCx`, tex 4391–4399): the standard bases,
when the ranks vanish in degrees `−1` and `4`. Kind: definition. -/
def FourFree.ofMatCx (rank : ℤ → ℕ)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0)
    (hlo : rank (-1) = 0) (hhi : rank 4 = 0) :
    FourFree (matCx rank dC hsq) (Fin (rank 0)) (Fin (rank 1)) (Fin (rank 2)) (Fin (rank 3)) where
  e0 := LinearEquiv.refl A _
  e1 := LinearEquiv.refl A _
  e2 := LinearEquiv.refl A _
  e3 := LinearEquiv.refl A _
  lo _ := funext fun i => (Fin.cast hlo i).elim0
  hi _ := funext fun i => (Fin.cast hhi i).elim0

/-- **The bases of a block-complex model** (tex 4185–4193: the cone models are block complexes):
the standard bases of `D⁰, …, D³`. Kind: definition. -/
def FourFree.ofBlock (D : BlockComplex A) :
    FourFree D.toGCx (Fin D.m0) (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) (Fin D.m1 ⊕ Unit ⊕ Fin D.m2)
      (Fin D.m2) where
  e0 := LinearEquiv.refl A _
  e1 := LinearEquiv.refl A _
  e2 := LinearEquiv.refl A _
  e3 := LinearEquiv.refl A _
  lo _ := funext fun i => i.elim
  hi _ := funext fun i => i.elim

/-- The comparison `p₂ i₁ : Y₁ⁿ → Y₂ⁿ` of two models of one complex (tex 4189–4193,
4437–4441). Kind: definition. -/
def heF (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (n : ℤ) : Y₁.X n →ₗ[A] Y₂.X n :=
  R₂.p.f n n rfl ∘ₗ R₁.i.f n n rfl

/-- The homotopy `−p₁ h₂ i₁ : Y₁ᵃ → Y₁ᵇ`, `b + 1 = a` (tex 4437–4441). Kind: definition. -/
def heH (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (a b : ℤ) (h : b + 1 = a) :
    Y₁.X a →ₗ[A] Y₁.X b :=
  -(R₁.p.f b b rfl ∘ₗ R₂.h a b h ∘ₗ R₁.i.f a a rfl)

/-- The comparison is a chain map (tex 4437–4441). Kind: PROVED. -/
theorem heF_d (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (a b : ℤ) (h : a + 1 = b)
    (y : Y₁.X a) : heF R₁ R₂ b (Y₁.d a b h y) = Y₂.d a b h (heF R₁ R₂ a y) := by
  simp only [heF, LinearMap.comp_apply]
  rw [GRetract.i_d R₁, GRetract.p_d R₂]

/-- **The comparisons are inverse up to homotopy** (tex 4437–4441: "The identity `1 − ip = dh +
hd` transports their compatibility homotopies as well"): `(p₁ i₂)(p₂ i₁) − 1 = d H + H d` with
`H = −p₁ h₂ i₁`. Kind: PROVED. -/
theorem heF_heF (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (a b c : ℤ) (hba : b + 1 = a)
    (hac : a + 1 = c) (y : Y₁.X a) :
    heF R₂ R₁ a (heF R₁ R₂ a y) - y =
      Y₁.d b a hba (heH R₁ R₂ a b hba y) + heH R₁ R₂ c a hac (Y₁.d a c hac y) := by
  obtain rfl : b = a - 1 := by omega
  obtain rfl : c = a + 1 := by omega
  have e := congrArg (R₁.p.f a a rfl) (R₂.homotopy a (R₁.i.f a a rfl y))
  rw [map_sub, map_add, R₁.p_i, GRetract.p_d R₁, ← GRetract.i_d R₁] at e
  simp only [heF, heH, LinearMap.comp_apply, LinearMap.neg_apply, map_neg]
  rw [← neg_add, ← e, neg_sub]

/-- **The matrix of a linear map in the bases** (tex 4444–4448). Kind: definition. -/
def matIn {V W : Type} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] (e : V ≃ₗ[A] (ι → A)) (e' : W ≃ₗ[A] (κ → A)) (φ : V →ₗ[A] W) :
    Matrix κ ι A :=
  LinearMap.toMatrix' (e'.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap)

section MatLemmas

variable {V W Z : Type} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
  [AddCommGroup Z] [Module A Z] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] (e : V ≃ₗ[A] (ι → A)) (e' : W ≃ₗ[A] (κ → A)) (e'' : Z ≃ₗ[A] (μ → A))

/-- Matrices of composites are products (tex 4444–4448). Kind: PROVED. -/
theorem matIn_comp (ψ : W →ₗ[A] Z) (φ : V →ₗ[A] W) :
    matIn e' e'' ψ * matIn e e' φ = matIn e e'' (ψ ∘ₗ φ) := by
  rw [matIn, matIn, matIn, ← LinearMap.toMatrix'_comp]
  congr 1
  exact LinearMap.ext fun x => by simp

omit [Fintype κ] [DecidableEq κ] in
/-- Matrices of differences are differences (tex 4444–4448). Kind: PROVED. -/
theorem matIn_sub (φ ψ : V →ₗ[A] W) : matIn e e' φ - matIn e e' ψ = matIn e e' (φ - ψ) := by
  rw [matIn, matIn, matIn, ← map_sub]
  congr 1
  exact LinearMap.ext fun x => by simp

omit [Fintype κ] [DecidableEq κ] in
/-- Matrices of sums are sums (tex 4444–4448). Kind: PROVED. -/
theorem matIn_add (φ ψ : V →ₗ[A] W) : matIn e e' φ + matIn e e' ψ = matIn e e' (φ + ψ) := by
  rw [matIn, matIn, matIn, ← map_add]
  congr 1
  exact LinearMap.ext fun x => by simp

omit [Fintype κ] [DecidableEq κ] in
/-- The matrix of zero is zero (tex 4444–4448). Kind: PROVED. -/
theorem matIn_zero : matIn e e' (0 : V →ₗ[A] W) = 0 := by
  rw [matIn, LinearMap.zero_comp, LinearMap.comp_zero, map_zero]

omit [Fintype κ] [DecidableEq κ] in
/-- The matrix of the identity is one (tex 4444–4448). Kind: PROVED. -/
theorem matIn_id : matIn e e (LinearMap.id : V →ₗ[A] V) = 1 := by
  have h : e.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  rw [matIn, h, LinearMap.toMatrix'_id]

end MatLemmas

variable {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3]
  [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1]
  [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1] [DecidableEq B2]
  [DecidableEq B3]

/-- **The homotopy-equivalence data of two retracts of one complex, in the bases** (tex 4189–4193,
4437–4441): for retracts `R₁ : X → Y₁`, `R₂ : X → Y₂` onto finite free models with bases,
`f = p₂ i₁`, `g = p₁ i₂`, `hA = −p₁ h₂ i₁`, `hB = −p₂ h₁ i₂` (finite maps, both models being
finite free), and the differentials of the models, as matrices. Kind: definition. -/
def modelEquiv_of_retracts (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂)
    (b₁ : FourFree Y₁ A0 A1 A2 A3) (b₂ : FourFree Y₂ B0 B1 B2 B3) :
    HEMat A A0 A1 A2 A3 B0 B1 B2 B3 where
  dA0 := matIn b₁.e0 b₁.e1 (Y₁.d 0 1 rfl)
  dA1 := matIn b₁.e1 b₁.e2 (Y₁.d 1 2 rfl)
  dA2 := matIn b₁.e2 b₁.e3 (Y₁.d 2 3 rfl)
  dB0 := matIn b₂.e0 b₂.e1 (Y₂.d 0 1 rfl)
  dB1 := matIn b₂.e1 b₂.e2 (Y₂.d 1 2 rfl)
  dB2 := matIn b₂.e2 b₂.e3 (Y₂.d 2 3 rfl)
  f0 := matIn b₁.e0 b₂.e0 (heF R₁ R₂ 0)
  f1 := matIn b₁.e1 b₂.e1 (heF R₁ R₂ 1)
  f2 := matIn b₁.e2 b₂.e2 (heF R₁ R₂ 2)
  f3 := matIn b₁.e3 b₂.e3 (heF R₁ R₂ 3)
  g0 := matIn b₂.e0 b₁.e0 (heF R₂ R₁ 0)
  g1 := matIn b₂.e1 b₁.e1 (heF R₂ R₁ 1)
  g2 := matIn b₂.e2 b₁.e2 (heF R₂ R₁ 2)
  g3 := matIn b₂.e3 b₁.e3 (heF R₂ R₁ 3)
  hA1 := matIn b₁.e1 b₁.e0 (heH R₁ R₂ 1 0 rfl)
  hA2 := matIn b₁.e2 b₁.e1 (heH R₁ R₂ 2 1 rfl)
  hA3 := matIn b₁.e3 b₁.e2 (heH R₁ R₂ 3 2 rfl)
  hB1 := matIn b₂.e1 b₂.e0 (heH R₂ R₁ 1 0 rfl)
  hB2 := matIn b₂.e2 b₂.e1 (heH R₂ R₁ 2 1 rfl)
  hB3 := matIn b₂.e3 b₂.e2 (heH R₂ R₁ 3 2 rfl)

/-- The square of a differential vanishes, as linear maps (tex 4391–4399). Kind: PROVED. -/
theorem gcx_d_comp_d (Y : GCx A) (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    Y.d b c hbc ∘ₗ Y.d a b hab = 0 :=
  LinearMap.ext fun x => Y.d_d a b c hab hbc x

/-- The comparison commutes with the differentials, as linear maps (tex 4437–4441).
Kind: PROVED. -/
theorem heF_comp_d (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (a b : ℤ) (h : a + 1 = b) :
    heF R₁ R₂ b ∘ₗ Y₁.d a b h - Y₂.d a b h ∘ₗ heF R₁ R₂ a = 0 :=
  LinearMap.ext fun y => by
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, heF_d, sub_self,
      LinearMap.zero_apply]

/-- **The homotopy-equivalence data of two retracts satisfy the identities exactly**
(tex 4189–4193, 4437–4441). Kind: PROVED. -/
theorem modelEquiv_of_retracts_holds (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂)
    (b₁ : FourFree Y₁ A0 A1 A2 A3) (b₂ : FourFree Y₂ B0 B1 B2 B3) :
    (modelEquiv_of_retracts R₁ R₂ b₁ b₂).Holds ⊥ := by
  have hdd : ∀ (Y : GCx A) (ι0 ι1 ι2 : Type) [Fintype ι0] [DecidableEq ι0] [Fintype ι1]
      [DecidableEq ι1] (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c)
      (u : Y.X a ≃ₗ[A] (ι0 → A)) (v : Y.X b ≃ₗ[A] (ι1 → A)) (w : Y.X c ≃ₗ[A] (ι2 → A)),
      matIn v w (Y.d b c hbc) * matIn u v (Y.d a b hab) = 0 := by
    intro Y ι0 ι1 ι2 _ _ _ _ a b c hab hbc u v w
    rw [matIn_comp, gcx_d_comp_d, matIn_zero]
  have hfd : ∀ (S₁ : GRetract X Y₁) (S₂ : GRetract X Y₂) (ι0 ι1 κ0 κ1 : Type) [Fintype ι0]
      [DecidableEq ι0] [Fintype ι1] [DecidableEq ι1] [Fintype κ0] [DecidableEq κ0] (a b : ℤ)
      (h : a + 1 = b) (u : Y₁.X a ≃ₗ[A] (ι0 → A)) (v : Y₁.X b ≃ₗ[A] (ι1 → A))
      (u' : Y₂.X a ≃ₗ[A] (κ0 → A)) (v' : Y₂.X b ≃ₗ[A] (κ1 → A)),
      matIn v v' (heF S₁ S₂ b) * matIn u v (Y₁.d a b h) -
        matIn u' v' (Y₂.d a b h) * matIn u u' (heF S₁ S₂ a) = 0 := by
    intro S₁ S₂ ι0 ι1 κ0 κ1 _ _ _ _ _ _ a b h u v u' v'
    rw [matIn_comp, matIn_comp, matIn_sub, heF_comp_d, matIn_zero]
  have hgd : ∀ (S₁ : GRetract X Y₂) (S₂ : GRetract X Y₁) (ι0 ι1 κ0 κ1 : Type) [Fintype ι0]
      [DecidableEq ι0] [Fintype ι1] [DecidableEq ι1] [Fintype κ0] [DecidableEq κ0] (a b : ℤ)
      (h : a + 1 = b) (u : Y₂.X a ≃ₗ[A] (ι0 → A)) (v : Y₂.X b ≃ₗ[A] (ι1 → A))
      (u' : Y₁.X a ≃ₗ[A] (κ0 → A)) (v' : Y₁.X b ≃ₗ[A] (κ1 → A)),
      matIn v v' (heF S₁ S₂ b) * matIn u v (Y₂.d a b h) -
        matIn u' v' (Y₁.d a b h) * matIn u u' (heF S₁ S₂ a) = 0 := by
    intro S₁ S₂ ι0 ι1 κ0 κ1 _ _ _ _ _ _ a b h u v u' v'
    rw [matIn_comp, matIn_comp, matIn_sub, heF_comp_d, matIn_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [matIn_bot_iff]
  · exact hdd Y₁ A0 A1 A2 0 1 2 rfl rfl b₁.e0 b₁.e1 b₁.e2
  · exact hdd Y₁ A1 A2 A3 1 2 3 rfl rfl b₁.e1 b₁.e2 b₁.e3
  · exact hdd Y₂ B0 B1 B2 0 1 2 rfl rfl b₂.e0 b₂.e1 b₂.e2
  · exact hdd Y₂ B1 B2 B3 1 2 3 rfl rfl b₂.e1 b₂.e2 b₂.e3
  · exact hfd R₁ R₂ A0 A1 B0 B1 0 1 rfl b₁.e0 b₁.e1 b₂.e0 b₂.e1
  · exact hfd R₁ R₂ A1 A2 B1 B2 1 2 rfl b₁.e1 b₁.e2 b₂.e1 b₂.e2
  · exact hfd R₁ R₂ A2 A3 B2 B3 2 3 rfl b₁.e2 b₁.e3 b₂.e2 b₂.e3
  · exact hgd R₂ R₁ B0 B1 A0 A1 0 1 rfl b₂.e0 b₂.e1 b₁.e0 b₁.e1
  · exact hgd R₂ R₁ B1 B2 A1 A2 1 2 rfl b₂.e1 b₂.e2 b₁.e1 b₁.e2
  · exact hgd R₂ R₁ B2 B3 A2 A3 2 3 rfl b₂.e2 b₂.e3 b₁.e2 b₁.e3
  · change matIn b₂.e0 b₁.e0 (heF R₂ R₁ 0) * matIn b₁.e0 b₂.e0 (heF R₁ R₂ 0) - 1 -
      matIn b₁.e1 b₁.e0 (heH R₁ R₂ 1 0 rfl) * matIn b₁.e0 b₁.e1 (Y₁.d 0 1 rfl) = 0
    rw [matIn_comp, matIn_comp, ← matIn_id b₁.e0, matIn_sub, matIn_sub]
    convert matIn_zero b₁.e0 b₁.e0
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    rw [heF_heF R₁ R₂ 0 (-1) 1 (by norm_num) rfl y, b₁.lo (heH R₁ R₂ 0 (-1) _ y), map_zero,
      zero_add, sub_self]
  · change matIn b₂.e1 b₁.e1 (heF R₂ R₁ 1) * matIn b₁.e1 b₂.e1 (heF R₁ R₂ 1) - 1 -
      (matIn b₁.e0 b₁.e1 (Y₁.d 0 1 rfl) * matIn b₁.e1 b₁.e0 (heH R₁ R₂ 1 0 rfl) +
        matIn b₁.e2 b₁.e1 (heH R₁ R₂ 2 1 rfl) * matIn b₁.e1 b₁.e2 (Y₁.d 1 2 rfl)) = 0
    rw [matIn_comp, matIn_comp, matIn_comp, ← matIn_id b₁.e1, matIn_add, matIn_sub, matIn_sub]
    convert matIn_zero b₁.e1 b₁.e1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [heF_heF R₁ R₂ 1 0 2 rfl rfl y, sub_self]
  · change matIn b₂.e2 b₁.e2 (heF R₂ R₁ 2) * matIn b₁.e2 b₂.e2 (heF R₁ R₂ 2) - 1 -
      (matIn b₁.e1 b₁.e2 (Y₁.d 1 2 rfl) * matIn b₁.e2 b₁.e1 (heH R₁ R₂ 2 1 rfl) +
        matIn b₁.e3 b₁.e2 (heH R₁ R₂ 3 2 rfl) * matIn b₁.e2 b₁.e3 (Y₁.d 2 3 rfl)) = 0
    rw [matIn_comp, matIn_comp, matIn_comp, ← matIn_id b₁.e2, matIn_add, matIn_sub, matIn_sub]
    convert matIn_zero b₁.e2 b₁.e2
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [heF_heF R₁ R₂ 2 1 3 rfl rfl y, sub_self]
  · change matIn b₂.e3 b₁.e3 (heF R₂ R₁ 3) * matIn b₁.e3 b₂.e3 (heF R₁ R₂ 3) - 1 -
      matIn b₁.e2 b₁.e3 (Y₁.d 2 3 rfl) * matIn b₁.e3 b₁.e2 (heH R₁ R₂ 3 2 rfl) = 0
    rw [matIn_comp, matIn_comp, ← matIn_id b₁.e3, matIn_sub, matIn_sub]
    convert matIn_zero b₁.e3 b₁.e3
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    rw [heF_heF R₁ R₂ 3 2 4 rfl rfl y, b₁.hi (Y₁.d 3 4 rfl y), map_zero, add_zero, sub_self]
  · change matIn b₁.e0 b₂.e0 (heF R₁ R₂ 0) * matIn b₂.e0 b₁.e0 (heF R₂ R₁ 0) - 1 -
      matIn b₂.e1 b₂.e0 (heH R₂ R₁ 1 0 rfl) * matIn b₂.e0 b₂.e1 (Y₂.d 0 1 rfl) = 0
    rw [matIn_comp, matIn_comp, ← matIn_id b₂.e0, matIn_sub, matIn_sub]
    convert matIn_zero b₂.e0 b₂.e0
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    rw [heF_heF R₂ R₁ 0 (-1) 1 (by norm_num) rfl y, b₂.lo (heH R₂ R₁ 0 (-1) _ y), map_zero,
      zero_add, sub_self]
  · change matIn b₁.e1 b₂.e1 (heF R₁ R₂ 1) * matIn b₂.e1 b₁.e1 (heF R₂ R₁ 1) - 1 -
      (matIn b₂.e0 b₂.e1 (Y₂.d 0 1 rfl) * matIn b₂.e1 b₂.e0 (heH R₂ R₁ 1 0 rfl) +
        matIn b₂.e2 b₂.e1 (heH R₂ R₁ 2 1 rfl) * matIn b₂.e1 b₂.e2 (Y₂.d 1 2 rfl)) = 0
    rw [matIn_comp, matIn_comp, matIn_comp, ← matIn_id b₂.e1, matIn_add, matIn_sub, matIn_sub]
    convert matIn_zero b₂.e1 b₂.e1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [heF_heF R₂ R₁ 1 0 2 rfl rfl y, sub_self]
  · change matIn b₁.e2 b₂.e2 (heF R₁ R₂ 2) * matIn b₂.e2 b₁.e2 (heF R₂ R₁ 2) - 1 -
      (matIn b₂.e1 b₂.e2 (Y₂.d 1 2 rfl) * matIn b₂.e2 b₂.e1 (heH R₂ R₁ 2 1 rfl) +
        matIn b₂.e3 b₂.e2 (heH R₂ R₁ 3 2 rfl) * matIn b₂.e2 b₂.e3 (Y₂.d 2 3 rfl)) = 0
    rw [matIn_comp, matIn_comp, matIn_comp, ← matIn_id b₂.e2, matIn_add, matIn_sub, matIn_sub]
    convert matIn_zero b₂.e2 b₂.e2
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [heF_heF R₂ R₁ 2 1 3 rfl rfl y, sub_self]
  · change matIn b₁.e3 b₂.e3 (heF R₁ R₂ 3) * matIn b₂.e3 b₁.e3 (heF R₂ R₁ 3) - 1 -
      matIn b₂.e2 b₂.e3 (Y₂.d 2 3 rfl) * matIn b₂.e3 b₂.e2 (heH R₂ R₁ 3 2 rfl) = 0
    rw [matIn_comp, matIn_comp, ← matIn_id b₂.e3, matIn_sub, matIn_sub]
    convert matIn_zero b₂.e3 b₂.e3
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    rw [heF_heF R₂ R₁ 3 2 4 rfl rfl y, b₂.hi (Y₂.d 3 4 rfl y), map_zero, add_zero, sub_self]

end Retracts


/-! ### The stage data from the stage retracts -/

section StageLift

variable {A0 A1 A2 A3 B0 B1 B2 B3 : Type}

/-- **The lift of homotopy-equivalence data along a surjection** (tex 4385–4451), entrywise.
Kind: definition. -/
def HEMat.liftAlong {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (E : HEMat S A0 A1 A2 A3 B0 B1 B2 B3) :
    HEMat R A0 A1 A2 A3 B0 B1 B2 B3 where
  dA0 := E.dA0.map (Function.surjInv hπ)
  dA1 := E.dA1.map (Function.surjInv hπ)
  dA2 := E.dA2.map (Function.surjInv hπ)
  dB0 := E.dB0.map (Function.surjInv hπ)
  dB1 := E.dB1.map (Function.surjInv hπ)
  dB2 := E.dB2.map (Function.surjInv hπ)
  f0 := E.f0.map (Function.surjInv hπ)
  f1 := E.f1.map (Function.surjInv hπ)
  f2 := E.f2.map (Function.surjInv hπ)
  f3 := E.f3.map (Function.surjInv hπ)
  g0 := E.g0.map (Function.surjInv hπ)
  g1 := E.g1.map (Function.surjInv hπ)
  g2 := E.g2.map (Function.surjInv hπ)
  g3 := E.g3.map (Function.surjInv hπ)
  hA1 := E.hA1.map (Function.surjInv hπ)
  hA2 := E.hA2.map (Function.surjInv hπ)
  hA3 := E.hA3.map (Function.surjInv hπ)
  hB1 := E.hB1.map (Function.surjInv hπ)
  hB2 := E.hB2.map (Function.surjInv hπ)
  hB3 := E.hB3.map (Function.surjInv hπ)

/-- The lift specializes to the data (tex 4385–4451). Kind: PROVED. -/
theorem HEMat.liftAlong_map {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (E : HEMat S A0 A1 A2 A3 B0 B1 B2 B3) :
    (E.liftAlong π hπ).map π = E := by
  have hM : ∀ {m n : Type} (M : Matrix m n S), (M.map (Function.surjInv hπ)).map π = M :=
    fun M => by
      ext a b
      exact Function.surjInv_eq hπ (M a b)
  obtain ⟨dA0, dA1, dA2, dB0, dB1, dB2, f0, f1, f2, f3,
    g0, g1, g2, g3, hA1, hA2, hA3, hB1, hB2, hB3⟩ := E
  simp only [HEMat.map, HEMat.liftAlong, hM]

/-- The zero data (tex 4385–4451: the data at the stages outside the retained set).
Kind: definition. -/
def HEMat.zero (R : Type) [CommRing R] : HEMat R A0 A1 A2 A3 B0 B1 B2 B3 where
  dA0 := 0
  dA1 := 0
  dA2 := 0
  dB0 := 0
  dB1 := 0
  dB2 := 0
  f0 := 0
  f1 := 0
  f2 := 0
  f3 := 0
  g0 := 0
  g1 := 0
  g2 := 0
  g3 := 0
  hA1 := 0
  hA2 := 0
  hA3 := 0
  hB1 := 0
  hB2 := 0
  hB3 := 0

variable [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1]
  [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1] [DecidableEq A2] [DecidableEq A3]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq B2] [DecidableEq B3]

/-- **The lifts satisfy the identities modulo the kernel exactly when the data satisfy them**
(tex 4385–4451). Kind: PROVED. -/
theorem HEMat.holds_liftAlong_iff {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (E : HEMat S A0 A1 A2 A3 B0 B1 B2 B3) :
    (E.liftAlong π hπ).Holds (RingHom.ker π) ↔ E.Holds ⊥ := by
  have h := HEMat.holds_map_iff (E.liftAlong π hπ) π ⊥
  rw [HEMat.liftAlong_map] at h
  rw [h, RingHom.ker_eq_comap_bot]

/-- **The lift of stage data to `Λ`** (tex 4385–4451): data over the stage `Λ ⧸ stageIdeal s`,
lifted entrywise. Kind: definition. -/
def stageLiftHE (s : ℕ) (E : HEMat (LamI ⧸ stageIdeal s) A0 A1 A2 A3 B0 B1 B2 B3) :
    HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3 :=
  E.liftAlong (Ideal.Quotient.mk (stageIdeal s)) Ideal.Quotient.mk_surjective

/-- **Exact stage data lift to data satisfying the identities modulo `stageIdeal s`**
(tex 4385–4451): the hypothesis of `HEMat.limit_holds`. Kind: PROVED. -/
theorem stageLiftHE_holds (s : ℕ) (E : HEMat (LamI ⧸ stageIdeal s) A0 A1 A2 A3 B0 B1 B2 B3)
    (h : E.Holds ⊥) : (stageLiftHE s E).Holds (stageIdeal s) := by
  have e := (HEMat.holds_liftAlong_iff (Ideal.Quotient.mk (stageIdeal s))
    Ideal.Quotient.mk_surjective E).2 h
  rwa [Ideal.mk_ker] at e

open scoped Classical in
/-- **The lifted stage data on a set of stages** (tex 4401–4406: a retained set of stages), zero
elsewhere. Kind: definition. -/
def heStagesOn (G : Set ℕ) (E : ∀ s, s ∈ G → HEMat (LamI ⧸ stageIdeal s) A0 A1 A2 A3 B0 B1 B2 B3) :
    ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3 :=
  fun s => if h : s ∈ G then stageLiftHE s (E s h) else HEMat.zero LamI

/-- **Exact stage data on a `U`-large set of stages give exact data over `Λ` in the limit**
(tex 4401–4405, 4444–4450). Kind: PROVED. -/
theorem limit_holds_of_stagesOn (G : Set ℕ)
    (E : ∀ s, s ∈ G → HEMat (LamI ⧸ stageIdeal s) A0 A1 A2 A3 B0 B1 B2 B3) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
    (hE : ∀ s (h : s ∈ G), (E s h).Holds ⊥) : (limitHE (heStagesOn G E) U).Holds ⊥ := by
  refine HEMat.limit_holds _ hU ?_
  filter_upwards [hG] with s hs
  have e : heStagesOn G E s = stageLiftHE s (E s hs) := dite_eq_left hs
  rw [e]
  exact stageLiftHE_holds s _ (hE s hs)

/-- **The comparison of the retained models at the stages passes to the limit** (tex 4189–4193,
4401–4405, 4437–4450: "Retained homotopy inverses remain homotopy inverses"): if at the stages of
a `U`-large set the complex `X s` has two retracts onto finite free models with bases of fixed
index types (for instance a cone model and a graded model), the limit over `Λ` of the lifted
comparison data (`modelEquiv_of_retracts`) satisfies the identities of a homotopy equivalence
exactly. Kind: PROVED. -/
theorem limit_holds_of_retracts (G : Set ℕ) {X Y₁ Y₂ : ∀ s, GCx (LamI ⧸ stageIdeal s)}
    (R₁ : ∀ s, s ∈ G → GRetract (X s) (Y₁ s)) (R₂ : ∀ s, s ∈ G → GRetract (X s) (Y₂ s))
    (b₁ : ∀ s, s ∈ G → FourFree (Y₁ s) A0 A1 A2 A3)
    (b₂ : ∀ s, s ∈ G → FourFree (Y₂ s) B0 B1 B2 B3) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) :
    (limitHE (heStagesOn G fun s h =>
      modelEquiv_of_retracts (R₁ s h) (R₂ s h) (b₁ s h) (b₂ s h)) U).Holds ⊥ :=
  limit_holds_of_stagesOn G _ hU hG fun s h =>
    modelEquiv_of_retracts_holds (R₁ s h) (R₂ s h) (b₁ s h) (b₂ s h)

end StageLift

/-! ### (c) The coordinates of two models related by the comparison -/

section Coordinates

variable {R : Type} [CommRing R] {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1]
  [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0]
  [DecidableEq A1] [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3]

/-- The model `A` of exact homotopy-equivalence data as a four-term complex (tex 4185–4193).
Kind: definition. -/
def HEMat.cxA (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥) : FourCx R A0 A1 A2 A3 where
  d0 := E.dA0
  d1 := E.dA1
  d2 := E.dA2
  d10 := (matIn_bot_iff _).1 hE.cA1
  d21 := (matIn_bot_iff _).1 hE.cA2

/-- The model `B` of exact homotopy-equivalence data as a four-term complex (tex 4185–4193).
Kind: definition. -/
def HEMat.cxB (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥) : FourCx R B0 B1 B2 B3 where
  d0 := E.dB0
  d1 := E.dB1
  d2 := E.dB2
  d10 := (matIn_bot_iff _).1 hE.cB1
  d21 := (matIn_bot_iff _).1 hE.cB2

/-- **The comparison factor is a unit** (tex 4189–4193: "determinants of unit disks. These are
`A_i`-units"): when `f g = 1` in every degree, `det f₁ det f₃ det g₀ det g₂` is a unit.
Kind: PROVED. -/
theorem HEMat.comparison_det_isUnit (E : HEMat R A0 A1 A2 A3 A0 A1 A2 A3)
    (h0 : E.f0 * E.g0 = 1) (h1 : E.f1 * E.g1 = 1) (h2 : E.f2 * E.g2 = 1)
    (h3 : E.f3 * E.g3 = 1) : IsUnit (E.f1.det * E.f3.det * E.g0.det * E.g2.det) := by
  have u : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι R}, P * Q = 1 →
      IsUnit P.det ∧ IsUnit Q.det := fun {ι _ _ P Q} h =>
    ⟨IsUnit.of_mul_eq_one Q.det (by rw [← det_mul, h, det_one]),
      IsUnit.of_mul_eq_one P.det (by rw [← det_mul, mul_eq_one_comm.mp h, det_one])⟩
  exact (((u h1).1.mul (u h3).1).mul (u h0).2).mul (u h2).2

/-- **The coordinates of two models related by an invertible comparison differ by its unit**
(tex 4189–4193: "replacing them by the retained homotopy equivalent free models contributes only
determinants of unit disks"). For exact data between models with the same index types whose
comparison is an isomorphism (`f g = 1` in every degree), the Knudsen–Mumford coordinate of `B`
at the transported class `f₁ z` and functional `λ g₂` is `det f₁ det f₃ det g₀ det g₂` (a unit,
`HEMat.comparison_det_isUnit`) times the coordinate of `A` at `(z, λ)`, for any orientation
(`kmCoord_chainIso`). Kind: PROVED. -/
theorem HEMat.kmCoord_comparison_iso [IsDomain R] (E : HEMat R A0 A1 A2 A3 A0 A1 A2 A3)
    (hE : E.Holds ⊥) (h0 : E.f0 * E.g0 = 1) (h1 : E.f1 * E.g1 = 1) (h2 : E.f2 * E.g2 = 1)
    (h3 : E.f3 * E.g3 = 1) {z : A1 → R} {lam : A2 → R} (hz : (E.cxA hE).d1 *ᵥ z = 0)
    (hlam : lam ᵥ* (E.cxA hE).d1 = 0) (hz' : (E.cxB hE).d1 *ᵥ (E.f1 *ᵥ z) = 0)
    (hlam' : (lam ᵥ* E.g2) ᵥ* (E.cxB hE).d1 = 0) (σ : (A0 ⊕ Unit) ⊕ A2 ≃ A1 ⊕ (A3 ⊕ Unit)) :
    kmCoord (E.cxB hE) (E.f1 *ᵥ z) (lam ᵥ* E.g2) hz' hlam' σ =
      E.f1.det * E.f3.det * E.g0.det * E.g2.det * kmCoord (E.cxA hE) z lam hz hlam σ := by
  have c0 : E.dB0 * E.f0 = E.f1 * E.dA0 := (sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf0)).symm
  have c1 : E.dB1 * E.f1 = E.f2 * E.dA1 := (sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf1)).symm
  have c2 : E.dB2 * E.f2 = E.f3 * E.dA2 := (sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf2)).symm
  have hgf : E.g2 * E.f2 = 1 := mul_eq_one_comm.mp h2
  exact kmCoord_chainIso (C := E.cxA hE) (C' := E.cxB hE)
    ⟨E.f0, E.g0, E.f1, E.g1, E.f2, E.g2, E.f3, E.g3, h0, h1, h2, h3⟩ c0 c1 c2 hz hlam hz' hlam'
    rfl (by rw [vecMul_vecMul, hgf, vecMul_one]) σ

end Coordinates

/-- **The general change of model, NOT proved here** (tex 4189–4193): for exact
homotopy-equivalence data between two four-term models over a domain, of possibly different
ranks, the Knudsen–Mumford coordinate of `B` at the transported class `f₁ z` and functional `λ g₂`
is a unit times the coordinate of `A` at `(z, λ)`, for any orientations. The case of an
invertible comparison is `HEMat.kmCoord_comparison_iso`. Kind: definition (a statement, not
proved). -/
def KmCoordComparisonUnit (R : Type) [CommRing R] : Prop :=
  ∀ (A0 A1 A2 A3 B0 B1 B2 B3 : Type) [Fintype A0] [Fintype A1] [Fintype A2] [Fintype A3]
    [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0] [DecidableEq A1]
    [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1] [DecidableEq B2]
    [DecidableEq B3] (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥) (z : A1 → R)
    (lam : A2 → R) (hz : (E.cxA hE).d1 *ᵥ z = 0) (hlam : lam ᵥ* (E.cxA hE).d1 = 0)
    (hz' : (E.cxB hE).d1 *ᵥ (E.f1 *ᵥ z) = 0) (hlam' : (lam ᵥ* E.g2) ᵥ* (E.cxB hE).d1 = 0)
    (σA : (A0 ⊕ Unit) ⊕ A2 ≃ A1 ⊕ (A3 ⊕ Unit)) (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)),
    ∃ u : Rˣ, kmCoord (E.cxB hE) (E.f1 *ᵥ z) (lam ᵥ* E.g2) hz' hlam' σB =
      (u : R) * kmCoord (E.cxA hE) z lam hz hlam σA

/-! ### (d) The maps to the original cochains -/

/-- **The remaining item: the limit models carry maps to the original cochains, NOT proved here**
(tex 4438–4439: "The resulting bounded finite free model carries actual maps and homotopies to
the original cochains"; tex 4449–4450: "Mere stagewise quasi-isomorphisms without those maps
would not justify a nonflat coefficient change"). For a complex `XΛ` over `Λ` (the original
cochains with `Λ`-coefficients) and two finite free complexes `Y₁`, `Y₂` over `Λ` with bases, the
limit `limitHE c U` of the stage comparison data is the comparison data of actual retracts of
`XΛ` onto `Y₁` and `Y₂` (`modelEquiv_of_retracts`). The stage retracts of the genuine stage
complexes are not carried through the limit in this tree. Kind: definition (a statement, not
proved). It does NOT hold as stated, since `XΛ` is not tied to the stage complexes: it fails for
`XΛ = 0` (`not_retainedMapsToCochains`). Do not use it as a hypothesis; restate it with the
original cochains whose stage reductions are the stage complexes. -/
def RetainedMapsToCochains {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1]
    [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3]
    [DecidableEq A0] [DecidableEq A1] [DecidableEq A2] [DecidableEq A3] [DecidableEq B0]
    [DecidableEq B1] [DecidableEq B2] [DecidableEq B3] (XΛ Y₁ Y₂ : GCx LamI)
    (b₁ : FourFree Y₁ A0 A1 A2 A3) (b₂ : FourFree Y₂ B0 B1 B2 B3)
    (c : ℕ → HEMat LamI A0 A1 A2 A3 B0 B1 B2 B3) (U : Ultrafilter ℕ) : Prop :=
  ∃ (R₁ : GRetract XΛ Y₁) (R₂ : GRetract XΛ Y₂), modelEquiv_of_retracts R₁ R₂ b₁ b₂ = limitHE c U

end ZInQ.Manuscript.RC.Wiring

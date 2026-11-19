import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentMatrixDisk

/-!
# Theorem 5.3, Lane RC35: the Knudsen–Mumford identification of the ordinary Kummer complex

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), its Kummer
coordinate (tex 3877–3890, 3895–3986, 4005–4018, 4050–4064).

## Which complex the identification is taken over

The coordinate of Definition `ex:arith-coordinate` (tex 3877–3890) enters the calibration (4.6)
through "their ordinary Kummer coordinate" (tex 4063): the coordinate of the central class
`L m_i P` and its paired functional in the inverse determinant line of the **ordinary compact
Kummer complex** `C_K` of `E^{(h)}` over the fixed field `K` (tex 4007), read in its integral
basis. The text computes the torsion factors there: "The ordinary Kummer complex has torsion
lengths `g_𝒜, s_𝒜, g_𝒜` in degrees one, two and three. A torsion disk with cokernel of length `e`
in degree `i` contributes `(−1)^{i+1} e` to the inverse determinant coordinate" (tex 4057–4060),
and "The integral torsion correction is still computed from the ordinary integral Kummer complex
and the integral local quotient triangles, not from their rationally acyclic reductions"
(tex 3982–3984). The complex is central: "At `t = 0` the moving character is trivial" (tex 4280),
and the moving prime is removed only after central specialization (tex 3489–3498). The text's
only `Λ`-adic complex is the address's primitive retained inner limit (tex 4392–4451), which is
compared with `C_K` at the centre: over `A = Λ_(t)` (residue field `ℚ₂`, tex 3925) by the actual
central Kummer comparison `i : K₀ → R₀` (tex 3953–3966), integrally by the support triangle with
the local singular quotients (tex 3489–3498, 4065–4080; the same triangle at the base is (5.7c),
tex 5344–5349). The ring `ℚ₂[[t]]` does not occur in the text; it is the `t`-adic completion of
`Λ_(t)`, and `Λ[1/2] ⊊ Λ_(t) ⊊ ℚ₂[[t]]`.

In the tree, `C_K` is the RC53 group's `compactCentralComplex G` (the genuine Galois Selmer data
over `ℤ₂` of the `2`-adic Tate module of the central twist with the `2`-adic Kummer conditions,
over the address's support `G.S`), and its integral normal form is constructed there
(`integralBlockCentralModel`: the retained finite free model `retainedCentralComplex G hfinite`,
its Smith core-and-disks normalization with the matrix disks `centralDiskMatrix G hfinite j`, and
the integral quasi-isomorphism to `C_K`).

## The Knudsen–Mumford determinant functor (PRINT, not a Lean proposition)

F. Knudsen and D. Mumford, *The projectivity of the moduli space of stable curves I:
Preliminaries on "det" and "Div"*, Math. Scand. 39 (1976) 19–55. Verbatim:

* p. 23: "Next we consider the category `𝒞·_X` of bounded complexes of objects in `𝒞_X`,
  morphisms being all maps of complexes. A map of complexes which induces an isomorphism in
  cohomology will be called a quasi-isomorphism. The subcategory of `𝒞·_X` whose maps are
  quasi-isomorphisms will be called `𝒞·is_X`."
* Definition 1, pp. 23–24: "A determinant functor from `𝒞·is` to `𝒫is` consists of the following
  data: I) For each scheme `X` a functor `f_X` from `𝒞·is_X` to `𝒫is_X`. II) For each scheme `X`
  and for each short-exact sequence: `0 → F'· →α F· →β F''· → 0` in `𝒞·_X` an isomorphism:
  `i_X(α, β): f(F'·) ⊗ f(F''·) ≅ f(F·)`." … "iv) f and i are normalized as follows: a)
  `f(0·) = 1`" … "v) We consider `𝒞is` as a full subcategory of `𝒞·is` by viewing objects of
  `𝒞is` as complexes with only one nonvanishing term, this term being placed in degree zero. Then
  for such objects: `f(F) = det*F`, `i_X(α, β) = i*(α, β)`."
* Theorem 1, p. 25: "There is one and, up to canonical isomorphism, only one determinant functor
  (f, i), which we will write (det, i)."
* p. 25: "Let `X` be a scheme, `H·` an acyclic object in `𝒞·_X`. If (f, i) is a determinant
  functor, we have an isomorphism: `f(0): f(H·) → 1`."
* p. 33: "If `H· = … → 0 → H^i →d H^{i+1} → 0 → …` is an acyclic complex with `i` even we define
  `det(0)` to be the composite `det(H·) = det*(H^{i+1})^{-1} ⊗ det*(H^i) → det*(H^{i+1})^{-1} ⊗
  det*(H^{i+1}) → … → 1`" (the first map `1 ⊗ det*(d)`).
* Theorem 2, p. 42: "There is one, and, up to canonical isomorphism, only one extended
  determinant functor (f, i), which we will write (det, i) again."
* Remark, pp. 42–43: "If `𝓕·` is a perfect complex and you filter it with subcomplexes such that
  the successive quotients `gr^n(𝓕·)` are all perfect, then there is a canonical isomorphism:
  `det(𝓕·) ≅ ⊗ det(gr^n 𝓕·)`." … "b) if the cohomology sheaves `H^n(𝓕·)` of the complex are
  perfect — we call these complexes the objects of the subcategory `Parf⁰ ⊂ Parf` — then
  `det(𝓕·) ≅ ⊗_n det*(H^n(𝓕·))^{(−1)^n}`."
* Corollary 1, p. 43: "Let `𝓕·` and `𝓖·` be two objects of `Parf⁰_X` and suppose `α` and `β`,
  `α, β: 𝓕· ⇉ 𝓖·`, are two quasi-isomorphisms such that `H^i(α) = H^i(β)` for each `i`. Then
  `det(α) = det(β)`."

Neither the tree nor Mathlib has a determinant functor, so these statements are not Lean
propositions here. The formal coordinate is the tree's based torsion `kmCoord` of the class-
and-functional augmented complex (`Torsion/KnudsenMumford.lean`): for complexes of finite free
modules with bases, the normalizations iv), v) and the acyclic case (p. 33: an acyclic two-term
complex `[R^m →B R^m]` has `det(0)` given by `det*(B)`) make the determinant line of a based
complex canonically trivial, and the isomorphism of Remark b) reads the class and the functional
as a vector of `det⁻¹`; `kmCoord` is that vector's coordinate, and the matrix-disk torsion
(`KmIdentMatrixDisk`: a disk contributes `det B^{±1}`, the case p. 33) is the case used here.
That `kmCoord` with its orientations is the coordinate of Definition `ex:arith-coordinate` read
through the Knudsen–Mumford isomorphism (signs included) is a human check. The invariance of the
coordinate under the comparison is the quasi-isomorphism invariance of `det` (Definition 1 I),
Corollary 1); its formal counterparts are `centralKMMap_quasiIso` (`KmIdentGenuine`), the
invariance of `kmCoord` under boundaries of the class and coboundaries of the functional
(`kmCoord_add_boundary_class`, `kmCoord_add_boundary_functional` of `KmIdentMatrixDisk`), and
the uniqueness of the core coordinate (`Central.isClassFunctionalCoord_unique`).

## Contents

* `constQt`, `constUnit`: constants of `ℚ₂[[t]]`; `centralKMDisk G hfinite j`: the constructed
  integral disk determinants as units of `ℚ₂[[t]]`.
* `unitCoreContraction`: the augmented core `[R --a--> R --0--> R --b--> R]` is contractible for
  units `a`, `b`.
* `centralKMIdentModel G hfinite a b`: a Knudsen–Mumford identification (core `[0]` of size one
  with `z₀ = λ₀ = u₀ = 1`, class `a`, functional `b`, disks the constructed integral disks).
* `centralKMCoord G hfinite a b`: its coordinate; `centralKMCoord_eq`, `central_centralKMCoord`,
  `v2_central_centralKMCoord`: `u = a b det B₁ (det B₂)⁻¹ det B₃`.
* `retainedA0`, `retainedB0`, `CentralClassFunctional`, `centralKMIdentModelOf`: the
  identification pinned by a central cycle `z₀` and a closed functional `λ₀` of the retained
  integral model; **G3** (`centralKMIdentModelOf_core`): the central value of the core coordinate
  `a b u₀` is `a₀ b₀`, the coordinate of the free parts of `z₀ ⊗ λ₀` in the retained integral
  basis, exactly.
* `centralKMCoord_eq_normalForm`: the coordinate is the Knudsen–Mumford coordinate of the
  retained integral normal form of `C_K` with its matrix disks, coefficients extended to
  `ℚ₂[[t]]`.
* `retainedE1_cycle`, `retainedFree2_closed`, `CentralClassFunctional.standard`: the retained
  free generator is a cycle, the free-line functional is closed; non-vacuity.
* `isClassFunctionalCoord_central`, `central_eq_of_noJump`: the determinant specialization of a
  two-term model (Version 19's Lemma `lem:v10-determinant-specialization` in the two-term case;
  that lemma is not in the 11/5 manuscript): the coordinate equation specializes at `t = 0`, and
  without a dimension jump the central value is the coordinate of the central tensor.

Kinds: definitions and PROVED. No input.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul v2_mul v2_intCast)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskTie DiskArith)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape centralDiskMatrix
  retainedCentralNormalization
  centralDiskMatrix_det_ne_zero retainedCentralComplex retainedCentralCoordinates)

attribute [local instance] Nat.fact_prime_two

/-! ### Constants of `ℚ₂[[t]]` -/

section Constants

/-- The constant power series of a `2`-adic integer. Kind: definition. -/
def constQt : ℤ_[2] →+* PowerSeries ℚ_[2] :=
  (PowerSeries.C (R := ℚ_[2])).comp PadicInt.Coe.ringHom

/-- `constQt x` is the constant power series `x`. Kind: PROVED. -/
theorem constQt_apply (x : ℤ_[2]) : constQt x = PowerSeries.C ((x : ℚ_[2])) := rfl

/-- The central value of a constant. Kind: PROVED. -/
theorem central_constQt (x : ℤ_[2]) : central (constQt x) = (x : ℚ_[2]) := by
  rw [constQt_apply]
  simp [central]

/-- The unit of `ℚ₂[[t]]` given by a nonzero `2`-adic integer. Kind: definition. -/
def constUnit (x : ℤ_[2]) (hx : x ≠ 0) : (PowerSeries ℚ_[2])ˣ :=
  Units.map (PowerSeries.C (R := ℚ_[2])).toMonoidHom
    (Units.mk0 (x : ℚ_[2]) (PadicInt.coe_ne_zero.2 hx))

/-- The value of a constant unit. Kind: PROVED. -/
theorem constUnit_val (x : ℤ_[2]) (hx : x ≠ 0) :
    ((constUnit x hx : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) = constQt x := rfl

/-- The central value of a constant unit. Kind: PROVED. -/
theorem central_constUnit (x : ℤ_[2]) (hx : x ≠ 0) :
    central ((constUnit x hx : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) = (x : ℚ_[2]) := by
  rw [constUnit_val, central_constQt]

/-- The central value of the inverse of a constant unit. Kind: PROVED. -/
theorem central_constUnit_inv (x : ℤ_[2]) (hx : x ≠ 0) :
    central (((constUnit x hx)⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) =
      (x : ℚ_[2])⁻¹ := by
  have h := congrArg central (constUnit x hx).mul_inv
  rw [central_mul, central_constUnit] at h
  have h1 : central (1 : PowerSeries ℚ_[2]) = 1 := by simp [central]
  rw [h1] at h
  have hx' : (x : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hx
  field_simp
  linear_combination h

end Constants

/-! ### The constructed integral disks -/

section Disks

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **The constructed integral disks of the ordinary Kummer complex** (tex 4057–4060), as units
of `ℚ₂[[t]]`: the determinants of the RC53 group's Smith disk matrices `centralDiskMatrix G
hfinite j` of the retained integral model of `C_K` (the disks with cokernel in degrees one, two,
three for `j = 1, 2, 3`). Kind: definition. -/
def centralKMDisk (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)) (j : ℤ) :
    (PowerSeries ℚ_[2])ˣ :=
  constUnit (centralDiskMatrix G hfinite j).det (centralDiskMatrix_det_ne_zero G hfinite j)

/-- The central value of a constructed disk is the integral disk determinant. Kind: PROVED. -/
theorem central_centralKMDisk (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)) (j : ℤ) :
    central ((centralKMDisk G hfinite j : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) =
      ((centralDiskMatrix G hfinite j).det : ℚ_[2]) :=
  central_constUnit _ _

end Disks

/-! ### The normalized core with a unit class and functional -/

section Core

variable {R : Type} [CommRing R]

/-- `a e₁` is a cycle of the normalized core. Kind: PROVED. -/
theorem twoTerm_zero_hz_smul (a : R) :
    (twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).d1 *ᵥ (a • (1 : Fin 1 → R)) = 0 := by
  simp [twoTerm]

/-- `b e₂*` is a closed functional of the normalized core. Kind: PROVED. -/
theorem twoTerm_zero_hw_smul (b : R) :
    (b • (1 : Fin 1 → R)) ᵥ* (twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).d1 = 0 := by
  simp [twoTerm]

/-- **The augmented normalized core is contractible for a unit class and a unit functional**:
`R --a--> R --0--> R --b--> R` with contraction `a⁻¹`, `b⁻¹` (`[a e₁]` generates `H¹` and `b e₂*`
is an isomorphism on `H²`). Kind: definition (PROVED identities). -/
def unitCoreContraction (a b : Rˣ) :
    Contraction ((twoTerm (0 : Matrix (Fin 1) (Fin 1) R)).aug ((a : R) • 1) ((b : R) • 1)
      (twoTerm_zero_hz_smul _) (twoTerm_zero_hw_smul _)).toBased where
  hOE := 0
  hEO := fromBlocks (of fun _ _ => ((a⁻¹ : Rˣ) : R)) 0 0 (of fun _ _ => ((b⁻¹ : Rˣ) : R))
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro ((e | u) | i) (j | (e' | u')) h
    all_goals first | exact e.elim | exact e'.elim | rfl | exact absurd rfl h
  htpy_E := by
    ext ((e | u) | i) ((e' | u') | i')
    all_goals try first | exact e.elim | exact e'.elim
    all_goals ((try fin_cases i); (try fin_cases i'))
    all_goals simp [FourCx.toBased_dEO, FourCx.toBased_dOE, FourCx.aug, twoTerm, mul_apply,
      Fintype.sum_sum_type]
  htpy_O := by
    ext (i | (e | u)) (i' | (e' | u'))
    all_goals try first | exact e.elim | exact e'.elim
    all_goals ((try fin_cases i); (try fin_cases i'))
    all_goals simp [FourCx.toBased_dEO, FourCx.toBased_dOE, FourCx.aug, twoTerm, mul_apply,
      Fintype.sum_sum_type]

/-- The normalized core has core coordinate `1`: `e₁ ⊗ e₂* = 1 · adj (0)`. Kind: PROVED. -/
theorem isClassFunctionalCoord_zero_one :
    Central.IsClassFunctionalCoord (0 : Matrix (Fin 1) (Fin 1) R) 1 1 1 := by
  unfold Central.IsClassFunctionalCoord
  ext i j
  fin_cases i; fin_cases j
  simp [vecMulVec_apply, adjugate_fin_one]

end Core

/-! ### The constructed identification and its coordinate -/

section Model

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))

/-- The Selmer data of the model identification: the core-and-disks model with the constructed
integral disks and zero local conditions (the target `modelSel` of the tree's consistency
instance). Kind: definition. -/
abbrev centralKMModelSel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData
    (PowerSeries ℚ_[2]) :=
  modelSel (exModel (centralKMDisk G hfinite 1) (centralKMDisk G hfinite 2)
    (centralKMDisk G hfinite 3))

/-- The functional of the model identification: `b` times the weighted degree-two coordinate.
Kind: definition. -/
def centralKMModelLam (b : PowerSeries ℚ_[2]) :
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx (centralKMModelSel G hfinite)).X 2
      →ₗ[PowerSeries ℚ_[2]] PowerSeries ℚ_[2] :=
  b • exLam (centralKMDisk G hfinite 1) (centralKMDisk G hfinite 2) (centralKMDisk G hfinite 3)

/-- **The Knudsen–Mumford identification with the constructed integral disks** (tex 3877–3890,
4057–4064): the normalized core `[0]` of size one (`z₀ = λ₀ = u₀ = 1`, the free lines of the
retained integral normal form of `C_K`, whose differential vanishes), the class `a e₁`, the
functional `b e₂*`, and the three disks `centralKMDisk G hfinite j` (the determinants of the
constructed integral disk matrices of `C_K`, constant in `t`, which is the case at `t = 0` where
the moving character is trivial, tex 4280). The target is the model itself; the identification
with the genuine target (the retained integral model of `C_K`) is `centralKMIdent` of
`KmIdentGenuine`. Kind: definition. -/
def centralKMIdentModel (a b : (PowerSeries ℚ_[2])ˣ) :
    KummerModelIdentification (centralKMModelSel G hfinite) where
  n := 1
  Dc := 0
  δ₁ := centralKMDisk G hfinite 1
  δ₂ := centralKMDisk G hfinite 2
  δ₃ := centralKMDisk G hfinite 3
  z₀ := 1
  w₀ := 1
  u₀ := 1
  a := a
  b := b
  z := (a : PowerSeries ℚ_[2]) • 1
  w := (b : PowerSeries ℚ_[2]) • 1
  hzdef := rfl
  hwdef := rfl
  hz := twoTerm_zero_hz_smul _
  hw := twoTerm_zero_hw_smul _
  hcore := unitCoreContraction a b
  hu₀ := isClassFunctionalCoord_zero_one
  φ := modelIncl _
  qis := quasiIso_modelIncl _
  zSel := (modelIncl _).f 1 1 rfl ⟨vec1 (kz ((a : PowerSeries ℚ_[2]) • 1)), vec1_mem _ _⟩
  lamSel := centralKMModelLam G hfinite b
  hclass := rfl
  hfun y := by
    change (b : PowerSeries ℚ_[2]) * (exW ⬝ᵥ vec2 y) = _
    simp [exW, vec2, kw, dotProduct, Fintype.sum_sum_type]

/-- **The ordinary Kummer coordinate in the constructed integral basis**: the Knudsen–Mumford
coordinate of the constructed identification (it depends only on the model data, not on the
target). Kind: definition. -/
def centralKMCoord (a b : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2] :=
  (centralKMIdentModel G hfinite a b).coord

variable {G hfinite}

/-- The class coefficient of the constructed identification. Kind: PROVED. -/
theorem centralKMIdentModel_a (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).a = a := rfl

/-- The functional coefficient of the constructed identification. Kind: PROVED. -/
theorem centralKMIdentModel_b (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).b = b := rfl

/-- **The core coordinate of the constructed identification is `1`** (the normalized core of
the retained integral model). Kind: PROVED. -/
theorem centralKMIdentModel_u₀ (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).u₀ = 1 := rfl

/-- The disks of the constructed identification are the constructed integral disks. -/
theorem centralKMIdentModel_δ₁ (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).δ₁ = centralKMDisk G hfinite 1 := rfl

/-- The degree-two disk of the constructed identification. Kind: PROVED. -/
theorem centralKMIdentModel_δ₂ (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).δ₂ = centralKMDisk G hfinite 2 := rfl

/-- The degree-three disk of the constructed identification. Kind: PROVED. -/
theorem centralKMIdentModel_δ₃ (a b : (PowerSeries ℚ_[2])ˣ) :
    (centralKMIdentModel G hfinite a b).δ₃ = centralKMDisk G hfinite 3 := rfl

/-- **`u = a · b · det B₁ · (det B₂)⁻¹ · det B₃`** for the constructed integral disk matrices
`B_j = centralDiskMatrix G hfinite j` (tex 4057–4060: each disk with cokernel in degree `i`
contributes `det^{(−1)^{i+1}}`). Kind: PROVED. -/
theorem centralKMCoord_eq (a b : (PowerSeries ℚ_[2])ˣ) :
    centralKMCoord G hfinite a b = (a : PowerSeries ℚ_[2]) * b * centralKMDisk G hfinite 1 *
      (((centralKMDisk G hfinite 2)⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) *
      centralKMDisk G hfinite 3 := by
  have h := (centralKMIdentModel G hfinite a b).coord_eq
  rw [centralKMIdentModel_u₀, mul_one] at h
  exact h

/-- The central value of the constructed coordinate. Kind: PROVED. -/
theorem central_centralKMCoord (a b : (PowerSeries ℚ_[2])ˣ) :
    central (centralKMCoord G hfinite a b) = central a * central b *
      ((centralDiskMatrix G hfinite 1).det : ℚ_[2]) *
      ((centralDiskMatrix G hfinite 2).det : ℚ_[2])⁻¹ *
      ((centralDiskMatrix G hfinite 3).det : ℚ_[2]) := by
  rw [centralKMCoord_eq]
  simp only [central_mul, central_centralKMDisk]
  rw [centralKMDisk, central_constUnit_inv]

/-- `v₂ (x⁻¹) = −v₂ x` for a nonzero `2`-adic integer. Kind: PROVED. -/
theorem v2_inv_coe_padicInt (x : ℤ_[2]) (hx : x ≠ 0) :
    v2 ((x : ℚ_[2])⁻¹) = ((-(x.valuation : ℤ) : ℤ) : WithTop ℤ) := by
  have hx' : (x : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hx
  have h := v2_mul ((x : ℚ_[2])⁻¹) (x : ℚ_[2])
  rw [inv_mul_cancel₀ hx', ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt x hx] at h
  have h1 : v2 (1 : ℚ_[2]) = 0 := by simp [v2]
  rw [h1] at h
  have hne : v2 ((x : ℚ_[2])⁻¹) ≠ ⊤ := by
    intro htop
    rw [htop, WithTop.top_add] at h
    exact WithTop.top_ne_coe h.symm
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hm] at h ⊢
  have h' : m + (x.valuation : ℤ) = 0 := by exact_mod_cast h.symm
  congr 1
  omega

/-- The central valuation of a constructed disk is the valuation of the integral disk
determinant. Kind: PROVED. -/
theorem v2_central_centralKMDisk (j : ℤ) :
    v2 (central ((centralKMDisk G hfinite j : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2])) =
      (((centralDiskMatrix G hfinite j).det.valuation : ℤ) : WithTop ℤ) := by
  rw [central_centralKMDisk]
  exact ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _
    (centralDiskMatrix_det_ne_zero G hfinite j)

/-- **The central valuation of the ordinary Kummer coordinate**: `v₂ a(0) + v₂ b(0)` plus the
alternating sum of the valuations of the constructed integral disk determinants (tex 4057–4064).
Kind: PROVED. -/
theorem v2_central_centralKMCoord (a b : (PowerSeries ℚ_[2])ˣ) :
    v2 (central (centralKMCoord G hfinite a b)) = v2 (central a) + v2 (central b) +
      (((centralDiskMatrix G hfinite 1).det.valuation : ℤ) : WithTop ℤ) +
      ((-((centralDiskMatrix G hfinite 2).det.valuation : ℤ) : ℤ) : WithTop ℤ) +
      (((centralDiskMatrix G hfinite 3).det.valuation : ℤ) : WithTop ℤ) := by
  rw [central_centralKMCoord]
  simp only [v2_mul]
  rw [ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _
      (centralDiskMatrix_det_ne_zero G hfinite 1),
    v2_inv_coe_padicInt _ (centralDiskMatrix_det_ne_zero G hfinite 2),
    ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _
      (centralDiskMatrix_det_ne_zero G hfinite 3)]

/-- The constructed integral disk matrices with coefficients extended to `ℚ₂[[t]]`.
Kind: definition. -/
abbrev centralDiskMatQt (j : ℤ) :=
  (centralDiskMatrix G hfinite j).map constQt

/-- The extended disk determinants are the constructed disks. Kind: PROVED. -/
theorem det_centralDiskMatQt (j : ℤ) :
    (centralDiskMatQt (G := G) (hfinite := hfinite) j).det =
      ((centralKMDisk G hfinite j : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) := by
  rw [centralDiskMatQt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- The extended disk determinants are units. Kind: PROVED. -/
theorem isUnit_det_centralDiskMatQt (j : ℤ) :
    IsUnit (centralDiskMatQt (G := G) (hfinite := hfinite) j).det := by
  rw [det_centralDiskMatQt]
  exact (centralKMDisk G hfinite j).isUnit

/-- **The constructed coordinate is the Knudsen–Mumford coordinate of the retained integral normal
form of `C_K`** (tex 3877–3890, 4057–4060): the core with one free line in degrees one and two and
the three constructed MATRIX disks `centralDiskMatrix G hfinite j` (which retain noncyclic
torsion), with coefficients extended to `ℚ₂[[t]]`, the class `a e₁` and the functional `b e₂*`,
in its standard (retained) bases. Kind: PROVED (with the matrix-disk torsion of
`KmIdentMatrixDisk`). -/
theorem centralKMCoord_eq_normalForm (a b : (PowerSeries ℚ_[2])ˣ) :
    centralKMCoord G hfinite a b =
      kmCoord (kummerModelMat (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2]))
          (centralDiskMatQt (G := G) (hfinite := hfinite) 1)
          (centralDiskMatQt (G := G) (hfinite := hfinite) 2)
          (centralDiskMatQt (G := G) (hfinite := hfinite) 3))
        (kzM ((a : PowerSeries ℚ_[2]) • 1)) (kwM ((b : PowerSeries ℚ_[2]) • 1))
        (kummerModelMat_hz _ _ _ _ (twoTerm_zero_hz_smul _))
        (kummerModelMat_hw _ _ _ _ (twoTerm_zero_hw_smul _)) (σKM 1 _ _ _) := by
  rw [kmCoord_kummerModelMat (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2]))
      ((a : PowerSeries ℚ_[2]) • 1) ((b : PowerSeries ℚ_[2]) • 1) ((a : PowerSeries ℚ_[2]) * b * 1)
      (twoTerm_zero_hz_smul _) (twoTerm_zero_hw_smul _) (unitCoreContraction a b)
      (isClassFunctionalCoord_smul _ _ _ isClassFunctionalCoord_zero_one) _ _ _
      (isUnit_det_centralDiskMatQt 1) (isUnit_det_centralDiskMatQt 2)
      (isUnit_det_centralDiskMatQt 3),
    centralKMCoord_eq, det_centralDiskMatQt 1, det_centralDiskMatQt 3]
  have hu : (isUnit_det_centralDiskMatQt (G := G) (hfinite := hfinite) 2).unit =
      centralKMDisk G hfinite 2 := by
    ext
    rw [IsUnit.unit_spec, det_centralDiskMatQt]
  rw [hu, mul_one]

end Model

/-! ### The identification pinned by a central cycle and a closed functional (G3) -/

section Pinned

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

/-- **The free-line coordinate of a degree-one cochain** of the retained integral model of `C_K`,
in the retained integral basis. Kind: definition. -/
def retainedA0 (z0 : (retainedCentralComplex G hfinite).X 1) : ℤ_[2] :=
  retainedCentralCoordinates G hfinite H 1 z0 (.inl ())

/-- The retained free generator of degree two. Kind: definition. -/
def retainedE2 : (retainedCentralComplex G hfinite).X 2 :=
  (retainedCentralCoordinates G hfinite H 2).symm (Pi.single (.inl ()) 1)

/-- **The value of a degree-two functional on the retained free generator** (its free-line
coefficient in the retained integral basis). Kind: definition. -/
def retainedB0 (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) : ℤ_[2] :=
  lam0 ((retainedCentralCoordinates G hfinite H 2).symm (Pi.single (.inl ()) 1))

/-- **A central class and closed functional on the retained integral model of `C_K`** (tex
3895–3909, 3953–3975): a degree-one cycle `z₀` and a closed degree-two functional `λ₀` with nonzero
free-line coefficients (at a known simple zero the class and functional of Lemma
`ex:arith-central-specialization` are nonzero there: their free-line coefficients have valuation
`j_rc + v₂(Lm)`, tex 3904–3906). Supplied by the lane of the point coefficients (the Kummer class
of `L m P` transported to the retained model and its paired functional). Kind: definition
(inputs). -/
structure CentralClassFunctional where
  /-- the central cycle -/
  z0 : (retainedCentralComplex G hfinite).X 1
  /-- it is a cycle -/
  hz0 : ((retainedCentralComplex G hfinite).d 1 2).hom z0 = 0
  /-- the central functional -/
  lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]
  /-- it is closed -/
  hlam0 : lam0 ∘ₗ ((retainedCentralComplex G hfinite).d 1 2).hom = 0
  /-- the free-line coefficient of the class is nonzero -/
  ha0 : retainedA0 G hfinite H z0 ≠ 0
  /-- the free-line coefficient of the functional is nonzero -/
  hb0 : retainedB0 G hfinite H lam0 ≠ 0

variable {G hfinite H}

/-- The class coefficient as a unit of `ℚ₂[[t]]`. Kind: definition. -/
def CentralClassFunctional.aUnit (Z : CentralClassFunctional G hfinite H) :
    (PowerSeries ℚ_[2])ˣ :=
  constUnit (retainedA0 G hfinite H Z.z0) Z.ha0

/-- The functional coefficient as a unit of `ℚ₂[[t]]`. Kind: definition. -/
def CentralClassFunctional.bUnit (Z : CentralClassFunctional G hfinite H) :
    (PowerSeries ℚ_[2])ˣ :=
  constUnit (retainedB0 G hfinite H Z.lam0) Z.hb0

variable (G hfinite H) in
/-- **The identification pinned by the central class and functional**: the constructed
identification with class coefficient `a₀` and functional coefficient `b₀`, the free-line
coefficients of `z₀` and `λ₀` in the retained integral basis. Kind: definition. -/
def centralKMIdentModelOf (Z : CentralClassFunctional G hfinite H) :
    KummerModelIdentification (centralKMModelSel G hfinite) :=
  centralKMIdentModel G hfinite Z.aUnit Z.bUnit

/-- **G3**: the class coefficient of the pinned identification is `C(a₀)`. Kind: PROVED. -/
theorem centralKMIdentModelOf_a (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentModelOf G hfinite H Z).a =
      PowerSeries.C ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) := rfl

/-- **G3**: the functional coefficient of the pinned identification is `C(b₀)`.
Kind: PROVED. -/
theorem centralKMIdentModelOf_b (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentModelOf G hfinite H Z).b =
      PowerSeries.C ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) := rfl

/-- **G3**: the core coordinate of the pinned identification is `1`. Kind: PROVED. -/
theorem centralKMIdentModelOf_u₀ (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentModelOf G hfinite H Z).u₀ = 1 := rfl

/-- **G3: the central value of the core coordinate is the coordinate of the free parts of
`z₀ ⊗ λ₀` in the retained integral basis**, exactly (unit `1`): `central (a b u₀) = a₀ b₀`. For
this identification the specialization from `ℚ₂[[t]]` to the centre (Version 19's Lemma
`lem:v10-determinant-specialization`, not in the 11/5 manuscript) is trivial, the identification
being constant in `t`. Kind: PROVED. -/
theorem centralKMIdentModelOf_core (Z : CentralClassFunctional G hfinite H) :
    central ((centralKMIdentModelOf G hfinite H Z).a * (centralKMIdentModelOf G hfinite H Z).b *
      (centralKMIdentModelOf G hfinite H Z).u₀) =
      ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) *
        ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) := by
  rw [centralKMIdentModelOf_u₀, mul_one, central_mul, centralKMIdentModelOf_a,
    centralKMIdentModelOf_b]
  simp [central]

/-- The coordinate of the pinned identification. Kind: PROVED. -/
theorem centralKMIdentModelOf_coord (Z : CentralClassFunctional G hfinite H) :
    (centralKMIdentModelOf G hfinite H Z).coord = centralKMCoord G hfinite Z.aUnit Z.bUnit :=
  rfl

variable (G hfinite H) in
/-- The retained free generator of degree one. Kind: definition. -/
def retainedE1 : (retainedCentralComplex G hfinite).X 1 :=
  (retainedCentralCoordinates G hfinite H 1).symm (Pi.single (.inl ()) 1)

variable (G hfinite H) in
/-- The free-line coordinate functional of degree two, in the retained integral basis.
Kind: definition. -/
def retainedFree2 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  (LinearMap.proj (Sum.inl ())).comp (retainedCentralCoordinates G hfinite H 2).toLinearMap

/-- The normalization commutes with the degree-one differentials (componentwise form).
Kind: PROVED. -/
theorem retainedNormalization_d12 (x : (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
      (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
      (centralDiskMatrix G hfinite 3)).X 1) :
    ((retainedCentralComplex G hfinite).d 1 2).hom
        (((retainedCentralNormalization G hfinite H).hom.f 1).hom x) =
      ((retainedCentralNormalization G hfinite H).hom.f 2).hom
        (((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
          (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
          (centralDiskMatrix G hfinite 3)).d 1 2).hom x) := by
  have e := congrArg (fun g => ModuleCat.Hom.hom g x)
    ((retainedCentralNormalization G hfinite H).hom.comm 1 2)
  simp only [ModuleCat.hom_comp] at e
  exact e

/-- **The retained free generator of degree one is a cycle.** Kind: PROVED. -/
theorem retainedE1_cycle :
    ((retainedCentralComplex G hfinite).d 1 2).hom (retainedE1 G hfinite H) = 0 := by
  have hx : retainedE1 G hfinite H =
      ((retainedCentralNormalization G hfinite H).hom.f 1).hom
        ((1, 0, 0) : ℤ_[2] × (Fin _ → ℤ_[2]) × (Fin _ → ℤ_[2])) := rfl
  rw [hx]
  refine (retainedNormalization_d12 _).trans ?_
  rw [ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d1]
  convert ((retainedCentralNormalization G hfinite H).hom.f 2).hom.map_zero using 2
  exact Prod.ext rfl (Prod.ext (Matrix.mulVec_zero (centralDiskMatrix G hfinite 2)) rfl)

/-- **The free-line coordinate functional of degree two is closed.** Kind: PROVED. -/
theorem retainedFree2_closed :
    retainedFree2 G hfinite H ∘ₗ ((retainedCentralComplex G hfinite).d 1 2).hom = 0 := by
  refine LinearMap.ext fun y => ?_
  have e := congrArg (fun g => ModuleCat.Hom.hom g y)
    ((retainedCentralNormalization G hfinite H).inv.comm 1 2)
  simp only [ModuleCat.hom_comp] at e
  change ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockCoordinates _ _ _ 2
    (((retainedCentralNormalization G hfinite H).inv.f 2).hom
      (((retainedCentralComplex G hfinite).d 1 2).hom y)) (.inl ()) = 0
  have e' : ((retainedCentralNormalization G hfinite H).inv.f 2).hom
      (((retainedCentralComplex G hfinite).d 1 2).hom y) =
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
          (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
          (centralDiskMatrix G hfinite 3)).d 1 2).hom
        (((retainedCentralNormalization G hfinite H).inv.f 1).hom y) := e.symm
  rw [e', ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d1]
  rfl

/-- The free-line coefficient of the retained free generator is `1`. Kind: PROVED. -/
theorem retainedA0_E1 : retainedA0 G hfinite H (retainedE1 G hfinite H) = 1 := by
  rw [retainedA0, retainedE1, LinearEquiv.apply_symm_apply]
  rfl

/-- The free-line functional takes the value `1` on the retained free generator. Kind: PROVED. -/
theorem retainedB0_free2 : retainedB0 G hfinite H (retainedFree2 G hfinite H) = 1 := by
  change (retainedCentralCoordinates G hfinite H 2 ((retainedCentralCoordinates G hfinite H 2).symm
    (Pi.single (.inl ()) 1))) (.inl ()) = 1
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (G hfinite H) in
/-- **Non-vacuity of `CentralClassFunctional`**: the retained free generator of degree one and
the free-line functional of degree two (both coefficients `1`), for every address datum `G`,
finiteness `hfinite` and shape `H`. Kind: definition (PROVED fields). -/
def CentralClassFunctional.standard : CentralClassFunctional G hfinite H where
  z0 := retainedE1 G hfinite H
  hz0 := retainedE1_cycle
  lam0 := retainedFree2 G hfinite H
  hlam0 := retainedFree2_closed
  ha0 := by rw [retainedA0_E1]; exact one_ne_zero
  hb0 := by rw [retainedB0_free2]; exact one_ne_zero

end Pinned

/-! ### Determinant specialization of a two-term model (Version 19, two-term case) -/

section Specialization

/-- `central` is the constant-coefficient ring homomorphism. -/
theorem central_eq_constantCoeff (f : PowerSeries ℚ_[2]) :
    central f = PowerSeries.constantCoeff f := by
  simp [central]

/-- **The coordinate equation specializes at `t = 0`**: if `z ⊗ λ = u · adj D` over `ℚ₂[[t]]`,
then `z(0) ⊗ λ(0) = u(0) · adj D(0)` (the adjugate commutes with ring homomorphisms). This is the
two-term case of Version 19's Lemma `lem:v10-determinant-specialization` (`quartic_v19.tex`; not
in the 11/5 manuscript). Kind: PROVED. -/
theorem isClassFunctionalCoord_central {n : ℕ} {D : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
    {z w : Fin n → PowerSeries ℚ_[2]} {u : PowerSeries ℚ_[2]}
    (h : Central.IsClassFunctionalCoord D z w u) :
    Central.IsClassFunctionalCoord (D.map central) (fun i => central (z i))
      (fun i => central (w i)) (central u) := by
  unfold Central.IsClassFunctionalCoord at h ⊢
  have hD : D.map central = (PowerSeries.constantCoeff (R := ℚ_[2])).mapMatrix D := by
    ext i j
    simp [central_eq_constantCoeff]
  rw [hD, ← RingHom.map_adjugate]
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, central_eq_constantCoeff]
  rw [← map_mul, ← map_mul, e]

/-- **Without a dimension jump the central value of the coordinate is the coordinate of the
central tensor**: if `z ⊗ λ = u · adj D` over `ℚ₂[[t]]`, `adj D(0) ≠ 0` (the central two-term
complex has the generic dimensions `(1, 1)`) and `z(0) ⊗ λ(0) = c · adj D(0)`, then `u(0) = c`.
Kind: PROVED. -/
theorem central_eq_of_noJump {n : ℕ} {D : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
    {z w : Fin n → PowerSeries ℚ_[2]} {u : PowerSeries ℚ_[2]} {c : ℚ_[2]}
    (h : Central.IsClassFunctionalCoord D z w u) (hjump : (D.map central).adjugate ≠ 0)
    (hc : Central.IsClassFunctionalCoord (D.map central) (fun i => central (z i))
      (fun i => central (w i)) c) :
    central u = c :=
  Central.isClassFunctionalCoord_unique hjump (isClassFunctionalCoord_central h) hc

end Specialization

end ZInQ.Manuscript.RC.Wiring.KmIdent

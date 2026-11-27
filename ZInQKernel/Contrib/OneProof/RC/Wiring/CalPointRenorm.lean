import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit

/-!
# Theorem 5.3, Lane RC34: what the free coefficients of the calibration block carry

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 4057–4064) and Definition
`ex:arith-coordinate` (tex 3877–3892). The RC53 group's Kummer blocks (`KummerCoordinateBlock`,
`KummerCoordinateBlockG`, and the literature form `KummerCoordinateBlockLit`) carry, beside the
Knudsen–Mumford identification `I`, seven fields for the point half of the Kummer valuation:

  `aP`, `bP`, `ha : I.a = C m · aP`, `hb : I.b = C m · bP`,
  `haP : v₂ a_P(0) = j_rc + v₂L`, `hbP : v₂ b_P(0) = j_rc + v₂L`, `hu₀ : v₂ u₀(0) = 0`.

**Finding (PROVED here): only `a · b · u₀` is intrinsic.** In a
`KummerModelIdentification` the class is `z = a • z₀`, the functional `w = b • w₀`, and
`z₀ ⊗ w₀ = u₀ · adj D_c`. Rescaling `z₀ ↦ α⁻¹ z`, `w₀ ↦ β⁻¹ w`, `a ↦ α`, `b ↦ β`,
`u₀ ↦ α⁻¹ β⁻¹ (a b u₀)` (`KMRenorm`) changes neither the class, the functional, the comparison,
the disks nor the coordinate (`kmRenorm_coord`), and preserves `a · b · u₀` (`kmRenorm_core`),
which is the class-functional coordinate of the core (`core_isCoord`, unique when
`adj D_c ≠ 0`: `core_unique`). Consequently the seven fields carry exactly one equation:

* `KummerCoordinateBlockG.core_v2`: a block gives `v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)`;
* `sevenFields_of_core`: conversely, from that single equation (and `m ≠ 0`) some
  renormalization of `I` satisfies all seven fields, with `a_P = b_P = 2^{j + vL}`;
* `sevenFields_iff_core`: the two statements are equivalent.

So the honest content of the point half is the valuation of the central core coordinate, i.e.
of the coordinate of the central class and functional in the retained integral basis; the lane
RC34 files `CalPointAlgebra` and `CalPointCentral` compute it from the genuine objects.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData)
open ZInQ.Contrib.CloudB3RC53.Torsion (KummerModelIdentification isClassFunctionalCoord_smul)
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul v2_mul v2_intCast)

attribute [local instance] Nat.fact_prime_two

/-! ### Renormalization of a Knudsen–Mumford identification -/

section Renorm

variable {S : Type} [CommRing S] [IsDomain S] {D : SelData S}

/-- **Renormalization of the free coefficients** of a Knudsen–Mumford identification by units
`α, β`: the class, functional, comparison, disks and core are unchanged; `a := α`, `b := β`,
`z₀ := α⁻¹ z`, `w₀ := β⁻¹ w`, `u₀ := α⁻¹ β⁻¹ (a b u₀)`. Kind: definition. -/
def KMRenorm (I : KummerModelIdentification D) (α β : Sˣ) : KummerModelIdentification D :=
  { I with
    z₀ := ((α⁻¹ : Sˣ) : S) • I.z
    w₀ := ((β⁻¹ : Sˣ) : S) • I.w
    u₀ := ((α⁻¹ : Sˣ) : S) * ((β⁻¹ : Sˣ) : S) * (I.a * I.b * I.u₀)
    a := α
    b := β
    hzdef := by rw [smul_smul, Units.mul_inv, one_smul]
    hwdef := by rw [smul_smul, Units.mul_inv, one_smul]
    hu₀ := isClassFunctionalCoord_smul I.Dc _ _ I.hu }

variable (I : KummerModelIdentification D) (α β : Sˣ)

/-- The renormalized class coefficient is `α`. PROVED. -/
theorem kmRenorm_a : (KMRenorm I α β).a = α := rfl

/-- The renormalized functional coefficient is `β`. PROVED. -/
theorem kmRenorm_b : (KMRenorm I α β).b = β := rfl

/-- The renormalized core coordinate. PROVED. -/
theorem kmRenorm_u₀ :
    (KMRenorm I α β).u₀ = ((α⁻¹ : Sˣ) : S) * ((β⁻¹ : Sˣ) : S) * (I.a * I.b * I.u₀) := rfl

/-- **Renormalization does not change the Knudsen–Mumford coordinate.** PROVED. -/
theorem kmRenorm_coord : (KMRenorm I α β).coord = I.coord := rfl

/-- Renormalization does not change the disks, the class or the functional. PROVED. -/
theorem kmRenorm_same : (KMRenorm I α β).δ₁ = I.δ₁ ∧ (KMRenorm I α β).δ₂ = I.δ₂ ∧
    (KMRenorm I α β).δ₃ = I.δ₃ ∧ (KMRenorm I α β).z = I.z ∧ (KMRenorm I α β).w = I.w ∧
    (KMRenorm I α β).zSel = I.zSel ∧ (KMRenorm I α β).lamSel = I.lamSel :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Renormalization preserves `a · b · u₀`.** PROVED. -/
theorem kmRenorm_core :
    (KMRenorm I α β).a * (KMRenorm I α β).b * (KMRenorm I α β).u₀ = I.a * I.b * I.u₀ := by
  rw [kmRenorm_a, kmRenorm_b, kmRenorm_u₀]
  have h1 : (α : S) * ((α⁻¹ : Sˣ) : S) = 1 := Units.mul_inv α
  have h2 : (β : S) * ((β⁻¹ : Sˣ) : S) = 1 := Units.mul_inv β
  calc (α : S) * β * (((α⁻¹ : Sˣ) : S) * ((β⁻¹ : Sˣ) : S) * (I.a * I.b * I.u₀)) =
        ((α : S) * ((α⁻¹ : Sˣ) : S)) * ((β : S) * ((β⁻¹ : Sˣ) : S)) * (I.a * I.b * I.u₀) := by
          ring
    _ = I.a * I.b * I.u₀ := by rw [h1, h2, one_mul, one_mul]

/-- **`a · b · u₀` is the class-functional coordinate of the core** (`z ⊗ w = (a b u₀) adj D_c`).
PROVED. -/
theorem core_isCoord : Central.IsClassFunctionalCoord I.Dc I.z I.w (I.a * I.b * I.u₀) := I.hu

/-- **The core coordinate is intrinsic**: when `adj D_c ≠ 0`, `a · b · u₀` is the only
class-functional coordinate of the core class and functional; in particular any two
identifications sharing `D_c`, `z`, `w` have the same `a · b · u₀`. PROVED. -/
theorem core_eq_of_isCoord (hadj : I.Dc.adjugate ≠ 0) {u : S}
    (hu : Central.IsClassFunctionalCoord I.Dc I.z I.w u) : u = I.a * I.b * I.u₀ :=
  Central.isClassFunctionalCoord_unique hadj hu I.hu

end Renorm

/-! ### The seven fields carry exactly one equation -/

section Content

open ZInQ.Contrib.RC53Assist.Calibration (KummerCoordinateBlockG)

/-- `v₂ (2^k) = k` in `ℚ₂`. PROVED. -/
theorem v2_two_zpow (k : ℤ) : v2 ((2 : ℚ_[2]) ^ k) = ((k : ℤ) : WithTop ℤ) := by
  have h2 : v2 (2 : ℚ_[2]) = ((1 : ℤ) : WithTop ℤ) := by
    have h := v2_intCast (n := 2) (by norm_num)
    have hp : padicValInt 2 (2 : ℤ) = 1 := by simp [padicValInt]
    rw [hp] at h
    exact_mod_cast h
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    unfold v2 at h2 ⊢
    rw [AddValuation.map_pow, h2]
    simp
  · rw [zpow_negSucc]
    unfold v2 at h2 ⊢
    rw [AddValuation.map_inv, AddValuation.map_pow, h2]
    simp [Int.negSucc_eq]

/-- `2^k ≠ 0` in `ℚ₂`. PROVED. -/
theorem two_zpow_ne_zero (k : ℤ) : (2 : ℚ_[2]) ^ k ≠ 0 := zpow_ne_zero _ two_ne_zero

/-- A constant power series with nonzero constant is a unit. Kind: definition. -/
def constUnit (c : ℚ_[2]) (hc : c ≠ 0) : (PowerSeries ℚ_[2])ˣ :=
  Units.map (PowerSeries.C (R := ℚ_[2])).toMonoidHom (Units.mk0 c hc)

/-- The value of `constUnit`. PROVED. -/
theorem constUnit_val (c : ℚ_[2]) (hc : c ≠ 0) :
    ((constUnit c hc : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) = PowerSeries.C c := rfl

/-- The central value of the inverse of `constUnit c` is `c⁻¹`. PROVED. -/
theorem central_constUnit_inv (c : ℚ_[2]) (hc : c ≠ 0) :
    central (((constUnit c hc)⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) = c⁻¹ := by
  have h := congrArg central (Units.inv_mul (constUnit c hc))
  rw [central_mul, constUnit_val] at h
  have h1 : central (1 : PowerSeries ℚ_[2]) = 1 := by simp [central]
  have hC : central (PowerSeries.C c) = c := by simp [central]
  rw [h1, hC] at h
  exact eq_inv_of_mul_eq_one_left h

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **A block gives the core equation** `v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)`. PROVED. -/
theorem KummerCoordinateBlockG.core_v2 (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA)
    (hm : m ≠ 0) :
    v2 (central (B.I.a * B.I.b * B.I.u₀)) =
      ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [central_mul, central_mul, v2_mul, v2_mul, B.v2_a hm, B.v2_b hm, B.hu₀, add_zero,
    ← WithTop.coe_add]
  congr 1
  ring

/-- **The seven fields, for an identification `I` and parameters `j, vL, m`**: `I.a = C m · a_P`,
`I.b = C m · b_P`, `v₂ a_P(0) = v₂ b_P(0) = j + vL`, `v₂ u₀(0) = 0`. Kind: definition. -/
def SevenFields {D : SelData (PowerSeries ℚ_[2])} (I : KummerModelIdentification D)
    (j vL m : ℤ) (aP bP : PowerSeries ℚ_[2]) : Prop :=
  I.a = PowerSeries.C (m : ℚ_[2]) * aP ∧ I.b = PowerSeries.C (m : ℚ_[2]) * bP ∧
    v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ) ∧ v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ) ∧
    v2 (central I.u₀) = 0

/-- **The seven fields give the core equation.** PROVED. -/
theorem core_of_sevenFields {D : SelData (PowerSeries ℚ_[2])} (I : KummerModelIdentification D)
    {aP bP : PowerSeries ℚ_[2]} (hm : m ≠ 0) (h : SevenFields I j vL m aP bP) :
    v2 (central (I.a * I.b * I.u₀)) =
      ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  obtain ⟨ha, hb, haP, hbP, hu⟩ := h
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [central_mul, central_mul, v2_mul, v2_mul, ha, hb, central_mul, central_mul, v2_mul, v2_mul,
    hC, v2_intCast hm, haP, hbP, hu, add_zero]
  norm_cast
  ring

/-- **The core equation gives the seven fields for a renormalization of `I`**, with
`a_P = b_P = 2^{j + vL}` and `α = β = m · 2^{j + vL}`. PROVED. -/
theorem sevenFields_of_core {D : SelData (PowerSeries ℚ_[2])} (I : KummerModelIdentification D)
    (hm : m ≠ 0)
    (hcore : v2 (central (I.a * I.b * I.u₀)) =
      ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ)) :
    ∃ (α β : (PowerSeries ℚ_[2])ˣ) (aP bP : PowerSeries ℚ_[2]),
      SevenFields (KMRenorm I α β) j vL m aP bP := by
  have hm' : (m : ℚ_[2]) ≠ 0 := by exact_mod_cast hm
  set c : ℚ_[2] := (m : ℚ_[2]) * (2 : ℚ_[2]) ^ (j + vL) with hcdef
  have hc : c ≠ 0 := mul_ne_zero hm' (two_zpow_ne_zero _)
  have hv2c : v2 c = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hcdef, v2_mul, v2_intCast hm, v2_two_zpow, ← WithTop.coe_add]
    congr 1
    ring
  refine ⟨constUnit c hc, constUnit c hc, PowerSeries.C ((2 : ℚ_[2]) ^ (j + vL)),
    PowerSeries.C ((2 : ℚ_[2]) ^ (j + vL)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [kmRenorm_a, constUnit_val, hcdef, map_mul]
  · rw [kmRenorm_b, constUnit_val, hcdef, map_mul]
  · simp only [central, PowerSeries.coeff_zero_C]
    exact v2_two_zpow _
  · simp only [central, PowerSeries.coeff_zero_C]
    exact v2_two_zpow _
  · rw [kmRenorm_u₀, central_mul, central_mul, central_constUnit_inv, v2_mul, v2_mul, hcore]
    have hinv : v2 c⁻¹ = ((-(j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
      unfold v2 at hv2c ⊢
      rw [AddValuation.map_inv, hv2c]
      rfl
    rw [hinv]
    norm_cast
    ring

/-- **The seven fields carry exactly one equation**: some renormalization of `I` satisfies them
if and only if `v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)` (renormalization preserves `a b u₀`).
PROVED. -/
theorem sevenFields_iff_core {D : SelData (PowerSeries ℚ_[2])} (I : KummerModelIdentification D)
    (hm : m ≠ 0) :
    (∃ (α β : (PowerSeries ℚ_[2])ˣ) (aP bP : PowerSeries ℚ_[2]),
      SevenFields (KMRenorm I α β) j vL m aP bP) ↔
      v2 (central (I.a * I.b * I.u₀)) =
        ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  constructor
  · rintro ⟨α, β, aP, bP, h⟩
    rw [← kmRenorm_core I α β]
    exact core_of_sevenFields _ hm h
  · exact sevenFields_of_core I hm

/-- **The seven fields for an identification in central form** (lane RC35's
`centralKMIdentOf`: `I.a = C a₀`, `I.b = C b₀`, `I.u₀ = 1`): if `v₂ a₀ = v₂ b₀ = j + vL + v₂ m`
and `m ≠ 0`, then the seven fields hold for `I` itself, with `a_P = C (a₀ / m)` and
`b_P = C (b₀ / m)` (no renormalization is needed). PROVED. -/
theorem sevenFields_of_central {D : SelData (PowerSeries ℚ_[2])}
    (I : KummerModelIdentification D) {a₀ b₀ : ℚ_[2]} (hm : m ≠ 0)
    (ha : I.a = PowerSeries.C a₀) (hb : I.b = PowerSeries.C b₀) (hu : I.u₀ = 1)
    (ha₀ : v2 a₀ = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ))
    (hb₀ : v2 b₀ = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ)) :
    SevenFields I j vL m (PowerSeries.C (a₀ / (m : ℚ_[2]))) (PowerSeries.C (b₀ / (m : ℚ_[2]))) := by
  have hm' : (m : ℚ_[2]) ≠ 0 := by exact_mod_cast hm
  have hvm : v2 (m : ℚ_[2]) = (((padicValInt 2 m : ℕ) : ℤ) : WithTop ℤ) := v2_intCast hm
  have hdiv : ∀ x : ℚ_[2], v2 x = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) →
      v2 (central (PowerSeries.C (x / (m : ℚ_[2])))) = ((j + vL : ℤ) : WithTop ℤ) := by
    intro x hx
    simp only [central, PowerSeries.coeff_zero_C]
    rw [div_eq_mul_inv, v2_mul, hx]
    have hinv : v2 (m : ℚ_[2])⁻¹ = ((-((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
      unfold v2 at hvm ⊢
      rw [AddValuation.map_inv, hvm]
      rfl
    rw [hinv]
    norm_cast
    ring
  refine ⟨?_, ?_, hdiv a₀ ha₀, hdiv b₀ hb₀, ?_⟩
  · rw [ha, ← map_mul, mul_div_cancel₀ _ hm']
  · rw [hb, ← map_mul, mul_div_cancel₀ _ hm']
  · rw [hu]
    simp [central, v2]

end Content

end ZInQ.Manuscript.RC.CalPoint

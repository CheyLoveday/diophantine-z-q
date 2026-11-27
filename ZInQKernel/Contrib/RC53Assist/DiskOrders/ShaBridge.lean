import ZInQKernel.Contrib.RC53Assist.DiskOrders.SelmerBridge

/-!
# The degree-two disk order of the calibration and the Tate–Shafarevich group

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), proof at
tex 4007–4014 ("the last finite group is Selmer modulo its maximal divisible subgroup"), with
the ordinary Kummer sequence `0 → E(K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K) → Ш(E/K)[2^∞] → 0` (cited at
tex 1098–1104; Silverman X.4.2) and finiteness of `Ш(E/K)[2^∞]` (tex 4003–4004: supplied by the
two analytic hypotheses).

* `KummerSequenceTwoPowerPrint` (PRINT): over `K = ℚ(√k)`, the image of `Sel_{2^∞}(E/K)` in
  `H¹(G_K, E)` is the `2`-primary part of `Ш(E/K)`, and its kernel (the image of
  `E(K) ⊗ ℚ₂/ℤ₂`) is divisible.
* `card_quot_eq_of_kummer`: an injective-image, divisible-kernel algebra lemma: if `j` has
  divisible source and finite cokernel and `φ` has divisible kernel and finite image `P`, then
  `range j = ker φ` and `|coker j| = |P|`.
* `card_selmer_quot_eq_sha`: `|Sel_{2^∞}(E_ℓ/K) / j(free part ⊗ ℚ₂/ℤ₂)| = |Ш(E_ℓ/K)[2^∞]|`.
* **`diskArith_address_sha`**: `DiskArith G t |Ш(E_ℓ/K)[2^∞]|` at an address curve, from the
  cited statements, finiteness of `Ш(E_ℓ/K)[2^∞]`, the coefficient comparison and Selmer corank
  one over `K`.

Kinds: definition (PRINT input), PROVED.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.SelmerTwoPower (Q2Z2)
open ZInQ.Manuscript.RC (SelmerCorankOneOverK)
open ZInQ.Contrib.RC53Assist.DerivedKummer (MilneLocalDualityPrint MilneFiniteLocalDualityPrint)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound
  (MilneFiniteDegreeBoundPrint)
open ZInQ.Contrib.RC53Assist.IntegralDuality
  (NekovarIntegralCompactLocality NekovarIntegralGlobalDuality)

section Print

/-- **PRINT** (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem X.4.2 for the
isogenies `[2^n]`, in the direct limit over `n`; the ordinary Kummer sequence cited at
tex 1098–1104): for an elliptic curve `E/ℚ` and `K = ℚ(√k)`, the sequence
`0 → E(K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K) → Ш(E/K)[2^∞] → 0` is exact. Stated in the two forms used:
a class of `Ш(E/K)` is `2`-primary exactly when it is the image of a Selmer class, and the
kernel of `H¹(G_K, E[2^∞]) → H¹(G_K, E)` (the image of the divisible group `E(K) ⊗ ℚ₂/ℤ₂`) is
divisible inside that kernel. Kind: definition (PRINT input; no inhabitant is supplied). -/
def KummerSequenceTwoPowerPrint : Prop :=
  ∀ (k : ℤ) (E : WeierstrassCurve ℚ), E.IsElliptic →
    (∀ x : shaK (sqrtK k) E, x ∈ AddCommGroup.primaryComponent (shaK (sqrtK k) E) 2 ↔
      ∃ y ∈ selmerK (sqrtK k) E, inclK (sqrtK k) E y = x) ∧
    (∀ y, inclK (sqrtK k) E y = 0 → ∀ n : ℕ, n ≠ 0 →
      ∃ z, inclK (sqrtK k) E z = 0 ∧ n • z = y)

end Print

section Algebra

variable {S T V : Type} [AddCommGroup S] [AddCommGroup T] [AddCommGroup V]

/-- **Cokernel of a divisible image against a divisible kernel**: if `j : V → S` has divisible
source and finite cokernel, and `φ : S → T` has divisible kernel and finite image `P`, then
`|S / j(V)| = |P|`. Kind: PROVED. -/
theorem card_quot_eq_of_kummer (j : V →+ S) (φ : S →+ T) (P : AddSubgroup T) [Finite P]
    (hV : ∀ (v : V) (n : ℕ), n ≠ 0 → ∃ w, n • w = v) (hfin : Finite (S ⧸ j.range))
    (himage : φ.range = P)
    (hker : ∀ y, φ y = 0 → ∀ n : ℕ, n ≠ 0 → ∃ z, φ z = 0 ∧ n • z = y) :
    Nat.card (S ⧸ j.range) = Nat.card P := by
  have hjk : j.range = φ.ker := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := hV v (Nat.card P) Nat.card_pos.ne'
      rw [AddMonoidHom.mem_ker, ← hw, map_nsmul, map_nsmul]
      have hP : φ (j w) ∈ P := himage ▸ AddMonoidHom.mem_range.2 ⟨j w, rfl⟩
      have h0 : (Nat.card P) • (⟨φ (j w), hP⟩ : P) = 0 := card_nsmul_eq_zero'
      exact congrArg Subtype.val h0
    · intro hx
      have hM : Nat.card (S ⧸ j.range) ≠ 0 := Nat.card_pos.ne'
      obtain ⟨z, -, hz⟩ := hker x hx _ hM
      rw [← QuotientAddGroup.eq_zero_iff, ← hz, QuotientAddGroup.mk_nsmul]
      exact card_nsmul_eq_zero'
  rw [Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hjk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv,
    Nat.card_congr (AddEquiv.addSubgroupCongr himage).toEquiv]

/-- `ℚ₂/ℤ₂` and its finite powers are divisible. Kind: PROVED. -/
theorem q2z2_pi_divisible {r : ℕ} (v : Fin r → Q2Z2) (n : ℕ) (hn : n ≠ 0) :
    ∃ w : Fin r → Q2Z2, n • w = v := by
  have hn' : (n : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.2 hn
  choose q hq using fun i => QuotientAddGroup.mk_surjective (v i)
  refine ⟨fun i => QuotientAddGroup.mk (q i / n), ?_⟩
  funext i
  rw [Pi.smul_apply, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn', hq i]

end Algebra

section ShaBridge

/-- Equality in `ℚ(√k)` is decided classically, as for the point groups of the central model.
Kind: definition. -/
local instance (priority := 10000) quadraticFieldDecEq' (k : ℤ) :
    DecidableEq (QuadraticField k) :=
  fun a b => Classical.propDecidable (a = b)

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))

/-- The Selmer classes mapped to `Ш(E_ℓ/K)`. Kind: definition. -/
def selmerToSha : SelK ℓ k →+ shaK (sqrtK k) (Ecurve ℓ) :=
  AddMonoidHom.codRestrict ((inclK (sqrtK k) (Ecurve ℓ)).comp (SelK ℓ k).subtype)
    (shaK (sqrtK k) (Ecurve ℓ)) (fun x => x.2)

/-- **The Selmer group modulo the image of the integral free part is `Ш(E_ℓ/K)[2^∞]`**
(tex 4010–4014 with the Kummer sequence), for finite `Ш(E_ℓ/K)[2^∞]`. Kind: PROVED (from the
PRINT). -/
theorem card_selmer_quot_eq_sha (hKum : KummerSequenceTwoPowerPrint)
    [Finite (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2)]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve)) :
    Nat.card (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
      (arithmeticCentralFinite ℓ k G hcurve hfinite)).range) =
      Nat.card (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2) := by
  obtain ⟨hA, hB⟩ := hKum k (Ecurve ℓ) inferInstance
  have hcard := card_torsion_two_eq_selmer ℓ k G hcurve hfinite I
  rw [card_torsion_two G hfinite] at hcard
  have hfin : Finite (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
      (arithmeticCentralFinite ℓ k G hcurve hfinite)).range) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ two_ne_zero)
  refine card_quot_eq_of_kummer _ (selmerToSha ℓ k) _ (fun v n hn => q2z2_pi_divisible v n hn)
    hfin ?_ ?_
  · ext x
    rw [hA x, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · intro y hy n hn
    have hy' : inclK (sqrtK k) (Ecurve ℓ) y.1 = 0 := congrArg Subtype.val hy
    obtain ⟨z, hz, hzy⟩ := hB y.1 hy' n hn
    have hzS : z ∈ SelK ℓ k := by
      change inclK (sqrtK k) (Ecurve ℓ) z ∈ shaK (sqrtK k) (Ecurve ℓ)
      rw [hz]
      exact AddSubgroup.zero_mem _
    exact ⟨⟨z, hzS⟩, Subtype.ext hz, Subtype.ext hzy⟩

/-- **`DiskArith` at an address curve with the actual torsion and `Ш` orders**: for Kummer data
`G` over `ℚ(√k)`, `k < 0`, whose central twist is the base change of `E_ℓ`, the disk orders are
`tA = |E^{(h)}(K)[2^∞]|` and `shaA = |Ш(E_ℓ/K)[2^∞]|`, from the eleven PRINT statements (the ten
of `diskArith_address` and `KummerSequenceTwoPowerPrint`), finiteness of `Ш(E_ℓ/K)[2^∞]`, the
places above `2` in the support, the coefficient comparison `I` and Selmer corank one over `K`.
Kind: PROVED (from the named inputs). -/
theorem diskArith_address_sha (hMW : MordellWeilNumberFieldPrint)
    (hKum : KummerSequenceTwoPowerPrint)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hneg : k < 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2)]
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSelC : SelmerCorankOneOverK ℓ k) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      (Nat.card (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2)) := by
  refine diskArith_address ℓ k G hcurve hMW hM hF hH h541 h543 hglob hloc hglobal hlocal hneg h2
    I hSelC _ ?_
  rw [card_selmer_quot_eq_sha ℓ k G hcurve hKum (centralCohomologyFinite G hloc hglob h2) I]
  exact card_primaryComponent_two

end ShaBridge

end ZInQ.Contrib.RC53Assist.DiskOrders

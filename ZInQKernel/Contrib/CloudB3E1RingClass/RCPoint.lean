import ZInQKernel.Contrib.CloudB3E1RingClass.MovingPi
import ZInQKernel.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge
import ZInQKernel.Contrib.CloudB3E2Norm.GenusQuad

/-!
# The ring-class point `P^{rc}_{h,k}`: the `χ_h`-weighted trace and its descent to `E^{(h)}(K)`

Manuscript `diophantine_zq.tex`, tex 2411–2416: "Let `P^{rc}_{h,k'}` be the unaveraged
conductor-`|h|` ring-class sum over `ℚ(√k')`, weighted by `χ_h` … Write `j_rc(h, k')` for its index
valuation." See also tex 3071–3085 and 3895–3907.

Fix a support `S` of `K`, a curve `W/K`, a square root `s ∈ K_S` of `h ∈ K`, and the quadratic
character `χ_h(σ) = σ(s)/s` (`quadChar`). Take a conductor `f` whose primes lie in `S`, with ring
class field `H_f ⊂ K_S` and `Gal(H_f/K)` a quotient of `G_{K,S}` (`ringClassRes`). Let `y ∈ W(K_S)`
be fixed by every element fixing `H_f`. In the text `y` is the realized Heegner point of conductor
`f` (lane E2's `realize`, fixed by `G_{H_f}`: `realize_fixed`).
* **`rcTrace`** (definition): the unaveraged trace `Σ_{τ ∈ Gal(H_f/K)} χ_h(τ̃) · τ̃(y)`, over lifts
  `τ̃ ∈ G_{K,S}` of `τ`. When `χ_h` is trivial on the elements fixing `H_f`, the summands do not
  depend on the lifts (`rcSummand_congr`). This is the case "`QuadOfDelta f`" of genus theory,
  proved by lane E2 for the address characters (`quadOfDelta_family`).
* **`rcTrace_galois`** (PROVED): `σ(P) = χ_h(σ) P` for every `σ ∈ G_{K,S}`; the trace lies in the
  `χ_h`-eigenspace.
* **`rcPointK`** (definition) and **`basePointS_rcPointK`** (PROVED): the trace descends to a point
  of the quadratic twist `E^{(h)} = twistK W h` over `K`. Its image under the twist identification
  `E^{(h)}(K_S) ≅ E(K_S)` (`globalTwistPointEquiv`) is the trace (Galois descent,
  `exists_basePointS_of_fixed`).
* `quadTrivial_of_quadOfDelta` (PROVED): lane E2's `QuadOfDelta f` at `S₀ = S₁ = S` gives the
  triviality hypothesis.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (globalTwistPointEquiv globalTwistPointEquiv_galois)
open ZInQ.Contrib.RC53Assist.CalibrationShape (basePointS basePointS_injective
  exists_basePointS_of_fixed)
open ZInQ.Manuscript.RC.TwistDictionary (twistK)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

/-- The action of `σ ∈ G_{K,S}` on `W(K_S)`. Kind: definition. -/
abbrev galPtS (σ : GKS K S) :
    (W.baseChange (KS K S)).toAffine.Point →+ (W.baseChange (KS K S)).toAffine.Point :=
  Affine.Point.map (galS K S σ).toAlgHom

omit [NumberField K] in
/-- The action is multiplicative. Kind: PROVED. -/
theorem galPtS_mul (σ τ : GKS K S) (P : (W.baseChange (KS K S)).toAffine.Point) :
    galPtS W (σ * τ) P = galPtS W σ (galPtS W τ P) := by
  rw [galPtS, galPtS, galPtS, Affine.Point.map_map]
  rfl

/-- `χ_h(σ) ∈ {±1}`, as an integer. Kind: definition. -/
abbrev chiH (σ : GKS K S) : ℤ := ((quadChar s hs hs0 σ : ℤˣ) : ℤ)

theorem chiH_mul (σ τ : GKS K S) : chiH s hs hs0 (σ * τ) = chiH s hs hs0 σ * chiH s hs hs0 τ := by
  simp [chiH, map_mul]

theorem chiH_sq (σ : GKS K S) : chiH s hs hs0 σ * chiH s hs hs0 σ = 1 := by
  rcases Int.units_eq_one_or (quadChar s hs hs0 σ) with h1 | h1 <;> simp [chiH, h1]

variable {f : ℕ} (hf : f ≠ 0) (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- A chosen lift of `τ ∈ Gal(H_f/K)` to `G_{K,S}`. Kind: definition. -/
def rcLift (τ : ringClassGal f hf S hS) : GKS K S :=
  (ringClassRes_surjective f hf S hS τ).choose

theorem ringClassRes_rcLift (τ : ringClassGal f hf S hS) :
    ringClassRes f hf S hS (rcLift hf hS τ) = τ :=
  (ringClassRes_surjective f hf S hS τ).choose_spec

instance : Finite (ringClassGal f hf S hS) :=
  inferInstanceAs (Finite (ringClassFieldOf f hf S hS ≃ₐ[K] ringClassFieldOf f hf S hS))

instance : Fintype (ringClassGal f hf S hS) := Fintype.ofFinite _

/-- The summand `χ_h(g) · g(y)`. Kind: definition. -/
def rcSummand (y : (W.baseChange (KS K S)).toAffine.Point) (g : GKS K S) :
    (W.baseChange (KS K S)).toAffine.Point :=
  chiH s hs hs0 g • galPtS W g y

variable {W s hs hs0 hf hS}

/-- **The summand depends only on the image in `Gal(H_f/K)`**, when `y` is fixed and `χ_h` is
trivial on the elements fixing `H_f`. Kind: PROVED. -/
theorem rcSummand_congr {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1) {g g' : GKS K S}
    (hgg : ringClassRes f hf S hS g = ringClassRes f hf S hS g') :
    rcSummand W s hs hs0 y g = rcSummand W s hs hs0 y g' := by
  have hk : ringClassRes f hf S hS (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, hgg, inv_mul_cancel]
  have hg' : g' = g * (g⁻¹ * g') := by group
  rw [rcSummand, rcSummand, hg', galPtS_mul, hy _ hk, chiH_mul, hχ _ hk, mul_one]

variable (W s hs hs0 hf hS)

/-- **The `χ_h`-weighted conductor-`f` ring-class trace** `Σ_{τ ∈ Gal(H_f/K)} χ_h(τ̃) τ̃(y)`
(tex 2411–2414), unaveraged. Kind: definition. -/
def rcTrace (y : (W.baseChange (KS K S)).toAffine.Point) :
    (W.baseChange (KS K S)).toAffine.Point :=
  ∑ τ : ringClassGal f hf S hS, rcSummand W s hs hs0 y (rcLift hf hS τ)

variable {W s hs hs0 hf hS}

/-- **The trace lies in the `χ_h`-eigenspace**: `σ(P) = χ_h(σ) P` (tex 2411–2415).
Kind: PROVED. -/
theorem rcTrace_galois {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1) (σ : GKS K S) :
    galPtS W σ (rcTrace W s hs hs0 hf hS y) = chiH s hs hs0 σ • rcTrace W s hs hs0 hf hS y := by
  classical
  have hrw : ∀ τ : ringClassGal f hf S hS,
      galPtS W σ (rcSummand W s hs hs0 y (rcLift hf hS τ)) =
        chiH s hs hs0 σ • rcSummand W s hs hs0 y
          (rcLift hf hS (ringClassRes f hf S hS σ * τ)) := by
    intro τ
    have hc := rcSummand_congr hy hχ (g := σ * rcLift hf hS τ)
      (g' := rcLift hf hS (ringClassRes f hf S hS σ * τ))
      (by rw [map_mul, ringClassRes_rcLift, ringClassRes_rcLift])
    rw [← hc, rcSummand, rcSummand, map_zsmul, ← galPtS_mul, smul_smul, chiH_mul, ← mul_assoc,
      chiH_sq, one_mul]
  unfold rcTrace
  rw [map_sum]
  simp only [hrw]
  rw [← Finset.smul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (ringClassRes f hf S hS σ)) _ _ (fun _ => rfl)

/-- **The twisted trace is fixed by `G_{K,S}`**: its image in `E^{(h)}(K_S)` under the twist
identification. Kind: PROVED. -/
theorem rcTrace_twist_fixed {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1) (σ : GKS K S) :
    Affine.Point.map (galS K S σ).toAlgHom
        ((globalTwistPointEquiv W s hs hs0).symm (rcTrace W s hs hs0 hf hS y)) =
      (globalTwistPointEquiv W s hs hs0).symm (rcTrace W s hs hs0 hf hS y) := by
  apply (globalTwistPointEquiv W s hs hs0).injective
  rw [globalTwistPointEquiv_galois, AddEquiv.apply_symm_apply]
  change chiH s hs hs0 σ • galPtS W σ (rcTrace W s hs hs0 hf hS y) = _
  rw [rcTrace_galois hy hχ, smul_smul, chiH_sq, one_smul]

/-- **The ring-class point `P^{rc}_{h,k} ∈ E^{(h)}(K)`** (tex 2411–2416): the descent of the
`χ_h`-weighted trace to the quadratic twist over `K`. Kind: definition. -/
def rcPointK {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1) :
    (twistK W h).toAffine.Point :=
  (exists_basePointS_of_fixed (twistK W h)
    ((globalTwistPointEquiv W s hs hs0).symm (rcTrace W s hs hs0 hf hS y))
    (rcTrace_twist_fixed hy hχ)).choose

/-- **`P^{rc}` maps to the trace**: over `K_S` and through the twist identification, the
`K`-point is the `χ_h`-weighted trace (Galois descent). Kind: PROVED. -/
theorem basePointS_rcPointK {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1) :
    globalTwistPointEquiv W s hs hs0 (basePointS (twistK W h) (rcPointK hy hχ)) =
      rcTrace W s hs hs0 hf hS y := by
  rw [rcPointK, (exists_basePointS_of_fixed (twistK W h)
    ((globalTwistPointEquiv W s hs hs0).symm (rcTrace W s hs hs0 hf hS y))
    (rcTrace_twist_fixed hy hχ)).choose_spec, AddEquiv.apply_symm_apply]

/-- `P^{rc}` is determined by this property. Kind: PROVED. -/
theorem rcPointK_unique {y : (W.baseChange (KS K S)).toAffine.Point}
    (hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y)
    (hχ : ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1)
    (Q : (twistK W h).toAffine.Point)
    (hQ : globalTwistPointEquiv W s hs hs0 (basePointS (twistK W h) Q) =
      rcTrace W s hs hs0 hf hS y) : Q = rcPointK hy hχ := by
  apply basePointS_injective (S := S) (twistK W h)
  apply (globalTwistPointEquiv W s hs hs0).injective
  rw [hQ, basePointS_rcPointK]

/-! ### The triviality hypothesis from genus theory -/

open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs resAbs_surjective resAbs_apply_coe resUnr_comp)
open ZInQ.Contrib.CloudB3E2.NormCochain (QuadOfDelta toAlgClosure)
open TauCeti.ClassFieldTheory

/-- The restriction along `S ⊆ S` is the identity. Kind: PROVED. -/
theorem inflMap_refl (g : GKS K S) : inflMap K (le_refl S) g = g := by
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S g
  exact resUnr_comp K (le_refl S) σ

/-- **An element restricting to the identity of `H_f` fixes `H_f` inside `K_S`.**
Kind: PROVED. -/
theorem fix_of_ringClassRes_eq_one [NeZero f] {g : GKS K S}
    (hg : ringClassRes f hf S hS g = 1) (z : KS K S)
    (hz : (z : AlgebraicClosure K) ∈ ZInQ.Contrib.CloudB3E2.NormCochain.toAlgClosure
      (TauCeti.ClassFieldTheory.ringClassField
        (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K f))) :
    galS K S g z = z := by
  have hO : ringClassOrder (K := K) f hf = ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K f :=
    ringClassOrder_eq_conductorOrder f
  have hzH : z ∈ ringClassFieldOf f hf S hS := by
    unfold ringClassFieldOf ZInQ.Contrib.CloudB3E2.NormCochain.ringClassFieldS
    rw [IntermediateField.mem_restrict]
    convert hz using 3
  let x : ringClassFieldOf f hf S hS := ⟨z, hzH⟩
  have hc := AlgEquiv.restrictNormal_commutes g (ringClassFieldOf f hf S hS) x
  have h1 : g.restrictNormal (ringClassFieldOf f hf S hS) = 1 := hg
  rw [h1, AlgEquiv.one_apply] at hc
  exact hc.symm

/-- **The triviality of `χ_h` on the elements fixing `H_f`, from lane E2's `QuadOfDelta f`**
(at `S₀ = S₁ = S`; genus theory, `quadOfDelta_family`). Kind: PROVED. -/
theorem quadTrivial_of_quadOfDelta [NeZero f]
    (hQ : QuadOfDelta (le_refl S) (le_refl S) s hs hs0 f) :
    ∀ g, ringClassRes f hf S hS g = 1 → chiH s hs hs0 g = 1 := by
  intro g hg
  have h := hQ g (fun z hz => by
    rw [inflMap_refl]; exact fix_of_ringClassRes_eq_one hg z hz)
  rw [inflMap_refl] at h
  simp [chiH, h]

end ZInQ.Contrib.CloudB3E1RingClass

import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists
import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Discharge

/-!
# Lane RC22 (glue sweep), Tate share: Chebotarev primes for the detecting stage, over `G_ℚ`

Manuscript (11/5 version), Appendix F, proof of Proposition `ex:app-detector`, tex 8362–8374:
"Finite Chebotarev supplies infinitely many good rational primes `ℓ₀` in its conjugacy class ...
Thus `Fr_{ℓ₀} ≡ C (mod 2^M)` ... The determinant also gives `ℓ₀ ≡ −1 (mod 2^M)`." Lane RC12
(`RC/Odd/Detector.lean`) lists Chebotarev and "`det ρ(Fr_{ℓ₀}) = ℓ₀`" as GLUE hypotheses; lane RC10's
(H12) (tex 3088–3100) uses the same two inputs for its retained primes. The same Chebotarev step,
with the same proof, is used in Proposition `ex:arith-moving-character`, tex 3670–3679 ("Finite
Chebotarev supplies infinitely many rational primes in its Frobenius class"), and its determinant
step `det(Fr_r) = r` at tex 3686; lane RC17's `MovingData.exists_frobenius` and
`moving_character_frobenius` (`RC/TateWiring/Kummer.lean`, Lane RC27) take them from here.

The tree proves Chebotarev in the form "Frobenius elements at primes outside `S` are dense in
`G_ℚ`" (`ZInQ.Contrib.ChebFD.C10.frobDense`, from `ZInQ.Contrib.chebotarevExists`, Tau Ceti's
density theorem), with `IsFrobAt h p` meaning `h x ≡ x^p` modulo a prime of `ℤ̄` over `p`. Here:
* `apply_eq_pow_of_isFrobAt`: such an `h` acts on `μ_{2^∞}` as `ζ ↦ ζ^p` for `p` odd (PROVED);
* `torsField E M = ℚ(E[2^M])` is finite over `ℚ`, and agreement on it gives congruent Tate matrices
  modulo `2^M` (`tateMatrix_congr_of_eqOn_torsField`, PROVED);
* `exists_frob_congr`: the Chebotarev step of tex 8362–8372 (and 3670–3679), PROVED with no
  remaining hypothesis;
* `toZModPow_det_eq_of_frob`, `det_tateRep_eq_of_isFrobAt`: `det ρ₂(Fr_p) = p` (tex 3686,
  8372–8374), PROVED from the tree's `det ρ₂ = χ₂`.

The detecting-stage corollary `exists_ell0_congr_neg_one` (`ℓ₀ ≡ −1 (mod 2^M)`) is in `TateOdd.lean`,
next to `ell0_congr_neg_one` (Lane RC27: moved there, with `toZModPow_det_eq_of_frob` moved here, so
that this file needs only the Tate image and Chebotarev and can be imported by lane RC17's
`Kummer.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring
open scoped WeierstrassCurve

/-- In a field, a `2`-power root of unity `η ≠ 1` has a `2`-power power equal to `-1` (PROVED). -/
theorem exists_two_pow_eq_neg_one {K : Type*} [Field K] {η : K} (h1 : η ≠ 1) {M : ℕ}
    (hM : η ^ (2 ^ M) = 1) : ∃ j : ℕ, η ^ (2 ^ j) = -1 := by
  classical
  have hex : ∃ k, η ^ (2 ^ k) = 1 := ⟨M, hM⟩
  have hk : η ^ (2 ^ Nat.find hex) = 1 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk
    exact h1 hk
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨j, ?_⟩
  have hjne : η ^ (2 ^ j) ≠ 1 := Nat.find_min hex (by omega)
  have hsq : (η ^ (2 ^ j)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hj]
    exact hk
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact absurd h hjne
  · exact h

/-- **A Frobenius element at an odd prime `p` acts on the `2`-power roots of unity as `ζ ↦ ζ^p`**
(tex 8362–8374 and 3088–3100: the Frobenius action used with `det ρ = χ_cyc`). `IsFrobAt h p` is the
tree's notion (`ZInQ.Contrib.ChebFD.C10.IsFrobAt`: `h x ≡ x^p` modulo a prime of `ℤ̄` over `p`). Kind:
PROVED (no remaining hypothesis): if `hζ ≠ ζ^p`, then `η = hζ · ζ^{-p} ≠ 1` is a `2`-power root of
unity with `η ≡ 1`, so `-1 = η^{2^j} ≡ 1` and `2` lies in the prime, i.e. `p = 2`. Consumer: the
hypothesis `hfrob` of `ell0_congr_neg_one`, `ell0_mod_four`, `det_tateMatrix_eq_of_frob`,
`H12_divisibility_tate`. -/
theorem apply_eq_pow_of_isFrobAt {h : GalQ} {p : ℕ} (hp2 : p ≠ 2)
    (hF : ZInQ.Contrib.ChebFD.C10.IsFrobAt h p) {M : ℕ} (ζ : Qbar) (hζ : ζ ^ (2 ^ M) = 1) :
    h ζ = ζ ^ p := by
  obtain ⟨P, hP, hPp, hfrob⟩ := hF
  by_contra hne
  have hint : ∀ x : Qbar, x ^ (2 ^ M) = 1 → x ∈ integralClosure ℤ Qbar := by
    intro x hx
    rw [mem_integralClosure_iff]
    refine IsIntegral.of_pow (pow_pos two_pos M) ?_
    rw [hx]
    exact isIntegral_one
  have hhζ : (h ζ) ^ (2 ^ M) = 1 := by rw [← map_pow, hζ, map_one]
  let a : ZInQ.Contrib.ChebFD.C10.Zbar := ⟨ζ, hint ζ hζ⟩
  let b : ZInQ.Contrib.ChebFD.C10.Zbar := ⟨h ζ, hint _ hhζ⟩
  have ha : a ^ (2 ^ M) = 1 := Subtype.ext (by simp [a, hζ])
  have hy : b - a ^ p ∈ P := hfrob a (b - a ^ p) (by simp [a, b])
  set c : ZInQ.Contrib.ChebFD.C10.Zbar := a ^ ((2 ^ M - 1) * p)
  have hac : a ^ p * c = 1 := by
    rw [← pow_add, show p + (2 ^ M - 1) * p = 2 ^ M * p by
      have : p ≤ 2 ^ M * p := Nat.le_mul_of_pos_left p (by positivity)
      rw [Nat.sub_mul, one_mul]; omega]
    rw [pow_mul, ha, one_pow]
  set η : ZInQ.Contrib.ChebFD.C10.Zbar := b * c
  have hη1 : η - 1 ∈ P := by
    have : η - 1 = (b - a ^ p) * c := by
      rw [sub_mul, ← hac]
    rw [this]
    exact P.mul_mem_right c hy
  have hηne : (η : Qbar) ≠ 1 := by
    intro h1
    apply hne
    have h2 : (b : Qbar) * (c : Qbar) * (a : Qbar) ^ p = (a : Qbar) ^ p := by
      rw [show (b : Qbar) * (c : Qbar) = (η : Qbar) from rfl, h1, one_mul]
    have h3 : (c : Qbar) * (a : Qbar) ^ p = 1 := by
      have := congrArg Subtype.val hac
      simpa [mul_comm] using this
    calc h ζ = (b : Qbar) := rfl
      _ = (b : Qbar) * ((c : Qbar) * (a : Qbar) ^ p) := by rw [h3, mul_one]
      _ = (a : Qbar) ^ p := by rw [← mul_assoc, h2]
      _ = ζ ^ p := rfl
  have hηM : (η : Qbar) ^ (2 ^ M) = 1 := by
    have : η ^ (2 ^ M) = 1 := by
      rw [show η = b * c from rfl, mul_pow, show c = a ^ ((2 ^ M - 1) * p) from rfl, ← pow_mul,
        mul_comm ((2 ^ M - 1) * p), pow_mul, ha, one_pow, mul_one]
      exact Subtype.ext (by simp [b, hhζ])
    simpa using congrArg Subtype.val this
  obtain ⟨j, hj⟩ := exists_two_pow_eq_neg_one hηne hηM
  have hj' : η ^ (2 ^ j) = -1 := Subtype.ext (by simpa using hj)
  have h2 : (2 : ZInQ.Contrib.ChebFD.C10.Zbar) ∈ P := by
    have hd : η - 1 ∣ η ^ (2 ^ j) - 1 ^ (2 ^ j) := sub_dvd_pow_sub_pow _ _ _
    obtain ⟨d, hd⟩ := hd
    have hm : η ^ (2 ^ j) - 1 ^ (2 ^ j) ∈ P := by rw [hd]; exact P.mul_mem_right d hη1
    rw [hj', one_pow] at hm
    have : (2 : ZInQ.Contrib.ChebFD.C10.Zbar) = -(-1 - 1) := by ring
    rw [this]
    exact P.neg_mem hm
  have h2Z : (2 : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]
    simpa using h2
  rw [hPp, Ideal.mem_span_singleton] at h2Z
  have hp : p ∣ 2 := by exact_mod_cast h2Z
  rcases (Nat.dvd_prime Nat.prime_two).mp hp with h1 | h1
  · subst h1
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : ℤ) ∈ P.under ℤ := by rw [hPp]; simp
    rw [Ideal.under, Ideal.mem_comap] at this
    simpa using this
  · exact hp2 h1


/-- The coordinates `{x, y}` of an affine point (none for the point at infinity). -/
def coordSet {W : WeierstrassCurve.Affine Qbar} : W.Point → Set Qbar
  | .zero => ∅
  | .some x y _ => {x, y}

/-- The coordinate set of a point is finite (PROVED). -/
theorem coordSet_finite {W : WeierstrassCurve.Affine Qbar} (P : W.Point) : (coordSet P).Finite := by
  rcases P with _ | ⟨x, y, _⟩
  · exact Set.finite_empty
  · exact (Set.finite_singleton y).insert x

/-- The coordinates of the points of `E[2^M]`. -/
def torsCoords (E : WeierstrassCurve ℚ) (M : ℕ) : Set Qbar :=
  ⋃ P : TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point M, coordSet (P : (E⁄Qbar).toAffine.Point)

/-- `E[2^M]` is finite (`|E[2^M]| = 4^M`, vendored Tau Ceti), so the set of coordinates of its points
is finite (PROVED). -/
theorem torsCoords_finite (E : WeierstrassCurve ℚ) [E.IsElliptic] (M : ℕ) :
    (torsCoords E M).Finite := by
  have hcard : Nat.card (TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point M) = (2 ^ M) ^ 2 := by
    convert (E⁄Qbar).natCard_tateModuleLevel two_ne_zero_qbar M
  have : Finite (TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point M) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact Set.finite_iUnion fun P => coordSet_finite _

/-- The field `ℚ(E[2^M]) ⊂ ℚ̄` generated by the coordinates of the points of `E[2^M]`. -/
def torsField (E : WeierstrassCurve ℚ) (M : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ (torsCoords E M)

/-- `ℚ(E[2^M])` is a finite extension of `ℚ` (PROVED). -/
instance torsField_finiteDimensional (E : WeierstrassCurve ℚ) [E.IsElliptic] (M : ℕ) :
    FiniteDimensional ℚ (torsField E M) := by
  have : Finite (torsCoords E M) := (torsCoords_finite E M).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/-- Two automorphisms agreeing on `ℚ(E[2^M])` act equally on `E[2^M]`. -/
theorem map_eq_of_eqOn_torsField (E : WeierstrassCurve ℚ) {M : ℕ} {h σ : GalQ}
    (hagree : ∀ x ∈ torsField E M, h x = σ x)
    (P : TauCeti.TateModuleLevel 2 (E⁄Qbar).toAffine.Point M) :
    WeierstrassCurve.Affine.Point.map h.toAlgHom (P : (E⁄Qbar).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom (P : (E⁄Qbar).toAffine.Point) := by
  have hsub : coordSet (P : (E⁄Qbar).toAffine.Point) ⊆ torsField E M := fun z hz =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_iUnion.mpr ⟨P, hz⟩)
  generalize hQ : (P : (E⁄Qbar).toAffine.Point) = Q at hsub
  rcases Q with _ | ⟨x, y, hxy⟩
  · rfl
  · have hx : h x = σ x := hagree x (hsub (by simp [coordSet]))
    have hy : h y = σ y := hagree y (hsub (by simp [coordSet]))
    show WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some _ _ _
    congr 1

/-- **Agreement on `ℚ(E[2^M])` gives congruent Tate matrices modulo `2^M`** (PROVED): the
difference `ρ₂(h) b_j − ρ₂(σ) b_j` projects to `0` in `E[2^M]`, hence lies in `2^M T₂E` (vendored Tau
Ceti `TateModule.proj_eq_zero_iff`). -/
theorem tateMatrix_congr_of_eqOn_torsField (E : WeierstrassCurve ℚ) [E.IsElliptic] {M : ℕ}
    {h σ : GalQ} (hagree : ∀ x ∈ torsField E M, h x = σ x) :
    (PadicInt.toZModPow M).mapMatrix (tateMatrix E h) =
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← sub_eq_zero, ← map_sub]
  set w := tateRep E 2 h (tateBasis E j) - tateRep E 2 σ (tateBasis E j) with hw
  have hproj : TauCeti.TateModule.proj M w = 0 := by
    apply Subtype.ext
    rw [hw, map_sub, AddSubgroup.coe_sub, coe_proj_tateRep, coe_proj_tateRep,
      map_eq_of_eqOn_torsField E hagree, sub_self, ZeroMemClass.coe_zero]
  obtain ⟨y, hy⟩ := TauCeti.TateModule.proj_eq_zero_iff.mp hproj
  have hent : tateMatrix E h i j - tateMatrix E σ i j = (2 : ℤ_[2]) ^ M * (tateBasis E).repr y i := by
    rw [tateMatrix, tateMatrix, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, ← sub_eq_zero]
    have : (tateBasis E).repr (tateRep E 2 h (tateBasis E j)) i -
        (tateBasis E).repr (tateRep E 2 σ (tateBasis E j)) i = (tateBasis E).repr w i := by
      rw [hw, map_sub, Finsupp.sub_apply]
    rw [this, hy, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  rw [hent, map_mul, map_pow, map_ofNat]
  have : ((2 : ZMod (2 ^ M))) ^ M = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ M)
  rw [this, zero_mul]

/-- **The Chebotarev step of tex 8362–8372 over `G_ℚ`** ("Finite Chebotarev supplies infinitely many
good rational primes `ℓ₀` in its conjugacy class. Choose a place realizing this representative, and
exclude two, ... and any other finite set"): for `σ ∈ G_ℚ`, `M`, a finite subextension `F₀` and a
finite set `S`, there are a prime `ℓ₀ ∉ S ∪ {2}` and a Frobenius `h` at `ℓ₀` with `h = σ` on `F₀`,
`ρ₂(h) ≡ ρ₂(σ) (mod 2^M)` and `hζ = ζ^{ℓ₀}` on `μ_{2^M}`. Kind: PROVED (no remaining hypothesis),
from the tree's Chebotarev density theorem (`ZInQ.Contrib.ChebFD.C10.frobDense` with
`ZInQ.Contrib.chebotarevExists`). -/
theorem exists_frob_congr (E : WeierstrassCurve ℚ) [E.IsElliptic] (σ : GalQ) (M : ℕ)
    (F₀ : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F₀] (S : Finset ℕ) :
    ∃ (h : GalQ) (ℓ₀ : ℕ), ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ℓ₀ ≠ 2 ∧ ZInQ.Contrib.ChebFD.C10.IsFrobAt h ℓ₀ ∧
      (∀ x ∈ F₀, h x = σ x) ∧
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E h) =
        (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) ∧
      (∀ ζ : Qbar, ζ ^ (2 ^ M) = 1 → h ζ = ζ ^ ℓ₀) := by
  obtain ⟨h, ℓ₀, hprime, hnot, hF, hagree⟩ :=
    ZInQ.Contrib.ChebFD.C10.frobDense ZInQ.Contrib.chebotarevExists (insert 2 S) (F₀ ⊔ torsField E M)
      inferInstance σ
  have h2 : ℓ₀ ≠ 2 := fun h2 => hnot (h2 ▸ Finset.mem_insert_self 2 S)
  refine ⟨h, ℓ₀, hprime, fun hS => hnot (Finset.mem_insert_of_mem hS), h2, hF,
    fun x hx => hagree x (le_sup_left (a := F₀) hx), ?_, fun ζ hζ => apply_eq_pow_of_isFrobAt h2 hF ζ hζ⟩
  exact tateMatrix_congr_of_eqOn_torsField E fun x hx => hagree x (le_sup_right (b := torsField E M) hx)

/-! ### The determinant of a Frobenius element: `det ρ₂(Fr_p) = p` -/

/-- **`det ρ₂(σ) ≡ ℓ₀ (mod 2^M)` for `σ` acting on `μ_{2^M}` as `ζ ↦ ζ^{ℓ₀}`** (PROVED from the tree's
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`, every elliptic `E/ℚ`). Lane RC27:
moved here from `TateOdd.lean` (statement and proof unchanged). -/
theorem toZModPow_det_eq_of_frob (E : WeierstrassCurve ℚ) [E.IsElliptic] {M ℓ₀ : ℕ} (σ : GalQ)
    (hfrob : ∀ ζ : Qbar, ζ ^ (2 ^ M) = 1 → σ ζ = ζ ^ ℓ₀) :
    PadicInt.toZModPow M (LinearMap.det (tateRep E 2 σ)) = (ℓ₀ : ZMod (2 ^ M)) := by
  rw [ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic E σ,
    show (cyclotomicCharacter Qbar 2 σ.toRingEquiv : ℤ_[2]) =
      (cyclotomicCharacter Qbar 2 σ.toRingEquiv).val from rfl, cyclotomicCharacter.toZModPow]
  symm
  refine modularCyclotomicCharacter.unique _ _ σ.toRingEquiv fun t ht => ?_
  have htM : (t : Qbar) ^ (2 ^ M) = 1 := by
    have h := congrArg Units.val ((mem_rootsOfUnity _ _).mp ht)
    simpa using h
  rw [ZMod.val_natCast]
  change σ (t : Qbar) = (t : Qbar) ^ (ℓ₀ % 2 ^ M)
  rw [hfrob _ htM]
  conv_lhs => rw [← Nat.div_add_mod ℓ₀ (2 ^ M), pow_add, pow_mul, htM, one_pow, one_mul]

/-- **`det ρ₂(Fr_p) = p`** (tex 3686: "`det(Fr_r) = r`"; tex 8372–8374): for an elliptic `E/ℚ`, an
odd prime `p` and an arithmetic Frobenius element `h ∈ G_ℚ` at `p` (the tree's `IsFrobAt`), the
determinant of `ρ_T(h)` on `T₂E` is `p`. Kind: PROVED (no remaining hypothesis): `h` acts on every
`μ_{2^M}` as `ζ ↦ ζ^p` (`apply_eq_pow_of_isFrobAt`), so `det ρ₂(h) ≡ p (mod 2^M)` for every `M`
(`toZModPow_det_eq_of_frob`, from the tree's `det ρ₂ = χ₂`). Consumer: lane RC17's
`moving_character_frobenius` (`v₂ det(1 ± Fr_r) ≤ c_E`, tex 3690–3691). -/
theorem det_tateRep_eq_of_isFrobAt (E : WeierstrassCurve ℚ) [E.IsElliptic] {h : GalQ} {p : ℕ}
    (hp2 : p ≠ 2) (hF : ZInQ.Contrib.ChebFD.C10.IsFrobAt h p) :
    LinearMap.det (tateRep E 2 h) = (p : ℤ_[2]) := by
  rw [← PadicInt.ext_of_toZModPow]
  intro M
  rw [toZModPow_det_eq_of_frob E h (fun ζ hζ => apply_eq_pow_of_isFrobAt hp2 hF ζ hζ), map_natCast]

end ZInQ.Manuscript.RC.GlueSweep.Tate

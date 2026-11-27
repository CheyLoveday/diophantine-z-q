import ZInQKernel.Contrib.OneProof.RC.Odd.Statements
import ZInQKernel.Contrib.OneProof.RC.Skeleton.Steps
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.IndexAlgebra

/-!
# Lane RC22 (glue sweep), odd share: visibility (O.8) — the skeleton field and the native index

Manuscript (11/5), Appendix F, Proposition `ex:app-visibility` (tex 9407–9445), used through the
field `RCSteps.visibility` of lane RC0's skeleton.

Lane RC12 proves (O.8) (`Odd.visibility_of_comparison`) from three hypotheses: `hO7` (the
comparison (O.7), ELLIOT + PRINT), `hnative` (the native-index lower bound, tex 9422–9428,
ELLIOT/GLUE) and `htorsion` (the height formula makes the genus point torsion when `D` is not a
simple zero, and `L` kills torsion, tex 9439–9441). This file:

* `visibility_field_of_comparison`: the skeleton's field `RCSteps.visibility`, verbatim, from lane
  RC12's `visibility_of_comparison` at `SimpleZero D := ord_{s=1} L(E^{(D)}, s) = 1`
  (`AnalyticRank (Etw ℓ D) 1`). The skeleton's field is therefore no longer an independent input:
  it is discharged by lane RC12's theorem from `hO7`, `hnative`, `htorsion`.
* `hnative_of_index`: lane RC12's `hnative` from the index algebra of the batch-3 `GenusOdd` area
  (`GenusOdd.le_twoDivIndex_iff`, PROVED), once `λ_θ(D)` is read as an additive Kummer functional
  `Λ_θ` (`λ_M ∘ red ∘ L`, tex 8378–8390, 8439–8456) applied to the genus point `P_D` of a native
  lattice, `Λ_θ` killing torsion (the multiplier `L`, tex 8274–8306), and `j_gen(D)` is the index
  valuation of `P_D` in that lattice (`GenusOdd.twoDivIndex`, the definition used by
  `GenusOdd.jgenOf`, tex 2411–2415, 9426).
* `htorsion_of_torsion`: lane RC12's `htorsion` from the torsion of `P_D` and the same functional.
* `htorsion_of_index_top`: lane RC12's `htorsion` from infinite index of `P_D` (the form proved at
  the genuine genus datum in `OddGenusTorsion.lean`, `genusIndex_eq_top_of_not_simpleZero`).
* `visibility_of_index`, `visibility_field_of_index`: (O.8), and the skeleton field, with `hnative`
  removed and `htorsion` replaced by infinite index of the genus point at non-simple zeros.

Kinds: every theorem here is PROVED from the hypotheses it lists. `ThetaComparison` ((O.7)) stays
ELLIOT + PRINT; the torsion of `P_D` at non-simple zeros is the qualitative Cai–Shu–Tian step
(PRINT `CST.CSTThm11Split` with the genus-character factorization, not proved in the tree in this
form); the Kummer functional and its torsion-killing property are the interface data of lane
RC12's detector (tex 8274–8456).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Odd

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **PROVED.** Lane RC12's `vZ` (`Padic.addValuation` of `((n : ℚ) : ℚ_[2])`) equals the
skeleton's `vZ` (`v2` of `(n : ℚ_[2])`): the two valuations of (O.8) (tex 9407–9445) agree, so lane
RC12's `Odd.visibility_of_comparison` concludes the skeleton field `RCSteps.visibility` (used by
`visibility_field_of_comparison`). -/
theorem vZ_odd_eq (n : ℤ) : ZInQ.Manuscript.RC.Odd.vZ n = ZInQ.Manuscript.RC.vZ n := by
  unfold ZInQ.Manuscript.RC.Odd.vZ ZInQ.Manuscript.RC.vZ ZInQ.Manuscript.RC.v2
  push_cast
  rfl

/-- **The skeleton field `RCSteps.visibility` from lane RC12's (O.8)** (App F
`ex:app-visibility`, tex 9407–9445). PROVED from (O.7) (`hO7`, lane RC12's `ThetaComparison`), the
native-index bound (`hnative`) and the torsion step (`htorsion`), by lane RC12's
`Odd.visibility_of_comparison` at `SimpleZero Dd := AnalyticRank (Etw ℓ Dd) 1`. The conclusion is
the type of the field `RCSteps.visibility` (lane RC0, `Skeleton/Steps.lean`), verbatim.
Consumer: `RCSteps.visibility`; discharger: `Odd.visibility_of_comparison`. -/
theorem visibility_field_of_comparison {ℓ : ℕ} (D : RCData ℓ) (lam : ℕ → ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω)
    (hnative : ∀ θ Dd, D.admissible θ Dd → AnalyticRank (Etw ℓ Dd) 1 → ∀ k : ℕ, k ≤ D.Mθ θ →
      (k : ℤ) ≤ D.jgen Dd - C → (2 : ℤ) ^ k ∣ lam θ Dd)
    (htorsion : ∀ θ Dd, D.admissible θ Dd → ¬ AnalyticRank (Etw ℓ Dd) 1 →
      (2 : ℤ) ^ D.Mθ θ ∣ lam θ Dd) :
    ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
      AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet := by
  obtain ⟨Cdet, h⟩ := ZInQ.Manuscript.RC.Odd.visibility_of_comparison D.Mθ D.aθ lam D.admissible
    (fun Dd => AnalyticRank (Etw ℓ Dd) 1) D.jgen ω C hO7 hnative htorsion
  refine ⟨Cdet, fun θ Dd hD hlt => ?_⟩
  have hlt' : ZInQ.Manuscript.RC.Odd.vZ (D.aθ θ Dd) < (((D.Mθ θ : ℕ) : ℤ) : WithTop ℤ) := by
    rw [vZ_odd_eq]; exact_mod_cast hlt
  obtain ⟨h1, h2⟩ := h θ Dd hD hlt'
  rw [vZ_odd_eq] at h2
  exact ⟨h1, h2⟩

section Index

variable {Pt : ℤ → Type*} [∀ D, AddCommGroup (Pt D)]

/-- **PROVED** (the integer lift in tex 9426–9428, 9439–9441: `λ_θ(D)` is an integer lift of a
residue modulo `2^{M_θ}`). If `(n : ZMod (2^M)) = 2^k • z` with `k ≤ M`, then `2^k ∣ n`. Used by
`two_pow_dvd_of_le_index`, `htorsion_of_index_top`. -/
theorem two_pow_dvd_of_zmod {M k : ℕ} (hk : k ≤ M) {n : ℤ} {z : ZMod (2 ^ M)}
    (h : ((n : ℤ) : ZMod (2 ^ M)) = (2 ^ k : ℕ) • z) : (2 : ℤ) ^ k ∣ n := by
  have : NeZero (2 ^ M) := ⟨pow_ne_zero _ two_ne_zero⟩
  set z' : ℤ := (z.val : ℤ)
  have hz : ((z' : ℤ) : ZMod (2 ^ M)) = z := by
    simp only [z', Int.cast_natCast, ZMod.natCast_zmod_val]
  have h0 : (((n - 2 ^ k * z' : ℤ)) : ZMod (2 ^ M)) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, hz, h, nsmul_eq_mul]
    push_cast
    ring
  have hdvd : ((2 ^ M : ℕ) : ℤ) ∣ n - 2 ^ k * z' :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hdvd' : (2 : ℤ) ^ k ∣ n - 2 ^ k * z' := by
    refine dvd_trans (pow_dvd_pow 2 hk) ?_
    exact_mod_cast hdvd
  have := dvd_add hdvd' (dvd_mul_right ((2 : ℤ) ^ k) z')
  rwa [sub_add_cancel] at this

/-- **The index-algebra core** (tex 9426–9428): if `x` lies in `lat` with index valuation at least
`k` (`x ≡ 2^k G` modulo torsion, `G ∈ lat`), `k ≤ M`, and `n` is an integer lift of `Λ x` for an
additive `Λ : A →+ ZMod (2^M)` killing torsion, then `2^k ∣ n`. PROVED from
`GenusOdd.le_twoDivIndex_iff`. -/
theorem two_pow_dvd_of_le_index {A : Type*} [AddCommGroup A] {lat : AddSubgroup A} {x : A}
    (hx : x ∈ lat) {M k : ℕ} (hk : k ≤ M) (Λ : A →+ ZMod (2 ^ M))
    (hΛ : ∀ t : A, IsOfFinAddOrder t → Λ t = 0) {n : ℤ}
    (hn : ((n : ℤ) : ZMod (2 ^ M)) = Λ x) (hke : (k : ℕ∞) ≤ twoDivIndex lat x) :
    (2 : ℤ) ^ k ∣ n := by
  obtain ⟨G, -, ht⟩ := (le_twoDivIndex_iff hx k).mp hke
  have hsplit : Λ x = (2 ^ k : ℕ) • Λ G := by
    have e : x = (x - (2 ^ k : ℕ) • G) + (2 ^ k : ℕ) • G := by abel
    rw [e, map_add, hΛ _ ht, zero_add, map_nsmul]
  exact two_pow_dvd_of_zmod hk (hn.trans hsplit)

/-- **Lane RC12's native-index bound `hnative` from the index algebra** (tex 9422–9428: "write
`P_D = m_D G + T` in its native rank-one free lattice … `L` kills `T` … an integral Kummer map
cannot decrease `v₂(m_D)`"). PROVED from `GenusOdd.le_twoDivIndex_iff` (index algebra, batch 3)
and the interface: `Λ θ D : Pt D →+ ZMod (2^{M_θ})` is the Kummer functional `λ_{M_θ} ∘ red ∘ L` on
the points carrying `P_D` (additive, killing torsion: `hΛ`), `λ_θ(D)` is an integer lift of
`Λ θ D (P_D)` (`hlam`), and `j_gen(D) − C` is at most the index valuation of `P_D` in its native
lattice `lat D ∋ P_D` (`hj`; with `j_gen` the index valuation itself, as in `GenusOdd.jgenOf`,
`C = 0` works). Consumer: the `hnative` hypothesis of `Odd.visibility_of_comparison` /
`Odd.visibility_O8`; discharger: `GenusOdd.le_twoDivIndex_iff`. -/
theorem hnative_of_index (M : ℕ → ℕ) (lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (C : ℤ)
    (lat : ∀ D, AddSubgroup (Pt D)) (P : ∀ D, Pt D) (hP : ∀ D, P D ∈ lat D)
    (Λ : ∀ θ D, Pt D →+ ZMod (2 ^ M θ))
    (hΛ : ∀ θ D (t : Pt D), IsOfFinAddOrder t → Λ θ D t = 0)
    (hlam : ∀ θ D, admissible θ D → ((lam θ D : ℤ) : ZMod (2 ^ M θ)) = Λ θ D (P D))
    (hj : ∀ D, SimpleZero D → jgen D - C ≤ ((twoDivIndex (lat D) (P D)).toNat : ℤ)) :
    ∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
      (2 : ℤ) ^ k ∣ lam θ D := by
  intro θ D hD hs k hk hkj
  have hkn : k ≤ (twoDivIndex (lat D) (P D)).toNat := by
    have := hkj.trans (hj D hs); exact_mod_cast this
  have hke : (k : ℕ∞) ≤ twoDivIndex (lat D) (P D) :=
    (Nat.cast_le.mpr hkn).trans (ENat.natCast_toNat_le_self _)
  obtain ⟨G, -, ht⟩ := (le_twoDivIndex_iff (hP D) k).mp hke
  have hsplit : Λ θ D (P D) = (2 ^ k : ℕ) • Λ θ D G := by
    have e : P D = (P D - (2 ^ k : ℕ) • G) + (2 ^ k : ℕ) • G := by abel
    rw [e, map_add, hΛ θ D _ ht, zero_add, map_nsmul]
  exact two_pow_dvd_of_zmod hk ((hlam θ D hD).trans hsplit)

/-- **Lane RC12's `htorsion` from the torsion of the genus point** (tex 9439–9441: "if an
admissible odd-sign `D` is not a simple zero … the genus point is torsion, `L` kills it"). PROVED
from the same Kummer-functional interface and `htors` (the genus point is torsion when `D` is not
a simple zero: the qualitative Cai–Shu–Tian step). Consumer: the `htorsion` hypothesis of
`Odd.visibility_of_comparison` / `Odd.visibility_O8`. -/
theorem htorsion_of_torsion (M : ℕ → ℕ) (lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (P : ∀ D, Pt D) (Λ : ∀ θ D, Pt D →+ ZMod (2 ^ M θ))
    (hΛ : ∀ θ D (t : Pt D), IsOfFinAddOrder t → Λ θ D t = 0)
    (hlam : ∀ θ D, admissible θ D → ((lam θ D : ℤ) : ZMod (2 ^ M θ)) = Λ θ D (P D))
    (htors : ∀ θ D, admissible θ D → ¬ SimpleZero D → IsOfFinAddOrder (P D)) :
    ∀ θ D, admissible θ D → ¬ SimpleZero D → (2 : ℤ) ^ M θ ∣ lam θ D := by
  intro θ D hD hs
  have h0 : ((lam θ D : ℤ) : ZMod (2 ^ M θ)) = 0 := by
    rw [hlam θ D hD, hΛ θ D _ (htors θ D hD hs)]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  exact_mod_cast this

/-- **Lane RC12's `htorsion` from infinite index of the genus point** (tex 9439–9441). PROVED
from the Kummer-functional interface and `htop` (the genus point has infinite index valuation in
its native lattice when `D` is not a simple zero; this is what the batch-3 height comparison gives,
`GlueSweep.Odd.genusIndex_eq_top_of_not_simpleZero`), by the index algebra
`GenusOdd.le_twoDivIndex_iff` at `e = M_θ`. Consumer: the `htorsion` hypothesis of
`Odd.visibility_of_comparison` / `Odd.visibility_O8`. -/
theorem htorsion_of_index_top (M : ℕ → ℕ) (lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (lat : ∀ D, AddSubgroup (Pt D)) (P : ∀ D, Pt D)
    (hP : ∀ D, P D ∈ lat D) (Λ : ∀ θ D, Pt D →+ ZMod (2 ^ M θ))
    (hΛ : ∀ θ D (t : Pt D), IsOfFinAddOrder t → Λ θ D t = 0)
    (hlam : ∀ θ D, admissible θ D → ((lam θ D : ℤ) : ZMod (2 ^ M θ)) = Λ θ D (P D))
    (htop : ∀ θ D, admissible θ D → ¬ SimpleZero D → twoDivIndex (lat D) (P D) = ⊤) :
    ∀ θ D, admissible θ D → ¬ SimpleZero D → (2 : ℤ) ^ M θ ∣ lam θ D := by
  intro θ D hD hs
  have hke : ((M θ : ℕ) : ℕ∞) ≤ twoDivIndex (lat D) (P D) := by rw [htop θ D hD hs]; exact le_top
  obtain ⟨G, -, ht⟩ := (le_twoDivIndex_iff (hP D) (M θ)).mp hke
  have hsplit : Λ θ D (P D) = (2 ^ M θ : ℕ) • Λ θ D G := by
    have e : P D = (P D - (2 ^ M θ : ℕ) • G) + (2 ^ M θ : ℕ) • G := by abel
    rw [e, map_add, hΛ θ D _ ht, zero_add, map_nsmul]
  exact two_pow_dvd_of_zmod le_rfl ((hlam θ D hD).trans hsplit)

/-- **(O.8) with the native index and the torsion step reduced to the index valuation** (App F
`ex:app-visibility`, tex 9407–9445). PROVED from (O.7) (`hO7`), the Kummer-functional interface
(`Λ`, `hΛ`, `hlam`), the index reading of `j_gen` (`hj`) and infinite index of the genus point at
non-simple zeros (`htop`), by lane RC12's `Odd.visibility_of_comparison` with
`hnative := hnative_of_index` and `htorsion := htorsion_of_index_top`. Consumer:
`Odd.visibility_of_comparison`. -/
theorem visibility_of_index (M : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison M aθ lam admissible ω)
    (lat : ∀ D, AddSubgroup (Pt D)) (P : ∀ D, Pt D) (hP : ∀ D, P D ∈ lat D)
    (Λ : ∀ θ D, Pt D →+ ZMod (2 ^ M θ))
    (hΛ : ∀ θ D (t : Pt D), IsOfFinAddOrder t → Λ θ D t = 0)
    (hlam : ∀ θ D, admissible θ D → ((lam θ D : ℤ) : ZMod (2 ^ M θ)) = Λ θ D (P D))
    (hj : ∀ D, SimpleZero D → jgen D - C ≤ ((twoDivIndex (lat D) (P D)).toNat : ℤ))
    (htop : ∀ θ D, admissible θ D → ¬ SimpleZero D → twoDivIndex (lat D) (P D) = ⊤) :
    ∃ Cdet : ℤ, ∀ θ D, admissible θ D →
      ZInQ.Manuscript.RC.Odd.vZ (aθ θ D) < ((M θ : ℤ) : WithTop ℤ) →
      SimpleZero D ∧ ((jgen D : ℤ) : WithTop ℤ) ≤
        ZInQ.Manuscript.RC.Odd.vZ (aθ θ D) + (Cdet : WithTop ℤ) :=
  ZInQ.Manuscript.RC.Odd.visibility_of_comparison M aθ lam admissible SimpleZero jgen ω C hO7
    (hnative_of_index M lam admissible SimpleZero jgen C lat P hP Λ hΛ hlam hj)
    (htorsion_of_index_top M lam admissible SimpleZero lat P hP Λ hΛ hlam htop)

/-- **The skeleton field `RCSteps.visibility` with the native index and the torsion step reduced
to the index valuation** (tex 9407–9445). PROVED from (O.7), the Kummer-functional interface, the
index reading of the skeleton's `j_gen` and infinite index of the genus point when
`ord_{s=1} L(E^{(D)}, s) ≠ 1`; the conclusion is the type of `RCSteps.visibility` verbatim.
Consumer: `RCSteps.visibility`; dischargers: `Odd.visibility_of_comparison`,
`GenusOdd.le_twoDivIndex_iff`. -/
theorem visibility_field_of_index {ℓ : ℕ} (D : RCData ℓ) (lam : ℕ → ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω)
    (lat : ∀ Dd, AddSubgroup (Pt Dd)) (P : ∀ Dd, Pt Dd) (hP : ∀ Dd, P Dd ∈ lat Dd)
    (Λ : ∀ θ Dd, Pt Dd →+ ZMod (2 ^ D.Mθ θ))
    (hΛ : ∀ θ Dd (t : Pt Dd), IsOfFinAddOrder t → Λ θ Dd t = 0)
    (hlam : ∀ θ Dd, D.admissible θ Dd → ((lam θ Dd : ℤ) : ZMod (2 ^ D.Mθ θ)) = Λ θ Dd (P Dd))
    (hj : ∀ Dd, AnalyticRank (Etw ℓ Dd) 1 →
      D.jgen Dd - C ≤ ((twoDivIndex (lat Dd) (P Dd)).toNat : ℤ))
    (htop : ∀ θ Dd, D.admissible θ Dd → ¬ AnalyticRank (Etw ℓ Dd) 1 →
      twoDivIndex (lat Dd) (P Dd) = ⊤) :
    ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
      AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet :=
  visibility_field_of_comparison D lam ω C hO7
    (hnative_of_index D.Mθ lam D.admissible (fun Dd => AnalyticRank (Etw ℓ Dd) 1) D.jgen C lat P hP
      Λ hΛ hlam hj)
    (htorsion_of_index_top D.Mθ lam D.admissible (fun Dd => AnalyticRank (Etw ℓ Dd) 1) lat P hP Λ
      hΛ hlam htop)

end Index

end ZInQ.Manuscript.RC.GlueSweep.Odd

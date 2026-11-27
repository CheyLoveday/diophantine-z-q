import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddVisibility
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddGenusTorsion
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# Lane RC22 (glue sweep), odd share: the skeleton field `RCSteps.visibility` at the genuine genus data

Manuscript (11/5), Appendix F, Proposition `ex:app-visibility` (tex 9407–9445), for `E = E_ℓ`.

Lane RC12's (O.8) (`Odd.visibility_of_comparison`) rests on (O.7) and two further hypotheses,
`hnative` (tex 9422–9428) and `htorsion` (tex 9439–9441). At the genuine genus data of the batch-3
`GenusOdd` area (`HeegnerDatum`: the field `K = ℚ(√(D h_*))`, the genus character
`χ = χ_{h_*} ∘ N`, a Heegner point `y`; the genus point `P_D = heegnerSum E χ y` in its native
lattice `eigenLattice E χ`; its index valuation `dat.index`, which is `j_gen` in
`GenusOdd.jgenOf`) both are PROVED here:

* `hnative` by the index algebra (`two_pow_dvd_of_le_index`, from `GenusOdd.le_twoDivIndex_iff`);
* `htorsion` by `genusIndex_eq_top_of_not_simpleZero_final` (Cai–Shu–Tian through
  `GenusOdd.datum_facts_core`, root number `−1`, no simple zero ⇒ `j(P_D) = ∞`).

What remains: (O.7) (`Odd.ThetaComparison`, ELLIOT + PRINT); the printed leaves `Prints` and the
batch-3 GLUE `GlueFinal` (in `visibility_field_genuine_reduced` only `ArtinFactorization`,
`RingClassGalois`, `GenusRoots`: `SplittingCriterion` is PROVED by `Splitting.splittingCriterion_proof`); the meaning of the stage support (`hadm`: an admissible `D` lies in the
prepared filter and `E^{(D)}` has root number `−1`, tex 8206–8221, 2491–2500); a genus datum at
each admissible `D` together with the reading of `λ_θ(D)` as a Kummer functional of `P_D` that
kills torsion (`KummerReading`, tex 8274–8306 for the multiplier `L`, 8378–8456 for `λ_M`).
-/

noncomputable section

open NumberField TauCeti.ClassFieldTheory

namespace ZInQ.Manuscript.RC.GlueSweep.Odd

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **The Kummer reading of `λ_θ(D)` at a genus datum** (interface; tex 8274–8306, 8378–8456):
there is an additive `Λ : E(H₁) →+ ZMod (2^{M_θ})` (the reduction at the detecting prime, the
multiplier `L` and the Kummer row `λ_M = b κ_M`) that kills the torsion of `E(H₁)` and sends the
genus point `P_D = heegnerSum E χ y` to the residue of the integer `λ_θ(D)`. -/
def KummerReading (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) {hstar Dd : ℤ}
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) (Mθ : ℕ) (lamv : ℤ) : Prop :=
  letI := dat.field; letI := dat.nf
  letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
  ∃ Λ : (E.baseChange (ringClassField (conductorOrder dat.K 1))).toAffine.Point →+
      ZMod (2 ^ Mθ),
    (∀ t, IsOfFinAddOrder t → Λ t = 0) ∧
      ((lamv : ℤ) : ZMod (2 ^ Mθ)) = Λ (heegnerSum E dat.χ dat.y)

/-- **The divisibility at one genus datum** (tex 9426–9428): under the Kummer reading, an index
valuation `j(P_D) ≥ k` with `k ≤ M_θ` gives `2^k ∣ λ_θ(D)`. PROVED from
`two_pow_dvd_of_le_index` (index algebra) and `GenusOdd.heegnerSum_mem_eigenLattice`. -/
theorem two_pow_dvd_of_kummerReading {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dd : ℤ}
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) {Mθ k : ℕ} (hk : k ≤ Mθ) {lamv : ℤ}
    (hK : KummerReading E f Lat κ dat Mθ lamv) (hke : (k : ℕ∞) ≤ dat.index) :
    (2 : ℤ) ^ k ∣ lamv := by
  let _ := dat.field; let _ := dat.nf
  let _ := Classical.decEq (ringClassField (conductorOrder dat.K 1))
  obtain ⟨Λ, hΛ, hlam⟩ := hK
  exact two_pow_dvd_of_le_index (heegnerSum_mem_eigenLattice E dat.quad.1 dat.y) hk Λ hΛ hlam hke

/-- **The skeleton field `RCSteps.visibility` at the genuine genus data** (App F
`ex:app-visibility`, tex 9407–9445). For `E = E_ℓ` with its newform `f`, a non-CM period lattice
and parametrization scale, the skeleton data `D : RCData ℓ` with `D.hstar` a genus partner: from
(O.7) (`hO7`, lane RC12's `ThetaComparison`), `Prints`, `GlueFinal`, the meaning of the stage
support (`hadm`), a genus datum with the Kummer reading of `λ_θ(D)` at every admissible `D`
(`hsel`) and the index reading of `j_gen` (`hj`), the conclusion is the type of the field
`RCSteps.visibility` verbatim. PROVED: lane RC12's `hnative` and `htorsion` are discharged
(`two_pow_dvd_of_kummerReading`, `genusIndex_eq_top_of_not_simpleZero_final`), and
`visibility_field_of_comparison` (lane RC12's `Odd.visibility_of_comparison`) concludes.
Consumer: `RCSteps.visibility`; dischargers: `Odd.visibility_of_comparison`,
`GenusOdd.le_twoDivIndex_iff`, `GenusOdd.datum_facts_core` (via
`genusIndex_eq_top_of_not_simpleZero_final`). -/
theorem visibility_field_genuine (Pr : Prints) (G : GlueFinal) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (D : RCData ℓ) (hgp : GenusPartner (Ecurve ℓ) D.hstar) (lam : ℕ → ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω)
    (hadm : ∀ θ Dd, D.admissible θ Dd →
      Prepared (Ecurve ℓ) D.hstar Dd ∧ RootNumber (Etw ℓ Dd) (-1))
    (sel : (Dd : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (Dd * D.hstar) 1 D.hstar))
    (hsel : ∀ θ Dd, D.admissible θ Dd → ∃ dat, sel Dd = some dat ∧
      KummerReading (Ecurve ℓ) f Lat κ dat (D.Mθ θ) (lam θ Dd))
    (hj : ∀ Dd dat, sel Dd = some dat → AnalyticRank (Etw ℓ Dd) 1 →
      D.jgen Dd - C ≤ (dat.index.toNat : ℤ)) :
    ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
      AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet := by
  refine visibility_field_of_comparison D lam ω C hO7 ?_ ?_
  · intro θ Dd hD hs k hk hkj
    obtain ⟨dat, hdat, hK⟩ := hsel θ Dd hD
    have hkn : k ≤ dat.index.toNat := by
      have := hkj.trans (hj Dd dat hdat hs); exact_mod_cast this
    exact two_pow_dvd_of_kummerReading dat hk hK
      ((Nat.cast_le.mpr hkn).trans (ENat.natCast_toNat_le_self _))
  · intro θ Dd hD hns
    obtain ⟨dat, -, hK⟩ := hsel θ Dd hD
    have htop : dat.index = ⊤ :=
      genusIndex_eq_top_of_not_simpleZero_final Pr G (Ecurve ℓ) rfl rfl f hf Lat hLat hNC κ hκ
        D.hstar hgp Dd (hadm θ Dd hD).1 (hadm θ Dd hD).2 hns dat
    exact two_pow_dvd_of_kummerReading dat le_rfl hK (by rw [htop]; exact le_top)

/-- **The same with `j_gen` read off the selection** (`D.jgen = GenusOdd.jgenOf …`, the definition
of the batch-3 area, tex 2411–2415): the index hypothesis holds with `C = 0` by definition.
PROVED. -/
theorem visibility_field_genuine_jgenOf (Pr : Prints) (G : GlueFinal) {ℓ : ℕ}
    [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (D : RCData ℓ) (hgp : GenusPartner (Ecurve ℓ) D.hstar) (lam : ℕ → ℤ → ℤ) (ω : ℕ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω)
    (hadm : ∀ θ Dd, D.admissible θ Dd →
      Prepared (Ecurve ℓ) D.hstar Dd ∧ RootNumber (Etw ℓ Dd) (-1))
    (sel : (Dd : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (Dd * D.hstar) 1 D.hstar))
    (hsel : ∀ θ Dd, D.admissible θ Dd → ∃ dat, sel Dd = some dat ∧
      KummerReading (Ecurve ℓ) f Lat κ dat (D.Mθ θ) (lam θ Dd))
    (hjgen : D.jgen = jgenOf (Ecurve ℓ) f Lat κ D.hstar sel) :
    ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
      AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet :=
  visibility_field_genuine Pr G hf hLat hNC hκ D hgp lam ω 0 hO7 hadm sel hsel
    (fun Dd dat hdat _ => by simp [hjgen, jgenOf, hdat])

/-- **The skeleton field at the genuine genus data, with the splitting criterion discharged**
(tex 9407–9445). PROVED: `visibility_field_genuine` with
`GlueFinal := ⟨hArtin, hGal, hRoots, Splitting.splittingCriterion_proof⟩`. Remaining GLUE of the
batch-3 area: `ArtinFactorization`, `RingClassGalois`, `GenusRoots`. -/
theorem visibility_field_genuine_reduced (Pr : Prints) (hArtin : ArtinFactorization)
    (hGal : RingClassGalois) (hRoots : GenusRoots) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (D : RCData ℓ) (hgp : GenusPartner (Ecurve ℓ) D.hstar) (lam : ℕ → ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ZInQ.Manuscript.RC.Odd.ThetaComparison D.Mθ D.aθ lam D.admissible ω)
    (hadm : ∀ θ Dd, D.admissible θ Dd →
      Prepared (Ecurve ℓ) D.hstar Dd ∧ RootNumber (Etw ℓ Dd) (-1))
    (sel : (Dd : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (Dd * D.hstar) 1 D.hstar))
    (hsel : ∀ θ Dd, D.admissible θ Dd → ∃ dat, sel Dd = some dat ∧
      KummerReading (Ecurve ℓ) f Lat κ dat (D.Mθ θ) (lam θ Dd))
    (hj : ∀ Dd dat, sel Dd = some dat → AnalyticRank (Etw ℓ Dd) 1 →
      D.jgen Dd - C ≤ (dat.index.toNat : ℤ)) :
    ∃ Cdet : ℤ, ∀ θ : ℕ, ∀ Dd : ℤ, D.admissible θ Dd → vZ (D.aθ θ Dd) < D.Mθ θ →
      AnalyticRank (Etw ℓ Dd) 1 ∧ (D.jgen Dd : WithTop ℤ) ≤ vZ (D.aθ θ Dd) + Cdet :=
  visibility_field_genuine Pr ⟨hArtin, hGal, hRoots, Splitting.splittingCriterion_proof⟩ hf hLat
    hNC hκ D hgp lam ω C hO7 hadm sel hsel hj

end ZInQ.Manuscript.RC.GlueSweep.Odd

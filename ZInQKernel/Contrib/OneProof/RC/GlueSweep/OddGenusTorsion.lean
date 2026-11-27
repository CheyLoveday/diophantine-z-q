import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Witness
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusTheoryReduction
import ZInQKernel.Contrib.CloudB3RC53.Assembly
import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST

/-!
# Lane RC22 (glue sweep), odd share: the genus point at a non-simple zero has infinite index

Manuscript (11/5), Appendix F, proof of (O.8) (`ex:app-visibility`, tex 9439–9441): "If an
admissible odd-sign `D` is not a simple zero, the height formula makes its genus point torsion,
and its coefficient vanishes modulo `2^M`" (the same height formula as tex 2464, 8268–8272).

Lane RC12 takes this step as the hypothesis `htorsion` of `Odd.visibility_O8` /
`Odd.visibility_of_comparison`. The batch-3 `GenusOdd` area proves, from the printed leaves
`Prints` and its reduced GLUE `GlueReduced`, one application of Cai–Shu–Tian with Elliot's
comparison at a genus datum (`GenusOdd.datum_facts_core`): a rational point `Q` on `E^{(D)}` with
`(L(E^{(h_*)}, s) L(E^{(D)}, s))'(1) = c · ĥ(Q)/2`, `c > 0`, and `j(P) ≤ j(Q) ≤ j(P) + 1` for the
index valuation `j` of the genus point `P = P_D^{gen}` in its native lattice. Lane RC12's step
follows: with root number `−1` (`L(E^{(D)}, 1) = 0`, the blueprint's
`centralValueZeroNode_proof`) and no simple zero, `L(E^{(D)}, s)` vanishes to order `≥ 2`, so the
derivative of the product vanishes (lane RC19's `deriv_eq_zero_of_two_le_analyticOrderAt`),
`ĥ(Q) = 0`, `Q` is torsion (`ĥ = 0 ⇔ torsion`, Tau Ceti), `j(Q) = ∞`, hence `j(P) = ∞`.

* `genusIndex_eq_top_of_not_simpleZero`: PROVED from `Prints`, `GlueReduced`, the genus partner,
  the prepared filter and the odd sign of `E^{(D)}`.
* `genusIndex_eq_top_of_not_simpleZero_final`: the same from the smallest GLUE of the batch-3 area,
  `GenusOdd.GlueFinal` (`ArtinFactorization`, `RingClassGalois`, `GenusRoots`,
  `SplittingCriterion`; `NeronTateTwist` is discharged there from lane RC19).

The conclusion `j(P_D^{gen}) = ∞` is the form consumed by
`GlueSweep.Odd.htorsion_of_index_top` (file `OddVisibility.lean`): with the native lattice
`eigenLattice E χ` and `P_D = heegnerSum E χ y`, it gives lane RC12's `htorsion` for the Kummer
functional. (Infinite index is what the coefficient needs: `2^{M} ∣ λ` for every `M`. That
`j(P) = ∞` forces `P` itself to be torsion would need Northcott over the genus field; it is not
used.)
-/

noncomputable section

open NumberField TauCeti.ClassFieldTheory

namespace ZInQ.Manuscript.RC.GlueSweep.Odd

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **PROVED** (the analytic step of tex 9439–9441: an odd-sign `D` that is not a simple zero has
`ord_{s=1} L(E^{(D)}, s) ≥ 2`). An entire function `F` with `F(1) = 0` whose order at `1` is not
exactly one vanishes to order at least two there. Used by `genusIndex_eq_top_of_not_simpleZero`. -/
theorem two_le_analyticOrderAt_of_ne_one {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h1 : F 1 = 0)
    (hne1 : analyticOrderAt F 1 ≠ 1) : 2 ≤ analyticOrderAt F 1 := by
  have hne0 : analyticOrderAt F 1 ≠ 0 := by
    intro h
    rcases analyticOrderAt_eq_zero.mp h with h' | h'
    · exact h' (hF.analyticAt 1)
    · exact h' h1
  generalize analyticOrderAt F 1 = o at hne0 hne1 ⊢
  induction o using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h0' : n ≠ 0 := fun h => hne0 (by simp [h])
    have h1' : n ≠ 1 := fun h => hne1 (by simp [h])
    exact_mod_cast (by omega : 2 ≤ n)

/-- **The genus point of a non-simple zero has infinite index** (tex 9439–9441, with the height
formula of tex 2464, 8268–8272). For `E/ℚ` elliptic with `a₁ = a₃ = 0`, its newform `f`, a non-CM
period lattice and parametrization scale (the data of `GenusOdd.GenusLower34`), a genus partner
`h_*`, `D` in the prepared filter with `E^{(D)}` of root number `−1` and
`ord_{s=1} L(E^{(D)}, s) ≠ 1`, every genus datum (`D h_*`, conductor one, `χ = χ_{h_*} ∘ N`) has
index valuation `j(P_D^{gen}) = ∞`. PROVED from `Prints` (Cai–Shu–Tian, Kolyvagin, BCDT) and the
batch-3 GLUE `GlueReduced`, through `GenusOdd.datum_facts_core`,
`centralValueZeroNode_proof`, `Height.deriv_eq_zero_of_two_le_analyticOrderAt` and Tau Ceti's
`ĥ = 0 ⇔ torsion`. Consumer: lane RC12's `htorsion` (through `htorsion_of_index_top`). -/
theorem genusIndex_eq_top_of_not_simpleZero (P : Prints) (G : GlueReduced)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (hstar : ℤ) (hgp : GenusPartner E hstar)
    (D : ℤ) (hp : Prepared E hstar D) (hodd : RootNumber (qtwist E D) (-1))
    (hns : ¬ AnalyticRank (qtwist E D) 1)
    (dat : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    dat.index = ⊤ := by
  have G' := glue34_of_reduced G
  obtain ⟨C, hC0, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  obtain ⟨h0, hsqh, hsqp, hcop⟩ := hp
  obtain ⟨hs0, hs4, hssq, hs5, hsp, har0⟩ := hgp
  have hN2 : ∀ p : ℕ, p ∣ newformLevel E → p ∣ 2 * newformLevel E :=
    fun p hp => dvd_mul_of_dvd_right hp 2
  have h2h : SquareAt 2 D := hsqp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h2s : SquareAt 2 hstar := hsp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h8 : D % 8 = 1 := h2h.2.1 rfl
  have s8 : hstar % 8 = 1 := h2s.2.1 rfl
  have hDg4 : 4 < |D * hstar| := by rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg hstar]
  have hs0' : (hstar : ℚ) ≠ 0 := by exact_mod_cast hs0.ne
  have htorS : ∀ Q : (qtwist E hstar).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hs0'
    have := (P.kolyvagin (qtwist E hstar) hE (P.bcdt _ hE) 0 (by norm_num) har0).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  -- `L(E^{(D)}, s)`: root number `−1` gives `L(E^{(D)}, 1) = 0`; no simple zero gives order `≥ 2`
  obtain ⟨N, hN, FD, hFD, hFE⟩ := hodd
  have hFD1 : FD 1 = 0 := centralValueZeroNode_proof (qtwist E D) N hN FD (by simpa using hFE)
  have hne1 : analyticOrderAt FD 1 ≠ 1 := fun h => hns ⟨FD, hFD.1, hFD.2, by exact_mod_cast h⟩
  have hFD' : deriv FD 1 = 0 :=
    ZInQ.Manuscript.RC.Height.deriv_eq_zero_of_two_le_analyticOrderAt hFD.1
      (two_le_analyticOrderAt_of_ne_one hFD.1 hFD1 hne1)
  obtain ⟨Fs, hFs, -⟩ := analyticRank_zero_iff.mp har0
  have hsqhN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p D :=
    fun p hp hpN => hsqp p hp (hN2 p hpN)
  have hsqsN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p hstar :=
    fun p hp hpN => hsp p hp (hN2 p hpN)
  -- Cai–Shu–Tian at the genus datum, with Elliot's comparison
  obtain ⟨Q, hder, -, hj2⟩ := by
    letI := dat.field; letI := dat.nf; letI := dat.nz
    exact datum_facts_core G' h₁ h₃ hC dat.K dat.finrank_two dat.totallyComplex dat.disc
      dat.χ dat.quad dat.prim dat.A dat.B dat.C dat.form dat.ι dat.y dat.hy
      (d₂ := D) (dR := D) (dT := hstar) (by push_cast; ring) hs4 hssq (by simp)
      (Nat.coprime_one_left _) (Int.odd_iff.mpr (by
        rw [Int.mul_emod, show D % 2 = 1 by omega, show hstar % 2 = 1 by omega]; norm_num))
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (fun p hp hpN => (hsqhN p hp hpN).mul (hsqsN p hp hpN) hp) (Nat.coprime_one_left _)
      (coprime_of_squareAt fun p hp hpN => (hsqsN p hp hpN).mul (hsqhN p hp hpN) hp)
      (Or.inr ⟨rfl, rfl⟩) htorS hFs hFD
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have hED : (qtwist E D).IsElliptic := qtwist_isElliptic E hD0
  have dW : deriv (fun s => Fs s * FD s) 1 = 0 := by
    rw [show (fun s => Fs s * FD s) = Fs * FD from rfl, deriv_mul (hFs.1 1) (hFD.1 1), hFD1,
      hFD']
    ring
  rw [dW] at hder
  have hDh0 : ((D * hstar : ℤ) : ℝ) ≠ 0 := by
    have : D * hstar ≠ 0 := mul_ne_zero h0.ne' hs0.ne
    exact_mod_cast this
  have hQ0 : Q.canonicalHeight = 0 := by
    rcases mul_eq_zero.mp hder.symm with h | h
    · exfalso
      rw [Complex.ofReal_eq_zero] at h
      have hpos : 0 < C / (((1 : ℕ) : ℝ) * Real.sqrt |((D * hstar : ℤ) : ℝ)|) := by
        apply div_pos hC0
        rw [Nat.cast_one, one_mul]
        exact Real.sqrt_pos.mpr (abs_pos.mpr hDh0)
      exact hpos.ne' h
    · rw [Complex.ofReal_eq_zero] at h
      linarith
  have hQt : IsOfFinAddOrder Q :=
    (WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder Q).mp hQ0
  have htop : twoDivIndex ⊤ Q = ⊤ := twoDivIndex_eq_top_of_torsion (AddSubgroup.mem_top Q) hQt
  have hj2' : twoDivIndex ⊤ Q ≤ dat.index + 1 := hj2
  rw [htop, top_le_iff] at hj2'
  exact (WithTop.add_eq_top.mp hj2').resolve_right ENat.one_ne_top

/-- **The genus point of a non-simple zero has infinite index, from `GlueFinal`** (tex
9439–9441). PROVED: `genusIndex_eq_top_of_not_simpleZero` with
`GlueReduced := glueReduced_of_RC19 (glueAfterRC19_of_final G)` (batch 3: `TwistDescent` PROVED,
`NeronTateTwist` discharged from lane RC19, `GenusTheory` reduced). Remaining GLUE:
`ArtinFactorization`, `RingClassGalois`, `GenusRoots`, `SplittingCriterion`. -/
theorem genusIndex_eq_top_of_not_simpleZero_final (P : Prints) (G : GlueFinal)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (hstar : ℤ) (hgp : GenusPartner E hstar)
    (D : ℤ) (hp : Prepared E hstar D) (hodd : RootNumber (qtwist E D) (-1))
    (hns : ¬ AnalyticRank (qtwist E D) 1)
    (dat : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    dat.index = ⊤ :=
  genusIndex_eq_top_of_not_simpleZero P (glueReduced_of_RC19 (glueAfterRC19_of_final G)) E h₁ h₃
    f hf Lat hLat hNC κ hκ hstar hgp D hp hodd hns dat

end ZInQ.Manuscript.RC.GlueSweep.Odd

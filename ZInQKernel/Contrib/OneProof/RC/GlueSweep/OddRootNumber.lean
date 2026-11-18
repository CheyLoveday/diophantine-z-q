import ZInQKernel.Contrib.OneProof.RC.Odd.ThetaLocal
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Prints
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusLower

/-!
# Lane RC22 (glue sweep), odd share: the sign `α(−1) = 1` with the root number of `E^{(h_*)}`

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-theta-form`, tex 8579–8592: "`α(−1)`
… `w(E^{(h_*)}) = +1` because `L(E^{(h_*)}, 1) ≠ 0`".

Lane RC12's `Odd.alpha_neg_one` takes the value `w(E^{(h_*)}) = +1` as the bare hypothesis
`hwEt : wEt = 1`. Lane RC13 proves that a nonzero central value forces root number `+1`
(`Nonvanishing.rootNumber_eq_one_of_centralNonzero`, from the functional equation at `s = 1`), and
the genus partner `h_*` of the batch-3 `GenusOdd` area carries `L(E^{(h_*)}, 1) ≠ 0` as the last
conjunct of `GenusOdd.GenusPartner` (it is produced by lane RC13's `Nonvanishing.genusPartner` /
`genusPartner_of_BFH`). This file removes `hwEt`:

* `alpha_neg_one_of_centralNonzero`: `hwEt` replaced by `RootNumber Et wEt` and
  `CentralNonzero Et` for the twist `Et = E^{(h_*)}`;
* `alpha_neg_one_of_genusPartner`: the same with `GenusOdd.GenusPartner E h_*`;
* `alpha_neg_one_of_twistSign`: in the manuscript's situation (every bad prime split in
  `ℚ(√h_*)`, tex 8251–8254, so `χ_{h_*}(p) = 1` at the level primes), also `htw` is removed: the
  root number of `E^{(h_*)}` is `sign(h_*) · w(E)` by the printed twist sign `BFHTwistSign`
  (lane RC13's statement of Bump–Friedberg–Hoffstein, p. 543), and it is `+1` by
  `rootNumber_eq_one_of_centralNonzero`.

`hwE` (`w(E) = −∏ w_{p^e}`, Atkin–Lehner, GLUE) has no prover in the tree. The general twist
formula `htw` (`w(E^{(h_*)}) = w(E) χ_{h_*}(−N)`, GLUE) has none either (lane RC13 deliberately
avoids it); the printed twist sign `BFHTwistSign` covers the discriminants in which every bad prime
splits, which is the case used by the manuscript.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Odd

open ZInQ.Contrib.CloudB3RC53

/-- **`α(−1) = 1` with `w(E^{(h_*)}) = +1` discharged** (tex 8579–8592). PROVED from lane RC12's
`Odd.alpha_neg_one` and lane RC13's `Nonvanishing.rootNumber_eq_one_of_centralNonzero`: the
hypothesis `hwEt : wEt = 1` of `Odd.alpha_neg_one` is replaced by "`wEt` is the root number of the
twist `Et`" and "`L(Et, 1) ≠ 0`". Remaining hypotheses: `hwE` (Atkin–Lehner, GLUE), `htw` (twist
formula, GLUE), `hχm1`, `hm`, `hℓ₀`. Consumer: `Odd.alpha_neg_one` (hypothesis `hwEt`);
discharger: `Nonvanishing.rootNumber_eq_one_of_centralNonzero`. -/
theorem alpha_neg_one_of_centralNonzero {ι : Type*} (P : Finset ι) (w χ : ι → ℤ) (e : ι → ℕ)
    (wE wEt χm1 : ℤ) (hwE : wE = -∏ i ∈ P, w i)
    (htw : wEt = wE * χm1 * ∏ i ∈ P, χ i ^ e i) (hχm1 : χm1 = -1)
    {Et : WeierstrassCurve ℚ} (hroot : RootNumber Et wEt)
    (hL : ZInQ.Manuscript.RC.Nonvanishing.CentralNonzero Et)
    {m ℓ₀ : ℕ} [Fact ℓ₀.Prime] (hm : m % 4 = 3) (hℓ₀ : ℓ₀ % 4 = 3) :
    (∏ i ∈ P, w i * χ i ^ e i) = 1 ∧
      (∏ i ∈ P, w i * χ i ^ e i) * jacobiSym (-1) m * legendreSym ℓ₀ (-1) = 1 :=
  ZInQ.Manuscript.RC.Odd.alpha_neg_one P w χ e wE wEt χm1 hwE htw hχm1
    (ZInQ.Manuscript.RC.Nonvanishing.rootNumber_eq_one_of_centralNonzero hroot hL) hm hℓ₀

/-- **`α(−1) = 1` at the genus partner** (tex 8579–8592, with `h_*` of tex 2404–2406, 8251–8254).
PROVED from `alpha_neg_one_of_centralNonzero`: `GenusOdd.GenusPartner E h_*` contains
`AnalyticRank (qtwist E h_*) 0`, i.e. `L(E^{(h_*)}, 1) ≠ 0`, so with `wEt` the root number of
`E^{(h_*)}` the hypothesis `hwEt` of `Odd.alpha_neg_one` is discharged. Consumer:
`Odd.alpha_neg_one`; dischargers: `Nonvanishing.rootNumber_eq_one_of_centralNonzero`,
`GenusOdd.GenusPartner` (produced by lane RC13's `Nonvanishing.genusPartner`). -/
theorem alpha_neg_one_of_genusPartner {ι : Type*} (P : Finset ι) (w χ : ι → ℤ) (e : ι → ℕ)
    (wE wEt χm1 : ℤ) (hwE : wE = -∏ i ∈ P, w i)
    (htw : wEt = wE * χm1 * ∏ i ∈ P, χ i ^ e i) (hχm1 : χm1 = -1)
    {E : WeierstrassCurve ℚ} {hstar : ℤ} (hgp : GenusOdd.GenusPartner E hstar)
    (hroot : RootNumber (qtwist E hstar) wEt)
    {m ℓ₀ : ℕ} [Fact ℓ₀.Prime] (hm : m % 4 = 3) (hℓ₀ : ℓ₀ % 4 = 3) :
    (∏ i ∈ P, w i * χ i ^ e i) = 1 ∧
      (∏ i ∈ P, w i * χ i ^ e i) * jacobiSym (-1) m * legendreSym ℓ₀ (-1) = 1 :=
  alpha_neg_one_of_centralNonzero P w χ e wE wEt χm1 hwE htw hχm1 hroot hgp.2.2.2.2.2 hm hℓ₀

/-- **`α(−1) = 1` with both `hwEt` and `htw` discharged, in the split case** (tex 8251–8254,
8579–8592). For `A = E` elliptic of root number `wE`, `h_* < 0` a fundamental discriminant in which
every bad prime of `A` splits (so `χ_{h_*}(p) = 1` at the level primes: hypothesis `hχ1`) and
`L(A^{(h_*)}, 1) ≠ 0`: the root number of `A^{(h_*)}` is `sign(h_*) wE = −wE` by the printed twist
sign (`Nonvanishing.BFHTwistSign`, with BCDT for modularity), and it is `+1` by
`Nonvanishing.rootNumber_eq_one_of_centralNonzero`; so lane RC12's `htw` holds with
`wEt := wE · (−1) · ∏ χ_i^{e_i}` and `hwEt` holds. PROVED from the prints `BFHTwistSign`,
`BCDTThmA` and the remaining GLUE `hwE`. Consumer: `Odd.alpha_neg_one` (hypotheses `htw`,
`hwEt`); dischargers: `Nonvanishing.BFHTwistSign` (PRINT),
`Nonvanishing.rootNumber_eq_one_of_centralNonzero`. -/
theorem alpha_neg_one_of_twistSign {ι : Type*} (P : Finset ι) (w χ : ι → ℤ) (e : ι → ℕ)
    (hTS : ZInQ.Manuscript.RC.Nonvanishing.BFHTwistSign)
    (hBCDT : ZInQ.Manuscript.PoleS12.BCDTThmA)
    {A : WeierstrassCurve ℚ} (hA : A.IsElliptic) {wE : ℤ} (hroot : RootNumber A wE)
    (hwE : wE = -∏ i ∈ P, w i) {hstar : ℤ}
    (hfund : ZInQ.Manuscript.RC.Nonvanishing.IsFundamentalDiscriminant hstar) (hneg : hstar < 0)
    (hsplit : ∀ p : ℕ, p.Prime → ¬ ZInQ.Manuscript.RC.Nonvanishing.GoodAt A p →
      ZInQ.Manuscript.RC.Nonvanishing.SplitsIn hstar p)
    (hχ1 : ∀ i ∈ P, χ i = 1)
    (hL : ZInQ.Manuscript.RC.Nonvanishing.CentralNonzero (qtwist A hstar))
    {m ℓ₀ : ℕ} [Fact ℓ₀.Prime] (hm : m % 4 = 3) (hℓ₀ : ℓ₀ % 4 = 3) :
    (∏ i ∈ P, w i * χ i ^ e i) = 1 ∧
      (∏ i ∈ P, w i * χ i ^ e i) * jacobiSym (-1) m * legendreSym ℓ₀ (-1) = 1 := by
  have htwist := hTS A hA (hBCDT A hA) wE hroot hstar hfund hsplit
  rw [Int.sign_eq_neg_one_of_neg hneg] at htwist
  have h1 := ZInQ.Manuscript.RC.Nonvanishing.rootNumber_eq_one_of_centralNonzero htwist hL
  have hprod : ∏ i ∈ P, χ i ^ e i = 1 :=
    Finset.prod_eq_one fun i hi => by rw [hχ1 i hi, one_pow]
  refine ZInQ.Manuscript.RC.Odd.alpha_neg_one P w χ e wE (wE * (-1) * ∏ i ∈ P, χ i ^ e i) (-1)
    hwE rfl rfl ?_ hm hℓ₀
  rw [hprod]
  linarith

end ZInQ.Manuscript.RC.GlueSweep.Odd

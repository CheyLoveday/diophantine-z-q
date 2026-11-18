import ZInQKernel.Contrib.CloudB3RC53.Prints

/-!
# Kolyvagin's Theorem 1 with its own premise: a weak Weil parametrization

`KolyvaginThm1Printed` (`Prints.lean`) takes as premise `IsModular E`: a `Γ₀(N)` cusp form whose
coefficients are those of `L(E, s)`. Kolyvagin's Theorem 1 (MPIM preprint MPI/90-69 (1990), p. 4)
assumes instead a weak Weil parametrization `X₀(N) → E` with `N` the conductor (p. 3). This file
states the print with that premise and derives the old form from it, through the modular
parametrization of Darmon's Theorem 5.4:

* `HasWeakWeilParametrization E`: the analytic data of a modular parametrization of `E` over `ℚ`
  at the conductor level. `X₀(N)` as a curve over `ℚ` is absent from Mathlib and Tau Ceti, so,
  as for the Cai–Shu–Tian print (`Prints/CST.lean`), the parametrization is stated through its
  complex-analytic model: a cusp form `f` on `Γ₀(N)` with the coefficients of `L(E, s)`, a period
  lattice `Lat` of `E`, and a nonzero RATIONAL `c` with `c · (periods of 2πi f dτ) ⊆ Lat`, so that
  `τ ↦ ℘_Lat-point of c ∫_{i∞}^τ 2πi f` (`CST.phiAn`) is a `Γ₀(N)`-invariant map
  `X₀(N)(ℂ) → E(ℂ)` sending `∞` to `O`. Darmon's proof of Theorem 5.4 gives exactly this
  description: "the pull-back `φ^*(ω_E)` is a nonzero rational multiple of the differential form
  `ω_f := 2πi f(τ) dτ`". `N` is `CST.newformLevel E`, which is the conductor by Carayol's theorem.
  The passage between the algebraic map over `ℚ` and these analytic data is a translation (the
  Eichler–Shimura construction), as for the Cai–Shu–Tian print.
* `KolyvaginThm1WeilParam` (PRINT): Kolyvagin's Theorem 1 with the weak Weil parametrization
  premise.
* `DarmonThm54` (PRINT): H. Darmon, "Rational points on curves", §5.1, Theorem 5.4: for an
  elliptic curve `E/ℚ` of conductor `N`, "there exists a nonconstant map of curves over `ℚ`
  `φ : X₀(N) → E`". Read in the author's version dated April 11, 2008 (§5.1, Theorem 5.4, p. 54
  of that version); the published version (Arithmetic Geometry, Clay Math. Proc. 8 (2009)) was
  not read, and its page (reported as p. 43) is UNVERIFIED. Darmon proves it from modularity
  (his Theorem 4.6) and Faltings' isogeny theorem.
* `kolyvaginThm1Printed_of_weilParam` (PROVED): the old `IsModular`-premise form follows from the
  two prints, so the current consumers of `Prints.kolyvagin` keep working
  (`prints_of_weilParam`).

The old leaf is not relabelled: its premise is not Kolyvagin's.

Classification: `KolyvaginThm1WeilParam`, `DarmonThm54` PRINT (analytic form of the
parametrization, as above); the bridges PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12 CST

/-- **`E` has a weak Weil parametrization `X₀(N) → E` over `ℚ`, `N` the conductor** (analytic
model; see the module docstring): a cusp form `f` of weight `2` on `Γ₀(N)`, `N = newformLevel E`,
with the coefficients of `L(E, s)`, a period lattice `Lat` of `E` (`IsLatticeOf`), and a nonzero
rational `c` scaling the periods of `2πi f dτ` into `Lat` (`IsParamScale`), so that `φ^* ω_E = c ω_f`
for the analytic map `CST.phiAn E f Lat c`. -/
def HasWeakWeilParametrization (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (c : ℚ),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) ∧
      IsLatticeOf E Lat ∧ IsParamScale (newformLevel E) f Lat (c : ℂ)

/-- **Kolyvagin, Theorem 1, with its own premise** (printed leaf; V. A. Kolyvagin, "On the
Mordell–Weil group and the Shafarevich–Tate group of modular elliptic curves", MPIM preprint
MPI/90-69 (1990), Theorem 1, p. 4, under the weak Weil parametrization of p. 3; tex L1093
`\cite[Theorem 1, pp. 4–5]{kolyvagin}`): an elliptic curve `E/ℚ` with a weak Weil parametrization
`X₀(N) → E` (`N` the conductor) and `ord_{s=1} L(E, s) = r ≤ 1` has `rank E(ℚ) = r` and finite
`Ш(E/ℚ)`. The parametrization is in its analytic form (`HasWeakWeilParametrization`). -/
def KolyvaginThm1WeilParam : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → HasWeakWeilParametrization E →
    ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
      Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- **Darmon, Theorem 5.4: the modular parametrization over `ℚ` at the conductor level**
(printed leaf; H. Darmon, "Rational points on curves", §5.1, Theorem 5.4; read in the author's
version dated April 11, 2008, p. 54; published page UNVERIFIED): for an elliptic curve `E/ℚ` of
conductor `N` there is a nonconstant map of curves over `ℚ` `φ : X₀(N) → E`. Stated through the
analytic model of the parametrization (`HasWeakWeilParametrization`), which Darmon's proof
describes: `φ^*(ω_E)` is a nonzero rational multiple of `ω_f = 2πi f(τ) dτ`. -/
def DarmonThm54 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → HasWeakWeilParametrization E

/-- **The old `IsModular`-premise form of Kolyvagin's Theorem 1 from the two prints** (PROVED):
Darmon's Theorem 5.4 supplies the weak Weil parametrization that Kolyvagin's Theorem 1 assumes. -/
theorem kolyvaginThm1Printed_of_weilParam (hD : DarmonThm54) (hK : KolyvaginThm1WeilParam) :
    KolyvaginThm1Printed :=
  fun E hE _ r hr hA => hK E hE (hD E hE) r hr hA

/-- **The printed leaves with Kolyvagin's own premise** (PROVED): `Prints` from BCDT Theorem A,
Darmon's Theorem 5.4, Kolyvagin's Theorem 1 with the weak Weil parametrization premise,
Dokchitser–Dokchitser Theorem 1.8 and Cai–Shu–Tian Theorem 1.1. -/
theorem prints_of_weilParam (hB : BCDTThmA) (hD : DarmonThm54) (hK : KolyvaginThm1WeilParam)
    (hdd : DokchitserThm18) (hcst : CST.CSTThm11Split) : Prints :=
  ⟨hB, kolyvaginThm1Printed_of_weilParam hD hK, hdd, hcst⟩

end ZInQ.Contrib.CloudB3RC53

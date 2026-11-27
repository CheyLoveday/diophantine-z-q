import ZInQKernel.Contrib.OneProof.HeightModelM.GR1Height
import ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS
import ZInQKernel.Contrib.OneProof.GR14Printed.Printed

/-!
# The two Gaudron–Rémond rows over Gaudron–Rémond's own height

Printed forms of the rows `gaudronRemondSec9LowerAnSS` and `gaudronRemondThm14AnSS` with the
height `IsAnStableHeightSS` (semistable Néron model) replaced by `IsGR1StableHeightOriginal`
(a semi-abelian model, GR1 §2.3, original normalization `h_F`):

* `GaudronRemondSec9LowerGR1`: GR1, Comment. Math. Helv. 89 (2014), Cor. 8.4, p. 400,
  `h(A) ≥ -(1/2)(dim A) log(2π)` "(sans hypothèse de polarisation)", read in `h_F` with
  `h(A) = h_F(A) + (g/2) log π` (p. 352). It gives `ZInQ.SemistabAssembly.BostLowerBoundAnSS`
  (`bostLowerBoundAnSS_of_GR1`) and the current row `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`
  (`gaudronRemondSec9LowerAnSS_of_GR1`, through the proved weakening
  `ZInQ.BostGR9.gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`).
* `GaudronRemondSec9LowerGR1Weak`: the same over the GR1 height at the current field's strength,
  `h_F(A) ≥ -(3/2) dim A` (the weakening GR make on p. 352 for Duke 163, Lemme 9.1). The print
  implies it (`gaudronRemondSec9LowerGR1Weak_of_GR1`), and it gives the current row
  (`gaudronRemondSec9LowerAnSS_of_GR1Weak`). The fold carries this weak form.
* `GaudronRemondThm14GR1`: É. Gaudron, G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163
  (2014), Thm 1.4, p. 2060 (`κ(A)` and `g ≥ 1`, p. 2058; isogenies and their degree, p. 2062), in
  the form `ZInQ.GR14Printed.GaudronRemondThm14Printed` over the GR1 height. It gives that form
  (`gaudronRemondThm14Printed_of_GR1`) and the current row
  `ZInQ.SemistabAssembly.GaudronRemondThm14AnSS` (`gaudronRemondThm14AnSS_of_GR1`, through the
  proved `ZInQ.GR14Printed.gaudronRemondThm14AnSS_of_printed`).

Each implication uses the printed leaf `EGAIV_9_7_7_OL` only through the identification
`isGR1StableHeightOriginal_of_isAnStableHeightSS`. So the GR1 rows with the EGA leaf imply the two
current rows, and replacing them in the bundle keeps `frozenTarget` (`FoldCheck.lean`). The
converse (from the GR1 height to the Néron-model height) is not proved here.
-/

noncomputable section

open CategoryTheory
open ZInQ.DefFaltings ZInQ.SemistabAssembly ZInQ.GR14Printed

namespace ZInQ.HeightModelM

/-- **Leaf: GR1 Cor. 8.4 over the GR1 height** (Comment. Math. Helv. 89 (2014), p. 400; attribution:
Bost): for every abelian variety `A` of dimension `g` over a number field,
`h(A) ≥ -(g/2) log(2π)`, where `h(A) = x + (g/2) log π` for the height `x = h_F(A)` of a
semi-abelian model (p. 352). `ZInQ.SemistabAssembly.BostLowerBoundAnSS` with `IsAnStableHeightSS`
replaced by `IsGR1StableHeightOriginal`. -/
def GaudronRemondSec9LowerGR1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightOriginal A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- The GR1 form of Cor. 8.4 gives Bost's bound over the Néron height. -/
theorem bostLowerBoundAnSS_of_GR1 (hE : EGAIV_9_7_7_OL) (h : GaudronRemondSec9LowerGR1) :
    BostLowerBoundAnSS :=
  fun K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightOriginal_of_isAnStableHeightSS hE hx)

/-- **The row `gaudronRemondSec9LowerAnSS` from the GR1 form of Cor. 8.4 and EGA IV₃ (9.7.7).** -/
theorem gaudronRemondSec9LowerAnSS_of_GR1 (hE : EGAIV_9_7_7_OL)
    (h : GaudronRemondSec9LowerGR1) : ZInQ.BostGR9.GaudronRemondSec9LowerAnSS :=
  ZInQ.BostGR9.gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS (bostLowerBoundAnSS_of_GR1 hE h)

/-- **GR1 Cor. 8.4 in the weakened form `h_F(A) ≥ -(3/2) dim A`, over the GR1 height**: the
field `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` with `IsAnStableHeightSS` replaced by
`IsGR1StableHeightOriginal`. This is the form the bundle carries (the current field's strength);
the print `GaudronRemondSec9LowerGR1` implies it (`gaudronRemondSec9LowerGR1Weak_of_GR1`). -/
def GaudronRemondSec9LowerGR1Weak : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightOriginal A x → -(3 / 2) * (g : ℝ) ≤ x

/-- **The print gives the weak form**: Cor. 8.4 read in `h_F` (p. 352) is
`h_F(A) ≥ -(g/2) log(2π²)`, and `(1/2) log(2π²) < 3/2`. -/
theorem gaudronRemondSec9LowerGR1Weak_of_GR1 (h : GaudronRemondSec9LowerGR1) :
    GaudronRemondSec9LowerGR1Weak := by
  intro K _ _ A g hg x hx
  have h1 := (ZInQ.BostGR9.deligne_bound_iff g x).mp (h K A g hg x hx)
  have h2 := ZInQ.BostGR9.half_log_two_pi_sq_lt
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

/-- **The row `gaudronRemondSec9LowerAnSS` from the weak GR1 form and EGA IV₃ (9.7.7).** -/
theorem gaudronRemondSec9LowerAnSS_of_GR1Weak (hE : EGAIV_9_7_7_OL)
    (h : GaudronRemondSec9LowerGR1Weak) : ZInQ.BostGR9.GaudronRemondSec9LowerAnSS :=
  fun K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightOriginal_of_isAnStableHeightSS hE hx)

/-- **Leaf: Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4, over the GR1 height**
(`κ(A)` and `g ≥ 1`, p. 2058; isogenies "surjectif de noyau fini" and the degree, p. 2062):
`ZInQ.GR14Printed.GaudronRemondThm14Printed` with `IsAnStableHeightSS` replaced by
`IsGR1StableHeightOriginal`. -/
def GaudronRemondThm14GR1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsGR1StableHeightOriginal A x →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ ∧
      (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogenyPrinted ψ ∧
      (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- The GR1 form of Thm 1.4 gives the printed form over the Néron height. -/
theorem gaudronRemondThm14Printed_of_GR1 (hE : EGAIV_9_7_7_OL) (h : GaudronRemondThm14GR1) :
    GaudronRemondThm14Printed :=
  fun K _ _ A B g x hg1 hg hx hiso =>
    h K A B g x hg1 hg (isGR1StableHeightOriginal_of_isAnStableHeightSS hE hx) hiso

/-- **The row `gaudronRemondThm14AnSS` from the GR1 form of Thm 1.4 and EGA IV₃ (9.7.7).** -/
theorem gaudronRemondThm14AnSS_of_GR1 (hE : EGAIV_9_7_7_OL) (h : GaudronRemondThm14GR1) :
    GaudronRemondThm14AnSS :=
  gaudronRemondThm14AnSS_of_printed (gaudronRemondThm14Printed_of_GR1 hE h)

end ZInQ.HeightModelM

import ZInQKernel.HDecomp.Objects

/-! # nos-proof: the field `r7a`, verbatim (ZInQKernel/HDecomp/Objects.lean l. 856-871, namespace `PkgI2`)

Dependencies (same file): `IsAbelianVariety` (l. 793), `IsAbelianScheme` (l. 801), `Pts` (l. 809),
`torsion` (l. 813), `galHom` (l. 818), `galAct` (l. 827), `IsInertia` (l. 833), `HasGoodReduction` (l. 840),
`InertiaTrivialOn` (l. 845). The chain's field is `r7a : _root_.PkgI2.NeronOggShafarevich.{0}`
(TailZ41, `OpenResearchLeaves26`). -/

open CategoryTheory AlgebraicGeometry
open PkgI2 (IsAbelianVariety HasGoodReduction InertiaTrivialOn)

namespace NOSOld

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

example : NeronOggShafarevich ↔ PkgI2.NeronOggShafarevich.{0} := Iff.rfl

end NOSOld

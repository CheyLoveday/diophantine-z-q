import ZInQKernel.Contrib.RC53Assist.TateCurve.Main
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois

/-!
# The Weil-pairing input is a theorem; the additive reading needs one printed input

`SilvermanIII81GaloisWeilPairingPrint` (`WeilInertia.lean`) is proved here from the Galois
equivariance of the Weil pairing already established in the vendored elliptic-curve library
(`WeierstrassCurve.weilPairing_torsionGaloisAction`). Consequently the additive-prime reading
`AdditiveReductionCoinvariantsVanish` follows from the semistable reduction criterion
`GrothendieckSemistableReductionPrint` alone.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open TauCeti
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion

set_option backward.isDefEq.respectTransparency false in
/-- **PROVED**. The Galois equivariance of the Weil pairing at every level `ℓ ^ n`, in the form
used by the additive reading, from the point-action theorem of the vendored library.
Locators: Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (the property letter is not
checked here); `WeierstrassCurve.weilPairing_torsionGaloisAction`. -/
theorem silvermanIII81GaloisWeilPairingPrint_proved : SilvermanIII81GaloisWeilPairingPrint := by
  classical
  intro E _ ℓ _ n σ P Q
  let : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hN : ((ℓ ^ n : ℕ) : GlueC10.Qbar) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)
  have hAct (R : TateModuleLevel ℓ (E.baseChange GlueC10.Qbar).toAffine.Point n) :
      Multiplicative.toAdd (E.torsionGaloisAction ((ℓ ^ n : ℕ) : ℤ) σ) R =
        TateModule.levelMap (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) n R := by
    apply Subtype.ext
    rw [WeierstrassCurve.torsionGaloisAction_apply_coe,
      WeierstrassCurve.pointGaloisAction_apply]
    rfl
  have h := E.weilPairing_torsionGaloisAction (K := GlueC10.Qbar) (ℓ ^ n) hN σ P Q
  rw [hAct P, hAct Q] at h
  have hu := congrArg (fun z : Additive (rootsOfUnity (ℓ ^ n) GlueC10.Qbar) =>
    ((Additive.toMul z).val : GlueC10.Qbar)) h
  apply Units.ext
  simp only [levelWeilUnit, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
    toMul_ofMul, restrictRootsOfUnity_coe_apply, Units.coe_map] at hu ⊢
  convert hu using 1
  rfl

/-- **PROVED FROM ONE PRINTED INPUT**. The vanishing of inertia coinvariants at additive primes
from the semistable reduction criterion alone. Locator: Silverberg-Zarhin, *Reduction of Abelian
Varieties*, Theorem 4.1 (a source not among the manuscript's bibliography entries). -/
theorem additiveReductionCoinvariantsVanish_of_semistability
    (hS : GrothendieckSemistableReductionPrint) :
    ZInQ.Contrib.RC53Assist.GlobalTrace.AdditiveReductionCoinvariantsVanish :=
  ZInQ.Contrib.RC53Assist.GlobalTrace.additiveReductionCoinvariantsVanish_of_prints
    hS silvermanIII81GaloisWeilPairingPrint_proved

end ZInQ.Contrib.RC53Assist.TateCurve

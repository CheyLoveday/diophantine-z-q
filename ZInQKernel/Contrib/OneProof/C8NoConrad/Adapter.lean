import ZInQKernel.Contrib.OneProof.C8NoConrad.GlobalSplit
import ZInQKernel.Contrib.OneProof.ConradBridges
import ZInQKernel.Contrib.OneProof.C8Dicts

/-! # C8 without Conrad: the adapter to the chain's statements

`c8TwistFinite_noConrad` proves step C8's conclusion `C8TwistFinite` (diophantine_zq.tex
L758-766: the twisting character of Pan's theorem has finite image) from R14
(`HSyn.EigenformRepExists`) and R13 (`PkgI4.EigenformHT`) alone, the inputs the consumer already
reads. It does not use `ConradAppB` (Conrad, App. B), `ConradAppBQp`, `ConradPropB3Qp`,
`LocAlgExponentEqWeight` or `TateTwistInvariantsInertia`. Inputs, all proved in the tree:

* `twistCharHTWt0_proof` (`C8Twist`): `ψ|G_{ℚ_5}` takes values in a finite `E/ℚ_5` and is
  Hodge–Tate of weight `0`; `Bridges.pureHT_of_hasHTWeights` turns that into the equivariant
  splitting `PureHT`;
* `finiteOfLocAlgTrivialQNoRam_of_dicts inertiaAtPDecomp_proof minkowskiInertiaQ_proof`
  (`C8CFT`, `C8Dicts`) at `k = 0`: class field theory over `ℚ`;
* `C8NoConrad.range_finite_of_pureHT` (this directory): the global splitting of `ψ` and Tate's
  theorem.

`g12DetPZ_noConrad` is the consumer's statement `G12DetPZ` with the same inputs as
`g12DetPZ_of_inputs` minus the bundle `C8Inputs`. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad

open _root_.PkgI4 (GaloisRep GaloisChar)

/-- Class field theory over `ℚ` in the unit form used by `C8NoConrad`, from the tree's
`FiniteOfLocAlgTrivialQNoRam` at `k = 0`. -/
theorem noRamUnits_five : ZInQ.Contrib.C8NoConrad.NoRamUnits 5 := by
  intro β hβ
  exact finiteOfLocAlgTrivialQNoRam_of_dicts inertiaAtPDecomp_proof minkowskiInertiaQ_proof 5 β
    ⟨0, fun u _ σ hσ => hβ u σ hσ⟩

/-- **Step C8 without Conrad's App. B**: the twist has finite image, from R13 and R14. -/
theorem c8TwistFinite_noConrad (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT) :
    C8TwistFinite := by
  intro r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨E, hE, ψE, hlift, hwt⟩ := twistCharHTWt0_proof hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  exact ZInQ.Contrib.C8NoConrad.range_finite_of_pureHT 5 noRamUnits_five ψ
    E.val.toRingHom ψE hlift (Bridges.pureHT_of_hasHTWeights 5 ψE 0 hwt)

/-- **C8's consumer `G12DetPZ` without `C8Inputs`** (the replacement for
`g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`). -/
theorem g12DetPZ_noConrad (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) : G12DetPZ :=
  g12DetPZ_of_twistFinite (c8TwistFinite_noConrad hR hHT) h9 hdR

end HDec.G0Galois.C8Conrad

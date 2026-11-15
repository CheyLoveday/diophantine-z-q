/-! ## Final: the three strict-henselization leaves from the single Néron leaf -/

namespace ShRoute

open ReductSplit ReductGlue

/-- **`StrictHenselizationNeron` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationNeron0_final (hN : NeronBaseChangeSH) : StrictHenselizationNeron0 :=
  strictHenselizationNeron0_of hN shExists0

/-- **`StrictHenselizationPair` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationPair0_final (hN : NeronBaseChangeSH) : StrictHenselizationPair0 :=
  strictHenselizationPair0_of hN shPair0

/-- **`StrictHenselizationInside` (char 0, perfect residue field) from `NeronBaseChangeSH`.** -/
theorem strictHenselizationInside0_final (hN : NeronBaseChangeSH) : StrictHenselizationInside0 :=
  strictHenselizationInside0_of hN shInside0

/-- **The route**: the general-DVR SGA 7 IX leaves 4.7, 3.3 (first assertion) and 3.5, for `K` of
characteristic 0 with perfect residue field, from their strictly henselian forms, the bundle leaf
`MulEtaleAbelianScheme` and the one Néron leaf `NeronBaseChangeSH`. -/
theorem route_final (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hU : SemistableUnipotentSH) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hN : NeronBaseChangeSH) :
    RaynaudSemistable0 ∧ SemistablePersistsDVR0 ∧ SemistableUnipotent0 :=
  ⟨raynaudSemistable0_of hR (strictHenselizationNeron0_final hN) hE,
   semistablePersistsDVR0_of hP (strictHenselizationPair0_final hN),
   semistableUnipotent0_of hU (strictHenselizationInside0_final hN)⟩

end ShRoute

#print axioms ShRoute.key_finite
#print axioms ShRoute.henselian_wE
#print axioms ShRoute.isSepClosed_wE
#print axioms ShRoute.isDVR_wE
#print axioms ShRoute.res_isAlgebraic
#print axioms ShRoute.shExists0
#print axioms ShRoute.shInside0
#print axioms ShRoute.shPair0
#print axioms ShRoute.strictHenselizationNeron0_final
#print axioms ShRoute.strictHenselizationPair0_final
#print axioms ShRoute.strictHenselizationInside0_final
#print axioms ShRoute.route_final

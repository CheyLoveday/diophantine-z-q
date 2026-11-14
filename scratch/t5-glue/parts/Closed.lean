
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Shimura

/-! ## §7. The field-theory glue, proved (`Field.lean` body) -/

/-- **`AutExtends`, proved** (`exists_ringEquiv_extend`, Steinitz via Mathlib's transcendence
bases and `IsAlgClosure.equivOfEquiv`). -/
theorem autExtends : AutExtends := fun ρ => exists_ringEquiv_extend ιC ρ.toRingEquiv

/-- **`FixedAlgebraic`, proved** (`mem_range_of_fixed`). -/
theorem fixedAlgebraic : FixedAlgebraic := fun z hz => mem_range_of_fixed ιC z hz

/-- **`X0RatStructure` from the canonical-model leaf and `DiscNeZero`.** -/
theorem x0RatStructure_of' (hL : X0ModuliGalois) (hD : DiscNeZero) : X0RatStructure :=
  x0RatStructure_of hL autExtends fixedAlgebraic hD

/-- **`CMModuli` from the printed main theorem of CM and the class-field/adelic glue.** -/
theorem cmModuli_of' (hL : ShimuraMainCM) (hAL : ArtinLift) (hI : LatHatInter)
    (hH : IdeleLatticeHeegner) : CMModuli :=
  cmModuli_of hL autExtends fixedAlgebraic hAL hI hH

/-- **Row T-5 (`Shimura.ShimuraReciprocityModFn`) from two printed leaves, one textbook fact and
three glue Props.** -/
theorem shimuraReciprocityModFn_of_leaves' (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hD : DiscNeZero) (hAL : ArtinLift) (hI : LatHatInter) (hH : IdeleLatticeHeegner) :
    ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_leaves hCM hX hD autExtends fixedAlgebraic hAL hI hH

end T5Glue

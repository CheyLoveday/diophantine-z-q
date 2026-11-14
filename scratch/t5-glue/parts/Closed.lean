
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Shimura

/-! ## §7. The field-theory glue, proved (`Field.lean` body) -/

/-- **`AutExtends`, proved** (`exists_ringEquiv_extend`, Steinitz via Mathlib's transcendence
bases and `IsAlgClosure.equivOfEquiv`). -/
theorem autExtends : AutExtends := fun ρ => exists_ringEquiv_extend ιC ρ.toRingEquiv

/-- **`FixedAlgebraic`, proved** (`mem_range_of_fixed`). -/
theorem fixedAlgebraic : FixedAlgebraic := fun z hz => mem_range_of_fixed ιC z hz

/-- **`DiscNeZero`, proved** (`disc_ppD_ne_zero`: `Δ = (64π¹²/27)·1728·Δ_{Mathlib}(τ)`). -/
theorem discNeZero : DiscNeZero := fun τ => disc_ppD_ne_zero τ

/-- **`X0RatStructure` from the canonical-model leaf alone.** -/
theorem x0RatStructure_of' (hL : X0ModuliGalois) : X0RatStructure :=
  x0RatStructure_of hL autExtends fixedAlgebraic discNeZero

/-- **`CMModuli` from the printed main theorem of CM and the class-field/adelic glue.** -/
theorem cmModuli_of' (hL : ShimuraMainCM) (hAL : ArtinLift) (hI : LatHatInter)
    (hH : IdeleLatticeHeegner) : CMModuli :=
  cmModuli_of hL autExtends fixedAlgebraic hAL hI hH

/-- **Row T-5 (`Shimura.ShimuraReciprocityModFn`) from two printed leaves and three glue Props.** -/
theorem shimuraReciprocityModFn_of_leaves' (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hAL : ArtinLift) (hI : LatHatInter) (hH : IdeleLatticeHeegner) :
    ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_leaves hCM hX discNeZero autExtends fixedAlgebraic hAL hI hH

end T5Glue

namespace T5Glue

open ZInQ.Contrib.TYZGenus.Shimura

/-- **`CMModuli` from the printed main theorem of CM, class field theory (`ArtinLift`) and three
adelic facts** (`LatHatInter`, `StrongApprox`, `IdeleLatticeScale`). -/
theorem cmModuli_of'' (hL : ShimuraMainCM) (hAL : ArtinLift) (hI : LatHatInter)
    (hSA : StrongApprox) (hS : IdeleLatticeScale) : CMModuli :=
  cmModuli_of' hL hAL hI (ideleLatticeHeegner_of hS hSA hI)

/-- **Row T-5 (`Shimura.ShimuraReciprocityModFn`): final form.** Two printed leaves
(`ShimuraMainCM`: Shimura 1971 Thm. 5.4; `X0ModuliGalois`: the canonical model of `X₀(N)`) and four
glue Props (`ArtinLift`: surjectivity of the global Artin map; `LatHatInter`: `K ∩ 𝔞̂ = 𝔞`;
`StrongApprox`; `IdeleLatticeScale`: the ring-class lattice computation). -/
theorem shimuraReciprocityModFn_of_leaves'' (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hAL : ArtinLift) (hI : LatHatInter) (hSA : StrongApprox) (hS : IdeleLatticeScale) :
    ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_leaves' hCM hX hAL hI (ideleLatticeHeegner_of hS hSA hI)

end T5Glue

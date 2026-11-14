
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Shimura

/-! ## §7. The field-theory glue and `DiscNeZero`, proved; final forms -/

/-- **`AutExtends`, proved** (`exists_ringEquiv_extend`, Steinitz via Mathlib's transcendence
bases and `IsAlgClosure.equivOfEquiv`). -/
theorem autExtends : AutExtends := fun ρ => exists_ringEquiv_extend ιC ρ.toRingEquiv

/-- **`FixedAlgebraic`, proved** (`mem_range_of_fixed`). -/
theorem fixedAlgebraic : FixedAlgebraic := fun z hz => mem_range_of_fixed ιC z hz

/-- **`DiscNeZero`, proved** (`disc_ppD_ne_zero`: `Δ = (64π¹²/27)·1728·Δ_{Mathlib}(τ)`). -/
theorem discNeZero : DiscNeZero := fun τ => disc_ppD_ne_zero τ

/-- **`X0RatStructure` from the canonical-model leaf alone.** -/
theorem x0RatStructure_of_leaf (hL : X0ModuliGalois) : X0RatStructure :=
  x0RatStructure_of hL autExtends fixedAlgebraic discNeZero

/-- **`CMModuli` from the printed main theorem of CM and two glue Props**: `ArtinLift`
(surjectivity of the global Artin map onto `Gal(K^ab/K)`) and `IdeleLatticeScale` (the ring-class
lattice computation). -/
theorem cmModuli_of_leaf (hL : ShimuraMainCM) (hAL : ArtinLift) (hS : IdeleLatticeScale) :
    CMModuli :=
  cmModuli_of hL autExtends fixedAlgebraic hAL latHatInter
    (ideleLatticeHeegner_of hS strongApprox latHatInter)

/-- **Row T-5 (the kernel's `Shimura.ShimuraReciprocityModFn`): final form.** Two printed leaves
(`ShimuraMainCM`: Shimura 1971 Thm. 5.4; `X0ModuliGalois`: the canonical model of `X₀(N)`) and two
glue Props (`ArtinLift`, `IdeleLatticeScale`). -/
theorem shimuraReciprocityModFn_of_t5Leaves (hCM : ShimuraMainCM) (hX : X0ModuliGalois)
    (hAL : ArtinLift) (hS : IdeleLatticeScale) : ShimuraReciprocityModFn :=
  shimuraReciprocityModFn_of_split (cmModuli_of_leaf hCM hAL hS) (x0RatStructure_of_leaf hX)

end T5Glue

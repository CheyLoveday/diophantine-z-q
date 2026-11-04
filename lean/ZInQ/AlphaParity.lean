/- Copyright (c) 2026. -/
module

public import ZInQ.AlphaCore

/-!
Consecutive alpha values cannot both be even. This is the literal AFP
`one_odd` helper, retaining its source premise and integer remainder.
-/

public section

namespace ZInQ.AlphaPower

/-- AFP `one_odd`, obtained by reducing the Cassini identity modulo two. -/
theorem alphaZ_mod_two_eq_one_or_succ (B n : Nat) (_hB : 2 < B) :
    alphaZ B n % 2 = 1 ∨ alphaZ B (n + 1) % 2 = 1 := by
  -- Cassini proves the parity fact without the retained source bound.
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  have ha0 : alphaZ B n % 2 = 0 := by omega
  have hb0 : alphaZ B (n + 1) % 2 = 0 := by omega
  have hc := congrArg (fun z : Int => z % 2) (alphaZ_cassini B n)
  norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, ha0, hb0] at hc

end ZInQ.AlphaPower

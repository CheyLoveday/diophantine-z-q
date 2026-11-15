# hx-used results log

Base: 43513d87 (leaf-fold25). Target: top hypothesis `hX : T5Glue.X0ModuliGalois` of `ZInQ.OneProof.frozenTarget`.

## 1. Consumers of hX on the route (VERIFIED, read at base)

* `ZInQKernel/OneProof/Main.lean:64,70`: `hX` enters only as
  `T5Glue.shimuraReciprocityModFn_of_printed hCM hX : Shimura.ShimuraReciprocityModFn` (argument `hS` of
  `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves`).
* `RingClassLattice.lean:3352` `shimuraReciprocityModFn_of_printed` → `:2762 _of_t5''` → `:2754 _of_t5'` → `:2741 _of_t5`
  → `shimuraReciprocityModFn_of_split (cmModuli_of_t5 ..) (x0RatStructure_of_leaf hX)` (:2686, :2716).
  `x0RatStructure_of` (:819) applies `hL` at `(N, g, σ₀, τ, τ)` and `(N, g, σ, τ, τ')`; `_of_split` instantiates
  `τ = Q.tauH`, `τ' = Q'.tauH` for Heegner forms `Q Q' : HeegnerForm N D` (same `D`).
* Consumers of `hS : ShimuraReciprocityModFn` (TYZChain/Main.lean:61 → L321.lean:2156 → :2137 → :2123 → Bridge.lean:3134):
  `Shimura.cmFieldOfDefinition_of_shimuraModFn hS`, `Shimura.shimuraReciprocityPic_of_shimuraModFn hS`,
  `Shimura.cmValueRingClass_of_modFn hS` (→ `cmAlgebraic_of_cmValue`), `T321.znOverH4_of hS`.
  Each of these uses `hS` only at `N = 32` and `g ∈ {X0.xC, X0.yC}`:
  ShimuraMain.lean:188-191 (`shimuraReciprocityPic_of` at 32, xC/yC), ShimuraMain.lean:55-59 and Bridge.lean:3102-3108
  (`CMValueRingClass` at 32, xC/yC), L321.lean:1988-1992 (via `cmFieldOfDefinition_of_shimuraModFn`).
* gz-heegner (origin/wip/gz-heegner) does not use the kernel's `hX`; it introduces `X0ModuliGaloisMero` (stronger) and
  proves `x0ModuliGalois_of_mero`.

=> used form: `X0ModuliGalois` at `N = 32`, `g ∈ {X0.xC, X0.yC}`, `τ, τ'` Heegner points of level 32 and equal discriminant.

# gt-ringclass results log

Target: `T5Glue.RingClassLattice` (origin/wip/t5-glue 39bb3cd2, `scratch/t5-glue/T5Glue.lean` §5h), the last glue
under hS = `Shimura.ShimuraReciprocityModFn` of `frozenTarget` (with `shimuraReciprocityModFn_of_t5''`).

## Step 0: setup
- origin/wip/t5-glue already contained in base (merge: up to date).
- Build tree: reflink copy of ~/dzq-v-crowdkit-ex/.lake/build (cb80af83, leaf-fold15; differs from base only in
  three Contrib/OneProof files, TailZ26, Main). `lake build …ShimuraModFn …ShimuraMain`: nothing rebuilt.
- `scratch/gt-ringclass/DevBase.lean`: verbatim copies (python extraction) of the T5Glue declarations the statement
  needs (`AfK latHat finPart icl Osub mem_Osub idealOf finPart_inv_mul finPart_mul_inv latHat_eq_closure
  latHat_add_mem mem_latHat_of_mem fIntAd_sub_latHatO RingClassLattice`). COMPILED.

## Step 1: `Ô_O = ℤ + 𝔣̂` — COMPILED (Dev.lean)
- `fHat m f` (AddSubgroup: `∀ v, |z_v|_v ≤ exp(-e_v)`, `e_v` = exponent of `v` in Tau Ceti's `conductorModulus`),
  `oHat` (`ℤ + 𝔣̂`, open hence closed), `algebraMap_mem_fHat_of_mem_conductor`,
  `exists_mem_conductor_of_algebraMap_mem_fHat` (Tau Ceti `mem_finitePart_of_forall_mem_pow_exponent`),
  `mem_fHat_of_fIntAd` (`f𝒪̂ ⊆ 𝔣̂`), **`mem_latHat_O_iff`**: `z ∈ closure(O) ↔ ∃ a : ℤ, z − a ∈ 𝔣̂`
  (⊆: closed subgroup containing `O = ℤ + f𝓞_K`; ⊇: density of `K` modulo `f𝒪̂`, `K ∩ 𝔣̂ = 𝔣 ⊆ O`).

# rayclass-cft results log

Task: prove `ShimuraGlue.Ray.RayClassCM` (x6-glue §5.1) from `ShimuraCFT.ShimuraMainThmIDeligneY3Ab`
(shimura-cft), or reduce it to named smaller Props.

## Setup (11-14 18:20 PST)
- Merged origin/wip/x6-glue and origin/wip/shimura-cft (commit 0f5ec31a).
- Build tree: `cp -r` of ~/dzq-check2/.lake/build and lean/.lake/build (both at b5ff0474 = this base).
- `scratch/rayclass-cft/Base.lean` = verbatim copy of `scratch/shimura-cft/ShimuraCFT.lean`:
  0 errors, 1 min 47 s, all `#print axioms` standard (VERIFIED).

## Finding 1: the Deligne form does not reach the second component (analysis, SPECULATIVE until written up)
- `RayClassCM` speaks of every `ℚ̄`-point `y` of `Y` with CM object. By clause 1, `y_ℂ = Ψ(z, g)` for some
  `g ∈ (B⊗𝔸_f)^×`. The moduli clause (3) of `ShimuraDeligneBody` is stated at `g = 1` only.
- `π₀(Y_ℚ̄) = ℚ^×_{>0}\𝔸_f^×/nrd K₃ = (ℤ/3)^×` has two elements, so the points `Ψ(τ, 1)` form one
  geometric component only. For a CM point on the other component, the leaf says nothing about the object at
  `Ψ(z, g)`, so `z` cannot be shown to be a CM point, and clause 4 cannot be applied.
- Missing pieces (both consequences of printed theorems):
  1. the moduli clause at every `u ∈ 𝒪̂^×` (the pair at `Ψ(τ, u)` is `ℂ²/ι(𝒪)(τ,1)ᵀ`; only the level
     structure changes), the case `g ∈ 𝒪̂^×` of Deligne's/Shimura's moduli interpretation;
  2. class number one: `(B⊗𝔸_f)^× = B^×_{>0} · 𝒪̂^×` (Eichler; `𝒪` maximal in indefinite `B`).

## Plan of the reduction
RayClassCM ⇐ ShimuraMainThmIDeligneY3AbU (leaf 1 above folded into the Deligne leaf) + ClassNumberOneB (leaf)
+ MumfordRigidityCore (existing leaf, for `R1fpProps`) + glue:
- `QHatIntegral k`: `q(𝒪_k) ⊆ 𝒪` ⇒ `q̂` maps the mod-3 congruence ideles into `K₃`;
- `CMBaseChange`: CM of `P/ℚ̄` passes to an object `Q/ℂ` with `IsBaseChangeOf ιe P Q`;
- `CMAnalytic`: CM of `Q/ℂ` uniformized by `Λ_τ` ι-compatibly gives `β ∈ 𝒪` with the CM relation and
  `ι(β)(τ,1)ᵀ = λ(τ,1)ᵀ`.
Everything else (Tau Ceti kernel of the Artin map = ray subgroup, Galois descent of residue fields,
extension of automorphisms of `ℚ̄` to `ℂ`, DCRel manipulations) to be proved.

## Step 1 (11-14, 18:47): the reduction compiles (VERIFIED)
Files (olean chain via `chk.sh`, LEAN_PATH + /tmp/rc-olean; each imports the previous):
`Base.lean` (shimura-cft verbatim) → `RayDefs.lean` (x6-glue's Ray section verbatim, lines 6587-6745)
→ `RayProof1..5.lean`. All compile with 0 errors.
- `RayClassCFT.rayClassCM_of (hL : ShimuraMainThmIDeligneY3AbU) (hMR : MumfordRigidityCore)
  (hCN : ClassNumberOneB) (hI4 hI3 hI24 : QHatIntegral _) (hB : CMBaseChange) (hA : CMAnalytic)
  (hO4 hO3 hO24 : RingOfIntegersGen _ _) : RayClassCM` — axioms [propext, Classical.choice, Quot.sound].
- `RayClassCFT.embed_core` (one field) — standard axioms.
- Proved on the way: `iota_mul/add/smul/algebraMap`, `det_iota` (det ι(x) = nrd x), `det_pos_of_eig`,
  `smul_eq_of_eig` (Möbius fixed point), `exists_lift_ringHom`, `fieldMap_ιC_inj`, `galPt_fieldMap`,
  `residueImage_le` (Galois descent via InfiniteGalois.fixedField_fixingSubgroup), `exists_pos_decomp`,
  `conj_mem_K3Q`, `dcRel_of_decomp`, `dcRel_fix`, `qHatU_unitEmbedding`, `nrd_pos_of_cm`, `obj_at`,
  `cm_data`, `isTotallyComplex_of_root`, `finrank_K4/K3/K24`, Tau Ceti kernel of the Artin map =
  ray subgroup (`ker_ideleClassArtinMap`, `range_ideleClassNormMap_rayClassField`, `mk_mem_raySubgroup_iff`).

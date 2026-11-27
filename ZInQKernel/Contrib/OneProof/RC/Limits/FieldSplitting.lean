import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
# Lane RC29, round 5: the field case of the graded finite free models

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451). Over a field `k`
the residual cohomology of a complex is its cohomology, and in Elliot's perturbation (tex
4423–4437) the error term is `ε = 0`: the model differential vanishes. This file proves the field
case of lane RC31's graded finite free models (`GradedModel`, `GRetract`) without residual base
change: every complex `X` of `k`-vector spaces with finite-dimensional cohomology is homotopy
equivalent to its cohomology with zero differential.

Construction in each degree `n` (classical choice):
* `Zⁿ = ker d`, `Bⁿ = im d ≤ Zⁿ`, and the cohomology `Hⁿ = Zⁿ / Bⁿ` (`subquotientOf`);
* a retraction `ρ : Xⁿ → Zⁿ` of the inclusion (its kernel is a complement `Eⁿ` of `Zⁿ`);
* a section `σ : Hⁿ → Zⁿ` of the quotient map (its image is a complement of `Bⁿ` in `Zⁿ`);
* a section `s` of `d : X^{n−1} → Bⁿ`, corrected by `ρ` to land in `E^{n−1}`: it is the inverse of
  `d|_{E^{n−1}} : E^{n−1} ≅ Bⁿ`;
* a basis `Hⁿ ≃ k^{rank n}`, `rank n = dim Hⁿ`.

Then `i = σ` (through the basis), `p = (Zⁿ → Hⁿ) ∘ ρ`, and the contraction `h` is `s` composed
with the projection onto `Bⁿ` along `σ(Hⁿ) ⊕ Eⁿ`. The identities `d i = 0`, `p d = 0`, `p i = 1`,
`1 − i p = d h + h d`, `h² = 0`, `h i = 0`, `p h = 0` hold, giving `fsplitModel : GradedModel X`
with zero model differential and `fsplitEquiv`, a homotopy equivalence of the model with `X`.

The decomposition is explicit: `fsplit_isCompl_E` (`Xⁿ = Zⁿ ⊕ ker ρ`), `fsplit_isCompl_H`
(`Zⁿ = Bⁿ ⊕ σ(Hⁿ)`), `fsplitDE` (`d : ker ρ ≅ B` one degree up). Finiteness transfers from
Mathlib's `homology` through `fsplitHomologyEquiv` (`fsplit_hfin_of_homology`, and
`fsplitModel_rank_eq_homology`). Non-vacuity: `fsplit_nonempty_of_finiteDimensional` (every
degreewise finite-dimensional complex, e.g. every `matCx`) and `fsplitEx_rank` (a model of rank
one in every degree).

Index technique: every per-degree object is a function of its degree only; the contraction is
relation-indexed (`b + 1 = a`) through the image of the differential `X.d b a`, and the two
spellings of the image are identified by `fsplit_range_congr`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### Cohomology as a subquotient -/

section Homology

variable {R : Type} [CommRing R]

/-- The subquotient along equalities of the maps. Kind: definition. -/
def fsplitSubquotientCongr {V W Z : Type} [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] [AddCommGroup Z] [Module R Z] {f f' : V →ₗ[R] W} {g g' : W →ₗ[R] Z}
    (hf : f = f') (hg : g = g') : subquotientOf f g ≃ₗ[R] subquotientOf f' g' := by
  subst hf hg
  exact LinearEquiv.refl R _

/-- **The cohomology of a relation-indexed complex in degree `n` is its cocycles modulo
coboundaries** (the linear-equivalence form of RC31's `moduleFinite_homology_iff`). Kind:
definition (PROVED identification). -/
def fsplitHomologyEquiv (C : GCx R) (n : ℤ) :
    C.toCC.homology n ≃ₗ[R] subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl) := by
  have e := C.toCC.homologyIsoSc' (n - 1) n (n + 1) (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  have hr : LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).moduleCatToCycles =
      (LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).f.hom).comap
        (LinearMap.ker (C.toCC.sc' (n - 1) n (n + 1)).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  exact ((e.toLinearEquiv.trans
    (C.toCC.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv).trans
      (Submodule.quotEquivOfEq _ _ hr)).trans (fsplitSubquotientCongr hf hg)

end Homology

/-! ### The per-degree splitting data over a field -/

section Splitting

variable {k : Type} [Field k] (X : GCx k)

/-- The cocycles `Zⁿ = ker (d : Xⁿ → X^{n+1})`. Kind: definition. -/
abbrev fsplitZ (n : ℤ) : Submodule k (X.X n) :=
  LinearMap.ker (X.d n (n + 1) rfl)

/-- The coboundaries `Bⁿ = im (d : X^{n−1} → Xⁿ)`, inside the cocycles. Kind: definition. -/
abbrev fsplitBq (n : ℤ) : Submodule k (fsplitZ X n) :=
  (LinearMap.range (X.d (n - 1) n (by omega))).comap (fsplitZ X n).subtype

/-- The images of two differentials into the same degree coincide. Kind: PROVED. -/
theorem fsplit_range_congr (a b b' : ℤ) (h : b + 1 = a) (h' : b' + 1 = a) :
    LinearMap.range (X.d b a h) = LinearMap.range (X.d b' a h') := by
  obtain rfl : b = b' := by omega
  rfl

/-- A differential out of degree `b` vanishes iff the standard one does. Kind: PROVED. -/
theorem fsplit_d_eq_zero_iff (a b : ℤ) (hab : b + 1 = a) (v : X.X b) :
    X.d b a hab v = 0 ↔ X.d b (b + 1) rfl v = 0 := by
  subst hab
  rfl

/-- A retraction `ρ : Xⁿ → Zⁿ` of the inclusion of the cocycles (its kernel is a complement
`Eⁿ`). Kind: definition (classical choice). -/
def fsplitRho (n : ℤ) : X.X n →ₗ[k] fsplitZ X n :=
  Classical.choose (LinearMap.exists_leftInverse_of_injective (fsplitZ X n).subtype
    (Submodule.ker_subtype _))

/-- `ρ` is the identity on cocycles. Kind: PROVED. -/
theorem fsplitRho_of_mem (n : ℤ) (v : X.X n) (hv : v ∈ fsplitZ X n) :
    fsplitRho X n v = ⟨v, hv⟩ :=
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (fsplitZ X n).subtype (Submodule.ker_subtype _))) ⟨v, hv⟩

/-- `ρ ∘ ι = 1`. Kind: PROVED. -/
theorem fsplitRho_coe (n : ℤ) (z : fsplitZ X n) : fsplitRho X n (z : X.X n) = z :=
  fsplitRho_of_mem X n z z.2

/-- A section `σ : Hⁿ → Zⁿ` of the quotient map (its image is a complement of `Bⁿ` in `Zⁿ`).
Kind: definition (classical choice). -/
def fsplitSigma (n : ℤ) : (fsplitZ X n ⧸ fsplitBq X n) →ₗ[k] fsplitZ X n :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (fsplitBq X n).mkQ
    (Submodule.range_mkQ _))

/-- `σ` is a section of the quotient map. Kind: PROVED. -/
theorem fsplitSigma_spec (n : ℤ) (w : fsplitZ X n ⧸ fsplitBq X n) :
    (fsplitBq X n).mkQ (fsplitSigma X n w) = w :=
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective
    (fsplitBq X n).mkQ (Submodule.range_mkQ _))) w

/-- A section of `d : X^b → im d`. Kind: definition (classical choice). -/
def fsplitS0 (a b : ℤ) (hab : b + 1 = a) : LinearMap.range (X.d b a hab) →ₗ[k] X.X b :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (X.d b a hab).rangeRestrict
    (LinearMap.range_rangeRestrict _))

/-- The section of `d` is a section. Kind: PROVED. -/
theorem fsplitS0_spec (a b : ℤ) (hab : b + 1 = a) (y : LinearMap.range (X.d b a hab)) :
    X.d b a hab (fsplitS0 X a b hab y) = y :=
  congrArg Subtype.val (LinearMap.congr_fun (Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective (X.d b a hab).rangeRestrict
      (LinearMap.range_rangeRestrict _))) y)

/-- The section of `d` corrected to land in `E^b = ker ρ`: the inverse of `d|_{E^b} : E^b ≅
im d`. Kind: definition. -/
def fsplitS (a b : ℤ) (hab : b + 1 = a) : LinearMap.range (X.d b a hab) →ₗ[k] X.X b :=
  fsplitS0 X a b hab - (fsplitZ X b).subtype ∘ₗ fsplitRho X b ∘ₗ fsplitS0 X a b hab

/-- The corrected section lies in `ker ρ`. Kind: PROVED. -/
theorem fsplitRho_fsplitS (a b : ℤ) (hab : b + 1 = a) (y : LinearMap.range (X.d b a hab)) :
    fsplitRho X b (fsplitS X a b hab y) = 0 := by
  change fsplitRho X b (fsplitS0 X a b hab y -
    (fsplitRho X b (fsplitS0 X a b hab y) : X.X b)) = 0
  rw [map_sub, fsplitRho_coe, sub_self]

/-- `d s = 1` on the image of `d`. Kind: PROVED. -/
theorem fsplitS_spec (a b : ℤ) (hab : b + 1 = a) (y : LinearMap.range (X.d b a hab)) :
    X.d b a hab (fsplitS X a b hab y) = y := by
  change X.d b a hab (fsplitS0 X a b hab y -
    (fsplitRho X b (fsplitS0 X a b hab y) : X.X b)) = y
  have h0 : X.d b a hab (fsplitRho X b (fsplitS0 X a b hab y) : X.X b) = 0 :=
    (fsplit_d_eq_zero_iff X a b hab _).2 (fsplitRho X b (fsplitS0 X a b hab y)).2
  rw [map_sub, h0, sub_zero, fsplitS0_spec]

/-- `s d = 1 − ι ρ`. Kind: PROVED. -/
theorem fsplitS_d (a b : ℤ) (hab : b + 1 = a) (x : X.X b) :
    fsplitS X a b hab ⟨X.d b a hab x, LinearMap.mem_range_self _ x⟩ =
      x - (fsplitRho X b x : X.X b) := by
  set y : LinearMap.range (X.d b a hab) := ⟨X.d b a hab x, LinearMap.mem_range_self _ x⟩
  have hv : X.d b a hab (fsplitS0 X a b hab y - x) = 0 := by
    rw [map_sub, fsplitS0_spec, sub_self]
  have hmem : fsplitS0 X a b hab y - x ∈ fsplitZ X b := (fsplit_d_eq_zero_iff X a b hab _).1 hv
  have h2 : ((fsplitRho X b (fsplitS0 X a b hab y) : X.X b) - (fsplitRho X b x : X.X b)) =
      fsplitS0 X a b hab y - x := by
    rw [← Submodule.coe_sub, ← map_sub, fsplitRho_of_mem X b _ hmem]
  change fsplitS0 X a b hab y - (fsplitRho X b (fsplitS0 X a b hab y) : X.X b) =
    x - (fsplitRho X b x : X.X b)
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact h2.symm

/-- `s d = 1` on `E^b = ker ρ`. Kind: PROVED. -/
theorem fsplitS_d_of_rho (a b : ℤ) (hab : b + 1 = a) (x : X.X b) (hx : fsplitRho X b x = 0) :
    fsplitS X a b hab ⟨X.d b a hab x, LinearMap.mem_range_self _ x⟩ = x := by
  rw [fsplitS_d, hx]
  exact sub_zero x

/-- **The complement `Eⁿ = ker ρ` of the cocycles**: `Xⁿ = Zⁿ ⊕ Eⁿ`. Kind: PROVED. -/
theorem fsplit_isCompl_E (n : ℤ) : IsCompl (fsplitZ X n) (LinearMap.ker (fsplitRho X n)) :=
  LinearMap.isCompl_of_proj (fsplitRho_coe X n)

/-- **The complement `σ(Hⁿ)` of the coboundaries inside the cocycles**: `Zⁿ = Bⁿ ⊕ σ(Hⁿ)`. Kind:
PROVED. -/
theorem fsplit_isCompl_H (n : ℤ) :
    IsCompl (fsplitBq X n) (LinearMap.range (fsplitSigma X n)) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro z hzB ⟨w, rfl⟩
    have hw : w = 0 :=
      calc w = (fsplitBq X n).mkQ (fsplitSigma X n w) := (fsplitSigma_spec X n w).symm
        _ = 0 := (Submodule.Quotient.mk_eq_zero (fsplitBq X n)).2 hzB
    rw [hw, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    have hq : (fsplitBq X n).mkQ (z - fsplitSigma X n ((fsplitBq X n).mkQ z)) = 0 := by
      rw [map_sub, fsplitSigma_spec, sub_self]
    rw [← sub_add_cancel z (fsplitSigma X n ((fsplitBq X n).mkQ z))]
    exact Submodule.add_mem_sup ((Submodule.Quotient.mk_eq_zero (fsplitBq X n)).1 hq)
      (LinearMap.mem_range_self _ _)

/-- **`d` restricted to `E^b = ker ρ` is an isomorphism onto the coboundaries** `im (X.d b a)`,
with inverse the corrected section `s`. Kind: definition (PROVED identities). -/
def fsplitDE (a b : ℤ) (hab : b + 1 = a) :
    LinearMap.ker (fsplitRho X b) ≃ₗ[k] LinearMap.range (X.d b a hab) :=
  LinearEquiv.ofLinearMap
    ((X.d b a hab).rangeRestrict ∘ₗ (LinearMap.ker (fsplitRho X b)).subtype)
    (LinearMap.codRestrict _ (fsplitS X a b hab) (fun y => fsplitRho_fsplitS X a b hab y))
    (LinearMap.ext fun y => Subtype.ext (fsplitS_spec X a b hab y))
    (LinearMap.ext fun e => Subtype.ext (fsplitS_d_of_rho X a b hab e (LinearMap.mem_ker.1 e.2)))

/-- The coboundary component `ι (ρ x − σ [ρ x])` of `x ∈ Xⁿ`. Kind: definition. -/
def fsplitPiBRaw (n : ℤ) : X.X n →ₗ[k] X.X n :=
  (fsplitZ X n).subtype ∘ₗ
    (fsplitRho X n - fsplitSigma X n ∘ₗ (fsplitBq X n).mkQ ∘ₗ fsplitRho X n)

/-- The coboundary component, evaluated. Kind: PROVED. -/
theorem fsplitPiBRaw_apply (n : ℤ) (x : X.X n) :
    fsplitPiBRaw X n x = (fsplitRho X n x : X.X n) -
      (fsplitSigma X n ((fsplitBq X n).mkQ (fsplitRho X n x)) : X.X n) :=
  rfl

/-- The coboundary component is a coboundary. Kind: PROVED. -/
theorem fsplitPiBRaw_mem (n : ℤ) (x : X.X n) :
    fsplitPiBRaw X n x ∈ LinearMap.range (X.d (n - 1) n (by omega)) := by
  have hq : (fsplitBq X n).mkQ (fsplitRho X n x -
      fsplitSigma X n ((fsplitBq X n).mkQ (fsplitRho X n x))) = 0 := by
    rw [map_sub, fsplitSigma_spec, sub_self]
  have hm : fsplitRho X n x - fsplitSigma X n ((fsplitBq X n).mkQ (fsplitRho X n x)) ∈
      fsplitBq X n :=
    (Submodule.Quotient.mk_eq_zero (fsplitBq X n)).1 hq
  exact hm

/-- The projection onto the coboundaries `Bᵃ = im (X.d b a)` along `σ(Hᵃ) ⊕ Eᵃ`. Kind:
definition. -/
def fsplitPiB (a b : ℤ) (hab : b + 1 = a) : X.X a →ₗ[k] LinearMap.range (X.d b a hab) :=
  LinearMap.codRestrict _ (fsplitPiBRaw X a) (fun x => by
    rw [fsplit_range_congr X a b (a - 1) hab (by omega)]
    exact fsplitPiBRaw_mem X a x)

/-- The projection onto the coboundaries, evaluated. Kind: PROVED. -/
theorem fsplitPiB_coe (a b : ℤ) (hab : b + 1 = a) (x : X.X a) :
    (fsplitPiB X a b hab x : X.X a) = fsplitPiBRaw X a x :=
  rfl

/-- The projection onto the coboundaries kills `ker ρ`. Kind: PROVED. -/
theorem fsplitPiB_of_rho (a b : ℤ) (hab : b + 1 = a) (x : X.X a) (hx : fsplitRho X a x = 0) :
    fsplitPiB X a b hab x = 0 := by
  apply Subtype.ext
  rw [fsplitPiB_coe, fsplitPiBRaw_apply, hx, map_zero, map_zero, sub_self]
  rfl

/-- The projection onto the coboundaries is the identity on coboundaries. Kind: PROVED. -/
theorem fsplitPiB_d (n : ℤ) (x : X.X n) :
    fsplitPiB X (n + 1) n rfl (X.d n (n + 1) rfl x) =
      ⟨X.d n (n + 1) rfl x, LinearMap.mem_range_self _ x⟩ := by
  have hz : X.d n (n + 1) rfl x ∈ fsplitZ X (n + 1) :=
    LinearMap.mem_ker.2 (X.d_d n (n + 1) (n + 1 + 1) rfl rfl x)
  have hb : (⟨X.d n (n + 1) rfl x, hz⟩ : fsplitZ X (n + 1)) ∈ fsplitBq X (n + 1) := by
    change X.d n (n + 1) rfl x ∈ LinearMap.range (X.d (n + 1 - 1) (n + 1) (by omega))
    rw [fsplit_range_congr X (n + 1) (n + 1 - 1) n (by omega) rfl]
    exact LinearMap.mem_range_self _ x
  have hq : (fsplitBq X (n + 1)).mkQ ⟨X.d n (n + 1) rfl x, hz⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hb
  apply Subtype.ext
  rw [fsplitPiB_coe, fsplitPiBRaw_apply, fsplitRho_of_mem X (n + 1) _ hz, hq, map_zero]
  exact sub_zero _

/-- **The contraction homotopy** `h = s ∘ π_B : Xᵃ → X^b` (`b + 1 = a`): the inverse of
`d|_{E^b}` on the coboundaries and `0` on `σ(Hᵃ) ⊕ Eᵃ`. Kind: definition. -/
def fsplitHtpy (a b : ℤ) (hab : b + 1 = a) : X.X a →ₗ[k] X.X b :=
  fsplitS X a b hab ∘ₗ fsplitPiB X a b hab

/-- `h` lands in `ker ρ`. Kind: PROVED. -/
theorem fsplitRho_htpy (a b : ℤ) (hab : b + 1 = a) (x : X.X a) :
    fsplitRho X b (fsplitHtpy X a b hab x) = 0 :=
  fsplitRho_fsplitS X a b hab _

/-- `h² = 0`. Kind: PROVED. -/
theorem fsplitHtpy_htpy (a b c : ℤ) (hab : b + 1 = a) (hbc : c + 1 = b) (x : X.X a) :
    fsplitHtpy X b c hbc (fsplitHtpy X a b hab x) = 0 := by
  change fsplitS X b c hbc (fsplitPiB X b c hbc (fsplitHtpy X a b hab x)) = 0
  rw [fsplitPiB_of_rho X b c hbc _ (fsplitRho_htpy X a b hab x), map_zero]

/-! ### The model maps -/

/-- **The rank of the model** in degree `n`: the dimension of the cohomology `Hⁿ`. Kind:
definition. -/
def fsplitRank (n : ℤ) : ℕ :=
  Module.finrank k (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl))

variable (hfin : ∀ n, FiniteDimensional k
  (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl)))

/-- A basis `Hⁿ ≃ k^{rank n}`. Kind: definition (classical choice). -/
def fsplitE (n : ℤ) : (fsplitZ X n ⧸ fsplitBq X n) ≃ₗ[k] (Fin (fsplitRank X n) → k) :=
  haveI := hfin n
  (Module.finBasis k (fsplitZ X n ⧸ fsplitBq X n)).equivFun

/-- The inclusion `i : k^{rank n} ≅ Hⁿ → Xⁿ` (through `σ`). Kind: definition. -/
def fsplitIMap (n : ℤ) : (Fin (fsplitRank X n) → k) →ₗ[k] X.X n :=
  (fsplitZ X n).subtype ∘ₗ fsplitSigma X n ∘ₗ (fsplitE X hfin n).symm.toLinearMap

/-- The projection `p : Xⁿ → Hⁿ ≅ k^{rank n}` (through `ρ`). Kind: definition. -/
def fsplitPMap (n : ℤ) : X.X n →ₗ[k] (Fin (fsplitRank X n) → k) :=
  (fsplitE X hfin n).toLinearMap ∘ₗ (fsplitBq X n).mkQ ∘ₗ fsplitRho X n

/-- `d i = 0`. Kind: PROVED. -/
theorem fsplit_d_IMap (n : ℤ) (y : Fin (fsplitRank X n) → k) :
    X.d n (n + 1) rfl (fsplitIMap X hfin n y) = 0 :=
  LinearMap.mem_ker.1 (fsplitSigma X n ((fsplitE X hfin n).symm y)).2

/-- `p d = 0`. Kind: PROVED. -/
theorem fsplitPMap_d (n : ℤ) (x : X.X n) :
    fsplitPMap X hfin (n + 1) (X.d n (n + 1) rfl x) = 0 := by
  have hz : X.d n (n + 1) rfl x ∈ fsplitZ X (n + 1) :=
    LinearMap.mem_ker.2 (X.d_d n (n + 1) (n + 1 + 1) rfl rfl x)
  have hb : (⟨X.d n (n + 1) rfl x, hz⟩ : fsplitZ X (n + 1)) ∈ fsplitBq X (n + 1) := by
    change X.d n (n + 1) rfl x ∈ LinearMap.range (X.d (n + 1 - 1) (n + 1) (by omega))
    rw [fsplit_range_congr X (n + 1) (n + 1 - 1) n (by omega) rfl]
    exact LinearMap.mem_range_self _ x
  have hq : (fsplitBq X (n + 1)).mkQ ⟨X.d n (n + 1) rfl x, hz⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hb
  change fsplitE X hfin (n + 1) ((fsplitBq X (n + 1)).mkQ
    (fsplitRho X (n + 1) (X.d n (n + 1) rfl x))) = 0
  rw [fsplitRho_of_mem X (n + 1) _ hz, hq, map_zero]

/-- `p i = 1`. Kind: PROVED. -/
theorem fsplitPMap_IMap (n : ℤ) (y : Fin (fsplitRank X n) → k) :
    fsplitPMap X hfin n (fsplitIMap X hfin n y) = y := by
  change fsplitE X hfin n ((fsplitBq X n).mkQ (fsplitRho X n
    (fsplitSigma X n ((fsplitE X hfin n).symm y) : X.X n))) = y
  rw [fsplitRho_coe, fsplitSigma_spec, LinearEquiv.apply_symm_apply]

/-- `i p = ι σ [ρ x]`. Kind: PROVED. -/
theorem fsplitIMap_PMap (n : ℤ) (x : X.X n) :
    fsplitIMap X hfin n (fsplitPMap X hfin n x) =
      (fsplitSigma X n ((fsplitBq X n).mkQ (fsplitRho X n x)) : X.X n) := by
  change (fsplitSigma X n ((fsplitE X hfin n).symm (fsplitE X hfin n
    ((fsplitBq X n).mkQ (fsplitRho X n x)))) : X.X n) = _
  rw [LinearEquiv.symm_apply_apply]

/-- `h i = 0`. Kind: PROVED. -/
theorem fsplitHtpy_IMap (a b : ℤ) (hab : b + 1 = a) (y : Fin (fsplitRank X a) → k) :
    fsplitHtpy X a b hab (fsplitIMap X hfin a y) = 0 := by
  have h0 : fsplitPiB X a b hab (fsplitIMap X hfin a y) = 0 := by
    apply Subtype.ext
    change ((fsplitRho X a (fsplitSigma X a ((fsplitE X hfin a).symm y) : X.X a) -
      fsplitSigma X a ((fsplitBq X a).mkQ (fsplitRho X a
        (fsplitSigma X a ((fsplitE X hfin a).symm y) : X.X a))) : fsplitZ X a) : X.X a) = 0
    rw [fsplitRho_coe, fsplitSigma_spec, sub_self]
    rfl
  change fsplitS X a b hab (fsplitPiB X a b hab (fsplitIMap X hfin a y)) = 0
  rw [h0, map_zero]

/-- `p h = 0`. Kind: PROVED. -/
theorem fsplitPMap_htpy (a b : ℤ) (hab : b + 1 = a) (x : X.X a) :
    fsplitPMap X hfin b (fsplitHtpy X a b hab x) = 0 := by
  change fsplitE X hfin b ((fsplitBq X b).mkQ (fsplitRho X b (fsplitHtpy X a b hab x))) = 0
  rw [fsplitRho_htpy, map_zero, map_zero]

/-- **`1 − i p = d h + h d`** (tex 4423–4437 with `ε = 0`). Kind: PROVED. -/
theorem fsplit_homotopy (n : ℤ) (x : X.X n) :
    x - fsplitIMap X hfin n (fsplitPMap X hfin n x) =
      X.d (n - 1) n (by omega) (fsplitHtpy X n (n - 1) (by omega) x) +
        fsplitHtpy X (n + 1) n rfl (X.d n (n + 1) rfl x) := by
  have h1 : X.d (n - 1) n (by omega) (fsplitHtpy X n (n - 1) (by omega) x) =
      fsplitPiBRaw X n x :=
    fsplitS_spec X n (n - 1) (by omega) _
  have h2 : fsplitHtpy X (n + 1) n rfl (X.d n (n + 1) rfl x) =
      x - (fsplitRho X n x : X.X n) := by
    change fsplitS X (n + 1) n rfl (fsplitPiB X (n + 1) n rfl (X.d n (n + 1) rfl x)) = _
    rw [fsplitPiB_d, fsplitS_d]
  rw [h1, h2, fsplitIMap_PMap, fsplitPiBRaw_apply]
  abel

/-! ### The graded model -/

/-- The zero model differential. Kind: definition. -/
def fsplitDC (a b : ℤ) (_h : a + 1 = b) : Matrix (Fin (fsplitRank X b)) (Fin (fsplitRank X a)) k :=
  0

/-- `0² = 0`. Kind: PROVED. -/
theorem fsplitDC_sq (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    fsplitDC X b c hbc * fsplitDC X a b hab = 0 :=
  Matrix.zero_mul _

/-- The model complex `k^{rank n}` with zero differential. Kind: definition. -/
abbrev fsplitCx : GCx k :=
  matCx (fsplitRank X) (fsplitDC X) (fsplitDC_sq X)

/-- The model differential vanishes. Kind: PROVED. -/
theorem fsplitCx_d (a b : ℤ) (h : a + 1 = b) (y : (fsplitCx X).X a) :
    (fsplitCx X).d a b h y = 0 :=
  Matrix.zero_mulVec (m := Fin (fsplitRank X b)) (y : Fin (fsplitRank X a) → k)

/-- The inclusion as a chain map. Kind: definition. -/
def fsplitI : GHom (fsplitCx X) X where
  f a b hab := by
    subst hab
    exact fsplitIMap X hfin a
  comm := by
    intro i i₁ j j₁ hij h₁ h₂ hj x
    subst hij hj h₁
    change fsplitIMap X hfin (i + 1) ((fsplitCx X).d i (i + 1) rfl x) =
      X.d i (i + 1) rfl (fsplitIMap X hfin i x)
    exact (congrArg (fsplitIMap X hfin (i + 1)) (fsplitCx_d X i (i + 1) rfl x)).trans
      ((map_zero (fsplitIMap X hfin (i + 1))).trans (fsplit_d_IMap X hfin i x).symm)

/-- The projection as a chain map. Kind: definition. -/
def fsplitP : GHom X (fsplitCx X) where
  f a b hab := by
    subst hab
    exact fsplitPMap X hfin a
  comm := by
    intro i i₁ j j₁ hij h₁ h₂ hj x
    subst hij hj h₁
    change fsplitPMap X hfin (i + 1) (X.d i (i + 1) rfl x) =
      (fsplitCx X).d i (i + 1) rfl (fsplitPMap X hfin i x)
    rw [fsplitPMap_d]
    exact (fsplitCx_d X i (i + 1) rfl _).symm

/-- **The normalized graded deformation retract of `X` onto its cohomology** (tex 4423–4437 with
`ε = 0`). Kind: definition (PROVED identities). -/
def fsplitRetract : GRetract X (fsplitCx X) where
  i := fsplitI X hfin
  p := fsplitP X hfin
  h := fsplitHtpy X
  p_i n y := fsplitPMap_IMap X hfin n y
  homotopy n x := fsplit_homotopy X hfin n x
  h_h a b c hab hbc x := fsplitHtpy_htpy X a b c hab hbc x
  h_i a b hab y := fsplitHtpy_IMap X hfin a b hab y
  p_h a b hab x := fsplitPMap_htpy X hfin a b hab x

/-- **The field case of the graded finite free model** (Lemma `ex:limits-inner-limit`, tex
4391–4451, over a field: the residual cohomology is the cohomology, and Elliot's perturbation has
`ε = 0`): ranks `dim Hⁿ`, zero model differential, and the normalized retract. Kind:
definition. -/
def fsplitModel : GradedModel X where
  rank := fsplitRank X
  dC := fsplitDC X
  dC_sq := fsplitDC_sq X
  retract := fsplitRetract X hfin

/-- The ranks of the field model are the dimensions of the cohomology. Kind: PROVED. -/
theorem fsplitModel_rank (n : ℤ) :
    (fsplitModel X hfin).rank n =
      Module.finrank k (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl)) :=
  rfl

/-- All model differentials of the field model vanish. Kind: PROVED. -/
theorem fsplitModel_dC (a b : ℤ) (h : a + 1 = b) : (fsplitModel X hfin).dC a b h = 0 :=
  rfl

/-- **Every complex over a field with finite-dimensional cohomology is homotopy equivalent to its
cohomology with zero differential.** Kind: definition (PROVED). -/
def fsplitEquiv : HomotopyEquiv (fsplitModel X hfin).modelCx.toCC X.toCC :=
  (fsplitModel X hfin).retract.homotopyEquiv

end Splitting

/-! ### Finiteness transfer and non-vacuity -/

section Finiteness

variable {k : Type} [Field k] (X : GCx k)

/-- Finite-dimensional cohomology in the shape of Mathlib's `homology` gives the finiteness
hypothesis of `fsplitModel`. Kind: PROVED. -/
theorem fsplit_hfin_of_homology (h : ∀ n, FiniteDimensional k (X.toCC.homology n)) (n : ℤ) :
    FiniteDimensional k (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl)) :=
  haveI := h n
  Module.Finite.equiv (fsplitHomologyEquiv X n)

/-- A degreewise finite-dimensional complex has finite-dimensional cohomology. Kind: PROVED. -/
theorem fsplit_hfin_of_finiteDimensional (h : ∀ n, FiniteDimensional k (X.X n)) (n : ℤ) :
    FiniteDimensional k (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl)) :=
  haveI := h n
  inferInstance

/-- The ranks of the field model are the dimensions of Mathlib's cohomology. Kind: PROVED. -/
theorem fsplitModel_rank_eq_homology
    (hfin : ∀ n, FiniteDimensional k
      (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl))) (n : ℤ) :
    (fsplitModel X hfin).rank n = Module.finrank k (X.toCC.homology n) :=
  (LinearEquiv.finrank_eq (fsplitHomologyEquiv X n)).symm

/-- **Non-vacuity**: every degreewise finite-dimensional complex over a field (for instance every
matrix complex `matCx`) has a graded finite free model with zero differential. Kind: PROVED. -/
theorem fsplit_nonempty_of_finiteDimensional (h : ∀ n, FiniteDimensional k (X.X n)) :
    ∃ R : GradedModel X, ∀ a b (hab : a + 1 = b), R.dC a b hab = 0 :=
  ⟨fsplitModel X (fsplit_hfin_of_finiteDimensional X h), fun a b hab =>
    fsplitModel_dC X _ a b hab⟩

/-- **Non-vacuity, concretely**: the complex `ℚ` in every degree with zero differential has the
field model. Kind: PROVED. -/
theorem fsplit_nonempty_example :
    ∃ R : GradedModel (matCx (A := ℚ) (fun _ => 1) (fun _ _ _ => 0)
      (fun _ _ _ _ _ => Matrix.zero_mul _)), ∀ a b (hab : a + 1 = b), R.dC a b hab = 0 :=
  fsplit_nonempty_of_finiteDimensional _ (fun n => by
    change FiniteDimensional ℚ (Fin 1 → ℚ)
    infer_instance)

/-- The field model from finite-dimensional cohomology in the shape of Mathlib's `homology`.
Kind: definition. -/
def fsplitModelOfHomology (h : ∀ n, FiniteDimensional k (X.toCC.homology n)) : GradedModel X :=
  fsplitModel X (fsplit_hfin_of_homology X h)

/-- **Homotopy equivalence with the cohomology**, from finite-dimensional cohomology in the shape
of Mathlib's `homology`. Kind: definition (PROVED). -/
def fsplitEquivOfHomology (h : ∀ n, FiniteDimensional k (X.toCC.homology n)) :
    HomotopyEquiv (fsplitModelOfHomology X h).modelCx.toCC X.toCC :=
  fsplitEquiv X (fsplit_hfin_of_homology X h)

/-- The inclusion of the cohomology is a quasi-isomorphism. Kind: PROVED. -/
theorem fsplit_quasiIso_i
    (hfin : ∀ n, FiniteDimensional k
      (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl))) :
    QuasiIso (GHom.toCC (fsplitModel X hfin).retract.i) :=
  (fsplitModel X hfin).retract.quasiIso_i

/-- The projection onto the cohomology is a quasi-isomorphism. Kind: PROVED. -/
theorem fsplit_quasiIso_p
    (hfin : ∀ n, FiniteDimensional k
      (subquotientOf (X.d (n - 1) n (by omega)) (X.d n (n + 1) rfl))) :
    QuasiIso (GHom.toCC (fsplitModel X hfin).retract.p) :=
  (fsplitModel X hfin).retract.quasiIso_p

/-- The cohomology of zero maps is the middle term. Kind: PROVED. -/
theorem fsplit_finrank_subquotient_zero {V W Z : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup Z] [Module k Z] :
    Module.finrank k (subquotientOf (0 : V →ₗ[k] W) (0 : W →ₗ[k] Z)) = Module.finrank k W := by
  have h1 : (LinearMap.range (0 : V →ₗ[k] W)).comap (LinearMap.ker (0 : W →ₗ[k] Z)).subtype =
      ⊥ := by
    rw [LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype]
  exact ((Submodule.quotEquivOfEqBot _ h1).trans
    (LinearEquiv.ofTop _ LinearMap.ker_zero)).finrank_eq

end Finiteness

/-! ### A concrete example -/

section Example

/-- The example complex: `ℚ` in every degree with zero differential. Kind: definition. -/
abbrev fsplitExCx : GCx ℚ :=
  matCx (fun _ => 1) (fun _ _ _ => 0) (fun _ _ _ _ _ => Matrix.zero_mul _)

/-- The example complex has finite-dimensional cohomology. Kind: PROVED. -/
theorem fsplitExCx_hfin (n : ℤ) : FiniteDimensional ℚ
    (subquotientOf (fsplitExCx.d (n - 1) n (by omega)) (fsplitExCx.d n (n + 1) rfl)) :=
  fsplit_hfin_of_finiteDimensional _ (fun _ => by
    change FiniteDimensional ℚ (Fin 1 → ℚ)
    infer_instance) n

/-- **Non-vacuity with a nonzero model**: the field model of the example complex has rank one in
every degree (and zero differential). Kind: PROVED. -/
theorem fsplitEx_rank (n : ℤ) : (fsplitModel fsplitExCx fsplitExCx_hfin).rank n = 1 := by
  rw [fsplitModel_rank]
  change Module.finrank ℚ (subquotientOf (Matrix.toLin' (0 : Matrix (Fin 1) (Fin 1) ℚ))
    (Matrix.toLin' (0 : Matrix (Fin 1) (Fin 1) ℚ))) = 1
  rw [map_zero, fsplit_finrank_subquotient_zero, Module.finrank_fin_fun]

end Example

end ZInQ.Manuscript.RC.Limits

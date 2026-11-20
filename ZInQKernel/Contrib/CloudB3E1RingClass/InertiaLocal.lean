import ZInQKernel.Contrib.CloudB3E1RingClass.ClassGroupMap

/-!
# The inertia group of `H_f/K` as the Artin image of local units

Manuscript `diophantine_zq.tex`, tex 3679–3681 (the inertia group of the ring class field `H_r`
at `r`).

For a place `v` of `K`, the local units `𝒪_v^×` act on `H_f` through the global Artin map of the
ideles concentrated at `v`:

* `unitPic f v : K_v^× → Pic(ℤ + f𝒪_K)`, `u ↦` the ring-class quotient of the idele class of `u`
  at `v`; `unitArtin f S v : K_v^× → Gal(H_f/K)`, its image under `Pic ≃ Gal(H_f/K)`.
* `locGal_eq_unitArtin`: if `σ ∈ G_{K_v}` represents the local Artin symbol of `u`, then the
  restriction of `σ` to `H_f` is `unitArtin u` (local–global compatibility,
  `globalArtinMap_local`, and `ringClassArtinEquiv_ringClassIdeleQuotient`).
* **`inertiaGal_eq_map_unitArtin`** (PROVED): the inertia group `inertiaGal f S v` is the image of
  `U(K_v, 0) = 𝒪_v^×` under `unitArtin` (the local Artin map sends `𝒪_v^×` onto the image of the
  inertia subgroup, `map_artinMap_unitFiltration_zero`). This holds at every place.
* **`inertiaGal_le_ker_galToClassGroup`** (PROVED): the inertia group lies in the kernel of
  `Gal(H_f/K) → Cl(K)`, at every place: a local unit idele has trivial ideal class.

Kinds: definitions and PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex

namespace ZInQ.Contrib.CloudB3E1RingClass

variable {K : Type} [Field K] [NumberField K]
variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- **The Picard class of a local idele** `u ∈ K_v^×`: the ring-class quotient
`C_K → Pic(ℤ + f𝒪_K)` of the idele class of `u` at `v` (tex 3679–3681). Kind: definition. -/
def unitPic (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Pic (ringClassOrder (K := K) f hf) :=
  (ringClassIdeleQuotient (ringClassOrder (K := K) f hf)).comp
    (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v)

/-- **The Artin symbol in `Gal(H_f/K)` of a local idele** `u ∈ K_v^×` (tex 3679–3681).
Kind: definition. -/
def unitArtin (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* ringClassGal f hf S hS :=
  (ringClassPicEquiv f hf S hS).toMonoidHom.comp (unitPic f hf v)

/-- **Local–global compatibility for `H_f`**: a representative `σ ∈ G_{K_v}` of the local Artin
symbol of `u` restricts to `unitArtin u` (tex 3679–3681). Kind: PROVED. -/
theorem locGal_eq_unitArtin (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (u : (v.adicCompletion K)ˣ)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) =
      artinMap (v.adicCompletion K) u) :
    locGal f hf S hS v σ = unitArtin f hf S hS v u := by
  have h1 : localArtinAt K (ringClassField (ringClassOrder (K := K) f hf)) v u =
      Abelianization.of (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)
        (locGal f hf S hS v σ)) :=
    localArtinAt_eq_of_mk_eq_artinMap v σ hσ (ringClassEmb f hf S hS v) _
      (ringClassEmb_locGal f hf S hS v σ)
  have h2 := of_ideleClassArtinMap K (ringClassField (ringClassOrder (K := K) f hf))
    (ringClassField (ringClassOrder (K := K) f hf)).val
    (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u)
  rw [IdeleClassGroup.ofAdicCompletion_apply, globalArtinMap_local, toMul_ofMul, h1,
    ← IdeleClassGroup.ofAdicCompletion_apply,
    ← ringClassArtinEquiv_ringClassIdeleQuotient] at h2
  have h3 := Abelianization.of_injective h2
  change _ = (AlgEquiv.autCongr (ringClassFieldOfEquiv f hf S hS)).symm
    (ringClassArtinEquiv (ringClassOrder (K := K) f hf) (unitPic f hf v u))
  rw [unitPic, MonoidHom.comp_apply, h3, MulEquiv.symm_apply_apply]

/-- **The inertia group at `v` is the Artin image of the local units** `𝒪_v^×` (tex 3679–3681),
at every place `v`. Kind: PROVED. -/
theorem inertiaGal_eq_map_unitArtin (v : HeightOneSpectrum (𝓞 K)) :
    inertiaGal f hf S hS v =
      (unitFiltration (v.adicCompletion K) 0).map (unitArtin f hf S hS v) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    have hmem : (QuotientGroup.mk σ :
        Field.absoluteGaloisGroupAbelianization (v.adicCompletion K)) ∈
        (unitFiltration (v.adicCompletion K) 0).map (artinMap (v.adicCompletion K)) := by
      rw [map_artinMap_unitFiltration_zero]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨u, hu, hu'⟩ := hmem
    exact ⟨u, hu, (locGal_eq_unitArtin f hf S hS v σ u hu'.symm).symm⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hmem : artinMap (v.adicCompletion K) u ∈
        (inertiaSubgroup (v.adicCompletion K)).map (QuotientGroup.mk' _) := by
      rw [← map_artinMap_unitFiltration_zero]
      exact ⟨u, hu, rfl⟩
    obtain ⟨σ, hσ, hσ'⟩ := hmem
    exact ⟨σ, hσ, locGal_eq_unitArtin f hf S hS v σ u hσ'⟩

/-! ### Inertia maps trivially to the class group -/

/-- `Pic(O) → Cl(K)` on the ring-class quotient of an idele class is the ideal class of its ray
class. Kind: PROVED. -/
theorem picToClassGroup_ringClassIdeleQuotient (O : NumberFieldOrder K)
    (c : IdeleClassGroup (𝓞 K) K) :
    picToClassGroup O (ringClassIdeleQuotient O c) =
      rayClassToClassGroup O.conductorModulus (rayClassQuotient O.conductorModulus c) := by
  rw [ringClassIdeleQuotient_apply]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, ker_rayClassToPic_le O⟩ _

/-- A local unit idele has trivial ideal class, for every modulus (tex 3679–3681).
Kind: PROVED. -/
theorem rayClassToClassGroup_rayClassQuotient_ofAdicCompletion (𝔪 : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    rayClassToClassGroup 𝔪 (rayClassQuotient 𝔪 (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u)) =
      1 := by
  rw [rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap, MonoidHom.comp_apply,
    ← MonoidHom.comp_apply (classMap _) (rayClassQuotient 𝔪), classMap_comp_rayClassQuotient,
    IdeleClassGroup.ofAdicCompletion_apply,
    rayClassQuotient_mk_of_mem (𝔪 := Modulus.one K) (by rw [ideleCongrOneSubgroup_one]; trivial)]
  have h1 : (⟨FiniteAdeleRing.toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K
      (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)),
      toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo (𝔪 := Modulus.one K)
        (by rw [ideleCongrOneSubgroup_one]; trivial)⟩ : idealsPrimeTo (Modulus.one K)) = 1 :=
    Subtype.ext (by simp [hu])
  rw [h1, map_one, map_one]

/-- **Inertia lies in the kernel of `Gal(H_f/K) → Cl(K)`** (the ring class field contains the
Hilbert class field, which is unramified): for every place `v` (tex 3679–3681). Kind: PROVED. -/
theorem inertiaGal_le_ker_galToClassGroup (v : HeightOneSpectrum (𝓞 K)) :
    inertiaGal f hf S hS v ≤ (galToClassGroup f hf S hS).ker := by
  rw [inertiaGal_eq_map_unitArtin]
  rintro _ ⟨u, hu, rfl⟩
  rw [MonoidHom.mem_ker, galToClassGroup, unitArtin, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, unitPic,
    MonoidHom.comp_apply, picToClassGroup_ringClassIdeleQuotient]
  exact rayClassToClassGroup_rayClassQuotient_ofAdicCompletion _ v u
    ((HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v).mp hu)

end ZInQ.Contrib.CloudB3E1RingClass

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-!
# An elementwise criterion for quasi-isomorphisms of complexes of modules

For a morphism `φ : K ⟶ L` of homological complexes of modules and a degree `j` (with previous
degree `i` and next degree `k`), `φ` is a quasi-isomorphism in degree `j` as soon as

* (surjectivity on classes) every cycle `y` of `L` in degree `j` is, up to a boundary, the image of
  a cycle `x` of `K`: `φ x = y + d z`;
* (injectivity on classes) a cycle `x` of `K` whose image is a boundary is a boundary.

`quasiIsoAt_of_elem` (PROVED), from the short-complex form `sc_quasiIso_of_elem`; the class map of
a short complex of modules is surjective and kills exactly the boundaries
(`homologyπ_eq_zero_iff_moduleCat`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

/-- The class of a cycle of a short complex of modules vanishes iff the cycle is a boundary. -/
theorem homologyπ_eq_zero_iff_moduleCat (S : ShortComplex (ModuleCat.{u} R)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w, S.f.hom w = S.iCycles.hom z := by
  constructor
  · intro h
    have h1 : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) = 0 := by
      have e := congrArg (fun f => f.hom z) (ShortComplex.π_moduleCatCyclesIso_hom S)
      change S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) at e
      rw [← e, h, map_zero]
    change (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatCyclesIso.hom.hom z) = 0 at h1
    have h2 : (show LinearMap.ker S.g.hom from S.moduleCatCyclesIso.hom.hom z) ∈
        LinearMap.range S.moduleCatToCycles := (Submodule.Quotient.mk_eq_zero _).1 h1
    obtain ⟨w, hw⟩ := h2
    refine ⟨w, ?_⟩
    have e2 := congrArg (fun f => f.hom z) (ShortComplex.moduleCatCyclesIso_hom_i S)
    change S.moduleCatLeftHomologyData.i.hom (S.moduleCatCyclesIso.hom.hom z) = _ at e2
    rw [← e2]
    exact congrArg Subtype.val hw
  · rintro ⟨w, hw⟩
    have hz : S.toCycles.hom w = z := by
      apply (ModuleCat.mono_iff_injective S.iCycles).1 inferInstance
      rw [← hw]
      exact congrArg (fun f => f.hom w) S.toCycles_i
    rw [← hz]
    exact congrArg (fun f => f.hom w) S.toCycles_comp_homologyπ

/-- The cycle of a short complex of modules with a given underlying element. -/
theorem exists_cycle_moduleCat (S : ShortComplex (ModuleCat.{u} R)) (y : S.X₂)
    (hy : S.g.hom y = 0) : ∃ z : S.cycles, S.iCycles.hom z = y :=
  ⟨S.moduleCatCyclesIso.inv.hom ⟨y, hy⟩,
    congrArg (fun f => f.hom (⟨y, hy⟩ : LinearMap.ker S.g.hom))
      (ShortComplex.moduleCatCyclesIso_inv_iCycles S)⟩

/-- **Elementwise criterion, short complexes.** -/
theorem sc_quasiIso_of_elem {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (hsurj : ∀ y, S₂.g.hom y = 0 → ∃ x, S₁.g.hom x = 0 ∧ ∃ z, φ.τ₂.hom x = y + S₂.f.hom z)
    (hinj : ∀ x, S₁.g.hom x = 0 → ∀ z, φ.τ₂.hom x = S₂.f.hom z → ∃ w, S₁.f.hom w = x) :
    ShortComplex.QuasiIso φ := by
  have hnat : ∀ c, (ShortComplex.homologyMap φ).hom (S₁.homologyπ.hom c) =
      S₂.homologyπ.hom ((ShortComplex.cyclesMap φ).hom c) := fun c =>
    congrArg (fun f => f.hom c) (ShortComplex.homologyπ_naturality φ)
  have hci : ∀ c, S₂.iCycles.hom ((ShortComplex.cyclesMap φ).hom c) =
      φ.τ₂.hom (S₁.iCycles.hom c) := fun c =>
    congrArg (fun f => f.hom c) (ShortComplex.cyclesMap_i φ)
  have hgi : ∀ (S : ShortComplex (ModuleCat.{u} R)) (c : S.cycles), S.g.hom (S.iCycles.hom c) = 0 :=
    fun S c => congrArg (fun f => f.hom c) S.iCycles_g
  have hπs : ∀ (S : ShortComplex (ModuleCat.{u} R)), Function.Surjective S.homologyπ.hom :=
    fun S => (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance
  have hiinj : ∀ (S : ShortComplex (ModuleCat.{u} R)), Function.Injective S.iCycles.hom :=
    fun S => (ModuleCat.mono_iff_injective S.iCycles).1 inferInstance
  refine ⟨(ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩⟩
  · change Function.Injective (ShortComplex.homologyMap φ).hom
    rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ := hπs S₁ h
    rw [hnat, homologyπ_eq_zero_iff_moduleCat, hci] at hh
    obtain ⟨z, hz⟩ := hh
    obtain ⟨w, hw⟩ := hinj _ (hgi S₁ c) z hz.symm
    exact (homologyπ_eq_zero_iff_moduleCat S₁ c).2 ⟨w, hw⟩
  · change Function.Surjective (ShortComplex.homologyMap φ).hom
    intro h
    obtain ⟨c, rfl⟩ := hπs S₂ h
    obtain ⟨x, hx, z, hxz⟩ := hsurj _ (hgi S₂ c)
    obtain ⟨c₁, hc₁⟩ := exists_cycle_moduleCat S₁ x hx
    refine ⟨S₁.homologyπ.hom c₁, ?_⟩
    rw [hnat, ← sub_eq_zero, ← map_sub, homologyπ_eq_zero_iff_moduleCat, map_sub, hci, hc₁, hxz]
    exact ⟨z, by abel⟩

/-- **Elementwise criterion for `QuasiIsoAt`.** -/
theorem quasiIsoAt_of_elem {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k)
    (hsurj : ∀ y, (L.d j k).hom y = 0 → ∃ x, (K.d j k).hom x = 0 ∧
      ∃ z, (φ.f j).hom x = y + (L.d i j).hom z)
    (hinj : ∀ x, (K.d j k).hom x = 0 → ∀ z, (φ.f j).hom x = (L.d i j).hom z →
      ∃ w, (K.d i j).hom w = x) :
    QuasiIsoAt φ j := by
  subst hi hk
  rw [quasiIsoAt_iff]
  exact sc_quasiIso_of_elem _ hsurj hinj

end ZInQ.Contrib.CloudB3RC53.TameModel

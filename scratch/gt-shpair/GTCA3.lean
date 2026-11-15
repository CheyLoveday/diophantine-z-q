import GTCA2

/-!
# gt-shpair, part E: separable residue fields, and strict henselizations along a finite extension
(any characteristic, any residue field)
-/

open IsLocalRing Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GTSHPair

open ReductSplit ReductGlue

section ResSep

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]

/-- **Elements of the inertia field have separable residues** (from `key_finite`, part (b)). -/
theorem sep_poly (hw : w.comap (algebraMap K Ω) = O) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) :
    ∃ f : O[X], (f.map (residue O)).Separable ∧
      (f.map ((algebraMap K Ω).comp O.subtype)).eval x ∈ w.nonunits := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  obtain ⟨f, hf, hfx⟩ := (key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw).2
  refine ⟨f, hf, ?_⟩
  rw [nonunits_comap] at hfx
  convert hfx using 1
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  rfl

/-- **The residue extension of the inertia field is separable.** -/
theorem res_isSeparable (hw : w.comap (algebraMap K Ω) = O) :
    letI := (resMap (hE_eq w hw)).toAlgebra
    Algebra.IsSeparable (ResidueField O) (ResidueField (wE (K := K) w)) := by
  letI := (resMap (hE_eq w hw)).toAlgebra
  constructor
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r
  obtain ⟨f, hf, hfx⟩ := sep_poly w hw (ιΩ w a) a.1.2 a.2
  have h0 : aeval (residue _ a) (f.map (residue O)) = 0 := by
    rw [aeval_def, eval₂_map]
    have e1 : (algebraMap (ResidueField O) (ResidueField (wE (K := K) w))).comp (residue O) =
        (residue _).comp (comapHom (hE_eq w hw)) := by
      ext b; exact resMap_residue (hE_eq w hw) b
    rw [e1, ← hom_eval₂, residue_eq_zero_iff, mem_max_comap_iff]
    convert hfx using 1
    rw [Polynomial.eval_map]
    change ιΩ w _ = _
    rw [hom_eval₂]
    rfl
  exact hf.of_dvd (minpoly.dvd _ _ h0)

/-- The inertia field is separable over `K`. -/
theorem inertiaField_isSeparable : Algebra.IsSeparable K (inertiaField (K := K) w) :=
  isSeparable_of_forall _ (fun x hx => by
    obtain ⟨M, hM, hxM, -⟩ := hx
    exact hM.isSeparable hxM)

end ResSep

end GTSHPair

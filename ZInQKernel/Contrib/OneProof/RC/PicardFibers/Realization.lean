import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Representatives

/-! Tex 9155–9156: only a placewise witness is needed to realize a tuple
on the actual weighted support. The finite patch is on-the-spot (c). -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler Adelic O7Actual O7Orbits

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- Read the level bit from any affine generator in the completed order. -/
def levelBit (s : StageAt O N M hN m) (j : Fin N.primeFactors.card)
    (X : (ActualOrder s).completion (levelPrime N j).val) : Bool :=
  let p := levelPrime N j
  let r := LocalWeights.level p.val (N.factorization p.val)
    (splitOrderChart s p (levelPrime_ne_detecting s j) X)
  residueBit r (1 - r)

/-- Read the division bit from twice the affine generator minus one. -/
def divisionBit (s : StageAt O N M hN m) (X : (ActualOrder s).completion s.ell) : Bool :=
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  let r := LocalDivision.red (divisionOrderChart s (2 * X - 1))
  residueBit r (-r)

private def moveLocalGenerator (s : StageAt O N M hN m) {p q : Prime} (h : p = q)
    (X : (ActualOrder s).completion p.val) : (ActualOrder s).completion q.val := by
  subst q
  exact X

/-- At a prime that indexes a coordinate, require the prescribed bit.
Away from these primes only integrality is required. -/
def LabelAt (s : StageAt O N M hN m) (t : Orientations N.primeFactors.card)
    (p : Prime) (X : (ActualOrder s).completion p.val) : Prop :=
  (∀ j : Fin N.primeFactors.card, ∀ h : p = levelPrime N j,
    levelBit s j (moveLocalGenerator s (p := p) (q := levelPrime N j) h X) = t j.castSucc) ∧
  (∀ h : p = (⟨s.ell, Fact.out⟩ : Prime),
    divisionBit s (moveLocalGenerator s (p := p) (q := ⟨s.ell, Fact.out⟩) h X) =
      t (Fin.last N.primeFactors.card))

/-- The open local realization statement. It asks only for conjugating
units in one local algebra at a time, with its prescribed residue bit. -/
def HasLocalRealizations (s : StageAt O N M hN m)
    (α : B (-1) (-(s.ell : ℚ))) (t : Orientations N.primeFactors.card) : Prop :=
  ∀ p : Prime, ∃ u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ,
    ∃ h : unitConjRing u⁻¹ (toLocal p.val α) ∈ (ActualOrder s).completion p.val,
      LabelAt s t p ⟨_, h⟩

private theorem labelAt_conj {A C : Type*} [Ring A] [CommRing C] (f : A →+* C)
    (u : Aˣ) (X : A) : f (unitConjRing u X) = f X := by
  rw [unitConjRing_apply, map_mul, map_mul, mul_comm (f (u : A)), mul_assoc,
    ← map_mul, Units.mul_inv, map_one, mul_one]

private theorem levelBit_conj (s : StageAt O N M hN m) (j : Fin N.primeFactors.card)
    (u : ((ActualOrder s).completion (levelPrime N j).val)ˣ)
    (X : (ActualOrder s).completion (levelPrime N j).val) :
    levelBit s j (unitConjRing u X) = levelBit s j X := by
  let p := levelPrime N j
  let f := (LocalWeights.level p.val (N.factorization p.val)).comp
    (splitOrderChart s p (levelPrime_ne_detecting s j)).toRingHom
  change residueBit (f (unitConjRing u X)) (1 - f (unitConjRing u X)) =
    residueBit (f X) (1 - f X)
  rw [labelAt_conj]

private theorem divisionBit_conj (s : StageAt O N M hN m) (u : ((ActualOrder s).completion s.ell)ˣ)
    (X : (ActualOrder s).completion s.ell) :
    divisionBit s (unitConjRing u X) = divisionBit s X := by
  let : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  let f := (LocalDivision.red (p := s.ell)).comp (divisionOrderChart s).toRingHom
  change residueBit (f (2 * unitConjRing u X - 1)) (-f (2 * unitConjRing u X - 1)) =
    residueBit (f (2 * X - 1)) (-f (2 * X - 1))
  have h : 2 * unitConjRing u X - 1 = unitConjRing u (2 * X - 1) := by
    rw [map_sub, map_mul, map_one, map_ofNat]
  rw [h, labelAt_conj]

private theorem chosen_generator (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0) (hn : Visibility.nrd x₀ = index s D)
    {z : FiniteUnits (ActualOrder s)} (hz : AdelicAdmissible α z)
    {c : ClassSet (ActualOrder s)} (g : (B (-1) (-(s.ell : ℚ)))ˣ)
    (r : integralUnits (ActualOrder s))
    (hf : classRepresentative c = diagonal (ActualOrder s) g * z * r.val) (p : Prime) :
    ∃ u : ((ActualOrder s).completion p.val)ˣ,
      localGenerator s H c (supportFromFrame s H hα hx hn hz g r hf) p =
        unitConjRing u ⟨_, hz p⟩ := by
  let r' : ((ActualOrder s).completion p.val)ˣ :=
    ⟨⟨(r.val.val p).val, (r.prop p).1⟩, ⟨(r.val.val p).inv, (r.prop p).2⟩,
      Subtype.ext (r.val.val p).val_inv, Subtype.ext (r.val.val p).inv_val⟩
  refine ⟨r'⁻¹, Subtype.ext ?_⟩
  let X := localGenerator s H c (supportFromFrame s H hα hx hn hz g r hf) p
  have hr : 2 * X.val - 1 =
    unitConjRing (r.val.val p)⁻¹ (unitConjRing (z.val p)⁻¹ (toLocal p.val x₀)) := by
    rw [localGenerator_spec, hf]
    change unitConjRing ((Units.map (toLocal p.val).toMonoidHom g * z.val p * r.val.val p)⁻¹)
      (toLocal p.val (unitConjRing g x₀)) = _
    rw [unitConjRing_map, unitConjRing_mul, unitConjRing_mul]
    congr 1
    group
  rw [← hα] at hr
  simp only [map_sub, map_mul, map_ofNat, map_one] at hr
  have htwo : IsUnit (2 : Bp p.val (-1) (-(s.ell : ℚ))) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ_[p.val]) ≠ 0)).map
        (algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))))
  exact htwo.mul_left_cancel (sub_left_inj.mp hr)

/-- Placewise witnesses patch to an admissible representative with exactly
the stated orientation on the actual support orbits. -/
theorem realize_tuple (s : StageAt O N M hN m) {D : ℤ}
    (_A : AdmissibleD s D) (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0) (hn : Visibility.nrd x₀ = index s D)
    (t : Orientations N.primeFactors.card) (h : HasLocalRealizations s α t) :
    ∃ z : {z : FiniteUnits (ActualOrder s) // AdelicAdmissible α z},
      orientation s H (orbitFromRep s H hα hx hn z) = t := by
  classical
  let p₀ : Prime := ⟨s.ell, Fact.out⟩
  let S : Finset Prime := insert p₀ (Finset.univ.image (levelPrime N))
  let P (p : Prime) (u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ) :=
    ∃ hu : unitConjRing u⁻¹ (toLocal p.val α) ∈ (ActualOrder s).completion p.val,
      LabelAt s t p ⟨_, hu⟩
  obtain ⟨z, hz, hlabel⟩ := patch_admissible_adele (ActualOrder s) α S P (by
    intro p
    obtain ⟨u, hu, ht⟩ := h p
    exact ⟨u, hu, fun _ => ⟨hu, ht⟩⟩)
  refine ⟨⟨z, hz⟩, ?_⟩
  let g := (exists_frame z).choose
  let r := (exists_frame z).choose_spec.choose
  let hf := (exists_frame z).choose_spec.choose_spec
  let x := supportFromFrame s H hα hx hn hz g r hf
  change generatorOrientation s H (adelicClass z) x = t
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · obtain ⟨hu, hb⟩ := hlabel p₀ (Finset.mem_insert_self ..)
    obtain ⟨u, he⟩ := chosen_generator s H hα hx hn hz g r hf p₀
    simp only [generatorOrientation, Fin.lastCases_last]
    change divisionBit s (localGenerator s H (adelicClass z) x p₀) = t (Fin.last _)
    rw [he, divisionBit_conj]
    exact hb.2 rfl
  · let p := levelPrime N j
    obtain ⟨hu, hb⟩ := hlabel p (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    obtain ⟨u, he⟩ := chosen_generator s H hα hx hn hz g r hf p
    simp only [generatorOrientation, Fin.lastCases_castSucc]
    change levelBit s j (localGenerator s H (adelicClass z) x p) = t j.castSucc
    rw [he, levelBit_conj]
    exact hb.1 j rfl

end ZInQ.Manuscript.RC.PicardFibers

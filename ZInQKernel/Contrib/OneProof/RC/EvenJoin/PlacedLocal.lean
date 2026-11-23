import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedBudget
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSourceAttachment
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerColumns

/-! The coefficient-one comparison on the actual cuspidal inventory,
with one local factor per normalized source (tex 9754–9861). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2
open IsDedekindDomain ModularForm NumberField O12 O12Local PrintsArith Symbols ThetaCoeff Wiring
open UpperHalfPlane ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1500000

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)] [NeZero (conductor W.S)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)
variable (hIndependent : OldNewIndependenceWeightTwo)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (H : D.sourceAttachments (hS := hS) hIndependent)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

local notation "T₀" => evenTypes W.S hS.1
local notation "K₀" => FixedField D.w
local notation "Columns" => ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P)))
local notation "Sources" => ↥(cuspSources (distinctCuspColumns A (evenBlockLevel_dvd (P := P))))
local notation "Y" => D.inventory T₀ hIndependent
local notation "M" => D.model hU C₀ hκ hIndependent hB hJ hodd H horder htwo
local notation "a₀" => fun s => ((Y).source s).a

variable {p : ℕ} (hpU : p ∈ U)

/-- The missing local model on each ramified source, with its computed
new-line scalar compared to the actual source's coefficient at the tested
prime when the undilated column is retained. The coefficient field is the
one used for the attachment. -/
def PlacedCuspLists.RamifiedNewvectorAt (Q : LocalPair p) [Fact p.Prime] : Prop :=
  ∀ s : Sources, p ∣ (Y).sourceLevel s →
    ∃ R : RamifiedFactor K₀ Q (H s).ρ,
      (∃ x : Columns, (Y).origin x = s ∧ (Y).degree x = 1) →
        (Classical.choice R.line).eigenvalue = a₀ s p

/-- The other missing input consists of finite evaluations of the genuine
Whittaker functions of the retained dilation columns. -/
def PlacedCuspLists.DilationWhittakerAt (hp : p ≠ 0) : Prop :=
  Nonempty (WhittakerColumnValues hp (fun (x : Columns) n => (Y).expansion x n.val))

private def blockKind (b : EvenBlock U) : CuspidalKind :=
  match b with
  | none => .thetaB
  | some j => .unary j.val.primeFactors

omit [NeZero (conductor W.S)] in
private theorem source_occurs (s : Sources) :
    ∃ (b : EvenBlock U) (c : ↥(A b).columns),
      ((A b).liftColumn (evenBlockLevel_dvd (P := P) b) c).source = s.val := by
  obtain ⟨x, hx⟩ := cuspSource_exists _ s
  obtain ⟨b, c, he⟩ := (mem_distinctCuspColumns A (evenBlockLevel_dvd (P := P)) _).mp x.property
  exact ⟨b, c, (congrArg CuspDilation.source he).trans hx⟩

private def sourceKind (s : Sources) : CuspidalKind :=
  blockKind (source_occurs s).choose

include hU hpU hB hJ in
omit [NeZero (conductor W.S)] in
private theorem sourceKind_ramified_iff (s : Sources) :
    (sourceKind s).ramifiedAt p ↔ p ∣ s.val.level := by
  let b := (source_occurs s).choose
  obtain ⟨c, hc⟩ := (source_occurs s).choose_spec
  rw [← hc]
  have he : (sourceKind s).ramifiedAt p ↔ p ∈ evenBlockPrimes b := by
    change (blockKind b).ramifiedAt p ↔ p ∈ evenBlockPrimes b
    cases b with
    | none => exact iff_of_true trivial hpU
    | some j => rfl
  exact he.trans (tested_dvd_source_iff hU hpU hB hJ b c).symm

/-- The model's positive coefficient functional is the sum of the placed
dilations. -/
theorem PlacedCuspLists.model_coefficient_sum (B : ℕ) (n : PosIndex)
    (z : Columns → K₀) :
    (M B).1.coefK z ((M B).2.index n) = ∑ x : Columns, z x * (Y).expansion x n.val := by
  change ∑ x : Columns, z x * Odd.divCoeff
    ((D.evenBasis hU hIndependent).base x).a ((Y).degree x) n.val = _
  simp only [PlacedCuspLists.evenBasis, Inventory.toBasis, Inventory.baseAt_a, Inventory.expansion]

/-- The old operator used at coefficient one is the coefficient of the
original dilation in the classical two-term oldspace formula. Each
discarded term is a dilation divisible by the tested prime. -/
def PlacedCuspLists.placedCuspidalData (B : ℕ) (Q : LocalPair p) [Fact p.Prime]
    (hr : D.RamifiedNewvectorAt hIndependent H Q) :
    CuspidalData (M B).1 Q where
  Factor := Sources
  kind := sourceKind
  factor x := some ((Y).origin x)
  ρ s := (H s).ρ
  coordinate x s hs := congrArg (fun t => (H t).ρ) (Option.some.inj hs)
  ram s hs := (hr s ((sourceKind_ramified_iff hU hB hJ hpU s).mp hs)).choose
  primeTo s hs := by
    intro g hg
    exact (H s).unramified p
      ⟨hU p hpU, (Nat.Prime.coprime_iff_not_dvd (hU p hpU).1).mpr
        (fun h => hs ((sourceKind_ramified_iff hU hB hJ hpU s).mpr h))⟩
      Q.Q Q.maximal Q.above g hg
  oldUp := scalarOp (fun x => a₀ ((Y).origin x) p)

local notation "C" => D.placedCuspidalData hU C₀ hκ hIndependent hB hJ hodd H horder htwo hpU

variable (B : ℕ) (Q : LocalPair p) [Fact p.Prime]
variable (hr : D.RamifiedNewvectorAt hIndependent H Q)

theorem PlacedCuspLists.placedCuspidal_active :
    (C B Q hr).active = Set.univ := by
  ext x
  exact iff_of_true ⟨(Y).origin x, rfl⟩ trivial

set_option backward.isDefEq.respectTransparency false in
/-- On the columns visible at coefficient one, the operator is the
source's coefficient at the tested prime on both sectors. -/
theorem PlacedCuspLists.placedCuspidal_up (z : Columns → K₀) (x : Columns)
    (hd : (Y).degree x = 1) :
    (C B Q hr).up z x = a₀ ((Y).origin x) p * z x := by
  classical
  let S := C B Q hr
  let s := (Y).origin x
  have hxs : S.factor x = some s := rfl
  change S.up z x = _
  by_cases hs : (S.kind s).ramifiedAt p
  · rw [S.up_on_ramified ⟨s, hxs, hs⟩, S.diagonalEntry_eq hxs hs]
    exact congrArg (· * z x)
      ((hr s ((sourceKind_ramified_iff hU hB hJ hpU s).mp hs)).choose_spec ⟨x, rfl, hd⟩)
  · have hnr : x ∉ S.ramified := by
      rintro ⟨t, ht, hrt⟩
      have e : s = t := Option.some.inj (hxs.symm.trans ht)
      exact hs (e.symm ▸ hrt)
    have hxo : x ∈ S.oldCoordinates := ⟨⟨s, hxs⟩, hnr⟩
    have hzero : @Eq K₀ (S.diagonalEntry x) 0 := S.diagonalEntry_eq_zero hnr
    change HAdd.hAdd (α := K₀) (β := K₀) (γ := K₀)
      (HMul.hMul (α := K₀) (β := K₀) (γ := K₀) (S.diagonalEntry x) (z x))
      (mask S.oldCoordinates
        (scalarOp (fun y => a₀ ((Y).origin y) p) (mask S.oldCoordinates z)) x) = _
    simp only [hzero, zero_mul, zero_add, mask_apply, hxo, ite_true, scalarOp_apply]

include hU hB hJ hpU in
omit [NeZero (conductor W.S)] [Fact p.Prime] in
/-- At a tested prime away from the source level, the classical action on
the column has its good eigenvalue term and the extra prime dilation.
The latter has zero coefficient at one. -/
theorem PlacedCuspLists.old_dilation_recurrence (x : Columns)
    (hprimeTo : ¬ p ∣ (Y).sourceLevel ((Y).origin x)) :
    GoodRec ((Y).expansion x) (a₀ ((Y).origin x) p) (((Y).source ((Y).origin x)).χ p) p := by
  have hp := (hU p hpU).1
  have hgood : IntrinsicGood T₀ ((Y).sourceLevel ((Y).origin x)) p :=
    ⟨hU p hpU, (Nat.Prime.coprime_iff_not_dvd hp).mpr hprimeTo⟩
  exact (((Y).source ((Y).origin x)).goodRec hgood hp).degeneracy hp.pos ((Y).degree_pos x)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (tested_not_dvd_degree hU hpU hB hJ x)).symm

omit [NeZero (conductor W.S)] [Fact p.Prime] in
/-- On a genuine dilation column, the coefficient-one reading is the
first coefficient of Tau Ceti's classical upper-triangular Hecke sum. -/
theorem PlacedCuspLists.classical_up_at_one (x : Columns) (hp : p.Prime) :
    D.κ ((Y).expansion x p) =
      (qExpansion 1 (heckeSlashUpperTri 2 p x.val.form)).coeff 1 := by
  rw [qExpansion_coeff_heckeSlashUpperTri' 2 p
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) hp.pos, mul_one, x.val.coeff_form]
  exact cuspInventory_coeff _ _ _ _ hIndependent x p

omit [NeZero (conductor W.S)] in
private theorem placed_source_normalized (s : Sources) : a₀ s 1 = 1 := by
  apply D.κ.injective
  rw [map_one]
  change D.κ ((s.val.eigen (T := T₀) D.κ _ _).a 1) = 1
  rw [NormalizedCuspSource.eigen_a]
  let : NeZero s.val.level := ⟨s.val.level_ne⟩
  exact s.val.newform.isNorm

set_option backward.isDefEq.respectTransparency false in
/-- The constructed operator gives exactly the coefficient-one reading of
the classical bad-prime operator. The ramified coefficient comes from
the computed Galois/Hecke line. -/
theorem PlacedCuspLists.placedCuspidal_at_one (z : Columns → K₀) :
    ∑ x : Columns, HMul.hMul (α := K₀) (β := K₀) (γ := K₀)
      ((C B Q hr).up z x) ((Y).expansion x 1) =
      ∑ x : Columns, z x * (Y).expansion x p := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hd : (Y).degree x = 1
  · rw [D.placedCuspidal_up hU C₀ hκ hIndependent hB hJ hodd H horder htwo hpU B Q hr z x hd,
      mul_comm (a₀ ((Y).origin x) p) (z x), mul_assoc]
    congr 1
    by_cases hx : p ∣ (Y).sourceLevel ((Y).origin x)
    · simp [Inventory.expansion, Odd.divCoeff, hd, placed_source_normalized D hIndependent]
    · have hp1 : ¬ p ∣ 1 := fun h => (hU p hpU).1.ne_one (Nat.dvd_one.mp h)
      have he := D.old_dilation_recurrence hU hIndependent hB hJ hpU x hx 1
      simpa only [mul_one, Odd.divCoeff_of_not_dvd _ hp1, mul_zero, add_zero] using he
  · have hp := (hU p hpU).1
    have hdp : ¬ (Y).degree x ∣ p := fun h =>
      (Nat.dvd_prime hp).mp h |>.elim hd
        (fun e => tested_not_dvd_degree hU hpU hB hJ x
          (show p ∣ (Y).degree x by rw [e]))
    simp [Inventory.expansion, Odd.divCoeff, hd, hdp]

set_option backward.isDefEq.respectTransparency false in
/-- Combine the classical identity at coefficient one with finite
Whittaker values from the actual dilation columns. -/
def PlacedCuspLists.placedWhittaker (hw : D.DilationWhittakerAt hIndependent
    (hU p hpU).1.ne_zero) :
    WhittakerComparison p (hU p hpU).1.ne_zero
      {z | SupportedOn (C B Q hr).active z} (C B Q hr).up
      (fun n z => (M B).1.coefK z ((M B).2.index n)) := by
  have hActive : {z : Columns → K₀ | SupportedOn (C B Q hr).active z} = Set.univ := by
    rw [D.placedCuspidal_active hU C₀ hκ hIndependent hB hJ hodd H horder htwo hpU B Q hr]
    ext z
    simp [SupportedOn]
  erw [hActive, show (fun n z => (M B).1.coefK z ((M B).2.index n)) =
    (fun n z => ∑ x : Columns, z x * (Y).expansion x n.val) from
      funext fun n => funext fun z =>
        D.model_coefficient_sum hU C₀ hκ hIndependent hB hJ hodd H horder htwo B n z]
  exact hw.some.comparison (D.placedCuspidal_at_one hU C₀ hκ hIndependent hB hJ hodd H horder htwo
    hpU B Q hr)


/-- The two local supplier statements suffice on the constructed row. -/
theorem PlacedCuspLists.cuspidalLocalAt_of_comparisons (B : ℕ)
    (hR : ∀ q (hq : q ∈ U) (Q : LocalPair q),
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.RamifiedNewvectorAt hIndependent H Q)
    (hW : ∀ q (hq : q ∈ U), D.DilationWhittakerAt hIndependent (hU q hq).1.ne_zero) :
    CuspidalLocalAt (M B).2 U hU := by
  intro q hq Q
  let : Fact q.Prime := ⟨(hU q hq).1⟩
  let cusp := D.placedCuspidalData hU C₀ hκ hIndependent hB hJ hodd H horder htwo hq B Q
    (hR q hq Q)
  refine ⟨cusp, ?_, ⟨D.placedWhittaker hU C₀ hκ hIndependent hB hJ hodd H horder htwo hq B Q
    (hR q hq Q) (hW q hq)⟩⟩
  have h : cusp.active = Set.univ :=
    D.placedCuspidal_active hU C₀ hκ hIndependent hB hJ hodd H horder htwo hq B Q (hR q hq Q)
  simp [h, SupportedOn]

include hB hJ in
/-- Supply the joint consumer's row binder from the existing good Carayol
hypothesis and the ramified and Whittaker comparisons on its attachments. -/
theorem PlacedCuspLists.placedGaloisInput_of_carayol
    (j : C₀.K₀ →+* F) (hK : (FinitePlace.embedding v).comp j = C₀.eK)
    (hC : F.subtype.comp j = C₀.eC) (hCarayol : CarayolRefold.CarayolThmAFrob) (B : ℕ)
    (hR : ∀ q (hq : q ∈ U) (Q : LocalPair q),
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.RamifiedNewvectorAt hIndependent
        (D.attachmentsOfCarayol hIndependent htwo hCarayol) Q)
    (hW : ∀ q (hq : q ∈ U), D.DilationWhittakerAt hIndependent (hU q hq).1.ne_zero) :
    PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hIndependent B U hU := by
  let att : D.sourceAttachments (hS := hS) hIndependent :=
    D.attachmentsOfCarayol hIndependent htwo hCarayol
  refine ⟨A, hB, hJ, D, att, ?_⟩
  exact D.cuspidalLocalAt_of_comparisons hU C₀ (D.fieldMap_source C₀ j hK hC)
    hIndependent hB hJ hodd att horder htwo B hR hW

end ZInQ.Manuscript.RC.EvenJoin

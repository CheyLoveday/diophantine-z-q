import ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedNewvector

/-! Construct the placed ramified factor from the conductor-one local inputs
and a comparison on one ordered inducing pair (tex 9773–9840, 9855–9861). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2 Matrix
open IsDedekindDomain ModularForm NumberField O12 O12Local PrintsArith Symbols ThetaCoeff Wiring
open UpperHalfPlane ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option maxHeartbeats 1500000
set_option Elab.async false
set_option quotPrecheck false

section Local

variable {p : ℕ} [Fact p.Prime] {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem unramified_eq_of_uniformizer {μ ν : LocalCharacter p K}
    (hμ : charTrivialAt p μ 0) (hν : charTrivialAt p ν 0)
    (he : μ (uniformizer p) = ν (uniformizer p)) :
    μ = ν := by
  apply MonoidHom.ext
  intro u
  let n := Padic.valuation (u : ℚ_[p])
  let a := u * (uniformizer p) ^ (-n)
  have hnorm : ‖(a : ℚ_[p])‖ = 1 := by
    have hv : Padic.valuation (a : ℚ_[p]) = 0 := by
      simp only [a, Units.val_mul, Units.val_zpow_eq_zpow_val]
      rw [Padic.valuation_mul u.ne_zero (zpow_ne_zero _ (uniformizer p).ne_zero),
        Padic.valuation_zpow]
      change n + (-n) * Padic.valuation (p : ℚ_[p]) = 0
      simp
    rw [Padic.norm_eq_zpow_neg_valuation a.ne_zero, hv, neg_zero, zpow_zero]
  have ha : unitAtLevel p 0 a := ⟨hnorm, Or.inl rfl⟩
  have hfactor : u = a * (uniformizer p) ^ n := by
    rw [show a = u * (uniformizer p) ^ (-n) from rfl, mul_assoc,
      ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc
    μ u = μ a * μ (uniformizer p ^ n) := (congrArg μ hfactor).trans (map_mul μ _ _)
    _ = ν a * ν (uniformizer p ^ n) := by simp only [hμ a ha, hν a ha, map_zpow, he]
    _ = ν u := ((congrArg ν hfactor).trans (map_mul ν _ _)).symm

private theorem induced_central_eq {π : LocalAction p K V}
    {χ half μ₁ μ₂ : LocalCharacter p K} (M : InducedModel p π half μ₁ μ₂)
    (hc : centralAction p π χ) {v : V} (hv : M.realize v 1 = 1) :
    χ = μ₁ * μ₂ := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  have h := M.right_translate v 1 (upper u u 0)
  rw [hc, one_mul, ← mul_one (upper u u 0), M.covariance] at h
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul, hv, mul_one, div_self',
    map_one, Units.val_one, MonoidHom.mul_apply, Units.val_mul] using h

private theorem fixed_eq_zero_of_induced_eval {π : LocalAction p K V}
    {half μ₁ μ₂ : LocalCharacter p K} (M : InducedModel p π half μ₁ μ₂)
    (hhalf : charTrivialAt p half 0) (h₂ : charConductor p μ₂ 1)
    {v : V} (hv : v ∈ levelSpace p π 1) (he : M.realize v 1 = 0) : v = 0 := by
  apply M.injective
  rw [map_zero]
  funext g
  exact M.support_and_evaluation hhalf h₂ hv g (Or.inr he)

/-- At level one the inducing function of a fixed vector is determined by
its value at the identity. A nonzero fixed vector gives the whole line. -/
theorem induced_finrank_level_one {π : LocalAction p K V}
    {half μ₁ μ₂ : LocalCharacter p K} (M : InducedModel p π half μ₁ μ₂)
    (hhalf : charTrivialAt p half 0) (h₂ : charConductor p μ₂ 1)
    (hlev : hasLevel p π 1) : Module.finrank K (levelSpace p π 1) = 1 := by
  obtain ⟨v, hv, he⟩ := M.normalized_generator hhalf h₂ hlev
  let w : levelSpace p π 1 := ⟨v, hv⟩
  have hw : w ≠ 0 := by
    intro h
    have hz : v = 0 := congrArg Subtype.val h
    simp [hz] at he
  apply (finrank_eq_one_iff_of_nonzero' w hw).mpr
  intro x
  let c := M.realize x.val 1
  refine ⟨c, Subtype.ext ?_⟩
  change c • v = x.val
  have hx : x.val - c • v ∈ levelSpace p π 1 :=
    Submodule.sub_mem _ x.property (Submodule.smul_mem _ c hv)
  have hval : M.realize (x.val - c • v) 1 = 0 := by
    simp [he, c]
  exact (sub_eq_zero.mp (fixed_eq_zero_of_induced_eval M hhalf h₂ hx hval)).symm

/-- The action on the fixed line determines the uniformizer value of the
unramified inducing character. The center determines the second character. -/
theorem orderedInducingCharacters_unique {π : LocalAction p K V}
    {χ half μ₁ μ₂ ν₁ ν₂ : LocalCharacter p K}
    (hc : centralAction p π χ) (hhalf : charTrivialAt p half 0)
    (hhalf₀ : (p : K) * (half (uniformizer p) : K) ^ 2 = 1)
    (hlev : hasLevel p π 1)
    (hμ₁ : charConductor p μ₁ 0) (hμ₂ : charConductor p μ₂ 1)
    (hν₁ : charConductor p ν₁ 0) (hν₂ : charConductor p ν₂ 1)
    (M : InducedModel p π half μ₁ μ₂) (N : InducedModel p π half ν₁ ν₂) :
    μ₁ = ν₁ ∧ μ₂ = ν₂ := by
  obtain ⟨v, hv, hM⟩ := M.normalized_generator hhalf hμ₂ hlev
  obtain ⟨w, _, hN⟩ := N.normalized_generator hhalf hν₂ hlev
  have hval : N.realize v 1 ≠ 0 := by
    intro h
    have hz := fixed_eq_zero_of_induced_eval N hhalf hν₂ hv h
    simp [hz] at hM
  have hh := localHecke_on_line M hhalf₀ (induced_finrank_level_one M hhalf hμ₂ hlev)
    hv hM (localHecke_preserves hv)
  have h := congrArg (fun u => N.realize u 1) hh
  have hsum : N.realize (localHecke π v) 1 = heckeSum p (N.realize v) 1 := by
    simp [localHecke, heckeSum, N.right_translate]
  rw [hsum, heckeSum_at_one_normalized p ν₁ ν₂ half hhalf₀ _ (N.covariance v)] at h
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
  have he : ν₁ (uniformizer p) = μ₁ (uniformizer p) := Units.ext
    (mul_left_cancel₀ ((half (uniformizer p))⁻¹).ne_zero (mul_right_cancel₀ hval h))
  have hfirst := unramified_eq_of_uniformizer hμ₁.1 hν₁.1 he.symm
  have hrest := (induced_central_eq M hc hM).symm.trans (induced_central_eq N hc hN)
  rw [hfirst] at hrest
  refine ⟨hfirst, ?_⟩
  apply MonoidHom.ext
  intro u
  apply Units.ext
  exact mul_left_cancel₀ (ν₁ u).ne_zero (by
    simpa only [MonoidHom.mul_apply, Units.val_mul] using
      congrArg (fun c : LocalCharacter p K => (c u : K)) hrest)

/-- At conductor one an ordered normalized model and a Carayol comparison
for its inducing pair supply the local factor. The conductor is obtained
from the central character and the existing fixed vector. -/
def ramifiedFactorOfPrincipal {Q : LocalPair p} {ρ : GalQ →* GL (Fin 2) K}
    (π : LocalAction p K V) (χ half μ₁ μ₂ : LocalCharacter p K)
    (hc : centralAction p π χ) (hchar : charConductor p χ 1)
    (hhalf : charTrivialAt p half 0)
    (hhalf₀ : (p : K) * (half (uniformizer p) : K) ^ 2 = 1)
    (hlev : hasLevel p π 1) (hold : CasselmanOldspace p π 1)
    (hswap : PrincipalInterchange p π half)
    (h₁ : charConductor p μ₁ 0) (h₂ : charConductor p μ₂ 1)
    (M : InducedModel p π half μ₁ μ₂) (C : ReciprocityAt Q)
    (hquad : ∀ w : weilAt Q, (w : GalQ) ∈ Q.Q.inertia GalQ →
      (χ (C.toUnits w) : K) = if bitChar p (w : GalQ) = 1 then 1 else -1)
    (hcompare : CarayolPrincipal Q ρ C μ₁ μ₂ half) :
    RamifiedFactor K Q ρ := by
  have hprod : χ = μ₁ * μ₂ := by
    obtain ⟨v, -, hv⟩ := M.normalized_generator hhalf h₂ hlev
    exact induced_central_eq M hc hv
  refine {
    V := V
    π := π
    χ := χ
    halfMod := half
    half_units := hhalf
    half_uniformizer := hhalf₀
    central := hc
    level := 1
    level_le := le_rfl
    occurs := hlev
    char_one := hchar
    conductor := 1
    exact_conductor := ⟨hlev, fun n hn h => hchar.2 n hn (central_trivial_of_level p π χ hc h)⟩
    casselman := .principal μ₁ μ₂ 0 1 h₁ h₂ (by decide) hprod ⟨M⟩
    oldspace := hold
    interchange := hswap
    reciprocity := C
    quadratic := hquad
    carayol := ?_ }
  rintro ν₁ ν₂ hν₁ hν₂ ⟨N⟩
  obtain ⟨rfl, rfl⟩ := orderedInducingCharacters_unique hc hhalf hhalf₀ hlev h₁ h₂ hν₁ hν₂ M N
  exact ⟨hcompare⟩

/-- The chosen half-modulus is the positive square root of the norm
after the complex embedding, on every element of the local field's unit group. -/
theorem halfModulusOfRoot_complex (κ : K →+* ℂ) (r : Kˣ)
    (hr : κ (r : K) = (Real.sqrt (p : ℝ) : ℂ)) (u : ℚ_[p]ˣ) :
    κ (halfModulusOfRoot p r u : K) = (Real.sqrt ‖(u : ℚ_[p])‖ : ℂ) := by
  let n := -Padic.valuation (u : ℚ_[p])
  rw [show (halfModulusOfRoot p r u : K) = (r : K) ^ n from
    Units.val_zpow_eq_zpow_val _ _, map_zpow₀, hr, ← Complex.ofReal_zpow]
  congr 1
  symm
  apply (Real.sqrt_eq_iff_eq_sq (norm_nonneg _) (by positivity)).mpr
  rw [Padic.norm_eq_zpow_neg_valuation u.ne_zero]
  change (p : ℝ) ^ n = (Real.sqrt (p : ℝ) ^ n) ^ 2
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm n, _root_.zpow_mul, zpow_natCast,
    Real.sq_sqrt (Nat.cast_nonneg p)]

/-- GLUE (tex 9841–9856). A normalized Whittaker functional on the
chosen local vector, with its diagonal value at the tested prime.
The integral-unipotent invariance is the restriction of Whittaker
equivariance to the kernel of the additive character. -/
def NormalizedCuspSource.LocalWhittakerDiagonal (s : NormalizedCuspSource)
    (κ : K →+* ℂ) (π : LocalAction p K V) (v : V) : Prop :=
  ∃ ev : V →ₛₗ[κ] ℂ, ev v = 1 ∧
    (∀ (x : ℚ_[p]) (w : V), ‖x‖ ≤ 1 → ev (π (upper 1 1 x) w) = ev w) ∧
    ev (π (upper (uniformizer p) 1 0) v) = s.coeff p / (p : ℂ)

/-- The right translates in the manuscript have the same individual
reading as the diagonal, by integral-unipotent invariance. -/
theorem NormalizedCuspSource.localWhittakerTest_of_diagonal
    {Q : LocalPair p} {ρ : GalQ →* GL (Fin 2) K} (R : RamifiedFactor K Q ρ)
    (s : NormalizedCuspSource) (κ : K →+* ℂ) (v : R.V)
    (hv : v ∈ levelSpace p R.π 1) (h : s.LocalWhittakerDiagonal κ R.π v) :
    s.LocalWhittakerTest R κ := by
  let : NeZero s.level := ⟨s.level_ne⟩
  obtain ⟨ev, hone, hinv, hdiag⟩ := h
  refine ⟨v, ev, hv, hone, fun b => ?_⟩
  have he : O12Local.representative p b = upper 1 1 (b.val : ℚ_[p]) * upper (uniformizer p) 1 0 := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [O12Local.representative, upper, Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, map_mul]
  change ev (R.π (upper 1 1 (b.val : ℚ_[p])) (R.π (upper (uniformizer p) 1 0) v)) = _
  rw [hinv _ _ (IsUltrametricDist.norm_natCast_le_one _ _), hdiag,
    whittakerIntegral_eq (TauCeti.one_mem_strictPeriods_Gamma1_map s.level)]
  rfl

end Local

section Placed

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (hIndependent : OldNewIndependenceWeightTwo)
variable (H : D.sourceAttachments (hS := hS) hIndependent)
variable {p : ℕ} [Fact p.Prime] {Q : LocalPair p}

local notation "Columns" => ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P)))
local notation "Sources" => ↥(cuspSources (distinctCuspColumns A (evenBlockLevel_dvd (P := P))))
local notation "Y" => D.inventory (evenTypes W.S hS.1) hIndependent
local notation "K" => FixedField D.w

/-- Local data of the actual adelized newform at conductor one, before
comparison to an attached Galois representation. The fixed vector is
the one used in the classical Fourier comparison. -/
structure LocalPrincipalAction {E : Type} [Field E] (half : LocalCharacter p E) where
  V : Type
  [addV : AddCommGroup V]
  [modV : Module E V]
  π : LocalAction p E V
  χ : LocalCharacter p E
  v : V
  v_fixed : v ∈ levelSpace p π 1
  v_ne_zero : v ≠ 0
  central : centralAction p π χ
  μ₁ : LocalCharacter p E
  μ₂ : LocalCharacter p E
  unramified : charConductor p μ₁ 0
  ramified : charConductor p μ₂ 1
  induced : InducedModel p π half μ₁ μ₂
  oldspace : CasselmanOldspace p π 1
  interchange : PrincipalInterchange p π half

attribute [instance] LocalPrincipalAction.addV LocalPrincipalAction.modV

/-- GLUE (tex 9773–9811, 9825–9827, 9841–9861). Realize the local
action of the classical source. Compare the exact attached homomorphism
to its chosen principal-series pair, and read the Whittaker functional
on the newvector when its degree-one column is retained.

The manuscript cites Carayol, Ann. Sci. ENS 19 (1986), §§0.3–0.7,
Théorème A, pp. 409–411, and Casselman, Math. Ann. 201 (1973),
Theorem 1, pp. 302–306, the Corollary on p. 306 and Theorem 4, p. 313
(locators as the manuscript gives them, not checked against the page).
It stays GLUE rather than a printed-form leaf because `LocalPrincipalAction`
is a project interface: the tree has no genuine local representation of
a newform for those statements to be about. -/
def PlacedCuspLists.RamifiedPrincipalInputsAt (C : ReciprocityAt Q)
    (half : LocalCharacter p K) : Prop :=
  ∀ s : Sources, p ∣ (Y).sourceLevel s →
    ∃ J : LocalPrincipalAction half,
      SourceCentralCharacterAt D.κ s J.χ ∧
      Nonempty (CarayolPrincipal Q (H s).ρ C J.μ₁ J.μ₂ half) ∧
      ((∃ x : Columns, (Y).origin x = s ∧ (Y).degree x = 1) →
        s.val.LocalWhittakerDiagonal D.κ J.π J.v)

/-- The positive square root in the enlarged source field lifts to a
unit of the receiving completion with its specified complex embedding. -/
theorem PlacedCuspLists.exists_placed_local_root
    (hr : (Real.sqrt (p : ℝ) : ℂ) ∈ D.E) :
    ∃ r : Kˣ, (r : K) ^ 2 = (p : K) ∧ D.κ (r : K) = (Real.sqrt (p : ℝ) : ℂ) := by
  obtain ⟨r, hr⟩ := D.in_image hr
  have hs : r ^ 2 = (p : K) := D.κ.injective (by
    rw [map_pow, hr, map_natCast]
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p))
  have hn : r ≠ 0 := by
    intro h
    have := ((Nat.cast_ne_zero (R := K)).mpr (Fact.out : p.Prime).ne_zero)
    apply this
    simpa [h] using hs.symm
  exact ⟨Units.mk0 r hn, hs, hr⟩

variable (hU : ∀ q ∈ U, (evenTypes W.S hS.1).Good q)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)

include hU hB hJ in
/-- Assemble the inherited factor on the very same matrices. The tests
of the individual representatives follow from the diagonal normalization. -/
theorem PlacedCuspLists.ramifiedLocalModelAt_of_principalInputs
    (hpU : p ∈ U) (C : ReciprocityAt Q) (hC : ReciprocityAt.ResidueCyclotomic C)
    (r : Kˣ) (hr : (r : K) ^ 2 = (p : K))
    (h : D.RamifiedPrincipalInputsAt hIndependent H C (halfModulusOfRoot p r)) :
    D.RamifiedLocalModelAt hIndependent H Q := by
  intro s hs
  obtain ⟨J, hcentral, ⟨hcompare⟩, hW⟩ := h s hs
  have hχ := sourceCentralCharacter_of_tested hU hpU hB hJ D.κ s hs J.χ hcentral
  have hp₂ := (hU p hpU).ne_two
  let R := ramifiedFactorOfPrincipal J.π J.χ (halfModulusOfRoot p r) J.μ₁ J.μ₂ J.central
    (charConductor_of_localUnitResidue hp₂ J.χ hχ) (halfModulusOfRoot_units p r)
    (halfModulusOfRoot_uniformizer p r hr) ⟨J.v, J.v_fixed, J.v_ne_zero⟩ J.oldspace
    J.interchange J.unramified J.ramified J.induced C
    (reciprocity_quadratic_of_residue hp₂ C hC J.χ hχ) hcompare
  exact ⟨R, fun h₁ => s.val.localWhittakerTest_of_diagonal R D.κ J.v J.v_fixed (hW h₁)⟩

include hU hB hJ in
/-- Use the geometric reciprocity coordinates at the chosen absolute prime
and the positive square root in the enlarged row's field. -/
theorem PlacedCuspLists.ramifiedLocalModelAt_of_localWeil
    (hpU : p ∈ U) (hr : (Real.sqrt (p : ℝ) : ℂ) ∈ D.E)
    (h : ∀ r : Kˣ, D.κ (r : K) = (Real.sqrt (p : ℝ) : ℂ) →
      D.RamifiedPrincipalInputsAt hIndependent H (localWeilReciprocity Q) (halfModulusOfRoot p r)) :
    D.RamifiedLocalModelAt hIndependent H Q := by
  obtain ⟨r, hsq, he⟩ := D.exists_placed_local_root hr
  exact D.ramifiedLocalModelAt_of_principalInputs hIndependent H hU hB hJ hpU
    (localWeilReciprocity Q) (localWeilReciprocity_residue Q) r hsq (h r he)

variable [NeZero (conductor W.S)]
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

include hB hJ in
/-- The existing coefficient-one row construction on the Carayol
attachments, with the ramified inputs on the same source representations. -/
theorem PlacedCuspLists.placedGaloisInput_of_carayol_of_principalInputs
    (j : C₀.K₀ →+* F) (hK : (FinitePlace.embedding v).comp j = C₀.eK)
    (hC : F.subtype.comp j = C₀.eC) (hCarayol : CarayolRefold.CarayolThmAFrob) (B : ℕ)
    (hroot : ∀ q ∈ U, (Real.sqrt (q : ℝ) : ℂ) ∈ D.E)
    (hR : ∀ q (hq : q ∈ U) (Q : LocalPair q),
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      ∀ r : Kˣ, D.κ (r : K) = (Real.sqrt (q : ℝ) : ℂ) →
        D.RamifiedPrincipalInputsAt hIndependent
          (D.attachmentsOfCarayol hIndependent htwo hCarayol)
          (localWeilReciprocity Q) (halfModulusOfRoot q r)) :
    PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hIndependent B U hU :=
  D.placedGaloisInput_of_carayol_of_localModels hIndependent hU hB hJ C₀ hodd horder htwo
    j hK hC hCarayol B (fun q hq Q =>
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.ramifiedLocalModelAt_of_localWeil hIndependent
        (D.attachmentsOfCarayol hIndependent htwo hCarayol) hU hB hJ hq
        (hroot q hq) (hR q hq Q))

end Placed

end ZInQ.Manuscript.RC.EvenJoin

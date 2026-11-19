import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Arithmetic

/-!
# The full transported local residue pairing

The degree-zero/degree-two cup uses the same normalized local coordinate
as the other two components. Pullback scales this coordinate by the tame
inverse residue size and acts on its coefficient through Tate conjugation.
Consequently the zero/two coefficient is the negative of the two/zero
coefficient after the derivative congruences are retained. All three
components of the transported local pairing are proved together
(tex 2762–2767, 2798–2805, 4385–4451, 4860–4863, 5027–5043).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidueIdentity

open CategoryTheory Module Filter NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda crossPairing)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped Matrix PowerSeries.WithPiTopology

section ZeroTwoCup

variable {R G M N : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]
  (β : M →ₗ[R] M →ₗ[R] N)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. The actual zero/two cup is the coefficient
homomorphism determined by the degree-zero value, applied to the actual
two-cochain (tex 2762–2767, 4860–4863). -/
theorem contCup_zerotwo_eq
    (w : (contCochains R G M).X 0) (z : (contCochains R G M).X 2) :
    contCup β continuous_of_discreteTopology 0 2 2 rfl w z =
      coefficientMap (β (evalZero R M w)) 2 z := by
  apply contCochains_ext
  intro v
  change cupFun β 0 2 2 rfl (contFun w) (contFun z) v = _
  rw [cupFun_apply, headProd_zero, one_smul]
  have hzero : (fun j : Fin 0 => v (Fin.castLE (by omega) j)) = Fin.elim0 :=
    Subsingleton.elim _ _
  have htwo : (fun j : Fin 2 => v ⟨0 + j, by omega⟩) = v := by
    funext j
    congr 1
    exact Fin.ext (Nat.zero_add j.val)
  rw [hzero, htwo]
  rfl

/-- Kind: proved theorem. The actual zero/two cup is natural for the
normalized local degree-two coordinates on every actual two-cocycle
(tex 2762–2767, 4860–4863). -/
theorem contCup_zerotwo_coordinate
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (cN : (contCochains R G N).X 2 →ₗ[R] N)
    (hcM : LocalDegreeTwoCoordinate cM)
    (hkillN : ∀ a, cN (((contCochains R G N).d 1 2).hom a) = 0)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ g h, u (g * h) = u g + u h)
    (hκa : ∀ g h, κ (g * h) = κ g + κ h)
    (hM : ∀ (g : G) (m : M), g • m = m)
    (hN : ∀ (g : G) (m : N), g • m = m)
    (hnM : LocalDegreeTwoNormalized cM u κ)
    (hnN : LocalDegreeTwoNormalized cN u κ)
    (w : (contCochains R G M).X 0) (z : (contCochains R G M).X 2)
    (hz : ((contCochains R G M).d 2 3).hom z = 0) :
    cN (contCup β continuous_of_discreteTopology 0 2 2 rfl w z) =
      β (evalZero R M w) (cM z) := by
  rw [contCup_zerotwo_eq]
  exact coefficientMap_coordinate cM cN hcM hkillN u κ hu hκ hua hκa
    hM hN hnM hnN (β (evalZero R M w)) z hz

end ZeroTwoCup

section LocalTransport

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {n : ℕ} [NeZero n] [Algebra (ZMod n) R] (X : LocalArithmeticData R n)

/-- Kind: proved theorem. Actual local conjugation commutes with the
one/two differential (tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transport_d12 (a : (contCochains R X.G X.M).X 1) :
    X.transport 2 (((contCochains R X.G X.M).d 1 2).hom a) =
      ((contCochains R X.G X.M).d 1 2).hom (X.transport 1 a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) (X.transportMap.comm 1 2)
  exact h.symm

/-- Kind: proved theorem. Actual local conjugation preserves two-cocycles
(tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transport_cycle_two
    (z : (contCochains R X.G X.M).X 2)
    (hz : ((contCochains R X.G X.M).d 2 3).hom z = 0) :
    ((contCochains R X.G X.M).d 2 3).hom (X.transport 2 z) = 0 := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f z) (X.transportMap.comm 2 3)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero] at h
  exact h

/-- Kind: proved theorem. Pullback of the actual normalized fundamental
cup multiplies its coefficient by the tame inverse residue size and by
Tate conjugation (tex 2798–2805, 5027–5032). -/
theorem LocalArithmeticData.transport_fundamental (m : X.M) :
    X.transport 2 (characterProduct X.u X.κ X.continuousU X.continuousK m) =
      characterProduct X.u X.κ X.continuousU X.continuousK
        (X.tameScale • X.j m) := by
  apply contCochains_ext
  intro v
  change X.j ((X.u (X.θ (v 0)) * X.κ (X.θ (v 1))) • m) =
    (X.u (v 0) * X.κ (v 1)) • (X.tameScale • X.j m)
  rw [X.pullU, X.pullK, map_smul]
  module

/-- Kind: proved theorem. The normalized local degree-two coordinate
commutes with actual conjugation on every two-cocycle, including the tame
inverse residue-size multiplier (tex 2798–2805, 4860–4863, 5027–5032). -/
theorem LocalArithmeticData.transport_coordinate_two
    (z : (contCochains R X.G X.M).X 2)
    (hz : ((contCochains R X.G X.M).d 2 3).hom z = 0) :
    X.cM (X.transport 2 z) = X.tameScale • X.j (X.cM z) := by
  let z₀ := characterProduct X.u X.κ X.continuousU X.continuousK (X.cM z)
  have hz₀ : ((contCochains R X.G X.M).d 2 3).hom z₀ = 0 :=
    characterProduct_cycle X.u X.κ X.continuousU X.continuousK X.trivialM
      X.additiveU X.additiveK _
  have hc₀ : X.cM z₀ = X.cM z :=
    X.normalizedM _ _ (characterProduct_eval X.u X.κ X.continuousU X.continuousK _)
  have hcycle : ((contCochains R X.G X.M).d 2 3).hom (z - z₀) = 0 := by
    rw [map_sub, hz, hz₀, sub_self]
  have hzero : X.cM (z - z₀) = 0 := by rw [map_sub, hc₀, sub_self]
  obtain ⟨a, ha⟩ := X.coordinateM.2.1 (z - z₀) hcycle hzero
  have hvalue : X.cM (X.transport 2 (z - z₀)) = 0 := by
    rw [← ha, X.transport_d12]
    exact X.coordinateM.1 _
  have hfund : X.cM (X.transport 2 z₀) = X.tameScale • X.j (X.cM z) := by
    rw [X.transport_fundamental]
    exact X.normalizedM _ _
      (characterProduct_eval X.u X.κ X.continuousU X.continuousK _)
  rw [map_sub, map_sub, hfund] at hvalue
  exact sub_eq_zero.mp hvalue

/-- Kind: definition. The original trace of the actual transported
zero/two local cup (tex 2798–2805, 4860–4863). -/
def LocalArithmeticData.cup02 (x y : Fin 2 → R) : R :=
  X.τ (contCup X.β continuous_of_discreteTopology 0 2 2 rfl
    (X.localZero x) (X.transport 2 (X.localTwo y)))

/-- Kind: proved theorem. The zero/two component of the actual transported
local cup is the original trace/Weil normalization times the tame scale
and conjugated determinant pairing. No zero/two table is assumed
(tex 2798–2805, 4860–4863, 5027–5043). -/
theorem LocalArithmeticData.cup02_formula (x y : Fin 2 → R) :
    X.cup02 x y = (X.tameScale * X.ε) * determinantForm x (X.J *ᵥ y) := by
  have hz := X.transport_cycle_two (X.localTwo y) (X.localTwo_cycle y)
  have hcycle : ((contCochains R X.G X.N).d 2 3).hom
      (contCup X.β continuous_of_discreteTopology 0 2 2 rfl
        (X.localZero x) (X.transport 2 (X.localTwo y))) = 0 := by
    rw [contCup_zerotwo_eq, ← coefficientMap_d23 _ X.trivialM X.trivialN,
      hz, map_zero]
  unfold LocalArithmeticData.cup02
  rw [trace_cycle_formula X.τ X.trace_kills X.cN X.coordinateN X.eN X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialN X.normalizedN _ hcycle]
  rw [contCup_zerotwo_coordinate X.β X.cM X.cN X.coordinateM X.coordinateN.1 X.u X.κ
    X.continuousU X.continuousK X.additiveU X.additiveK X.trivialM X.trivialN
    X.normalizedM X.normalizedN _ _ hz, X.localZero_value,
    X.transport_coordinate_two _ (X.localTwo_cycle y), X.localTwo_value,
    map_smul, map_smul, X.scalarWeil_conj, X.eM.apply_symm_apply, X.eM.apply_symm_apply]
  simp only [smul_eq_mul]
  unfold LocalArithmeticData.ε
  ring

end LocalTransport

section RetainedZeroTwo

/-- Kind: local instance. The retained two-power exponent is nonzero
(tex 2723–2727, 4860–4863). -/
local instance fullExponent_neZero (i : ℕ) : NeZero (2 ^ i) :=
  ⟨pow_ne_zero i two_ne_zero⟩

/-- Kind: local instance. The finite coefficient stages carry their
original discrete topology (tex 2723–2727, 4385–4451). -/
local instance fullStage_topology (i : ℕ) : TopologicalSpace (StageA i) := ⊥

/-- Kind: local instance. The stage topology is discrete
(tex 2723–2727, 4385–4451). -/
local instance fullStage_discrete (i : ℕ) : DiscreteTopology (StageA i) := ⟨rfl⟩

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}
  {D : RetainedLimitPairingStages U C} (X : RetainedLocalArithmetic U C D)

/-- Kind: cochain realization input. The zero/two matrix lifts the
original transported zero/two cup on the same actual degree-zero and
degree-two representatives as the other retained components. It is not
an equality with a determinant table (tex 4385–4451, 4860–4863). -/
structure RetainedZeroTwo : Prop where
  /-- Kind: original cochain matrix-lift identification
  (tex 4385–4451, 4860–4863). -/
  realization02 : ∀ i, ∀ [NeZero i], ∀ a b : Fin 2,
    stageMap i (D.loc 0 2 i a b) = (X.stage i).cup02 (Pi.single a 1) (Pi.single b 1)

/-- Kind: proved theorem. The existing retained stage lift and the original
cochain trace transport supply the zero/two realization input. No
zero/two residue formula occurs as a hypothesis
(tex 4385–4451, 4860–4863). -/
theorem RetainedZeroTwo.of_splitStages
    (G Uc : ∀ i, GCx (StageA i))
    (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ιc i))
      (splitSelData (G i) (res i) (Uc i) (ιc i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (hlift : ∀ i, i ≠ 0 → ∀ a b,
      (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b)
    (htrace02 : ∀ i, ∀ [NeZero i], ∀ x y : Fin 2 → StageA i,
      tr i (0, (Q i).cupL.P 0 2 2 rfl x y) = (X.stage i).cup02 x y) :
    RetainedZeroTwo X := by
  refine ⟨?_⟩
  intro i _ a b
  have he := congrFun (congrFun (hlift i (NeZero.ne i) 0 2) a) b
  simp only [Matrix.map_apply] at he
  have hQ : stageLocMat (Q i) (tr i) 0 2 a b =
      tr i (0, (Q i).cupL.P 0 2 2 rfl (Pi.single a 1) (Pi.single b 1)) := rfl
  exact (he.trans hQ).trans (htrace02 i (Pi.single a 1) (Pi.single b 1))

/-- Kind: proved theorem. The actual zero/two stage cup supplies its
matrix from the same scalar lifts, with the tame scale included
(tex 4385–4451, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.stage_matrix02 (h02 : RetainedZeroTwo X)
    (i : ℕ) [NeZero i] :
    (D.loc 0 2 i).map (stageMap i) = cupMatrix20
      (stageMap i (X.s i * (X.ε i : Lambda))) (X.J.map (stageMap i)) := by
  ext a b
  rw [Matrix.map_apply, h02.realization02, (X.stage i).cup02_formula]
  change _ = crossForm (stageMap i (X.s i * (X.ε i : Lambda))) (X.J.map (stageMap i))
    (Pi.single a 1) (Pi.single b 1)
  rw [crossForm_apply, map_mul, ← X.s_lift i, ← X.ε_lift i, X.J_lift i]

/-- Kind: proved theorem. The zero/two local matrix survives the retained
inner limit and has the negative original trace/Weil normalization
(tex 4385–4451, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.matrix02_limit (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) :
    ulimMat U (D.loc 0 2) = cupMatrix20 (-(ulim U (fun i => (X.ε i : Lambda)))) X.J := by
  have hn : ∀ᶠ i in (U : Filter ℕ), i ≠ 0 := Eventually.filter_mono hU (by simp)
  have h : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      D.loc 0 2 i a b - cupMatrix20 (X.s i * (X.ε i : Lambda)) X.J a b ∈ stageIdeal i := by
    filter_upwards [hn] with i hi
    have : NeZero i := ⟨hi⟩
    intro a b
    rw [← ker_stageMap, RingHom.mem_ker, map_sub]
    have he := (X.stage_matrix02 h02 i).trans
      (map_cupMatrix20 (stageMap i) (X.s i * (X.ε i : Lambda)) X.J).symm
    have hv := congrFun (congrFun he a) b
    simp only [Matrix.map_apply] at hv
    rw [hv, sub_self]
  have he := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU h
  rw [ulim_cupMatrix20, ulim_mul, X.scale_limit hU, neg_one_mul] at he
  exact he

/-- Kind: definition. The zero/two normalization at the coefficient fibre
is the negative original local trace/Weil normalization
(tex 4860–4863, 5027–5043). -/
def RetainedLocalArithmetic.ε₀At (P : Ideal Lambda) [P.IsPrime] : ResAt P := -X.εAt P

/-- Kind: definition. The two/zero normalization at the coefficient fibre
is the original local trace/Weil normalization
(tex 4860–4863, 5027–5043). -/
def RetainedLocalArithmetic.ε₂At (P : Ideal Lambda) [P.IsPrime] : ResAt P := X.εAt P

/-- Kind: proved theorem. The zero/two normalization is nonzero because
the original retained scalar is a unit (tex 4385–4451, 5035–5038). -/
theorem RetainedLocalArithmetic.ε₀At_ne_zero (P : Ideal Lambda) [P.IsPrime] :
    X.ε₀At P ≠ 0 := neg_ne_zero.mpr (X.εAt_ne_zero P)

/-- Kind: proved theorem. The two/zero normalization is nonzero because
the original retained scalar is a unit (tex 4385–4451, 5035–5038). -/
theorem RetainedLocalArithmetic.ε₂At_ne_zero (P : Ideal Lambda) [P.IsPrime] :
    X.ε₂At P ≠ 0 := X.εAt_ne_zero P

/-- Kind: proved theorem. The actual zero/two and two/zero local cups give
the two corresponding transported residue components
(tex 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.residue02_20 (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime] :
    (localPairingOfMat (D.locK P)).b02 = crossPairing (X.ε₀At P) (X.JAt P) ∧
      (localPairingOfMat (D.locK P)).b20 = crossPairing (X.ε₂At P) (X.JAt P) := by
  have h0 : D.locK P 0 2 = cupMatrix20 (X.ε₀At P) (X.JAt P) := by
    change (ulimMat U (D.loc 0 2)).map (algebraMap Lambda (ResAt P)) = _
    rw [X.matrix02_limit h02 hU, map_cupMatrix20, map_neg]
    rfl
  have h2 : D.locK P 2 0 = cupMatrix20 (X.ε₂At P) (X.JAt P) := by
    change (ulimMat U (D.loc 2 0)).map (algebraMap Lambda (ResAt P)) = _
    rw [X.matrix20_limit hU, map_cupMatrix20]
    rfl
  constructor
  · refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    change x ⬝ᵥ (D.locK P 0 2 *ᵥ y) = _
    rw [h0]
    exact (bilin_eq_dot_coords (crossForm (X.ε₀At P) (X.JAt P))
      (LinearEquiv.refl (ResAt P) (Fin 2 → ResAt P))
      (LinearEquiv.refl (ResAt P) (Fin 2 → ResAt P)) x y).symm
  · refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [localPairing_b20_of_cupMatrix (D.locK P) (X.ε₂At P) (X.JAt P) h2]
    rfl

/-- Kind: proved theorem. The full retained residue pairing equals the
transported pairing, including its zero/two component and both adjoint
normalizations. The only added input identifies the matrix with the
original zero/two cochain cup, not its residue formula
(tex 4385–4451, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.hloc (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime] :
    localPairingOfMat (D.locK P) =
      transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (X.JAt P) := by
  obtain ⟨h0, h2⟩ := X.residue02_20 h02 hU P
  have h1 : (localPairingOfMat (D.locK P)).b11 =
      (transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (X.JAt P)).b11 := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    exact (X.residue_inputs hU P).1 x y
  cases hA : localPairingOfMat (D.locK P) with
  | mk a b c =>
    rw [hA] at h0 h1 h2
    change a = crossPairing (X.ε₀At P) (X.JAt P) at h0
    change b = (transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (X.JAt P)).b11 at h1
    change c = crossPairing (X.ε₂At P) (X.JAt P) at h2
    cases h0
    cases h1
    cases h2
    rfl

/-- Kind: proved theorem. The full residue identity has exactly the
coefficient conjugation of the height-one stage-step consumer
(tex 2798–2805, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.hloc_at_conj (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime]
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S) (W : WeierstrassCurve K)
    (hW : W.map (Cn.κ : K →+* K) = W) [W.IsElliptic]
    [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (hJ : X.JAt P = conjMatrix Cn W hW P) :
    localPairingOfMat (D.locK P) =
      transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (conjMatrix Cn W hW P) := by
  rw [← hJ]
  exact X.hloc h02 hU P

open scoped WeierstrassCurve

/-- Kind: proved theorem. The existing realized Tate-conjugation
dictionary supplies the full residue identity for rational curves
(tex 2798–2805, 3090–3096, 4860–4863, 5027–5043). -/
theorem RetainedLocalArithmetic.hloc_at_rational_curve (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime]
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (B : WeierstrassCurve ℚ) [B.IsElliptic]
    [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (B⁄K)]
    (Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S)
    (hW : (B⁄K).map (Cn.κ : K →+* K) = B⁄K)
    (hJ : X.J = (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda)) :
    localPairingOfMat (D.locK P) =
      transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (conjMatrix Cn (B⁄K) hW P) := by
  apply X.hloc_at_conj h02 hU P Cn (B⁄K) hW
  unfold RetainedLocalArithmetic.JAt
  rw [hJ, Matrix.map_map, conjMatrix_eq_conjMatrixK B Cn hW P]
  congr 1

end RetainedZeroTwo

end ZInQ.Contrib.RC53Assist.ResidueIdentity

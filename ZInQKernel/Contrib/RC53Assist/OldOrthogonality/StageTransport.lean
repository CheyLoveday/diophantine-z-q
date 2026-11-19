import ZInQKernel.Contrib.RC53Assist.OldOrthogonality.VerifiedOrthogonality

noncomputable section

namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.ConditionFunctor

set_option maxHeartbeats 800000
set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {A B A' B' : Type}
  [AddCommGroup A] [Module R A] [DistribMulAction (GKS K S) A] [SMulCommClass (GKS K S) R A]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul (GKS K S) A]
  [AddCommGroup B] [Module R B] [DistribMulAction (GKS K S) B] [SMulCommClass (GKS K S) R B]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul (GKS K S) B]
  [AddCommGroup A'] [Module R A'] [DistribMulAction (GKS K S) A'] [SMulCommClass (GKS K S) R A']
  [TopologicalSpace A'] [DiscreteTopology A'] [ContinuousSMul (GKS K S) A']
  [AddCommGroup B'] [Module R B'] [DistribMulAction (GKS K S) B'] [SMulCommClass (GKS K S) R B']
  [TopologicalSpace B'] [DiscreteTopology B'] [ContinuousSMul (GKS K S) B']
  {v : Places K S}

/-- Repack a local condition through a fixed local cochain isomorphism. -/
def repack (E : ComplexIso (locAt K S R A v) (locAt K S R A' v))
    (c : CondAt K S R A v) : CondAt K S R A' v := ⟨c.U, E.condition c.i⟩

/-- Complement transport at the level of local-condition records.
Keeping the records abstract avoids any concrete coefficient normalization. -/
theorem repack_complement {T T' : GCx R}
    (EA : ComplexIso (locAt K S R A v) (locAt K S R A' v))
    (EB : ComplexIso (locAt K S R B v) (locAt K S R B' v)) (ET : ComplexIso T T')
    (c : CondAt K S R A v) (d : CondAt K S R B v)
    (P : GPair (locAt K S R A v) (locAt K S R B v) T)
    (P' : GPair (locAt K S R A' v) (locAt K S R B' v) T')
    (J : LocalTruncIsotropy c.i d.i P)
    (tr : T'.X 2 →ₗ[R] R) (htr : ∀ z, tr (T'.d 1 2 rfl z) = 0)
    (hZero : ∀ a b : ℤ, a + b = 3 → Subsingleton (c.U.X a) ∨ Subsingleton (d.U.X b))
    (hJ : ∀ a b (hab : a + b = 3) (u : c.U.X a) (y : d.U.X b), J.h a b 2 hab u y = 0)
    (hPair : ∀ a b k (hab : a + b = k) (x : (locAt K S R A v).X a) (y : (locAt K S R B v).X b),
      ET.e k (P.P a b k hab x y) = P'.P a b k hab (EA.e a x) (EB.e b y))
    (hOld : QuasiIso (GHom.toCC (orthLocalMap c.i d.i P J (ET.pullTrace tr) (ET.pullTrace_kills tr htr))))
    (J' : LocalTruncIsotropy (repack EA c).i (repack EB d).i P') :
    QuasiIso (GHom.toCC (orthLocalMap (repack EA c).i (repack EB d).i P' J' tr htr)) := by
  apply localComplement_transport_zero EA EB ET c.i d.i P P' J J' tr htr hJ ?_ hPair hOld
  intro a b hab u y
  rcases hZero a b hab with hA | hB
  · have := hA
    rw [Subsingleton.elim u 0, LinearMap.map_zero₂]
  · have := hB
    rw [Subsingleton.elim y 0]
    exact (J'.h a b 2 hab u).map_zero

end ZInQ.Contrib.RC53Assist.OldOrthogonality.ConditionFunctor


namespace ZInQ.Contrib.RC53Assist.OldOrthogonality.ConcreteTransport

set_option maxHeartbeats 800000
set_option autoImplicit false

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy MilneLocalTateDualityKummerCharZero)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients
open ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport
open ZInQ.Contrib.RC53Assist.OldOrthogonality.StageOrthogonality
open ZInQ.Contrib.RC53Assist.OldOrthogonality.Truncations

section Eta

variable {R : Type} [CommRing R] {U U' C C' E : GCx R}
  {ι : GHom U C} {ι' : GHom U' C'} {P : GPair C C' E}

/-- Reconstructing the three fields of truncated isotropy gives the original datum. -/
theorem isotropy_eta (J : LocalTruncIsotropy ι ι' P) :
    (LocalTruncIsotropy.mk
      (fun a b c hab => J.h a b c hab)
      (fun a a₁ b b₁ hab ha hb u y => J.isotropy₂ a a₁ b b₁ hab ha hb u y)
      (fun a a₁ b b₁ c c₁ hab ha hb hc hge u y => J.isotropy₃ a a₁ b b₁ c c₁ hab ha hb hc hge u y)) = J := by
  cases J
  rfl

end Eta

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (hFull : FullTorsion K S₀ W (2 ^ i))
  (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) (hμ : HasRootsOfUnity K S (2 ^ i))
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (P : Set (HeightOneSpectrum (𝓞 K)))
  (hα : ∀ v ∈ P, IsLocallyQuadAt i α (quadChar s hs hs0) v)

/-- The old trace is the pullback through the normalized cyclotomic comparison. -/
def oldTrace
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (v : Places K S) :
    (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i :=
  (localSupportT hS i hμ₀ hμ v).pullTrace (trv v)

/-- Boundary vanishing is transported separately from the local-condition data. -/
theorem oldTrace_kills
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (v : Places K S) (z : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 1) :
    oldTrace hS i hμ₀ hμ trv v
      ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0 :=
  (localSupportT hS i hμ₀ hμ v).pullTrace_kills (trv v) (htrv v) z

/-- The degree-two trace isomorphism is transported before assembling comparisons. -/
theorem oldTrace_iso
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv2 : ∀ v, InducesIsoH2 (trv v)) (v : Places K S) :
    InducesIsoH2 (oldTrace hS i hμ₀ hμ trv v) :=
  (localSupportT hS i hμ₀ hμ v).pullTrace_induces (trv v) (htrv2 v)

/-- A named actual old isotropy datum, with no change of coefficient field. -/
def oldIsotropy
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (hM : MilneLocalTateDualityKummerCharZero) (v : Places K S) :
    LocalTruncIsotropy
      (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) :=
  actLIso hS W i s hs hs0 hFull P α hμ₀ hα
    (oldTrace hS i hμ₀ hμ trv) (oldTrace_kills hS i hμ₀ hμ trv htrv)
    hM (oldTrace_iso hS i hμ₀ hμ trv htrv2) v

/-- The named old datum has zero homotopy in total degree three. -/
theorem oldIsotropy_h_zero
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (hM : MilneLocalTateDualityKummerCharZero) (v : Places K S)
    (a b : ℤ) (hab : a + b = 3)
    (u : (actLCondA hS W i s hs hs0 hFull P α hα v).U.X a)
    (y : (actLCondB hS W i s hs hs0 hFull P α hα v).U.X b) :
    (oldIsotropy hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2 hM v).h a b 2 hab u y = 0 := rfl

/-- RC29's actual local complement with the named pulled-back trace and datum. -/
theorem oldComparison_quasiIso
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (v : Places K S) :
    QuasiIso (GHom.toCC (orthLocalMap
      (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)
      (oldIsotropy hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2 hM v)
      (oldTrace hS i hμ₀ hμ trv v) (oldTrace_kills hS i hμ₀ hμ trv htrv v))) :=
  actLPerf hS W i s hs hs0 hFull P α hμ₀ hα
    (oldTrace hS i hμ₀ hμ trv) (oldTrace_kills hS i hμ₀ hμ trv htrv)
    hM h524 h756 hK hSfin hS₀fin h2₀ (oldTrace_iso hS i hμ₀ hμ trv htrv2) v
    (oldIsotropy hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2 hM v)

open ZInQ.Contrib.RC53Assist.OldOrthogonality.ConditionFunctor

/-- In total degree three one of the two actual old condition terms vanishes. -/
theorem oldTerms_zero (v : Places K S) (a b : ℤ) (hab : a + b = 3) :
    Subsingleton ((actLCondA hS W i s hs hs0 hFull P α hα v).U.X a) ∨
      Subsingleton ((actLCondB hS W i s hs hs0 hFull P α hα v).U.X b) := by
  classical
  by_cases hv : v.1 ∈ S₀
  · by_cases hp : v.1 ∈ P
    · have hA : OrthConcentratedAt (actLCondA hS W i s hs hs0 hFull P α hα v) := by
        rw [actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hp]
        have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hp))
      have hB : OrthConcentratedAt (actLCondB hS W i s hs hs0 hFull P α hα v) := by
        rw [actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hp]
        have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
        exact orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
          (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hp)))
      by_cases ha : a = 0 ∨ a = 1
      · exact Or.inr (hB b (by omega) (by omega))
      · exact Or.inl (hA a (by omega) (by omega))
    · right
      rw [actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hp]
      exact inferInstanceAs (Subsingleton PUnit)
  · have hA : OrthConcentratedAt (actLCondA hS W i s hs hs0 hFull P α hα v) := by
      rw [actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv]
      exact orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i α) v hv
    have hB : OrthConcentratedAt (actLCondB hS W i s hs hs0 hFull P α hα v) := by
      rw [actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv]
      exact orth_urAt_vanishes hS (Acoef i) (Mcoef K S₀ W i (charInv α)) v hv
    by_cases ha : a = 0 ∨ a = 1
    · exact Or.inr (hB b (by omega) (by omega))
    · exact Or.inl (hA a (by omega) (by omega))

/-- First condition equality is proved at the record level. -/
theorem firstCondition_repack (v : Places K S) :
    transportedOldA hS W i α hFull s hs hs0 P hα v =
      repack (localSupportA hS W i α hFull v) (actLCondA hS W i s hs hs0 hFull P α hα v) := rfl

/-- Dual condition equality is proved at the record level. -/
theorem dualCondition_repack (v : Places K S) :
    transportedOldB hS W i α hFull s hs hs0 P hα v =
      repack (localSupportB hS W i α hFull v) (actLCondB hS W i s hs hs0 hFull P α hα v) := rfl

include hμ₀ in
/-- RC29's actual comparison transported through the local-condition functor. -/
theorem repackedComparison_quasiIso
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (v : Places K S)
    (J : LocalTruncIsotropy
      (repack (localSupportA hS W i α hFull v) (actLCondA hS W i s hs hs0 hFull P α hα v)).i
      (repack (localSupportB hS W i α hFull v) (actLCondB hS W i s hs hs0 hFull P α hα v)).i
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (repack (localSupportA hS W i α hFull v) (actLCondA hS W i s hs hs0 hFull P α hα v)).i
      (repack (localSupportB hS W i α hFull v) (actLCondB hS W i s hs hs0 hFull P α hα v)).i
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v) J (trv v) (htrv v))) :=
  repack_complement
    (localSupportA hS W i α hFull v) (localSupportB hS W i α hFull v) (localSupportT hS i hμ₀ hμ v)
    (actLCondA hS W i s hs hs0 hFull P α hα v) (actLCondB hS W i s hs hs0 hFull P α hα v)
    (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)
    (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v)
    (oldIsotropy hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2 hM v) (trv v) (htrv v)
    (oldTerms_zero hS W i α hFull s hs hs0 P hα v)
    (oldIsotropy_h_zero hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2 hM v)
    (localSupport_cup hS W i α hFull hμ₀ hμ v)
    (oldComparison_quasiIso hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2
      hM h524 h756 hK hSfin hS₀fin h2₀ v) J

include hμ₀ in
/-- The concrete local comparison in the exact stage consumer's representation. -/
theorem localComparison_exact
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (v : Places K S)
    (J : LocalTruncIsotropy
      (transportedOldA hS W i α hFull s hs hs0 P hα v).i
      (transportedOldB hS W i α hFull s hs hs0 P hα v).i
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v)) :
    QuasiIso (GHom.toCC (orthLocalMap
      (transportedOldA hS W i α hFull s hs hs0 P hα v).i
      (transportedOldB hS W i α hFull s hs hs0 P hα v).i
      (orthGaloisPair K (weilPairingData W i (characterAfterSupport hS i α) hμ)
        (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) v) J (trv v) (htrv v))) :=
  actLPerf_congr (weilPairingData W i (characterAfterSupport hS i α) hμ)
    (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
    (firstCondition_repack hS W i α hFull s hs hs0 P hα v)
    (dualCondition_repack hS W i α hFull s hs hs0 P hα v) (trv v) (htrv v)
    (repackedComparison_quasiIso hS W i α hFull hμ₀ hμ s hs hs0 P hα trv htrv htrv2
      hM h524 h756 hK hSfin hS₀fin h2₀ v) J

include hμ₀

/-- The local orthogonality hypothesis of the stage Selmer-duality theorem,
including the derivative places, with all old local comparisons supplied by
RC29 and all derivative comparisons proved from full local duality. -/
theorem stageOrthogonalComplementsT [Fintype (Places K S)]
    (Q : Finset (Places K S))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (I : GaloisTruncIsotropyData K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q))
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (tr : (galoisCompactTT K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1 (Acoef i) hμ)).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (Tate1 (Acoef i) hμ)).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (Tate1 (Acoef i) hμ)) (3 - 1)).mkQ z) = ∑ v, trv v (z v)) :
    OrthogonalComplementsT K (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I tr htr := by
  have := acoef_selfInjective i
  apply derivativeOverride_horth
    (weilPairingData W i (characterAfterSupport hS i α) hμ)
    (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α)) Q
    (transportedOldA hS W i α hFull s hs hs0 P hα)
    (transportedOldB hS W i α hFull s hs hs0 P hα) I trv htrv
    (fun v J => localComparison_exact hS W i α hFull hμ₀ hμ s hs hs0 P hα
      trv htrv htrv2 hM h524 h756 hK hSfin hS₀fin h2₀ v J) ?_ tr htr hsum
  intro v _
  have hFullS := fullTorsion_afterSupport hS W (2 ^ i) hFull
  exact h524 S 2 (Acoef i) (nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i)
    (Mcoef K S W i (characterAfterSupport hS i α))
    (Mcoef K S W i (charInv (characterAfterSupport hS i α))) (Tate1 (Acoef i) hμ)
    (weilPairingData W i (characterAfterSupport hS i α) hμ)
    (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
    (weilPairingM_bijective W hμ (Acoef i) (characterAfterSupport hS i α) hFullS)
    (weilPairingM_flip_bijective W hμ (Acoef i) (characterAfterSupport hS i α) hFullS)
    (isCyclotomicTwist_tate1 (Acoef i) hμ) v (trv v) (htrv v) (htrv2 v)

/-- The original stage Selmer-duality consumer with its local orthogonality
input supplied by the actual old conditions and the derivative truncations. -/
theorem stageSelmerDuality_oldConditions [Fintype (Places K S)]
    (Q : Finset (Places K S))
    (hM : MilneLocalTateDualityKummerCharZero) (h524 : NekovarProp524 K)
    (h543 : NekovarProp543T K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (I : GaloisTruncIsotropyData K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q))
    (trv : ∀ v : Places K S, (locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).X 2 →ₗ[Acoef i] Acoef i)
    (htrv : ∀ v z, trv v ((locAt K S (Acoef i) (Tate1 (Acoef i) hμ) v).d 1 2 rfl z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (tr : (galoisCompactTT K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (Tate1 (Acoef i) hμ)).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (Tate1 (Acoef i) hμ)).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (Tate1 (Acoef i) hμ)) (3 - 1)).mkQ z) = ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (weilPairingData W i (characterAfterSupport hS i α) hμ)
      (weilPairingM_smul W hμ (Acoef i) (characterAfterSupport hS i α))
      (actualStageA hS W i α hFull s hs hs0 P hα Q)
      (actualStageB hS W i α hFull s hs hs0 P hα Q) I) tr htr)) := by
  exact ZInQ.Contrib.RC53Assist.InnerLimitArith.stageSelmerDuality
    W i (characterAfterSupport hS i α) hμ h543 hK hSfin (fun v hv => hS (h2₀ v hv))
    (fullTorsion_afterSupport hS W (2 ^ i) hFull)
    (actualStageA hS W i α hFull s hs hs0 P hα Q)
    (actualStageB hS W i α hFull s hs hs0 P hα Q) I tr htr htr3
    (stageOrthogonalComplementsT hS W i α hFull hμ₀ hμ s hs hs0 P hα Q
      hM h524 h756 hK hSfin hS₀fin h2₀ I trv htrv htrv2 tr htr hsum)


end ZInQ.Contrib.RC53Assist.OldOrthogonality.ConcreteTransport

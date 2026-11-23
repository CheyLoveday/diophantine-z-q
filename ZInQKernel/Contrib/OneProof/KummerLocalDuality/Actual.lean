import ZInQKernel.Contrib.OneProof.KummerLocalDuality.TateCup
import ZInQKernel.Contrib.OneProof.KummerLocalDuality.TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup
import ZInQKernel.Contrib.RC53Assist.ResidualBounds.StageBounds

/-!
# The finite local perfectness input of `actLPerf`

The Kummer case uses finite local Tate duality for the actual cup pairing.
The finite trace on `localCx` and its degree-two isomorphism are supplied
separately. The Kummer annihilator, full/zero and unramified cases use the
same results as `actLPerf`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.Duality (MilneLocalTateDualityKummerCharZero LocalTruncIsotropy)
open ZInQ.Contrib.CloudB3RC53.ContBridge (contCohomologyLinearEquiv continuousSMul_of_discrete)
open ZInQ.Contrib.RC53Assist.ResidualBounds (natCx_homology_subsingleton_neg natPositiveHomologyIso)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (P : Set (HeightOneSpectrum (𝓞 K)))
  [NeZero i] [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)

variable (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
  (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)

private theorem acoefLocalHomology_range (v : Places K S)
    (α' : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α'] (n : ℤ) (hn : n < 0 ∨ 2 < n) :
    Subsingleton ((locAt K S (Acoef i) (MinS hS W i α') v).toCC.homology n) := by
  let M := ResMod (locMap K S v.1) (MinS hS W i α')
  rcases hn with hn | hn
  · exact natCx_homology_subsingleton_neg (contCochains (Acoef i) (Gloc K v.1) M) n hn
  · letI : Finite (NumberField.RingOfIntegers K ⧸ v.1.asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient v.1.ne_bot
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : ContinuousSMul (Acoef i) M := continuousSMul_of_discrete (Acoef i) M
    have hcd : TauCeti.CohomologicalDimensionLE 2 (Gloc K v.1) 2 :=
      (TauCeti.cohomologicalDimensionAt_le_iff 2 (Gloc K v.1) 2).mp
        (TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two
          (K := v.1.adicCompletion K) 2).le
    have ht : TauCeti.IsPPrimaryTorsion 2 M := (TauCeti.isPPrimaryTorsion_iff).2
      fun x => ⟨i, two_pow_smul_mcoef W i α' x⟩
    cases n with
    | negSucc n => omega
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast] at hn
      cases n with
      | zero => omega
      | succ n =>
        have hn' : 2 < n + 1 := by omega
        let A := TauCeti.ofDiscreteModule (Acoef i) (Gloc K v.1) M
        have hZ := hcd M ht (n + 1) hn'
        letI : Subsingleton (continuousCohomology (n + 1) A) :=
          (TauCeti.ContCohomology.subsingleton_continuousCohomology_ofDiscreteModule_iff A (n + 1)).mp hZ
        letI : Subsingleton ((contCochains (Acoef i) (Gloc K v.1) M).homology (n + 1)) :=
          (contCohomologyLinearEquiv (Acoef i) (Gloc K v.1) M (n + 1)).symm.injective.subsingleton
        exact (natPositiveHomologyIso (contCochains (Acoef i) (Gloc K v.1) M) n).toLinearEquiv.injective.subsingleton

include hFull in
/-- The local cup adjoint on full cochains for the actual finite modules.
This is the `hLD` argument of `orthPerPlace_of_localDuality` at a Kummer place. -/
theorem actualLocalCupAdjoint_quasiIso (v : Places K S)
    (tr : (locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((locAt K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 tr) :
    QuasiIso (GHom.toCC (adjHom
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) 2 tr htr)) := by
  letI := acoef_selfInjective i
  exact quasiIso_adjHom_of_cupPerfect_zero_two
    (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)
    tr htr (acoefLocalHomology_range hS W i v α) (acoefLocalHomology_range hS W i v (charInv α))
    (actualFiniteCupPerfect hS W i α hμ₀ hFull v tr htr h2)

open scoped Classical in
/-- The conclusion of `actLPerf` from finite Tate duality at the Kummer
places, the existing Kummer annihilator and unramified duality inputs,
and the supplied finite trace. -/
theorem actLPerf_of_finiteTate (hM : MilneLocalTateDualityKummerCharZero)
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K)
    (hSfin : S.Finite) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (v : Places K S)
    (J : LocalTruncIsotropy (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (actLCondA hS W i s hs hs0 hFull P α hα v).i
      (actLCondB hS W i s hs hs0 hFull P α hα v).i
      (orthGaloisPair K (actLBeta hS W i α hμ₀) (actLBeta_smul hS W i α hμ₀) v) J (trv v)
      (htrv v))) := by
  clear hSfin
  by_cases hv : v.1 ∈ S₀
  · by_cases hP : v.1 ∈ P
    · letI := acoef_selfInjective i
      haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
      refine actLPerf_congr _ _ (actLCondA_of_P hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_P hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v) (fun J₀ => ?_) J
      exact orthPerPlace_of_localDuality _ _
        (actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP))
        (actualKummerAtS hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP)))
        J₀ (trv v) (htrv v)
        (actualLocalCupAdjoint_quasiIso (hS := hS) (W := W) (i := i) (hFull := hFull)
          (α := α) (hμ₀ := hμ₀) v (trv v) (htrv v) (htrv2 v))
        (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hP)))
        (orth_kummerAt_concentrated v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
          (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP))))
        (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hP)))
        (orth_kummerAt_h01 v (localTwist W h v.1) (2 ^ i)
          (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
          (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv (hα v.1 hP))))
        (kummerPerPlace_annihilator hS W i s hs hs0 hFull v hμ₀ α (hα v.1 hP)
          (kummerExactAnn_kannPsi hS W i s hs hs0 hFull v hμ₀ hM) (trv v) (htrv v) (htrv2 v))
    · exact actLPerf_congr _ _ (actLCondA_of_notP hS W i s hs hs0 hFull P α hα hv hP)
        (actLCondB_of_notP hS W i s hs hs0 hFull P α hα hv hP) (trv v) (htrv v)
        (actLPerf_full_zero _ _ v (trv v) (htrv v)) J
  · exact actLPerf_congr _ _ (actLCondA_of_notS0 hS W i s hs hs0 hFull P α hα hv)
      (actLCondB_of_notS0 hS W i s hs hs0 hFull P α hα hv) (trv v) (htrv v)
      (fun J₀ => orthUr_quasiIso_of_print h756 hS 2 (nekovarFiniteSetting_acoef K hK S₀ hS₀fin h2₀ i)
        (weilPairingM (S := S₀) W hμ₀ (Acoef i) α) (weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α)
        (weilPairingM_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
        (weilPairingM_flip_bijective (S := S₀) W hμ₀ (Acoef i) α hFull)
        (isCyclotomicTwist_tate1 (Acoef i) hμ₀) v hv J₀ (trv v) (htrv v) (htrv2 v)) J

end ZInQ.Manuscript.RC.KummerMaps

import ZInQKernel.Contrib.CloudB3E2Norm.H20Frob
import ZInQKernel.Contrib.CloudB3E1RingClass.CSTBridge

/-!
# The Frobenius `σ` acts on the ring class field as the Artin element

Manuscript `diophantine_zq.tex`, tex 2931–2932 (`σ_q` a Frobenius at a prime above `q`, acting on
`H_d` as the Artin element).

`H20DictFields.field_iv` (and `hnorm_of_full_anchor`) take `σ ∈ G_{K,S}` whose restriction acts on
the ring class field `H_{O_d}` (Tau Ceti's, read in `K̄` through `Kˢ`, for CST's order
`conductorOrder K d`) as the Artin element of `𝔮`. Lane E1's `exists_frobeniusLift_locGal` (used
in `H20Frob.exists_sigma_frob`) produces `σ` with `ringClassRes σ = artinClass 𝔮` on E1's copy
`ringClassFieldOf` of `H_d` inside `K_S` (for E1's order `ringClassOrder d`). This file proves the
two descriptions agree:

* `coe_ringClassFieldOfEquiv_symm` (PROVED): E1's identification of `H_d ⊆ K_S` with Tau Ceti's
  ring class field is the inclusion on elements;
* `act_of_ringClassRes` (PROVED): if `ringClassRes σ = artinClass J`, then `σ` acts on `H_d` as
  `ringClassArtinEquiv (picClass J)`;
* **`hσ_field_iv`** (PROVED): the hypothesis `hσ` of `field_iv` for `σ` (through the restriction
  `G_{K,S} → G_{K,S₁}` to the point support), transported along
  `ringClassOrder_eq_conductorOrder`;
* **`exists_sigma_field_iv`** (PROVED): at a place `w` over `q` not over `d` with ideal `𝔮`, there
  is `σ = p_w(φ)`, `φ` an arithmetic Frobenius lift, with `infl(σ) = Frob_w` (the leaf's
  Frobenius, `H20Frob.eq_frobLift`) and satisfying the hypothesis of `field_iv` at `𝔮`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open ZInQ.Contrib.CloudB3RC53.CST (conductorOrder)
open ZInQ.Contrib.CloudB3E1RingClass
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

section Core

variable {S : Set (HeightOneSpectrum (𝓞 K))} (d : ℕ) (hd : d ≠ 0)
  (hdS : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- E1's identification of `H_d ⊆ K_S` with Tau Ceti's ring class field is the inclusion.
Kind: PROVED. -/
theorem coe_ringClassFieldOfEquiv_symm (w : ringClassField (ringClassOrder (K := K) d hd)) :
    (((ringClassFieldOfEquiv d hd S hdS).symm w : ringClassFieldOf d hd S hdS) :
      AlgebraicClosure K) = sepIncl K w := rfl

/-- **`σ` acts on `H_d` as the Artin element** when `ringClassRes σ = artinClass J`.
Kind: PROVED. -/
theorem act_of_ringClassRes (σ : GKS K S)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) d hd).conductorModulus)
    (hσ : ringClassRes d hd S hdS σ = artinClass d hd S hdS J)
    (z : ringClassField (ringClassOrder (K := K) d hd))
    (hz : sepIncl K z ∈ unramifiedOutside K S) :
    ((galS K S σ ⟨sepIncl K z, hz⟩ : KS K S) : AlgebraicClosure K) =
      sepIncl K (ringClassArtinEquiv (ringClassOrder (K := K) d hd)
        ((ringClassOrder (K := K) d hd).picClass J) z) := by
  set e := ringClassFieldOfEquiv d hd S hdS
  have hc : ((e.symm z : ringClassFieldOf d hd S hdS) : KS K S) = ⟨sepIncl K z, hz⟩ :=
    Subtype.ext (coe_ringClassFieldOfEquiv_symm d hd hdS z)
  have h1 : ((ringClassRes d hd S hdS σ (e.symm z) : ringClassFieldOf d hd S hdS) : KS K S) =
      galS K S σ ⟨sepIncl K z, hz⟩ := by
    rw [← hc]
    exact AlgEquiv.restrictNormal_commutes σ (ringClassFieldOf d hd S hdS) _
  rw [← h1, hσ]
  change (((AlgEquiv.autCongr e).symm (ringClassArtinEquiv (ringClassOrder (K := K) d hd)
    ((ringClassOrder (K := K) d hd).picClass J)) (e.symm z) : ringClassFieldOf d hd S hdS) :
      AlgebraicClosure K) = _
  rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  exact coe_ringClassFieldOfEquiv_symm d hd hdS _

end Core

section FieldIV

variable {S S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₁ ⊆ S) (d : ℕ) [NeZero d]
  (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₁)

include hS hSd in
/-- E1's support hypothesis for `S` from the one for `S₁ ⊆ S`. Kind: PROVED. -/
theorem hdS_of (v : HeightOneSpectrum (𝓞 K)) (hv : (d : 𝓞 K) ∈ v.asIdeal) : v ∈ S := hS (hSd v hv)

/-- **The hypothesis of `field_iv`** for `σ` with `ringClassRes σ = artinClass 𝔮` (PROVED): through
`G_{K,S} → G_{K,S₁}`, `σ` acts on the ring class field of `conductorOrder K d` (read in `K_{S₁}`) as
the Artin element of `𝔮`. -/
theorem hσ_field_iv (σ : GKS K S) (𝔮 : HeightOneSpectrum (𝓞 K))
    (h : 𝔮.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K d).conductorModulus)
    (J : integralIdealsPrimeTo (ringClassOrder (K := K) d (NeZero.ne d)).conductorModulus)
    (hJ : (J : Ideal (𝓞 K)) = 𝔮.asIdeal)
    (hσ : ringClassRes d (NeZero.ne d) S (hdS_of hS d hSd) σ =
      artinClass d (NeZero.ne d) S (hdS_of hS d hSd) J)
    (z : ringClassField (conductorOrder K d)) :
    ((galS K S₁ (inflMap K hS σ) ⟨sepIncl K z, sepIncl_mem d hSd z⟩ :
        unramifiedOutside K S₁) : AlgebraicClosure K) =
      sepIncl K (ringClassArtinEquiv (conductorOrder K d)
        ((conductorOrder K d).picClass ⟨𝔮.asIdeal, h⟩) z) := by
  have key : ∀ (O : TauCeti.GlobalNumberFields.NumberFieldOrder K)
      (hO : ringClassOrder (K := K) d (NeZero.ne d) = O)
      (h : 𝔮.asIdeal ∈ integralIdealsPrimeTo O.conductorModulus)
      (z : ringClassField O) (hz : sepIncl K z ∈ unramifiedOutside K S),
        ((galS K S σ ⟨sepIncl K z, hz⟩ : KS K S) : AlgebraicClosure K) =
          sepIncl K (ringClassArtinEquiv O (O.picClass ⟨𝔮.asIdeal, h⟩) z) := by
    intro O hO
    subst hO
    intro h z hz
    have hJ' : J = ⟨𝔮.asIdeal, h⟩ := Subtype.ext hJ
    rw [← hJ']
    exact act_of_ringClassRes d (NeZero.ne d) (hdS_of hS d hSd) σ J hσ z hz
  have hz : sepIncl K z ∈ unramifiedOutside K S :=
    ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside_mono K hS (sepIncl_mem d hSd z)
  rw [← key _ (ringClassOrder_eq_conductorOrder d) h z hz]
  have hk : ksIncl hS ⟨sepIncl K z, sepIncl_mem d hSd z⟩ = ⟨sepIncl K z, hz⟩ :=
    Subtype.ext (coe_ksIncl hS _)
  have h3 := ksIncl_infl hS σ ⟨sepIncl K z, sepIncl_mem d hSd z⟩
  rw [hk] at h3
  rw [← h3, coe_ksIncl]

end FieldIV

section Exists

variable {S₀ S S₁ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (d : ℕ)
  [NeZero d] (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₁)

/-- **The `σ` of the norm relation, for the dictionary and the leaf at once** (PROVED): at a new
place `w ∉ S₀` not over `d`, whose ideal is `𝔮` (prime to the conductor), there is `σ = p_w(φ)`
with `φ` an arithmetic Frobenius lift such that `infl(σ) = Frob_w` (`H20Frob.eq_frobLift`) and
`σ` satisfies the hypothesis of `field_iv` at `𝔮` (the two memberships `h`, `hJ` of `𝔮` among the
ideals prime to the conductor hold for `w` not over `d`; lane E1's `mem_primeTo_of_not_mem`). -/
theorem exists_sigma_field_iv (w : NewPlaces K S₀ S) (hwd : (d : 𝓞 K) ∉ w.1.asIdeal)
    (h : w.1.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K d).conductorModulus)
    (hJ : w.1.asIdeal ∈
      integralIdealsPrimeTo (ringClassOrder (K := K) d (NeZero.ne d)).conductorModulus) :
    ∃ φ : Gloc K w.1, TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ ∧
      inflMap K hS (locMap K S w.1 φ) = urFrobElt K w ∧
      ∀ z : ringClassField (conductorOrder K d),
        ((galS K S₁ (inflMap K h1 (locMap K S w.1 φ)) ⟨sepIncl K z, sepIncl_mem d hSd z⟩ :
            unramifiedOutside K S₁) : AlgebraicClosure K) =
          sepIncl K (ringClassArtinEquiv (conductorOrder K d)
            ((conductorOrder K d).picClass ⟨w.1.asIdeal, h⟩) z) := by
  obtain ⟨φ, hφ, hinf, hres⟩ := exists_sigma_frob hS d (NeZero.ne d) (hdS_of h1 d hSd) w hwd
    ⟨w.1.asIdeal, hJ⟩ rfl
  exact ⟨φ, hφ, hinf, hσ_field_iv h1 d hSd _ w.1 h ⟨w.1.asIdeal, hJ⟩ rfl hres⟩

end Exists

end ZInQ.Contrib.CloudB3E2.NormCochain

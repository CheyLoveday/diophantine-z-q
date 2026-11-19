import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompQIso
import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompBridge
import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCoefficient

/-!
# Theorem 5.3, Lane RC37: the concrete Kummer coefficient comparison

Manuscript `diophantine_zq.tex`, tex 4005–4014 (the universal-coefficient identification
`H¹(C_K) ⊗ ℚ₂/ℤ₂ ≅ Sel_{2^∞}(E/K)` of the calibration). The RC53 group's named input
`KummerCoefficientComparison ℓ k S hFull` asks for a quasi-isomorphism
`τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(Sel_{2^∞}(E_ℓ/K))`, `K = ℚ(√k)`. This file builds it.

* `kcArithLevelData k S E hFull`: the level datum of the embedding `K_S ⊂ ℚˢ` (the restriction
  `G_K → G_{K,S}` and the point maps `E(K_S)[2^m] → E(ℚˢ)[2^∞]`, all PROVED from the bridge
  `KummerCompBridge.lean`).
* `KcArithSelmerLevel k S E` (GLUE, faithful): **the Selmer group at level `2^m` through
  `G_{K,S}`** — for `K` totally complex (`k < 0`), `S` finite containing the primes above `2`,
  and `E[2^∞] ⊂ E(K_S)`, a continuous cocycle `f : G_{K,S} → E(K_S)[2^m]` inflates to a class of
  `Sel_{2^m}(E/K)` iff ... (`sel_of_loc`), and every class of `Sel_{2^m}(E/K)` is such an
  inflation (`loc_of_sel`). Classical (Silverman X.4.4, the Néron–Ogg–Shafarevich criterion and
  inflation–restriction); the content not in the tree is the description of classes unramified
  outside `S` as inflations from `G_{K,S}` (the named statement (b) of the comparison).
* `kcSelmerSupport_of_level`: PROVED, the passage to `Sel_{2^∞}` (`selmer_class_from_level`,
  `levelToInfinite_mem_selmer`).
* **`kcKummerCoefficientComparison`**: the inhabitant of `KummerCoefficientComparison ℓ k S hFull`
  for `k < 0`, `S` finite containing the primes above `2`, from `KcArithSelmerLevel`; and
  **`kcKummerCoefficientComparisonSigned`**, the same for `curve t`.

The real-quadratic case is excluded on purpose: for `k > 0` the target imposes local triviality at
the two real places, where `H¹(ℝ, E) = E(ℝ)/N(E(ℂ))` need not vanish, while `C_K` has local
conditions only at the finite places of `S`; the comparison is then not a quasi-isomorphism in
general.

Kinds: definitions, PROVED, and the named input `KcArithSelmerLevel` (GLUE).
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit ZInQ.Contrib.CloudB3RC53
open TauCeti TauCeti.ContCohomology

attribute [local instance] levTop continuousSMul_lev

section Arith

variable (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n))

/-- **The level datum of the embedding `K_S ⊂ ℚˢ`**: restriction `G_K → G_{K,S}` (surjective)
and the point maps `E(K_S)[2^m] → E(ℚˢ)[2^∞]` (injective, compatible, jointly surjective under
`E[2^∞] ⊂ E(K_S)`). Kind: definition (all fields PROVED). -/
def kcArithLevelData :
    KcLevelData S (E.baseChange (QuadraticField k)) (galK (sqrtK k)) (TwoPowerCoeff E) where
  ρ := kcGal k S
  J := kcLevInf k S E
  J_smul m g P := kcLevInf_smul k S E m g P
  J_compat m m' P P' h := Subtype.ext (by rw [coe_kcLevInf, coe_kcLevInf, h])
  J_inj m P h := by
    apply Subtype.ext
    apply kcPt_injective k S E
    have h1 : ((kcLevInf k S E m P : TwoPowerCoeff E) : E.PointCoeff) = 0 := by
      rw [h]
      rfl
    rw [coe_kcLevInf] at h1
    rw [h1]
    exact (map_zero (kcPt k S E)).symm
  J_surj x := by
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.1 x.2
    let t : E.TorsionCoeff (2 ^ n) := ⟨x.1, AddSubgroup.torsionBy.nsmul_iff.2 hn⟩
    refine ⟨n, (kcLevEquiv k S E n (hFull n)).symm t, ?_⟩
    apply Subtype.ext
    rw [coe_kcLevInf, ← coe_kcLev, ← kcLevEquiv_apply k S E n (hFull n),
      AddEquiv.apply_symm_apply]
  ρ_surj := kcGal_surjective k S

/-- The inflation along `kcArithLevelData` is the tree-bridge inflation `kcInflInf`.
Kind: PROVED. -/
theorem kcInflate_arith (m : ℕ) : kcInflate (kcArithLevelData k S E hFull) m = kcInflInf k S E m :=
  rfl

omit [E.IsElliptic] in
/-- Finite-level inflation preserves cocycles. Kind: PROVED. -/
theorem kcInfl_mem_ker {m : ℕ}
    {f : (contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1}
    (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0) :
    ((kcInfl k S E m).f 1).hom f ∈
      LinearMap.ker ((contCochains ℤ (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))).d 1 2).hom := by
  rw [LinearMap.mem_ker]
  have e := congrArg (fun g => g.hom f) ((kcInfl k S E m).comm 1 2)
  change ((contCochains ℤ (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))).d 1 2).hom
    (((kcInfl k S E m).f 1).hom f) = ((kcInfl k S E m).f 2).hom
      (((contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f) at e
  rw [e, hf, map_zero]

/-- **The named input (GLUE): `Sel_{2^m}(E/K)` through `G_{K,S}` and the places of `S`.** Under the
hypotheses of the classical description — `E` elliptic, `K = ℚ(√k)` totally complex (`k < 0`), `S` a
finite set of primes of `K` containing those above `2`, and `E[2^∞] ⊂ E(K_S)` (so `E` has good
reduction outside `S`, by Néron–Ogg–Shafarevich) — for a continuous cocycle `f : G_{K,S} →
E(K_S)[2^m]`:
* `sel_of_loc`: if `f` is locally trivial at every place of `S` (`KcLocTriv`: its restriction to
  `G_{K_v}` is a coboundary in `E(K̄_v)`), its inflation to `G_K = Gal(ℚˢ/K)` lies in
  `Sel_{2^m}(E/K)` (at `v ∉ S` the class is unramified at a prime of good reduction, hence locally
  trivial; at the complex places there is nothing to check);
* `loc_of_sel`: every class of `Sel_{2^m}(E/K)` is the inflation of such a cocycle (Silverman
  X.4.4: Selmer classes are unramified outside `S`; an unramified-outside-`S` class with values
  in `E[2^m] ⊂ E(K_S)` is inflated from `G_{K,S}` — the named statement (b): such a class
  restricts to zero on `ker(G_K → G_{K,S})` — and inflation–restriction; at `v ∈ S` local
  triviality is `KcLocTriv`).
The Selmer group is the tree's `selmerLevelK` (local triviality at every place of `K`), the
inflation the bridge's `kcInfl`. Kind: definition (input, GLUE). -/
structure KcArithSelmerLevel : Prop where
  sel_of_loc : E.IsElliptic → k < 0 → S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S) →
    (∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n)) →
    ∀ (m : ℕ) (f : (contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
      (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0),
      KcLocTriv (E.baseChange (QuadraticField k)) f →
        kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩ ∈
          selmerLevelK (sqrtK k) E m
  loc_of_sel : E.IsElliptic → k < 0 → S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S) →
    (∀ n : ℕ, FullTorsion (QuadraticField k) S (E.baseChange (QuadraticField k)) (2 ^ n)) →
    ∀ (m : ℕ) (c : H1 (galK (sqrtK k)) (E.TorsionCoeff (2 ^ m))),
      c ∈ selmerLevelK (sqrtK k) E m →
      ∃ (f : (contCochains ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
        (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
          (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0),
        KcLocTriv (E.baseChange (QuadraticField k)) f ∧
          kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩ = c

/-- **Finite to infinite level on inflated classes**: `E[2^m] → E[2^∞]` sends the class of the
level inflation to the class of the infinite inflation. Kind: PROVED. -/
theorem kc_levelToInfinite_kerToH1 (m : ℕ)
    (f : (contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).X 1)
    (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) m)).d 1 2).hom f = 0) :
    levelToInfinite (sqrtK k) E m
        (kerToH1 (k := ℤ) ⟨((kcInfl k S E m).f 1).hom f, kcInfl_mem_ker k S E hf⟩) =
      kerToH1 (k := ℤ) ⟨((kcInflate (kcArithLevelData k S E hFull) m).f 1).hom f,
        kcInflate_mem_ker (kcArithLevelData k S E hFull) hf⟩ := by
  rw [levelToInfinite, kerToH1_apply, kerToH1_apply]
  erw [explicitCoeff1_mk]

/-- **The input of the generic construction from the finite-level GLUE.** Kind: PROVED. -/
theorem kcSelmerSupport_of_level (hk : k < 0) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S)
    (G : KcArithSelmerLevel k S E) :
    KcSelmerSupport (kcArithLevelData k S E hFull) (selmerK (sqrtK k) E) where
  sel_of_loc m f hf hloc := by
    rw [← kc_levelToInfinite_kerToH1 k S E hFull m f hf]
    exact levelToInfinite_mem_selmer (sqrtK k) E
      (G.sel_of_loc inferInstance hk hS h2 hFull m f hf hloc)
  loc_of_sel s hs := by
    obtain ⟨n, c, hc⟩ := selmer_class_from_level (sqrtK k) E ⟨s, hs⟩
    obtain ⟨f, hf, hloc, hcf⟩ := G.loc_of_sel inferInstance hk hS h2 hFull n c c.2
    refine ⟨n, f, hf, hloc, ?_⟩
    rw [← kc_levelToInfinite_kerToH1 k S E hFull n f hf, hcf]
    exact hc

end Arith

/-! ### The inhabitants -/

section Inhabitants

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))

/-- **The concrete Kummer coefficient comparison** `τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(Sel_{2^∞}(E_ℓ/K))`
for `K = ℚ(√k)` totally complex, `S` finite containing the primes above `2`: the morphism
`kcPhi` of the level datum `kcArithLevelData`, a quasi-isomorphism by `kcPhi_quasiIso`; the only
input is the finite-level Selmer description `KcArithSelmerLevel` (GLUE). Kind: definition
(PROVED from the named input). -/
def kcKummerCoefficientComparison (hk : k < 0) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S)
    (G : KcArithSelmerLevel k S (Ecurve ℓ)) : KummerCoefficientComparison ℓ k S hFull where
  finite_support := hS
  comparison := kcPhi hFull (kcArithLevelData k S (Ecurve ℓ) hFull) (SelK ℓ k)
    (kcSelmerSupport_of_level k S (Ecurve ℓ) hFull hk hS h2 G)
  quasiIso := kcPhi_quasiIso hFull (kcArithLevelData k S (Ecurve ℓ) hFull) (SelK ℓ k)
    (kcSelmerSupport_of_level k S (Ecurve ℓ) hFull hk hS h2 G)

/-- The comparison of `kcKummerCoefficientComparison` is `kcPhi`. Kind: PROVED. -/
theorem kcKummerCoefficientComparison_comparison (hk : k < 0) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S)
    (G : KcArithSelmerLevel k S (Ecurve ℓ)) :
    (kcKummerCoefficientComparison ℓ k S hFull hk hS h2 G).comparison =
      kcPhi hFull (kcArithLevelData k S (Ecurve ℓ) hFull) (SelK ℓ k)
        (kcSelmerSupport_of_level k S (Ecurve ℓ) hFull hk hS h2 G) :=
  rfl

end Inhabitants

section Signed

variable (t : ℚ) (k : ℤ) [(curve t).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((curve t).baseChange (QuadraticField k)) (2 ^ n))

/-- **The signed version**: the same construction for `E_t = curve t`, an inhabitant of
`KummerCoefficientComparisonSigned t k S hFull`. Kind: definition (PROVED from the named
input). -/
def kcKummerCoefficientComparisonSigned (hk : k < 0) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S)
    (G : KcArithSelmerLevel k S (curve t)) : KummerCoefficientComparisonSigned t k S hFull where
  finite_support := hS
  comparison := kcPhi hFull (kcArithLevelData k S (curve t) hFull) (SelKSigned t k)
    (kcSelmerSupport_of_level k S (curve t) hFull hk hS h2 G)
  quasiIso := kcPhi_quasiIso hFull (kcArithLevelData k S (curve t) hFull) (SelKSigned t k)
    (kcSelmerSupport_of_level k S (curve t) hFull hk hS h2 G)

end Signed

end ZInQ.Manuscript.RC

import ZInQKernel.Contrib.CloudB3E1Torsion.AugLift
import ZInQKernel.Contrib.CloudB3E1Torsion.KmScale
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.HomotopyComparison
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18RetainedChain

/-!
# The Knudsen–Mumford coordinate changes by a unit along a homotopy equivalence

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate`, tex 4189–4193: "replacing
them by the retained homotopy equivalent free models contributes only determinants of unit disks.
These are `A_i`-units. Their limits and inverse limits are `Λ`-units."

Let `E : HEMat R …` be exact homotopy-equivalence data over a domain `R`, between two four-term
models of possibly different ranks, read over its fraction field `K`. For a cycle `z` and a closed
functional `λ` of the first model over `K`, the following holds.

**`kmCoord_comparison_unit`** (PROVED): for any orientations there is a unit `ε ∈ R^×` with
`kmCoord(B, f₁ z, λ g₂) = ε · kmCoord(A, z, λ)`.

Proof:
1. `z` and `λ` are scaled to integral representatives, `a z = z₀` and `b λ = λ₀` with
   `a, b ∈ R ∖ {0}`. Both coordinates scale by `a b` (`kmCoord_smul`).
2. Over `R`, `E` lifts to the augmented complexes at `(z₀, λ₀)` (`augF`, `augHomotopyData`). The
   cone of the lift is contractible over `R` (`HomotopyData.coneContraction`), so its torsion `τ`
   is a unit of `R`.
3. Over `K`, the coordinate formula through the cone (`kmCoord_eq_of_augmented_comparison`) gives
   `kmCoord(A) = (−1)^{|κo|} kmCoord(B) τ⁻¹`, with `τ` read in `K` (`coneR_augF_map`).

**`kmCoordComparisonLamUnit`** (PROVED) is lane RC32's named statement `KmCoordComparisonLamUnit`,
the case `R = Λ`, `K = Frac Λ`. **`htildeE_of_retained'`** (PROVED) is lane RC32's
`htildeE_of_retained` without that input.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.Wiring (HEMat KmCoordComparisonLamUnit LamI FracLam lamToF)

/-! ### Chain maps over a field -/

section Field

variable {K : Type} [Field K] {κe κo κe' κo' : Type} [Fintype κe] [Fintype κo] [DecidableEq κe]
  [DecidableEq κo] [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx K κe κo} {D : BasedCx K κe' κo'}

/-- A chain map over a field, as the field form `ChainMapB`. Kind: definition. -/
def chainMapToB (f : ChainMapR C D) : ChainMapB C D :=
  ⟨f.fE, f.fO, f.deg_fE, f.deg_fO, f.commOE, f.commEO⟩

omit [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo'] in
/-- The two cones agree. Kind: PROVED. -/
theorem cone_toB (f : ChainMapR C D) : BasedCx.cone (chainMapToB f) = BasedCx.coneR f := rfl

end Field

/-- Equal classes and functionals give equal coordinates. Kind: PROVED. -/
theorem kmCoord_congr_vec {R : Type} [CommRing R] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1]
    [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    (C : FourCx R ι0 ι1 ι2 ι3) {z z' : ι1 → R} {lam lam' : ι2 → R} (hzz : z = z')
    (hll : lam = lam') (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (hz' : C.d1 *ᵥ z' = 0)
    (hlam' : lam' ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ = kmCoord C z' lam' hz' hlam' σ := by
  subst hzz hll
  rfl

/-! ### The comparison over a domain, read over its fraction field -/

section Domain

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
  {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1]
  [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0]
  [DecidableEq A1] [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3]

omit [IsDomain R] [IsFractionRing R K] in
/-- **The cone of the augmented comparison over `K` is the cone over `R`, read in `K`**, for
integral representatives `z₀ = a z`, `λ₀ = b λ`. Kind: PROVED. -/
theorem coneR_augF_map (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥)
    (hEF : (E.map (algebraMap R K)).Holds ⊥) {z₀ : A1 → R} {l₀ : A2 → R}
    (hz₀ : E.dA1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* E.dA1 = 0) {z : A1 → K} {lam : A2 → K}
    (hzK : (E.map (algebraMap R K)).dA1 *ᵥ z = 0)
    (hlK : lam ᵥ* (E.map (algebraMap R K)).dA1 = 0)
    (hzz : ∀ i, algebraMap R K (z₀ i) = z i) (hll : ∀ i, algebraMap R K (l₀ i) = lam i) :
    BasedCx.coneR (augF (E.map (algebraMap R K)) hEF hzK hlK) =
      (BasedCx.coneR (augF E hE hz₀ hl₀)).map (algebraMap R K) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · ext i j
    rcases i with (i | i | i) | ((i | i) | i) <;> rcases j with ((j | j) | j) | (j | j | j) <;>
      simp [BasedCx.coneR, BasedCx.map, augF, FourCx.toBased_dOE, FourCx.toBased_dEO,
        FourCx.aug, HEMat.cxA, HEMat.cxB, HEMat.map, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, map_sum, map_mul, hzz, hll]
  · ext i j
    rcases i with ((i | i) | i) | (i | i | i) <;> rcases j with (j | j | j) | ((j | j) | j) <;>
      simp [BasedCx.coneR, BasedCx.map, augF, FourCx.toBased_dOE, FourCx.toBased_dEO,
        FourCx.aug, HEMat.cxA, HEMat.cxB, HEMat.map, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, hzz, hll]

/-- **The Knudsen–Mumford coordinate changes by a unit of `R` along a homotopy equivalence**
(tex 4189–4193): see the module docstring. Kind: PROVED. -/
theorem kmCoord_comparison_unit (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥)
    (hEF : (E.map (algebraMap R K)).Holds ⊥) (z : A1 → K) (lam : A2 → K)
    (hz : (E.map (algebraMap R K)).dA1 *ᵥ z = 0) (hlam : lam ᵥ* (E.map (algebraMap R K)).dA1 = 0)
    (σA : (A0 ⊕ Unit) ⊕ A2 ≃ A1 ⊕ (A3 ⊕ Unit)) (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit)) :
    ∃ ε : Rˣ, (E.map (algebraMap R K)).retainedKm hEF hz hlam σB =
      algebraMap R K (ε : R) * kmCoord ((E.map (algebraMap R K)).cxA hEF) z lam hz hlam σA := by
  classical
  set F := E.map (algebraMap R K) with hF
  -- integral representatives
  obtain ⟨⟨a, ha⟩, hza⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    Finset.univ z
  obtain ⟨⟨b, hb⟩, hlb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    Finset.univ lam
  choose z₀ hz₀ using fun i => hza i (Finset.mem_univ i)
  choose l₀ hl₀ using fun i => hlb i (Finset.mem_univ i)
  have ha0 : algebraMap R K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hzz : ∀ i, algebraMap R K (z₀ i) = (algebraMap R K a • z) i := fun i => by
    rw [hz₀ i, Algebra.smul_def]; rfl
  have hll : ∀ i, algebraMap R K (l₀ i) = (algebraMap R K b • lam) i := fun i => by
    rw [hl₀ i, Algebra.smul_def]; rfl
  have hz' : F.dA1 *ᵥ (algebraMap R K a • z) = 0 := by rw [mulVec_smul, hz, smul_zero]
  have hlam' : (algebraMap R K b • lam) ᵥ* F.dA1 = 0 := by rw [smul_vecMul, hlam, smul_zero]
  have hzR : E.dA1 *ᵥ z₀ = 0 := by
    funext i
    apply IsFractionRing.injective R K
    have h := congrFun hz' i
    rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
    convert h using 2 <;> first | rfl | (funext k; exact hzz k)
  have hlR : l₀ ᵥ* E.dA1 = 0 := by
    funext j
    apply IsFractionRing.injective R K
    have h := congrFun hlam' j
    rw [RingHom.map_vecMul, Pi.zero_apply, map_zero]
    convert h using 2 <;> first | rfl | (funext k; exact hll k)
  -- the cone over `R` and its unit torsion
  set σ := σB.sumCongr σA.symm
  have HR := augHomotopyData E hE hzR hlR
  have hunit := isUnit_tau_coneR HR σ
  have htor : torsion (BasedCx.cone (chainMapToB (augF F hEF hz' hlam'))) σ =
      algebraMap R K (tau (BasedCx.coneR (augF E hE hzR hlR)) HR.coneContraction σ) := by
    rw [cone_toB, coneR_augF_map E hE hEF hzR hlR hz' hlam' hzz hll, coneR_map]
    exact torsion_coneR_map _ HR σ
  have hne : torsion (BasedCx.cone (chainMapToB (augF F hEF hz' hlam'))) σ ≠ 0 := by
    rw [htor]
    exact fun h => hunit.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h)
  -- the coordinate formula over `K`
  have key := ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy.kmCoord_eq_of_augmented_comparison
    (C := F.cxA hEF) (D := F.cxB hEF) hz' hlam' (F.transport_cycle hEF hz')
    (F.transport_closed hEF hlam') (chainMapToB (augF F hEF hz' hlam')) σA σB hne
  rw [htor] at key
  rw [kmCoord_smul _ z lam hz hlam ha0 hb0 hz' hlam' σA] at key
  have hB : kmCoord (F.cxB hEF) (F.f1 *ᵥ (algebraMap R K a • z))
      ((algebraMap R K b • lam) ᵥ* F.g2) (F.transport_cycle hEF hz')
      (F.transport_closed hEF hlam') σB =
      algebraMap R K a * algebraMap R K b * F.retainedKm hEF hz hlam σB := by
    rw [kmCoord_congr_vec (F.cxB hEF) (mulVec_smul _ _ _) (smul_vecMul _ _ _) _ _
      (by rw [← mulVec_smul]; exact F.transport_cycle hEF hz')
      (by rw [← smul_vecMul]; exact F.transport_closed hEF hlam') σB]
    exact kmCoord_smul _ _ _ (F.transport_cycle hEF hz) (F.transport_closed hEF hlam) ha0 hb0
      _ _ σB
  rw [hB] at key
  refine ⟨(-1) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit)) * hunit.unit, ?_⟩
  set t := algebraMap R K (tau (BasedCx.coneR (augF E hE hzR hlR)) HR.coneContraction σ)
  have ht : t ≠ 0 := fun h => hunit.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h)
  have hs : ((-1 : K) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit))) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hc : algebraMap R K a * algebraMap R K b ≠ 0 := mul_ne_zero ha0 hb0
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    IsUnit.unit_spec, map_mul, map_pow, map_neg, map_one]
  change F.retainedKm hEF hz hlam σB = (-1) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit)) * t *
    kmCoord (F.cxA hEF) z lam hz hlam σA
  have key' : algebraMap R K a * algebraMap R K b * kmCoord (F.cxA hEF) z lam hz hlam σA * t =
      (-1) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit)) * (algebraMap R K a * algebraMap R K b *
        F.retainedKm hEF hz hlam σB) := by
    rw [key]; field_simp
  apply mul_left_cancel₀ hc
  calc algebraMap R K a * algebraMap R K b * F.retainedKm hEF hz hlam σB
      = ((-1 : K) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit))) ^ 2 *
          (algebraMap R K a * algebraMap R K b * F.retainedKm hEF hz hlam σB) := by
        rw [hs, one_mul]
    _ = (-1) ^ Fintype.card (A1 ⊕ (A3 ⊕ Unit)) *
          (algebraMap R K a * algebraMap R K b * kmCoord (F.cxA hEF) z lam hz hlam σA * t) := by
        rw [key']; ring
    _ = _ := by ring

end Domain

/-! ### Lane RC32's named statement and its consumer -/

/-- **Lane RC32's `KmCoordComparisonLamUnit`, proved** (tex 4189–4193): the case `R = Λ`,
`K = Frac Λ` of `kmCoord_comparison_unit`. Kind: PROVED. -/
theorem kmCoordComparisonLamUnit : KmCoordComparisonLamUnit := by
  intro A0 A1 A2 A3 B0 B1 B2 B3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E hE hEF z lam hz hlam σA σB
  exact kmCoord_comparison_unit (R := LamI) (K := FracLam) E hE hEF z lam hz hlam σA σB

section HTilde

open Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx)

variable {ι : Type} [DecidableEq ι] {Cx : ∀ s, Finset ι → GCx (StageRing s)}
  {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
  {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
  (x : Addr Fam.b) (ps : List ℕ)
  (G : Set ℕ) (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx ps.length)
  (bw : ∀ s i, (Cx s (insert (pidx i) (chainT pidx i))).X 0)
  (μ : ∀ s i, (Cx s (chainT pidx i)).X 3 →ₗ[StageRing s] StageRing s)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G)
  (f : FrobSeq LamI)
  (hs : ∀ᶠ s in (U : Filter ℕ), (stageMatsOn G cd bw μ s).Holds (stageIdeal s) f ps.length)

/-- **Lane RC32's relaxed end field from the retained-basis identification, without the named
input** (tex 4147, 4150–4152, 4189–4193): `htildeE_of_retained` with
`KmCoordComparisonLamUnit` discharged by `kmCoordComparisonLamUnit`. Kind: PROVED. -/
theorem htildeE_of_retained' {B0 B1 B2 B3 : Type} [Fintype B0]
    [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq B0] [DecidableEq B1] [DecidableEq B2]
    [DecidableEq B3]
    (RM : ∀ s (_ : s ∈ G), RetainedModel (Cx s (chainT pidx ps.length)) B0 B1 B2 B3)
    (σB : (B0 ⊕ Unit) ⊕ B2 ≃ B1 ⊕ (B3 ⊕ Unit))
    (hret : ps ≠ [] → IsTExpansion (etaF ℓ Fam x * retainedEndCoord G cd RM bw μ hU hG f hs σB)
      (D.uTilde Fam x))
    (hnil : ps = [] → IsTExpansion (etaF ℓ Fam x *
      (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
        ps.length) (D.uTilde Fam x)) :
    ∃ ε : ZInQ.Manuscript.RC.Limits.Lambdaˣ, (ps = [] → ε = 1) ∧
      IsTExpansion (lamToF (ε : ZInQ.Manuscript.RC.Limits.Lambda) * (etaF ℓ Fam x *
        (fracChain (stageMatsOn G cd bw μ) U).chainV (fracChain_holds _ hU f ps.length hs)
          ps.length)) (D.uTilde Fam x) :=
  htildeE_of_retained D Fam x ps G cd bw μ hU hG f hs kmCoordComparisonLamUnit RM σB hret hnil

end HTilde

end ZInQ.Contrib.CloudB3E1Torsion

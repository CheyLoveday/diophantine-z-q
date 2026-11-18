import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4Bridge
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.NonVacuity

/-!
# E1a, part 9: `OrigCoordLink` by cases, with no exactness at degenerate constituents

RC0's round-4 input `OrigCoordLink` (`RC/Wiring/ClearingComplex4.lean`, tex 5605–5611): where
`Δ_x ≠ 0`, `ũ_x = η_x · c^{orig}_x`, `c^{orig}_x` the Knudsen–Mumford coordinate of `[z] ⊗ [λ]` of
the sign-evaluated pre-cancellation complex `C_x`. RC0's `integralCore_coord_ne_zero` shows that
batch 3's core route (`relIsKM_of_core`, an integral core with exact augmentation at EVERY address)
forces `ũ_x ≠ 0` everywhere, which fails at generically acyclic constituents (tex 3889–3890,
5612–5615). Here the coordinate is handled by cases on whether `c^{orig}_x` vanishes:

* `kmOrig_eq` (PROVED): `c^{orig}_x = det B_x · c_x` with `c = cOf M.D z μ` (new-local
  cancellation);
* `kmOrig_zero_of_acyclic` (PROVED): at a generically acyclic constituent (`Δ_x ≠ 0`),
  `c^{orig}_x = 0` (E1b's acyclic part, `coordComputation_km`);
* `uK_zero_of_uTilde_zero` (PROVED);
* `urelK_eq_kmOrig_of_core` (PROVED, one address): the core route at a single address;
* **`origCoordLink_of_cases` (PROVED)**: `OrigCoordLink D F M z λ (φO η_Λ)` from the (4.7) data
  `T` (with `hutilde`, `CorrectedIsEta` by `correctedIsEta_of_triangles`) and, at each `x` with
  `Δ_x ≠ 0`,
  - **degenerate** (`c^{orig}_x = 0`: e.g. every generically acyclic constituent): the (4.7)
    relaxed coordinate vanishes, `u_{rel,x} = 0` (the text's convention `u = 0`, tex 3889–3890);
  - **non-degenerate** (`c^{orig}_x ≠ 0`, so the augmented `C_x` is acyclic): an integral two-term
    core carrying `u_{rel,x}` with the same Knudsen–Mumford coordinate as `C_x` (batch 3's
    `PreCoreLink`; supplied by a retained comparison map through the cone invariance
    `kmCoord_eq_of_fourMap_retained`). No exactness is assumed at degenerate constituents.
* `degenerate_of_patterns` (PROVED): the degenerate input splits along E2's patterns: at a
  generically acyclic constituent it is `u_{rel,x} = 0`; at a rank-one constituent it is needed only
  where `c^{orig}_x = 0`.
* `origCases_zero_example` (LESSON 2): the case inputs hold for every genuine identification with
  the zero class and functional and interface data with `ũ = 0` (all addresses degenerate); the
  non-degenerate branch is inhabited in batch 3's `CoordLink/ComparisonExample.lean`
  (`ũ = −t`, `Identification2`).

**Classification.** PROVED (the two case inputs are named).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- The original coordinate `c^{orig}_x`. -/
abbrev kmOrig (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) : FractionRing OO :=
  kmCoord (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) (evK (sgnChar x) ∘ z)
    (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x)
    (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N)

/-- **`c^{orig}_x = det B_x · c_x`** (PROVED; the new-local cancellation). -/
theorem kmOrig_eq (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) :
    kmOrig M z lam hz hlam x = evK (sgnChar x) (M.C.map (φO b)).B.det *
      cOf M.D z (transportFun (M.C.map (φO b)) lam) hz
        (hμ_cancel (M.C.map (φO b)) M.isUnit_B hlam) x := by
  have key := kmCoord_preCancel (C := Cev (M.C.map (φO b)) x)
    (isUnit_Bev (M.C.map (φO b)) M.isUnit_B x) (z := evK (sgnChar x) ∘ z)
    (lam := evK (sgnChar x) ∘ lam) (hz := hzev (hzC M.isUnit_B hz) x) (hlam := hlamev hlam x)
  refine key.trans ?_
  rw [det_Bev (M.C.map (φO b)) x]
  congr 1
  unfold cOf
  exact (kmCoord_congr (Dev_toFour_eq (M.C.map (φO b)) M.isUnit_B x) rfl
    (transport_map M.isUnit_B lam x) _ _ _ _ _).symm

/-- **At a generically acyclic constituent the original coordinate vanishes** (PROVED; E1b's
acyclic part). -/
theorem kmOrig_zero_of_acyclic (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0)
    (hA : M.D.AcyclicPattern x) : kmOrig M z lam hz hlam x = 0 := by
  rw [kmOrig_eq]
  have h := (coordComputation_km M.D z (transportFun (M.C.map (φO b)) lam) hz
    (hμ_cancel (M.C.map (φO b)) M.isUnit_B hlam) M.toIdentification.A0 M.toIdentification.s
    M.toIdentification.s_ne M.toIdentification.central).2 x hΔ hA
  rw [h.2, mul_zero]

/-- A representation of a vanishing corrected coordinate at `x` is zero there. -/
theorem uK_zero_of_uTilde_zero {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {e : Addr F.b → ℕ}
    {g : Addr F.b → Lam} (hrep : UTildeRep Dd F e g) (x : Addr F.b) (h0 : Dd.uTilde F x = 0) :
    uK (O := OO) (e x) (g x) = 0 := by
  have hg : g x = 0 := by
    apply ιQ_injective
    have h1 := uTilde_eq_of_rep hrep x
    rw [h0] at h1
    have h2 : PowerSeries.C ((2 : ℚ_[2]) ^ e x)⁻¹ ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.coeff 0) h
      simp at this
    rw [map_zero]
    exact (mul_eq_zero.mp h1.symm).resolve_left h2
  simp [Determinant.uK, hg]

/-- **The core route at one address** (PROVED): the relaxed coordinate `urelK x` is the original
coordinate when an integral core with exact augmentation carries the (4.7) relaxed coordinate and
has the same Knudsen–Mumford coordinate as `C_x`. -/
theorem urelK_eq_kmOrig_of_core {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) {e₀ : Addr F.b → ℕ}
    {g₀ : Addr F.b → Lam} (h₀ : UTildeRep Dd F e₀ g₀) (x : Addr F.b)
    (T : CommonCoordinateTrianglesN Dd F x)
    (hcompat : T.chi (Central.eta T.Q T.v T.g) = ιQ (Determinant.signEval (sgnChar x) ηΛ))
    (c : IntegralCore)
    (hcore : Central.IsClassFunctionalCoord (c.D.map ιQ) (ιQ ∘ c.zc) (ιQ ∘ c.wc) T.urel)
    (hlink : kmOrig M z lam hz hlam x =
      kmCoord (twoTerm (c.D.map ψO)) (ψO ∘ c.zc) (ψO ∘ c.wc) c.hz c.hw (σ₀ c.n)) :
    urelK ηΛ hunit e₀ g₀ x = kmOrig M z lam hz hlam x := by
  rw [hlink]
  have hu := hcore
  rw [urel_eq_of_triangles ηΛ hunit h₀ x T hcompat] at hu
  have hK := isClassFunctionalCoord_transport c.D c.zc c.wc (e₀ x) ((hunit x).unit⁻¹ * g₀ x) hu
  obtain ⟨hc⟩ := exists_contraction _ (FourCx.isExact_toBased _ c.exact)
  exact (kmCoord_twoTerm _ _ _ _ _ _ hc hK).symm

/-- **`OrigCoordLink` by cases** (PROVED): from the (4.7) data, the degenerate input
(`u_{rel,x} = 0` where `c^{orig}_x = 0`) and the non-degenerate input (an integral core with the
same coordinate as `C_x` where `c^{orig}_x ≠ 0`), at the addresses with `Δ_x ≠ 0`. -/
theorem origCoordLink_of_cases {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hcompat : ∀ x, (T x).chi (Central.eta (T x).Q (T x).v (T x).g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ))
    (hdeg : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      kmOrig M z lam hz hlam x = 0 → (T x).urel = 0)
    (hnd : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      kmOrig M z lam hz hlam x ≠ 0 →
      ∃ c : IntegralCore,
        Central.IsClassFunctionalCoord (c.D.map ιQ) (ιQ ∘ c.zc) (ιQ ∘ c.wc) (T x).urel ∧
        kmOrig M z lam hz hlam x =
          kmCoord (twoTerm (c.D.map ψO)) (ψO ∘ c.zc) (ψO ∘ c.wc) c.hz c.hw (σ₀ c.n)) :
    OrigCoordLink Dd F M z lam hz hlam (φO F.b ηΛ) := by
  intro e g hrep x hΔ
  change uK (e x) (g x) = evK (sgnChar x) (φO F.b ηΛ) * kmOrig M z lam hz hlam x
  by_cases h0 : kmOrig M z lam hz hlam x = 0
  · have hu : (T x).urel = 0 := hdeg x hΔ h0
    have ht : Dd.uTilde F x = 0 := by rw [(T x).hutilde, hu, mul_zero]
    rw [uK_zero_of_uTilde_zero hrep x ht, h0, mul_zero]
  · obtain ⟨c, hc, hlink⟩ := hnd x hΔ h0
    rw [correctedIsEta_of_triangles Dd F ηΛ hunit e₀ g₀ h₀ e g hrep x,
      urelK_eq_kmOrig_of_core Dd F M z lam hz hlam ηΛ hunit h₀ x (T x) (hcompat x) c hc hlink]

/-- **The degenerate input along E2's patterns** (PROVED): it holds if `u_{rel,x} = 0` at every
generically acyclic constituent and at every rank-one constituent with `c^{orig}_x = 0`. -/
theorem degenerate_of_patterns {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hA : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.AcyclicPattern x →
      (T x).urel = 0)
    (hR : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → M.D.RankOnePattern x →
      kmOrig M z lam hz hlam x = 0 → (T x).urel = 0) :
    ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      kmOrig M z lam hz hlam x = 0 → (T x).urel = 0 := by
  intro x hΔ h0
  obtain ⟨d0, d1, d2⟩ := M.D.dets_of_Δ M.toIdentification.A0 M.toIdentification.s
    M.toIdentification.s_ne M.toIdentification.central x hΔ
  rcases M.D.patterns_of_det_ne_zero x d0 d1 d2 with h | h
  · exact hR x hΔ h h0
  · exact hA x hΔ h

/-! ### LESSON 2: the case inputs with all addresses degenerate -/

/-- The (4.7) data for `ũ = u_prim = 0`: no unused primes, `η = 1`, `u_rel = 0`. -/
def trianglesZero (ℓ : ℕ) (F : Family) (x : Addr F.b) :
    CommonCoordinateTrianglesN (ddZero ℓ) F x where
  R := PowerSeries ℚ_[2]
  chi := RingHom.id _
  Q := ∅
  v _ := 0
  g _ := 1
  l _ := 1
  e _ := 1
  ei _ := 1
  hsign := by simp
  hratio := by simp
  hinv := by simp
  urel := 0
  U := ∅
  hU := by simp
  hutilde := by simp [ddZero]
  qn _ := 1
  hodd := by simp
  F _ := 1
  a _ := 0
  z _ := 1
  zi _ := 1
  ha := by simp
  hd := by simp
  hl := by simp
  he := by simp
  u _ := 0
  hrel := rfl
  hprim := rfl
  eps _ := 1
  hstep := by simp

/-- **LESSON 2: the case inputs of `origCoordLink_of_cases` hold together** for every genuine
identification, with the zero class and functional and interface data with `ũ = 0` (every address
is degenerate: the coordinate of the zero class vanishes). -/
theorem origCases_zero_example (ℓ : ℕ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK) :
    OrigCoordLink (ddZero ℓ) F M 0 0 (mulVec_zero _) (zero_vecMul _) (φO F.b 1) :=
  origCoordLink_of_cases (ddZero ℓ) F M 0 0 (mulVec_zero _) (zero_vecMul _) 1
    (fun _ => by simp) (fun _ => 0) (fun _ => 0) (fun x j => by simp [ddZero])
    (trianglesZero ℓ F) (fun x => by
      change (∏ q ∈ (∅ : Finset ℕ), Central.correctionFactor (0 : PowerSeries ℚ_[2]) 1) =
        ιQ (Determinant.signEval (sgnChar x) 1)
      rw [Finset.prod_empty, map_one, map_one])
    (fun _ _ _ => rfl)
    (fun x _ h => absurd (by
      have hz' : (evK (sgnChar x) ∘
          (0 : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))) = 0 := by
        funext i; simp
      exact (kmCoord_congr rfl hz' rfl _ _ (mulVec_zero _) (hlamev (zero_vecMul _) x) _).trans
        (kmCoord_zero_class _ _ _ _ _)) h)

end ZInQ.Contrib.CloudB3RC53.CoordLink

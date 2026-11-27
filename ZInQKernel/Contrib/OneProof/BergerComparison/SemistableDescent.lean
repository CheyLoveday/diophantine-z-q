import ZInQKernel.Contrib.OneProof.BergerComparison.LogTranscendence
import ZInQKernel.Contrib.OneProof.BergerComparison.Transport

/-! Frobenius transport on the embedded semistable rings. The two Frobenius endomorphisms are the
restrictions along the proved inclusion of the crystalline image. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne FontaineSt BergerReroute
open PanBergerSplit (flatAct)
open ZInQ.Contrib.G9.BdrKer.Cp
open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 600000

private abbrev logP := toBdR p (logPTilde p)

private def maxIntoSt : Bmax p →ₐ[ℚ_[p]] Bst p :=
  Subalgebra.inclusion (bmax_le_bst p)

private def crisIntoSt {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    CrystallineRing p h →ₐ[ℚ_[p]] FontaineRing p h :=
  Subalgebra.inclusion (bcrisOf_le_bstFOf p h (xi p) (theta_xi' p))

private def stLog : Bst p := ⟨logP p, logPTilde_mem_bst p⟩

private def stCrisLog {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) : FontaineRing p h :=
  ⟨logP p, Algebra.subset_adjoin (Or.inr rfl)⟩

/-- Evaluate a maximal coefficient polynomial in the actual maximal image. -/
def evaluateMaximalSt : (Bmax p)[X] →+* Bst p :=
  eval₂RingHom (maxIntoSt p).toRingHom (stLog p)

/-- Apply coefficient Frobenius, then evaluate at the scaled logarithm
in the actual crystalline image. -/
def evaluateFrobeniusSt {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    (Bmax p)[X] →+* FontaineRing p h :=
  eval₂RingHom ((crisIntoSt p h).comp (coefficientFrobenius p h)).toRingHom (p * stCrisLog p h)

/-- Maximal evaluation is the actual ambient polynomial evaluation. -/
theorem evaluateMaximalSt_val (Q : (Bmax p)[X]) :
    (evaluateMaximalSt p Q : BdR p) = aeval (logP p) Q := by
  rw [aeval_def]
  exact Polynomial.hom_eval₂ Q (maxIntoSt p).toRingHom (Bst p).val.toRingHom (stLog p)

/-- Polynomial representatives of the actual maximal semistable image suffice. -/
theorem evaluateMaximalSt_surjective : Function.Surjective (evaluateMaximalSt p) := by
  intro x
  have hx' (y : BdR p) (hy : y ∈ Bst p) : y ∈ Algebra.adjoin (Bmax p) {logP p} := by
    rw [bst_eq_adjoin p] at hy
    exact hy
  have hx := hx' x.val x.property
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨Q, hQ⟩ := hx
  exact ⟨Q, Subtype.ext ((evaluateMaximalSt_val p Q).trans hQ)⟩

/-- The maximal image is a polynomial ring by the logarithm
transcendence theorem. -/
theorem evaluateMaximalSt_injective : Function.Injective (evaluateMaximalSt p) := by
  intro Q R h
  apply transcendental_iff_injective.mp (logPTilde_transcendental p)
  rw [← evaluateMaximalSt_val, ← evaluateMaximalSt_val, h]

private def maxStEquiv : (Bmax p)[X] ≃+* Bst p :=
  RingEquiv.ofBijective (evaluateMaximalSt p)
    ⟨evaluateMaximalSt_injective p, evaluateMaximalSt_surjective p⟩

private def frobStRing {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Bst p →+* FontaineRing p h :=
  (evaluateFrobeniusSt p h).comp (maxStEquiv p).symm.toRingHom

private theorem frobStRing_apply {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (Q : (Bmax p)[X]) :
    frobStRing p h (evaluateMaximalSt p Q) = evaluateFrobeniusSt p h Q := by
  change evaluateFrobeniusSt p h ((maxStEquiv p).symm ((maxStEquiv p) Q)) = _
  rw [RingEquiv.symm_apply_apply]

private theorem frobStRing_coeff {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (b : Bmax p) :
    frobStRing p h (maxIntoSt p b) = crisIntoSt p h (coefficientFrobenius p h b) := by
  change frobStRing p h ((maxIntoSt p).toRingHom b) =
    ((crisIntoSt p h).comp (coefficientFrobenius p h)).toRingHom b
  simpa only [evaluateMaximalSt, evaluateFrobeniusSt, coe_eval₂RingHom, eval₂_C]
    using frobStRing_apply p h (C b)

/-- The prescribed Frobenius between the actual semistable images. -/
def semistableFrobenius {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    Bst p →ₐ[ℚ_[p]] FontaineRing p h :=
  { frobStRing p h with
    commutes' := by
      intro q
      change frobStRing p h (maxIntoSt p (algebraMap ℚ_[p] (Bmax p) q)) =
        algebraMap ℚ_[p] (FontaineRing p h) q
      rw [frobStRing_coeff p h, AlgHom.commutes, AlgHom.commutes] }

theorem semistableFrobenius_coeff {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (b : Bmax p) :
    semistableFrobenius p h (maxIntoSt p b) = crisIntoSt p h (coefficientFrobenius p h b) :=
  frobStRing_coeff p h b

theorem semistableFrobenius_log {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    semistableFrobenius p h (stLog p) = p * stCrisLog p h := by
  change frobStRing p h (stLog p) = _
  simpa only [evaluateMaximalSt, evaluateFrobeniusSt, coe_eval₂RingHom, eval₂_X]
    using frobStRing_apply p h X

private theorem maxIntoSt_galois (σ : GQp p) (q : Bmax p) :
    periodAct p _ (bst_stable p) σ (maxIntoSt p q) = maxIntoSt p (maxGalois p σ q) := by
  apply Subtype.ext
  change bdrAct p σ (q : BdR p) = bdrAct p σ (q : BdR p)
  rfl

private theorem inclusion_val {S T : Subalgebra ℚ_[p] (BdR p)} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h x : T) : BdR p) = (x : BdR p) := rfl

private theorem periodAct_val_ring (B : Subalgebra ℚ_[p] (BdR p))
    (hB : ∀ σ : GQp p, ∀ x ∈ B, bdrAct p σ x ∈ B) (σ : GQp p) (x : B) :
    (periodAct p B hB σ x : BdR p) = bdrAct p σ (x : BdR p) := rfl

private theorem crisIntoSt_val {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (q : CrystallineRing p h) : (crisIntoSt p h q : BdR p) = (q : BdR p) :=
  inclusion_val p (bcrisOf_le_bstFOf p h (xi p) (theta_xi' p)) q

private theorem crisIntoSt_galois_frob {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (σ : GQp p) (q : Bmax p) :
    crisIntoSt p h (coefficientFrobenius p h (maxGalois p σ q)) =
      periodAct p _ (bstF_stable p h) σ (crisIntoSt p h (coefficientFrobenius p h q)) := by
  apply Subtype.ext
  exact (crisIntoSt_val p h (coefficientFrobenius p h (maxGalois p σ q))).trans
    ((coefficientFrobenius_galois p h σ q).trans
      ((congrArg (bdrAct p σ) (crisIntoSt_val p h (coefficientFrobenius p h q))).symm.trans
        (periodAct_val_ring p (FontaineRing p h) (bstF_stable p h) σ
          (crisIntoSt p h (coefficientFrobenius p h q))).symm))

private theorem semistable_galois_coeff {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (σ : GQp p) (q : Bmax p) :
    semistableFrobenius p h (periodAct p _ (bst_stable p) σ (maxIntoSt p q)) =
      periodAct p _ (bstF_stable p h) σ (semistableFrobenius p h (maxIntoSt p q)) := by
  let F := semistableFrobenius p h
  let G := periodAct p _ (bst_stable p) σ
  let G' := periodAct p _ (bstF_stable p h) σ
  calc
    F (G (maxIntoSt p q)) = F (maxIntoSt p (maxGalois p σ q)) :=
      congrArg F (maxIntoSt_galois p σ q)
    _ = crisIntoSt p h (coefficientFrobenius p h (maxGalois p σ q)) :=
      semistableFrobenius_coeff p h (maxGalois p σ q)
    _ = G' (crisIntoSt p h (coefficientFrobenius p h q)) := crisIntoSt_galois_frob p h σ q
    _ = G' (F (maxIntoSt p q)) := congrArg G' (semistableFrobenius_coeff p h q).symm

private theorem semistable_galois_log {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (σ : GQp p) :
    semistableFrobenius p h (periodAct p _ (bst_stable p) σ (stLog p)) =
      periodAct p _ (bstF_stable p h) σ (semistableFrobenius p h (stLog p)) := by
  obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
  let δ : Bmax p := ⟨toBdR p (logTeich p hu1), LogPTransc.logTeich_mem_bmax p hu1⟩
  have hg : periodAct p _ (bst_stable p) σ (stLog p) = maxIntoSt p δ + stLog p :=
    Subtype.ext (bdrAct_logPTilde p σ hu hu1)
  rw [hg, map_add, semistableFrobenius_coeff, semistableFrobenius_log, map_mul, map_natCast]
  apply Subtype.ext
  change (coefficientFrobenius p h δ : BdR p) + (p : BdR p) * logP p =
    p * bdrAct p σ (logP p)
  rw [show (coefficientFrobenius p h δ : BdR p) = p * toBdR p (logTeich p hu1) from
    localizedFrobenius_logTeich p h hu1, bdrAct_logPTilde p σ hu hu1, mul_add]

/-- On the embedded rings the only nonconstant contribution to the
Galois comparison is the shift by a kernel logarithm, which is scaled
by the same p as the semistable variable. -/
theorem semistableFrobenius_galois {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (σ : GQp p) (b : Bst p) :
    semistableFrobenius p h (periodAct p _ (bst_stable p) σ b) =
      periodAct p _ (bstF_stable p h) σ (semistableFrobenius p h b) := by
  let F := semistableFrobenius p h
  let G := periodAct p _ (bst_stable p) σ
  let G' := periodAct p _ (bstF_stable p h) σ
  let A := (F.comp G).toRingHom.comp (evaluateMaximalSt p)
  let B := (G'.comp F).toRingHom.comp (evaluateMaximalSt p)
  have hEq : A = B := Polynomial.ringHom_ext (fun q => by
      change F (G (evaluateMaximalSt p (C q))) = G' (F (evaluateMaximalSt p (C q)))
      rw [show evaluateMaximalSt p (C q) = maxIntoSt p q from eval₂_C ..]
      exact semistable_galois_coeff p h σ q)
    (by
      change F (G (evaluateMaximalSt p X)) = G' (F (evaluateMaximalSt p X))
      rw [show evaluateMaximalSt p X = stLog p from eval₂_X ..]
      exact semistable_galois_log p h σ)
  obtain ⟨Q, rfl⟩ := evaluateMaximalSt_surjective p b
  exact DFunLike.congr_fun hEq Q

/-- The natural inclusion of the actual Fontaine image. -/
def includeFontaineSt {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    FontaineRing p h →ₐ[ℚ_[p]] Bst p :=
  Subalgebra.inclusion (LogPTransc.bstFOf_le_bst p h (theta_xi' p))

/-- Frobenius as an endomorphism of the maximal semistable image. -/
def maximalStFrobenius {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) : Bst p →ₐ[ℚ_[p]] Bst p :=
  (includeFontaineSt p h).comp (semistableFrobenius p h)

/-- The restriction of Frobenius to the Fontaine semistable image. -/
def fontaineStFrobenius {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε) :
    FontaineRing p h →ₐ[ℚ_[p]] FontaineRing p h :=
  (semistableFrobenius p h).comp (includeFontaineSt p h)

/-- The comparison intertwines the induced Frobenius on the maximal
image and its restriction to the Fontaine image. -/
theorem semistableFrobenius_intertwines {ε : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε)
    (b : Bst p) :
    semistableFrobenius p h (maximalStFrobenius p h b) =
      fontaineStFrobenius p h (semistableFrobenius p h b) := rfl

/-- The actual semistable map supplies the ring input for basis transport. -/
theorem frobeniusTransport : FrobeniusTransport p :=
  fun _ h => ⟨semistableFrobenius p h, semistableFrobenius_galois p h⟩

end ZInQ.Manuscript.BergerComparison

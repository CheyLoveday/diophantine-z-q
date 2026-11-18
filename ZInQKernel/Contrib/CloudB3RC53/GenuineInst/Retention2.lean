import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate4Witness

/-!
# Genuine instantiations, part 9: place-by-place retention without `UnramifiedNewPlace`

Manuscript `diophantine_zq.tex`, tex L4159–4193 ("all old orthogonal conditions and their
homotopies are retained"; the new place `q` carries the full local complex on the relaxed side and
the unramified condition on the primitive side).

`CommonCoordinate.PlaceRetention` describes the new place `q` by an `UnramifiedNewPlace`, whose
fields demand *degreewise isomorphisms* of the full local complex at `q` with the three-term tame
model; genuine continuous cochains are only quasi-isomorphic to it, so that field cannot be
instantiated by the genuine local complex. Here the new place is described by **arbitrary**
complexes and a chain map:

* `PlaceRetention2`: as `PlaceRetention`, with `NP` replaced by `Lq` (the full local complex at
  `q`), `Uq` (the unramified condition at `q`) and `ιq : Uq → Lq` (its map into the local complex).
  No term-level model of either is required; the genuine instance (`GenuineRetention2`, next file)
  takes `Lq = C^•_cont(G_{K_q}, M)`, `Uq = [W --(Φ−1)--> W]`, `ιq = urToLocal_galois`.
  `PlaceRetention2.retained` / `toRetainedPairing`: the retained-homotopy equality is PROVED exactly
  as before (it never looked at `NP`).
* `SelmerFunctionals2`, `SelmerFunctionals2.restrict` (`w_R|old = e_q w_P`, PROVED from
  `pairedFunctional_natural`), `NaturalStep2`, `NaturalStep2.toActualStep`.
* RC0's consumer: `CommonCoordinateTrianglesG2` (round 4's `CommonCoordinateTrianglesG` with each
  step a `NaturalStep2`), `CommonCoordinateTrianglesG2.toTriangles` (RC0's
  `CommonCoordinateTriangles`), `CommonCoordinateInputsG2`, **`commonCoordinateInputs_of_G2`**,
  `commonCoordinateTarget_of_G2` — the same targets as round 4's `commonCoordinateInputs_of_G`.
* Forgetting the tame model: `PlaceRetention.toPlaceRetention2`,
  `SelmerFunctionals.toSelmerFunctionals2`,
  `NaturalStep.toNaturalStep2`, `CommonCoordinateTrianglesG.toG2`, `commonCoordinateInputsG2_of_G`
  (so the `2`-interfaces are weaker than the old ones), and non-vacuity (LESSON 2):
  `nonempty_placeRetention2`, `nonempty_trianglesG2_three`.

**Classification.** PROVED (interfaces and their transport).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open Matrix CategoryTheory ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.CommonCoordinate

universe u

variable {S : Type u} [CommRing S]

/-- **Place-by-place retention data, with the new place given by its actual complexes**
(tex L4159–4166). As `CommonCoordinate.PlaceRetention`, except that the new place `q` is described
by the full local complex `Lq`, the unramified condition `Uq` and the map `ιq : Uq → Lq` themselves
(no `UnramifiedNewPlace`, i.e. no degreewise tame model). -/
structure PlaceRetention2 (DR DPp : SelData S) {UP US : GCx S} (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) where
  /-- Global target. -/
  E : GCx S
  /-- Local target. -/
  EL : GCx S
  /-- Restriction on the target. -/
  resE : GHom E EL
  /-- Global cup product (shared by both pairings). -/
  cupG : GPair DPp.G DR.G E
  /-- Local cup product (shared by both pairings). -/
  cupL : GPair DPp.L DR.L EL
  compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
    (hk : k = k') (a : DPp.G.X i) (b : DR.G.X j),
    resE.f k k' hk (cupG.P i j k h a b) =
      cupL.P i' j' k' h' (DPp.res.f i i' hi a) (DR.res.f j j' hj b)
  /-- The index type of places. -/
  ι : Type
  /-- The old places. -/
  old : Finset ι
  /-- The old local condition at `v` (primitive/relaxed side). -/
  Uo : ι → GCx S
  /-- The old orthogonal local condition at `v` (strict/orthogonal side). -/
  Uo' : ι → GCx S
  /-- The old isotropy homotopy at `v`. -/
  hv : ∀ (v : ι) (i j k : ℤ), i + j = k + 1 → (Uo' v).X i →ₗ[S] (Uo v).X j →ₗ[S] EL.X k
  /-- The full local complex at the new place `q`. -/
  Lq : GCx S
  /-- The unramified condition at `q`. -/
  Uq : GCx S
  /-- Its map into the local complex at `q`. -/
  ιq : GHom Uq Lq
  /-- The orthogonal of the unramified condition at `q`. -/
  Uq' : GCx S
  /-- The isotropy homotopy at `q` for the primitive pairing. -/
  hq : ∀ i j k : ℤ, i + j = k + 1 → Uq'.X i →ₗ[S] Uq.X j →ₗ[S] EL.X k
  /-- Old components of `U_R`. -/
  pR : ∀ (v : ι) (j : ℤ), DR.U.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_P`. -/
  pP : ∀ (v : ι) (j : ℤ), UP.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_S`. -/
  pS : ∀ (v : ι) (i : ℤ), US.X i →ₗ[S] (Uo' v).X i
  /-- Old components of `U_{P⊥}`. -/
  pPp : ∀ (v : ι) (i : ℤ), DPp.U.X i →ₗ[S] (Uo' v).X i
  /-- The `q`-component of `U_R` (in the full complex at `q`). -/
  qR : ∀ j : ℤ, DR.U.X j →ₗ[S] Lq.X j
  /-- The `q`-component of `U_P` (in the unramified condition). -/
  qP : ∀ j : ℤ, UP.X j →ₗ[S] Uq.X j
  /-- The `q`-component of `U_{P⊥}`. -/
  qPp : ∀ i : ℤ, DPp.U.X i →ₗ[S] Uq'.X i
  /-- The relaxed homotopy on `U_S × U_R`. -/
  hR : ∀ i j k : ℤ, i + j = k + 1 → US.X i →ₗ[S] DR.U.X j →ₗ[S] EL.X k
  /-- … is the sum of the old per-place homotopies (the strict condition at `q` is zero). -/
  hR_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : US.X i) (y : DR.U.X j),
    hR i j k h x y = ∑ v ∈ old, hv v i j k h (pS v i x) (pR v j y)
  isoR : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : US.X i) (y : DR.U.X j),
    EL.d k k₁ hk (hR i j k h x y) + hR i₁ j k₁ (by omega) (US.d i i₁ hi x) y +
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn i •
          hR i j₁ k₁ (by omega) x (DR.U.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) ((ghomComp fS DPp.ι).f i i rfl x) (DR.ι.f j j rfl y)
  /-- The primitive homotopy on `U_{P⊥} × U_P`. -/
  hP : ∀ i j k : ℤ, i + j = k + 1 → DPp.U.X i →ₗ[S] UP.X j →ₗ[S] EL.X k
  /-- … is the sum of the same old per-place homotopies and the homotopy at `q`. -/
  hP_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : DPp.U.X i) (y : UP.X j),
    hP i j k h x y = ∑ v ∈ old, hv v i j k h (pPp v i x) (pP v j y) + hq i j k h (qPp i x) (qP j y)
  isoP : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : DPp.U.X i) (y : UP.X j),
    EL.d k k₁ hk (hP i j k h x y) + hP i₁ j k₁ (by omega) (DPp.U.d i i₁ hi x) y +
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.sgn i • hP i j₁ k₁ (by omega) x (UP.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) (DPp.ι.f i i rfl x) ((ghomComp fP DR.ι).f j j rfl y)
  /-- Every old condition is retained by `f_P`: it is the identity on each old summand. -/
  ret_P : ∀ (v : ι) (j : ℤ) (y : UP.X j), pR v j (fP.f j j rfl y) = pP v j y
  /-- Every old orthogonal condition is retained by `f_S`. -/
  ret_S : ∀ (v : ι) (i : ℤ) (x : US.X i), pPp v i (fS.f i i rfl x) = pS v i x
  /-- At `q`, `f_P` is the map of the unramified condition into the full complex. -/
  q_P : ∀ (j : ℤ) (y : UP.X j), qR j (fP.f j j rfl y) = ιq.f j j rfl (qP j y)
  /-- At `q`, `f_S` is `0 → U_q^{ur}`: the strict condition at `q` is zero. -/
  q_S : ∀ (i : ℤ) (x : US.X i), qPp i (fS.f i i rfl x) = 0

variable {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U} {fS : GHom US DPp.U}

/-- **The retained homotopies** (tex L4163–4165), PROVED from the place-by-place retention:
`h_R(u, f_P v) = h_P(f_S u, v)`. -/
theorem PlaceRetention2.retained (R : PlaceRetention2 DR DPp fP fS) (i j k : ℤ)
    (h : i + j = k + 1) (x : US.X i) (y : UP.X j) :
    R.hR i j k h x (fP.f j j rfl y) = R.hP i j k h (fS.f i i rfl x) y := by
  rw [R.hR_eq, R.hP_eq, R.q_S, map_zero, LinearMap.zero_apply, add_zero]
  exact Finset.sum_congr rfl fun v _ => by rw [R.ret_P, R.ret_S]

/-- **The `RetainedPairing` of the place-by-place retention data.** -/
def PlaceRetention2.toRetainedPairing (R : PlaceRetention2 DR DPp fP fS) :
    RetainedPairing DR DPp fP fS where
  E := R.E
  EL := R.EL
  resE := R.resE
  cupG := R.cupG
  cupL := R.cupL
  compat := R.compat
  hR := R.hR
  isoR := R.isoR
  hP := R.hP
  isoP := R.isoP
  retained := R.retained

/-- **Forgetting the tame model**: every `PlaceRetention` gives a `PlaceRetention2` (with
`Lq = NP.Lq`, `Uq = NP.Uq`, `ιq = NP.ιq`). -/
def _root_.ZInQ.Contrib.CloudB3RC53.CommonCoordinate.PlaceRetention.toPlaceRetention2
    (R : PlaceRetention DR DPp fP fS) : PlaceRetention2 DR DPp fP fS where
  E := R.E
  EL := R.EL
  resE := R.resE
  cupG := R.cupG
  cupL := R.cupL
  compat := R.compat
  ι := R.ι
  old := R.old
  Uo := R.Uo
  Uo' := R.Uo'
  hv := R.hv
  Lq := R.NP.Lq
  Uq := R.NP.Uq
  ιq := R.NP.ιq
  Uq' := R.Uq'
  hq := R.hq
  pR := R.pR
  pP := R.pP
  pS := R.pS
  pPp := R.pPp
  qR := R.qR
  qP := R.qP
  qPp := R.qPp
  hR := R.hR
  hR_eq := R.hR_eq
  isoR := R.isoR
  hP := R.hP
  hP_eq := R.hP_eq
  isoP := R.isoP
  ret_P := R.ret_P
  ret_S := R.ret_S
  q_P := R.q_P
  q_S := R.q_S

/-- The retained pairing is unchanged by forgetting the tame model (definitional). -/
theorem toPlaceRetention2_toRetainedPairing (R : PlaceRetention DR DPp fP fS) :
    R.toPlaceRetention2.toRetainedPairing = R.toRetainedPairing :=
  rfl

/-- **Non-vacuity of `PlaceRetention2`** (LESSON 2): batch 3's example. -/
theorem nonempty_placeRetention2 (S : Type u) [CommRing S] :
    Nonempty (PlaceRetention2 (relSel S) (constSel S) (constId S) (constId S)) :=
  ⟨(examplePlaceRetention S).toPlaceRetention2⟩

/-- **The triangular-basis functionals are paired functionals of retained Selmer data, the new
place given by its actual complexes** (tex L4159–4177). As `SelmerFunctionals`, with a
`PlaceRetention2`. -/
def SelmerFunctionals2 {K : Type} [CommRing K] {n : ℕ} {κ : Type} (wR : Fin n ⊕ κ → K)
    (wP : Fin n → K) (eK : K) : Prop :=
  ∃ (S : CommRingCat.{0}) (DR DPp : SelData S) (UP US : GCx S) (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) (R : PlaceRetention2 DR DPp fP fS)
    (tr : (coneCx R.toRetainedPairing.QP.resE).X 3 →ₗ[S] S)
    (_ : ∀ z, tr ((coneCx R.toRetainedPairing.QP.resE).d 2 3 rfl z) = 0)
    (zS : (selCx (restrictData DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (_ : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (φP : Fin n → (selCx (restrictData DR fP)).X 2)
    (_ : ∀ i, (selCx (restrictData DR fP)).d 2 3 rfl (φP i) = 0)
    (φR : Fin n ⊕ κ → (selCx DR).X 2)
    (_ : ∀ i, φR (Sum.inl i) = (changeMap DR fP).f 2 2 rfl (φP i))
    (ψ : S →+* K),
    ψ e = eK ∧
      (∀ j, wR j = ψ (pairedFun R.toRetainedPairing.QR
        (tr : (coneCx R.toRetainedPairing.QR.resE).X 3 →ₗ[S] S) zS (φR j))) ∧
      (∀ i, wP i = ψ (pairedFun R.toRetainedPairing.QP tr zP (φP i)))

/-- **`w_R|old = e_q w_P`** (tex L4170–4177), PROVED from the naturality of the cup pairing. -/
theorem SelmerFunctionals2.restrict {K : Type} [CommRing K] {n : ℕ} {κ : Type}
    {wR : Fin n ⊕ κ → K} {wP : Fin n → K} {eK : K} (h : SelmerFunctionals2 wR wP eK) (i : Fin n) :
    wR (Sum.inl i) = eK * wP i := by
  obtain ⟨S, DR, DPp, UP, US, fP, fS, R, tr, htr, zS, zP, e, b, hlift, φP, hφP, φR, hφR, ψ,
    he, hwR, hwP⟩ := h
  rw [hwR, hwP, hφR, pairedFunctional_natural R.toRetainedPairing tr htr zS zP e b hlift (φP i)
    (hφP i), map_mul, he]

/-- `SelmerFunctionals` gives `SelmerFunctionals2`. -/
theorem _root_.ZInQ.Contrib.CloudB3RC53.CommonCoordinate.SelmerFunctionals.toSelmerFunctionals2
    {K : Type} [CommRing K] {n : ℕ} {κ : Type} {wR : Fin n ⊕ κ → K} {wP : Fin n → K} {eK : K}
    (h : SelmerFunctionals wR wP eK) : SelmerFunctionals2 wR wP eK := by
  obtain ⟨S, DR, DPp, UP, US, fP, fS, R, tr, htr, zS, zP, e, b, hlift, φP, hφP, φR, hφR, ψ,
    he, hwR, hwP⟩ := h
  exact ⟨S, DR, DPp, UP, US, fP, fS, R.toPlaceRetention2, tr, htr, zS, zP, e, b, hlift, φP, hφP,
    φR, hφR, ψ, he, hwR, hwP⟩

/-- **One relaxation step from retained naturality, the new place given by its actual
complexes** (tex L4159–4193): `NaturalStep` with `SelmerFunctionals2`. -/
def NaturalStep2 {K : Type} [CommRing K] (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (uprim urel ε : K) (unitR unitP : K → Prop) : Prop :=
  ∃ (n : ℕ) (DPa PP QP : Matrix (Fin n) (Fin n) K)
    (DRa PR QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (zPa wPa : Fin n → K)
    (zRa wRa : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K),
    IsUnit PP.det ∧ IsUnit QP.det ∧ IsUnit PR.det ∧ IsUnit QR.det ∧
    PR * DRa * QR = fromBlocks (PP * DPa * QP) X 0 (twoPlaceBlock F q z zi) ∧
    (∀ i, (QR⁻¹ *ᵥ zRa) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zPa) i) ∧
    SelmerFunctionals2 (wRa ᵥ* PR⁻¹) (wPa ᵥ* PP⁻¹) (pointFactor a z zi) ∧
    IsCoordOn DRa zRa wRa urel ∧ IsClassFunctionalCoord DPa zPa wPa uprim ∧
    (PP * DPa * QP).adjugate ≠ 0 ∧
    unitR (PR.det * QR.det) ∧ unitP (PP.det * QP.det) ∧
    ε = qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)

/-- `NaturalStep2` gives `ActualStep`: the functional relation is PROVED by
`SelmerFunctionals2.restrict`. -/
theorem NaturalStep2.toActualStep {K : Type} [CommRing K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop}
    (h : NaturalStep2 F q qi a z zi uprim urel ε unitR unitP) :
    ActualStep F q qi a z zi uprim urel ε unitR unitP := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS, h8, h9,
    h10, h11, h12, h13⟩ := h
  exact ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS.restrict,
    h8, h9, h10, h11, h12, h13⟩

/-- `NaturalStep` gives `NaturalStep2`. -/
theorem _root_.ZInQ.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep.toNaturalStep2
    {K : Type} [CommRing K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop}
    (h : NaturalStep F q qi a z zi uprim urel ε unitR unitP) :
    NaturalStep2 F q qi a z zi uprim urel ε unitR unitP := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6, hS, h8, h9,
    h10, h11, h12, h13⟩ := h
  exact ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, h1, h2, h3, h4, h5, h6,
    hS.toSelmerFunctionals2, h8, h9, h10, h11, h12, h13⟩

/-! ### RC0's consumer -/

/-- **The support-triangle data at one address, each step a `NaturalStep2`** (Lemma
`ex:arith-common-coordinate`, tex 4142–4328): round 4's `CommonCoordinateTrianglesG` with the
retention at the new place stated over its actual complexes. -/
structure CommonCoordinateTrianglesG2 {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type 1 where
  /-- the coefficient ring `𝒪[G]` -/
  R : Type
  [commR : CommRing R]
  /-- the evaluation at the character of the address -/
  chi : R →+* PowerSeries ℚ_[2]
  /-- `v_q = (l_q/e_q² − 1)/2` -/
  v : ℕ → R
  /-- the inertia generators `g_q` of the universal quadratic character -/
  g : ℕ → R
  /-- the quotient factors `l_q` -/
  l : ℕ → R
  /-- the point factors `e_q` -/
  e : ℕ → R
  /-- their inverses -/
  ei : ℕ → R
  /-- the character is the quadratic character of `x`: `x(g_q) = (−1)^{λ_q(x)}` -/
  hchi : ∀ q ∈ Fam.Q, chi (g q) = (-1) ^ (Fam.lam q x).val
  /-- `x(l_q) x(e_q)^{-2} = 1 + 2 x(v_q)` -/
  hratio : ∀ q ∈ Fam.Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q)
  /-- `e_q` is invertible at the character -/
  hinv : ∀ q ∈ Fam.Q, chi (e q) * chi (ei q) = 1
  /-- the relaxed coordinate -/
  urel : PowerSeries ℚ_[2]
  /-- the corrected coordinate is `η u_rel` at the address -/
  hutilde : D.uTilde Fam x = chi (Central.eta Fam.Q v g) * urel
  /-- the Frobenius matrices at the unused primes -/
  F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- their traces `a_p` -/
  a : ℕ → PowerSeries ℚ_[2]
  /-- the scalar Frobenius values `z` -/
  z : ℕ → PowerSeries ℚ_[2]
  /-- their inverses `z⁻¹` -/
  zi : ℕ → PowerSeries ℚ_[2]
  /-- `tr Fr_p = a_p` -/
  ha : ∀ p ∈ unusedAt Fam x, (F p).trace = a p
  /-- `det Fr_p = p` -/
  hd : ∀ p ∈ unusedAt Fam x, (F p).det = PowerSeries.C (p : ℚ_[2])
  /-- `z z⁻¹ = 1` -/
  hzi : ∀ p ∈ unusedAt Fam x, z p * zi p = 1
  /-- `l_p = det(1 − p⁻¹ z Fr_p) det(1 − p⁻¹ z⁻¹ Fr_p)` at the character -/
  hl : ∀ p ∈ unusedAt Fam x, chi (l p) =
    quotientFactor (F p) (PowerSeries.C ((p : ℚ_[2])⁻¹)) (z p) (zi p)
  /-- `e_p = a_p − z − z⁻¹` at the character -/
  he : ∀ p ∈ unusedAt Fam x, chi (e p) = pointFactor (a p) (z p) (zi p)
  /-- the coordinates relaxed at `T ⊆ U` -/
  u : Finset ℕ → PowerSeries ℚ_[2]
  /-- relaxed at every unused prime: `u_rel` -/
  hrel : u (unusedAt Fam x) = urel
  /-- relaxed at none: `u_prim,x` -/
  hprim : u ∅ = D.uPrim Fam x
  /-- the step units `ε_p` -/
  eps : ℕ → PowerSeries ℚ_[2]
  /-- each relaxation step is a `NaturalStep2` -/
  hstep : ∀ T ⊆ unusedAt Fam x, ∀ p ∈ unusedAt Fam x, p ∉ T →
    NaturalStep2 (F p) (PowerSeries.C (p : ℚ_[2])) (PowerSeries.C ((p : ℚ_[2])⁻¹)) (a p)
      (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit

attribute [instance] CommonCoordinateTrianglesG2.commR

/-- **RC0's `CommonCoordinateTriangles` from `CommonCoordinateTrianglesG2`** (PROVED; the
bookkeeping is round 4's `CommonCoordinateTrianglesG.toN`, the steps through
`NaturalStep2.toActualStep`). -/
def CommonCoordinateTrianglesG2.toTriangles {ℓ : ℕ} {D : RCData ℓ} {Fam : Family}
    {x : Addr Fam.b} (M : CommonCoordinateTrianglesG2 D Fam x) (hodd : ∀ q ∈ Fam.Q, Odd q) :
    CommonCoordinateTriangles D Fam x where
  R := M.R
  chi := M.chi
  Q := Fam.Q
  v := M.v
  g := M.g
  l := M.l
  e := M.e
  ei := M.ei
  hsign q hq := by
    rw [M.hchi q hq]
    exact neg_one_pow_eq_or _ _
  hratio := M.hratio
  hinv := M.hinv
  urel := M.urel
  U := unusedAt Fam x
  hU q := by
    rw [mem_unusedAt]
    constructor
    · rintro ⟨hq, h0⟩
      refine ⟨hq, ?_⟩
      rw [M.hchi q hq, h0]
      simp
    · rintro ⟨hq, h1⟩
      refine ⟨hq, (neg_one_pow_val_eq_one_iff _).mp ?_⟩
      rw [← M.hchi q hq]
      exact h1
  hutilde := M.hutilde
  qn p := p
  hodd p hp := hodd p (mem_unusedAt.mp hp).1
  F := M.F
  a := M.a
  z := M.z
  zi := M.zi
  ha := M.ha
  hd := M.hd
  hl := M.hl
  he := M.he
  u := M.u
  hrel := M.hrel
  hprim := M.hprim
  eps := M.eps
  hstep T hT p hp hpT := (M.hstep T hT p hp hpT).toActualStep

/-- **The inputs of (4.7), each relaxation step a `NaturalStep2`** (tex 4142–4328). -/
def CommonCoordinateInputsG2 {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateTrianglesG2 D F x)

/-- **RC0's `CommonCoordinateInputs` from `CommonCoordinateInputsG2`** (PROVED). -/
theorem commonCoordinateInputs_of_G2 {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG2 D) :
    CommonCoordinateInputs D :=
  commonCoordinateInputs_of_triangles fun Co Ce F hF x => by
    obtain ⟨M⟩ := h Co Ce F hF x
    exact ⟨M.toTriangles (odd_of_finalFamilyAt hF)⟩

/-- **`RCSteps.common_coordinate` from `CommonCoordinateInputsG2`** ((4.7), tex 4142–4328;
PROVED). -/
theorem commonCoordinateTarget_of_G2 {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG2 D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_inputs (commonCoordinateInputs_of_G2 h)

/-- Round 4's triangle data give `CommonCoordinateTrianglesG2` (forgetting the tame model). -/
def _root_.ZInQ.Manuscript.RC.Wiring.CommonCoordinateTrianglesG.toG2 {ℓ : ℕ} {D : RCData ℓ}
    {Fam : Family} {x : Addr Fam.b} (M : CommonCoordinateTrianglesG D Fam x) :
    CommonCoordinateTrianglesG2 D Fam x where
  R := M.R
  chi := M.chi
  v := M.v
  g := M.g
  l := M.l
  e := M.e
  ei := M.ei
  hchi := M.hchi
  hratio := M.hratio
  hinv := M.hinv
  urel := M.urel
  hutilde := M.hutilde
  F := M.F
  a := M.a
  z := M.z
  zi := M.zi
  ha := M.ha
  hd := M.hd
  hzi := M.hzi
  hl := M.hl
  he := M.he
  u := M.u
  hrel := M.hrel
  hprim := M.hprim
  eps := M.eps
  hstep T hT p hp hpT := (M.hstep T hT p hp hpT).toNaturalStep2

/-- `CommonCoordinateInputsG2` is weaker than round 4's `CommonCoordinateInputsG` (PROVED). -/
theorem commonCoordinateInputsG2_of_G {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG D) :
    CommonCoordinateInputsG2 D := fun Co Ce F hF x => by
  obtain ⟨M⟩ := h Co Ce F hF x
  exact ⟨M.toG2⟩

/-- **Non-vacuity of `CommonCoordinateTrianglesG2` at a family with an unused graph prime**
(LESSON 2): round 4's witness at `q = 3`. -/
theorem nonempty_trianglesG2_three :
    Nonempty (CommonCoordinateTrianglesG2 exDataThree famThree 0) :=
  ⟨(trianglesG_three exDataThree rfl rfl).toG2⟩

end ZInQ.Contrib.CloudB3RC53.GenuineInst

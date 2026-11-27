import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange

/-!
# Common coordinate, part 1: naturality of the cup pairing and `λ_R ∘ i = e_q λ_P`

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex L4142–4328), proof, tex L4159–4180:

> Let `i : C_P → C_R` be the primitive-to-relaxed map, and let `j : C_S → C_{P⊥}` be the paired
> strict-to-primitive map. All old orthogonal conditions and their homotopies are retained. At `q`
> these are the maps from the unramified condition to the full condition and from zero to the
> unramified condition. Naturality of the cup pairing [Nekovář, 6.4.1–6.4.3] gives
> `β_R(v, iw) = β_P(jv, w)`. [...] The generic paired strict lift satisfies `j z_S = e_q^c z_{P⊥}`.
> Conjugation sends `z` to `z⁻¹`, so `e_q^c = e_q`. Consequently `λ_R ∘ i = e_q λ_P`.

Over the Selmer complexes and the cup product of `PairedFunctional/SelmerPairing.lean`
(Nekovář's `∪_{res, h}`), with the change-of-condition maps `changeMap` of
`SelmerDuality/SupportChange.lean`:

* `cup_naturality` (PROVED; the content of Nekovář 6.4.1–6.4.3 used here): if the two pairings
  share the global and local cup products and the isotropy homotopies are retained
  (`h_R(u, f_P v) = h_P(f_S u, v)`), then `β_R(v, i w) = β_P(j v, w)` on the nose.
* `pairedFunctional_natural` (PROVED, tex L4170–4177): if `j z_S = e z_{P⊥} + d b` (the paired
  strict lift, up to its retained boundary), then on cocycles `w` of `C_P`,
  `λ_R(i w) = e · λ_P(w)` with `λ_R = tr(z_S ∪ ·)`, `λ_P = tr(z_{P⊥} ∪ ·)`.
* `e_q^c = e_q` is RC15's `pointFactor_swap`.

**Classification.** PROVED (the naturality is proved for the abstract model; the identification
of the abstract complexes with the actual Galois cochains is the same open identification as for
`SelmerDuality`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {S : Type u} [CommRing S]

section Naturality

variable (DR DPp : SelData S) {UP US : GCx S} (fP : GHom UP DR.U) (fS : GHom US DPp.U)

/-- **Retained pairing data** for the primitive and relaxed Selmer complexes (tex L4163–4166):
one global and one local cup product and target, shared by both pairings, and two isotropy
homotopies — `h_R` for `(U_S, U_R)` and `h_P` for `(U_{P⊥}, U_P)` — retained along the
condition maps: `h_R(u, f_P v) = h_P(f_S u, v)`. -/
structure RetainedPairing where
  /-- Global target. -/
  E : GCx S
  /-- Local target. -/
  EL : GCx S
  /-- Restriction on the target. -/
  resE : GHom E EL
  /-- Global cup product. -/
  cupG : GPair DPp.G DR.G E
  /-- Local cup product. -/
  cupL : GPair DPp.L DR.L EL
  compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
    (hk : k = k') (a : DPp.G.X i) (b : DR.G.X j),
    resE.f k k' hk (cupG.P i j k h a b) =
      cupL.P i' j' k' h' (DPp.res.f i i' hi a) (DR.res.f j j' hj b)
  /-- The relaxed homotopy on `U_S × U_R`. -/
  hR : ∀ i j k : ℤ, i + j = k + 1 → US.X i →ₗ[S] DR.U.X j →ₗ[S] EL.X k
  isoR : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (u : US.X i) (v : DR.U.X j),
    EL.d k k₁ hk (hR i j k h u v) + hR i₁ j k₁ (by omega) (US.d i i₁ hi u) v +
        sgn i • hR i j₁ k₁ (by omega) u (DR.U.d j j₁ hj v) =
      cupL.P i j k₁ (by omega) ((ghomComp fS DPp.ι).f i i rfl u) (DR.ι.f j j rfl v)
  /-- The primitive homotopy on `U_{P⊥} × U_P`. -/
  hP : ∀ i j k : ℤ, i + j = k + 1 → DPp.U.X i →ₗ[S] UP.X j →ₗ[S] EL.X k
  isoP : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (u : DPp.U.X i) (v : UP.X j),
    EL.d k k₁ hk (hP i j k h u v) + hP i₁ j k₁ (by omega) (DPp.U.d i i₁ hi u) v +
        sgn i • hP i j₁ k₁ (by omega) u (UP.d j j₁ hj v) =
      cupL.P i j k₁ (by omega) (DPp.ι.f i i rfl u) ((ghomComp fP DR.ι).f j j rfl v)
  /-- The homotopies are retained along the condition maps. -/
  retained : ∀ (i j k : ℤ) (h : i + j = k + 1) (u : US.X i) (v : UP.X j),
    hR i j k h u (fP.f j j rfl v) = hP i j k h (fS.f i i rfl u) v

variable {DR DPp fP fS}

/-- The relaxed pairing `β_R : C_S × C_R → Cone(E → E_L)[−1]`. -/
def RetainedPairing.QR (T : RetainedPairing DR DPp fP fS) :
    SelPairData (restrictData DPp fS) DR where
  E := T.E
  EL := T.EL
  resE := T.resE
  cupG := T.cupG
  cupL := T.cupL
  compat := T.compat
  hU := T.hR
  isotropy := T.isoR

/-- The primitive pairing `β_P : C_{P⊥} × C_P → Cone(E → E_L)[−1]`. -/
def RetainedPairing.QP (T : RetainedPairing DR DPp fP fS) :
    SelPairData DPp (restrictData DR fP) where
  E := T.E
  EL := T.EL
  resE := T.resE
  cupG := T.cupG
  cupL := T.cupL
  compat := T.compat
  hU := T.hP
  isotropy := T.isoP

/-- **Naturality of the cup pairing** (tex L4163–4168; the content of Nekovář, *Selmer
complexes*, 6.4.1–6.4.3, as cited, proved here for the abstract model): with
`i = changeMap DR fP : C_P → C_R` and `j = changeMap DPp fS : C_S → C_{P⊥}`,
`β_R(v, i w) = β_P(j v, w)`. -/
theorem cup_naturality (T : RetainedPairing DR DPp fP fS) (i j k : ℤ) (h : i + j = k)
    (c : (selCx (restrictData DPp fS)).X i) (c' : (selCx (restrictData DR fP)).X j) :
    selCup T.QR i j k h c ((changeMap DR fP).f j j rfl c') =
      selCup T.QP i j k h ((changeMap DPp fS).f i i rfl c) c' := by
  obtain ⟨a, u, x⟩ := c
  obtain ⟨b, v, y⟩ := c'
  change selCupFun T.QR i j k h (a, u, x) (b, fP.f j j rfl v, y) =
    selCupFun T.QP i j k h (a, fS.f i i rfl u, x) (b, v, y)
  have e1 : T.QR.hU i j (k - 1) (by omega) u (fP.f j j rfl v) =
      T.QP.hU i j (k - 1) (by omega) (fS.f i i rfl u) v := T.retained i j (k - 1) (by omega) u v
  simp only [selCupFun]
  rw [e1]
  rfl

/-- The paired functional `λ(w) = tr(z ∪ w)` on degree two. -/
def pairedFun {D D' : SelData S} (Q : SelPairData D D') (tr : (coneCx Q.resE).X 3 →ₗ[S] S)
    (z : (selCx D).X 1) : (selCx D').X 2 →ₗ[S] S :=
  tr.comp (selCup Q 1 2 3 rfl z)

/-- **`λ_R ∘ i = e λ_P`** (tex L4170–4177). Let `T` be retained pairing data, `tr` a trace of
degree three killing coboundaries, `z_S ∈ C_S^1`, `z_{P⊥} ∈ C_{P⊥}^1` and `e ∈ S` with
`j z_S = e z_{P⊥} + d b` (the paired strict lift, with its retained boundary `b`). Then for every
cocycle `w ∈ C_P^2`, `λ_R(i w) = e · λ_P(w)`. -/
theorem pairedFunctional_natural (T : RetainedPairing DR DPp fP fS)
    (tr : (coneCx T.QP.resE).X 3 →ₗ[S] S)
    (htr : ∀ z, tr ((coneCx T.QP.resE).d 2 3 rfl z) = 0)
    (zS : (selCx (restrictData DPp fS)).X 1) (zP : (selCx DPp).X 1) (e : S)
    (b : (selCx DPp).X 0)
    (hlift : (changeMap DPp fS).f 1 1 rfl zS = e • zP + (selCx DPp).d 0 1 rfl b)
    (w : (selCx (restrictData DR fP)).X 2)
    (hw : (selCx (restrictData DR fP)).d 2 3 rfl w = 0) :
    pairedFun T.QR (tr : (coneCx T.QR.resE).X 3 →ₗ[S] S) zS ((changeMap DR fP).f 2 2 rfl w) =
      e * pairedFun T.QP tr zP w := by
  show tr (selCup T.QR 1 2 3 rfl zS ((changeMap DR fP).f 2 2 rfl w)) =
    e * tr (selCup T.QP 1 2 3 rfl zP w)
  rw [cup_naturality T 1 2 3 rfl zS w, hlift]
  erw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [smul_eq_mul]
  -- the boundary term: `tr(d b ∪ w) = tr(d(b ∪ w)) = 0` as `d w = 0`
  have hl := selmerCupLeibniz_proof S DPp (restrictData DR fP) T.QP 0 1 2 3 2 3 rfl rfl rfl rfl b w
  rw [hw] at hl
  erw [map_zero, smul_zero, add_zero] at hl
  have h0 := htr (selCup T.QP 0 2 2 rfl b w)
  rw [hl] at h0
  rw [h0, add_zero]

end Naturality

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate

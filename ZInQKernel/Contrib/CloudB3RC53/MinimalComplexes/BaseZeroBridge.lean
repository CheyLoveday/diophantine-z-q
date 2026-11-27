import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.MinimalModel
import ZInQKernel.Contrib.OneProof.RC.Central.BaseZero

/-!
# RC53 MinimalComplexes: the central two-term model fed to the base-zero lemma

Lemma `ex:arith-base-zero` (tex L4330–4373; proof L4346–4366): "Full Selmer corank one gives central
dimensions `(1,1)` in degrees one and two and zero in every other degree. [...] Over the DVR `A`, a
bounded finite free complex decomposes, by successive Smith reductions, into free zero-differential
summands and two-term disks [...]". The central lane's `baseZero_core`
(`RC/Central/BaseZero.lean`) takes a residue map `ρ : A →+* k` killing the maximal ideal, a two-term
model `D : Matrix (Fin (m + 1)) (Fin (m + 1)) A` and `hcentral : (D.map ρ).rank = m`.

`MinimalModel.lean` computes the central dimensions over Mathlib's residue field `A/𝔪`. Here they are
computed with an **arbitrary** residue map `ρ : A →+* k` to a field killing `𝔪` (for the genuine
`A = Λ_(t)`, `ρ` is the residue map to `ℚ₂`), so no field isomorphism with `IsLocalRing.residue` is
needed: every statement below holds verbatim for every such `ρ` (and `IsLocalRing.residue` itself is
one, `residue_kills_maximal`).

Nodes (PROVED):
* `MinimalPartDimsAt`: for any residue map `ρ`, the minimal part of a split form has, in each degree,
  the size `dim_k Hⁿ(K ⊗_ρ k)` (rank–nullity with `ρ`).
* `CentralTwoTermModelAt`: if `Hⁿ(K ⊗_ρ k)` vanishes for `n ∉ {1, 2}` and is one-dimensional in
  degrees one and two, then after a degree-preserving change of bases `K` is unit disks plus
  `[A --δ--> A]` in degrees one and two, and the `1 × 1` matrix `D = (δ)` satisfies
  `hcentral : (D.map ρ).rank = 0` (RC15's hypothesis with `m = 0`).
* `BaseZeroFromComplex`: over a DVR `A` with fraction field `F` and any residue map `ρ`, for such a
  complex the conclusion of `baseZero_core` holds for the produced model `D` and every integral cycle
  `z`, integral functional `w`, generic coordinate `uprim` and `ε₀` satisfying `baseZero_core`'s
  remaining hypotheses: the inputs of `baseZero_core` are produced exactly.
-/

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open Matrix

universe u v

section At

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Type*} [Fintype I] [DecidableEq I]
  {k : Type*} [Field k]

/-- Mathlib's residue map kills the maximal ideal. -/
theorem residue_kills_maximal : ∀ x ∈ IsLocalRing.maximalIdeal R, IsLocalRing.residue R x = 0 :=
  fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx

/-- The degree-`n` columns of `d ⊗_ρ k`. -/
noncomputable def resColsAt (ρ : R →+* k) (deg : I → ℤ) (d : Matrix I I R) (n : ℤ) :
    Matrix I {a // deg a = n} k :=
  (d.map ρ).submatrix id Subtype.val

/-- `dim_k Hⁿ(K ⊗_ρ k)` by rank–nullity: `dim (K ⊗ k)ⁿ − rank d̄ⁿ − rank d̄ⁿ⁻¹`. -/
noncomputable def resDimAt (ρ : R →+* k) (deg : I → ℤ) (d : Matrix I I R) (n : ℤ) : ℤ :=
  (Fintype.card {a // deg a = n} : ℤ) - (resColsAt ρ deg d n).rank -
    (resColsAt ρ deg d (n - 1)).rank

/-- `resDimAt` for Mathlib's residue map is `resDim` of `MinimalModel.lean`. -/
theorem resDimAt_residue (deg : I → ℤ) (d : Matrix I I R) (n : ℤ) :
    resDimAt (IsLocalRing.residue R) deg d n = resDim deg d n := rfl

theorem resColsAt_conj (ρ : R →+* k) {deg : I → ℤ} {P d Q : Matrix I I R} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (hP : IsDegPreserving deg P) (hQ : IsDegPreserving deg Q) (n : ℤ) :
    (resColsAt ρ deg (P * d * Q) n).rank = (resColsAt ρ deg d n).rank := by
  have hPm : P.map ρ * Q.map ρ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ ρ.map_zero ρ.map_one]
  have hQm : Q.map ρ * P.map ρ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ ρ.map_zero ρ.map_one]
  have hblk := block_mul_degP deg (Q.map ρ) (P.map ρ) (hP.map ρ) hQm n
  unfold resColsAt
  rw [Matrix.map_mul, Matrix.map_mul, cols_mul_degP deg _ _ (hQ.map ρ) n]
  have : (P.map ρ * d.map ρ).submatrix id (Subtype.val : {a // deg a = n} → I) =
      P.map ρ * (d.map ρ).submatrix id Subtype.val := by
    ext x a; simp [mul_apply]
  rw [this, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_right_inverse hblk),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse hPm)]

theorem split_at (ρ : R →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0)
    {D : Matrix I I R} {kind : I → Fin 3} {partner : I → I}
    (hS : SplitForm D kind partner) (y x : I) :
    D.map ρ y x = if kind x = 1 ∧ y = partner x then 1 else 0 := by
  obtain ⟨s1, -, s3, s4⟩ := hS
  rw [map_apply]
  split_ifs with h
  · obtain ⟨hk, rfl⟩ := h
    rw [(s1 x hk).2.2, map_one]
  · by_cases h0 : D y x = 0
    · rw [h0, map_zero]
    · rcases s3 x y h0 with ⟨c1, c2⟩ | c
      · exact hρ _ (s4 x y c1 c2)
      · exact absurd c h

theorem rank_resColsAt_split (ρ : R →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0)
    (deg : I → ℤ) {D : Matrix I I R} {kind : I → Fin 3}
    {partner : I → I} (hS : SplitForm D kind partner) (n : ℤ) :
    (resColsAt ρ deg D n).rank = Fintype.card {x : {a // deg a = n} // kind x.1 = 1} := by
  set S := {x : {a // deg a = n} // kind x.1 = 1}
  have hinv : ∀ s : S, partner (partner s.1.1) = s.1.1 := fun s => (hS.1 s.1.1 s.2).2.1
  set A : Matrix I S k := Matrix.of fun y s => if y = partner s.1.1 then 1 else 0 with hA
  set B : Matrix S {a // deg a = n} k := Matrix.of fun s x => if s.1 = x then 1 else 0 with hB
  have hAB : resColsAt ρ deg D n = A * B := by
    ext y x
    rw [resColsAt, submatrix_apply, split_at ρ hρ hS, mul_apply]
    by_cases hk : kind x.1 = 1
    · rw [Finset.sum_eq_single ⟨x, hk⟩]
      · simp [hA, hB, hk]
      · intro s _ hs
        have : s.1 ≠ x := fun h => hs (Subtype.ext h)
        simp [hB, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg (fun h => hk h.1)]
      apply (Finset.sum_eq_zero _).symm
      intro s _
      have : s.1 ≠ x := fun h => hk (h ▸ s.2)
      simp [hB, this]
  have hAA : Aᵀ * A = 1 := by
    ext s s'
    rw [mul_apply, one_apply]
    rw [Finset.sum_eq_single (partner s.1.1)]
    · by_cases hss : s = s'
      · subst hss; simp [hA]
      · have hne : partner s.1.1 ≠ partner s'.1.1 := by
          intro h
          apply hss
          apply Subtype.ext; apply Subtype.ext
          rw [← hinv s, h, hinv s']
        simp [hA, hne, hss]
    · intro y _ hy
      simp [hA, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hBB : B * Bᵀ = 1 := by
    ext s s'
    rw [mul_apply, one_apply, Finset.sum_eq_single s.1]
    · by_cases hss : s = s'
      · subst hss; simp [hB]
      · have hne : s'.1 ≠ s.1 := fun h => hss (Subtype.ext h.symm)
        simp [hB, hne, hss]
    · intro x _ hx
      have : s.1 ≠ x := fun h => hx h.symm
      simp [hB, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hAB]
  apply le_antisymm
  · exact (rank_mul_le_right A B).trans (rank_le_card_height B)
  · have h1 : Fintype.card S ≤ B.rank := by
      rw [← rank_one (R := k) (n := S), ← hBB]
      exact rank_mul_le_left B Bᵀ
    have h2 : B.rank ≤ (A * B).rank := by
      have : Aᵀ * (A * B) = B := by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
      calc B.rank = (Aᵀ * (A * B)).rank := by rw [this]
        _ ≤ (A * B).rank := rank_mul_le_right _ _
    exact h1.trans h2

end At

/-- **The minimal part has the size of the `ρ`-residue cohomology**, for an arbitrary residue map
`ρ : R →+* k` to a field killing `𝔪` (tex L5357–5359, L4346–4358). Classification: PROVED. -/
def MinimalPartDimsAt : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (k : Type u) [Field k] (ρ : R →+* k),
    (∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0) →
    ∀ (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d P Q : Matrix I I R) (kind : I → Fin 3) (partner : I → I),
    IsGradedDiff deg d → P * Q = 1 → Q * P = 1 → IsDegPreserving deg P →
    IsDegPreserving deg Q → SplitForm (P * d * Q) kind partner →
      ∀ n : ℤ, resDimAt ρ deg d n = Fintype.card {x : {a // deg a = n} // kind x.1 = 0}

theorem minimalPartDimsAt_proof : MinimalPartDimsAt.{u, v} := by
  intro R _ _ k _ ρ hρ I _ _ deg d P Q kind partner hg hPQ hQP hP hQ hS n
  have hgD : IsGradedDiff deg (P * d * Q) := IsGradedDiff.conj hP hg hQ
  unfold resDimAt
  rw [← resColsAt_conj ρ hPQ hQP hP hQ n, ← resColsAt_conj ρ hPQ hQP hP hQ (n - 1),
    rank_resColsAt_split ρ hρ deg hS, rank_resColsAt_split ρ hρ deg hS,
    card_deg_eq_kinds deg kind n, card_kind_two deg hgD hS n]
  push_cast
  ring

/-- **The central two-term model for an arbitrary residue map** (tex L4346–4358; RC15
`baseZero_core`'s `D` and `hcentral` with `m = 0`). Let `R` be a local ring, `ρ : R →+* k` a map to a
field killing `𝔪`, and `(I, deg, d)` a bounded complex of finite free `R`-modules whose `ρ`-residue
cohomology vanishes outside degrees one and two and is one-dimensional in degrees one and two. Then
there are a degree-preserving change of bases `P, Q` putting `d` in split form (unit disks plus a
minimal part), the minimal part is spanned by `s₁` (degree one) and `s₂` (degree two), its entry
`δ = (P d Q) s₂ s₁` lies in `𝔪`, and `D = (δ)` satisfies `(D.map ρ).rank = 0`.
Classification: PROVED. -/
def CentralTwoTermModelAt : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (k : Type u) [Field k] (ρ : R →+* k),
    (∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0) →
    ∀ (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d : Matrix I I R), IsGradedDiff deg d → d * d = 0 →
    (∀ n, n ≠ 1 → n ≠ 2 → resDimAt ρ deg d n = 0) → resDimAt ρ deg d 1 = 1 →
    resDimAt ρ deg d 2 = 1 →
      ∃ (P Q : Matrix I I R) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
        P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
        SplitForm (P * d * Q) kind partner ∧
        kind s₁ = 0 ∧ kind s₂ = 0 ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
        (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
        (P * d * Q) s₂ s₁ ∈ IsLocalRing.maximalIdeal R ∧
        ((Matrix.of fun _ _ => (P * d * Q) s₂ s₁ : Matrix (Fin (0 + 1)) (Fin (0 + 1)) R).map
          ρ).rank = 0

theorem centralTwoTermModelAt_proof : CentralTwoTermModelAt.{u, v} := by
  intro R _ _ k _ ρ hρ I _ _ deg d hg hd h0 h1 h2
  obtain ⟨P, Q, kind, partner, hPQ, hQP, hP, hQ, hS⟩ := minimalModelSplit_proof R I deg d hg hd
  have hdim := minimalPartDimsAt_proof R k ρ hρ I deg d P Q kind partner hg hPQ hQP hP hQ hS
  have e1 : Fintype.card {x : {a // deg a = 1} // kind x.1 = 0} = 1 := by
    have := hdim 1; rw [h1] at this; exact_mod_cast this.symm
  have e2 : Fintype.card {x : {a // deg a = 2} // kind x.1 = 0} = 1 := by
    have := hdim 2; rw [h2] at this; exact_mod_cast this.symm
  obtain ⟨t₁, ht₁⟩ := Fintype.card_eq_one_iff.mp e1
  obtain ⟨t₂, ht₂⟩ := Fintype.card_eq_one_iff.mp e2
  refine ⟨P, Q, kind, partner, t₁.1.1, t₂.1.1, hPQ, hQP, hP, hQ, hS, t₁.2, t₂.2, t₁.1.2, t₂.1.2,
    fun x hx => ?_, hS.2.2.2 _ _ t₁.2 t₂.2, ?_⟩
  · by_cases hx1 : deg x = 1
    · left
      have := ht₁ ⟨⟨x, hx1⟩, hx⟩
      rw [← this]
    · by_cases hx2 : deg x = 2
      · right
        have := ht₂ ⟨⟨x, hx2⟩, hx⟩
        rw [← this]
      · exfalso
        have e0 := hdim (deg x)
        rw [h0 _ hx1 hx2] at e0
        have hpos : 0 < Fintype.card {y : {a // deg a = deg x} // kind y.1 = 0} :=
          Fintype.card_pos_iff.mpr ⟨⟨⟨x, rfl⟩, hx⟩⟩
        omega
  · have hz : (Matrix.of fun _ _ => (P * d * Q) t₂.1.1 t₁.1.1 :
        Matrix (Fin (0 + 1)) (Fin (0 + 1)) R).map ρ = 0 := by
      ext i j
      simp only [map_apply, of_apply, Matrix.zero_apply]
      exact hρ _ (hS.2.2.2 _ _ t₁.2 t₂.2)
    rw [hz, rank_zero]

/-- **The base-zero lemma from the actual complex** (tex L4330–4373, with L4346–4358). Let `A` be a
DVR with fraction field `F`, `ρ : A →+* k` a residue map killing `𝔪`, and `(I, deg, d)` a bounded
complex of finite free `A`-modules with `ρ`-central dimensions `(1, 1)` in degrees one and two and
zero elsewhere. Then there is a degree-preserving change of bases to unit disks plus the two-term
model `D = (δ)` in degrees one and two, `hcentral : (D.map ρ).rank = 0` holds, and for every integral
cycle `z` of `D`, integral functional `w`, generic coordinate `uprim` (`IsClassFunctionalCoord`) with
vanishing central cycle, and every `ε₀`, the conclusion of `baseZero_core` holds. This produces
exactly `baseZero_core`'s inputs `D`, `hcentral` (with `m = 0`) for the given `ρ`.
Classification: PROVED (GLUE with `baseZero_core`). -/
def BaseZeroFromComplex : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (F : Type u) [Field F]
    [Algebra A F] [IsFractionRing A F] (k : Type u) [Field k] (ρ : A →+* k),
    (∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) →
    ∀ (I : Type v) [Fintype I] [DecidableEq I]
    (deg : I → ℤ) (d : Matrix I I A), IsGradedDiff deg d → d * d = 0 →
    (∀ n, n ≠ 1 → n ≠ 2 → resDimAt ρ deg d n = 0) → resDimAt ρ deg d 1 = 1 →
    resDimAt ρ deg d 2 = 1 →
      ∃ (P Q : Matrix I I A) (kind : I → Fin 3) (partner : I → I) (s₁ s₂ : I),
        P * Q = 1 ∧ Q * P = 1 ∧ IsDegPreserving deg P ∧ IsDegPreserving deg Q ∧
        SplitForm (P * d * Q) kind partner ∧ deg s₁ = 1 ∧ deg s₂ = 2 ∧
        (∀ x, kind x = 0 → x = s₁ ∨ x = s₂) ∧
        let D : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A := Matrix.of fun _ _ => (P * d * Q) s₂ s₁
        (D.map ρ).rank = 0 ∧
        ∀ (z w : Fin (0 + 1) → A) (uprim : F), D *ᵥ z = 0 →
          ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord (D.map (algebraMap A F))
            (fun i => algebraMap A F (z i)) (fun i => algebraMap A F (w i)) uprim →
          (∀ i, ρ (z i) = 0) → ∀ ε₀ : A,
            (∃ u₀ : A, algebraMap A F u₀ = uprim ∧ ρ u₀ = 0) ∧
              (∃ a : A, algebraMap A F a = algebraMap A F ε₀ * uprim ∧ ρ a = 0)

theorem baseZeroFromComplex_proof : BaseZeroFromComplex.{u, v} := by
  intro A _ _ _ F _ _ _ k _ ρ hρ I _ _ deg d hg hd h0 h1 h2
  obtain ⟨P, Q, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, -, -, hs₁, hs₂, hmin, -, hc⟩ :=
    centralTwoTermModelAt_proof A k ρ hρ I deg d hg hd h0 h1 h2
  refine ⟨P, Q, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, hs₁, hs₂, hmin, hc, ?_⟩
  intro z w uprim hz hu hz0 ε₀
  exact ZInQ.Manuscript.RC.Central.baseZero_core (F := F) ρ hρ _ hc z w hz uprim hu hz0 ε₀

/-- Mathlib's residue map is an admissible `ρ`, and for it `resDimAt` is `resDim`
(`MinimalModel.lean`); so `CentralTwoTermModelAt` contains `CentralTwoTermModel`'s hypotheses
verbatim. PROVED. -/
theorem residue_admissible (R : Type u) [CommRing R] [IsLocalRing R] :
    ∀ x ∈ IsLocalRing.maximalIdeal R, IsLocalRing.residue R x = 0 :=
  residue_kills_maximal

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes

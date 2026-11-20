import ZInQKernel.Contrib.OneProof.RC.Height.SumDifference
import ZInQKernel.Contrib.OneProof.RC.Height.Torsion

/-!
# Lane RC19 (height): a rational free line has index at most two in its native lattice

The 11/5 manuscript (`diophantine_zq.tex`), proof of Proposition `ex:sec7-genus-lower`, lines
2433–2435, before (3.4):

> Each rational free line has index at most two in its native rank-one lattice: conjugation fixes
> the free class, and the norm makes twice the class rational.

This is where the error `|ε| ≤ 2` in (3.4) comes from: if the rational line has index `m` in the
native lattice, the canonical heights of the generators differ by the factor `m² ∈ {1, 4}`, so the
two-adic index valuations move by at most two. This file proves the statement and its height
consequence in the two situations that occur:

* `rational_line_index_le_two`: the rational points `W(ℚ)` inside `W(K)`, `K = ℚ(√k)`, when the
  conjugation `σ` fixes the free class (`σ g ≡ g` modulo torsion); the norm `g + σg` is rational
  and equals `2g` modulo torsion;
* `twisted_line_index_le_two`: the twisted rational points `ι(E^{(hk)}(ℚ))` in `E^{(h)}(K)`, when
  `σ` negates the free class (`σ g ≡ −g`); the anti-norm `g − σg` is `ι` of a rational point of the
  twist and equals `2g` modulo torsion.

In both cases there are integers `m, n` with `q ≡ m g` and `2 g ≡ n q` modulo torsion, `mn = 2`,
and `ĥ(q) = m² ĥ(g)`, so `ĥ(q) = ĥ(g)` or `ĥ(q) = 4 ĥ(g)`.

Version 19 of the manuscript spells the argument out (paragraph "The native genus lattice",
`quartic_v19.tex` lines 18324–18346): the native lattice is identified with `E^{(h)}(K_h)` by the
twist isomorphism, and the involution of `K_h/ℚ` fixes its free quotient because the other
rational character component has rank zero. `conj_sub_isOfFinAddOrder_of_twist_torsion` proves that
implication and `native_lattice_index_le_two` is the resulting statement (the rank inputs are the
forward theorems, supplied elsewhere).

Every declaration in this file is PROVED.
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53

/-- **The index relation**: if `g` is not torsion, `q ≡ m g` and `2 g ≡ n q` modulo torsion, then
`mn = 2`. PROVED. -/
theorem index_mul_eq_two {G : Type*} [AddCommGroup G] {g q : G} (hg : ¬IsOfFinAddOrder g)
    {m n : ℤ} (hq : IsOfFinAddOrder (q - m • g)) (h2 : IsOfFinAddOrder (2 • g - n • q)) :
    m * n = 2 := by
  have h3 : IsOfFinAddOrder ((2 • g - n • q) + n • (q - m • g)) := h2.add hq.zsmul
  have h4 : (2 • g - n • q) + n • (q - m • g) = (2 - m * n) • g := by
    rw [smul_sub, sub_smul, mul_comm m n, mul_smul, two_nsmul, two_zsmul]
    abel
  rw [h4] at h3
  have := eq_zero_of_isOfFinAddOrder_zsmul hg h3
  linarith

/-- An integer with `m ∣ 2` has `m² ∈ {1, 4}`. PROVED. -/
theorem sq_eq_one_or_four_of_mul_eq_two {m n : ℤ} (h : m * n = 2) : m ^ 2 = 1 ∨ m ^ 2 = 4 := by
  have hdvd : m ∣ 2 := ⟨n, h.symm⟩
  have hle : m.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hdvd)
  have h0 : m ≠ 0 := by rintro rfl; simp at h
  have : m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> norm_num

section Height

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- **The height consequence of index at most two**: with `q ≡ m g`, `2 g ≡ n q` modulo torsion and
`g` not torsion, `mn = 2`, `ĥ(q) = m² ĥ(g)`, and `ĥ(q) ∈ {ĥ(g), 4 ĥ(g)}`. PROVED. -/
theorem canonicalHeight_of_index_two {g q : W.Point} (hg : ¬IsOfFinAddOrder g) {m n : ℤ}
    (hq : IsOfFinAddOrder (q - m • g)) (h2 : IsOfFinAddOrder (2 • g - n • q)) :
    m * n = 2 ∧ q.canonicalHeight = (m : ℝ) ^ 2 * g.canonicalHeight ∧
      (q.canonicalHeight = g.canonicalHeight ∨ q.canonicalHeight = 4 * g.canonicalHeight) := by
  have hmn := index_mul_eq_two hg hq h2
  have hh : q.canonicalHeight = (m : ℝ) ^ 2 * g.canonicalHeight := by
    have e : q = m • g + (q - m • g) := by abel
    rw [e, canonicalHeight_add_of_isOfFinAddOrder _ hq, Point.canonicalHeight_zsmul]
  refine ⟨hmn, hh, ?_⟩
  rcases sq_eq_one_or_four_of_mul_eq_two hmn with h1 | h4
  · left
    rw [hh, show (m : ℝ) ^ 2 = 1 by exact_mod_cast h1, one_mul]
  · right
    rw [hh, show (m : ℝ) ^ 2 = 4 by exact_mod_cast h4]

end Height

section Galois

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
  {k : ℚ} (D : QuadData K k)

/-- **The rational line in `W(K)`** (tex 2433–2435). Let `g` generate `W(K)` modulo torsion with
`σ g ≡ g` ("conjugation fixes the free class") and let `q` generate `W(ℚ)` modulo torsion. Then
there are integers `m, n` with `q_K ≡ m g`, `2 g ≡ n q_K`, `mn = 2`, `ĥ_K(q_K) = m² ĥ_K(g)` (index
at most two), and `ĥ_K(q_K) = 2 ĥ_ℚ(q)`. PROVED. -/
theorem rational_line_index_le_two (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (g : (W.baseChange K).toAffine.Point) (hg : IsFreeGenerator g)
    (hconj : IsOfFinAddOrder (conj D g - g))
    (q : (W.baseChange ℚ).toAffine.Point) (hq : IsFreeGenerator q) :
    ∃ m n : ℤ, IsOfFinAddOrder (Point.baseChange ℚ K q - m • g) ∧
      IsOfFinAddOrder (2 • g - n • Point.baseChange ℚ K q) ∧ m * n = 2 ∧
      (Point.baseChange ℚ K q).canonicalHeight = (m : ℝ) ^ 2 * g.canonicalHeight ∧
      (Point.baseChange ℚ K q).canonicalHeight = 2 * q.canonicalHeight := by
  -- the norm `g + σg` is rational
  have hfix : conj D (g + conj D g) = g + conj D g := by rw [map_add, conj_conj, add_comm]
  set r := descend D (g + conj D g) hfix with hr
  have hrK : Point.baseChange ℚ K r = g + conj D g := baseChange_descend D _ hfix
  obtain ⟨n, hn⟩ := hq.2 r
  obtain ⟨m, hm⟩ := hg.2 (Point.baseChange ℚ K q)
  -- `2 g ≡ n q_K`
  have h2 : IsOfFinAddOrder (2 • g - n • Point.baseChange ℚ K q) := by
    have hnK : IsOfFinAddOrder (Point.baseChange ℚ K (r - n • q)) :=
      (Point.baseChange ℚ K).isOfFinAddOrder hn
    rw [map_sub, map_zsmul, hrK] at hnK
    have e : 2 • g - n • Point.baseChange ℚ K q =
        (g + conj D g - n • Point.baseChange ℚ K q) - (conj D g - g) := by
      rw [two_nsmul]; abel
    rw [e]
    exact isOfFinAddOrder_sub' hnK hconj
  obtain ⟨hmn, hh, -⟩ := canonicalHeight_of_index_two hg.1 hm h2
  refine ⟨m, n, hm, h2, hmn, hh, ?_⟩
  rw [canonicalHeight_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]
  norm_num

/-- **The twisted rational line in `E^{(h)}(K)`** (tex 2433–2435, for the companion factor). Let
`g` generate `E^{(h)}(K)` modulo torsion with `σ g ≡ −g` and let `q` generate `E^{(hk)}(ℚ)` modulo
torsion. Then there are integers `m, n` with `ι(q_K) ≡ m g`, `2 g ≡ n ι(q_K)`, `mn = 2`,
`ĥ_K(ι(q_K)) = m² ĥ_K(g)`, and `ĥ_K(ι(q_K)) = 2 ĥ_ℚ(q)`. PROVED. -/
theorem twisted_line_index_le_two (E : WeierstrassCurve ℚ) (h : ℚ) [(qtwist E h).IsElliptic]
    [(qtwist E (h * k)).IsElliptic]
    (g : ((qtwist E h).baseChange K).toAffine.Point) (hg : IsFreeGenerator g)
    (hconj : IsOfFinAddOrder (conj D g + g))
    (q : ((qtwist E (h * k)).baseChange ℚ).toAffine.Point) (hq : IsFreeGenerator q) :
    ∃ m n : ℤ, IsOfFinAddOrder (iota E h k D (Point.baseChange ℚ K q) - m • g) ∧
      IsOfFinAddOrder (2 • g - n • iota E h k D (Point.baseChange ℚ K q)) ∧ m * n = 2 ∧
      (iota E h k D (Point.baseChange ℚ K q)).canonicalHeight =
        (m : ℝ) ^ 2 * g.canonicalHeight ∧
      (iota E h k D (Point.baseChange ℚ K q)).canonicalHeight = 2 * q.canonicalHeight := by
  -- the anti-norm `g − σg` is `ι` of a rational point of the twist
  have hfix := conj_iota_symm_sub E h k D g
  set r := descend D ((iota E h k D).symm (g - conj D g)) hfix with hr
  have hrK : iota E h k D (Point.baseChange ℚ K r) = g - conj D g := by
    rw [hr, baseChange_descend, AddEquiv.apply_symm_apply]
  obtain ⟨n, hn⟩ := hq.2 r
  obtain ⟨m, hm⟩ := hg.2 (iota E h k D (Point.baseChange ℚ K q))
  have h2 : IsOfFinAddOrder (2 • g - n • iota E h k D (Point.baseChange ℚ K q)) := by
    have hnK : IsOfFinAddOrder (iota E h k D (Point.baseChange ℚ K (r - n • q))) :=
      ((iota E h k D).toAddMonoidHom.comp (Point.baseChange ℚ K)).isOfFinAddOrder hn
    rw [map_sub, map_zsmul, map_sub, map_zsmul, hrK] at hnK
    have e : 2 • g - n • iota E h k D (Point.baseChange ℚ K q) =
        (g - conj D g - n • iota E h k D (Point.baseChange ℚ K q)) + (conj D g + g) := by
      rw [two_nsmul]; abel
    rw [e]
    exact hnK.add hconj
  obtain ⟨hmn, hh, -⟩ := canonicalHeight_of_index_two hg.1 hm h2
  refine ⟨m, n, hm, h2, hmn, hh, ?_⟩
  rw [canonicalHeight_twistAddEquiv, canonicalHeight_baseChange,
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]
  norm_num

/-- **The involution fixes the free quotient when the other rational component has rank zero**
(V19, paragraph "The native genus lattice", lines 18336–18342 of `quartic_v19.tex`: "The remaining
involution of `K_h/ℚ` fixes its free quotient: the only other rational character component is the
`h_*`-component, whose rank is zero"). If every point of `E^{(hk)}(ℚ)` is torsion, then
`P − σP` is torsion for every `P ∈ E^{(h)}(K)`: `ι⁻¹(P − σP)` is `σ`-invariant, hence rational on
the twist, hence torsion. PROVED. -/
theorem conj_sub_isOfFinAddOrder_of_twist_torsion (E : WeierstrassCurve ℚ) (h : ℚ)
    (htors : ∀ R : ((qtwist E (h * k)).baseChange ℚ).toAffine.Point, IsOfFinAddOrder R)
    (P : ((qtwist E h).baseChange K).toAffine.Point) : IsOfFinAddOrder (conj D P - P) := by
  have hfix := conj_iota_symm_sub E h k D P
  have hr := baseChange_descend D _ hfix
  have h1 : IsOfFinAddOrder (iota E h k D (Point.baseChange ℚ K
      (descend D ((iota E h k D).symm (P - conj D P)) hfix))) :=
    ((iota E h k D).toAddMonoidHom.comp (Point.baseChange ℚ K)).isOfFinAddOrder (htors _)
  rw [hr, AddEquiv.apply_symm_apply] at h1
  have h2 := h1.neg
  rwa [neg_sub] at h2

/-- **The involution negates the free quotient when the rational component has rank zero**: if
every point of `E^{(h)}(ℚ)` is torsion, then `P + σP` is torsion for every `P ∈ E^{(h)}(K)` (it is
`σ`-invariant, hence rational). PROVED. -/
theorem conj_add_isOfFinAddOrder_of_torsion (E : WeierstrassCurve ℚ) (h : ℚ)
    (htors : ∀ R : ((qtwist E h).baseChange ℚ).toAffine.Point, IsOfFinAddOrder R)
    (P : ((qtwist E h).baseChange K).toAffine.Point) : IsOfFinAddOrder (conj D P + P) := by
  have hfix := conj_add_conj E h k D P
  have hr := baseChange_descend D _ hfix
  have h1 := (Point.baseChange ℚ K).isOfFinAddOrder (htors (descend D _ hfix))
  rw [hr] at h1
  rwa [add_comm] at h1

include D in
/-- **The native genus lattice, V19 form** (tex 2433–2435 of the 11/5 text; V19 lines 18324–18346):
for `K = ℚ(√k)`, if `E^{(hk)}(ℚ)` has rank zero (every point torsion), `g` generates `E^{(h)}(K)`
modulo torsion and `q` generates `E^{(h)}(ℚ)` modulo torsion, then the rational line has index at
most two: `q_K ≡ m g`, `2g ≡ n q_K`, `mn = 2`, `ĥ_K(q_K) = m² ĥ_K(g)`, `ĥ_K(q_K) = 2 ĥ_ℚ(q)`.
PROVED. -/
theorem native_lattice_index_le_two (E : WeierstrassCurve ℚ) (h : ℚ) [(qtwist E h).IsElliptic]
    (htors : ∀ R : ((qtwist E (h * k)).baseChange ℚ).toAffine.Point, IsOfFinAddOrder R)
    (g : ((qtwist E h).baseChange K).toAffine.Point) (hg : IsFreeGenerator g)
    (q : ((qtwist E h).baseChange ℚ).toAffine.Point) (hq : IsFreeGenerator q) :
    ∃ m n : ℤ, IsOfFinAddOrder (Point.baseChange ℚ K q - m • g) ∧
      IsOfFinAddOrder (2 • g - n • Point.baseChange ℚ K q) ∧ m * n = 2 ∧
      (Point.baseChange ℚ K q).canonicalHeight = (m : ℝ) ^ 2 * g.canonicalHeight ∧
      (Point.baseChange ℚ K q).canonicalHeight = 2 * q.canonicalHeight :=
  rational_line_index_le_two D (qtwist E h) g hg
    (conj_sub_isOfFinAddOrder_of_twist_torsion D E h htors g) q hq

end Galois

end ZInQ.Manuscript.RC.Height

import ZInQKernel.OneProof.H.TailG

/-!
# sgr-direct: the consumer of `shimuraIntegralModelRep` without the integral model (route NV)

The field `shimuraIntegralModelRep` enters the H chain only through `HDec.HeckeRestNV.HeckeVertWitness`
(no vertical ramification of the Hecke cover `E/ℚ(X)` at the primes `p > 324`). This file proves
`HeckeVertWitness` along h-b1's Lemma NV, simplified to one branch point, from fields already in the
bundles (`r1r2`, `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints`) and five named Props:

* `NVLocalInertia` (GLUE, local algebra of tame covers; h-b1 §3 step 3): if the residue fields over a
  rational branch point `b` are unramified at `p`, a conjugate of each vertical inertia element lies in an
  inertia group over `b`;
* `RamifiedSqrtInertia` (textbook Hilbert theory): over a point with ramification index `∣ 2`, a
  nontrivial inertia element moves `√(c (X − b))`. **Proved below** (`ramifiedSqrtInertia`, from Mathlib's
  `card_inertia_eq_ramificationIdxIn` and `ramificationIdx_tower`);
* `VertInertiaTrivial` (GLUE, textbook Hilbert theory): trivial vertical inertia gives ramification index 1;
* `HeckeBranchFibreUnram` (GLUE from the field `shimuraMainThmIDeligneY3AbU`, its reciprocity law at CM points;
  h-b1 §3 step 2): the residue fields of the Hecke cover over `−16/27` (CM points by `ℤ[√−6]`) are unramified at
  `p > 324`;
* `HeckeSqrtBranch` (GLUE from Elkies' model of `X₆`, the field `elkiesX6StarPrinted`): `E` contains a
  square root of `a (27X + 16)` with `a` a unit at every `p > 324`.

The proofs of `heckeVertWitness_of_nv`, `ramifiedSqrtInertia` and `heckeVertWitness_of_nv'` (the composite with
`RamifiedSqrtInertia` discharged: four named Props remain) are compiled here (standard axioms).
-/

set_option linter.style.haveILetI false

noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
open GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

namespace SGRDirect

/-! ## Inertia sets -/

/-- The inertia set of a prime `Q` of the integral closure of `ℚ[X]` in `E`: the `σ ∈ Gal(E/ℚ(X))` with
`σ b ∈ B` and `σ b ≡ b mod Q` for every `b ∈ B`. -/
def InertiaQ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    (Q : Ideal (integralClosure ℚ[X] E)) : Set Gal(E/RatFunc ℚ) :=
  {σ | ∀ b : integralClosure ℚ[X] E, ∃ c : integralClosure ℚ[X] E, (c : E) = σ (b : E) ∧ c - b ∈ Q}

/-- The inertia set of a prime `q` of the integral closure of `ℤ[X]` in `E` (through `ℚ[X]`). -/
def InertiaZ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E] :
    letI := intPolyAlg E
    Ideal (integralClosure ℤ[X] E) → Set Gal(E/RatFunc ℚ) :=
  letI := intPolyAlg E
  fun q => {σ | ∀ b : integralClosure ℤ[X] E, ∃ c : integralClosure ℤ[X] E,
    (c : E) = σ (b : E) ∧ c - b ∈ q}

/-! ## The named Props -/

/-- **GLUE (local algebra of tame covers; h-b1 §3, Lemma NV step 3).** Let `E/ℚ(X)` be finite Galois of
degree `< p`, with branch data in `S ∪ {∞}`, the points of `S` `p`-integral and pairwise distinct mod `p`.
If every residue field of `E` over a point `b ∈ S` is unramified at `p`, then for every prime `q` of the
integral closure of `ℤ[X]` in `E` over `p ℤ[X]` and every `τ` in the inertia of `q`, some conjugate
`g τ g⁻¹` lies in the inertia of a prime over `X − b`.
*Proof route* (not compiled): near the closed point `(p, X − b)` of `ℤ_(p)[X]` only the divisors `p = 0` and
`X = b` can ramify (`p`-integrality, distinctness); both tamely (degree `< p`, characteristic 0). By
Abhyankar's lemma (SGA 1 XIII 5.3; the kernel's T2 for the DVR form) and Zariski–Nagata purity (proved in
the chain, `PropTSGlue.PurityGlobalDim2`, t-purity3) the cover is, strictly henselian locally, a quotient of
`ℤ_p^{sh}[z^{1/n}, p^{1/n}]`; the residue field of the branch over `z = 0` is then `k_p(p^{1/c})` with
`c = [I_𝔓 : I_{Q_b}]`, so unramified residue fields force `I_𝔓 = I_{Q_b}`, and `I_q ⊆ I_𝔓`. -/
def NVLocalInertia : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf → Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    ∀ b ∈ S,
    (∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime → 𝔓.under ℚ[X] = Ideal.span {X - C b} →
      ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p) →
    letI := intPolyAlg E
    ∀ q : Ideal (integralClosure ℤ[X] E), q.IsPrime → q.under ℤ[X] = vertPrime p →
    ∀ τ ∈ InertiaZ E q, ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧
      Q.under ℚ[X] = Ideal.span {X - C b} ∧ ∃ g : Gal(E/RatFunc ℚ), g * τ * g⁻¹ ∈ InertiaQ E Q

/-- **GLUE (textbook Hilbert theory).** Over a prime `Q` above `X − b` with ramification index dividing `2`,
an inertia element fixing a square root of `c (X − b)` (`c ≠ 0`) is trivial. (`|I_Q| = e_Q ≤ 2`; if `I_Q`
fixed `s` then `s` would lie in the inertia field, over which `X − b` is unramified, but `v(s²) = 1` is odd.) -/
def RamifiedSqrtInertia : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (b c : ℚ), c ≠ 0 → ∀ s : E,
    s ^ 2 = algebraMap ℚ[X] E (C c * (X - C b)) →
    ∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = Ideal.span {X - C b} →
    Q.ramificationIdx ℚ[X] ∣ 2 → ∀ σ ∈ InertiaQ E Q, σ s = s → σ = 1

/-- **GLUE (textbook Hilbert theory).** A prime of the integral closure of `ℤ[X]` in a finite Galois
`E/ℚ(X)` over `p ℤ[X]` whose inertia set is trivial has ramification index `1` (`B_q` is a DVR over the DVR
`ℤ[X]_{(p)}` and `|I_q| = e_q · [κ(q) : κ(p)]_{insep}`). -/
def VertInertiaTrivial : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (p : ℕ), p.Prime →
    letI := intPolyAlg E
    ∀ q : Ideal (integralClosure ℤ[X] E), q.IsPrime → q.under ℤ[X] = vertPrime p →
    (∀ τ ∈ InertiaZ E q, τ = 1) → q.ramificationIdx ℤ[X] = 1

/-- **GLUE from the field `shimuraMainThmIDeligneY3AbU` (Shimura's reciprocity law at CM points on `Y₃`;
h-b1 §3 step 2).** For a triple with R1fp,
R1hecke, R2fp and any `E` carrying the normalization chart, every residue field of `E` over the branch value
`−16/27` (whose points are CM points by the maximal order `ℤ[√−6]`, conductor `1`) is unramified at every
prime `p > 324`: by Shimura reciprocity the field of definition of a level-3 CM point lies in the ray class
field of conductor `3` of its CM field, unramified outside `{2, 3}`. -/
def HeckeBranchFibreUnram : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C (-16 / 27)} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

/-- **GLUE from Elkies' model of `X₆` (the field `elkiesX6StarPrinted`).** For a triple with R1fp, R1hecke,
R2fp and any `E` carrying the normalization chart, `E` contains a square root of `a (27X + 16)` for an integer
`a` prime to every `p > 324`. Elkies' coordinate `t` on `X₆/W` (`t = 0, 1, ∞` at the CM points of discriminant
`−24, −4, −3`) is `t = (27X + 16)/16` in the coordinate `X` of R2fp (branch values `−16/27, 0, ∞` with the same
CM types), and Elkies' chart `s² = −t` gives `(4s)² = −(27X + 16)` in `ℚ(X₆) ⊆ E` (`Y₃ → X₆` is dominant), so
`a = −1` (rv-h-b1 §2: `ℚ(X₆) = ℚ(X)(√X, √(−(27X + 16)))`, constants `−1, 3`). -/
def HeckeSqrtBranch : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ (a : ℤ) (s : E), (∀ p : ℕ, p.Prime → 324 < p → ¬ (p : ℤ) ∣ a) ∧
        s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))


/-! ## Helpers -/

section Helpers

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

theorem gal_fix (σ : Gal(E/RatFunc ℚ)) (f : ℚ[X]) :
    σ (algebraMap ℚ[X] E f) = algebraMap ℚ[X] E f := by
  rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]

theorem gal_sq (σ : Gal(E/RatFunc ℚ)) {s : E} {f : ℚ[X]} (hs : s ^ 2 = algebraMap ℚ[X] E f) :
    σ s = s ∨ σ s = -s := by
  have h : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, gal_fix]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem conj_fix (g τ : Gal(E/RatFunc ℚ)) {s : E} {f : ℚ[X]} (hs : s ^ 2 = algebraMap ℚ[X] E f)
    (hτ : τ s = s) : (g * τ * g⁻¹) s = s := by
  have hgg : g (g⁻¹ s) = s := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rcases gal_sq g⁻¹ hs with h | h
  · rw [h] at hgg
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, hτ, hgg]
  · rw [h, map_neg] at hgg
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, map_neg, hτ, map_neg]
    exact hgg

theorem algebraMap_int_injective :
    letI := intPolyAlg E
    Function.Injective (algebraMap ℤ[X] E) := by
  letI := intPolyAlg E
  have h1 : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  exact h1.comp (Polynomial.map_injective _ (Int.cast_injective (α := ℚ)))

theorem exists_vertPrime (p : ℕ) (hp : p.Prime) :
    letI := intPolyAlg E
    ∃ q : Ideal (integralClosure ℤ[X] E), q.IsPrime ∧ q.under ℤ[X] = vertPrime p := by
  letI := intPolyAlg E
  haveI := vertPrime_isPrime p hp
  refine Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (vertPrime p) ?_
  intro f hf
  rw [RingHom.mem_ker] at hf
  have : algebraMap ℤ[X] E f = 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E) E, hf, map_zero]
  rw [algebraMap_int_injective (E := E) (this.trans (map_zero _).symm)]
  exact Ideal.zero_mem _

/-- A vertical inertia element fixes a square root of `a (27X + 16)` (`p ∤ 2·3·a`). -/
theorem vert_fix (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (s : E)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))) :
    letI := intPolyAlg E
    ∀ q : Ideal (integralClosure ℤ[X] E), q.under ℤ[X] = vertPrime p →
    ∀ τ ∈ InertiaZ E q, τ s = s := by
  letI := intPolyAlg E
  intro q hq τ hτ
  set f : ℤ[X] := C a * (C 27 * X + C 16) with hfdef
  have hf : algebraMap ℤ[X] E f = s ^ 2 := by
    rw [hs]
    show algebraMap ℚ[X] E (f.map (Int.castRingHom ℚ)) = _
    congr 1
    rw [hfdef, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
    simp
  have hint : IsIntegral ℤ[X] s := by
    refine ⟨X ^ 2 - C f, monic_X_pow_sub_C f (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hf, sub_self]
  let sZ : integralClosure ℤ[X] E := ⟨s, hint⟩
  obtain ⟨c, hc, hcq⟩ := hτ sZ
  rcases gal_sq τ hs with h | h
  · exact h
  · exfalso
    have hc' : c = -sZ := Subtype.ext (by rw [hc]; exact h)
    rw [hc'] at hcq
    have h2 : (2 : integralClosure ℤ[X] E) * sZ ∈ q := by
      have := q.neg_mem_iff.mpr hcq
      convert this using 1
      ring
    have h4 : algebraMap ℤ[X] (integralClosure ℤ[X] E) (4 * f) ∈ q := by
      have := q.mul_mem_left (2 * sZ) h2
      convert this using 1
      apply Subtype.ext
      show algebraMap ℤ[X] E (4 * f) = 2 * s * (2 * s)
      rw [map_mul, hf, map_ofNat]
      ring
    have hv : 4 * f ∈ vertPrime p := by
      rw [← hq]; exact h4
    rw [vertPrime, Ideal.mem_map_C_iff] at hv
    have h0 := hv 0
    simp [hfdef] at h0
    rw [Ideal.mem_span_singleton] at h0
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h64 : (p : ℤ) ∣ 64 * a := by
      convert h0 using 1
      ring
    rcases hpz.dvd_or_dvd h64 with h | h
    · have h' : p ∣ 2 ^ 6 := by exact_mod_cast h
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h'
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact ha h

end Helpers

/-! ## The composite -/

/-- **One unramified vertical prime from route NV** (compiled), for one `E` with the Hecke cover's branch data,
degree, branch fibre at `−16/27` and square root. -/
theorem vertUnramWitness_of_nv (hL : NVLocalInertia) (hR : RamifiedSqrtInertia)
    (hV : VertInertiaTrivial)
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] [IsGalois (RatFunc ℚ) E]
    (p : ℕ) (hp : p.Prime) (hp324 : 324 < p)
    (hB : BranchData E {0, -16 / 27} nY3 6) (hD : Module.finrank (RatFunc ℚ) E ≤ 324)
    (hF : ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C (-16 / 27)} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p)
    (a : ℤ) (s : E) (ha : ¬ (p : ℤ) ∣ a)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16))) :
    VertUnramWitness E p := by
  letI := intPolyAlg E
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hqu⟩ := exists_vertPrime (E := E) p hp
  refine ⟨q, hq, hqu, hV E p hp q hq hqu ?_⟩
  intro τ hτ
  have hτs : τ s = s := vert_fix p hp (by omega) a ha s hs q hqu τ hτ
  have hmem : (-16 / 27 : ℚ) ∈ ({0, -16 / 27} : Finset ℚ) := by simp
  have h1627 : padicValRat p (16 / 27) = 0 := padicValRat_16_27 p (by omega)
  have hint : ∀ b ∈ ({0, -16 / 27} : Finset ℚ), 0 ≤ padicValRat p b := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simp
    · rw [neg_div, padicValRat.neg, h1627]
  have hdist : ∀ b ∈ ({0, -16 / 27} : Finset ℚ), ∀ b' ∈ ({0, -16 / 27} : Finset ℚ), b ≠ b' →
      padicValRat p (b - b') = 0 := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · rw [zero_sub, neg_div, neg_neg, h1627]
    · rw [sub_zero, neg_div, padicValRat.neg, h1627]
    · exact absurd rfl hne
  obtain ⟨Q, hQ, hQu, g, hg⟩ := hL E {0, -16 / 27} nY3 6 p hp hB (by omega) hint hdist
    (-16 / 27) hmem hF q hq hqu τ hτ
  have ha0 : (a : ℚ) ≠ 0 := by
    rintro h
    exact ha (by rw [Int.cast_eq_zero.mp h]; exact dvd_zero _)
  have hs' : s ^ 2 = algebraMap ℚ[X] E (C (27 * (a : ℚ)) * (X - C (-16 / 27))) := by
    rw [hs]
    congr 1
    have e1 : (X - C (-16 / 27 : ℚ) : ℚ[X]) = X + C (16 / 27) := by
      rw [show (-16 / 27 : ℚ) = -(16 / 27) by norm_num, C_neg, sub_neg_eq_add]
    have e2 : (C (27 : ℚ) * C (16 / 27) : ℚ[X]) = C 16 := by rw [← C_mul]; norm_num
    rw [e1, C_mul]
    linear_combination (-C (a : ℚ)) * e2
  have hram : Q.ramificationIdx ℚ[X] ∣ 2 := by
    have := hB.2.1 (-16 / 27) hmem Q hQ hQu
    simpa [nY3] using this
  have h1 := hR E (-16 / 27) (27 * a) (mul_ne_zero (by norm_num) ha0) s hs' Q hQ hQu hram
    (g * τ * g⁻¹) hg (conj_fix g τ hs' hτs)
  have : τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
  rw [this, h1]
  group

/-- **`HeckeVertWitness` by route NV, without the integral model of the Shimura curve** (compiled). Inputs:
the bundle fields `r1r2` (as `R1R2fp`), `t5` (as `TorsionStructure`), `qmAutCard`, `serreRigidity3`,
`alFixedPoints` (the same inputs as `HeckeRestAll.coverModelOfHecke_of_heckeRest`, which give `HeckeBranch`
and `HeckeDegree`), and the five named Props above. -/
theorem heckeVertWitness_of_nv (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hR : RamifiedSqrtInertia) (hV : VertInertiaTrivial)
    (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness := by
  have hB : HeckeBranch :=
    heckeBranch_of' hRR HeckeRestCurve.curveChartInf (HeckeRest.heckeFibreSizes_of hT hA hS hW) hT
  have hD : HeckeDegree := heckeDegree_of_torsion hT
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  obtain ⟨a, s, ha, hs⟩ := hQ Y Φ π h1 hh h2 E hN
  exact vertUnramWitness_of_nv hL hR hV E p hp hp324 (hB Y Φ π h1 hh h2 E hN)
    (hD Y Φ π h1 hh h2 E hN) (hF Y Φ π h1 hh h2 E hN p hp hp324) a s (ha p hp hp324) hs

/-! ## `RamifiedSqrtInertia` is proved (Mathlib's Hilbert theory) -/

section Ram

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]

/-- The inclusion of the integral closure of `ℚ[X]` in an intermediate field into that in `E`. -/
def incl (K' : IntermediateField (RatFunc ℚ) E) :
    integralClosure ℚ[X] K' →+* integralClosure ℚ[X] E where
  toFun x := ⟨((x : K') : E), by
    have h := x.2
    exact h.map (IsScalarTower.toAlgHom ℚ[X] K' E)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

example (K' : IntermediateField (RatFunc ℚ) E) : IsDedekindDomain (integralClosure ℚ[X] K') :=
  integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')


/-- **`RamifiedSqrtInertia` is a theorem** (compiled). With `H'` the fixing group of the ring of integers `A'` of
the fixed field of `σ`: `|I_{H'}(Q)| = e(Q|A') ≥ 2` (`σ ∈ I_{H'}(Q)`, `σ ≠ 1`), so `e(Q ∩ A' | X − b) = 1` by the
tower and `e(Q | X − b) ∣ 2`; but `s ∈ Q ∩ A'` and `X − b = c⁻¹ s²` give `e(Q ∩ A' | X − b) ≥ 2`. -/
theorem ramifiedSqrtInertia : RamifiedSqrtInertia := by
  intro E _ _ _ _ _ _ b c hc s hs Q hQ hQu he σ hσ hσs
  by_contra hne
  haveI := hQ
  -- the base `A = ℚ[X]`, `(integralClosure ℚ[X] E)` its integral closure in `E`, `G = Gal(E/ℚ(X))`
  haveI hinjE : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E := IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  haveI : SMulCommClass Gal(E/RatFunc ℚ) ℚ[X] E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]⟩
  haveI hG : IsGaloisGroup Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) (RatFunc ℚ) E
  -- the intermediate field fixed by `σ` and its ring of integers `A'`
  set K' : IntermediateField (RatFunc ℚ) E := IntermediateField.fixedField (Subgroup.zpowers σ)
  set A' := integralClosure ℚ[X] K'
  haveI : IsDedekindDomain A' := integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')
  letI : Algebra A' (integralClosure ℚ[X] E) := (incl K').toAlgebra
  haveI : IsScalarTower ℚ[X] A' (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    show algebraMap ℚ[X] E a = (((algebraMap ℚ[X] A' a : A') : K') : E)
    rw [IsScalarTower.algebraMap_apply ℚ[X] K' E]
    rfl)
  have hincl_inj : Function.Injective (algebraMap A' (integralClosure ℚ[X] E)) := by
    intro x y hxy
    have h1 : (((x : K') : E)) = (((y : K') : E)) :=
      congrArg (fun z : (integralClosure ℚ[X] E) => (z : E)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hQE : Function.Injective (algebraMap ℚ[X] E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp hinjE
  have hQB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro x y h
    apply hQE
    rw [IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E x,
      IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E y, h]
  have hQA' : Function.Injective (algebraMap ℚ[X] A') := by
    intro x y h
    apply hQB
    rw [IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) x,
      IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) y, h]
  haveI : FaithfulSMul ℚ[X] A' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hQA'
  haveI : Module.IsTorsionFree ℚ[X] A' := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : FaithfulSMul A' (integralClosure ℚ[X] E) := (faithfulSMul_iff_algebraMap_injective A' (integralClosure ℚ[X] E)).mpr hincl_inj
  haveI hH : IsGaloisGroup (fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E)))) A' (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isScalarTower Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) A'
  set H' := fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E))) with hH'def
  have hσK' : ∀ x : E, x ∈ K' → σ x = x := fun x hx =>
    (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_zpowers σ)
  have hσH' : σ ∈ H' := by
    rw [hH'def, mem_fixingSubgroup_iff]
    rintro _ ⟨a, rfl⟩
    apply Subtype.ext
    show σ (((a : K') : E)) = ((a : K') : E)
    exact hσK' _ (a : K').2
  -- the instances of the cardinality formula
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Finite A' (integralClosure ℚ[X] E) := Module.Finite.of_restrictScalars_finite ℚ[X] A' (integralClosure ℚ[X] E)
  haveI : Module.IsTorsionFree A' (integralClosure ℚ[X] E) := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : Algebra.IsIntegral A' (integralClosure ℚ[X] E) := Algebra.IsInvariant.isIntegral A' (integralClosure ℚ[X] E) H'
  set Q' : Ideal A' := Q.under A' with hQ'def
  haveI : Q'.IsPrime := Ideal.IsPrime.under A' Q
  haveI : Q.LiesOver Q' := ⟨rfl⟩
  haveI : CharZero Q'.ResidueField := by
    let f : ℚ →+* Q'.ResidueField :=
      ((algebraMap A' Q'.ResidueField).comp (algebraMap ℚ[X] A')).comp Polynomial.C
    exact charZero_of_injective_ringHom f.injective
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := H') Q' Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q' Q H'] at hcard
  -- `σ` lies in the inertia of `Q` in `H'`, and is nontrivial
  have hσI : (⟨σ, hσH'⟩ : H') ∈ Q.inertia H' := by
    intro x
    obtain ⟨c', hc', hc'Q⟩ := hσ x
    have : (⟨σ, hσH'⟩ : H') • x = c' := by
      apply Subtype.ext
      rw [hc']
      rfl
    rw [this]
    exact hc'Q
  have hIne : Q.inertia H' ≠ ⊥ := by
    intro h
    have h1 : (⟨σ, hσH'⟩ : H') ∈ (⊥ : Subgroup H') := h ▸ hσI
    rw [Subgroup.mem_bot] at h1
    exact hne (congrArg Subtype.val h1)
  have h2le : 1 < Q.ramificationIdx A' := by
    rw [← hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hIne
  -- the tower `ℚ[X] ⊆ A' ⊆ B`
  have htow := Ideal.ramificationIdx_tower (R := ℚ[X]) Q' Q
  have he0 : Q.ramificationIdx ℚ[X] ≠ 0 := by
    rintro h0
    rw [h0, zero_dvd_iff] at he
    exact two_ne_zero he
  have he2 : Q.ramificationIdx ℚ[X] ≤ 2 := Nat.le_of_dvd two_pos he
  have he1 : Q'.ramificationIdx ℚ[X] = 1 := by
    have hpos : Q'.ramificationIdx ℚ[X] ≠ 0 := by
      intro h0; rw [htow, h0, zero_mul] at he0; exact he0 rfl
    rw [htow] at he2
    have : Q'.ramificationIdx ℚ[X] * 2 ≤ 2 :=
      le_trans (Nat.mul_le_mul_left _ h2le) he2
    omega
  -- `s` lies in `A'`
  have hsK' : s ∈ K' := by
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hσs, ih (Subgroup.zpow_mem_zpowers σ n)]
    | pred n ih =>
      have h1 : (σ ^ (-(n : ℤ) - 1)) (σ s) = (σ ^ (-(n : ℤ))) s := by
        rw [← AlgEquiv.mul_apply, ← zpow_add_one, sub_add_cancel]
      rw [hσs] at h1
      rw [h1, ih (Subgroup.zpow_mem_zpowers σ _)]
  have hintE : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - Polynomial.C (C c * (X - C b)), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  have hintK : IsIntegral ℚ[X] (⟨s, hsK'⟩ : K') := by
    exact isIntegral_algebraMap_iff.mp hintE
  set s' : A' := ⟨⟨s, hsK'⟩, hintK⟩ with hs'def
  have hs'B : ((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E) = s := rfl
  have hs'sq : s' ^ 2 = algebraMap ℚ[X] A' (C c * (X - C b)) := by
    apply hincl_inj
    apply Subtype.ext
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    show (((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E)) ^ 2 = _
    rw [hs'B, hs]
    rfl
  -- `s' ∈ Q'`
  have hpQ : C c * (X - C b) ∈ Q.under ℚ[X] := by
    rw [hQu, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  have hs'Q : s' ∈ Q' := by
    apply (inferInstance : Q'.IsPrime).mem_of_pow_mem 2
    rw [hs'sq, ← Ideal.mem_comap, ← Ideal.under_def, hQ'def, Ideal.under_under]
    exact hpQ
  -- `p A' ⊆ Q'²`
  have hle : Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ 2 := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [Set.mem_singleton_iff] at hf
    subst hf
    have : algebraMap ℚ[X] A' (X - C b) = algebraMap ℚ[X] A' (C c⁻¹) * s' ^ 2 := by
      rw [hs'sq, ← map_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hs'Q 2)
  -- contradiction with `e(Q' | p) = 1`
  haveI : Q'.LiesOver (Ideal.span {X - C b}) := ⟨by rw [hQ'def, Ideal.under_under, hQu]⟩
  have hp0 : (Ideal.span {X - C b} : Ideal ℚ[X]) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero b
  have he1' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {X - C b}) Q' hp0
  rw [he1] at he1'
  have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n} := hle
  by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n}
  · have := le_csSup hbdd h2mem
    rw [Ideal.ramificationIdx'] at he1'
    omega
  · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he1'
    exact zero_ne_one he1'

end Ram

/-- **`HeckeVertWitness` by route NV, with `RamifiedSqrtInertia` proved** (compiled): the bundle fields `r1r2`,
`t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints` and four named Props. -/
theorem heckeVertWitness_of_nv' (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hV : VertInertiaTrivial)
    (hF : HeckeBranchFibreUnram) (hQ : HeckeSqrtBranch) : HeckeVertWitness :=
  heckeVertWitness_of_nv hRR hT hA hS hW hL ramifiedSqrtInertia hV hF hQ

end SGRDirect


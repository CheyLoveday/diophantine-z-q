import ZInQKernel.Contrib.CloudB3E2Norm.H20Frob
import ZInQKernel.Contrib.CloudB3E1RingClass.MovingGenuine

/-!
# The two scalar facts of the leaf's Frobenius value

Manuscript `diophantine_zq.tex`, tex 4144–4145 and 4283–4292: the scalar Frobenius value at an
unused prime `q` is `z = x(ε(F̃r_q)) (1 + t)`, where `x(ε(F̃r_q)) = (h_x/q)` is the genuine
unramified quadratic sign and `1 + t` is the value of the moving character at the orientation.

`H20Frob.charValueAt_leaf` reduced lane RC32's `CharValueAt` for the leaf's value `zAt Fam x q` to
two scalar facts at the place `w` over `q`:

* `χ_h(Frob_w) = frobSign Fam x q`;
* `ψ(π(Frob_w)) = 1 + t`.

This file **proves** both:

* `exists_sqrt_of_residue_eq_one` (PROVED; Hensel): a principal unit of `𝒪[F]` is a square, for
  `F` a nonarchimedean local field of odd residue characteristic.
* **`frobLift_sqrt_eq_iff`** (PROVED; Teichmüller and Euler's criterion): for an arithmetic
  Frobenius lift `σ` and `t² = u` with `u ∈ 𝒪[F]ˣ`, `σ t = t ↔ ū` is a square in the residue field.
* **`quadChar_frob_eq_one_iff`** (PROVED): `χ_h(Frob_w) = 1` iff `h` is a square modulo `w`, for `h`
  a `w`-unit and `w ∤ 2`.
* `isSquare_residue_iff_jacobiSym` (PROVED): at a place of residue degree one over `q`, an integer
  `n` with `q ∤ n` is a square modulo `w` iff `(n/q) = 1`.
* **`quadChar_frob_eq_frobSign`** (PROVED; with lane RC32's `sgnChar_frobLift_of_unused`): the
  first scalar fact, for `h = h_x` and an unused prime `q` (`λ_q(x) = 0`) at a place `w` of residue
  degree one over `q`.
* **`psi_frob_eq_onePlusT`** (PROVED; lane E1's `movingPsi_genuine`): the second scalar fact, for
  `ψ ∘ π` the inflation of E1's genuine moving character `Ψ = (1 + t)^ξ` and `w` an active
  orientation `𝔭_j`.
* **`charValueAt_leaf_genuine`** (PROVED): lane RC32's `CharValueAt` at `w` for the leaf's value,
  from the two.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ValuativeRel IsLocalRing Polynomial
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

/-! ### The Frobenius on a square root in a local field -/

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **A principal unit is a square** (Hensel, `2` a unit). Kind: PROVED. -/
theorem exists_sqrt_of_residue_eq_one (h2 : IsUnit (2 : 𝒪[F])) (u : 𝒪[F])
    (hu : residue 𝒪[F] u = 1) : ∃ v : 𝒪[F], v ^ 2 = u := by
  have hmon : (X ^ 2 - C u : 𝒪[F][X]).Monic := monic_X_pow_sub_C u two_ne_zero
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u) hmon 1 (by
    rw [← residue_eq_zero_iff]
    simp [hu]) (by simpa [one_add_one_eq_two] using h2)
  refine ⟨a, ?_⟩
  have := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  exact sub_eq_zero.1 this

/-- **The Frobenius on a square root of a unit** (PROVED; tex 4288–4292): for an arithmetic
Frobenius lift `σ` of `F`, residue characteristic `≠ 2`, and `t² = u`, `u ∈ 𝒪[F]ˣ`: `σ t = t`
exactly when the residue of `u` is a square. -/
theorem frobLift_sqrt_eq_iff (hchar : ringChar 𝓀[F] ≠ 2) (σ : Field.absoluteGaloisGroup F)
    (hσ : TauCeti.IsArithFrobeniusLift F σ) (u : 𝒪[F]ˣ) (t : AlgebraicClosure F)
    (ht : t ^ 2 = algebraMap F (AlgebraicClosure F) ((u : 𝒪[F]) : F)) :
    DFunLike.coe (F := Gal(AlgebraicClosure F/F)) σ t = t ↔
      IsSquare (residue 𝒪[F] (u : 𝒪[F])) := by
  classical
  let _ := Fintype.ofFinite 𝓀[F]
  set N := Nat.card 𝓀[F] with hN
  set ι : 𝒪[F] →+* AlgebraicClosure F := (algebraMap F (AlgebraicClosure F)).comp
    (𝒪[F]).subtype with hι
  have hιinj : Function.Injective ι :=
    (algebraMap F (AlgebraicClosure F)).injective.comp Subtype.val_injective
  -- the residue characteristic
  obtain ⟨d, hp, hNd⟩ := FiniteField.card 𝓀[F] (ringChar 𝓀[F])
  have hNcard : N = ringChar 𝓀[F] ^ (d : ℕ) := by rw [hN, Nat.card_eq_fintype_card, hNd]
  have hpodd : Odd (ringChar 𝓀[F]) := hp.odd_of_ne_two hchar
  have hNodd : Odd N := hNcard ▸ hpodd.pow
  have hN1 : 1 ≤ N := hNodd.pos
  have h2 : IsUnit (2 : 𝒪[F]) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h0
    apply hchar
    have := ringChar.dvd (R := 𝓀[F]) (x := 2) (by exact_mod_cast h0)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  -- the Teichmüller lift of the residue
  set x : 𝓀[F]ˣ := Units.map (residue 𝒪[F]).toMonoidHom u with hx
  set ω : 𝒪[F]ˣ := TauCeti.teichmuller 𝒪[F] x with hω
  have hωpow : ω ^ (N - 1) = 1 := TauCeti.teichmuller_pow_card_sub_one 𝒪[F] x
  have hωres : residue 𝒪[F] (ω : 𝒪[F]) = residue 𝒪[F] (u : 𝒪[F]) :=
    ((TauCeti.teichmuller_eq_iff 𝒪[F]).1 rfl).2
  -- the principal part has a square root
  obtain ⟨v, hv⟩ := exists_sqrt_of_residue_eq_one h2 ((u : 𝒪[F]) * ((ω⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) (by
    rw [map_mul, ← hωres, ← map_mul, Units.mul_inv, map_one])
  have hvu : IsUnit v := by
    have : IsUnit (v ^ 2) := hv ▸ (u * ω⁻¹).isUnit
    exact isUnit_pow_iff two_ne_zero |>.1 this
  have hιv : ι v ≠ 0 := fun h0 => hvu.ne_zero (hιinj (h0.trans (map_zero ι).symm))
  -- `y = t / v` is a root of unity of order dividing `2(N − 1)`
  set y := t / ι v with hy
  have hty : t = y * ι v := (div_mul_cancel₀ t hιv).symm
  have hy2 : y ^ 2 = ι (ω : 𝒪[F]) := by
    have h1 : ι v ^ 2 * ι (ω : 𝒪[F]) = ι (u : 𝒪[F]) := by
      rw [← map_pow, ← map_mul, hv, mul_assoc, Units.inv_mul, mul_one]
    have hιu : t ^ 2 = ι (u : 𝒪[F]) := ht
    rw [hy, div_pow, hιu, ← h1, mul_div_cancel_left₀ _ (pow_ne_zero 2 hιv)]
  have hym : y ^ (2 * (N - 1)) = 1 := by
    rw [pow_mul, hy2, ← map_pow, ← Units.val_pow_eq_pow_val, hωpow, Units.val_one, map_one]
  have hcop : (2 * (N - 1)).Coprime (ringChar 𝓀[F]) := by
    refine Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 hchar.symm) ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hdN : ringChar 𝓀[F] ∣ N := by
      rw [hNcard]; exact dvd_pow_self _ (PNat.ne_zero d)
    have := (Nat.dvd_sub_iff_right (by omega) hdN).2 hdvd
    simp only [Nat.sub_sub_self hN1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hσy : DFunLike.coe (F := Gal(AlgebraicClosure F/F)) σ y = y ^ N :=
    hσ.apply_of_pow_eq_one hcop hym
  have hσv : DFunLike.coe (F := Gal(AlgebraicClosure F/F)) σ (ι v) = ι v :=
    AlgEquiv.commutes (show Gal(AlgebraicClosure F/F) from σ) _
  have hσt : DFunLike.coe (F := Gal(AlgebraicClosure F/F)) σ t =
      t * (ι (ω : 𝒪[F])) ^ ((N - 1) / 2) := by
    obtain ⟨k, hk⟩ := hNodd
    have hk' : (N - 1) / 2 = k := by omega
    rw [hty, map_mul (show Gal(AlgebraicClosure F/F) from σ), hσy, hσv, hk', ← hy2, ← pow_mul]
    rw [show N = 2 * k + 1 from hk, pow_succ]
    ring
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at ht
    exact u.ne_zero (Subtype.val_injective ((algebraMap F _).injective (ht.symm.trans
      (map_zero _).symm)))
  -- reduce to the residue
  have hres : DFunLike.coe (F := Gal(AlgebraicClosure F/F)) σ t = t ↔
      (ω : 𝒪[F]) ^ ((N - 1) / 2) = 1 := by
    rw [hσt, ← map_pow]
    constructor
    · intro h
      have : ι ((ω : 𝒪[F]) ^ ((N - 1) / 2)) = 1 := by
        have := mul_left_cancel₀ ht0 (h.trans (mul_one t).symm)
        exact this
      exact hιinj (this.trans (map_one ι).symm)
    · intro h
      rw [h, map_one, mul_one]
  rw [hres]
  have hteich : (ω : 𝒪[F]) ^ ((N - 1) / 2) = 1 ↔ x ^ ((N - 1) / 2) = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, ← map_pow, Units.val_eq_one]
    constructor
    · intro h
      exact TauCeti.teichmuller_injective 𝒪[F] (h.trans (map_one _).symm)
    · intro h
      rw [h, map_one]
  rw [hteich]
  have hx0 : residue 𝒪[F] (u : 𝒪[F]) ≠ 0 := (u.isUnit.map (residue 𝒪[F])).ne_zero
  obtain ⟨k, hk⟩ := hNodd
  rw [FiniteField.isSquare_iff hchar hx0, ← Nat.card_eq_fintype_card, ← hN,
    show N / 2 = (N - 1) / 2 by omega, ← Units.val_eq_one, Units.val_pow_eq_pow_val]
  rfl

end Local

/-! ### The quadratic character at the Frobenius of a place -/

section Global

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)

/-- **`χ_h(Frob_w) = 1` iff `h` is a square modulo `w`** (PROVED; tex 4288–4292): for `w ∉ S₀`,
`w ∤ 2`, and `h` a `w`-adic unit `u`. -/
theorem quadChar_frob_eq_one_iff (w : NewPlaces K S₀ S)
    (hchar : ringChar 𝓀[w.1.adicCompletion K] ≠ 2) (u : 𝒪[w.1.adicCompletion K]ˣ)
    (hu : ((u : 𝒪[w.1.adicCompletion K]) : w.1.adicCompletion K) =
      algebraMap K (w.1.adicCompletion K) h) :
    quadChar s hs hs0 (urFrobElt K w) = 1 ↔
      IsSquare (residue 𝒪[w.1.adicCompletion K] (u : 𝒪[w.1.adicCompletion K])) := by
  obtain ⟨φ, hφ⟩ := TauCeti.exists_isArithFrobeniusLift (w.1.adicCompletion K)
  rw [← locMap_frobLift w φ hφ]
  set t := decompEmb K w.1 ((s : AlgebraicClosure K))
  have ht : t ^ 2 = algebraMap (w.1.adicCompletion K) (AlgebraicClosure (w.1.adicCompletion K))
      ((u : 𝒪[w.1.adicCompletion K]) : w.1.adicCompletion K) := by
    rw [hu, ← map_pow]
    have h1 : ((s : AlgebraicClosure K)) ^ 2 = algebraMap K (AlgebraicClosure K) h := by
      show ((s ^ 2 : KS K S₀) : AlgebraicClosure K) = _
      rw [hs]
      rfl
    rw [h1, AlgHom.commutes, IsScalarTower.algebraMap_apply K (w.1.adicCompletion K)]
  rw [← frobLift_sqrt_eq_iff hchar φ hφ u t ht]
  have hiff : galS K S₀ (locMap K S₀ w.1 φ) s = s ↔
      DFunLike.coe (F := Gal(AlgebraicClosure (w.1.adicCompletion K)/w.1.adicCompletion K)) φ t =
        t := by
    rw [← Subtype.coe_inj, coe_locMap_apply]
    constructor
    · intro h1
      have := congrArg (decompEmb K w.1) h1
      rwa [decompEmb_decompMap] at this
    · intro h1
      apply (decompEmb K w.1).toRingHom.injective
      change decompEmb K w.1 _ = decompEmb K w.1 _
      rw [decompEmb_decompMap]
      exact h1
  rw [← hiff]
  unfold quadChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h1
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

end Global

/-! ### Residue degree one -/

section Degree

variable {K : Type} [Field K] [NumberField K]

/-- **At a place of residue degree one over `q`, `n ∈ ℤ` with `q ∤ n` is a square modulo `w` iff
`(n/q) = 1`** (PROVED: the residue field of `K_w` is `𝐅_q`). -/
theorem isSquare_residue_iff_jacobiSym (w : HeightOneSpectrum (𝓞 K)) (q : ℕ) [hq : Fact q.Prime]
    (hcard : Nat.card (𝓞 K ⧸ w.asIdeal) = q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    IsSquare ((n : 𝓀[w.adicCompletion K])) ↔ jacobiSym n q = 1 := by
  have hk : Nat.card 𝓀[w.adicCompletion K] = q :=
    (Nat.card_congr
      (HeightOneSpectrum.residueFieldEquivAdicCompletion (K := K) w).toEquiv).symm.trans hcard
  have : Finite 𝓀[w.adicCompletion K] := Nat.finite_of_card_ne_zero (hk ▸ hq.out.ne_zero)
  have hchar : CharP 𝓀[w.adicCompletion K] q := by
    have h0 : ((q : ℕ) : 𝓀[w.adicCompletion K]) = 0 := by
      let _ := Fintype.ofFinite 𝓀[w.adicCompletion K]
      rw [← hk, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
    rcases (Nat.dvd_prime hq.out).1 (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · have := ringChar.charP 𝓀[w.adicCompletion K]
      rwa [h] at this
  let f := ZMod.castHom (dvd_refl q) 𝓀[w.adicCompletion K]
  have hf : Function.Bijective f :=
    f.injective.bijective_of_nat_card_le (by rw [hk, Nat.card_zmod])
  let e := RingEquiv.ofBijective f hf
  have hen : e (n : ZMod q) = (n : 𝓀[w.adicCompletion K]) := map_intCast e n
  have hn0 : (n : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff q hn0, ← hen]
  constructor
  · intro h
    have := h.map e.symm.toRingHom
    simpa using this
  · intro h
    exact h.map e.toRingHom

end Degree

/-! ### The first scalar fact -/

section SignFact

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)

/-- **`χ_h(Frob_w) = (n/q)`** for `h = n ∈ ℤ`, `q ∤ 2n`, at a place `w ∉ S₀` of residue degree one
over the prime `q` (PROVED). -/
theorem quadChar_frob_eq_jacobiSym (w : NewPlaces K S₀ S) (q : ℕ) [hq : Fact q.Prime]
    (hq2 : q ≠ 2) (hcard : Nat.card (𝓞 K ⧸ w.1.asIdeal) = q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n)
    (hh : h = (n : K)) :
    ((quadChar s hs hs0 (urFrobElt K w) : ℤˣ) : ℤ) = jacobiSym n q := by
  have hk : Nat.card 𝓀[w.1.adicCompletion K] = q :=
    (Nat.card_congr
      (HeightOneSpectrum.residueFieldEquivAdicCompletion (K := K) w.1).toEquiv).symm.trans hcard
  have : Finite 𝓀[w.1.adicCompletion K] := Nat.finite_of_card_ne_zero (hk ▸ hq.out.ne_zero)
  have hcharq : ringChar 𝓀[w.1.adicCompletion K] = q := by
    have h0 : ((q : ℕ) : 𝓀[w.1.adicCompletion K]) = 0 := by
      let _ := Fintype.ofFinite 𝓀[w.1.adicCompletion K]
      rw [← hk, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
    rcases (Nat.dvd_prime hq.out).1 (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hchar : ringChar 𝓀[w.1.adicCompletion K] ≠ 2 := hcharq ▸ hq2
  -- `n` is a unit of `𝒪[K_w]`
  have hres : residue 𝒪[w.1.adicCompletion K] (n : 𝒪[w.1.adicCompletion K]) ≠ 0 := by
    rw [map_intCast]
    intro h0
    have hc := ringChar.charP 𝓀[w.1.adicCompletion K]
    rw [hcharq] at hc
    exact hn ((CharP.intCast_eq_zero_iff 𝓀[w.1.adicCompletion K] q n).1 h0)
  set u : 𝒪[w.1.adicCompletion K]ˣ := (residue_ne_zero_iff_isUnit _).1 hres |>.unit
  have hu : ((u : 𝒪[w.1.adicCompletion K]) : w.1.adicCompletion K) =
      algebraMap K (w.1.adicCompletion K) h := by
    rw [hh, map_intCast]
    simp [u]
  have h1 := quadChar_frob_eq_one_iff s hs hs0 w hchar u hu
  have hsq : IsSquare (residue 𝒪[w.1.adicCompletion K] (u : 𝒪[w.1.adicCompletion K])) ↔
      jacobiSym n q = 1 := by
    rw [show (u : 𝒪[w.1.adicCompletion K]) = (n : 𝒪[w.1.adicCompletion K]) by simp [u],
      map_intCast]
    exact isSquare_residue_iff_jacobiSym w.1 q hcard n hn
  have hpm : jacobiSym n q = 1 ∨ jacobiSym n q = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_comm, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact (Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hq.out).2 fun h =>
      hn (Int.natCast_dvd.2 h)))
  rcases Int.units_eq_one_or (quadChar s hs hs0 (urFrobElt K w)) with hc | hc
  · rw [hc, Units.val_one]
    exact ((hsq.1 (h1.1 hc))).symm
  · rw [hc]
    rcases hpm with hj | hj
    · exact absurd (h1.2 (hsq.2 hj)) (by rw [hc]; decide)
    · rw [hj]; rfl

/-- **The first scalar fact `χ_h(Frob_w) = frobSign Fam x q`** (PROVED; tex 4288–4292): for
`h = h_x`, an unused prime `q ∈ Q` (`λ_q(x) = 0`), odd, not dividing `h_x`, and `w ∉ S₀` of residue
degree one over `q`. -/
theorem quadChar_frob_eq_frobSign (w : NewPlaces K S₀ S) (Fam : ZInQ.Manuscript.RC.Family)
    (hQ : ∀ q ∈ Fam.Q, q.Prime) (x : ZInQ.Manuscript.RC.Addr Fam.b) {q : ℕ} (hqQ : q ∈ Fam.Q)
    (hx : Fam.lam q x = 0) (hq2 : q ≠ 2) (hcard : Nat.card (𝓞 K ⧸ w.1.asIdeal) = q)
    (hn : ¬ (q : ℤ) ∣ Fam.h x) (hh : h = (Fam.h x : K)) :
    quadChar s hs hs0 (urFrobElt K w) = frobSign Fam x q := by
  have : Fact q.Prime := ⟨hQ q hqQ⟩
  apply Units.ext
  rw [quadChar_frob_eq_jacobiSym s hs hs0 w q hq2 hcard _ hn hh, frobSign,
    sgnChar_frobLift_of_unused Fam hQ hqQ hx 0]

end SignFact

/-! ### The second scalar fact, and the leaf's value -/

section PsiFact

variable {K : Type} [Field K] [NumberField K] {S₀ S Sr : Set (HeightOneSpectrum (𝓞 K))}
  {i : ℕ} [NeZero i] {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)

/-- **The second scalar fact `ψ(π(Frob_w)) = 1 + t`** (PROVED; tex 2781–2783, 4266–4268): if
`ψ ∘ π` is the inflation of a moving character `Ψ = (1 + t)^ξ` on `G_{K,S_r}` (`S_r ⊆ S₀`) and `Ψ`
takes the value `1 + t` on every arithmetic Frobenius lift at the place `v` of `w` — for lane
E1's genuine moving character at an active orientation `v = 𝔭_j`, the third clause of
`movingPsi_genuine`. -/
theorem psi_frob_eq_onePlusT (hSr : Sr ⊆ S₀) (w : NewPlaces K S₀ S)
    (ξ : GKS K Sr →* Multiplicative (ZMod (2 ^ (2 * i))))
    (hΨ : ∀ g, ψ (π g) = movingCharS i ξ (inflMap K hSr g)) (v : HeightOneSpectrum (𝓞 K))
    (hwv : w.1 = v)
    (hact : ∀ φ : Gloc K v, TauCeti.IsArithFrobeniusLift (v.adicCompletion K) φ →
      movingCharS i ξ (locMap K Sr v φ) = ZInQ.Manuscript.RC.CoefModules.onePlusT i) :
    ψ (π (urFrobElt K w)) = ZInQ.Manuscript.RC.CoefModules.onePlusT i := by
  rcases w with ⟨w₁, hw₁⟩
  dsimp only at hwv
  subst hwv
  obtain ⟨φ, hφ⟩ := TauCeti.exists_isArithFrobeniusLift (w₁.adicCompletion K)
  rw [← locMap_frobLift ⟨w₁, hw₁⟩ φ hφ, hΨ, locMap_compat K hSr w₁ φ]
  exact hact φ hφ

variable (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)

/-- **Lane RC32's `CharValueAt` for the leaf's value at an unused active orientation** (PROVED;
tex 4144–4145, 4283–4292): at a place `w ∉ S₀` of residue degree one over an unused odd prime
`q ∈ Q` not dividing `h_x = h`, with `ψ ∘ π` the inflation of a moving character equal to `1 + t`
on the Frobenius lifts at `w`, the stage character `stageRingChar i (χ_h · ψ ∘ π)` takes the
leaf's value `zAt Fam x q` (pushed to the stage) at `Frob_w`. -/
theorem charValueAt_leaf_genuine (w : NewPlaces K S₀ S) (Fam : ZInQ.Manuscript.RC.Family)
    (hQ : ∀ q ∈ Fam.Q, q.Prime) (x : ZInQ.Manuscript.RC.Addr Fam.b) {q : ℕ} (hqQ : q ∈ Fam.Q)
    (hx : Fam.lam q x = 0) (hq2 : q ≠ 2) (hcard : Nat.card (𝓞 K ⧸ w.1.asIdeal) = q)
    (hn : ¬ (q : ℤ) ∣ Fam.h x) (hh : h = (Fam.h x : K)) (hSr : Sr ⊆ S₀)
    (ξ : GKS K Sr →* Multiplicative (ZMod (2 ^ (2 * i))))
    (hΨ : ∀ g, ψ (π g) = movingCharS i ξ (inflMap K hSr g))
    (hact : ∀ φ : Gloc K w.1, TauCeti.IsArithFrobeniusLift (w.1.adicCompletion K) φ →
      movingCharS i ξ (locMap K Sr w.1 φ) = ZInQ.Manuscript.RC.CoefModules.onePlusT i) :
    CharValueAt (stageRingChar i (alphaStage i s hs hs0 π ψ)) w
      (stageMk i (zAt Fam x q : LamI)) :=
  charValueAt_leaf i s hs hs0 π ψ w Fam x q
    (quadChar_frob_eq_frobSign s hs hs0 w Fam hQ x hqQ hx hq2 hcard hn hh)
    (psi_frob_eq_onePlusT π ψ hSr w ξ hΨ w.1 rfl hact)

end PsiFact

end ZInQ.Contrib.CloudB3E2.NormCochain

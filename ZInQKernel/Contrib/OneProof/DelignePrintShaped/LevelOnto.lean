import ZInQKernel.Contrib.OneProof.DelignePrintShaped.Bridges

/-! # The onto half of the level-3 classification over `ℂ`

Proved here (standard axioms only): from T2a (`VoightQMComplexModuliPrint`, its second clause, Voight
Prop. 43.6.28) and T2c′ (`BoutotCarayolPolarizationPrint`, Boutot–Carayol Prop. 1.5 over `ℂ`), every complex QM
abelian surface with full level-3 structure `P` is the moduli object of some point `[z, g]` (`levelOnto_of`).

* **The level points of `ℂ²/Λ_τ`** (`exists_isLevelTorusAt`): `P` carries a principal polarization of type `μ`
  (T2c′), so T2a gives `τ ∈ ℍ` and an `ι`-equivariant uniformization `Φu : ℂ² → P.A(ℂ)` with kernel `Λ_τ`. The point `η(1)` is `3`-torsion, so `η(1) = Φu(ℓ_τ(w)/3)`
  for some `w ∈ 𝒪`, and `𝒪`-linearity gives `η(a) = Φu(ℓ_τ(a w)/3)` for all `a ∈ 𝒪`. The kernel of `η` being
  `3𝒪`, right multiplication by `w` is injective on `𝒪/3𝒪`.
* **`w` is a unit modulo `3`** (`LevelOntoAux.not_three_dvd_nrd`): otherwise `3 ∣ nrd(w) = w̄ w` puts `w̄`, hence
  `w`, hence `1` in `3𝒪`.
* **An adelic unit** (`LevelOntoAux.exists_invModThree_of_nrd`, `exists_invModThree_of_injective`): with
  `e₃ ∈ ℤ̂` the idempotent supported at the place `3`, `u = (1 − e₃) + e₃ nrd(w)⁻¹ w̄` lies in `𝒪̂^×` (its inverse
  is `(1 − e₃) + e₃ w`) and `w u = 1 + (1 − e₃)(w − 1) ∈ 1 + 3𝒪̂`, because `(1 − e₃)/3 ∈ ℤ̂`.
-/

set_option autoImplicit false

noncomputable section

namespace DelignePS

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open Y3Hodge (HPM DCRelPM toPM)

namespace LevelOntoAux

/-! ## 1. The idempotent of `ℤ̂` at the place `3` -/

section Idempotent

open IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

/-- The place `3` of `ℚ`. -/
def placeThree : HeightOneSpectrum (𝓞 ℚ) := (primesEquiv (R := 𝓞 ℚ)).symm ⟨3, Nat.prime_three⟩

theorem primesEquiv_placeThree : ((primesEquiv (R := 𝓞 ℚ) placeThree : Nat.Primes) : ℕ) = 3 :=
  congrArg (fun p : Nat.Primes => (p : ℕ)) ((primesEquiv (R := 𝓞 ℚ)).apply_symm_apply _)

theorem eq_placeThree {v : HeightOneSpectrum (𝓞 ℚ)} (h : (primesEquiv (R := 𝓞 ℚ) v : ℕ) ∣ 3) :
    v = placeThree := by
  have h3 : (primesEquiv (R := 𝓞 ℚ) v : ℕ) = 3 :=
    (Nat.prime_dvd_prime_iff_eq (primesEquiv (R := 𝓞 ℚ) v).2 Nat.prime_three).1 h
  apply (primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext (h3.trans primesEquiv_placeThree.symm)

/-- If the prime of `v` does not divide `N`, then `1/N` is integral at `v`. -/
theorem inv_natCast_mem {v : HeightOneSpectrum (𝓞 ℚ)} {N : ℕ}
    (hN : ¬ (primesEquiv (R := 𝓞 ℚ) v : ℕ) ∣ N) :
    algebraMap ℚ AQ ((N : ℚ)⁻¹) v ∈ v.adicCompletionIntegers ℚ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (dvd_zero _)
  have hcop : (primesEquiv (R := 𝓞 ℚ) v : ℕ).Coprime N :=
    (Nat.Prime.coprime_iff_not_dvd (primesEquiv (R := 𝓞 ℚ) v).2).2 hN
  have hu : IsUnit ((N : ℕ) : ℤ_[primesEquiv (R := 𝓞 ℚ) v]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
  let loc : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv (R := 𝓞 ℚ) v] :=
    (adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v :
      v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv (R := 𝓞 ℚ) v])
  set d : v.adicCompletionIntegers ℚ := loc.symm (↑(hu.unit⁻¹)) with hd
  have h1 : (N : v.adicCompletionIntegers ℚ) * d = 1 := by
    apply loc.injective
    rw [map_mul, map_natCast, hd, RingEquiv.apply_symm_apply, map_one]
    exact hu.mul_val_inv
  have h2 : (N : v.adicCompletion ℚ) * (d : v.adicCompletion ℚ) = 1 := by
    have h := congrArg (v.adicCompletionIntegers ℚ).subtype h1
    rwa [map_mul, map_natCast, map_one] at h
  have hc : (N : AQ) * algebraMap ℚ AQ ((N : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ AQ) N, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN0),
      map_one]
  have h3 := congrArg (evQ v) hc
  rw [map_mul, map_natCast, map_one, evQ_apply] at h3
  have h4 : algebraMap ℚ AQ ((N : ℚ)⁻¹) v = d := by
    calc algebraMap ℚ AQ ((N : ℚ)⁻¹) v
        = ((d : v.adicCompletion ℚ) * N) * algebraMap ℚ AQ ((N : ℚ)⁻¹) v := by
          rw [mul_comm (d : v.adicCompletion ℚ), h2, one_mul]
      _ = d * (N * algebraMap ℚ AQ ((N : ℚ)⁻¹) v) := mul_assoc _ _ _
      _ = d := by rw [h3, mul_one]
  rw [h4]
  exact d.2

open Classical in
/-- The idempotent `e₃ ∈ ℤ̂` supported at the place `3`. -/
def eThree : AQ :=
  ⟨fun v => if v = placeThree then 1 else 0, Filter.Eventually.of_forall fun v => by
    dsimp only
    split_ifs
    · exact SetLike.mem_coe.2 (one_mem _)
    · exact SetLike.mem_coe.2 (zero_mem _)⟩

open Classical in
theorem eThree_apply (v : HeightOneSpectrum (𝓞 ℚ)) :
    eThree v = if v = placeThree then 1 else 0 := rfl

theorem eThree_mem : eThree ∈ ZhatQ := fun v => by
  rw [eThree_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem eThree_mul_self : eThree * eThree = eThree := by
  refine FiniteAdeleRing.ext ℚ fun v => ?_
  change evQ v (eThree * eThree) = evQ v eThree
  rw [map_mul, evQ_apply, eThree_apply]
  split_ifs <;> simp

/-- `f₃ = (1 − e₃)/3`. -/
def fThree : AQ := (1 - eThree) * algebraMap ℚ AQ (((3 : ℕ) : ℚ)⁻¹)

theorem fThree_mem : fThree ∈ ZhatQ := fun v => by
  change evQ v ((1 - eThree) * algebraMap ℚ AQ (((3 : ℕ) : ℚ)⁻¹)) ∈ _
  rw [map_mul, map_sub, map_one, evQ_apply, evQ_apply, eThree_apply]
  split_ifs with h
  · rw [sub_self, zero_mul]
    exact zero_mem _
  · rw [sub_zero, one_mul]
    exact inv_natCast_mem fun h3 => h (eq_placeThree h3)

theorem three_mul_fThree : (3 : AQ) * fThree = 1 - eThree := by
  have h : (3 : AQ) * algebraMap ℚ AQ (((3 : ℕ) : ℚ)⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap ℚ AQ) 3, ← map_mul]
    norm_num
  rw [fThree, mul_left_comm, h, mul_one]

/-- `e₃ / N ∈ ℤ̂` for `3 ∤ N`. -/
theorem eThree_mul_inv_mem {N : ℕ} (hN : ¬ 3 ∣ N) :
    eThree * algebraMap ℚ AQ ((N : ℚ)⁻¹) ∈ ZhatQ := fun v => by
  change evQ v (eThree * algebraMap ℚ AQ ((N : ℚ)⁻¹)) ∈ _
  rw [map_mul, evQ_apply, evQ_apply, eThree_apply]
  split_ifs with h
  · subst h
    rw [one_mul]
    exact inv_natCast_mem (by rw [primesEquiv_placeThree]; exact hN)
  · rw [zero_mul]
    exact zero_mem _

theorem eThree_mul_inv_int_mem {N : ℤ} (hN : ¬ (3 : ℤ) ∣ N) :
    eThree * algebraMap ℚ AQ ((N : ℚ)⁻¹) ∈ ZhatQ := by
  have hN' : ¬ 3 ∣ N.natAbs := fun h => hN (by exact_mod_cast Int.ofNat_dvd_left.2 h)
  rcases Int.natAbs_eq N with h | h
  · rw [h, Int.cast_natCast]
    exact eThree_mul_inv_mem hN'
  · rw [h, Int.cast_neg, Int.cast_natCast, inv_neg, map_neg, mul_neg]
    exact ZhatS.neg_mem (eThree_mul_inv_mem hN')

end Idempotent

/-! ## 2. `𝒪̂` is a `ℤ̂`-module; reduced norms on `𝒪` -/

theorem algebraMap_mem_OhatQ {a : AQ} (ha : a ∈ ZhatQ) : algebraMap AQ BAQ a ∈ OhatQ := by
  refine OhatQ_of_cQ fun i => ?_
  fin_cases i
  · show a - 0 ∈ ZhatQ
    rw [sub_zero]
    exact ha
  · show (0 : AQ) - 0 ∈ ZhatQ
    rw [sub_zero]
    exact ZhatS.zero_mem
  · show (2 : AQ) * 0 ∈ ZhatQ
    rw [mul_zero]
    exact ZhatS.zero_mem
  · show (2 : AQ) * 0 ∈ ZhatQ
    rw [mul_zero]
    exact ZhatS.zero_mem

theorem smul_mem_OhatQ {a : AQ} (ha : a ∈ ZhatQ) {x : BAQ} (hx : x ∈ OhatQ) : a • x ∈ OhatQ := by
  rw [Algebra.smul_def]
  exact OhatQ_mul (algebraMap_mem_OhatQ ha) hx

theorem three_mul_eq_smul (x : BAQ) : (3 : BAQ) * x = (3 : AQ) • x := by
  rw [Algebra.smul_def, map_ofNat]

theorem coe_three_O : ((3 : O) : B) = 3 := map_ofNat O.subtype 3

/-- The reduced norm of an element of `𝒪` is an integer. -/
theorem exists_int_nrd {w : B} (hw : w ∈ O) : ∃ N : ℤ, ShimuraGlue.nrdQ ℚ w = N := by
  have h := nrd_mem_of_mem (bEmb_mem_of_inO hw)
  rw [nrd_bEmb] at h
  exact (rat_mem_zhat_iff _).1 h

theorem bEmb_intCast (N : ℤ) : bEmb (((N : ℚ) : B)) = (N : BAQ) :=
  (bEmb.commutes (N : ℚ)).trans (map_intCast _ N)

theorem bEmb_star_mul {w : B} {N : ℤ} (hN : ShimuraGlue.nrdQ ℚ w = N) :
    bEmb (star w) * bEmb w = (N : AQ) • (1 : BAQ) := by
  rw [← map_mul, star_mul_eq, ← nrd_coe_eq, hN, bEmb_intCast, Algebra.smul_def, mul_one, map_intCast]

theorem bEmb_mul_star {w : B} {N : ℤ} (hN : ShimuraGlue.nrdQ ℚ w = N) :
    bEmb w * bEmb (star w) = (N : AQ) • (1 : BAQ) := by
  rw [← map_mul, ← nrd_coe_eq, hN, bEmb_intCast, Algebra.smul_def, mul_one, map_intCast]

/-! ## 3. The adelic unit `u ≡ w⁻¹ (mod 3)` -/

/-- **For `w ∈ 𝒪` with `3 ∤ nrd(w)`, some `u ∈ 𝒪̂^×` has `w u ∈ 1 + 3𝒪̂`**:
`u = (1 − e₃) + e₃ nrd(w)⁻¹ w̄`, with inverse `(1 − e₃) + e₃ w`. -/
theorem exists_invModThree_of_nrd {w : O} {N : ℤ} (hN : ShimuraGlue.nrdQ ℚ (w : B) = N)
    (h3 : ¬ (3 : ℤ) ∣ N) : ∃ u ∈ OhatU, InvModThree u w := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact h3 (dvd_zero 3)
  have hee : eThree * eThree = eThree := eThree_mul_self
  have hNc : (N : AQ) * algebraMap ℚ AQ ((N : ℚ)⁻¹) = 1 := by
    rw [← map_intCast (algebraMap ℚ AQ) N, ← map_mul, mul_inv_cancel₀ (Int.cast_ne_zero.2 hN0),
      map_one]
  have hf : (3 : AQ) * fThree = 1 - eThree := three_mul_fThree
  have hSW := bEmb_star_mul hN
  have hWS := bEmb_mul_star hN
  set e : AQ := eThree with he_def
  set c : AQ := algebraMap ℚ AQ ((N : ℚ)⁻¹) with hc_def
  set f : AQ := fThree with hf_def
  set W : BAQ := bEmb (w : B) with hW_def
  set S : BAQ := bEmb (star (w : B)) with hS_def
  have h1e : 1 - e ∈ ZhatQ := ZhatS.sub_mem ZhatS.one_mem eThree_mem
  have hec : e * c ∈ ZhatQ := eThree_mul_inv_int_mem h3
  have hxy : ((1 - e) • (1 : BAQ) + (e * c) • S) * ((1 - e) • (1 : BAQ) + e • W) = 1 := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hSW]
    match_scalars <;> first
      | linear_combination (1 + c * (N : AQ)) * hee + e * hNc
      | linear_combination -hee
      | linear_combination -c * hee
  have hyx : ((1 - e) • (1 : BAQ) + e • W) * ((1 - e) • (1 : BAQ) + (e * c) • S) = 1 := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hWS]
    match_scalars <;> first
      | linear_combination (1 + c * (N : AQ)) * hee + e * hNc
      | linear_combination -hee
      | linear_combination -c * hee
  refine ⟨⟨_, _, hxy, hyx⟩, ⟨?_, ?_⟩, f • (W - 1), ?_, ?_⟩
  · exact OhatQ_add (smul_mem_OhatQ h1e OhatQ_one)
      (smul_mem_OhatQ hec (bEmb_mem_of_inO (inO_star w.2)))
  · exact OhatQ_add (smul_mem_OhatQ h1e OhatQ_one) (smul_mem_OhatQ eThree_mem (bEmb_mem_of_inO w.2))
  · refine smul_mem_OhatQ fThree_mem ?_
    rw [sub_eq_add_neg]
    exact OhatQ_add (bEmb_mem_of_inO w.2) (OhatQ_neg OhatQ_one)
  · show W * ((1 - e) • (1 : BAQ) + (e * c) • S) = 1 + 3 * (f • (W - 1))
    rw [three_mul_eq_smul]
    simp only [mul_add, mul_smul_comm, mul_one, hWS, smul_smul, smul_sub]
    match_scalars <;> first
      | linear_combination -hf
      | linear_combination e * hNc + hf

/-! ## 4. Units modulo `3` -/

/-- **If right multiplication by `w ∈ 𝒪` is injective on `𝒪/3𝒪`, then `3 ∤ nrd(w)`**: otherwise `w̄ w = nrd(w)`
puts `w̄` in `3𝒪`, so `w = 3 b̄`, and then `1 · w ∈ 3𝒪` puts `1` in `3𝒪`, against `nrd(3) = 9`. -/
theorem not_three_dvd_nrd {w : O}
    (hinj : ∀ a : O, (3 : ℚ)⁻¹ • ((a : B) * (w : B)) ∈ O → ∃ b : O, a = 3 * b)
    {N : ℤ} (hN : ShimuraGlue.nrdQ ℚ (w : B) = N) : ¬ (3 : ℤ) ∣ N := by
  rintro ⟨k, rfl⟩
  have h1 : (3 : ℚ)⁻¹ • (star (w : B) * (w : B)) ∈ O := by
    have e1 : star (w : B) * (w : B) = ((((3 * k : ℤ) : ℚ)) : B) := by
      rw [star_mul_eq, ← nrd_coe_eq, hN]
    have e2 : (3 : ℚ)⁻¹ • ((((3 * k : ℤ) : ℚ)) : B) = ((k : ℤ) : B) := by
      rw [show ((((3 * k : ℤ) : ℚ)) : B) = algebraMap ℚ B ((3 * k : ℤ) : ℚ) from rfl, Algebra.smul_def,
        ← map_mul, show (3 : ℚ)⁻¹ * ((3 * k : ℤ) : ℚ) = (k : ℚ) by push_cast; ring, map_intCast]
    rw [e1, e2]
    exact intCast_mem O k
  obtain ⟨b, hb⟩ := hinj ⟨star (w : B), inO_star w.2⟩ h1
  have hb' : star (w : B) = 3 * (b : B) := by
    have := congrArg Subtype.val hb
    rwa [Subring.coe_mul, coe_three_O] at this
  have hw3 : (w : B) = 3 * star (b : B) := by
    calc (w : B) = star (star (w : B)) := (star_star _).symm
      _ = star (3 * (b : B)) := by rw [hb']
      _ = star (b : B) * 3 := by rw [star_mul, star_ofNat]
      _ = 3 * star (b : B) := (Commute.ofNat_right _ 3).eq
  have h2 : (3 : ℚ)⁻¹ • (((1 : O) : B) * (w : B)) ∈ O := by
    have e3 : (3 : ℚ)⁻¹ • (((1 : O) : B) * (w : B)) = star (b : B) := by
      rw [OneMemClass.coe_one, one_mul, hw3,
        show (3 : B) * star (b : B) = (3 : ℚ) • star (b : B) by rw [Algebra.smul_def]; simp, smul_smul]
      norm_num
    rw [e3]
    exact inO_star b.2
  obtain ⟨b', hb''⟩ := hinj 1 h2
  obtain ⟨M, hM⟩ := exists_int_nrd b'.2
  have h4 := congrArg (fun z : O => ShimuraGlue.nrdQ ℚ (z : B)) hb''
  simp only [OneMemClass.coe_one, map_one, Subring.coe_mul, map_mul, hM] at h4
  have h9 : ShimuraGlue.nrdQ ℚ ((3 : O) : B) = 9 := by
    rw [coe_three_O, show (3 : B) = ((3 : ℚ) : B) from (map_ofNat (algebraMap ℚ B) 3).symm,
      ShimuraGlue.nrdQ_apply]
    show (3 : ℚ) ^ 2 - 2 * 0 ^ 2 + 3 * 0 ^ 2 - 6 * 0 ^ 2 = 9
    norm_num
  rw [h9] at h4
  have h5 : (1 : ℤ) = 9 * M := by exact_mod_cast h4
  omega

end LevelOntoAux

open LevelOntoAux

/-- **The adelic step**: if right multiplication by `w ∈ 𝒪` is injective on `𝒪/3𝒪`, then some `u ∈ 𝒪̂^×` has
`w ≡ u⁻¹ (mod 3𝒪̂)`. -/
theorem exists_invModThree_of_injective {w : O}
    (hinj : ∀ a : O, (3 : ℚ)⁻¹ • ((a : B) * (w : B)) ∈ O → ∃ b : O, a = 3 * b) :
    ∃ u ∈ OhatU, InvModThree u w := by
  obtain ⟨N, hN⟩ := exists_int_nrd w.2
  exact exists_invModThree_of_nrd hN (not_three_dvd_nrd hinj hN)

/-! ## 5. The level structure of `P` on `ℂ²/Λ_τ` -/

/-- **Every principally polarized `P` is `(ℂ²/Λ_τ, ι_τ, η_w)`** for some `τ ∈ ℍ` and `w ∈ 𝒪` (T2a's second
clause), and right multiplication by `w` is injective on `𝒪/3𝒪` (the kernel of `η` is `3𝒪`). -/
theorem exists_isLevelTorusAt (hV : VoightQMComplexModuliPrint) (P : QML3 ℂ)
    (hP : HasPrincipalRiemannMu P.A P.q) :
    ∃ (τ : UpperHalfPlane) (w : O), IsLevelTorusAt P τ w ∧
      ∀ a : O, (3 : ℚ)⁻¹ • ((a : B) * (w : B)) ∈ O → ∃ b : O, a = 3 * b := by
  obtain ⟨τ, Φu, hU, hι⟩ := hV.2.1 P.A P.surface P.q hP
  obtain ⟨-, hker, hsurj⟩ := (ZInQ.HomLattice.isUniformization_iff _ _ _).mp hU
  obtain ⟨z0, hz0⟩ := hsurj (Additive.toMul (P.e.eta 1))
  have h3 : P.e.eta 3 = 0 := (P.e.ker 3).2 ⟨1, (mul_one 3).symm⟩
  have h3' : P.e.eta 1 + P.e.eta 1 + P.e.eta 1 = 0 := by
    have e3 : (3 : O) = 1 + 1 + 1 := by norm_num
    rwa [e3, map_add, map_add] at h3
  have hz3 : z0 + z0 + z0 ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
    rw [← hker, hU.1, hU.1, hz0]
    have := congrArg Additive.toMul h3'
    simp only [toMul_add, toMul_zero] at this
    exact this
  obtain ⟨c, hc, hce⟩ := (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ _).1 hz3
  set w : O := ⟨c, hc⟩ with hw_def
  have hw3 : ell τ (w : B) = z0 + z0 + z0 := (Y3Fix.latVec_eq τ c).symm.trans hce.symm
  have hz0' : z0 = (3 : ℂ)⁻¹ • ell τ (w : B) := by
    rw [hw3]
    have : z0 + z0 + z0 = (3 : ℂ) • z0 := by
      rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ three_ne_zero, one_smul]
  have hη : ∀ a : O, Additive.toMul (P.e.eta a) = Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) := by
    intro a
    have h1 : P.e.eta a = qmAct P.q ℂ a (P.e.eta 1) := by
      have := P.e.linear a 1
      rwa [mul_one] at this
    have h4 : Φu ((qmMat a).mulVec z0) = Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) := by
      rw [hz0', Matrix.mulVec_smul, ← ell_mul]
    have h5 : Φu ((qmMat a).mulVec z0) = Φu z0 ≫ (P.q.iota a).hom := hι a z0
    rw [h1, ← h4, h5, hz0]
    rfl
  refine ⟨τ, w, ⟨Φu, hU, hι, fun a => ?_⟩, fun a ha => ?_⟩
  · rw [hη a, Subring.coe_mul]
  · apply (P.e.ker a).1
    have hmem : (3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B)) ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
      rw [third_smul_ell, ell_mem_iff]
      exact ha
    have h1 : Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) = 1 := (hker _).2 hmem
    apply Additive.toMul.injective
    rw [hη a, h1]
    rfl

/-! ## 6. `LevelOnto` from T2a and T2c′ -/

/-- **The onto half of the level-3 classification over `ℂ`**: from T2a and T2c′, every complex QM abelian surface
with full level-3 structure is the moduli object of a point `[τ, u]` with `τ ∈ ℍ` and `u ∈ 𝒪̂^×`. -/
theorem levelOnto_of (hV : VoightQMComplexModuliPrint) (hP : BoutotCarayolPolarizationPrint) : LevelOnto := by
  intro P
  obtain ⟨τ, w, hT, hinj⟩ := exists_isLevelTorusAt hV P (hP P)
  obtain ⟨u, hu, huw⟩ := exists_invModThree_of_injective hinj
  exact ⟨toPM τ, u, τ, u, w, hu, dcRelPM_refl _ _, huw, hT⟩

end DelignePS

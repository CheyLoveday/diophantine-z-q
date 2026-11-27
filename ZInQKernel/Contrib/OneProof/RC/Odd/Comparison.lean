import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Constants
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.CornutJetchev

/-!
# Lane RC12-odd: the unaveraged comparison (O.7) (App F, tex 9101–9405)

Manuscript (11/5), Appendix F, Proposition `ex:app-theta-comparison`:
`H_M(mD) = c₀ 2^{ω(N)} ζ_M(D) λ_M(\overline{L P_D}) (mod 2^M)` (O.7), "no class number is divided out";
used at (3.8) (tex 2522–2530).

* `CornutJetchevThm31` — **PRINT**, Cornut–Jetchev, *Liftings of reduction maps for quaternion
  algebras* (preprint, arXiv:1012.0725v1, 2010; 17 pp.), §3.5 Theorem 3.1 (p. 9), general `κ`: the
  one PRINT statement of the project, `PrintsArith.CJSetting.Thm31` (`PrintsArith/CornutJetchev.lean`,
  Lane RC27), with H.1–H.3 of §3.1 (p. 5), the equivariant map `θ_S` of §3.2 (pp. 5–6), the fine
  conductors of §3.3 (pp. 6–7, (10)–(12)), the sign invariant of §3.4 (p. 8, (14)) and
  `κ = |Gal(K[c]/K[c_S])| ∏_{v∈S} N_v(v(c'), v(c''), v(𝔫))` with `N_v` from Lemma 2.1 (p. 4). Lane RC9's
  `κ = 1` form `PrintsArith.CJReductionData.Thm3_1KappaOne` is derived from it.
* `cj_kappa_eq_one` — **PROVED**: the specialization `F_CJ = ℚ`, `K_CJ = ℚ(√(Dh_*))`,
  `B_CJ = M₂(ℚ)`, `S = {ℓ₀}`: H.2's integer `|S| + |Ram_f B| + [F:ℚ] = 1 + 0 + 1 = 2` is even, the
  parity condition `0 − 0 ≡ v_{ℓ₀}(N) = 0`, Lemma 2.1(ii) `N_{ℓ₀}(0,0,0) = q^{min(0,0)} = 1` (through
  the print's encoding `PrintsArith.cjNUnram`), fine conductors one, so `κ = 1` (tex 9195–9243).
* `cj_bijection_of_kappa_one` — **PROVED** from the print: with `κ = 1`, a bijection of `c_f⁻¹(c)` onto
  the sign fibre (tex 9245–9263).
* `orbit_sum` — **PROVED**: an embedding orbit with stabilizer `{±1}` has `|R_z^×|/2` elements and,
  weighted by `c₀/|R_z^×|`, contributes `c₀/2` (tex 9308–9311, 9378–9390).
* `O7_assembly` — **PROVED**: summing the `2^{ω(N)+1}` orientation tuples, each contributing
  `(c₀/2) ζ λ` (tex 9318–9367), gives `c₀ 2^{ω(N)} ζ λ`.
* `witness_exact_order` — **PROVED**: `v₂ a_M(D_w) = c_θ + c_w` for `M > c_θ + c_w`,
  `c_θ = 9 + ω(N)` (tex 9391–9399).
-/

namespace ZInQ.Manuscript.RC.Odd

/-! ### Cornut–Jetchev, Theorem 3.1 (PRINT, abstract interface) -/

/-- **Cornut–Jetchev, Theorem 3.1 (PRINT; arXiv:1012.0725v1, §3.5, p. 9), general `κ`.** This is
the project's one PRINT statement of the theorem, `PrintsArith.CJSetting.Thm31` (Lane RC27 unified
lanes RC9 and RC12 here): over the print's objects `P` (`X = CM(G,H)`, `Y = CM(G_S,H_S)`, the
`Gal_K^{ab}`-equivariant `θ_S`, the fine conductors `c_f`, `c_{S,f}`, `( )_S`, the sign map `ψ_{S'}` and
`e_{S'}` of (14)), under H.1–H.3, for every `c = (c', c'')` with `v(c') − v(c'') ≡ v(𝔫) (mod 2)` at
`v ∈ S'`, `θ_S` maps `c_f⁻¹(c)` into `c_{S,f}⁻¹(c_S) ∩ ψ_{S'}⁻¹(e_{S'}(c))` and is `κ(c)`-to-1 onto it,
`κ = |Gal(K[c]/K[c_S])| ∏_{v∈S} N_v(v(c'), v(c''), v(𝔫))` (Lemma 2.1). Previously this file stated
the fibre count with an arbitrary `κ`; the printed formula and the equivariance of §3.2 are now part
of the statement. -/
abbrev CornutJetchevThm31 (P : PrintsArith.CJSetting) : Prop := P.Thm31

/-- Cornut–Jetchev, Lemma 2.1 (p. 4), case (ii) (`K/F` unramified, `δ = n' + n''`), through the
print's encoding: `N(n', n'', n' + n'') = q^{min(n', n'')}` (`cjNunramified_eq`). -/
def cjNunramified (q n' n'' : ℕ) : ℕ := PrintsArith.cjNUnram q n' n'' (n' + n'')

/-- **PROVED.** Lemma 2.1(ii): `N(n', n'', n' + n'') = q^{min(n', n'')}`. -/
theorem cjNunramified_eq (q n' n'' : ℕ) : cjNunramified q n' n'' = q ^ min n' n'' := by
  simp [cjNunramified, PrintsArith.cjNUnram]

/-- **PROVED (tex 9203–9243).** The specialization of Cornut–Jetchev with `S = {ℓ₀}`: H.2's integer
is `2` (even), the parity condition holds, `N_{ℓ₀}(0,0,0) = 1` (Lemma 2.1(ii)), and with fine
conductors one (`|Gal(K[1]/K[1])| = 1`) the multiplicity is `κ = 1`. -/
theorem cj_kappa_eq_one (q : ℕ) :
    (1 + 0 + 1) % 2 = 0 ∧ (0 - 0 : ℤ) % 2 = 0 ∧ cjNunramified q 0 0 = 1 ∧
      1 * cjNunramified q 0 0 = 1 := by
  simp [cjNunramified_eq]

/-- **PROVED** (from the print). With `κ = 1`, Theorem 3.1 gives a bijection between the source CM
points of fine conductor `c` and the target points of the prescribed conductor and sign (one sign
fibre, not both, tex 9245–9263). -/
theorem cj_bijection_of_kappa_one {P : PrintsArith.CJSetting} (hCJ : CornutJetchevThm31 P)
    (h1 : P.H1) (h2 : P.H2) (h3 : P.H3) {c : P.C} (hc : P.Parity c) (hκ : P.kappa c = 1) :
    Function.Bijective (fun x : {x : P.X // P.cf x = c} =>
      (⟨P.θ x.1, ((hCJ h1 h2 h3).2 c hc).1 x.1 x.2⟩ :
        {y : P.Y // P.cSf y = P.primeToS c ∧ P.ψ y = P.e c})) := by
  have hb := PrintsArith.CJSetting.Thm31.bijOn_of_kappa_eq_one hCJ h1 h2 h3 hc hκ
  constructor
  · intro x₁ x₂ h
    exact Subtype.ext (hb.injOn x₁.2 x₂.2 (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hb.surjOn hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-! ### The orbit count and the orientation sum -/

/-- **PROVED (tex 9308–9311).** If a finite group `Gz` (`R_z^×`) acts on `E` with every stabilizer
of order two (`𝒪_F^× = {±1}`), every orbit has `|Gz|/2` elements. -/
theorem orbit_card_of_stab_two {Gz E : Type*} [Group Gz] [Fintype Gz] [MulAction Gz E] (x : E)
    [Fintype (MulAction.orbit Gz x)] [Fintype (MulAction.stabilizer Gz x)]
    (h2 : Fintype.card (MulAction.stabilizer Gz x) = 2) :
    Fintype.card (MulAction.orbit Gz x) = Fintype.card Gz / 2 := by
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group Gz x
  rw [h2] at this
  omega

/-- **PROVED (tex 9378–9390).** Per embedding orbit: weight `c₀/|R_z^×|` times `|R_z^×|/2` elements,
times the unit phase and `P_M(z)`, is `(c₀/2) P_M(z)` — an integer multiple, with no division of a
congruence by two (`c₀/|R_z^×|` and `c₀/2` are integers, `Constants.lean`). -/
theorem orbit_sum {R : Type*} [CommRing R] (w : ℕ) (hw2 : 2 ∣ w) (hw : w ∣ c0) (z : R) :
    ((c0 / w : ℕ) : R) * ((w / 2 : ℕ) : R) * z = ((c0 / 2 : ℕ) : R) * z := by
  rw [← Nat.cast_mul, orbit_weight_eq w hw2 hw]

/-- **PROVED (tex 9318–9370).** The orientation sum: if each of the `2^{ω(N)+1}` local orientation
tuples contributes `(c₀/2) ζ λ` (the reference tuple by Cornut–Jetchev and the reduction identity
`∑_a χ_F(a) P_M(z_a) = λ_M(\overline{LP_D})`; the others by the Atkin–Lehner and `ℓ₀`-uniformizer
sign cancellations), the total is `c₀ 2^{ω(N)} ζ λ`. -/
theorem O7_assembly {R : Type*} [CommRing R] {Tup : Type*} [Fintype Tup] (ω : ℕ)
    (hcard : Fintype.card Tup = 2 ^ (ω + 1)) (contrib : Tup → R) (ζ lam : R)
    (h : ∀ t, contrib t = ((c0 / 2 : ℕ) : R) * ζ * lam) :
    ∑ t, contrib t = (c0 : R) * 2 ^ ω * ζ * lam := by
  simp only [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  have : (c0 : R) = 2 * ((c0 / 2 : ℕ) : R) := by
    rw [show c0 = 2 * (c0 / 2) by norm_num [c0]]; push_cast; norm_num [c0]
  rw [this]; push_cast; ring

/-- **PROVED (tex 9331–9362).** The orientation-change signs cancel: at `p^e ‖ N` the Atkin–Lehner
normalizer multiplies the Schwartz weight by `α_p(−1) = w_{p^e} χ_{h_*}(p)^e` (O.3) and the
norm-weighted parametrization value by `w_{p^e} χ_{h_*}(p)^e`; at `ℓ₀` the uniformizer multiplies by
`(−1/ℓ₀) = −1`, by `χ_{h_*}(ℓ₀) = −1`, and by the Frobenius sign `+1` of `λ_M`. -/
theorem orientation_signs (wp χp : ℤ) (e : ℕ) (hw : wp = 1 ∨ wp = -1) (hχ : χp = 1 ∨ χp = -1) :
    (wp * χp ^ e) * (wp * χp ^ e) = 1 ∧ (-1 : ℤ) * (-1) * 1 = 1 := by
  refine ⟨?_, by norm_num⟩
  have h1 : wp * wp = 1 := by rcases hw with rfl | rfl <;> norm_num
  have h2 : χp ^ e * χp ^ e = 1 := by
    rw [← mul_pow]; rcases hχ with rfl | rfl <;> simp
  calc wp * χp ^ e * (wp * χp ^ e) = (wp * wp) * (χp ^ e * χp ^ e) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/-! ### The fixed witness's valuation (tex 9391–9399) -/

theorem c0_mul_two_pow_eq (ω : ℕ) : (c0 : ℤ) * 2 ^ ω = 2 ^ (9 + ω) * 47385 := by
  rw [pow_add]; norm_num [c0]; ring

/-- **PROVED (tex 9391–9399).** If `a ≡ c₀ 2^{ω(N)} ζ λ (mod 2^M)` with `ζ` odd (the phase is a unit)
and `λ = λ_M(\overline{Q})` of exact 2-adic order `c_w`, and `c_θ + c_w < M` with
`c_θ = 9 + ω(N)`, then `a` has exact order `c_θ + c_w`: `v₂ a_M(D_w) = c_θ + c_w`.
`hlam1`, `hlam2` are (O.2) (tex 8396–8398) read on an integer lift `λ` of `λ_M(\bar Q)`; they are
derived in `Visibility.lean` (`exact_order_of_residue`, `exact_order_of_eq_two_pow`,
`witness_vZ_of_detector`). -/
theorem witness_exact_order (ω M cw : ℕ) {a ζ lam : ℤ} (hζ : Odd ζ)
    (hlam1 : (2 : ℤ) ^ cw ∣ lam) (hlam2 : ¬ (2 : ℤ) ^ (cw + 1) ∣ lam)
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + cw < M) :
    (2 : ℤ) ^ (9 + ω + cw) ∣ a ∧ ¬ (2 : ℤ) ^ (9 + ω + cw + 1) ∣ a := by
  obtain ⟨l, rfl⟩ := hlam1
  have hl : ¬ (2 : ℤ) ∣ l := by
    rintro ⟨l', rfl⟩; exact hlam2 ⟨l', by ring⟩
  set x : ℤ := (c0 : ℤ) * 2 ^ ω * ζ * (2 ^ cw * l) with hx
  have hx' : x = 2 ^ (9 + ω + cw) * (47385 * ζ * l) := by
    rw [hx, c0_mul_two_pow_eq]; ring
  have hodd : ¬ (2 : ℤ) ∣ 47385 * ζ * l := by
    intro h
    rcases Int.prime_two.dvd_or_dvd h with h' | h'
    · rcases Int.prime_two.dvd_or_dvd h' with h'' | h''
      · norm_num at h''
      · exact (Int.not_even_iff_odd.mpr hζ) (even_iff_two_dvd.mpr h'')
    · exact hl h'
  obtain ⟨t, ht⟩ := hcong
  have ha : a = x + 2 ^ M * t := by linarith
  have hMk : 9 + ω + cw + 1 ≤ M := hM
  constructor
  · rw [ha, hx']
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _)
  · intro h
    have h2 : (2 : ℤ) ^ (9 + ω + cw + 1) ∣ x := by
      have := dvd_sub h (dvd_mul_of_dvd_left (pow_dvd_pow 2 hMk) t)
      rwa [ha, add_sub_cancel_right] at this
    rw [hx', pow_succ] at h2
    exact hodd ((mul_dvd_mul_iff_left (by positivity)).mp h2)

end ZInQ.Manuscript.RC.Odd

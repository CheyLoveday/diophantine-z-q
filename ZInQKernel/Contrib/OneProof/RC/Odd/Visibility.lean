import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Comparison
import ZInQKernel.Contrib.OneProof.RC.Odd.Detector

/-!
# Lane RC12-odd: visibility (O.8) (App F, `ex:app-visibility`, tex 9407–9445)

"There is one constant `C_det`, independent of the actual stage and admissible `D`, for which
(O.8) holds. Explicitly, for a known simple-zero `D`, `v₂ a_M(D) ≥ min{M, j_gen(D) − C_det}`. For
every admissible `D`, the strict inequality `v₂ a_M(D) < M` implies `ord_{s=1} L(E^D, s) = 1` and
`j_gen(D) ≤ v₂ a_M(D) + C_det`. If an admissible odd-sign `D` is not a simple zero, its coefficient
vanishes modulo `2^M`."

`visibility_O8` is **PROVED** from three hypotheses, each the manuscript's own input:
* `hO7` — the comparison (O.7)/(3.8) after phase removal (tex 9112–9113, 2081–2084): at every stage
  `θ` and admissible `D`, `a_θ(D) ≡ c₀ 2^{ω(N)} ζ λ_θ(D) (mod 2^{M_θ})` with `ζ` odd and
  `λ_θ(D)` an integer lift of `λ_{M_θ}(\overline{LP_D})`;
* `hnative` — the native-index lower bound (tex 9422–9428): for a known simple zero `D`,
  `P_D = m_D G + T`, `L` kills `T`, an integral Kummer map cannot decrease `v₂(m_D)`, and the rational
  line has index `≤ 2` in the native lattice; all absorbed in one constant `C`:
  `2^k ∣ λ_θ(D)` whenever `k ≤ min(M_θ, j_gen(D) − C)` (ELLIOT/GLUE);
* `htorsion` — the height formula (Cai–Shu–Tian Thm 1.1, PRINT, stated in the project as
  `CST.CSTThm11Split`; qualitative direction only) together with `L` killing torsion
  (tex 9439–9441): an admissible `D` that is not a simple zero has torsion genus point, so
  `λ_θ(D) ≡ 0 (mod 2^{M_θ})`.

The conclusion is the shape of the skeleton's Prop `RCSteps.visibility` (lane RC0), with
`SimpleZero D` to be instantiated by `ord_{s=1} L(E^{(D)}, s) = 1` and `vZ` the 2-adic valuation
`Padic.addValuation` on `ℤ ⊂ ℚ₂` (definitionally the skeleton's `vZ`).

**The fixed witness and (O.2)** (lane RC27). What the text asserts about `λ_M(\bar Q)`,
`Q = L P_{D_w}`, is (O.2)/(3.7): at every stage of the detecting sequence,
`v₂ λ_M(\bar Q) = c_w < M` with `c_w = a + 1` fixed before the precision varies (tex 8236–8239,
8396–8398, 2486–2493). The proof: `λ_M = b ∘ κ_M`, and "for the fixed witness, specialization of a
compatible division point identifies this evaluation with the cocycle value at `σ²`, whose `b`-value
is `2^{a+1}`" (tex 8457–8460), where `σ = hτ`, `ρ(h) = 1`, `c_Q(h) = 2^a t₀`, `b t₀ = 1`, `bC = b`
(tex 8343–8360). The hypotheses `hlam1`, `hlam2` of `witness_exact_order` / `witness_vZ` are (O.2)
read on an integer lift `λ` of `λ_M(\bar Q)` (with `c_w < M`, implied by `hM`); they are not supplied
by batch 3's `FixedWitness`, which gives only the nontorsion of the genus point and of a rational
point `Q` on `E^{(D_w)}` (the input of tex 8314–8330). Here:
* `WitnessDetector` — the detector data of tex 8308–8360 (abstract interface: the Kummer cocycle
  `c_Q` on a group with a representation `ρ`, `h ∈ ker ρ`, complex conjugation `τ`, the row `b`, `t₀`,
  `a`); non-vacuity `witnessDetector_example`;
* `WitnessDetector.row_sq` (**PROVED**, from `IsCocycle.sigma_sq`, `row_value`):
  `b c_Q(σ²) = 2^{c_w}`;
* `WitnessDetector.lambda_eq_two_pow` (**PROVED**): the specialization identity
  `λ_M(\bar Q) = b c_Q(σ²) mod 2^M` gives `λ_M(\bar Q) = 2^{c_w}` in `ℤ/2^M`;
* `exact_order_of_eq_two_pow`, `exact_order_of_residue` (**PROVED**): (O.2) on the residue gives
  `hlam1`, `hlam2` for every integer lift;
* `witness_vZ_of_detector`, `witness_vZ_of_O2` (**PROVED**): `v₂ a_M(D_w) = c_θ + c_w` from (O.7) and
  the detector data with the specialization identity (resp. from (O.2) on the residue).
The step from the nontorsion of `Q` (batch 3's `FixedWitness`) to the detector data — Serre's open
image theorem for `A = E^{(D_w)}` (PRINT, lane RC9's `SerreThm3`), the Kummer injection
`A(ℚ) ⊗ ℚ₂ ↪ H¹(ℚ, V₂A)` (GLUE), the central-scalar coboundary (PROVED,
`IsCocycle.coboundary_of_central`), `c_Q(h^d) = d c_Q(h)` (PROVED, `IsCocycle.pow_of_ker`), the row
`b` of the `+1`-eigenspace of `C` (GLUE, `C² = 1`, `det C = −1`) — and the specialization identity at
every stage (finite Chebotarev for `F₀(E[2^M], A[2^M], 2^{−M}Q)`, GLUE; good reduction identifying the
reduced division cocycle with `κ_M`, GLUE, tex 8392–8398) remain ELLIOT/GLUE/PRINT inputs.
-/

namespace ZInQ.Manuscript.RC.Odd

/-- The 2-adic valuation of an integer, in `WithTop ℤ` (`vZ 0 = ⊤`); the same definition as the
skeleton's `vZ`. -/
noncomputable def vZ (n : ℤ) : WithTop ℤ := Padic.addValuation ((n : ℚ) : ℚ_[2])

theorem vZ_of_ne_zero {n : ℤ} (hn : n ≠ 0) : vZ n = ((padicValInt 2 n : ℤ) : WithTop ℤ) := by
  have : ((n : ℚ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  rw [vZ, Padic.addValuation.apply this]
  congr 1
  have h := Padic.valuation_intCast (p := 2) n
  rw [← h]; norm_cast

/-- **PROVED.** `2^k ∣ n ↔ k ≤ v₂(n)`. -/
theorem two_pow_dvd_iff_le_vZ (n : ℤ) (k : ℕ) : (2 : ℤ) ^ k ∣ n ↔ ((k : ℤ) : WithTop ℤ) ≤ vZ n := by
  by_cases hn : n = 0
  · subst hn; simp [vZ]
  · rw [vZ_of_ne_zero hn, WithTop.coe_le_coe, Int.ofNat_le]
    have := padicValInt_dvd_iff (p := 2) k n
    simp only [hn, false_or] at this
    exact_mod_cast this

/-- **(O.8), PROVED from (O.7), the native-index bound and the height formula.** -/
theorem visibility_O8 (M : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ∀ θ D, admissible θ D → ∃ ζ : ℤ, Odd ζ ∧
      (2 : ℤ) ^ M θ ∣ aθ θ D - (c0 : ℤ) * 2 ^ ω * ζ * lam θ D)
    (hnative : ∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
      (2 : ℤ) ^ k ∣ lam θ D)
    (htorsion : ∀ θ D, admissible θ D → ¬ SimpleZero D → (2 : ℤ) ^ M θ ∣ lam θ D) :
    (∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
        ((k : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D)) ∧
    (∀ θ D, admissible θ D → ¬ SimpleZero D → ((M θ : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D)) ∧
    (∃ Cdet : ℤ, ∀ θ D, admissible θ D → vZ (aθ θ D) < ((M θ : ℤ) : WithTop ℤ) →
      SimpleZero D ∧ ((jgen D : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D) + (Cdet : WithTop ℤ)) := by
  -- the lower bound transfers from `λ` to `a` through (O.7)
  have transfer : ∀ θ D, admissible θ D → ∀ k : ℕ, k ≤ M θ → (2 : ℤ) ^ k ∣ lam θ D →
      (2 : ℤ) ^ k ∣ aθ θ D := by
    intro θ D hD k hk hl
    obtain ⟨ζ, -, hc⟩ := hO7 θ D hD
    have h1 : (2 : ℤ) ^ k ∣ aθ θ D - (c0 : ℤ) * 2 ^ ω * ζ * lam θ D :=
      dvd_trans (pow_dvd_pow 2 hk) hc
    have h2 : (2 : ℤ) ^ k ∣ (c0 : ℤ) * 2 ^ ω * ζ * lam θ D := dvd_mul_of_dvd_right hl _
    have := dvd_add h1 h2
    rwa [sub_add_cancel] at this
  refine ⟨?_, ?_, ⟨C, ?_⟩⟩
  · intro θ D hD hs k hk hj
    exact (two_pow_dvd_iff_le_vZ _ k).mp (transfer θ D hD k hk (hnative θ D hD hs k hk hj))
  · intro θ D hD hs
    exact (two_pow_dvd_iff_le_vZ _ _).mp (transfer θ D hD _ le_rfl (htorsion θ D hD hs))
  · intro θ D hD hlt
    have hsimple : SimpleZero D := by
      by_contra hs
      have := (two_pow_dvd_iff_le_vZ _ _).mp (transfer θ D hD _ le_rfl (htorsion θ D hD hs))
      exact absurd hlt (not_lt.mpr this)
    refine ⟨hsimple, ?_⟩
    have ha0 : aθ θ D ≠ 0 := by
      intro h0; rw [h0] at hlt; simp [vZ] at hlt
    rw [vZ_of_ne_zero ha0] at hlt ⊢
    set n := padicValInt 2 (aθ θ D)
    have hnM : n < M θ := by
      have : ((n : ℤ) : WithTop ℤ) < ((M θ : ℤ) : WithTop ℤ) := hlt
      exact_mod_cast WithTop.coe_lt_coe.mp this
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    by_contra hj
    rw [not_le] at hj
    have hk : ((n + 1 : ℕ) : ℤ) ≤ jgen D - C := by push_cast; linarith
    have hdiv := transfer θ D hD (n + 1) (by omega) (hnative θ D hD hsimple (n + 1) (by omega) hk)
    have := (two_pow_dvd_iff_le_vZ _ _).mp hdiv
    rw [vZ_of_ne_zero ha0, WithTop.coe_le_coe] at this
    push_cast at this
    omega

/-- **PROVED (tex 9391–9399, `v₂`-form).** At the fixed witness, `v₂ a_M(D_w) = c_θ + c_w`. The
hypotheses `hlam1`, `hlam2` are (O.2) (tex 8396–8398: `v₂ λ_M(\bar Q) = c_w < M`) read on an integer
lift `λ` of `λ_M(\bar Q)`; they are derived from the detector data in `witness_vZ_of_detector` and from
(O.2) on the residue in `witness_vZ_of_O2` (see the module docstring). -/
theorem witness_vZ (ω M cw : ℕ) {a ζ lam : ℤ} (hζ : Odd ζ)
    (hlam1 : (2 : ℤ) ^ cw ∣ lam) (hlam2 : ¬ (2 : ℤ) ^ (cw + 1) ∣ lam)
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + cw < M) :
    vZ a = (((9 + ω + cw : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨h1, h2⟩ := witness_exact_order ω M cw hζ hlam1 hlam2 hcong hM
  have ha0 : a ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have hle := (two_pow_dvd_iff_le_vZ a _).mp h1
  have hnle : ¬ ((((9 + ω + cw + 1 : ℕ)) : ℤ) : WithTop ℤ) ≤ vZ a :=
    fun h => h2 ((two_pow_dvd_iff_le_vZ a _).mpr h)
  rw [vZ_of_ne_zero ha0] at hle hnle ⊢
  rw [WithTop.coe_le_coe] at hle hnle
  have : padicValInt 2 a = 9 + ω + cw := by
    have h1' : ((9 + ω + cw : ℕ) : ℤ) ≤ (padicValInt 2 a : ℤ) := hle
    have h2' : ¬ ((9 + ω + cw + 1 : ℕ) : ℤ) ≤ (padicValInt 2 a : ℤ) := hnle
    omega
  rw [this]

/-! ### (O.2) at the fixed witness (tex 8225–8405, 2469–2493) -/

/-- **The detector data of the fixed witness** (App F, Proposition `ex:app-detector`, proof,
tex 8308–8360; §7, tex 2469–2482), abstract interface (DEPARTURE of form: the absolute Galois group,
the Tate module `T = T₂A` and the Kummer cocycle `c_Q` of `Q = L P_{D_w}` are not formalized; the
group `Gp`, the module `T` and the cocycle stand for them). Fields: the representation `ρ`
(`ρ_A`), the cocycle `c = c_Q` (`c(gh) = c(g) + ρ(g) c(h)`, tex 8308–8312), `h ∈ H = ker ρ`
(tex 8312, 8340–8350), complex conjugation `τ` (`τ² = 1`, tex 8343–8346), the primitive row
`b : T → ℤ₂` with `bC = b`, `C = ρ(τ)` (tex 8346–8348), `t₀` with `b t₀ = 1`, and `a` with
`c(h) = v = 2^a t₀` (tex 8349). The existence of such data for the genuine `c_Q` is the ELLIOT +
PRINT + GLUE step listed in the module docstring. Non-vacuity: `witnessDetector_example`. -/
structure WitnessDetector (Gp T : Type*) [Group Gp] [AddCommGroup T] where
  ρ : Gp →* AddMonoid.End T
  c : Gp → T
  cocycle : IsCocycle ρ c
  h : Gp
  τ : Gp
  ker_h : ρ h = 1
  invol : τ * τ = 1
  b : T →+ ℤ_[2]
  row_fixed : ∀ x, b (ρ τ x) = b x
  t₀ : T
  row_one : b t₀ = 1
  a : ℕ
  translation : c h = (2 ^ a) • t₀

namespace WitnessDetector

variable {Gp T : Type*} [Group Gp] [AddCommGroup T]

/-- `σ = hτ` (tex 8350). -/
def σ (X : WitnessDetector Gp T) : Gp := X.h * X.τ

/-- `c_w = a + 1` (tex 8358). -/
def cw (X : WitnessDetector Gp T) : ℕ := X.a + 1

/-- **PROVED (tex 8350–8358).** `c_Q(σ²) = (1 + C) v` and `b c_Q(σ²) = 2^{a+1} = 2^{c_w}`. -/
theorem row_sq (X : WitnessDetector Gp T) : X.b (X.c (X.σ * X.σ)) = 2 ^ X.cw := by
  obtain ⟨-, hsq⟩ := X.cocycle.sigma_sq X.ker_h X.invol
  rw [σ, hsq, X.translation, cw]
  exact row_value (X.ρ X.τ) X.b X.row_fixed X.t₀ X.row_one X.a

/-- **PROVED (tex 8457–8460, (O.2)).** If the stage value `λ_M(\bar Q) ∈ ℤ/2^M` is the reduction of
the row value of the cocycle at `σ²` (the specialization identity), then `λ_M(\bar Q) = 2^{c_w}`. -/
theorem lambda_eq_two_pow (X : WitnessDetector Gp T) {M : ℕ} {lamM : ZMod (2 ^ M)}
    (hspec : lamM = PadicInt.toZModPow M (X.b (X.c (X.σ * X.σ)))) : lamM = 2 ^ X.cw := by
  rw [hspec, X.row_sq, map_pow, map_ofNat]

end WitnessDetector

/-- **PROVED (non-vacuity of `WitnessDetector`).** On the free group `ℤ` (multiplicatively) acting
trivially on `T = ℤ₂` with the cocycle `n ↦ n`, `h = 1`, `τ = 0`, `b = id`, `t₀ = 1`, `a = 0`: all
fields hold (`c_w = 1`). -/
noncomputable def witnessDetector_example : WitnessDetector (Multiplicative ℤ) ℤ_[2] where
  ρ := 1
  c := fun g => ((Multiplicative.toAdd g : ℤ) : ℤ_[2])
  cocycle := fun g h => by simp
  h := Multiplicative.ofAdd 1
  τ := 1
  ker_h := rfl
  invol := mul_one 1
  b := AddMonoidHom.id ℤ_[2]
  row_fixed := fun x => by simp
  t₀ := 1
  row_one := rfl
  a := 0
  translation := by simp

/-- **PROVED.** An integer lift of `2^{c_w}` modulo `2^M`, `c_w < M`, has exact `2`-adic order `c_w`:
the hypotheses `hlam1`, `hlam2` of `witness_exact_order`. -/
theorem exact_order_of_eq_two_pow {M cw : ℕ} (hcw : cw < M) {lam : ℤ}
    (h : ((lam : ℤ) : ZMod (2 ^ M)) = 2 ^ cw) :
    (2 : ℤ) ^ cw ∣ lam ∧ ¬ (2 : ℤ) ^ (cw + 1) ∣ lam := by
  have h' : ((lam : ℤ) : ZMod (2 ^ M)) = (((2 : ℤ) ^ cw : ℤ) : ZMod (2 ^ M)) := by
    rw [h]; push_cast; rfl
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  push_cast at h'
  have hM1 : (2 : ℤ) ^ cw ∣ (2 : ℤ) ^ M := pow_dvd_pow 2 hcw.le
  have hM2 : (2 : ℤ) ^ (cw + 1) ∣ (2 : ℤ) ^ M := pow_dvd_pow 2 hcw
  constructor
  · have := dvd_sub (dvd_refl ((2 : ℤ) ^ cw)) (dvd_trans hM1 h')
    rwa [sub_sub_cancel] at this
  · intro hd
    have h2 : (2 : ℤ) ^ (cw + 1) ∣ (2 : ℤ) ^ cw := by
      have := dvd_add (dvd_trans hM2 h') hd
      rwa [sub_add_cancel] at this
    have h3 : (2 : ℤ) ^ (cw + 1) ≤ 2 ^ cw := Int.le_of_dvd (by positivity) h2
    have h4 : (2 : ℤ) ^ cw < 2 ^ (cw + 1) := pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self cw)
    omega

/-- **PROVED.** (O.2) on the residue: if `x = λ_M(\bar Q) ∈ ℤ/2^M` has exact `2`-adic order `c_w`
(`2^{c_w} ∣ x`, `2^{c_w+1} ∤ x`) with `c_w < M`, every integer lift `λ` of `x` satisfies `hlam1`,
`hlam2`. -/
theorem exact_order_of_residue {M cw : ℕ} (hcw : cw < M) {x : ZMod (2 ^ M)}
    (h1 : (2 : ZMod (2 ^ M)) ^ cw ∣ x) (h2 : ¬ (2 : ZMod (2 ^ M)) ^ (cw + 1) ∣ x) {lam : ℤ}
    (hlift : ((lam : ℤ) : ZMod (2 ^ M)) = x) :
    (2 : ℤ) ^ cw ∣ lam ∧ ¬ (2 : ℤ) ^ (cw + 1) ∣ lam := by
  refine ⟨?_, fun hd => h2 ?_⟩
  · obtain ⟨y, rfl⟩ := h1
    have : NeZero (2 ^ M) := ⟨by positivity⟩
    have hcast :
        ((lam : ℤ) : ZMod (2 ^ M)) = (((2 : ℤ) ^ cw * (y.val : ℤ) : ℤ) : ZMod (2 ^ M)) := by
      rw [hlift]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id', id]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
    push_cast at hcast
    have hM1 : (2 : ℤ) ^ cw ∣ (2 : ℤ) ^ M := pow_dvd_pow 2 hcw.le
    have := dvd_sub (dvd_mul_right ((2 : ℤ) ^ cw) (y.val : ℤ)) (dvd_trans hM1 hcast)
    rwa [sub_sub_cancel] at this
  · rw [← hlift]
    have := map_dvd (Int.castRingHom (ZMod (2 ^ M))) hd
    rwa [map_pow, map_ofNat, eq_intCast] at this

/-- **PROVED (non-vacuity of the residue form of (O.2)).** For `c_w < M`, the residue `2^{c_w}` in
`ℤ/2^M` has `2`-adic valuation exactly `c_w`. -/
theorem residue_exact_order_two_pow {M cw : ℕ} (hcw : cw < M) :
    (2 : ZMod (2 ^ M)) ^ cw ∣ (2 : ZMod (2 ^ M)) ^ cw ∧
      ¬ (2 : ZMod (2 ^ M)) ^ (cw + 1) ∣ (2 : ZMod (2 ^ M)) ^ cw := by
  refine ⟨dvd_refl _, ?_⟩
  rintro ⟨y, hy⟩
  have : NeZero (2 ^ M) := ⟨by positivity⟩
  have hcast : (((2 : ℤ) ^ cw : ℤ) : ZMod (2 ^ M)) =
      (((2 : ℤ) ^ (cw + 1) * (y.val : ℤ) : ℤ) : ZMod (2 ^ M)) := by
    push_cast; rw [ZMod.natCast_val, ZMod.cast_id', id]; exact hy
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  push_cast at hcast
  have hM2 : (2 : ℤ) ^ (cw + 1) ∣ (2 : ℤ) ^ M := pow_dvd_pow 2 hcw
  have h2 : (2 : ℤ) ^ (cw + 1) ∣ (2 : ℤ) ^ cw := by
    have := dvd_sub (dvd_mul_right ((2 : ℤ) ^ (cw + 1)) (y.val : ℤ)) (dvd_trans hM2 hcast)
    rwa [sub_sub_cancel] at this
  have h3 : (2 : ℤ) ^ (cw + 1) ≤ 2 ^ cw := Int.le_of_dvd (by positivity) h2
  have h4 : (2 : ℤ) ^ cw < 2 ^ (cw + 1) := pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self cw)
  omega

/-- **PROVED (tex 9391–9399 with (O.2) in its detector form, tex 8343–8360, 8457–8460).** From (O.7)
at the witness and the detector data with the specialization identity
`λ_M(\bar Q) = b c_Q(σ²) mod 2^M` (for the integer lift `λ`): `v₂ a_M(D_w) = c_θ + c_w`,
`c_θ = 9 + ω(N)`, `c_w = a + 1`, whenever `M > c_θ + c_w`. -/
theorem witness_vZ_of_detector {Gp T : Type*} [Group Gp] [AddCommGroup T]
    (X : WitnessDetector Gp T) (ω M : ℕ) {a ζ lam : ℤ} (hζ : Odd ζ)
    (hspec : ((lam : ℤ) : ZMod (2 ^ M)) = PadicInt.toZModPow M (X.b (X.c (X.σ * X.σ))))
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + X.cw < M) :
    vZ a = (((9 + ω + X.cw : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨h1, h2⟩ := exact_order_of_eq_two_pow (by omega) (X.lambda_eq_two_pow hspec)
  exact witness_vZ ω M X.cw hζ h1 h2 hcong hM

/-- **PROVED (tex 9391–9399 with (O.2) as printed, tex 8396–8398).** From (O.7) at the witness and
(O.2) on the residue `x = λ_M(\bar Q)` (`v₂ x = c_w`) with `λ` an integer lift of `x`:
`v₂ a_M(D_w) = c_θ + c_w` whenever `M > c_θ + c_w`. -/
theorem witness_vZ_of_O2 (ω M cw : ℕ) {a ζ lam : ℤ} {x : ZMod (2 ^ M)} (hζ : Odd ζ)
    (h1 : (2 : ZMod (2 ^ M)) ^ cw ∣ x) (h2 : ¬ (2 : ZMod (2 ^ M)) ^ (cw + 1) ∣ x)
    (hlift : ((lam : ℤ) : ZMod (2 ^ M)) = x)
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + cw < M) :
    vZ a = (((9 + ω + cw : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨h1', h2'⟩ := exact_order_of_residue (by omega) h1 h2 hlift
  exact witness_vZ ω M cw hζ h1' h2' hcong hM

end ZInQ.Manuscript.RC.Odd

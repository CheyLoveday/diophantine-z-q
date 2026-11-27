import ZInQKernel.Contrib.CloudB3RC53.TameQuotient.QuadraticCoordinates
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.GenuineIdentification
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison

/-!
# The tame model with trivial `𝔽₂` coefficients: the comparison chain maps (row 1)

Manuscript `diophantine_zq.tex`, the tame model (4.4), tex L3443–3448 and L3470–3479. For a
nonarchimedean local field `K` with odd residue characteristic and residue field of odd
cardinality `q`, and the trivial coefficient module `𝔽₂` (every action of a group on `ZMod 2` is
trivial, `smul_zmod_two`), the tame model `M --(Φ−1, 0)--> M² --(0, Φ−q)--> M` with `M = 𝔽₂`,
`Φ = 1` has zero differentials (`q` odd). This file builds the comparison chain maps to the
genuine continuous cochains (lane RC26's `contCochains`, extended by zero with `natCx`):

* `tameF2L hp hq : GHom (tL 𝔽₂ 1 q) (natCx C^•_cont(G_K, 𝔽₂))`: degree `0` constants; degree `1`
  `(a, b) ↦ a·χ_ur + b·χ_ϖ` (the unramified and ramified characters, `TameQuotient`); degree `2`
  `m ↦ m·(χ_ur ∪ χ_ϖ)`, `(g, h) ↦ m χ_ur(g) χ_ϖ(h)` (the cup product, a `2`-cocycle);
* `tameF2U : GHom (tU 𝔽₂ 1) (natCx C^•_cont(Gal(K^{ur}/K), 𝔽₂))`: constants and `a ↦ a·χ̄_ur`;
* `tameF2_comm`: the square with the inclusion `tιH` and inflation along restriction
  `G_K → Gal(K^{ur}/K)` commutes.

Here `χ_ϖ` is the ramified character of a fixed square root `sqrtUnif K` of a fixed uniformizer
`unif K`. All PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (tL tLX tLd tU tUX tUd tιH)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GHom GCx)

/-- **Every action of a group on `ZMod 2` by additive automorphisms is trivial.** -/
theorem smul_zmod_two {G : Type*} [Group G] [DistribMulAction G (ZMod 2)] (g : G) (m : ZMod 2) :
    g • m = m := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 m with rfl | rfl
  · exact smul_zero g
  · rcases h01 (g • (1 : ZMod 2)) with h | h
    · exact absurd h ((smul_eq_zero_iff_eq g).not.2 one_ne_zero)
    · exact h

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A fixed uniformizer of `K`. -/
def unif : Kˣ := (exists_isUniformizer (K := K)).choose

theorem unif_spec : normalizedValuation K (unif K) = .ofAdd 1 :=
  (isUniformizer_def _).1 (exists_isUniformizer (K := K)).choose_spec

/-- A fixed square root of the uniformizer in `K^{alg}`. -/
def sqrtUnif : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (unif K : K)) two_pos).choose

theorem sqrtUnif_sq : sqrtUnif K ^ 2 = algebraMap K (AlgebraicClosure K) (unif K : K) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (unif K : K)) two_pos).choose_spec

theorem sqrtUnif_ne_zero : sqrtUnif K ≠ 0 := by
  intro h
  have := sqrtUnif_sq K
  rw [h, zero_pow two_ne_zero] at this
  exact (unif K).ne_zero ((map_eq_zero _).1 this.symm)

variable {K}

theorem two_ne_zero_algClosure (hp : ringChar 𝓀[K] ≠ 2) : (2 : AlgebraicClosure K) ≠ 0 := by
  have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
    (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_coprime_ringChar h2c
  rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
  exact (map_ne_zero _).2 h2K

/-- The ramified character `χ_ϖ` of the fixed square root of the uniformizer. -/
abbrev ramF2 : Gal(AlgebraicClosure K/K) → ZMod 2 := ramChar (sqrtUnif K)

theorem ramF2_mul (hp : ringChar 𝓀[K] ≠ 2) (g h : Gal(AlgebraicClosure K/K)) :
    ramF2 (g * h) = ramF2 g + ramF2 h :=
  ramChar_mul (sqrtUnif_sq K) (sqrtUnif_ne_zero K) (two_ne_zero_algClosure hp) g h

theorem continuous_ramF2 (hp : ringChar 𝓀[K] ≠ 2) : Continuous (ramF2 (K := K)) :=
  continuous_ramChar (sqrtUnif_sq K) (sqrtUnif_ne_zero K) (two_ne_zero_algClosure hp)

/-- The degree-`1` cochain `a·χ_ur + b·χ_ϖ`. -/
def c1 (a b : ZMod 2) (g : Gal(AlgebraicClosure K/K)) : ZMod 2 := a * urChar K g + b * ramF2 g

theorem continuous_c1 (hp : ringChar 𝓀[K] ≠ 2) (a b : ZMod 2) : Continuous (c1 (K := K) a b) :=
  (continuous_of_discreteTopology (f := fun x : ZMod 2 × ZMod 2 => a * x.1 + b * x.2)).comp
    (continuous_urChar.prodMk (continuous_ramF2 hp))

theorem c1_mul (hp : ringChar 𝓀[K] ≠ 2) (a b : ZMod 2) (g h : Gal(AlgebraicClosure K/K)) :
    c1 a b (g * h) = c1 a b g + c1 a b h := by
  simp only [c1]
  rw [urChar_mul, ramF2_mul hp]
  ring

/-- The degree-`2` cochain `m·(χ_ur ∪ χ_ϖ)`. -/
def c2 (m : ZMod 2) (p : Gal(AlgebraicClosure K/K) × Gal(AlgebraicClosure K/K)) : ZMod 2 :=
  m * (urChar K p.1 * ramF2 p.2)

theorem continuous_c2 (hp : ringChar 𝓀[K] ≠ 2) (m : ZMod 2) : Continuous (c2 (K := K) m) :=
  (continuous_of_discreteTopology (f := fun x : ZMod 2 × ZMod 2 => m * (x.1 * x.2))).comp
    ((continuous_urChar.comp continuous_fst).prodMk ((continuous_ramF2 hp).comp continuous_snd))

theorem fin1_eq'' {G : Type*} (v : Fin 1 → G) : v = fun _ => v 0 := by
  funext i
  rw [Subsingleton.elim i 0]

theorem fin2_eq' {G : Type*} (v : Fin 2 → G) : v = ![v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

theorem fin3_eq' {G : Type*} (v : Fin 3 → G) : v = ![v 0, v 1, v 2] := by
  funext i
  fin_cases i <;> rfl

/-! ### The full local comparison -/

section Full

variable [DistribMulAction (Gal(AlgebraicClosure K/K)) (ZMod 2)]
  [SMulCommClass (Gal(AlgebraicClosure K/K)) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (Gal(AlgebraicClosure K/K)) (ZMod 2)]

variable {q : ℕ} {hp : ringChar 𝓀[K] ≠ 2}

/-- Degree `0`: constants. -/
def lin0 : ZMod 2 →ₗ[ZMod 2] (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).X 0 where
  toFun m := mkCochain0 (k := ZMod 2) (G := Gal(AlgebraicClosure K/K)) m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree `1`: `(a, b) ↦ a·χ_ur + b·χ_ϖ`. -/
def lin1 (hp : ringChar 𝓀[K] ≠ 2) : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).X 1 where
  toFun x := mkCochain1 (k := ZMod 2) (c1 x.1 x.2) (continuous_c1 hp _ _)
  map_add' x y := contCochains_ext fun v => by
    change c1 (x.1 + y.1) (x.2 + y.2) (v 0) = c1 x.1 x.2 (v 0) + c1 y.1 y.2 (v 0)
    simp only [c1]; ring
  map_smul' r x := contCochains_ext fun v => by
    change c1 (r * x.1) (r * x.2) (v 0) = r • c1 x.1 x.2 (v 0)
    simp only [c1, smul_eq_mul]; ring

/-- Degree `2`: `m ↦ m·(χ_ur ∪ χ_ϖ)`. -/
def lin2 (hp : ringChar 𝓀[K] ≠ 2) : ZMod 2 →ₗ[ZMod 2] (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).X 2 where
  toFun m := mkCochain2 (k := ZMod 2) (c2 m) (continuous_c2 hp m)
  map_add' x y := contCochains_ext fun v => by
    change c2 (x + y) (v 0, v 1) = c2 x (v 0, v 1) + c2 y (v 0, v 1)
    simp only [c2]; ring
  map_smul' r x := contCochains_ext fun v => by
    change c2 (r * x) (v 0, v 1) = r • c2 x (v 0, v 1)
    simp only [c2, smul_eq_mul]; ring

/-- The components of `tameF2L`. -/
def compL (hp : ringChar 𝓀[K] ≠ 2) :
    (i : ℤ) → (tL (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) q).X i →ₗ[ZMod 2]
      (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2))).X i
  | 0 => lin0
  | 1 => lin1 hp
  | 2 => lin2 hp
  | _ => 0

theorem commL0 (m : ZMod 2) :
    lin1 (K := K) hp (m - m, 0) = ((contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).d 0 1).hom (lin0 m) := by
  refine contCochains_ext fun v => ?_
  rw [fin1_eq'' v, contFun_d01, smul_zmod_two]
  change c1 (m - m) 0 (v 0) = m - m
  simp [c1]

theorem commL1 (hq : Odd q) (a b : ZMod 2) :
    lin2 (K := K) hp (b - ((q : ℕ) : ZMod 2) • b) = ((contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).d 1 2).hom (lin1 hp (a, b)) := by
  have hq2 : ((q : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_iff]
    obtain ⟨r, hr⟩ := hq
    exact ⟨r, by simp [hr, ZMod.val_one]; ring⟩
  refine contCochains_ext fun v => ?_
  rw [fin2_eq' v, contFun_d12, smul_zmod_two]
  change c2 _ (v 0, v 1) = c1 a b (v 1) - c1 a b (v 0 * v 1) + c1 a b (v 0)
  rw [c1_mul hp, hq2]
  simp only [c2, one_smul, sub_self, zero_mul]
  abel

theorem commL2 (m : ZMod 2) : ((contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2)).d 2 3).hom (lin2 (K := K) hp m) = 0 := by
  refine contCochains_ext fun v => ?_
  rw [fin3_eq' v, contFun_d23, smul_zmod_two]
  change c2 m (v 1, v 2) - c2 m (v 0 * v 1, v 2) + c2 m (v 0, v 1 * v 2) - c2 m (v 0, v 1) = 0
  simp only [c2, urChar_mul, ramF2_mul hp]
  ring

theorem compL_comm (hp : ringChar 𝓀[K] ≠ 2) (hq : Odd q) (i : ℤ)
    (x : (tL (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) q).X i) :
    compL (q := q) hp (i + 1)
        ((tL (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) q).d i (i + 1) rfl x) =
      (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2))).d i (i + 1) rfl (compL hp i x) := by
  match i with
  | 0 => exact commL0 (hp := hp) (show ZMod 2 from x)
  | 1 => exact commL1 (hp := hp) hq (show ZMod 2 × ZMod 2 from x).1 (show ZMod 2 × ZMod 2 from x).2
  | 2 => exact (commL2 (hp := hp) (show ZMod 2 from x)).symm
  | Int.ofNat (n + 3) => exact (map_zero _).symm
  | Int.negSucc n =>
    change compL hp (Int.negSucc n + 1) 0 = (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2))).d _ _ rfl 0
    exact (map_zero _).trans (map_zero _).symm

/-- **The comparison of the tame model with the genuine local cochains** (trivial `𝔽₂`). -/
def tameF2L (hp : ringChar 𝓀[K] ≠ 2) (hq : Odd q) :
    GHom (tL (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) q) (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2))) where
  f i j h := by subst h; exact compL hp i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact compL_comm hp hq i x

end Full

/-! ### The unramified comparison and the square -/

section Unr


variable (K) in
/-- The unramified character of `Gal(K^{ur}/K)`: parity of the `ℤ̂`-coordinate. -/
def urBar (h : Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) : ZMod 2 :=
  Multiplicative.toAdd ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2)) :
    zHat →ₜ* Multiplicative (ZMod 2)) (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K) h))

theorem urChar_eq_urBar (g : Gal(AlgebraicClosure K/K)) :
    urChar K g = urBar K (restrictMaximalUnramifiedHom K g) := rfl

theorem urBar_mul (g h : Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) : urBar K (g * h) = urBar K g + urBar K h := by
  simp only [urBar]
  rw [map_mul, map_mul, toAdd_mul]

theorem continuous_urBar : Continuous (urBar K) :=
  (continuous_of_discreteTopology (f := (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2))).comp
    ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2))).continuous.comp
      (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).continuous)

variable [DistribMulAction Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)] [SMulCommClass Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2) (ZMod 2)]
  [ContinuousSMul Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)]

/-- Degree `0` of the unramified comparison: constants. -/
def lin0U : ZMod 2 →ₗ[ZMod 2] (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)).X 0 where
  toFun m := mkCochain0 (k := ZMod 2) (G := Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree `1` of the unramified comparison: `a ↦ a·χ̄_ur`. -/
def lin1U : ZMod 2 →ₗ[ZMod 2] (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)).X 1 where
  toFun a := mkCochain1 (k := ZMod 2) (fun h => a * urBar K h)
    ((continuous_of_discreteTopology (f := fun x : ZMod 2 => a * x)).comp continuous_urBar)
  map_add' x y := contCochains_ext fun v => by
    change (x + y) * urBar K (v 0) = x * urBar K (v 0) + y * urBar K (v 0)
    ring
  map_smul' r x := contCochains_ext fun v => by
    change (r * x) * urBar K (v 0) = r • (x * urBar K (v 0))
    rw [smul_eq_mul]; ring

/-- The components of `tameF2U`. -/
def compU :
    (i : ℤ) → (tU (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)).X i →ₗ[ZMod 2]
      (natCx (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2))).X i
  | 0 => lin0U
  | 1 => lin1U
  | _ => 0

theorem commU0 (m : ZMod 2) :
    lin1U (K := K) (m - m) = ((contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)).d 0 1).hom (lin0U m) := by
  refine contCochains_ext fun v => ?_
  rw [fin1_eq'' v, contFun_d01, smul_zmod_two]
  change (m - m) * urBar K (v 0) = m - m
  simp

theorem commU1 (a : ZMod 2) :
    ((contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2)).d 1 2).hom (lin1U (K := K) a) = 0 := by
  refine contCochains_ext fun v => ?_
  rw [fin2_eq' v, contFun_d12, smul_zmod_two]
  change a * urBar K (v 1) - a * urBar K (v 0 * v 1) + a * urBar K (v 0) = 0
  rw [urBar_mul]
  ring

theorem compU_comm (i : ℤ)
    (x : (tU (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)).X i) :
    compU (K := K) (i + 1) ((tU (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)).d i (i + 1) rfl x) =
      (natCx (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2))).d i (i + 1) rfl (compU i x) := by
  match i with
  | 0 => exact commU0 (show ZMod 2 from x)
  | 1 => exact (commU1 (show ZMod 2 from x)).symm
  | 2 => exact (map_zero _).symm
  | Int.ofNat (n + 3) => exact (map_zero _).symm
  | Int.negSucc n =>
    change compU (Int.negSucc n + 1) 0 = (natCx (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2))).d _ _ rfl 0
    exact (map_zero _).trans (map_zero _).symm

/-- **The comparison of the unramified two-term model with the unramified cochains.** -/
def tameF2U :
    GHom (tU (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))
      (natCx (contCochains (ZMod 2) Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K) (ZMod 2))) where
  f i j h := by subst h; exact compU i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact compU_comm i x

end Unr

section Square

variable [DistribMulAction (Gal(AlgebraicClosure K/K)) (ZMod 2)]
  [SMulCommClass (Gal(AlgebraicClosure K/K)) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (Gal(AlgebraicClosure K/K)) (ZMod 2)]
  [DistribMulAction (Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) (ZMod 2)]
  [SMulCommClass (Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) (ZMod 2)]

/-- Inflation along a restriction map `π : G_K → Gal(K^{ur}/K)` (trivial coefficients). -/
def inflF2 (π : Gal(AlgebraicClosure K/K) →ₜ* Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) :
    contCochains (ZMod 2) (Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K)) (ZMod 2) ⟶
      contCochains (ZMod 2) (Gal(AlgebraicClosure K/K)) (ZMod 2) :=
  contCochainsMap π LinearMap.id continuous_id (fun g m => by
    rw [LinearMap.id_apply, LinearMap.id_apply, smul_zmod_two, smul_zmod_two])

/-- **The comparison square commutes** with the inclusion of the unramified model and inflation. -/
theorem tameF2_comm (hp : ringChar 𝓀[K] ≠ 2) {q : ℕ} (hq : Odd q)
    (π : Gal(AlgebraicClosure K/K) →ₜ* Gal(maximalUnramifiedExtension K (AlgebraicClosure K)/K))
    (hπ : ∀ g, π g = restrictMaximalUnramifiedHom K g) :
    SelmerDuality.GHom.toCC (tιH (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) q) ≫
        SelmerDuality.GHom.toCC (tameF2L hp hq) =
      SelmerDuality.GHom.toCC (tameF2U (K := K)) ≫ SelmerDuality.GHom.toCC (natHom (inflF2 π)) := by
  ext n x
  rcases n with (_ | _ | n) | n
  · refine contCochains_ext fun v => ?_
    rfl
  · refine contCochains_ext fun v => ?_
    change c1 (show ZMod 2 from x) 0 (v 0) = (show ZMod 2 from x) * urBar K (π (v 0))
    simp [c1, hπ, urChar_eq_urBar]
  · change compL hp (Int.ofNat (n + 2)) 0 = natF (inflF2 π) (Int.ofNat (n + 2)) (compU _ x)
    rcases n with _ | n
    · exact (map_zero _).trans (by
        rw [show compU (K := K) (Int.ofNat 2) x = 0 from rfl]; exact (map_zero _).symm)
    · exact (map_zero _).trans (by
        rw [show compU (K := K) (Int.ofNat (n + 3)) x = 0 from rfl]; exact (map_zero _).symm)
  · change compL hp (Int.negSucc n) 0 = natF (inflF2 π) (Int.negSucc n) (compU _ x)
    exact (map_zero _).trans (map_zero _).symm

end Square

end ZInQ.Contrib.CloudB3RC53.TameModel

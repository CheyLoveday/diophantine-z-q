import ZInQKernel.HDecomp.ModCurves.Leaves
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # javanpeykar-dict: the Belyi property under a constant field extension (algebra) -/

noncomputable section

namespace JavanpeykarDict

open Polynomial

section Unram

variable {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
  [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL]

theorem mem_nonunits_comap {w : ValuationSubring FL} {f : F →+* FL} {x : F} :
    x ∈ (w.comap f).nonunits ↔ f x ∈ w.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem mul_mem_nonunits {w : ValuationSubring FL} {x y : FL} (hx : x ∈ w.nonunits) (hy : y ∈ w) :
    x * y ∈ w.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hx

theorem aeval_mem {w : ValuationSubring FL} (hw : ∀ c : L, algebraMap L FL c ∈ w) {z : FL}
    (hz : z ∈ w) (r : L[X]) : aeval z r ∈ w := by
  induction r using Polynomial.induction_on with
  | C a => simpa using hw a
  | add p q hp hq => simpa using add_mem hp hq
  | monomial n a _ =>
    simpa [pow_succ] using mul_mem (mul_mem (hw a) (pow_mem hz n)) hz

/-- **The Belyi ramification condition survives a constant field extension (glue, proved).** Given
the `e = 1` property of the places of `F_L / F` over every place of `F/K` with a principal maximal
ideal (`hS`), a `K`-rational Belyi function `t` of `F` (`hB`, the second clause of `IsBelyiFunction`)
gives the same clause for `ι t` over `L`, `L` algebraically closed and algebraic over `K`. -/
theorem belyi_unram (ι : F →ₐ[K] FL) [IsAlgClosed L] [Algebra.IsAlgebraic K L] (t : F)
    (hB : ∀ w : ValuationSubring F, (∀ c : K, algebraMap K F c ∈ w) → t ∈ w →
      ∀ q : Polynomial K, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
        Polynomial.aeval t q ∈ w.nonunits →
        ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval t q * y)
    (hS : ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y) :
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ι t ∈ w →
      ∀ q : Polynomial L, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
        Polynomial.aeval (ι t) q ∈ w.nonunits →
        ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval (ι t) q * y := by
  intro w hw ht q hqm hqi hqX hqX1 hq x hx
  -- `q = X - C a`
  have hdeg : q.natDegree = 1 :=
    natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible L hqi)
  set a : L := -q.coeff 0 with ha_def
  have hqa : q = X - C a := by
    rw [hqm.eq_X_add_C hdeg, ha_def, map_neg, sub_neg_eq_add]
  have ha0 : a ≠ 0 := by
    rintro h; apply hqX; rw [hqa, h, map_zero, sub_zero]
  have ha1 : a ≠ 1 := by
    rintro h; apply hqX1; rw [hqa, h, map_one]
  -- the minimal polynomial of `a` over `K`
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set p := minpoly K a with hp_def
  have hpm : p.Monic := minpoly.monic hint
  have hpi : Irreducible p := minpoly.irreducible hint
  have hpX : p ≠ X := by
    intro h; apply ha0
    have := minpoly.aeval K a
    rw [← hp_def, h, aeval_X] at this
    exact this
  have hpX1 : p ≠ X - 1 := by
    intro h; apply ha1
    have := minpoly.aeval K a
    rw [← hp_def, h, map_sub, aeval_X, map_one, sub_eq_zero] at this
    exact this
  -- `p = (X - a) r` over `L`
  set r := (p.map (algebraMap K L)) /ₘ (X - C a) with hr_def
  have hroot : (p.map (algebraMap K L)).IsRoot a := by
    rw [IsRoot.def, eval_map, ← aeval_def]
    exact minpoly.aeval K a
  have hfac : (X - C a) * r = p.map (algebraMap K L) := mul_divByMonic_eq_iff_isRoot.mpr hroot
  set u := aeval (ι t) r with hu_def
  have hu : u ∈ w := aeval_mem hw ht r
  have hkey : ι (aeval t p) = (ι t - algebraMap L FL a) * u := by
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_map_algebraMap L, ← hfac, map_mul,
      map_sub, aeval_X, aeval_C]
  have hqt : aeval (ι t) q = ι t - algebraMap L FL a := by
    rw [hqa, map_sub, aeval_X, aeval_C]
  rw [hqt] at hq ⊢
  -- `p(t)` is a nonunit at `w₀ = w ∩ F`, so a uniformizer there
  have hpt : aeval t p ∈ (w.comap (ι : F →+* FL)).nonunits := by
    rw [mem_nonunits_comap]
    change ι (aeval t p) ∈ w.nonunits
    rw [hkey]
    exact mul_mem_nonunits hq hu
  have hconst : ∀ c : K, algebraMap K F c ∈ w.comap (ι : F →+* FL) := by
    intro c
    rw [ValuationSubring.mem_comap]
    change ι (algebraMap K F c) ∈ w
    rw [ι.commutes, IsScalarTower.algebraMap_apply K L FL]
    exact hw _
  have ht0 : t ∈ w.comap (ι : F →+* FL) := ValuationSubring.mem_comap.mpr ht
  have hgen := hB (w.comap (ι : F →+* FL)) hconst ht0 p hpm hpi hpX hpX1 hpt
  obtain ⟨y, hy, rfl⟩ := hS w hw (aeval t p) hpt hgen x hx
  refine ⟨u * y, mul_mem hu hy, ?_⟩
  rw [hkey, mul_assoc]

end Unram

end JavanpeykarDict

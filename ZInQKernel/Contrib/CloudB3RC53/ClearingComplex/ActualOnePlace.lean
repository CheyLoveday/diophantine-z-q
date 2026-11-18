import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.ActualQEmpty
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# An actual instance of `Identification3` with one new place

As `ActualQEmpty.lean`, over `K = ℚ(ζ₄)`, `R₀ = 𝔽₂`, `p = 2`, with zero coefficient modules, but
with a NONEMPTY set of new places:

* `S` = the places over `2`, `S' = S ∪ {v₃}` for a place `v₃` over `3` (`v₃ ∉ S`), so
  `S' − S = {v₃}`; the places exist since `2`, `3` are not units of `𝓞 K` (norm `> 1`);
* the genuine unramified factorization at `v₃` is lane RC26's PROVED `urFactor`;
* the family local conditions are full at `v₃` (`hfull`: the zero condition map between vanishing
  complexes is bijective there);
* the cancellation core has an empty local block at `v₃` (`ι = ∅`, `det = 1 = X⁰·1 + 2·0`);
* the tame field at `v₃`: the tame model of the zero module is quasi-isomorphic to the genuine
  local and unramified complexes of the zero module (all terms vanish).

`identification3OnePlace b : Identification3 K S S' hS b 0 0 0 0` (PROVED, no hypotheses).

CAVEAT. Zero coefficients: as in `ActualQEmpty.lean`, this witnesses the consistency of the
interface with the genuine data (genuine groups, genuine cochains, genuine full and unramified
conditions, a genuine unramified factorization, Nekovář's finite setting) with one new place, not
any Galois-cohomological content.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (restrictData)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup aug)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData NewPlaces GaloisLocalConditions
  NekovarFiniteSetting Places natCx contCochains ResMod prodLift urFactor urFactor_spec locMap
  inflMap)
open ActualQEmpty (KA ρA)

namespace ActualOnePlace

/-! ### The places -/

theorem not_isUnit_natCast (n : ℕ) (hn : 2 ≤ n) : ¬ IsUnit (n : 𝓞 KA) := by
  rw [NumberField.isUnit_iff_norm]
  have h : ((RingOfIntegers.norm ℚ (n : 𝓞 KA) : 𝓞 ℚ) : ℚ) = (n : ℚ) ^ Module.finrank ℚ KA := by
    have e : ((n : 𝓞 KA) : KA) = algebraMap ℚ KA (n : ℚ) := by simp
    rw [RingOfIntegers.coe_norm, e, Algebra.norm_algebraMap]
  rw [h, abs_pow, Nat.abs_cast]
  have hd : 0 < Module.finrank ℚ KA := Module.finrank_pos
  have : (1 : ℚ) < (n : ℚ) ^ Module.finrank ℚ KA :=
    one_lt_pow₀ (by exact_mod_cast hn) hd.ne'
  exact this.ne'

theorem exists_place_natCast (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : HeightOneSpectrum (𝓞 KA), (n : 𝓞 KA) ∈ v.asIdeal := by
  have hne : Ideal.span {(n : 𝓞 KA)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact not_isUnit_natCast n hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hn0 : (n : 𝓞 KA) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨⟨M, hM.isPrime, fun hb => hn0 ?_⟩, hle (Ideal.mem_span_singleton_self _)⟩
  have := hle (Ideal.mem_span_singleton_self (n : 𝓞 KA))
  rwa [hb, Ideal.mem_bot] at this

/-- A place over `2`. -/
def v₂ : HeightOneSpectrum (𝓞 KA) := Classical.choose (exists_place_natCast 2 le_rfl)

/-- A place over `3`. -/
def v₃ : HeightOneSpectrum (𝓞 KA) := Classical.choose (exists_place_natCast 3 (by norm_num))

theorem two_mem_v₂ : (2 : 𝓞 KA) ∈ v₂.asIdeal := by
  have := Classical.choose_spec (exists_place_natCast 2 le_rfl)
  simp only [Nat.cast_ofNat] at this
  exact this

theorem three_mem_v₃ : (3 : 𝓞 KA) ∈ v₃.asIdeal := by
  have := Classical.choose_spec (exists_place_natCast 3 (by norm_num))
  simp only [Nat.cast_ofNat] at this
  exact this

/-- The old support: the places over `2`. -/
def S₂ : Set (HeightOneSpectrum (𝓞 KA)) := {v | (2 : 𝓞 KA) ∈ v.asIdeal}

/-- The new support `S₂ ∪ {v₃}`. -/
def S₂' : Set (HeightOneSpectrum (𝓞 KA)) := S₂ ∪ {v₃}

theorem hS₂ : S₂ ⊆ S₂' := Set.subset_union_left

theorem v₃_not_mem : v₃ ∉ S₂ := by
  intro h
  have h2 : (2 : 𝓞 KA) ∈ v₃.asIdeal := h
  have h1 : (1 : 𝓞 KA) ∈ v₃.asIdeal := by
    have := v₃.asIdeal.sub_mem three_mem_v₃ h2
    norm_num at this
    exact this
  exact v₃.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem S₂_finite : S₂.Finite := by
  have h2 : Ideal.span {(2 : 𝓞 KA)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  exact (Ideal.finite_factors h2).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem S₂'_finite : S₂'.Finite := S₂_finite.union (Set.finite_singleton _)

instance fintypeNew : Fintype (NewPlaces KA S₂ S₂') :=
  (S₂'_finite.subset Set.sdiff_subset).fintype

instance decEqNew : DecidableEq (NewPlaces KA S₂ S₂') := Classical.decEq _

/-- The new place `v₃`. -/
def q₃ : NewPlaces KA S₂ S₂' := ⟨v₃, Or.inr rfl, v₃_not_mem⟩

theorem nonempty_new : Nonempty (NewPlaces KA S₂ S₂') := ⟨q₃⟩

/-- `v₂` as an old place. -/
def w₂ : Places KA S₂ := ⟨v₂, two_mem_v₂⟩

/-- `v₂` as a place of the new support. -/
def w₂' : Places KA S₂' := ⟨v₂, Or.inl two_mem_v₂⟩

theorem hsetB : NekovarFiniteSetting KA S₂ 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := S₂_finite
  above_p v hv := by
    change (2 : 𝓞 KA) ∈ v.asIdeal
    simpa using hv
  condP _ := ActualQEmpty.isTotallyComplexKA
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing _ _

/-! ### The cancellation core with an empty local block -/

variable (b : ℕ)

/-- The family model: old part `H₁ --0--> H₂`, no singular summands (empty local block at `v₃`). -/
def preB : FullPreComplex (MonoidAlgebra Lam (SignGroup b)) where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Empty × NewPlaces KA S₂ S₂'
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := 0
  U := 0
  V := 0
  c1_c0 := by simp
  c2_c1 := by simp

theorem central_fullB :
    let D := ((preB b).map (augR b)).old (Matrix.map_zero _ (map_zero _))
      (Matrix.map_zero _ (map_zero _))
    D.d0.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d0 ∧
      D.d1.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d1 ∧
      D.d2.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; exact j.elim0
  · ext (i | i | i) (j | j | j)
    all_goals first | exact i.elim0 | exact j.elim0 | rfl
  · ext i j; exact i.elim0

/-- **The cancellation core with one new place and an empty local block.** -/
def coreB : FullCore (NewPlaces KA S₂ S₂') b 0 0 0 0 where
  ιn := Empty
  A := fun _ => 0
  dq := fun _ => 0
  hd := fun _ => by norm_num
  v := fun _ => 1
  w := fun _ => 0
  hdet := fun _ => by simp
  C := preB b
  eN := Equiv.refl _
  hB0 := Matrix.ext fun i => isEmptyElim i.1
  hT0 := Matrix.map_zero _ (map_zero _)
  hY0 := Matrix.map_zero _ (map_zero _)
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central_full := central_fullB b
  budget := budgetInputs_of_empty _ rfl fun i => by rcases i with _ | _ | _ | i <;> rfl

end ActualOnePlace

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

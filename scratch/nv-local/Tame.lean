import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal

set_option linter.style.haveILetI false

open Polynomial CategoryTheory AlgebraicGeometry IsLocalRing
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

noncomputable section

namespace SGRDirect.NVLocal

/-- **The ramification index is unchanged by localizing the base at a submonoid** missing the prime
(Mathlib's `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`, for any submonoid). -/
theorem ramificationIdx_map_localization {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ] [Algebra R S] [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Rₘ Sₘ] (M : Submonoid R)
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    (P : Ideal S) [P.IsPrime] (hP : Disjoint (M : Set R) (P.under R)) :
    (P.map (algebraMap S Sₘ)).ramificationIdx Rₘ = P.ramificationIdx R := by
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid S M : Submonoid S) : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxP
    exact Set.disjoint_left.mp hP hx hxP
  haveI hPm : (P.map (algebraMap S Sₘ)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ Sₘ P inferInstance hdisj
  have hcomap : (P.map (algebraMap S Sₘ)).comap (algebraMap S Sₘ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ Sₘ inferInstance hdisj
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₘ))
  let R₂ := Localization.AtPrime P
  haveI : (P.map (algebraMap S Sₘ)).LiesOver P := ⟨hcomap.symm⟩
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₘ))
  haveI : IsLocalization.AtPrime R₁ P := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S M) R₁ (P.map (algebraMap S Sₘ))
    exact hcomap.symm
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  have hunder : (P.map (algebraMap S Sₘ)).under Rₘ = (P.under R).map (algebraMap R Rₘ) := by
    rw [← IsLocalization.map_under M Rₘ ((P.map (algebraMap S Sₘ)).under Rₘ)]
    congr 1
    have hc : Ideal.under S (P.map (algebraMap S Sₘ)) = P := hcomap
    rw [Ideal.under_under, ← Ideal.under_under (B := S), hc]
  have hcomp : (algebraMap R₂ R₁).comp (algebraMap R R₂) = (algebraMap Rₘ R₁).comp (algebraMap R Rₘ) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have key : (P.under R).map (algebraMap R R₂) =
      (((P.map (algebraMap S Sₘ)).under Rₘ).map (algebraMap Rₘ R₁)).comap (algebraMap R₂ R₁) := by
    rw [hunder, Ideal.map_map, ← hcomp, ← Ideal.map_map, Ideal.comap_map_of_bijective _ h]
  rw [Module.length_quotient, Module.length_quotient, key, Ideal.coheight_comap_of_surjective _ h.2]


/-- **GLUE (local algebra of tame covers; the geometric half of h-b1 §3 step 3 in general form).**
Let `R` be a noetherian domain with fraction field `K`, `m` a maximal ideal with `R_m` regular local of
dimension `2` and `m = (f, g)`, `(f)` prime, and residue characteristic `p` (`p ∈ m`). Let `L/K` be finite
Galois of degree `< p` (so all ramification near `m` is tame), with integral closure `S` of `R`, unramified
(`e = 1`) at every height-one prime `P ⊆ m` not containing `f` or `g` (the branch locus near `m` lies in the
normal-crossings divisor `fg = 0`). Then at every maximal ideal `𝔓` of `S` over `m`, the branch of `f = 0` is
unique and normal: all primes of `S` over `(f)` contained in `𝔓` coincide, and for such a prime `Q` the
localization of `S/Q` at `𝔓` is integrally closed (every element of a fraction field of `S/Q` integral over
`S/Q` is a quotient `a/s` with `s ∉ 𝔓`).
*Proof route* (not compiled): Abhyankar's lemma (SGA 1 XIII 5.2–5.3, UNVERIFIED numbers): after the Kummer base
change `R_m[ζ_N][T, U]/(T^N − f, U^N − g)` (`N = [L : K]`, invertible; a regular local ring of dimension `2`
after localizing), the normalization of `L` is unramified in codimension one (Abhyankar's lemma for DVRs, the
kernel's T2, at `(T)` and `(U)`; base change at the other height-one primes), hence étale by purity (the
chain's `PropTSGlue.purityGlobalDim2`, proved); its specialization along `T = 0` is étale over a DVR, hence
normal, so each closed point carries a unique normal branch; going down and the Reynolds operator of the tame
group `Gal(L(ζ_N, T, U)/L)` (with CRT, the branches upstairs being comaximal at `𝔓`) descend both to `S`
(docs/research/nv-local.md §2.3). -/
def TameBranchNormal : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L] (m : Ideal R) [m.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime m) → ringKrullDim (Localization.AtPrime m) = 2 →
    ∀ f g : R, m = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : R) ∈ m → Module.finrank K L < p →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≤ m → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure R L), P'.IsPrime → P'.under R = P →
        P'.ramificationIdx R = 1) →
    ∀ 𝔓 : Ideal (integralClosure R L), 𝔓.IsMaximal → 𝔓.under R = m →
    ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.under R = Ideal.span {f} → Q ≤ 𝔓 →
      (∀ Q' : Ideal (integralClosure R L), Q'.IsPrime → Q'.under R = Ideal.span {f} → Q' ≤ 𝔓 →
        Q' = Q) ∧
      (∀ (F : Type) [Field F] [Algebra (integralClosure R L ⧸ Q) F]
          [IsFractionRing (integralClosure R L ⧸ Q) F] (z : F),
        IsIntegral (integralClosure R L ⧸ Q) z →
        ∃ a s : integralClosure R L, s ∉ 𝔓 ∧
          algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))

/-! ## `BranchRegular` from `TameBranchNormal` -/

/-- `m = (dX − a, p)` for a maximal ideal of `ℤ[X]` containing both (`b = a/d`, `p ∤ d`). -/
theorem maximal_eq_span (p : ℕ) [hp : Fact p.Prime] (b : ℚ) (hb : 0 ≤ padicValRat p b)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hbm : C (b.den : ℤ) * X - C b.num ∈ m) :
    m = Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
  apply le_antisymm
  · intro u hu
    have h1 := homog_mem (Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)}) b.num b.den
      (Ideal.subset_span (by simp)) u
    have hdv : (p : ℤ) ∣ nval b u := (mem_m_iff p b hb m hpm hbm u).mp hu
    obtain ⟨t, ht⟩ := hdv
    have h2 : C (nval b u) ∈ Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
      rw [ht, C_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have h3 : C ((b.den : ℤ) ^ u.natDegree) * u ∈
        Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
      have := Ideal.add_mem _ h1 h2
      simpa [nval] using this
    -- `d^k` is invertible mod `p`
    have hcop : IsCoprime ((b.den : ℤ) ^ u.natDegree) (p : ℤ) := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hnd := not_dvd_den_of_nonneg p b hb
      have : Nat.Coprime b.den p :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd))
      exact_mod_cast this
    obtain ⟨α, β, hαβ⟩ := hcop
    have : u = C α * (C ((b.den : ℤ) ^ u.natDegree) * u) + C β * u * C (p : ℤ) := by
      have h := congrArg (C : ℤ → ℤ[X]) hαβ
      rw [C_add, C_mul, C_mul, C_1] at h
      linear_combination (-u) * h
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hbm
    · exact hpm


/-- `dX − a` is primitive (`b = a/d` in lowest terms). -/
theorem secGen_isPrimitive (b : ℚ) : (C (b.den : ℤ) * X - C b.num).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have e1 : (C (b.den : ℤ) * X - C b.num).coeff 1 = (b.den : ℤ) := by
    rw [coeff_sub, coeff_C_mul, coeff_X_one, coeff_C]; simp
  have e0 : (C (b.den : ℤ) * X - C b.num).coeff 0 = -b.num := by
    rw [coeff_sub, coeff_C_mul, coeff_X_zero, coeff_C]; simp
  have h1 : r ∣ (b.den : ℤ) := e1 ▸ hr 1
  have h0 : r ∣ b.num := dvd_neg.mp (e0 ▸ hr 0)
  have hcop : IsCoprime b.num (b.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact b.reduced
  exact hcop.isUnit_of_dvd' h0 h1

/-- The prime `(dX − a)` of `ℤ[X]` is the kernel of `X ↦ b` (Gauss's lemma). -/
theorem span_secGen_eq (b : ℚ) : Ideal.span {C (b.den : ℤ) * X - C b.num} =
    (Ideal.span {X - C b}).comap (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
  ext u
  rw [Ideal.mem_span_singleton, Ideal.mem_comap, Ideal.mem_span_singleton, coe_mapRingHom,
    IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (secGen_isPrimitive b)]
  have hmap : (C (b.den : ℤ) * X - C b.num).map (Int.castRingHom ℚ) = C (b.den : ℚ) * (X - C b) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
    simp only [eq_intCast, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num b, C_mul]
    ring
  rw [hmap]
  have hu : IsUnit (C (b.den : ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast b.den_nz))
  exact hu.mul_left_dvd

theorem span_secGen_isPrime (b : ℚ) : (Ideal.span {C (b.den : ℤ) * X - C b.num}).IsPrime := by
  rw [span_secGen_eq]
  haveI : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
  exact Ideal.comap_isPrime _ _

end SGRDirect.NVLocal

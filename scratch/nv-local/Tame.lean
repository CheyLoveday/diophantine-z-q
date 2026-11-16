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
      (∀ (F : Type) [CommRing F] [Algebra (integralClosure R L ⧸ Q) F]
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

theorem secGen_map (b : ℚ) :
    (C (b.den : ℤ) * X - C b.num).map (Int.castRingHom ℚ) = C (b.den : ℚ) * (X - C b) := by
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
  simp only [eq_intCast, Int.cast_natCast]
  rw [← Rat.mul_den_eq_num b, C_mul]
  ring

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


section Loc

variable (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

/-- The nonzero integers in `ℤ[X]`. -/
abbrev intSub : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])

omit [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] in
/-- The `ℚ[X]`-closure is the localization of the `ℤ[X]`-closure at the nonzero integers. -/
theorem isLocalization_B :
    letI := intPolyAlg E
    letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub)
      (integralClosure ℚ[X] E) := by
  letI := intPolyAlg E
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  have hcoe : ∀ k : ℤ, (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
      (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E) = (k : E) := by
    intro k
    show algebraMap ℚ[X] E ((C k).map (Int.castRingHom ℚ)) = (k : E)
    simp
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hk
    refine ⟨⟨algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k) |> algebraMap _ (integralClosure ℚ[X] E),
      algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (k : ℚ)⁻¹), ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show ((algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) * algebraMap ℚ[X] E (C (k : ℚ)⁻¹) = 1
      rw [hcoe, show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
        mul_inv_cancel₀ hk0, C_1, map_one]
    · apply Subtype.ext
      show algebraMap ℚ[X] E (C (k : ℚ)⁻¹) * ((algebraMap (integralClosure ℤ[X] E)
        (integralClosure ℚ[X] E) (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) = 1
      rw [hcoe, show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
        inv_mul_cancel₀ hk0, C_1, map_one]
  · intro z
    obtain ⟨k, hk, c, hc⟩ := exists_int_mul_mem z
    refine ⟨⟨c, ⟨_, ⟨C k, ⟨k, mem_nonZeroDivisors_of_ne_zero hk, rfl⟩, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show (z : E) * ((algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
      (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) = c
    rw [hcoe, hc, mul_comm]
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : x = y := Subtype.ext (congrArg (fun w : integralClosure ℚ[X] E => (w : E)) hxy)
    rw [this]

omit [IsScalarTower ℚ[X] (RatFunc ℚ) E] in
/-- **Height-one primes near `m` off `(dX − a)` and `(p)` are unramified** (from `BranchData` and the
distinctness mod `p`; the ramification index is transported from the `ℚ[X]`-closure by
`ramificationIdx_map_localization`). -/
theorem unram_near (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ) [hp : Fact p.Prime]
    (hB : BranchData E S n nInf) (hint : ∀ b ∈ S, 0 ≤ padicValRat p b)
    (hdist : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) (b : ℚ) (hb : b ∈ S)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hbm : C (b.den : ℤ) * X - C b.num ∈ m) :
    letI := intPolyAlg E
    ∀ P : Ideal ℤ[X], P.IsPrime → P.height = 1 → P ≤ m → C (b.den : ℤ) * X - C b.num ∉ P →
      C (p : ℤ) ∉ P → ∀ P' : Ideal (integralClosure ℤ[X] E), P'.IsPrime → P'.under ℤ[X] = P →
        P'.ramificationIdx ℤ[X] = 1 := by
  letI := intPolyAlg E
  intro P hP _ hPm hfP hgP P' hP' hP'u
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  letI : Algebra ℤ[X] ℚ[X] := Polynomial.algebra ℤ ℚ
  letI : Algebra ℤ[X] (integralClosure ℚ[X] E) :=
    ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp (algebraMap ℤ[X] ℚ[X])).toAlgebra
  haveI : IsScalarTower ℤ[X] ℚ[X] (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (by
      show algebraMap ℚ[X] E (algebraMap ℤ[X] ℚ[X] x) = algebraMap ℚ[X] E (x.map (Int.castRingHom ℚ))
      rw [Polynomial.algebraMap_def ℤ ℚ]
      congr 2))
  haveI : IsLocalization intSub ℚ[X] := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  haveI := isLocalization_B E
  haveI := hP'
  -- `P` contains no nonzero integer
  have hPZ : P.comap (C : ℤ →+* ℤ[X]) = ⊥ := by
    by_contra hne
    haveI : (P.comap (C : ℤ →+* ℤ[X])).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (P.comap (C : ℤ →+* ℤ[X])).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    have hle : P.comap (C : ℤ →+* ℤ[X]) ≤ m.comap C := Ideal.comap_mono hPm
    have hmne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)
    have heq := hmax.eq_of_le hmne hle
    apply hgP
    rw [← Ideal.mem_comap, heq, Ideal.mem_comap]
    exact hpm
  have hdisj : Disjoint ((intSub : Submonoid ℤ[X]) : Set ℤ[X]) (P'.under ℤ[X]) := by
    rw [hP'u, Set.disjoint_left]
    rintro _ ⟨k, hk, rfl⟩ hkP
    have : k ∈ P.comap (C : ℤ →+* ℤ[X]) := hkP
    rw [hPZ, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hk this
  have hdisj' : Disjoint ((Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub :
      Submonoid (integralClosure ℤ[X] E)) : Set (integralClosure ℤ[X] E)) (P' : Set _) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxP
    exact Set.disjoint_left.mp hdisj hx hxP
  haveI hPB : (P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P' inferInstance hdisj'
  have hcomapB : (P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))).comap
      (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) = P' :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj'
  rw [← ramificationIdx_map_localization (Rₘ := ℚ[X]) (Sₘ := integralClosure ℚ[X] E) intSub P' hdisj]
  refine hB.1 _ hPB ?_
  intro b' hb' hcon
  set F : ℤ[X] := C (b'.den : ℤ) * X - C b'.num with hFdef
  have hFm : algebraMap ℚ[X] (integralClosure ℚ[X] E) (F.map (Int.castRingHom ℚ)) ∈
      P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) := by
    rw [← Ideal.mem_comap, ← Ideal.under_def, hcon]
    have hF : F ∈ Ideal.span {F} := Ideal.mem_span_singleton_self F
    rw [hFdef, span_secGen_eq b', Ideal.mem_comap] at hF
    exact hF
  have hFP : F ∈ P := by
    rw [← hP'u, Ideal.under_def, Ideal.mem_comap, ← hcomapB, Ideal.mem_comap,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X] ℚ[X],
      Polynomial.algebraMap_def ℤ ℚ]
    exact hFm
  by_cases hbb : b' = b
  · rw [hFdef, hbb] at hFP
    exact hfP hFP
  · apply (notMem_of_val_zero p b (hint b hb) m (Ideal.IsMaximal.ne_top ‹_›) hpm hbm F ?_ ?_)
      (hPm hFP)
    · rw [hFdef, secGen_map, eval_mul, eval_C, eval_sub, eval_X, eval_C]
      exact mul_ne_zero (by exact_mod_cast b'.den_nz) (sub_ne_zero.mpr (Ne.symm hbb))
    · rw [hFdef, secGen_map, eval_mul, eval_C, eval_sub, eval_X, eval_C,
        padicValRat.mul (by exact_mod_cast b'.den_nz) (sub_ne_zero.mpr (Ne.symm hbb)),
        hdist b hb b' hb' (Ne.symm hbb), padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p b' (hint b' hb'))]
      simp

end Loc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **`BranchRegular` from `TameBranchNormal`** (compiled): take `R = ℤ[X]`, `m = (dX − a, p)`, `f = dX − a`,
`g = p`; `ℤ[X]_m` is regular of dimension `2` (`regular_dim2_intPoly`), the other height-one primes near `m`
are unramified (`unram_near`), the branch `Q` of `B` gives the prime `Q ∩ C` of `C` over `(f)`, and `B/Q` is a
fraction field of `C/(Q ∩ C)` (`B` is the localization of `C` at the nonzero integers). -/
theorem branchRegular_of_tame (h : TameBranchNormal) : BranchRegular := by
  intro E _ _ _ _ _ _ S n nInf p hp hB hdeg hint hdist b hb
  letI := intPolyAlg E
  intro 𝔓 h𝔓 hp𝔓 hb𝔓 Q hQ hQu hQ𝔓
  haveI : Fact p.Prime := ⟨hp⟩
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  set m := 𝔓.under ℤ[X] with hmdef
  haveI : m.IsMaximal := Ideal.IsMaximal.under ℤ[X] 𝔓
  have hmne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥ := by
    intro h0
    have : (p : ℤ) ∈ m.comap (C : ℤ →+* ℤ[X]) := hp𝔓
    rw [h0, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  obtain ⟨hreg, hdim⟩ := regular_dim2_intPoly m hmne
  have hm := maximal_eq_span p b (hint b hb) m hp𝔓 hb𝔓
  have hpR : (p : ℤ[X]) ∈ m := by rw [← map_natCast C p]; exact hp𝔓
  have hunr := unram_near E S n nInf p hB hint hdist b hb m hp𝔓 hb𝔓
  have hcomp : (zqIncl E).comp (algebraMap ℤ[X] (integralClosure ℤ[X] E)) =
      (algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    exact RingHom.ext (fun x => Subtype.ext rfl)
  have hunderC : ∀ Q' : Ideal (integralClosure ℚ[X] E), Q'.under ℚ[X] = Ideal.span {X - C b} →
      (Q'.comap (zqIncl E)).under ℤ[X] = Ideal.span {C (b.den : ℤ) * X - C b.num} := by
    intro Q' hQ'u
    rw [span_secGen_eq, ← hQ'u, Ideal.under_def, Ideal.under_def, Ideal.comap_comap, hcomp,
      ← Ideal.comap_comap]
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  haveI hloc := isLocalization_B E
  let QC := Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))
  haveI : QC.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hUB, hN⟩ := h ℤ[X] (RatFunc ℚ) E m hreg hdim _ _ hm (span_secGen_isPrime b) p hp hpR hdeg
    hunr 𝔓 h𝔓 rfl QC inferInstance (hunderC Q hQu) hQ𝔓
  refine ⟨?_, ?_⟩
  · intro Q' hQ' hQ'u hQ'𝔓
    haveI : (Q'.comap (zqIncl E)).IsPrime := Ideal.comap_isPrime _ _
    have hc := hUB (Q'.comap (zqIncl E)) inferInstance (hunderC Q' hQ'u) hQ'𝔓
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub)
      (integralClosure ℚ[X] E) Q', ← IsLocalization.map_under
      (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub) (integralClosure ℚ[X] E) Q]
    exact congrArg (Ideal.map _) hc
  · intro z hz
    have hspan : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
    haveI : Q.LiesOver (Ideal.span {X - C b}) := ⟨hQu.symm⟩
    haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {X - C b})
    letI alg : Algebra (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) :=
      Ideal.Quotient.algebraQuotientOfLEComap le_rfl
    have hinj : Function.Injective (algebraMap (integralClosure ℤ[X] E ⧸ QC)
        (integralClosure ℚ[X] E ⧸ Q)) := Ideal.algebraMap_quotient_injective
    have hmk : ∀ c, algebraMap (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q)
        (Ideal.Quotient.mk QC c) = Ideal.Quotient.mk Q (zqIncl E c) := fun _ => rfl
    have hkQ : ∀ k : ℤ, k ≠ 0 → zqIncl E (k : integralClosure ℤ[X] E) ∉ Q := by
      intro k hk hkQ
      have hu : IsUnit (zqIncl E (k : integralClosure ℤ[X] E)) := by
        rw [map_intCast]
        refine isUnit_iff_exists.mpr ⟨algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (k : ℚ)⁻¹), ?_, ?_⟩
        · apply Subtype.ext
          show (k : E) * algebraMap ℚ[X] E (C (k : ℚ)⁻¹) = 1
          rw [show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
            mul_inv_cancel₀ (by exact_mod_cast hk), C_1, map_one]
        · apply Subtype.ext
          show algebraMap ℚ[X] E (C (k : ℚ)⁻¹) * (k : E) = 1
          rw [show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
            inv_mul_cancel₀ (by exact_mod_cast hk), C_1, map_one]
      exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ hkQ hu)
    haveI : IsFractionRing (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, hx⟩
        have hx0 := hinj.ne (nonZeroDivisors.ne_zero hx)
        rw [map_zero] at hx0
        obtain ⟨y, hy⟩ := Ideal.Quotient.exists_inv hx0
        exact IsUnit.of_mul_eq_one _ hy
      · intro w
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
        obtain ⟨k, hk, c, hc⟩ := exists_int_mul_mem y
        have hk0 : Ideal.Quotient.mk QC (k : integralClosure ℤ[X] E) ≠ 0 := by
          intro h0
          apply hkQ k hk
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmk, h0, map_zero]
        refine ⟨⟨Ideal.Quotient.mk QC c, ⟨_, mem_nonZeroDivisors_of_ne_zero hk0⟩⟩, ?_⟩
        show Ideal.Quotient.mk Q y * algebraMap _ _ (Ideal.Quotient.mk QC (k : integralClosure ℤ[X] E)) =
          algebraMap _ _ (Ideal.Quotient.mk QC c)
        rw [hmk, hmk, ← map_mul]
        congr 1
        apply Subtype.ext
        show (y : E) * ((k : integralClosure ℤ[X] E) : E) = c
        rw [hc]; push_cast; ring
      · intro x y hxy
        exact ⟨1, by rw [hinj hxy]⟩
    haveI : IsScalarTower ℤ (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) :=
      ⟨fun n a w => by
        rw [Algebra.smul_def, Algebra.smul_def, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast,
          mul_assoc]⟩
    have hz' : IsIntegral (integralClosure ℤ[X] E ⧸ QC) z := hz.tower_top
    obtain ⟨a, s, hs, hsz⟩ := hN (integralClosure ℚ[X] E ⧸ Q) z hz'
    exact ⟨a, s, hs, hsz⟩

end SGRDirect.NVLocal

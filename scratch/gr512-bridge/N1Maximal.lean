import ZInQKernel.Contrib.OneProof.EichlerBound.Order

/-!
# gr512-bridge, N1: `LeafQM.O` is a maximal order of `B = (2, −3 | ℚ)`

Every subring `O' ⊇ 𝒪` of `B` all of whose elements are integral over `ℤ` is `𝒪`. Proof: an element
of `B` integral over `ℤ` has integral reduced trace and norm (its minimal polynomial over `ℚ` divides a
monic integer polynomial: Gauss's lemma); for `x ∈ O'`, `trd(x e) ∈ ℤ` for `e` in the basis
`1, i, (1+j)/2, (i+k)/2` of `𝒪` and `nrd(x) ∈ ℤ` force `x ∈ 𝒪` (a congruence modulo `144`, checked by
`decide` on `2·4·6·12` residues).
-/

set_option linter.style.longLine false

noncomputable section

namespace GR512Bridge.N1

open EichlerBound Polynomial
open scoped QuaternionAlgebra

/-! ## 1. Integral elements have integral reduced trace and norm -/

theorem trd_algebraMap (q : ℚ) : trd (algebraMap ℚ B q) = 2 * q := by
  simp [trd]

theorem nrd_algebraMap (q : ℚ) : nrd (algebraMap ℚ B q) = q ^ 2 := by
  simp [nrd]

/-- The reduced characteristic polynomial `X² − trd(x) X + nrd(x)` over `ℚ`. -/
def charpolyQ (x : B) : ℚ[X] := X ^ 2 - C (trd x) * X + C (nrd x)

theorem charpolyQ_monic (x : B) : (charpolyQ x).Monic := by
  unfold charpolyQ; monicity!

theorem charpolyQ_natDegree (x : B) : (charpolyQ x).natDegree = 2 := by
  unfold charpolyQ; compute_degree!

theorem aeval_charpolyQ (x : B) : aeval x (charpolyQ x) = 0 := by
  unfold charpolyQ
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
  rw [sq, sq_eq_trd, QuaternionAlgebra.coe_algebraMap]
  abel

/-- **An element of `B` integral over `ℤ` has `trd, nrd ∈ ℤ`.** -/
theorem int_of_isIntegral {x : B} (hx : IsIntegral ℤ x) :
    (∃ z : ℤ, trd x = z) ∧ (∃ z : ℤ, nrd x = z) := by
  by_cases hq : x ∈ (algebraMap ℚ B).range
  · obtain ⟨q, rfl⟩ := hq
    have hqi : IsIntegral ℤ q := (isIntegral_algHom_iff ((Algebra.ofId ℚ B).restrictScalars ℤ) (algebraMap ℚ B).injective).mp hx
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
    refine ⟨⟨2 * z, ?_⟩, ⟨z ^ 2, ?_⟩⟩
    · rw [trd_algebraMap, ← hz]; push_cast; simp
    · rw [nrd_algebraMap, ← hz]; push_cast; simp
  · have hxQ : IsIntegral ℚ x := hx.tower_top
    have hdvd : minpoly ℚ x ∣ charpolyQ x := minpoly.dvd ℚ x (aeval_charpolyQ x)
    have hdeg1 : (minpoly ℚ x).natDegree ≠ 1 := fun h => hq (minpoly.natDegree_eq_one_iff.mp h)
    have hpos := minpoly.natDegree_pos hxQ
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      rw [← charpolyQ_natDegree x]
      exact natDegree_le_of_dvd hdvd (charpolyQ_monic x).ne_zero
    have heq : charpolyQ x = minpoly ℚ x :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxQ) (charpolyQ_monic x) hdvd
        (by rw [charpolyQ_natDegree]; omega)
    obtain ⟨P, hPm, hP⟩ := hx
    have hdvdP : minpoly ℚ x ∣ P.map (algebraMap ℤ ℚ) :=
      minpoly.dvd ℚ x (by rw [aeval_map_algebraMap, aeval_def]; exact hP)
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hPm hdvdP
    rw [(minpoly.monic hxQ).leadingCoeff, C_1, mul_one, ← heq] at hg
    have h1 := congrArg (fun p => p.coeff 1) hg
    have h0 := congrArg (fun p => p.coeff 0) hg
    simp [charpolyQ, coeff_X, coeff_C] at h1 h0
    refine ⟨⟨-g.coeff 1, by push_cast; linarith⟩, ⟨g.coeff 0, by linarith⟩⟩

/-! ## 2. The congruence -/

/-- The residue check (`2·4·6·12 = 576` cases). -/
theorem residues : ∀ (a : Fin 2) (b : Fin 4) (c : Fin 6) (d : Fin 12),
    (36 * ((a : ℕ) : ℤ) ^ 2 - 18 * ((b : ℕ) : ℤ) ^ 2 + 12 * ((c : ℕ) : ℤ) ^ 2 - 6 * ((d : ℕ) : ℤ) ^ 2) % 144 = 0 →
      (((d : ℕ) : ℤ) - (b : ℕ)) % 2 = 0 →
        ((c : ℕ) : ℤ) % 3 = 0 ∧ ((d : ℕ) : ℤ) % 6 = 0 ∧ (3 * ((b : ℕ) : ℤ) - (d : ℕ)) % 12 = 0 := by
  decide

theorem residues' (a b c d : ℕ) (ha : a < 2) (hb : b < 4) (hc : c < 6) (hd : d < 12) :
    (36 * (a : ℤ) ^ 2 - 18 * (b : ℤ) ^ 2 + 12 * (c : ℤ) ^ 2 - 6 * (d : ℤ) ^ 2) % 144 = 0 →
      ((d : ℤ) - b) % 2 = 0 →
        (c : ℤ) % 3 = 0 ∧ (d : ℤ) % 6 = 0 ∧ (3 * (b : ℤ) - d) % 12 = 0 :=
  residues ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

theorem int_core (A B y z N : ℤ) (hzB : (z - B) % 2 = 0)
    (h : 36 * A ^ 2 - 18 * B ^ 2 + 12 * y ^ 2 - 6 * z ^ 2 = 144 * N) :
    y % 3 = 0 ∧ z % 6 = 0 ∧ (3 * B - z) % 12 = 0 := by
  obtain ⟨q1, a, rfl, ha0, ha1⟩ : ∃ q a : ℤ, A = 2 * q + a ∧ 0 ≤ a ∧ a < 2 :=
    ⟨A / 2, A % 2, by omega, by omega, by omega⟩
  obtain ⟨q2, b, rfl, hb0, hb1⟩ : ∃ q b : ℤ, B = 4 * q + b ∧ 0 ≤ b ∧ b < 4 :=
    ⟨B / 4, B % 4, by omega, by omega, by omega⟩
  obtain ⟨q3, c, rfl, hc0, hc1⟩ : ∃ q c : ℤ, y = 6 * q + c ∧ 0 ≤ c ∧ c < 6 :=
    ⟨y / 6, y % 6, by omega, by omega, by omega⟩
  obtain ⟨q4, d, rfl, hd0, hd1⟩ : ∃ q d : ℤ, z = 12 * q + d ∧ 0 ≤ d ∧ d < 12 :=
    ⟨z / 12, z % 12, by omega, by omega, by omega⟩
  have e : 36 * a ^ 2 - 18 * b ^ 2 + 12 * c ^ 2 - 6 * d ^ 2 =
      144 * (N - (q1 ^ 2 + q1 * a) + (2 * q2 ^ 2 + q2 * b) - (3 * q3 ^ 2 + q3 * c) +
        (6 * q4 ^ 2 + q4 * d)) := by
    linear_combination h
  lift a to ℕ using ha0
  lift b to ℕ using hb0
  lift c to ℕ using hc0
  lift d to ℕ using hd0
  have := residues' a b c d (by omega) (by omega) (by omega) (by omega)
    (by rw [e]; simp) (by omega)
  omega

/-! ## 3. Maximality -/

/-- `x` with `trd(x 𝒪) ⊆ ℤ` and `nrd(x) ∈ ℤ` lies in `𝒪`. -/
theorem mem_O_of_int {x : B} (htr : ∀ e ∈ LeafQM.O, ∃ z : ℤ, trd (x * e) = z)
    (hn : ∃ z : ℤ, nrd x = z) : x ∈ LeafQM.O := by
  obtain ⟨A, hA⟩ := htr (LeafQM.ofInt ![1, 0, 0, 0]) (ofInt_mem _)
  obtain ⟨Bi, hB⟩ := htr (LeafQM.ofInt ![0, 1, 0, 0]) (ofInt_mem _)
  obtain ⟨C, hC⟩ := htr (LeafQM.ofInt ![0, 0, 1, 0]) (ofInt_mem _)
  obtain ⟨D, hD⟩ := htr (LeafQM.ofInt ![0, 0, 0, 1]) (ofInt_mem _)
  obtain ⟨N, hN⟩ := hn
  simp [trd, LeafQM.ofInt] at hA hB hC hD
  have hA' : (A : ℚ) = 2 * x.re := by linarith
  have hB' : (Bi : ℚ) = 4 * x.imI := by linarith
  have hC' : (C : ℚ) = x.re - 3 * x.imJ := by linarith
  have hD' : (D : ℚ) = 2 * x.imI + 6 * x.imK := by linarith
  have hcore : 36 * A ^ 2 - 18 * Bi ^ 2 + 12 * (A - 2 * C) ^ 2 - 6 * (2 * D - Bi) ^ 2 = 144 * N := by
    have : ((36 * A ^ 2 - 18 * Bi ^ 2 + 12 * (A - 2 * C) ^ 2 - 6 * (2 * D - Bi) ^ 2 : ℤ) : ℚ) =
        ((144 * N : ℤ) : ℚ) := by
      push_cast
      rw [hA', hB', hC', hD', ← hN]
      unfold nrd
      ring
    exact_mod_cast this
  obtain ⟨h3, h6, h12⟩ := int_core A Bi (A - 2 * C) (2 * D - Bi) N (by omega) hcore
  obtain ⟨n2, hn2⟩ : ∃ n2 : ℤ, A - 2 * C = 3 * n2 := ⟨(A - 2 * C) / 3, by omega⟩
  obtain ⟨n3, hn3⟩ : ∃ n3 : ℤ, 2 * D - Bi = 6 * n3 := ⟨(2 * D - Bi) / 6, by omega⟩
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℤ, 3 * Bi - (2 * D - Bi) = 12 * n1 := ⟨(3 * Bi - (2 * D - Bi)) / 12, by omega⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, A + C = 3 * n0 := ⟨(A + C) / 3, by omega⟩
  have e2 : ((A - 2 * C : ℤ) : ℚ) = ((3 * n2 : ℤ) : ℚ) := by rw [hn2]
  have e3 : ((2 * D - Bi : ℤ) : ℚ) = ((6 * n3 : ℤ) : ℚ) := by rw [hn3]
  have e1 : ((3 * Bi - (2 * D - Bi) : ℤ) : ℚ) = ((12 * n1 : ℤ) : ℚ) := by rw [hn1]
  have e0 : ((A + C : ℤ) : ℚ) = ((3 * n0 : ℤ) : ℚ) := by rw [hn0]
  push_cast at e2 e3 e1 e0
  refine ⟨![n0, n1, n2, n3], ?_⟩
  ext <;> simp [LeafQM.ofInt] <;> linarith

/-- **N1: `𝒪 = LeafQM.O` is a maximal order of `B = (2, −3 | ℚ)`**: a subring of `B` containing `𝒪`
all of whose elements are integral over `ℤ` (in particular any order containing `𝒪`) is `𝒪`. -/
theorem O_maximal (O' : Subring B) (hle : LeafQM.O ≤ O') (hint : ∀ x ∈ O', IsIntegral ℤ x) :
    O' = LeafQM.O := by
  refine le_antisymm (fun x hx => ?_) hle
  apply mem_O_of_int
  · intro e he
    exact (int_of_isIntegral (hint _ (O'.mul_mem hx (hle he)))).1
  · exact (int_of_isIntegral (hint x hx)).2

end GR512Bridge.N1

#print axioms GR512Bridge.N1.O_maximal

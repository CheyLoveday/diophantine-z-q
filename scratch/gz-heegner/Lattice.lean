import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development: lattice algebra (Dirichlet composition, homothety vs `Γ₀(N)`). -/

noncomputable section

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open scoped MatrixGroups

namespace ZInQ.GZHeegner

/-- `s_D = i√|D|`, the normalized square root of `D < 0`. -/
def sD (D : ℤ) : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)

theorem sD_sq {D : ℤ} (hD : D < 0) : sD D ^ 2 = D := ZInQ.GZHL3.Reps.sqrt_sq_D hD

theorem tau_eq {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    Q.tau = (-(Q.B : ℂ) + sD D) / (2 * Q.A) := rfl

theorem A_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (Q.A : ℂ) ≠ 0 := by
  exact_mod_cast Q.A_pos.ne'

/-- The lattice `⟨a, (−b + √D)/2⟩ ⊂ ℂ` (the ideal of norm `a` attached to the form `[a, b, c]`). -/
def jLat (D a b : ℤ) : Submodule ℤ ℂ := Submodule.span ℤ {(a : ℂ), (-(b : ℂ) + sD D) / 2}

/-- Product of two lattices given by pairs of generators. -/
theorem span_pair_mul_span_pair (x₁ x₂ y₁ y₂ : ℂ) (L : Submodule ℤ ℂ)
    (h11 : x₁ * y₁ ∈ L) (h12 : x₁ * y₂ ∈ L) (h21 : x₂ * y₁ ∈ L) (h22 : x₂ * y₂ ∈ L) :
    Submodule.span ℤ {x₁, x₂} * Submodule.span ℤ {y₁, y₂} ≤ L := by
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact h11
  · rw [Set.mem_singleton_iff] at hy; subst hy; exact h12
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact h21
  · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact h22

theorem mul_mem_span_pair_mul (x₁ x₂ y₁ y₂ : ℂ) {x y : ℂ} (hx : x = x₁ ∨ x = x₂)
    (hy : y = y₁ ∨ y = y₂) :
    x * y ∈ Submodule.span ℤ {x₁, x₂} * Submodule.span ℤ {y₁, y₂} := by
  apply Submodule.mul_mem_mul
  · rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rcases hy with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)

theorem mem_span_pair_of {u v z : ℂ} (c d : ℤ) (h : z = c * u + d * v) :
    z ∈ Submodule.span ℤ {u, v} :=
  Submodule.mem_span_pair.2 ⟨c, d, by rw [h]; simp [zsmul_eq_mul]⟩

/-! ### Parity and Bezout -/

theorem add_even_of_disc {A B C a b t D : ℤ} (hd : B ^ 2 - 4 * A * C = D)
    (ht : b ^ 2 - D = 4 * a * t) : ∃ e : ℤ, b + B = 2 * e := by
  rcases Int.even_or_odd (b + B) with ⟨e, he⟩ | ⟨e, he⟩
  · exact ⟨e, by omega⟩
  · exfalso
    have h1 : (2 * e + 1) * (2 * e + 1 - 2 * B) = 2 * (2 * (a * t - A * C)) := by
      have hb : b = 2 * e + 1 - B := by omega
      subst hb; linear_combination ht - hd
    have hodd : Odd ((2 * e + 1) * (2 * e + 1 - 2 * B)) :=
      Int.odd_mul.2 ⟨⟨e, rfl⟩, ⟨e - B, by ring⟩⟩
    rw [h1] at hodd
    exact (Int.not_even_iff_odd.2 hodd) ⟨2 * (a * t - A * C), by ring⟩

/-- A form of squarefree discriminant is primitive. -/
theorem gcd_eq_one_of_squarefree {A B C D : ℤ} (hsq : Squarefree D) (hd : B ^ 2 - 4 * A * C = D) :
    Int.gcd (Int.gcd A B) C = 1 := by
  set g : ℕ := Int.gcd (Int.gcd A B) C
  have hgA : (g : ℤ) ∣ A := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  have h2 : (g : ℤ) * g ∣ D := by
    rw [← hd]
    exact dvd_sub (by rw [sq]; exact mul_dvd_mul hgB hgB)
      (by
        obtain ⟨x, hx⟩ := hgA; obtain ⟨y, hy⟩ := hgC
        exact ⟨4 * x * y, by rw [hx, hy]; ring⟩)
  have hu := hsq _ h2
  rw [Int.isUnit_iff] at hu
  rcases hu with h | h
  · exact_mod_cast h
  · have : (0 : ℤ) ≤ g := Int.natCast_nonneg _
    omega

/-- Bezout for a triple with `gcd = 1`. -/
theorem exists_bezout3 {x y z : ℤ} (h : Int.gcd (Int.gcd x y) z = 1) :
    ∃ p q r : ℤ, p * x + q * y + r * z = 1 := by
  have h1 : IsCoprime ((Int.gcd x y : ℕ) : ℤ) z := Int.isCoprime_iff_gcd_eq_one.2 (by simpa using h)
  obtain ⟨u, v, huv⟩ := h1
  refine ⟨u * Int.gcdA x y, u * Int.gcdB x y, v, ?_⟩
  rw [Int.gcd_eq_gcd_ab x y] at huv
  linear_combination huv

/-! ### Dirichlet composition with an ideal of norm prime to `A` -/

section Compose

variable {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) {a b : ℤ}

/-- The composite form `[aA, B + 2Ak, C']` (data of the composition, see `exists_compose`). -/
theorem exists_compose (hsq : Squarefree D) (ha : 0 < a) (hab : 4 * a ∣ b ^ 2 - D)
    (hcop : IsCoprime a Q.A) :
    ∃ Q' : HeegnerForm N D, 2 * Q.A ∣ Q'.B - Q.B ∧ jLat D a b * Q'.lat = Q.lat ∧
      jLat D a b * Q'.latN = Q.latN := by
  obtain ⟨t, ht⟩ := hab
  have hd := Q.disc
  obtain ⟨e, he⟩ := add_even_of_disc hd ht
  obtain ⟨u, v, huv⟩ := hcop
  set A := Q.A with hAdef
  set B := Q.B with hBdef
  set C := Q.C with hCdef
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = -(e * v) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, l = e * u := ⟨_, rfl⟩
  have hkl : B + 2 * A * k = -b + 2 * a * l := by
    rw [hk, hl]; linear_combination he - 2 * e * huv
  obtain ⟨W, hW⟩ : ∃ W : ℤ, W = C + B * k + A * k ^ 2 := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ℤ, C' = u * W + v * (t + l * (B + 2 * A * k) - a * l ^ 2) :=
    ⟨_, rfl⟩
  have hW' : A * W = a * (t + l * (B + 2 * A * k) - a * l ^ 2) := by
    have hb : b = 2 * a * l - B - 2 * A * k := by linarith
    rw [hb] at ht
    have h4 : 4 * (A * W) = 4 * (a * (t + l * (B + 2 * A * k) - a * l ^ 2)) := by
      rw [hW]; linear_combination ht - hd
    omega
  have haC : a * C' = W := by
    rw [hC']
    linear_combination W * huv - v * hW'
  obtain ⟨B', hB'⟩ : ∃ B' : ℤ, B' = B + 2 * A * k := ⟨_, rfl⟩
  have hdisc : B' ^ 2 - 4 * (a * A) * C' = D := by
    have : 4 * (a * A) * C' = 4 * A * (a * C') := by ring
    rw [this, haC, hW, hB']; linear_combination hd
  let Q' : HeegnerForm N D :=
    { A := a * A
      B := B'
      C := C'
      A_pos := mul_pos ha Q.A_pos
      N_dvd := dvd_mul_of_dvd_right Q.N_dvd a
      disc := hdisc
      D_neg := Q.D_neg
      primitive := gcd_eq_one_of_squarefree hsq hdisc }
  obtain ⟨A₁, hA₁⟩ := Q.N_dvd
  -- Bezout for `(a, B', N C')`
  obtain ⟨p, q, r, hpqr⟩ := exists_bezout3 (gcd_eq_one_of_squarefree hsq hdisc)
  have hbez : (p * A + r * u * C') * a + q * B' + (r * v * A₁) * (N * C') = 1 := by
    have hA : A = N * A₁ := hA₁
    rw [hA] at huv hpqr ⊢
    linear_combination hpqr + r * C' * huv
  -- complex numbers
  have hA0 : (A : ℂ) ≠ 0 := A_ne_zero Q
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN0 : (N : ℂ) ≠ 0 := by
    have : (N : ℤ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hA₁; exact Q.A_pos.ne' hA₁
    exact_mod_cast this
  have hs := sD_sq Q.D_neg
  set s := sD D
  have hτ : Q.tau = (-(B : ℂ) + s) / (2 * A) := rfl
  have hτ' : Q'.tau = (-(B' : ℂ) + s) / (2 * (a * A)) := by
    show cmPoint (a * A) B' D = _
    simp only [cmPoint]; push_cast; rfl
  have hkl' : (B : ℂ) + 2 * A * k = -b + 2 * a * l := by exact_mod_cast hkl
  have hB'c : (B' : ℂ) = B + 2 * A * k := by simp only [hB']; push_cast; ring
  have haC' : (a : ℂ) * C' = C + B * k + A * k ^ 2 := by
    have := haC; rw [hW] at this; exact_mod_cast this
  have hdc : (B : ℂ) ^ 2 - 4 * A * C = D := by exact_mod_cast hd
  have hAN : (A : ℂ) = N * A₁ := by exact_mod_cast hA₁
  -- the four products, in the basis `(1, τ)`
  have e1 : (a : ℂ) * Q'.tau = -k + Q.tau := by
    rw [hτ', hτ, hB'c]; field_simp; ring
  have e2 : (-(b : ℂ) + s) / 2 = (A * k + B - a * l) + A * Q.tau := by
    rw [hτ]; field_simp; linear_combination (-1 : ℂ) * hkl'
  have hroot : (A : ℂ) * Q.tau ^ 2 + B * Q.tau + C = 0 :=
    ZInQ.GZHL3.Reps.cmPoint_root Q.A_pos Q.disc Q.D_neg
  have hτ'' : Q'.tau = (Q.tau - k) / a := by
    rw [eq_div_iff ha0]; linear_combination e1
  have e3 : (-(b : ℂ) + s) / 2 * Q'.tau = (k * l - C') - l * Q.tau := by
    rw [hτ'', e2]
    field_simp
    linear_combination hroot + haC'
  -- generators of the product lattices
  have gen : ∀ (y₁ : ℂ) {L : Submodule ℤ ℂ}, L = Submodule.span ℤ {y₁, Q'.tau} →
      (a : ℂ) * y₁ ∈ jLat D a b * L ∧ (a : ℂ) * Q'.tau ∈ jLat D a b * L ∧
      (-(b : ℂ) + s) / 2 * y₁ ∈ jLat D a b * L ∧
      (-(b : ℂ) + s) / 2 * Q'.tau ∈ jLat D a b * L := by
    intro y₁ L hL
    subst hL
    exact ⟨mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inl rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inl rfl) (Or.inr rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inl rfl),
      mul_mem_span_pair_mul _ _ _ _ (Or.inr rfl) (Or.inr rfl)⟩
  have zmem : ∀ {M : Submodule ℤ ℂ} (c : ℤ) {x : ℂ}, x ∈ M → (c : ℂ) * x ∈ M := by
    intro M c x hx
    have := M.smul_mem c hx
    rwa [zsmul_eq_mul] at this
  have hbezC : (((p * A + r * u * C') * a + q * B' + r * v * A₁ * (N * C') : ℤ) : ℂ) = 1 := by
    exact_mod_cast hbez
  push_cast at hbezC
  rw [hB'c] at hbezC
  refine ⟨Q', ⟨k, by simp [Q', hB']⟩, ?_, ?_⟩
  · obtain ⟨m1, m2, m3, m4⟩ := gen 1 (L := Q'.lat) rfl
    rw [mul_one] at m1 m3
    apply le_antisymm
    · apply span_pair_mul_span_pair
      · exact mem_span_pair_of a 0 (by simp)
      · exact mem_span_pair_of (-k) 1 (by rw [e1]; simp)
      · exact mem_span_pair_of (A * k + B - a * l) A (by rw [mul_one, e2]; push_cast; ring)
      · exact mem_span_pair_of (k * l - C') (-l) (by rw [e3]; push_cast; ring)
    · set M := jLat D a b * Q'.lat
      have hone : (1 : ℂ) ∈ M := by
        have h : (1 : ℂ) = ((p * A + r * u * C' + q * l : ℤ) : ℂ) * a +
            (q : ℂ) * ((-(b : ℂ) + s) / 2 - (A : ℤ) * ((a : ℂ) * Q'.tau)) +
            (-(r * v * A₁ * N) : ℤ) * ((-(b : ℂ) + s) / 2 * Q'.tau + (l : ℤ) * ((a : ℂ) * Q'.tau)) := by
          rw [e3, e1, e2]
          push_cast
          linear_combination -hbezC
        rw [h]
        exact M.add_mem (M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2))))
          (zmem _ (M.add_mem m4 (zmem _ m2)))
      rw [HeegnerForm.lat, Submodule.span_le]
      rintro _ (rfl | h)
      · exact hone
      · rw [Set.mem_singleton_iff] at h; subst h
        have : Q.tau = (a : ℂ) * Q'.tau + (k : ℤ) * 1 := by rw [e1]; ring
        rw [this]
        exact M.add_mem m2 (zmem _ hone)
  · obtain ⟨m1, m2, m3, m4⟩ := gen (1 / (N : ℂ)) (L := Q'.latN) rfl
    apply le_antisymm
    · apply span_pair_mul_span_pair
      · exact mem_span_pair_of a 0 (by simp)
      · exact mem_span_pair_of (-(k * N)) 1 (by rw [e1]; field_simp; push_cast; ring)
      · exact mem_span_pair_of (A * k + B - a * l) A₁ (by
          rw [e2]; push_cast; rw [hAN]; field_simp)
      · exact mem_span_pair_of (N * (k * l - C')) (-l) (by rw [e3]; field_simp; push_cast; ring)
    · set M := jLat D a b * Q'.latN
      have hone : (1 / (N : ℂ)) ∈ M := by
        have h : (1 / (N : ℂ)) = ((p * A + r * u * C' + q * l : ℤ) : ℂ) * (a * (1 / (N : ℂ))) +
            (q : ℂ) * ((-(b : ℂ) + s) / 2 * (1 / (N : ℂ)) - (A₁ : ℤ) * ((a : ℂ) * Q'.tau)) +
            (-(r * v * A₁) : ℤ) * ((-(b : ℂ) + s) / 2 * Q'.tau + (l : ℤ) * ((a : ℂ) * Q'.tau)) := by
          rw [e3, e1, e2, hAN]
          rw [hAN] at hbezC
          field_simp
          push_cast
          linear_combination -hbezC - ((p : ℂ) * a) * hAN
        rw [h]
        exact M.add_mem (M.add_mem (zmem _ m1) (zmem _ (M.sub_mem m3 (zmem _ m2))))
          (zmem _ (M.add_mem m4 (zmem _ m2)))
      rw [HeegnerForm.latN, Submodule.span_le]
      rintro _ (rfl | h)
      · exact hone
      · rw [Set.mem_singleton_iff] at h; subst h
        have : Q.tau = (a : ℂ) * Q'.tau + (k * N : ℤ) * (1 / (N : ℂ)) := by
          rw [e1]; field_simp; push_cast; ring
        rw [this]
        exact M.add_mem m2 (zmem _ hone)

end Compose

end ZInQ.GZHeegner

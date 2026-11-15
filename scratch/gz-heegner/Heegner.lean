import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development file (single file; see log.md). -/

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

/-! ### Homothety of lattice pairs versus `Γ₀(N)`-equivalence -/

/-- `(⟨1, τ_Q⟩, ⟨1/N, τ_Q⟩) = j·(⟨1, τ_{Q'}⟩, ⟨1/N, τ_{Q'}⟩)`. -/
def PairHom {N : ℕ} {D : ℤ} (Q Q' : HeegnerForm N D) (j : ℂ) : Prop :=
  Q.lat = Q'.lat.map (LinearMap.mulLeft ℤ j) ∧ Q.latN = Q'.latN.map (LinearMap.mulLeft ℤ j)

theorem map_mulLeft_span_pair (j u v : ℂ) :
    (Submodule.span ℤ {u, v}).map (LinearMap.mulLeft ℤ j) = Submodule.span ℤ {j * u, j * v} := by
  rw [Submodule.map_span, Set.image_pair]; rfl

theorem span_pair_eq {u₁ u₂ v₁ v₂ : ℂ} (h1 : u₁ ∈ Submodule.span ℤ {v₁, v₂})
    (h2 : u₂ ∈ Submodule.span ℤ {v₁, v₂}) (h3 : v₁ ∈ Submodule.span ℤ {u₁, u₂})
    (h4 : v₂ ∈ Submodule.span ℤ {u₁, u₂}) :
    Submodule.span ℤ {u₁, u₂} = Submodule.span ℤ {v₁, v₂} := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ (rfl | h)
    · exact h1
    · rw [Set.mem_singleton_iff] at h; subst h; exact h2
  · rw [Submodule.span_le]; rintro _ (rfl | h)
    · exact h3
    · rw [Set.mem_singleton_iff] at h; subst h; exact h4

theorem gamma0_dvd {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ

theorem N_ne_zero {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : (N : ℂ) ≠ 0 := by
  have : (N : ℤ) ≠ 0 := by
    intro h0; obtain ⟨x, hx⟩ := Q.N_dvd; rw [h0, zero_mul] at hx; exact Q.A_pos.ne' hx
  exact_mod_cast this

/-- **`Γ₀(N)`-equivalent Heegner forms have homothetic lattice pairs.** -/
theorem pairHom_of_equiv {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D}
    (h : ZInQ.GZHL3.Gamma0Equiv Q Q') : ∃ j : ℂ, j ≠ 0 ∧ PairHom Q Q' j := by
  obtain ⟨γ, hγ, e⟩ := h
  obtain ⟨c₁, hc₁⟩ := gamma0_dvd hγ
  have hdet : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast ZInQ.GZHL3.Reps.det_SL γ
  set τ : ℂ := (Q.tauH : ℂ)
  set w : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) with hwdef
  have hw : w ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ Q.tauH
    simpa [UpperHalfPlane.denom, w, τ] using this
  have hzw : (Q'.tau : ℂ) * w = ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) := by
    have : (Q'.tau : ℂ) = ((γ • Q.tauH : ℍ) : ℂ) := by rw [e]; rfl
    rw [this, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    exact div_mul_cancel₀ _ hw
  have hc : ((γ 1 0 : ℤ) : ℂ) = N * c₁ := by exact_mod_cast hc₁
  have hN := N_ne_zero Q
  have hτ : Q.tau = τ := rfl
  have hdet' : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) - 1 = 0 := by
    rw [hdet]; ring
  set iN : ℂ := 1 / (N : ℂ) with hiNdef
  have hiN : (N : ℂ) * iN - 1 = 0 := by rw [hiNdef]; field_simp; ring
  have hc' : ((γ 1 0 : ℤ) : ℂ) - N * c₁ = 0 := by rw [hc]; ring
  refine ⟨w, hw, ?_, ?_⟩
  · rw [HeegnerForm.lat, HeegnerForm.lat, map_mulLeft_span_pair, mul_one, hτ]
    apply span_pair_eq
    · exact mem_span_pair_of (γ 0 0) (-(γ 1 0)) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast; linear_combination -hdet)
    · exact mem_span_pair_of (-(γ 0 1)) (γ 1 1) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast; linear_combination -τ * hdet)
    · exact mem_span_pair_of (γ 1 1) (γ 1 0) (by rw [hwdef]; ring)
    · exact mem_span_pair_of (γ 0 1) (γ 0 0) (by rw [mul_comm w Q'.tau, hzw]; ring)
  · rw [HeegnerForm.latN, HeegnerForm.latN, map_mulLeft_span_pair, ← hiNdef, hτ]
    apply span_pair_eq
    · exact mem_span_pair_of (γ 0 0) (-c₁) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast
        linear_combination (-iN) * hdet' - ((γ 0 1 : ℤ) + (γ 0 0 : ℤ) * τ) * iN * hc' -
          ((γ 0 1 : ℤ) + (γ 0 0 : ℤ) * τ) * c₁ * hiN)
    · exact mem_span_pair_of (-(γ 0 1 * N)) (γ 1 1) (by
        rw [mul_comm w Q'.tau, hzw, hwdef]; push_cast
        linear_combination (-τ) * hdet' +
          ((γ 0 1 : ℤ) * (((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ))) * hiN)
    · exact mem_span_pair_of (γ 1 1) c₁ (by
        rw [hwdef]; linear_combination (τ * iN) * hc' + (c₁ * τ) * hiN)
    · exact mem_span_pair_of (γ 0 1 * N) (γ 0 0) (by
        rw [mul_comm w Q'.tau, hzw]; push_cast; linear_combination (-((γ 0 1 : ℤ) : ℂ)) * hiN)

theorem int_indep {τ : ℂ} (hτ : 0 < τ.im) {x y : ℤ} (h : (x : ℂ) + y * τ = 0) : x = 0 ∧ y = 0 := by
  have him := congrArg Complex.im h
  simp at him
  rcases him with h1 | h1
  · subst h1; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exact absurd h1 hτ.ne'

theorem exists_coords {u v z : ℂ} (h : z ∈ Submodule.span ℤ {u, v}) :
    ∃ c d : ℤ, z = c * u + d * v := by
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 h
  exact ⟨c, d, by rw [← hcd]; simp [zsmul_eq_mul]⟩

/-- **Homothetic lattice pairs come from `Γ₀(N)`-equivalent Heegner forms.** -/
theorem equiv_of_pairHom {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} {j : ℂ} (h : PairHom Q Q' j) :
    ZInQ.GZHL3.Gamma0Equiv Q Q' := by
  obtain ⟨hL, hLN⟩ := h
  rw [HeegnerForm.lat, HeegnerForm.lat, map_mulLeft_span_pair, mul_one] at hL
  rw [HeegnerForm.latN, HeegnerForm.latN, map_mulLeft_span_pair] at hLN
  have hτ1 : 0 < Q.tau.im := Q.tauH.im_pos
  have hτ2 : 0 < Q'.tau.im := Q'.tauH.im_pos
  have hN := N_ne_zero Q
  -- `j = t + r τ`, `j τ' = q + p τ`
  obtain ⟨t, r, htr⟩ := exists_coords (z := j) (by rw [hL]; exact Submodule.subset_span (by simp))
  obtain ⟨q, p, hqp⟩ := exists_coords (z := j * Q'.tau)
    (by rw [hL]; exact Submodule.subset_span (by simp))
  obtain ⟨x, y, hxy⟩ := exists_coords (z := 1) (by rw [← hL]; exact Submodule.subset_span (by simp))
  obtain ⟨u, v, huv⟩ := exists_coords (z := Q.tau) (by
    rw [← hL]; exact Submodule.subset_span (by simp))
  obtain ⟨α, β, hαβ⟩ := exists_coords (z := j * (1 / N)) (by
    rw [hLN]; exact Submodule.subset_span (by simp))
  have e1 : ((x * t + y * q - 1 : ℤ) : ℂ) + ((x * r + y * p : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast; linear_combination -hxy - x * htr - y * hqp
  have e2 : ((u * t + v * q : ℤ) : ℂ) + ((u * r + v * p - 1 : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast; linear_combination -huv - u * htr - v * hqp
  have e3 : ((t - α : ℤ) : ℂ) + ((r - N * β : ℤ) : ℂ) * Q.tau = 0 := by
    push_cast
    have : j = α + N * β * Q.tau := by
      have h' := hαβ; field_simp at h'; linear_combination h'
    linear_combination this - htr
  obtain ⟨i1, i2⟩ := int_indep hτ1 e1
  obtain ⟨i3, i4⟩ := int_indep hτ1 e2
  obtain ⟨-, i6⟩ := int_indep hτ1 e3
  have hdet1 : (x * v - y * u) * (t * p - q * r) = 1 := by
    linear_combination (u * r + v * p) * i1 + i4 - (u * t + v * q) * i2
  have hj : j ≠ 0 := by
    rintro rfl; simp at hxy
  -- the determinant is positive
  have him : (((t * p - q * r : ℤ) : ℝ)) * Q.tau.im = Complex.normSq j * Q'.tau.im := by
    have h1 : (starRingEnd ℂ) j * (j * Q'.tau) = (Complex.normSq j : ℂ) * Q'.tau := by
      rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    have h2 := congrArg Complex.im h1
    rw [hqp] at h2
    conv_lhs at h2 => rw [htr]
    simp only [map_add, map_mul, map_intCast, map_one, Complex.mul_im, Complex.add_im,
      Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im] at h2
    push_cast
    linear_combination h2
  have hpos : 0 < t * p - q * r := by
    have h3 : 0 < Complex.normSq j * Q'.tau.im := mul_pos (Complex.normSq_pos.2 hj) hτ2
    rw [← him] at h3
    have h4 : (0 : ℝ) < ((t * p - q * r : ℤ) : ℝ) := pos_of_mul_pos_left h3 hτ1.le
    exact_mod_cast h4
  have hdet : t * p - q * r = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' (by linarith [hdet1] : (t * p - q * r) * (x * v - y * u) = 1) with h | h
    · exact h.1
    · omega
  have hr : r = N * β := by linarith
  let γ : SL(2, ℤ) := ⟨!![p, q; r, t], by simp [Matrix.det_fin_two]; linarith⟩
  refine ⟨γ, ?_, ?_⟩
  · show ((γ 1 0 : ℤ) : ZMod N) = 0
    simp [γ, hr]
  · apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [γ, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    have hτ' : (Q'.tauH : ℂ) = Q'.tau := rfl
    have hτq : (Q.tauH : ℂ) = Q.tau := rfl
    have hden : (r : ℂ) * Q.tau + t = j := by rw [htr]; ring
    rw [hτ', hτq, div_eq_iff (by rw [hden]; exact hj), hden]
    linear_combination -hqp


/-! ## §2. The canonical model of `X₀(N)` for meromorphic functions (the leaf) -/

open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA
open scoped WeierstrassCurve.Affine

/-- **`g ∈ ℚ(X₀(N))`, as a function on `ℍ`**: `g` is `Γ₀(N)`-invariant, meromorphic on `ℍ`,
of moderate growth at every cusp (`g(γτ) = O(e^{2πk Im τ})` as `Im τ → ∞`, i.e. meromorphic at the
cusp `γ∞`), and has a Laurent expansion `g = q^{-k} Σ aₙ qⁿ` with `aₙ ∈ ℚ` for `Im τ` large.
The values of `g` at its poles are irrelevant (junk). Compared with the kernel's `IsRatModFn`, the
only change is that poles in `ℍ` are allowed: the `q`-expansion is required only near `∞`. -/
def IsRatModFnMero (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ τ : UpperHalfPlane, MeromorphicAt (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
  (∀ γ : SL(2, ℤ), ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty]
        fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

/-- `g` is **regular at `τ`** (holomorphic in a neighbourhood, with value `g τ`). -/
def RegularAt (g : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : Prop :=
  AnalyticAt ℂ (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)

/-- **X0-MODULI, printed form (every `g ∈ ℚ(X₀(N))` regular at the two points).** As the kernel's
`T5Glue.X0ModuliGalois`, with `IsRatModFn N g` (regular on all of `ℍ`) weakened to
`IsRatModFnMero N g` (`g ∈ ℚ(X₀(N))`, poles allowed) plus regularity of `g` at `τ` and `τ'`:
for `σ ∈ Aut(ℂ)` carrying the algebraic point `(E_τ, ⟨1/N⟩)` of `Y₀(N)` to `(E_{τ'}, ⟨k/N⟩)`,
`σ(g(τ)) = g(τ')`.

This is the printed statement: `X₀(N)_ℚ` is the coarse moduli space of pairs `(E, C)`, compatibly
with `Aut(ℂ)`, and `g(x)^σ = g(x^σ)` for every `g ∈ ℚ(X₀(N))` **regular at `x`** (Shimura 1971,
*Introduction to the arithmetic theory of automorphic functions*, §6.7, Prop. 6.9, Thm. 6.23;
Deligne–Rapoport, LNM 349, VI.6 and VII; Diamond–Shurman, §7.5–7.7; theorem numbers UNVERIFIED,
from memory). The kernel's regular-on-`ℍ` form is the special case (`x0ModuliGalois_of_mero`). -/
def X0ModuliGaloisMero : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFnMero N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ), RegularAt g τ → RegularAt g τ' →
      (∀ i < N, ∃ a : Qbar, ιC a = T5Glue.modCoord N τ i) →
      T5Glue.IsConjModel (σ : ℂ →+* ℂ) (T5Glue.pp τ) (T5Glue.pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((T5Glue.pp τ).weierstrassP (1 / N)) = μ ^ 2 * (T5Glue.pp τ').weierstrassP (k / N) ∧
        σ ((T5Glue.pp τ).derivWeierstrassP (1 / N)) =
          μ ^ 3 * (T5Glue.pp τ').derivWeierstrassP (k / N)) →
      σ (g τ) = g τ'

/-! ## §3. The coordinates of the modular parametrization, and the analytic glue -/

section Param

variable (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℚ)

/-- `z(τ) = c·φ_f(τ) ∈ ℂ`, the parameter of `φ(τ) ∈ ℂ/L`. -/
def zPar (τ : UpperHalfPlane) : ℂ := (c : ℂ) * ZInQ.GZHL3.eichler f τ

/-- `x(φ(τ)) = ℘_L(c φ_f(τ)) − b₂/12` (junk at the poles `c φ_f(τ) ∈ L`). -/
def xPar (τ : UpperHalfPlane) : ℂ := L.weierstrassP (zPar f c τ) - (E⁄ℂ).b₂ / 12

/-- `y(φ(τ)) = (℘'_L(c φ_f(τ)) − a₁x − a₃)/2`. -/
def yPar (τ : UpperHalfPlane) : ℂ :=
  (L.derivWeierstrassP (zPar f c τ) - (E⁄ℂ).a₁ * xPar E L f c τ - (E⁄ℂ).a₃) / 2

open Classical in
/-- `1/(x(φ(τ)) − t)`, `0` at the poles of `x∘φ`. -/
def gPar (t : ℚ) (τ : UpperHalfPlane) : ℂ :=
  if zPar f c τ ∈ L.lattice then 0 else (xPar E L f c τ - t)⁻¹

end Param

/-- The hypotheses shared by the analytic glue: `E/ℚ` with the L-series of the newform `f` of
level `N`, trivial character, `L` the period lattice of `E`, `c ∈ ℚ^×` with `c Λ_f ⊆ L`. -/
def ParamSetting (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) : Prop :=
  f.χ = 1 ∧ (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) ∧
    ZInQ.GZHL3.IsPeriodLattice E L ∧ c ≠ 0 ∧ ZInQ.GZHL3.PeriodsIn f c L

/-- **(GLUE, analysis) Meromorphy and regularity of the coordinates of `φ`.** `x∘φ`, `y∘φ` and
`1/(x∘φ − t)` are meromorphic on `ℍ`; `x∘φ`, `y∘φ` are regular where `c φ_f(τ) ∉ L`, and
`1/(x∘φ − t)` (value `0` at the poles of `x∘φ`) is regular where `c φ_f(τ) ∈ L` or `x(φ(τ)) ≠ t`.
Content: `φ_f` is holomorphic on `ℍ` (Hecke's bound `aₙ(f) = O(n)`; Mathlib
`ModularForms/Bounds.lean`), `℘_L` is holomorphic off `L` with a double pole at each point of `L`
(Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). -/
def ParamRegular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    (∀ τ : UpperHalfPlane, MeromorphicAt (xPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      MeromorphicAt (yPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      ∀ t : ℚ, MeromorphicAt (gPar E L f c t ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
    (∀ τ : UpperHalfPlane, zPar f c τ ∉ L.lattice →
      RegularAt (xPar E L f c) τ ∧ RegularAt (yPar E L f c) τ) ∧
    (∀ (t : ℚ) (τ : UpperHalfPlane), (zPar f c τ ∈ L.lattice ∨ xPar E L f c τ ≠ t) →
      RegularAt (gPar E L f c t) τ)

/-- **(GLUE, analysis) Moderate growth of the coordinates of `φ` at every cusp.** For
`γ ∈ SL₂(ℤ)`, `x(φ(γτ))`, `y(φ(γτ))`, `1/(x(φ(γτ)) − t)` are `O(e^{2πk Im τ})` as `Im τ → ∞`.
Content: `f|γ` is a cusp form for `γ⁻¹Γ₀(N)γ`, so `φ_f(γτ) → φ_f(γ∞)` exponentially fast with a
`q^{1/h}`-expansion, and `℘_L` has at most a double pole there. -/
def ParamCuspGrowth : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c → ∀ γ : SL(2, ℤ), ∃ k : ℕ,
    (fun τ : UpperHalfPlane => xPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
    (fun τ : UpperHalfPlane => yPar E L f c (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
    ∀ t : ℚ, (fun τ : UpperHalfPlane => gPar E L f c t (γ • τ)) =O[UpperHalfPlane.atImInfty]
        (fun τ => Real.exp (2 * Real.pi * k * τ.im))

/-- A rational Laurent expansion in `q = e^{2πiτ}` valid for `Im τ > T`. -/
def HasRatQExp (g : UpperHalfPlane → ℂ) : Prop :=
  ∃ (k : ℕ) (a : ℕ → ℚ) (T : ℝ), ∀ τ : UpperHalfPlane, T < τ.im →
    HasSum (fun n : ℕ => (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
      (Complex.exp (2 * Real.pi * Complex.I * τ) ^ k * g τ)

/-- **(GLUE, analysis) Rational `q`-expansions of the coordinates of `φ`.** Near `∞`,
`c φ_f(τ) = c q + …` has rational coefficients (`aₙ(f) = aₙ(E) ∈ ℤ`, `c ∈ ℚ`), and the Laurent
expansion of `℘_L` at `0` has coefficients in `ℚ[g₂, g₃] = ℚ` (`g₂ = c₄/12`, `g₃ = c₆/216`), so
`x∘φ = c⁻²q⁻² + …`, `y∘φ`, `1/(x∘φ − t)` are Laurent series in `q` with rational coefficients. -/
def ParamQExpansion : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    HasRatQExp (xPar E L f c) ∧ HasRatQExp (yPar E L f c) ∧ ∀ t : ℚ, HasRatQExp (gPar E L f c t)

/-! ## §4. The class-group glue -/

open TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField

/-- **(GLUE, algebraic number theory) Every ideal class of `ℚ(√−m)`, `m ≡ 3 (mod 4)`
squarefree, contains an ideal `J = ⟨a, (−b + √−m)/2⟩` with `a` prime to a given `M`.** (E.g. a
prime of degree one not dividing `M`, by Tau Ceti's Chebotarev theorem, as in the kernel's
`RingClassTwo.exists_prime_picClass_eq`; or: every class contains an integral ideal prime to `M`,
whose primitive part has the Hermite basis `⟨a, (−b + √D)/2⟩`.) -/
def HeegnerClassJ : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → ∀ M : ℤ, M ≠ 0 →
    ∀ cl : Pic (conductorOrder (QNeg m) 1),
    ∃ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) 1).conductorModulus) (a b : ℤ),
      (conductorOrder (QNeg m) 1).picClass J = cl ∧ 0 < a ∧ 4 * a ∣ b ^ 2 - (-(m : ℤ)) ∧
      IsCoprime a M ∧ idealLat m 1 J = jLat (-(m : ℤ)) a b

/-! ## §5. Glue: Galois theory of `ℂ`, periodicity, the coordinates in `ℚ(X₀(N))` -/

/-- **`σ ∈ Aut(ℂ)` restricts to `ℚ̄`** (through `ιC`). -/
theorem exists_galQ_of_sigma (σ : ℂ ≃+* ℂ) : ∃ ρ : GalQ, ∀ a : Qbar, σ (ιC a) = ιC (ρ a) := by
  letI : Algebra Qbar ℂ := ιC.toAlgebra
  have hst : IsScalarTower ℚ Qbar ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp [RingHom.algebraMap_toAlgebra]
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Qbar, ιC y = z := by
    intro z hz
    have hz' : IsAlgebraic Qbar z := hz.extendScalars (algebraMap ℚ Qbar).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ (φ : ℂ ≃+* ℂ) (x : Qbar), IsAlgebraic ℚ (φ (ιC x)) := by
    intro φ x
    have h1 : IsAlgebraic ℚ (ιCA x) := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom ιCA
    exact h1.algHom ((φ : ℂ →+* ℂ).toRatAlgHom)
  choose ρf hρf using fun x => hrange (σ (ιC x)) (halg σ x)
  choose ρi hρi using fun x => hrange (σ.symm (ιC x)) (halg σ.symm x)
  have hinj : Function.Injective ιC := ιC.injective
  let ρh : Qbar →+* Qbar :=
    { toFun := ρf
      map_one' := hinj (by rw [hρf]; simp)
      map_mul' := fun x y => hinj (by rw [hρf, map_mul, map_mul, map_mul, hρf, hρf])
      map_zero' := hinj (by rw [hρf]; simp)
      map_add' := fun x y => hinj (by rw [hρf, map_add, map_add, map_add, hρf, hρf]) }
  have hbij : Function.Bijective ρh := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨ρi y, ?_⟩⟩
    · have h := congrArg ιC hxy
      change ιC (ρf x) = ιC (ρf y) at h
      rw [hρf, hρf] at h
      exact hinj (σ.injective h)
    · apply hinj
      change ιC (ρf (ρi y)) = ιC y
      rw [hρf, hρi, RingEquiv.apply_symm_apply]
  exact ⟨AlgEquiv.ofBijective ρh.toRatAlgHom hbij, fun x => (hρf x).symm⟩

/-- **The fixed field of `Aut(ℂ/κ(K))` is `κ(K)`**, `K = ℚ(√−m)`. -/
theorem mem_kappa_of_fixed {m : ℕ} [NeZero m] (z : ℂ)
    (hz : ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) → σ z = z) :
    ∃ k : QNeg m, kappa m k = z := by
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  let ε : SeparableClosure (QNeg m) →+* ℂ := ιC.comp e.toRingHom
  have hK : ∀ k : QNeg m, ε (algebraMap (QNeg m) (SeparableClosure (QNeg m)) k) = kappa m k :=
    fun k => T5Glue.kappa_eq_of_normalized e he k
  obtain ⟨a, ha⟩ := T5Glue.fixedAlgebraic z (fun σ hσ => hz σ (fun k => by
    rw [← hK k]; exact hσ _))
  letI : Algebra (SeparableClosure (QNeg m)) ℂ := ε.toAlgebra
  have hst : IsScalarTower ℚ (SeparableClosure (QNeg m)) ℂ :=
    IsScalarTower.of_algebraMap_eq fun q => by simp [RingHom.algebraMap_toAlgebra]
  have hzalg : IsAlgebraic ℚ z := by
    rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom ιCA
  obtain ⟨b, hb⟩ := T5Glue.mem_range_of_isAlgebraic
    (hzalg.extendScalars (algebraMap ℚ (SeparableClosure (QNeg m))).injective)
  have hb' : ε b = z := hb
  have hfix : ∀ τ : SeparableClosure (QNeg m) ≃ₐ[QNeg m] SeparableClosure (QNeg m), τ b = b := by
    intro τ
    obtain ⟨σ, hσ⟩ := T5Glue.exists_ringEquiv_extend ε τ.toRingEquiv
    have hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k := fun k => by
      rw [← hK k, hσ]; simp
    have h1 := hz σ hσK
    rw [← hb', hσ] at h1
    exact ε.injective h1
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed b).2 hfix
  exact ⟨k, by rw [← hK, hk, hb']⟩

theorem weierPt_eq_zero (E : WeierstrassCurve ℚ) (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    ZInQ.GZHL3.weierPt E L z = 0 := by
  unfold ZInQ.GZHL3.weierPt
  rw [dif_neg (fun h => h.1 hz)]

theorem weierPt_eq_some (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) {z : ℂ} (hz : z ∉ L.lattice) :
    ZInQ.GZHL3.weierPt E L z = .some _ _ (ZInQ.GZHL3.weierPt_some E hL hz) := by
  unfold ZInQ.GZHL3.weierPt
  rw [dif_pos ⟨hz, ZInQ.GZHL3.weierPt_some E hL hz⟩]

/-- `weierPt E L` is `L`-periodic. -/
theorem weierPt_add (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : ZInQ.GZHL3.weierPt E L (z + l) = ZInQ.GZHL3.weierPt E L z := by
  have h1 : L.weierstrassP (z + l) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨l, hl⟩
  have h2 : L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  by_cases hz : z ∈ L.lattice
  · rw [weierPt_eq_zero E L hz, weierPt_eq_zero E L (L.lattice.add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h hl)
    rw [weierPt_eq_some E hL hz, weierPt_eq_some E hL hzl]
    simp only [Affine.Point.some.injEq, h1, h2, and_self]

section Inv

variable {E : WeierstrassCurve ℚ} {L : PeriodPair} {N : ℕ} [NeZero N] {f : Newform N 2} {c : ℚ}

theorem zPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    ∃ l ∈ L.lattice, zPar f c (γ • τ) = zPar f c τ + l :=
  ⟨_, hP γ hγ τ, by simp only [zPar]; ring⟩

theorem xPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    xPar E L f c (γ • τ) = xPar E L f c τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  simp only [xPar, e, L.weierstrassP_add_coe _ ⟨l, hl⟩]

theorem yPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    yPar E L f c (γ • τ) = yPar E L f c τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  simp only [yPar, xPar_smul hP hγ τ, e, L.derivWeierstrassP_add_coe _ ⟨l, hl⟩]

theorem gPar_smul (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (t : ℚ) (τ : UpperHalfPlane) :
    gPar E L f c t (γ • τ) = gPar E L f c t τ := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  have h3 : zPar f c τ + l ∈ L.lattice ↔ zPar f c τ ∈ L.lattice :=
    ⟨fun h => by simpa using L.lattice.sub_mem h hl, fun h => L.lattice.add_mem h hl⟩
  unfold gPar
  rw [xPar_smul hP hγ τ]
  by_cases h : zPar f c τ ∈ L.lattice
  · rw [if_pos (by rw [e]; exact h3.2 h), if_pos h]
  · rw [if_neg (by rw [e]; exact fun h' => h (h3.1 h')), if_neg h]

theorem weierPt_smul [E.IsElliptic] (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (hP : ZInQ.GZHL3.PeriodsIn f c L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    ZInQ.GZHL3.weierPt E L (zPar f c (γ • τ)) = ZInQ.GZHL3.weierPt E L (zPar f c τ) := by
  obtain ⟨l, hl, e⟩ := zPar_smul hP hγ τ
  rw [e, weierPt_add E hL _ hl]

end Inv

/-- **The coordinates of `φ` lie in `ℚ(X₀(N))`** (from the three analytic glue Props; the
`Γ₀(N)`-invariance is proved here from `c Λ_f ⊆ L`). -/
theorem isRatModFnMero_coords (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) :
    IsRatModFnMero N (xPar E L f c) ∧ IsRatModFnMero N (yPar E L f c) ∧
      ∀ t : ℚ, IsRatModFnMero N (gPar E L f c t) := by
  obtain ⟨hmer, -, -⟩ := hR E N f L c hs
  obtain ⟨qx, qy, qg⟩ := hQ E N f L c hs
  have hP := hs.2.2.2.2
  refine ⟨⟨fun γ hγ τ => xPar_smul hP hγ τ, fun τ => (hmer τ).1, fun γ => ?_, qx⟩,
    ⟨fun γ hγ τ => yPar_smul hP hγ τ, fun τ => (hmer τ).2.1, fun γ => ?_, qy⟩,
    fun t => ⟨fun γ hγ τ => gPar_smul hP hγ t τ, fun τ => (hmer τ).2.2 t, fun γ => ?_, qg t⟩⟩
  · obtain ⟨k, hk, -, -⟩ := hG E N f L c hs γ; exact ⟨k, hk⟩
  · obtain ⟨k, -, hk, -⟩ := hG E N f L c hs γ; exact ⟨k, hk⟩
  · obtain ⟨k, -, -, hk⟩ := hG E N f L c hs γ; exact ⟨k, hk t⟩

/-- `σ` as a `ℚ`-algebra map. -/
abbrev sigA (σ : ℂ ≃+* ℂ) : ℂ →ₐ[ℚ] ℂ := (σ : ℂ →+* ℂ).toRatAlgHom

/-- **Galois transport of a point of the modular parametrization.** If `σ(g(τ)) = g(τ')` for every
`g ∈ ℚ(X₀(N))` regular at `τ` and `τ'`, then `σ(φ(τ)) = φ(τ')` in `E(ℂ)`. -/
theorem point_transport (hR : ParamRegular) (hG : ParamCuspGrowth) (hQ : ParamQExpansion)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane)
    (hσ : ∀ g, IsRatModFnMero N g → RegularAt g τ → RegularAt g τ' → σ (g τ) = g τ') :
    Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c τ)) =
      ZInQ.GZHL3.weierPt E L (zPar f c τ') := by
  obtain ⟨-, hreg, hgreg⟩ := hR E N f L c hs
  obtain ⟨mx, my, mg⟩ := isRatModFnMero_coords hR hG hQ E f L c hs
  have hL := hs.2.2.1
  -- a value `t ∈ {0, 1}` avoiding a given complex number
  have avoid : ∀ w : ℂ, ∃ t : ℚ, w ≠ t := fun w => by
    by_cases h : w = ((0 : ℚ) : ℂ)
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨0, h⟩
  by_cases hz : zPar f c τ ∈ L.lattice <;> by_cases hz' : zPar f c τ' ∈ L.lattice
  · rw [weierPt_eq_zero E L hz, weierPt_eq_zero E L hz', map_zero]
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ')
    have h := hσ _ (mg t) (hgreg t τ (Or.inl hz)) (hgreg t τ' (Or.inr ht))
    simp only [gPar, hz, hz', ite_true, ite_false, map_zero] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h.symm
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ)
    have h := hσ _ (mg t) (hgreg t τ (Or.inr ht)) (hgreg t τ' (Or.inl hz'))
    simp only [gPar, hz, hz', ite_true, ite_false, map_eq_zero_iff _ σ.injective] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h
  · have hx := hσ _ mx (hreg τ hz).1 (hreg τ' hz').1
    have hy := hσ _ my (hreg τ hz).2 (hreg τ' hz').2
    rw [weierPt_eq_some E hL hz, weierPt_eq_some E hL hz', Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

end ZInQ.GZHeegner

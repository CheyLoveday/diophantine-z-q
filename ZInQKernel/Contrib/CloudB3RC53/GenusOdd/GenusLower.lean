import ZInQKernel.Contrib.CloudB3RC53.Prints
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Elliot
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Arith

/-!
# GenusOdd: Proposition `ex:sec7-genus-lower`, identity (3.4) (tex L2403–2439)

**Known issue K3** (`docs/research/mcheck-rc-app.md`, section K3): (3.4) needs Cai–Shu–Tian
Theorem 1.1 in a form whose conductor factor is `c √|disc K|` with no other dependence on `c` or
`K`, with the unaveraged sum and the height relative to `K`. That form is exactly the printed leaf
`Prints.cst` (`CST.CSTThm11Split`), stated UNVERIFIED (pending reading) in `Prints/CST.lean`; it is
used here as stated and is **not** reconstructed or re-proved (ruling recorded in the RC53 notes).
No Gross–Zagier argument of our own enters.

## The objects (tex L2403–2415)

For a positive squarefree `h` in the prepared filter containing one (`Prepared`), a fixed negative
genus partner `h_*` (`GenusPartner`) and a rough companion `k'` (`Companion`):

* the genus point `P_h^gen`: the unaveraged conductor-one genus sum over `ℚ(√(h h_*))`, weighted by
  `χ_{h_*}(N𝔞)` ((O.1), tex L8212–8215): `heegnerSum` of a `HeegnerDatum` with `D = h h_*`,
  `c = 1`, `d₁ = h_*`;
* the ring-class point `P_{h,k'}^rc`: the unaveraged conductor-`|h|` sum over `ℚ(√k')` weighted by
  `χ_h`: `heegnerSum` of a `HeegnerDatum` with `D = k'`, `c = |h|`, `d₁ = h`;
* `j_gen(h)`, `j_rc(h, k')`: their index valuations in their native lattices (`twoDivIndex` in
  `eigenLattice`).

A `HeegnerDatum` carries the field, the character, a Heegner form, an embedding `ι : H_c → ℂ` and a
point `y ∈ E(H_c)` with `ι(y) = φ(τ)`: the complex-analytic model of `Prints/CST.lean` (the algebraic
Heegner point on `X₀(N)` is not available). `jgenOf`, `jrcOf` read the index off a selection of
data (one datum per `h`, resp. `(h, k')`).

## The proof (tex L2427–2439)

PRINT `Prints.cst` twice (common constant `C`: "the parametrization is the same"), PRINT
`Prints.kolyvagin` and `Prints.bcdt` (ranks of `E^{(h)}`, `E^{(h_*)}`, `E^{(hk')}`), the GLUE of
`Glue.lean`, and Elliot's index-at-most-two comparison (PROVED, `Elliot.lean`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

section Data

variable (E : WeierstrassCurve ℚ)
  (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
  (Lat : PeriodPair) (κ : ℂ)

-- `open Classical` exactly as in `CST.CSTThm11Split`, so that `hy` is CST's hypothesis verbatim.
open Classical in
/-- **A Heegner datum** for discriminant `D`, conductor `c` and character `χ = χ_{d₁} ∘ N`: an
imaginary quadratic field `K` of discriminant `D`, a primitive quadratic ring class character of
conductor `c` equal to `χ_{d₁} ∘ N`, a Heegner form `[A, B, C]` of level `N` and discriminant
`D c²`, an embedding `ι : H_c → ℂ` and a point `y ∈ E(H_c)` with `ι(y) = φ(τ_{[A,B,C]})` (the
analytic model of the Heegner point, `Prints/CST.lean`). -/
structure HeegnerDatum (D : ℤ) (c : ℕ) (d₁ : ℤ) where
  K : Type
  [field : Field K]
  [nf : NumberField K]
  [nz : NeZero c]
  finrank_two : Module.finrank ℚ K = 2
  totallyComplex : IsTotallyComplex K
  disc : discr K = D
  χ : Pic (conductorOrder K c) →* ℂˣ
  quad : IsQuadRingClassChar K c d₁ χ
  prim : IsPrimitiveRingClassChar K c χ
  A : ℤ
  B : ℤ
  C : ℤ
  form : IsHeegnerForm (newformLevel E) (D * c ^ 2) A B C
  ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ
  y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point
  hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
    phiAn E f Lat κ (cmPoint A B (D * c ^ 2))

variable {E f Lat κ}

/-- The index valuation of `P_χ` in its native lattice (`j` of tex L2415). -/
def nativeIndex (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
    (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point) : ℕ∞ :=
  letI := Classical.decEq (ringClassField (conductorOrder K c))
  twoDivIndex (eigenLattice E χ) (heegnerSum E χ y)

/-- The index valuation of the datum's unaveraged Heegner sum in its native lattice. -/
def HeegnerDatum.index {D : ℤ} {c : ℕ} {d₁ : ℤ} (dat : HeegnerDatum E f Lat κ D c d₁) : ℕ∞ :=
  letI := dat.field; letI := dat.nf; letI := dat.nz
  nativeIndex E dat.χ dat.y

variable (E f Lat κ)

/-- **`j_gen(h)`** (tex L2411–2415) read off a selection of genus data (`D = h h_*`, `c = 1`,
`χ = χ_{h_*} ∘ N`); `0` where no datum is selected. -/
def jgenOf (hstar : ℤ) (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (h : ℤ) : ℤ :=
  match selG h with
  | some dat => (dat.index.toNat : ℤ)
  | none => 0

/-- **`j_rc(h, k')`** (tex L2411–2415) read off a selection of ring-class data (`D = k'`,
`c = |h|`, `χ = χ_h ∘ N`); `0` where no datum is selected. -/
def jrcOf (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h)) (h k : ℤ) : ℤ :=
  match selR h k with
  | some dat => (dat.index.toNat : ℤ)
  | none => 0

end Data

/-! ### The parameters of (3.4) -/

/-- **The prepared positive filter containing one** (tex L2404–2410, L2343–2346): `h` positive,
squarefree, a unit square at every prime of `2N` (the squareclasses of one), prime to `h_*` (the
fixed support includes `h_*`, tex L2407–2408). -/
def Prepared (E : WeierstrassCurve ℚ) (hstar h : ℤ) : Prop :=
  0 < h ∧ Squarefree h ∧ (∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p h) ∧
    IsCoprime h hstar

/-- **The negative genus partner** (tex L2403–2406): `h_*` a negative odd fundamental
discriminant (`≡ 1 mod 4`, squarefree) with `|h_*| > 4`, in the squareclasses of one at `2N`, and
`L(E^{(h_*)}, 1) ≠ 0`. -/
def GenusPartner (E : WeierstrassCurve ℚ) (hstar : ℤ) : Prop :=
  hstar < 0 ∧ hstar % 4 = 1 ∧ Squarefree hstar ∧ 4 < |hstar| ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p hstar) ∧
    AnalyticRank (qtwist E hstar) 0

/-- **The rough companion relation** (Proposition `ex:sec7-rough-companion`, tex L2349–2353, with
the primes of `h_*` in the avoidance set, tex L2408–2409): `k'` a negative odd fundamental
discriminant (`≡ 1 mod 4`, squarefree), a unit square at every prime dividing `2Nh` (so it avoids
the extra-unit fields: `k' ≡ 1 mod 8`), prime to `h_*`, with `L_*(hk') ≠ 0`. -/
def Companion (E : WeierstrassCurve ℚ) (Lat : PeriodPair) (hstar h k' : ℤ) : Prop :=
  k' < 0 ∧ k' % 4 = 1 ∧ Squarefree k' ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * newformLevel E * h → SquareAt p k') ∧
    IsCoprime k' hstar ∧ Lstar E Lat (h * k') ≠ 0

/-! ### One application of Cai–Shu–Tian -/

section Core

open Classical in
/-- The conclusion of `CST.CSTThm11Split` for fixed `(E, f, Lat, κ)` and constant `C` (verbatim). -/
def CSTFormula (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    discr K ≠ -3 → discr K ≠ -4 →
    (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p) →
    ∀ (c : ℕ) [NeZero c], Nat.Coprime c (newformLevel E) →
    ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsPrimitiveRingClassChar K c χ →
    ∀ A B C' : ℤ, IsHeegnerForm (newformLevel E) (discr K * c ^ 2) A B C' →
    ∀ ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ,
    ∀ y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (discr K * c ^ 2)) →
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (twistedLFunction E (chiAt (conductorOrder K c) χ)) s) →
      deriv F 1 = ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) * heightK E K c χ y

theorem cst_formula (P : Prints) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) (κ : ℂ)
    (hκ : IsParamScale (newformLevel E) f Lat κ) : ∃ C : ℝ, 0 < C ∧ CSTFormula E f Lat κ C :=
  P.cst E f hf Lat hLat hNC κ hκ

theorem splits_of_squareAt (G : Glue34) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {N : ℕ} (h : ∀ p : ℕ, p.Prime → p ∣ N → SquareAt p (discr K)) :
    ∀ p : ℕ, p.Prime → p ∣ N → SplitsIn K p :=
  fun p hp hpN => G.split K hK p hp (h p hp hpN)

theorem coprime_of_squareAt {N : ℕ} {d : ℤ} (h : ∀ p : ℕ, p.Prime → p ∣ N → SquareAt p d) :
    Nat.Coprime d.natAbs N := by
  refine Nat.coprime_of_dvd fun p hp hpd hpN => (h p hp hpN).1 ?_
  exact Int.natCast_dvd.mpr hpd

open Classical in
/-- **One application of Cai–Shu–Tian, with Elliot's comparison** (PROVED from `Prints.cst` and the
GLUE). For a field `K` of discriminant `D`, `χ = χ_{d₁} ∘ N` on `Pic(O_c)`, `d₁ d₂ = D c²`, a Heegner
point `y` and entire continuations `F₁, F₂` of `L(E^{(d₁)}, s)`, `L(E^{(d₂)}, s)`: if `E^{(d_T)}(ℚ)` is
torsion for the one of `d₁, d₂` called `d_T`, there is `Q` on the rational line `E^{(d_R)}(ℚ)` (the
other one) with `(F₁F₂)'(1) = C/(c√|D|) · ĥ(Q)/2` and `j(P_χ) ≤ j(Q) ≤ j(P_χ) + 1`. -/
theorem datum_facts_core (G : Glue34) {E : WeierstrassCurve ℚ} [E.IsElliptic] (h₁ : E.a₁ = 0)
    (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {C : ℝ} (hC : CSTFormula E f Lat κ C)
    {D : ℤ} {c : ℕ} {d₁ d₂ dR dT : ℤ} (K : Type) [Field K] [NumberField K] [NeZero c]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = D)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c d₁ χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (D * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (D * c ^ 2)))
    (hprod : d₁ * d₂ = D * c ^ 2) (hd₁ : d₁ % 4 = 1) (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁)
    (hcD : Nat.Coprime c D.natAbs) (hDodd : Odd D) (hD3 : D ≠ -3) (hD4 : D ≠ -4)
    (hDN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p D)
    (hcN : Nat.Coprime c (newformLevel E)) (hdN : Nat.Coprime (d₁ * d₂).natAbs (newformLevel E))
    (hRT : (dR = d₁ ∧ dT = d₂) ∨ (dR = d₂ ∧ dT = d₁))
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P)
    {F₁ F₂ : ℂ → ℂ} (hF₁ : IsLContinuation (qtwist E d₁) F₁)
    (hF₂ : IsLContinuation (qtwist E d₂) F₂) :
    ∃ Q : (qtwist E dR).toAffine.Point,
      deriv (fun s => F₁ s * F₂ s) 1 =
        ((C / ((c : ℝ) * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ) * ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
      nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
  subst hdisc
  let _ : DecidableEq (ringClassField (conductorOrder K c)) :=
    Classical.decEq (ringClassField (conductorOrder K c))
  -- genus theory: `√d₁, √d₂ ∈ H_c` and complex conjugation
  obtain ⟨hgal, s₁, s₂, hs₁, hs₂, hσ, ρ, hρ⟩ := G.genus K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq
    hcd hcD χ hquad
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; norm_num at hd₁
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hprod
    have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
    have hD0 : discr K ≠ 0 := by rintro h; rw [h] at hDodd; norm_num at hDodd
    exact (mul_ne_zero hD0 (pow_ne_zero 2 hc0)) hprod.symm
  have _ := hgal
  have hsplit := splits_of_squareAt G hK2 hDN
  -- Cai–Shu–Tian at this datum
  have hCST := hC K hK2 hTC hD3 hD4 hsplit c hcN χ hprim A B C' hform ι y hy
    (fun s => F₁ s * F₂ s) (hF₁.1.mul hF₂.1) (fun s hs => by
      rw [hF₁.2 s hs, hF₂.2 s hs]
      exact (G.artin E K hK2 hTC hDodd hsplit c d₁ d₂ hprod hd₁ hsq hcd hcD hdN χ hquad s hs).symm)
  rw [heightK_eq_canonicalHeight E hquad.1 y] at hCST
  have hP : heegnerSum E χ y ∈ eigenLattice E χ := heegnerSum_mem_eigenLattice E hquad.1 y
  have hn : 0 < Module.finrank K (ringClassField (conductorOrder K c)) := Module.finrank_pos
  have htower : Module.finrank ℚ (ringClassField (conductorOrder K c)) =
      2 * Module.finrank K (ringClassField (conductorOrder K c)) := by
    rw [← Module.finrank_mul_finrank ℚ K, hK2]
  have finish : ∀ (dR' dT' : ℤ) (sR sT : ringClassField (conductorOrder K c)),
      sR ^ 2 = (dR' : ringClassField (conductorOrder K c)) →
      sT ^ 2 = (dT' : ringClassField (conductorOrder K c)) → dR' ≠ 0 → dT' ≠ 0 →
      (∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
        σ sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sR ∧
        σ sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sT) →
      ((ρ sR = sR ∧ ρ sT = -sT) ∨ (ρ sR = -sR ∧ ρ sT = sT)) →
      (∀ P : (qtwist E dT').toAffine.Point, IsOfFinAddOrder P) →
      ∃ Q : (qtwist E dR').toAffine.Point,
        deriv (fun s => F₁ s * F₂ s) 1 =
          ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) *
            ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
        nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
    intro dR' dT' sR sT hsR hsT hdR hdT hσ' hρ' htor'
    have hcast : ∀ d : ℤ, ((d : ringClassField (conductorOrder K c))) =
        algebraMap ℚ (ringClassField (conductorOrder K c)) (d : ℚ) := fun d => by
      rw [map_intCast]
    have hne : ∀ {d : ℤ} {s : ringClassField (conductorOrder K c)},
        s ^ 2 = (d : ringClassField (conductorOrder K c)) → d ≠ 0 → s ≠ 0 := by
      intro d s hs hd h0
      rw [h0] at hs
      have : ((d : ringClassField (conductorOrder K c))) = 0 := by rw [← hs]; ring
      exact hd (by exact_mod_cast this)
    have hsR0 := hne hsR hdR
    have hsT0 := hne hsT hdT
    have hsRd : sR ^ 2 = algebraMap ℚ _ (dR' : ℚ) := by rw [hsR, hcast]
    have hsTd : sT ^ 2 = algebraMap ℚ _ (dT' : ℚ) := by rw [hsT, hcast]
    have helliot := two_nsmul_mem_twist_add_torsion E G.descent h₁ h₃ hK2 hsR0 hsRd hsT0 hsTd
      hσ' ρ hρ' htor'
    obtain ⟨Q, hQ⟩ := helliot _ hP
    refine ⟨Q, ?_, ?_⟩
    · have hsqH : ∀ (m : ℕ) (x : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point),
          ((m • x).canonicalHeight) = (m : ℝ) ^ 2 * x.canonicalHeight :=
        fun m x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul m x
      have h2P := height_add_torsion hsqH
        (twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) Q) _ hQ
      rw [add_sub_cancel, hsqH, G.height E h₁ h₃ (dR' : ℚ) _ sR hsR0 hsRd Q, htower] at h2P
      have hn' : (Module.finrank K (ringClassField (conductorOrder K c)) : ℝ) ≠ 0 := by
        exact_mod_cast hn.ne'
      push_cast at h2P
      have key : ((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ))⁻¹ *
          (heegnerSum E χ y).canonicalHeight = Q.canonicalHeight / 2 := by
        rw [show (heegnerSum E χ y).canonicalHeight = 2 * (Module.finrank K
            (ringClassField (conductorOrder K c)) : ℝ) * Q.canonicalHeight / 4 by linarith]
        field_simp
        ring
      rw [hCST, key]
    · have hψM : ∀ r, twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) r ∈ eigenLattice E χ := by
        intro r σ
        have hsRne : sR ≠ -sR := fun h => hsR0 (by
          have : (2 : ringClassField (conductorOrder K c)) * sR = 0 := by linear_combination h
          simpa using this)
        have hcs : chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = 1 ∨
            chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = -1 := by
          unfold chiSign; split_ifs <;> simp
        have hs := (hσ' σ).1
        show galPt E σ _ = _
        rcases hcs with h | h
        · rw [h] at hs
          have hσs : σ sR = sR := by rw [hs]; simp
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inl hσs) r, if_pos (by exact hσs), h, one_smul]
        · rw [h] at hs
          have hσs : σ sR = -sR := by rw [hs]; simp
          have hσs' : ¬ σ sR = sR := fun h' => hsRne (h'.symm.trans hσs)
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inr hσs) r, if_neg (by exact hσs'), h, neg_smul, one_smul]
      have := twoDivIndex_transfer _ (twistEmb_injective E (dR' : ℚ) sR _) (eigenLattice E χ) hψM
        helliot hP hQ
      exact this
  rcases hRT with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1 e2
    exact finish _ _ s₁ s₂ hs₁ hs₂ hd₁0 hd₂0 hσ hρ htorT
  · subst e1 e2
    refine finish _ _ s₂ s₁ hs₂ hs₁ hd₂0 hd₁0 (fun σ => ⟨(hσ σ).2, (hσ σ).1⟩) ?_ htorT
    rcases hρ with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
    · exact Or.inl ⟨b, a⟩

end Core

end ZInQ.Contrib.CloudB3RC53.GenusOdd

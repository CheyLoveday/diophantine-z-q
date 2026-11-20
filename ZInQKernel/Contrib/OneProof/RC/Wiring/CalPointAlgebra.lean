import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointFreeLine
import ZInQKernel.Contrib.OneProof.RC.Height.SumDifference
import ZInQKernel.Contrib.CloudB3RC53.Calibration.Bookkeeping
import ZInQKernel.Contrib.CloudB3RC53.Calibration.Lengths

/-!
# Theorem 5.3, Lane RC34: the free-line algebra of the point half of the calibration

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, tex 3895–3986) and the proof of
Proposition `ex:arith-central-calibration` (tex 4005–4021, 4057–4064):

> "On a rank-one Mordell–Weil free lattice, both free-line coefficients consequently have
> valuation `j_rc(h,k) + v₂(Lm)`." (tex 3905–3907)
>
> "On the integral rank-one Mordell–Weil free lattice, the central conjugation transport is an
> involutive automorphism (including the quadratic sign), hence acts by `+1` or `−1`. It
> preserves the point index; it need not fix the point. The two free-line coefficients both have
> valuation `j_rc(h,k) + v₂(Lm)`. An orientation sign is a fixed unit; there is no independently
> chosen scalar multiplying the functional." (tex 3977–3982)
>
> "Self-duality identifies the degree-three torsion with the degree-one torsion and gives a
> unimodular pairing of the free degree-one and degree-two parts." (tex 4015–4017)

This file proves the algebra behind these sentences, for abstract modules.

* `freeCoeff hg z`: the coefficient of `z` on a free-line generator `g` (modulo torsion), with
  its additivity, `R`-linearity and invariance under torsion; `freeCoeff_change`: changing the
  generator multiplies coefficients by a unit (`IsFreeLineGenerator.isUnit_freeCoeff`).
* `IsFreeLineGenerator.map_linearEquiv`: an isomorphism carries free-line generators to
  free-line generators; `freeCoeff_map_endo`: an endomorphism multiplies free coefficients by
  the coefficient of the image of the generator; `freeCoeff_involution`: an involutive
  endomorphism acts on the free line by `+1` or `−1` (tex 3977–3979).
* `functional_apply`, `pairing_apply`: a linear functional (a paired functional `PD(g₂, −)`)
  kills torsion and is determined on the free line by its value on the generator.
* `exists_isFreeLineGenerator`: a finitely generated module of rank one over a principal ideal
  domain has a free-line generator.
* `IsIndexValuation P j` (definition of `j_rc`, tex 2411–2416: the index valuation of a point
  in its native rank-one lattice): `P ≡ n g` modulo torsion for a free generator `g` and
  `v₂ n = j`; `IsIndexValuation.unique`: it does not depend on the generator.
* `freeCoeff_map_zsmul` (the Kummer transfer): if an additive map `κ` from a rank-one group to
  a `ℤ₂`-module carries a free generator to a free-line generator, the free coefficient of
  `κ(k P)` is `k n` for `P ≡ n g`.
* `FreeLinePointData`: the point half of the calibration at one address, abstract form (the
  fixed multiplier `L` with `v₂L = vL`, the point with index valuation `j`, the Kummer
  identification of the free lattice, the conjugate-dual transport, the free generator of the
  degree-two line and the unimodularity of the pairing); the derived central class `κ(LmP)`
  (`zc`), central functional `PD(−, c_K κ(LmP))` and their free coefficients `classCoeff`,
  `funCoeff`; `classCoeff_eq`, `funCoeff_eq`, `v2_classCoeff`, `v2_funCoeff` (both have
  valuation `j + vL + v₂m`); `example` (non-vacuity).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open ZInQ.Manuscript.RC.Height (IsFreeGenerator)

/-! ### Coefficients on a free line -/

section FreeLine

variable {R : Type*} [CommRing R] {H : Type*} [AddCommGroup H] [Module R H] {g : H}

/-- **The coefficient of `z` on the free-line generator `g`**, modulo torsion (tex 3905–3907).
Kind: definition. -/
def freeCoeff (hg : IsFreeLineGenerator R g) (z : H) : R := (hg.2 z).choose

/-- `z − (freeCoeff z) • g` is torsion. PROVED. -/
theorem freeCoeff_spec (hg : IsFreeLineGenerator R g) (z : H) :
    z - freeCoeff hg z • g ∈ Submodule.torsion R H :=
  (hg.2 z).choose_spec

/-- The free coefficient is characterized by `z − c • g` torsion. PROVED. -/
theorem freeCoeff_eq_of (hg : IsFreeLineGenerator R g) {z : H} {c : R}
    (h : z - c • g ∈ Submodule.torsion R H) : freeCoeff hg z = c :=
  hg.coeff_unique (freeCoeff_spec hg z) h

/-- Elements congruent modulo torsion have the same free coefficient. PROVED. -/
theorem freeCoeff_congr (hg : IsFreeLineGenerator R g) {z z' : H}
    (h : z - z' ∈ Submodule.torsion R H) : freeCoeff hg z = freeCoeff hg z' := by
  apply freeCoeff_eq_of hg
  have e : z - freeCoeff hg z' • g = (z - z') + (z' - freeCoeff hg z' • g) := by abel
  rw [e]
  exact Submodule.add_mem _ h (freeCoeff_spec hg z')

/-- A torsion element has free coefficient zero. PROVED. -/
theorem freeCoeff_of_mem_torsion (hg : IsFreeLineGenerator R g) {t : H}
    (ht : t ∈ Submodule.torsion R H) : freeCoeff hg t = 0 :=
  freeCoeff_eq_of hg (by simpa using ht)

/-- The generator has free coefficient one. PROVED. -/
theorem freeCoeff_self (hg : IsFreeLineGenerator R g) : freeCoeff hg g = 1 :=
  freeCoeff_eq_of hg (by simp)

/-- Additivity. PROVED. -/
theorem freeCoeff_add (hg : IsFreeLineGenerator R g) (z z' : H) :
    freeCoeff hg (z + z') = freeCoeff hg z + freeCoeff hg z' := by
  apply freeCoeff_eq_of hg
  have e : z + z' - (freeCoeff hg z + freeCoeff hg z') • g =
      (z - freeCoeff hg z • g) + (z' - freeCoeff hg z' • g) := by
    rw [add_smul]; abel
  rw [e]
  exact Submodule.add_mem _ (freeCoeff_spec hg z) (freeCoeff_spec hg z')

/-- `R`-linearity. PROVED. -/
theorem freeCoeff_smul (hg : IsFreeLineGenerator R g) (r : R) (z : H) :
    freeCoeff hg (r • z) = r * freeCoeff hg z := by
  apply freeCoeff_eq_of hg
  have e : r • z - (r * freeCoeff hg z) • g = r • (z - freeCoeff hg z • g) := by
    rw [smul_sub, smul_smul]
  rw [e]
  exact Submodule.smul_mem _ r (freeCoeff_spec hg z)

/-- The coefficient of `c • g` is `c`. PROVED. -/
theorem freeCoeff_smul_self (hg : IsFreeLineGenerator R g) (c : R) :
    freeCoeff hg (c • g) = c := by
  rw [freeCoeff_smul, freeCoeff_self, mul_one]

/-- **Changing the free-line generator.** The coefficients on `g` are those on `g'` times the
coefficient of `g'` on `g`. PROVED. -/
theorem freeCoeff_change (hg : IsFreeLineGenerator R g) {g' : H}
    (hg' : IsFreeLineGenerator R g') (z : H) :
    freeCoeff hg z = freeCoeff hg' z * freeCoeff hg g' := by
  rw [freeCoeff_congr hg (freeCoeff_spec hg' z), freeCoeff_smul]

/-- **Two free-line generators differ by a unit** (modulo torsion). PROVED. -/
theorem IsFreeLineGenerator.isUnit_freeCoeff (hg : IsFreeLineGenerator R g) {g' : H}
    (hg' : IsFreeLineGenerator R g') : IsUnit (freeCoeff hg g') := by
  have h := freeCoeff_change hg hg' g
  rw [freeCoeff_self] at h
  exact isUnit_iff_exists_inv.mpr ⟨freeCoeff hg' g, by rw [mul_comm]; exact h.symm⟩

/-- A linear map carries torsion into torsion. PROVED. -/
theorem map_mem_torsion {H' : Type*} [AddCommGroup H'] [Module R H'] (f : H →ₗ[R] H')
    {t : H} (ht : t ∈ Submodule.torsion R H) : f t ∈ Submodule.torsion R H' := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff t).1 ht
  refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
  rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, ha, map_zero]

/-- **An isomorphism carries free-line generators to free-line generators.** PROVED. -/
theorem IsFreeLineGenerator.map_linearEquiv {H' : Type*} [AddCommGroup H'] [Module R H']
    (e : H ≃ₗ[R] H') (hg : IsFreeLineGenerator R g) : IsFreeLineGenerator R (e g) := by
  refine ⟨fun r hr => hg.1 r ?_, fun z => ?_⟩
  · have := map_mem_torsion e.symm.toLinearMap hr
    simpa using this
  · refine ⟨freeCoeff hg (e.symm z), ?_⟩
    have h := map_mem_torsion e.toLinearMap (freeCoeff_spec hg (e.symm z))
    simpa using h

/-- **An endomorphism multiplies free coefficients by the coefficient of the image of the
generator.** PROVED. -/
theorem freeCoeff_map_endo (hg : IsFreeLineGenerator R g) (f : H →ₗ[R] H) (z : H) :
    freeCoeff hg (f z) = freeCoeff hg z * freeCoeff hg (f g) := by
  have h := map_mem_torsion f (freeCoeff_spec hg z)
  rw [map_sub, map_smul] at h
  rw [freeCoeff_congr hg h, freeCoeff_smul]

/-- **An involutive endomorphism acts on the free line by `+1` or `−1`** (tex 3977–3979: "the
central conjugation transport is an involutive automorphism …, hence acts by `+1` or `−1`").
PROVED. -/
theorem freeCoeff_involution [IsDomain R] (hg : IsFreeLineGenerator R g) (f : H →ₗ[R] H)
    (hf : ∀ y, f (f y) = y) : freeCoeff hg (f g) = 1 ∨ freeCoeff hg (f g) = -1 := by
  have h := freeCoeff_map_endo hg f (f g)
  rw [hf, freeCoeff_self] at h
  exact mul_self_eq_one_iff.mp h.symm

/-- **A linear functional kills torsion** (the target ring has no torsion). PROVED. -/
theorem functional_torsion (φ : H →ₗ[R] R) {t : H} (ht : t ∈ Submodule.torsion R H) :
    φ t = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff t).1 ht
  have h : (a : R) * φ t = 0 := by
    rw [← smul_eq_mul, ← map_smul, Submonoid.smul_def] at *
    rw [ha, map_zero]
  exact (mem_nonZeroDivisors_iff.mp a.2).1 (φ t) h

/-- **A linear functional is determined on the free line by its value on the generator.**
PROVED. -/
theorem functional_apply (φ : H →ₗ[R] R) (hg : IsFreeLineGenerator R g) (z : H) :
    φ z = freeCoeff hg z * φ g := by
  have h := functional_torsion φ (freeCoeff_spec hg z)
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  exact h

/-- **The paired functional `PD(g₂, −)` on the free line** (tex 3902, 3976): its value at `y`
is the free coefficient of `y` times its value at the generator. PROVED. -/
theorem pairing_apply {H₂ : Type*} [AddCommGroup H₂] [Module R H₂]
    (PD : H₂ →ₗ[R] H →ₗ[R] R) (hg : IsFreeLineGenerator R g) (g₂ : H₂) (y : H) :
    PD g₂ y = freeCoeff hg y * PD g₂ g := functional_apply (PD g₂) hg y

end FreeLine

/-! ### Existence of free-line generators -/

section Exists

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {H : Type*} [AddCommGroup H] [Module R H]

omit [IsPrincipalIdealRing R] in
/-- The torsion submodule has rank zero. PROVED. -/
theorem finrank_torsion_eq_zero :
    Module.finrank R (Submodule.torsion R H) = 0 := by
  apply Module.finrank_eq_zero_of_rank_eq_zero
  rw [rank_eq_zero_iff]
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
  refine ⟨a, nonZeroDivisors.coe_ne_zero a, ?_⟩
  apply Subtype.ext
  simpa [Submonoid.smul_def] using ha

/-- **A finitely generated module of rank one over a principal ideal domain has a free-line
generator**: `H/H_tors` is free of rank one; lift a basis vector. PROVED. -/
theorem exists_isFreeLineGenerator [Module.Finite R H] (h1 : Module.finrank R H = 1) :
    ∃ g : H, IsFreeLineGenerator R g := by
  set T := Submodule.torsion R H
  have : Module.Free R (H ⧸ T) := Module.free_of_finite_type_torsion_free'
  have hrk : Module.finrank R (H ⧸ T) = 1 := by
    have := Submodule.finrank_quotient_add_finrank T
    rw [finrank_torsion_eq_zero, add_zero, h1] at this
    exact this
  let b := Module.finBasisOfFinrankEq R (H ⧸ T) hrk
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective T (b 0)
  have hsum : ∀ x : H ⧸ T, b.repr x 0 • b 0 = x := fun x => by
    have := b.sum_repr x
    rwa [Fin.sum_univ_one] at this
  refine ⟨g, fun r hr => ?_, fun z => ⟨b.repr (Submodule.Quotient.mk z) 0, ?_⟩⟩
  · have h0 : (Submodule.Quotient.mk (r • g) : H ⧸ T) = 0 :=
      (Submodule.Quotient.mk_eq_zero T).2 hr
    rw [Submodule.Quotient.mk_smul, hg] at h0
    have := congrArg (fun x => b.repr x 0) h0
    simpa using this
  · apply (Submodule.Quotient.mk_eq_zero T).1
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hg, hsum, sub_self]

end Exists

/-! ### The index valuation of a point in its native rank-one lattice -/

section Index

variable {G : Type*} [AddCommGroup G]

/-- **The coefficient on a free generator is unique** (modulo torsion). PROVED. -/
theorem freeGen_coeff_unique {g : G} (hg : IsFreeGenerator g) {P : G} {n n' : ℤ}
    (h : IsOfFinAddOrder (P - n • g)) (h' : IsOfFinAddOrder (P - n' • g)) : n = n' := by
  have hd := ZInQ.Manuscript.RC.Height.isOfFinAddOrder_sub' h' h
  have e : P - n' • g - (P - n • g) = (n - n') • g := by rw [sub_smul]; abel
  rw [e] at hd
  have := ZInQ.Manuscript.RC.Height.eq_zero_of_isOfFinAddOrder_zsmul hg.1 hd
  omega

/-- **Two free generators differ by a sign** modulo torsion. PROVED. -/
theorem freeGen_coeff_sign {g g' : G} (hg : IsFreeGenerator g) (hg' : IsFreeGenerator g')
    {a : ℤ} (ha : IsOfFinAddOrder (g' - a • g)) : a = 1 ∨ a = -1 := by
  obtain ⟨b, hb⟩ := hg'.2 g
  have h1 : IsOfFinAddOrder (g - (b * a) • g) := by
    have e : g - (b * a) • g = (g - b • g') + b • (g' - a • g) := by
      rw [mul_smul, smul_sub]; abel
    rw [e]
    exact hb.add ha.zsmul
  have h0 : IsOfFinAddOrder (g - (1 : ℤ) • g) := by simp
  have hba : b * a = 1 := freeGen_coeff_unique hg h1 h0
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hba)

/-- **The index valuation of a point** (tex 2411–2416: "Write `j_gen(h)` and `j_rc(h,k')` for
their index valuations"): in a rank-one group, `P ≡ n g` modulo torsion for a free generator `g`
with `n ≠ 0`, and `v₂ n = j` (the `2`-adic valuation of the index of `ℤ P` in the free lattice).
Kind: definition. -/
def IsIndexValuation (P : G) (j : ℤ) : Prop :=
  ∃ g : G, ∃ n : ℤ, IsFreeGenerator g ∧ IsOfFinAddOrder (P - n • g) ∧ n ≠ 0 ∧
    ((padicValInt 2 n : ℕ) : ℤ) = j

/-- **The index valuation does not depend on the free generator.** PROVED. -/
theorem IsIndexValuation.unique {P : G} {j j' : ℤ} (h : IsIndexValuation P j)
    (h' : IsIndexValuation P j') : j = j' := by
  obtain ⟨g, n, hg, hn, -, rfl⟩ := h
  obtain ⟨g', n', hg', hn', -, rfl⟩ := h'
  obtain ⟨a, ha⟩ := hg.2 g'
  have hsign := freeGen_coeff_sign hg hg' ha
  have h1 : IsOfFinAddOrder (P - (n' * a) • g) := by
    have e : P - (n' * a) • g = (P - n' • g') + n' • (g' - a • g) := by
      rw [mul_smul, smul_sub]; abel
    rw [e]
    exact hn'.add ha.zsmul
  have hnn : n = n' * a := freeGen_coeff_unique hg hn h1
  subst hnn
  rcases hsign with rfl | rfl <;> simp [padicValInt]

end Index

/-! ### The Kummer transfer -/

section Kummer

variable {G : Type*} [AddCommGroup G] {H : Type*} [AddCommGroup H] [Module ℤ_[2] H]

/-- **An additive map sends elements of finite order into the `ℤ₂`-torsion.** PROVED. -/
theorem mem_torsion_of_isOfFinAddOrder (κ : G →+ H) {t : G} (ht : IsOfFinAddOrder t) :
    κ t ∈ Submodule.torsion ℤ_[2] H := by
  obtain ⟨k, hk, hkt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 ht
  have hk0 : (k : ℤ_[2]) ≠ 0 := by exact_mod_cast hk.ne'
  refine (Submodule.mem_torsion_iff _).2 ⟨⟨(k : ℤ_[2]), mem_nonZeroDivisors_of_ne_zero hk0⟩, ?_⟩
  rw [Submonoid.smul_def]
  change (k : ℤ_[2]) • κ t = 0
  rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hkt, map_zero]

/-- **The Kummer transfer** (tex 3905–3907: "On a rank-one Mordell–Weil free lattice, both
free-line coefficients consequently have valuation `j_rc(h,k) + v₂(Lm)`"): if an additive map
`κ` carries `g` (for the text a free generator of the rank-one lattice) to a free-line generator
of the `ℤ₂`-module, then for `P ≡ n g` modulo torsion the free coefficient of `κ(k P)` is `k n`.
PROVED. -/
theorem freeCoeff_map_zsmul (κ : G →+ H) {g : G} (hκ : IsFreeLineGenerator ℤ_[2] (κ g)) {P : G}
    {n : ℤ} (hP : IsOfFinAddOrder (P - n • g)) (k : ℤ) :
    freeCoeff hκ (κ (k • P)) = ((k * n : ℤ) : ℤ_[2]) := by
  apply freeCoeff_eq_of hκ
  have e : κ (k • P) - ((k * n : ℤ) : ℤ_[2]) • κ g = κ (k • (P - n • g)) := by
    rw [Int.cast_smul_eq_zsmul, smul_sub, map_sub, map_zsmul, map_zsmul, map_zsmul, mul_smul]
  rw [e]
  exact mem_torsion_of_isOfFinAddOrder κ hP.zsmul

end Kummer

/-! ### The point half of the calibration at one address, abstract form -/

section PointData

/-- **The point half of the calibration at one address, abstract form** (tex 2411–2416,
3073–3085, 3895–3986, 4005–4021, 4057–4064). For `ℤ₂`-modules `H₁`, `H₂` (the first and second
cohomology of the ordinary compact Kummer complex), an abelian group `MW` (the native rank-one
lattice, `E^{(h)}(K)`), a map `κ : MW → H₁` (the Kummer map) and a pairing `PD` (the retained
duality pairing of the free degree-two and degree-one parts). Fields, with tex lines and kinds:

* `L`, `hL`, `hvL`: the fixed multiplier `L ≠ 0` of (H11), with `v₂L = vL` (3073–3085, 3897;
  definition).
* `P`: the point (for the text `P^{rc}_{h,k}` in its native lattice; 2411–2416, 3904; data).
* `gen`, `hgen`: a free generator of the rank-one lattice (3905, 4020–4021; input, rank one).
* `nP`, `hnP`, `hnP0`, `hj`: `P ≡ nP · gen`, `nP ≠ 0`, `v₂ nP = j`, so `j` is the index valuation
  of `P` (2416; definition of `j_rc`).
* `hκ`: the Kummer map carries the free generator to a free-line generator of `H₁` (3905,
  4007–4014; GLUE, Kummer sequence and finite `Ш`).
* `cK`, `hcK`: the conjugate-dual transport, an involutive endomorphism of `H₁` (3904,
  3977–3979; data, named).
* `g₂`, `hg₂`: a free-line generator of `H₂` (4015–4017; data).
* `hPD`: the pairing of the free lines is unimodular (4015–4017; GLUE, self-duality; PROVED for
  the retained model in `CalPointSelfDual.isUnit_evD`).

Kind: definition (a hypothesis structure); non-vacuity: `FreeLinePointData.example`. -/
structure FreeLinePointData (H₁ H₂ MW : Type*) [AddCommGroup H₁] [Module ℤ_[2] H₁]
    [AddCommGroup H₂] [Module ℤ_[2] H₂] [AddCommGroup MW] (κ : MW →+ H₁)
    (PD : H₂ →ₗ[ℤ_[2]] H₁ →ₗ[ℤ_[2]] ℤ_[2]) (j vL : ℤ) where
  /-- the fixed multiplier `L` -/
  L : ℤ
  /-- `L ≠ 0` -/
  hL : L ≠ 0
  /-- `v₂ L = vL` -/
  hvL : ((padicValInt 2 L : ℕ) : ℤ) = vL
  /-- the point -/
  P : MW
  /-- a free generator of the native rank-one lattice -/
  gen : MW
  /-- it is a free generator -/
  hgen : IsFreeGenerator gen
  /-- the coefficient of the point on the generator -/
  nP : ℤ
  /-- `P ≡ nP · gen` modulo torsion -/
  hnP : IsOfFinAddOrder (P - nP • gen)
  /-- the point is not torsion -/
  hnP0 : nP ≠ 0
  /-- `j` is the index valuation of the point -/
  hj : ((padicValInt 2 nP : ℕ) : ℤ) = j
  /-- the Kummer map carries the free generator to a free-line generator -/
  hκ : IsFreeLineGenerator ℤ_[2] (κ gen)
  /-- the conjugate-dual transport -/
  cK : H₁ →ₗ[ℤ_[2]] H₁
  /-- it is involutive -/
  hcK : ∀ y, cK (cK y) = y
  /-- a free-line generator of the degree-two cohomology -/
  g₂ : H₂
  /-- it is a free-line generator -/
  hg₂ : IsFreeLineGenerator ℤ_[2] g₂
  /-- the pairing of the free lines is unimodular -/
  hPD : IsUnit (PD g₂ (κ gen))

namespace FreeLinePointData

variable {H₁ H₂ MW : Type*} [AddCommGroup H₁] [Module ℤ_[2] H₁] [AddCommGroup H₂]
  [Module ℤ_[2] H₂] [AddCommGroup MW] {κ : MW →+ H₁} {PD : H₂ →ₗ[ℤ_[2]] H₁ →ₗ[ℤ_[2]] ℤ_[2]}
  {j vL : ℤ} (D : FreeLinePointData H₁ H₂ MW κ PD j vL)

/-- `j` is the index valuation of the point (tex 2416). PROVED. -/
theorem isIndexValuation : IsIndexValuation D.P j :=
  ⟨D.gen, D.nP, D.hgen, D.hnP, D.hnP0, D.hj⟩

/-- **The central class** `z₀ = κ(L m P)` (tex 3901: `z₀ = i(LmP)`). Kind: definition. -/
def zc (m : ℤ) : H₁ := κ ((D.L * m) • D.P)

/-- **The central functional** `x ↦ PD(x, c_K(κ(L m P)))` (tex 3902, 3976: "the Kummer-dual
functional of the same transported point"; no independently chosen scalar, tex 3980–3981).
Kind: definition. -/
def lc (m : ℤ) : H₂ →ₗ[ℤ_[2]] ℤ_[2] := PD.flip (D.cK (D.zc m))

/-- The free-line coefficient of the central class. Kind: definition. -/
def classCoeff (m : ℤ) : ℤ_[2] := freeCoeff D.hκ (D.zc m)

/-- The coefficient of the central functional on the free-line generator of `H₂`.
Kind: definition. -/
def funCoeff (m : ℤ) : ℤ_[2] := D.lc m D.g₂

/-- The sign of the conjugate-dual transport on the free line. Kind: definition. -/
def sgnK : ℤ_[2] := freeCoeff D.hκ (D.cK (κ D.gen))

/-- **The free coefficient of the central class is `L m nP`.** PROVED. -/
theorem classCoeff_eq (m : ℤ) : D.classCoeff m = ((D.L * m * D.nP : ℤ) : ℤ_[2]) :=
  freeCoeff_map_zsmul κ D.hκ D.hnP (D.L * m)

/-- **The conjugate-dual transport acts on the free line by `+1` or `−1`** (tex 3977–3979).
PROVED. -/
theorem sgnK_eq : D.sgnK = 1 ∨ D.sgnK = -1 :=
  freeCoeff_involution D.hκ D.cK D.hcK

/-- **The coefficient of the central functional** is the free coefficient of the class times the
sign of the transport times the unimodular pairing of the generators. PROVED. -/
theorem funCoeff_eq (m : ℤ) :
    D.funCoeff m = D.classCoeff m * D.sgnK * PD D.g₂ (κ D.gen) := by
  unfold funCoeff lc
  rw [LinearMap.flip_apply, pairing_apply PD D.hκ D.g₂, freeCoeff_map_endo D.hκ D.cK]
  rfl

/-- The sign times the pairing of the generators is a unit. PROVED. -/
theorem isUnit_sgnK_mul : IsUnit (D.sgnK * PD D.g₂ (κ D.gen)) := by
  refine IsUnit.mul ?_ D.hPD
  rcases D.sgnK_eq with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

/-- **The two free coefficients are associated** (tex 3979–3980: "The two free-line
coefficients both have valuation `j_rc(h,k) + v₂(Lm)`"). PROVED. -/
theorem funCoeff_associated (m : ℤ) : ∃ ε : ℤ_[2]ˣ, D.funCoeff m = ε * D.classCoeff m := by
  obtain ⟨ε, hε⟩ := D.isUnit_sgnK_mul
  exact ⟨ε, by rw [D.funCoeff_eq, hε, mul_assoc, mul_comm]⟩

end FreeLinePointData

/-- **Non-vacuity of `FreeLinePointData`**: `H₁ = H₂ = ℤ₂`, `MW = ℤ`, `κ` the inclusion, `PD`
the multiplication, `L = P = gen = 1`, `c_K = id`, `j = vL = 0`. PROVED. -/
def FreeLinePointData.example :
    FreeLinePointData ℤ_[2] ℤ_[2] ℤ (Int.castAddHom ℤ_[2]) (LinearMap.mul ℤ_[2] ℤ_[2]) 0 0 where
  L := 1
  hL := one_ne_zero
  hvL := by simp
  P := 1
  gen := 1
  hgen := ⟨by simp [isOfFinAddOrder_iff_nsmul_eq_zero], fun P => ⟨P, by simp⟩⟩
  nP := 1
  hnP := by simp
  hnP0 := one_ne_zero
  hj := by simp
  hκ := ⟨fun r hr => by
      simp at hr
      obtain ⟨a, ha, h⟩ := hr
      exact h.resolve_left ha, fun z => ⟨z, by simp⟩⟩
  cK := LinearMap.id
  hcK := fun _ => rfl
  g₂ := 1
  hg₂ := ⟨fun r hr => by
      simp at hr
      obtain ⟨a, ha, h⟩ := hr
      exact h.resolve_left ha, fun z => ⟨z, by simp⟩⟩
  hPD := by simp

end PointData

end ZInQ.Manuscript.RC.CalPoint

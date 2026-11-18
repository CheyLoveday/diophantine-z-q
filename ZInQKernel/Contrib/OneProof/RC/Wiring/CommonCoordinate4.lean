import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep

/-!
**Theorem 5.3, Lane RC0 round 4: (4.7) from retained naturality at the family's graph primes**

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4142–4328). Round 3's leaf
`CommonCoordinateInputsT` and batch 3's repaired form `CommonCoordinateInputsN` (`NaturalStep`:
the functional relation `w_R|old = e_q w_P` is derived from retained Selmer data, not assumed) take,
at each address `x` of a final family, a finite set `Q` of graph primes, a ring homomorphism `chi`
and a set `U` of unused primes that are not tied to the family or to `x`. With `Q = ∅` the leaf
collapses to `ũ_x = u_prim,x`, which is its own target up to the unit. Here the leaf is tightened to
the text:

* the graph primes are the family's primes `Fam.Q` ("In a binary family let `Q` be the union of its
  prime supports", tex 2731–2732; "First choose its actual finite set `Q`", tex 4232–4235);
* the character is the quadratic character of the address: `x(g_q) = (−1)^{λ_q(x)}` at the inertia
  generators `g_q` of the universal quadratic character (tex 4283–4285), at every graph prime
  (the graph-wide prescription, tex 4196–4207);
* the unused primes are those of the address: `U = {q ∈ Q : λ_q(x) = 0}` (`unusedAt`; "the primes
  unused by an individual character, including every graph prime at augmentation", tex 2735–2736;
  "For an inactive character `x`, `x(g_q) = 1`", tex 4291–4292);
* the residue cardinality at an unused prime is the prime itself ("the trace and determinant of
  `Fr_q` are `a_q` and `q`", tex 4213), odd by the admissibility of the family;
* the second scalar is the inverse of the first ("Write `z` for the scalar Frobenius value. With
  `e_q = a_q − z − z^{-1}`", tex 4144–4145).

Results (PROVED, standard axioms):

* `CommonCoordinateTrianglesG.toN`: batch 3's `CommonCoordinateTrianglesN` from the tightened data
  (`x(g_q) = ±1` and `U = {q ∈ Q : x(g_q) = 1}` are now theorems, `hsign`, `hU`);
* `commonCoordinateInputs_of_G : CommonCoordinateInputsG D → CommonCoordinateInputs D` (through
  batch 3's `commonCoordinateInputs_of_natural`), and `commonCoordinateTarget_of_G`;
* non-vacuity: `trianglesG_of_Q_empty` here (a family without graph primes) and, with one unused
  prime and a genuine `NaturalStep` at `q = 3`, `nonempty_trianglesG_three`
  (`CommonCoordinate4Witness.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! The unused primes of an address -/

/-- **The unused primes of the address `x`** (tex 2735–2736, 4142–4143, 4291–4295): the graph
primes `q ∈ Q` of the family with `λ_q(x) = 0`, i.e. those at which the quadratic character of `x`
is unramified (`q ∤ h_x`). At `x = 0` every graph prime is unused. -/
def unusedAt (Fam : Family) (x : Addr Fam.b) : Finset ℕ :=
  Fam.Q.filter fun q => Fam.lam q x = 0

theorem mem_unusedAt {Fam : Family} {x : Addr Fam.b} {q : ℕ} :
    q ∈ unusedAt Fam x ↔ q ∈ Fam.Q ∧ Fam.lam q x = 0 :=
  Finset.mem_filter

/-- At augmentation every graph prime is unused (PROVED). -/
theorem unusedAt_zero (Fam : Family) : unusedAt Fam 0 = Fam.Q := by
  ext q
  simp [mem_unusedAt]

/-- `−1 ≠ 1` in `ℚ₂[[t]]` (PROVED). -/
theorem neg_one_ne_one_powerSeries : (-1 : PowerSeries ℚ_[2]) ≠ 1 := by
  intro h
  have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ_[2])) h
  rw [map_neg, map_one] at h0
  norm_num at h0

/-- `(−1)^{λ}` for `λ ∈ 𝔽₂` is `1` in `ℚ₂[[t]]` exactly when `λ = 0` (PROVED). -/
theorem neg_one_pow_val_eq_one_iff (c : ZMod 2) :
    (-1 : PowerSeries ℚ_[2]) ^ c.val = 1 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    have hv : c.val = 1 := by
      have hlt := ZMod.val_lt c
      have h0 : c.val ≠ 0 := fun h0 => hc ((ZMod.val_eq_zero c).mp h0)
      omega
    rw [hv, pow_one] at h
    exact neg_one_ne_one_powerSeries h
  · rintro rfl
    simp

/-! The tightened support-triangle data -/

/-- **The support-triangle data at one address, tied to the family and the address**
(Lemma `ex:arith-common-coordinate`, tex 4142–4328). As batch 3's `CommonCoordinateTrianglesN`
(each relaxation step a `NaturalStep`), with `Q`, `U`, `hsign`, `hU`, `qn`, `hodd` replaced by the
family's data. Write `U = unusedAt Fam x`.

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `R`, `chi` | the coefficient ring `𝒪[G]` of the family and its evaluation at the character of `x` | 2728, 2747–2751, 4297 | definition | RC15 / RC7 |
| `g` | the inertia generators `g_q ∈ G` of the universal quadratic character | 4283–4285 | definition | RC15 |
| `hchi` | the character is the quadratic character of `x`: `x(g_q) = (−1)^{λ_q(x)}`, `q ∈ Fam.Q` | 4283–4285 | definition | RC15 / RC4 |
| `l`, `e`, `ei`, `v` | `l_q`, `e_q`, `e_q⁻¹` and `v_q = (l_q/e_q² − 1)/2` in `𝒪[G]` | 4196–4226 | definition | RC15 |
| `hratio` | `x(l_q) x(e_q⁻¹)² = 1 + 2 x(v_q)` at every graph prime | 4208–4220 | ELLIOT (the Frobenius model at `q`, `q² l_q = e_q² + (q−1)(q−1−(z+z⁻¹)e_q)`) | RC15 / RC4 |
| `hinv` | `e_q` is invertible at the character, at every graph prime | 4196–4207 | ELLIOT (`ē_q = t²/(1+t) ≠ 0`) | RC15 |
| `urel`, `hutilde` | the relaxed coordinate and `ũ_x = x(η) u_rel,x`, `η = ∏_{q ∈ Q} (1 + v_q(1 + g_q))` | 4219–4227 | definition | RC15 / RC7 |
| `F`, `a`, `z`, `zi`, `ha`, `hd`, `hzi`, `hl`, `he` | at each `p ∈ U`: a Frobenius matrix over `ℚ₂[[t]]` with trace `a_p` and determinant `p`, the scalar Frobenius value `z` and `z⁻¹`, `l_p` the two-place quotient factor and `e_p = a_p − z − z⁻¹` | 4144–4146, 4208–4216 | definition | RC15 / RC4 |
| `u`, `hrel`, `hprim` | the coordinates relaxed at `T ⊆ U`, `u U = u_rel`, `u ∅ = u_prim,x` | 4159–4188 | definition | RC15 |
| `eps`, `hstep` | each relaxation step `T → T ∪ {p}`, `p ∈ U`, is a `NaturalStep`: the support triangle in the original integral bases with `Λ`-unit basis comparisons, its functionals the paired functionals of retained Selmer data (`SelmerFunctionals`; `w_R|old = e_q w_P` is PROVED from naturality of the cup pairing) | 4159–4193 | ELLIOT + GLUE (Nekovář 6.4.1–6.4.3 through batch 3's retention data) | RC15 / batch 3 CommonCoordinate |
-/
structure CommonCoordinateTrianglesG {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type 1 where
  /-- the coefficient ring `𝒪[G]` -/
  R : Type
  [commR : CommRing R]
  /-- the evaluation at the character of the address -/
  chi : R →+* PowerSeries ℚ_[2]
  /-- `v_q = (l_q/e_q² − 1)/2` -/
  v : ℕ → R
  /-- the inertia generators `g_q` of the universal quadratic character -/
  g : ℕ → R
  /-- the quotient factors `l_q` -/
  l : ℕ → R
  /-- the point factors `e_q` -/
  e : ℕ → R
  /-- their inverses -/
  ei : ℕ → R
  /-- the character is the quadratic character of `x`: `x(g_q) = (−1)^{λ_q(x)}` -/
  hchi : ∀ q ∈ Fam.Q, chi (g q) = (-1) ^ (Fam.lam q x).val
  /-- `x(l_q) x(e_q)^{-2} = 1 + 2 x(v_q)` -/
  hratio : ∀ q ∈ Fam.Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q)
  /-- `e_q` is invertible at the character -/
  hinv : ∀ q ∈ Fam.Q, chi (e q) * chi (ei q) = 1
  /-- the relaxed coordinate -/
  urel : PowerSeries ℚ_[2]
  /-- the corrected coordinate is `η u_rel` at the address -/
  hutilde : D.uTilde Fam x = chi (Central.eta Fam.Q v g) * urel
  /-- the Frobenius matrices at the unused primes -/
  F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- their traces `a_p` -/
  a : ℕ → PowerSeries ℚ_[2]
  /-- the scalar Frobenius values `z` -/
  z : ℕ → PowerSeries ℚ_[2]
  /-- their inverses `z⁻¹` -/
  zi : ℕ → PowerSeries ℚ_[2]
  /-- `tr Fr_p = a_p` -/
  ha : ∀ p ∈ unusedAt Fam x, (F p).trace = a p
  /-- `det Fr_p = p` -/
  hd : ∀ p ∈ unusedAt Fam x, (F p).det = PowerSeries.C (p : ℚ_[2])
  /-- `z z⁻¹ = 1` -/
  hzi : ∀ p ∈ unusedAt Fam x, z p * zi p = 1
  /-- `l_p = det(1 − p⁻¹ z Fr_p) det(1 − p⁻¹ z⁻¹ Fr_p)` at the character -/
  hl : ∀ p ∈ unusedAt Fam x, chi (l p) =
    quotientFactor (F p) (PowerSeries.C ((p : ℚ_[2])⁻¹)) (z p) (zi p)
  /-- `e_p = a_p − z − z⁻¹` at the character -/
  he : ∀ p ∈ unusedAt Fam x, chi (e p) = pointFactor (a p) (z p) (zi p)
  /-- the coordinates relaxed at `T ⊆ U` -/
  u : Finset ℕ → PowerSeries ℚ_[2]
  /-- relaxed at every unused prime: `u_rel` -/
  hrel : u (unusedAt Fam x) = urel
  /-- relaxed at none: `u_prim,x` -/
  hprim : u ∅ = D.uPrim Fam x
  /-- the step units `ε_p` -/
  eps : ℕ → PowerSeries ℚ_[2]
  /-- each relaxation step is a `NaturalStep` -/
  hstep : ∀ T ⊆ unusedAt Fam x, ∀ p ∈ unusedAt Fam x, p ∉ T →
    NaturalStep (F p) (PowerSeries.C (p : ℚ_[2])) (PowerSeries.C ((p : ℚ_[2])⁻¹)) (a p)
      (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit

attribute [instance] CommonCoordinateTrianglesG.commR

/-- **Batch 3's `CommonCoordinateTrianglesN` from the tightened data** (PROVED): `Q` is the
family's set of primes; `x(g_q) = ±1` and `U = {q ∈ Q : x(g_q) = 1}` follow from
`x(g_q) = (−1)^{λ_q(x)}`; the residue cardinalities are the unused primes themselves, odd when the
graph primes are. -/
def CommonCoordinateTrianglesG.toN {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}
    (M : CommonCoordinateTrianglesG D Fam x) (hodd : ∀ q ∈ Fam.Q, Odd q) :
    CommonCoordinateTrianglesN D Fam x where
  R := M.R
  chi := M.chi
  Q := Fam.Q
  v := M.v
  g := M.g
  l := M.l
  e := M.e
  ei := M.ei
  hsign q hq := by
    rw [M.hchi q hq]
    exact neg_one_pow_eq_or _ _
  hratio := M.hratio
  hinv := M.hinv
  urel := M.urel
  U := unusedAt Fam x
  hU q := by
    rw [mem_unusedAt]
    constructor
    · rintro ⟨hq, h0⟩
      refine ⟨hq, ?_⟩
      rw [M.hchi q hq, h0]
      simp
    · rintro ⟨hq, h1⟩
      refine ⟨hq, (neg_one_pow_val_eq_one_iff _).mp ?_⟩
      rw [← M.hchi q hq]
      exact h1
  hutilde := M.hutilde
  qn p := p
  hodd p hp := hodd p (mem_unusedAt.mp hp).1
  F := M.F
  a := M.a
  z := M.z
  zi := M.zi
  ha := M.ha
  hd := M.hd
  hl := M.hl
  he := M.he
  u := M.u
  hrel := M.hrel
  hprim := M.hprim
  eps := M.eps
  hstep := M.hstep

/-- **The inputs of (4.7), tied to the family and the address** (tex 4142–4328): at every address
of a final family, one `CommonCoordinateTrianglesG`. -/
def CommonCoordinateInputsG {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateTrianglesG D F x)

/-- The graph primes of a final family are odd (PROVED, from its admissibility). -/
theorem odd_of_finalFamilyAt {ℓ : ℕ} {D : RCData ℓ} {Co Ce : ℤ} {F : Family}
    (hF : D.FinalFamilyAt Co Ce F) : ∀ q ∈ F.Q, Odd q :=
  fun q hq => (hF.1 q hq).1.odd_of_ne_two (hF.1 q hq).2.1

/-- Batch 3's `CommonCoordinateInputsN` from `CommonCoordinateInputsG` (PROVED). -/
theorem commonCoordinateInputsN_of_G {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG D) :
    CommonCoordinateInputsN D := fun Co Ce F hF x => by
  obtain ⟨M⟩ := h Co Ce F hF x
  exact ⟨M.toN (odd_of_finalFamilyAt hF)⟩

/-- **RC0's `CommonCoordinateInputs` from the tightened leaf** (PROVED, through batch 3's
`commonCoordinateInputs_of_natural`). -/
theorem commonCoordinateInputs_of_G {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG D) :
    CommonCoordinateInputs D :=
  commonCoordinateInputs_of_natural (commonCoordinateInputsN_of_G h)

/-- **`RCSteps.common_coordinate` from the tightened leaf** ((4.7), tex 4142–4328; PROVED). -/
theorem commonCoordinateTarget_of_G {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsG D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_inputs (commonCoordinateInputs_of_G h)

/-! Non-vacuity at a family without graph primes -/

/-- **A family without graph primes** (PROVED): the structure exists exactly as the text says,
`η = 1`, `U = ∅`, `ũ_x = u_prim,x`; the steps are vacuous. -/
def trianglesG_of_Q_empty {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (hQ : Fam.Q = ∅) (h : D.uTilde Fam x = D.uPrim Fam x) : CommonCoordinateTrianglesG D Fam x where
  R := PowerSeries ℚ_[2]
  chi := RingHom.id _
  v _ := 0
  g _ := 1
  l _ := 0
  e _ := 0
  ei _ := 0
  hchi q hq := by rw [hQ] at hq; exact absurd hq (Finset.notMem_empty q)
  hratio q hq := by rw [hQ] at hq; exact absurd hq (Finset.notMem_empty q)
  hinv q hq := by rw [hQ] at hq; exact absurd hq (Finset.notMem_empty q)
  urel := D.uPrim Fam x
  hutilde := by rw [h, hQ]; simp [Central.eta]
  F _ := 1
  a _ := 2
  z _ := 1
  zi _ := 1
  ha p hp := by simp [mem_unusedAt, hQ] at hp
  hd p hp := by simp [mem_unusedAt, hQ] at hp
  hzi p hp := by simp [mem_unusedAt, hQ] at hp
  hl p hp := by simp [mem_unusedAt, hQ] at hp
  he p hp := by simp [mem_unusedAt, hQ] at hp
  u _ := D.uPrim Fam x
  hrel := rfl
  hprim := rfl
  eps _ := 1
  hstep _ _ p hp := by simp [mem_unusedAt, hQ] at hp

end ZInQ.Manuscript.RC.Wiring

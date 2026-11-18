import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.CompanionLeaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus

/-!
# Theorem 5.3, Lane RC24 (round 2): the intrinsic odd filter has no veto at good primes

Round 1 read the intrinsic odd source through the stage support `W.admissible` of the data. In
Branch 2 that support is prime to `W.S`, which contains every prime of `k` (`CompanionLeaf`), while
the fresh prime of `k` is good for the odd stage types: so every set containing it read zero, and
with App F's readings this forces every nonempty reading to vanish, contradicting a nonempty
witness. The text reads the odd source on its own filter: "Enlarging `S_lab` records labels and
prime exclusions; it does not change the coefficient source" (tex 2027–2029); "The intrinsic odd
symbol continues to omit the primes of `k`" (2603); "Later stationary prime-selection tests may
enrich the common label alphabet without resieving the intrinsic odd source" (9481–9483);
"Additional stationary tests at primes dividing `k` … do not add conditions to that odd symbol"
(10594–10596). Round 2 makes that filter a field of the label data (`LabelData.oddAdmissible`).

This file records, as theorems, the difference between the two filters:

* `admissible_vetoes_fresh`: in Branch 2 the stage support of the data vetoes the fresh prime in
  every set (the round-1 mechanism; PROVED);
* `OddFilterTyped`: the intrinsic filter is read through the stage types on products of good primes
  (its fixed unit squareclasses at its own support, positive sign and moving condition
  `(D/ℓ₀) = 1`, tex 2016–2025, 10589–10592) — a property of the genuine filter;
* `oddAdmissible_no_veto`: a typed filter vetoes no good prime: if one set of good primes lies in
  it, then for every good prime `p` some set of good primes containing `p` lies in it (PROVED,
  Dirichlet's theorem);
* `not_oddFilterTyped_of_mask`: hence the round-1 choice (the stage support as the odd filter) is
  not typed in Branch 2 (PROVED);
* `typeFilter_typed`: the filter of the text's shape — positive, a square at `m₁` and at `ℓ₀`, prime
  to both — is typed (PROVED); so `OddFilterTyped` is satisfiable by a nonempty filter.

`oddAdmissible_no_veto` requires `OddFilterTyped` and a member of the filter.
`OddFilterTyped` is not a field of `AddressDensityLeaf`. `typeFilter_typed` proves a
property of the displayed filter shape; it does not construct label data satisfying
`oddAdmissible_iff` together with the data specification and nonzero density models.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter Finset

variable {ℓ : ℕ} {W : WData ℓ}

/-! ## The stage support vetoes the fresh prime -/

/-- **The fresh prime of `k` is good for every odd stage type** (PROVED: it is prime to `m₁` by
freshness and differs from `ℓ₀ θ`, which is prime to the common modulus `m ⊇ 4|k|`). -/
theorem LabelData.fresh_good (D : LabelData W) {p : ℕ} (hp : p.Prime) (hpk : (p : ℤ) ∣ W.kfin)
    (hpm₁ : ¬ p ∣ D.m₁) (θ : ℕ) : (D.T₁ θ).Good p := by
  have hpkN : p ∣ W.kfin.natAbs := by
    have hh := Int.natAbs_dvd_natAbs.mpr hpk
    simpa using hh
  have hpm : p ∣ D.m := (hpkN.trans (dvd_mul_left _ _)).trans D.kdvdm
  refine ⟨hp, ?_⟩
  rw [D.T₁_m]
  exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm₁)
    (Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right hpm (D.ℓ₀_cop θ)))

/-- **In Branch 2 the stage support of the data vetoes every prime of `k`** (PROVED; the mechanism
of the round-1 inconsistency): `W.admissible ⊆ W.prepared`, prepared indices are prime to `W.S`
(`PreparedSpec`, tex 2344–2346, 2404–2410), and `W.S` contains the primes of `k`
(`CompanionLeaf`, tex 2595–2603). -/
theorem admissible_vetoes_fresh (hprep : PreparedSpec W)
    (hsplit : ∀ θ d, W.admissible θ d → W.prepared d) (hcomp : CompanionLeaf W)
    (hU : ¬ W.OddEmptyUnit) {p : ℕ} (hp : p.Prime) (hpk : (p : ℤ) ∣ W.kfin) :
    ∀ θ (U : Finset ℕ), p ∈ U → ¬ W.admissible θ (∏ q ∈ U, (q : ℤ)) := by
  intro θ U hpU hadm
  have hpS : p ∈ W.S := (hcomp hU).2.2.2.2.1 p hp hpk
  exact (hprep _ (hsplit θ _ hadm)).2.2.2 p hpS (Finset.dvd_prod_of_mem _ hpU)

/-! ## Typed filters have no veto -/

/-- **The intrinsic odd filter is read through the stage types** (definition of the property; tex
2016–2025, 10589–10592: the filter consists of its fixed unit squareclasses at its own coefficient
support, the positive sign and the moving condition `(D/ℓ₀) = 1`, all of which are recorded by the
stage types when the support lies in `m₁`): on products of distinct primes good for the stage
types, membership depends only on the total stage type. -/
def OddFilterTyped (D : LabelData W) : Prop :=
  ∀ θ (U U' : Finset ℕ), (∀ q ∈ U, (D.T₁ θ).Good q) → (∀ q ∈ U', (D.T₁ θ).Good q) →
    (∑ q ∈ U, (D.T₁ θ).typ q) = (∑ q ∈ U', (D.T₁ θ).typ q) →
    (D.oddAdmissible θ (∏ q ∈ U, (q : ℤ)) ↔ D.oddAdmissible θ (∏ q ∈ U', (q : ℤ)))

/-- Congruent good primes have the same stage type (PROVED: the type is the squareclass modulo
`m₁` and the Legendre bit at `ℓ₀`). -/
theorem LabelData.T₁_typ_eq_of_cast_eq (D : LabelData W) (θ : ℕ) {p p' : ℕ}
    (hp : Nat.Coprime p D.m₁) (h : (p' : ZMod (D.m₁ * D.ℓ₀ θ)) = p) :
    (D.T₁ θ).typ p' = (D.T₁ θ).typ p := by
  rw [D.T₁_typ, D.T₁_typ]
  have h₁ : ((p' : ℤ) : ZMod D.m₁) = ((p : ℤ) : ZMod D.m₁) := by
    have := congrArg (ZMod.castHom (dvd_mul_right D.m₁ (D.ℓ₀ θ)) (ZMod D.m₁)) h
    simpa using this
  have h₂ : ((p' : ℤ) : ZMod (D.ℓ₀ θ)) = ((p : ℤ) : ZMod (D.ℓ₀ θ)) := by
    have := congrArg (ZMod.castHom (dvd_mul_left (D.ℓ₀ θ) D.m₁) (ZMod (D.ℓ₀ θ))) h
    simpa using this
  have hu := isUnit_natCast_of_coprime hp
  refine Prod.ext ?_ ?_
  · show sqClassOf D.m₁ (p' : ℤ) = sqClassOf D.m₁ (p : ℤ)
    rw [sqClassOf_eq_sqMk hu.unit (h₁.trans hu.unit_spec.symm),
      sqClassOf_eq_sqMk hu.unit hu.unit_spec.symm]
  · show legBit (p' : ℤ) (D.ℓ₀ θ) = legBit (p : ℤ) (D.ℓ₀ θ)
    exact legBit_congr (by rw [h₂])

/-- **A typed filter vetoes no good prime** (PROVED; Dirichlet's theorem): if a set `U` of good
primes lies in the filter, then for every good prime `p` the set `U ∪ {p, p'}`, with `p' ≡ p`
modulo `m₁ℓ₀` a fresh prime, has the same total type and lies in the filter. Contrast
`admissible_vetoes_fresh`. -/
theorem oddAdmissible_no_veto (D : LabelData W) (htyped : OddFilterTyped D) {θ : ℕ}
    {U : Finset ℕ} (hU : ∀ q ∈ U, (D.T₁ θ).Good q)
    (hadm : D.oddAdmissible θ (∏ q ∈ U, (q : ℤ))) {p : ℕ} (hp : (D.T₁ θ).Good p) :
    ∃ U' : Finset ℕ, p ∈ U' ∧ (∀ q ∈ U', (D.T₁ θ).Good q) ∧
      D.oddAdmissible θ (∏ q ∈ U', (q : ℤ)) := by
  classical
  by_cases hpU : p ∈ U
  · exact ⟨U, hpU, hU, hadm⟩
  have hm : (D.T₁ θ).m = D.m₁ * D.ℓ₀ θ := D.T₁_m θ
  have hpc : Nat.Coprime p (D.m₁ * D.ℓ₀ θ) := by rw [← hm]; exact hp.2
  have : NeZero (D.m₁ * D.ℓ₀ θ) := ⟨Nat.mul_ne_zero D.m₁_pos.ne' (D.ℓ₀_prime θ).ne_zero⟩
  have hunit : IsUnit (p : ZMod (D.m₁ * D.ℓ₀ θ)) := (ZMod.isUnit_iff_coprime p _).2 hpc
  obtain ⟨p', hp'gt, hp'prime, hp'mod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hunit (U.sup id + p)
  have hp'U : p' ∉ U := fun h => by
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  have hp'p : p' ≠ p := by omega
  have hp'good : (D.T₁ θ).Good p' := by
    refine ⟨hp'prime, ?_⟩
    rw [hm]
    have : IsUnit (p' : ZMod (D.m₁ * D.ℓ₀ θ)) := hp'mod ▸ hunit
    exact (ZMod.isUnit_iff_coprime p' _).1 this
  have htyp : (D.T₁ θ).typ p' = (D.T₁ θ).typ p :=
    D.T₁_typ_eq_of_cast_eq θ (Nat.Coprime.coprime_mul_right_right hpc) hp'mod
  have hpU' : p ∉ insert p' U := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hp'p h.symm
    · exact hpU h
  have hgood : ∀ q ∈ insert p (insert p' U), (D.T₁ θ).Good q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp'good
    · exact hU q hq
  have hsum : (∑ q ∈ insert p (insert p' U), (D.T₁ θ).typ q) = ∑ q ∈ U, (D.T₁ θ).typ q := by
    rw [Finset.sum_insert hpU', Finset.sum_insert hp'U, htyp]
    have key : ∀ (a s : D.L₁), a + (a + s) = s := fun a s => by
      refine Prod.ext ?_ ?_
      · show a.1 + (a.1 + s.1) = s.1
        have h1 : a.1 + a.1 = 0 := sqClass_add_self a.1
        calc a.1 + (a.1 + s.1) = (a.1 + a.1) + s.1 := (add_assoc a.1 a.1 s.1).symm
          _ = 0 + s.1 := congrArg (· + s.1) h1
          _ = s.1 := zero_add s.1
      · show a.2 + (a.2 + s.2) = s.2
        generalize a.2 = x
        generalize s.2 = y
        revert x y; decide
    exact key _ _
  exact ⟨insert p (insert p' U), Finset.mem_insert_self _ _, hgood,
    (htyped θ _ _ hgood hU hsum).mpr hadm⟩

/-- **The round-1 choice is not typed in Branch 2** (PROVED): if the odd filter is contained in the
stage support of the data and contains `1` at some stage, then in Branch 2, with a fresh prime of
`k`, it is not read through the stage types (`oddAdmissible_no_veto` against
`admissible_vetoes_fresh`). -/
theorem not_oddFilterTyped_of_mask (D : LabelData W) (hprep : PreparedSpec W)
    (hsplit : ∀ θ d, W.admissible θ d → W.prepared d) (hcomp : CompanionLeaf W)
    (hU : ¬ W.OddEmptyUnit) (hfresh : FreshPrime W D)
    (hmask : ∀ θ d, D.oddAdmissible θ d → W.admissible θ d) {θ : ℕ}
    (h1 : D.oddAdmissible θ 1) : ¬ OddFilterTyped D := by
  intro htyped
  obtain ⟨p, hp, hpk, hpm₁⟩ := hfresh
  obtain ⟨U', hpU', -, hadm'⟩ := oddAdmissible_no_veto D htyped (U := ∅) (θ := θ)
    (fun q hq => absurd hq (Finset.notMem_empty q)) (by simpa using h1)
    (D.fresh_good hp hpk hpm₁ θ)
  exact admissible_vetoes_fresh hprep hsplit hcomp hU hp hpk θ U' hpU' (hmask θ _ hadm')

/-! ## The text's filter shape is typed -/

/-- **The filter of the text's shape** (definition; tex 10589–10592): positive, a square modulo
`m₁` and modulo `ℓ₀ θ`. -/
def LabelData.typeFilter (D : LabelData W) (θ : ℕ) (d : ℤ) : Prop :=
  0 < d ∧ IsSquare (d : ZMod D.m₁) ∧ IsSquare (d : ZMod (D.ℓ₀ θ))

/-- **The filter of the text's shape is read through the stage types** (PROVED: on products of good
primes, squareness modulo `m₁` is the vanishing of the first coordinate of the total type, and
squareness modulo `ℓ₀` the vanishing of its second coordinate). -/
theorem typeFilter_typed (D : LabelData W) (θ : ℕ) (U U' : Finset ℕ)
    (hU : ∀ q ∈ U, (D.T₁ θ).Good q) (hU' : ∀ q ∈ U', (D.T₁ θ).Good q)
    (hsum : (∑ q ∈ U, (D.T₁ θ).typ q) = (∑ q ∈ U', (D.T₁ θ).typ q)) :
    D.typeFilter θ (∏ q ∈ U, (q : ℤ)) ↔ D.typeFilter θ (∏ q ∈ U', (q : ℤ)) := by
  have key : ∀ V : Finset ℕ, (∀ q ∈ V, (D.T₁ θ).Good q) →
      (D.typeFilter θ (∏ q ∈ V, (q : ℤ)) ↔
        (∑ q ∈ V, (D.T₁ θ).typ q).1 = 0 ∧ (∑ q ∈ V, (D.T₁ θ).typ q).2 = 0) := by
    intro V hV
    have hc₁ : ∀ q ∈ V, Nat.Coprime q D.m₁ := fun q hq => by
      have := (hV q hq).2
      rw [D.T₁_m] at this
      exact Nat.Coprime.coprime_mul_right_right this
    have hnd : ∀ q ∈ V, ¬ ((D.ℓ₀ θ : ℕ) : ℤ) ∣ (q : ℤ) := fun q hq hdvd => by
      have hc := (hV q hq).2
      rw [D.T₁_m] at hc
      have h1 : D.ℓ₀ θ ∣ q := Int.natCast_dvd_natCast.mp hdvd
      have h2 : Nat.Coprime q (D.ℓ₀ θ) := Nat.Coprime.coprime_mul_left_right hc
      exact (D.ℓ₀_prime θ).one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) h1)
    have hpos : 0 < ∏ q ∈ V, (q : ℤ) :=
      Finset.prod_pos fun q hq => by exact_mod_cast (hV q hq).1.pos
    have hfst : (∑ q ∈ V, (D.T₁ θ).typ q).1 = sqClassOf D.m₁ (∏ q ∈ V, (q : ℤ)) := by
      rw [Prod.fst_sum, sqClassOf_prod _ (fun q => (q : ℤ))
        (fun q hq => isUnit_natCast_of_coprime (hc₁ q hq))]
      exact Finset.sum_congr rfl fun q _ => by rw [D.T₁_typ]
    have hsnd : (∑ q ∈ V, (D.T₁ θ).typ q).2 = legBit (∏ q ∈ V, (q : ℤ)) (D.ℓ₀ θ) := by
      rw [Prod.snd_sum, legBit_prod _ (fun q => (q : ℤ)) (D.ℓ₀_prime θ) hnd]
      exact Finset.sum_congr rfl fun q _ => by rw [D.T₁_typ]
    rw [hfst, hsnd, sqClassOf_eq_zero_iff (isUnit_prod_of_coprime hc₁), legBit_eq_zero_iff]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hpos, h.1, h.2⟩⟩
  rw [key U hU, key U' hU', hsum]

/-- **`OddFilterTyped` is satisfiable by the filter of the text's shape** (PROVED). -/
theorem oddFilterTyped_of_typeFilter (D : LabelData W)
    (h : ∀ θ d, D.oddAdmissible θ d ↔ D.typeFilter θ d) : OddFilterTyped D := by
  intro θ U U' hU hU' hsum
  rw [h, h]
  exact typeFilter_typed D θ U U' hU hU' hsum

end ZInQ.Manuscript.RC.AddressGenuine

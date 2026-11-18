import Research.DerivativeSwitch.FiniteSelmerCoefficients
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Retaining varying finite-stage coefficients at every precision

One ultrafilter selects the residue at each precision after reduction from
the cofinal stages. Compatibility of the selected residues is proved without
assuming that the original sequence of coefficient arrays is compatible.
-/

namespace Research.DerivativeSwitch.RetainedCoefficients

open Filter FiniteSelmerCoefficients

noncomputable section

private theorem eventually_value {A : Type*} [Finite A] (U : Ultrafilter ℕ) (f : ℕ → A) :
    ∃ a : A, ∀ᶠ i in (U : Filter ℕ), f i = a := by
  obtain ⟨a, ha⟩ := (U.map f).eq_pure_of_finite
  use a
  have h : ({a} : Set A) ∈ (U.map f : Filter A) := by rw [ha]; simp
  exact h

private def selectedValue {A : Type*} [Finite A] (U : Ultrafilter ℕ) (f : ℕ → A) : A :=
  (eventually_value U f).choose

private theorem eventually_selected {A : Type*} [Finite A] (U : Ultrafilter ℕ) (f : ℕ → A) :
    ∀ᶠ i in (U : Filter ℕ), f i = selectedValue U f := (eventually_value U f).choose_spec

private theorem selected_eq {A : Type*} [Finite A] {U : Ultrafilter ℕ} {f : ℕ → A} {a : A}
    (ha : ∀ᶠ i in (U : Filter ℕ), f i = a) : selectedValue U f = a := by
  obtain ⟨_, h, h'⟩ := ((eventually_selected U f).and ha).exists
  exact h.symm.trans h'

abbrev StageFamily := (i : ℕ) → Scalar i

def atPrecision (n : ℕ) (f : StageFamily) (i : ℕ) : Scalar n :=
  if h : n ≤ i then reduce h (f i) else 0

variable (U : Ultrafilter ℕ) (cofinal : ∀ n, ∀ᶠ i in (U : Filter ℕ), n ≤ i)

/-- The retained coefficient at a single finite precision. -/
def residue (n : ℕ) : StageFamily →+* Scalar n where
  toFun f := selectedValue U (atPrecision n f)
  map_zero' := by
    apply selected_eq
    filter_upwards [cofinal n] with i hi
    simp [atPrecision, hi]
  map_one' := by
    apply selected_eq
    filter_upwards [cofinal n] with i hi
    simp [atPrecision, hi]
  map_add' f g := by
    apply selected_eq
    filter_upwards [cofinal n, eventually_selected U (atPrecision n f),
      eventually_selected U (atPrecision n g)] with i hi hf hg
    simpa [atPrecision, hi] using congrArg₂ (· + ·) hf hg
  map_mul' f g := by
    apply selected_eq
    filter_upwards [cofinal n, eventually_selected U (atPrecision n f),
      eventually_selected U (atPrecision n g)] with i hi hf hg
    simpa [atPrecision, hi] using congrArg₂ (· * ·) hf hg

/-- The cofinal choice may be used on all the entries of a finite diagram. -/
theorem residue_eventually (n : ℕ) (f : StageFamily) :
    ∀ᶠ i in (U : Filter ℕ), atPrecision n f i = residue U cofinal n f :=
  eventually_selected U (atPrecision n f)

theorem residue_compatible {n m : ℕ} (h : n ≤ m) (f : StageFamily) :
    reduce h (residue U cofinal m f) = residue U cofinal n f := by
  obtain ⟨i, hi, hm, hn⟩ := ((cofinal m).and
    ((residue_eventually U cofinal m f).and (residue_eventually U cofinal n f))).exists
  rw [atPrecision, dite_eq_left hi] at hm
  rw [atPrecision, dite_eq_left (h.trans hi)] at hn
  rw [← hm, ← hn, ← RingHom.comp_apply, reduce_comp]

/-- The inverse-limit ring presented by compatible finite residues. -/
def CompatibleScalars : Subring StageFamily where
  carrier := { f | ∀ {n m : ℕ} (h : n ≤ m), reduce h (f m) = f n }
  zero_mem' := by intro n m h; simp
  one_mem' := by intro n m h; simp
  add_mem' {f g} hf hg := by intro n m h; simp [hf h, hg h]
  mul_mem' {f g} hf hg := by intro n m h; simp [hf h, hg h]
  neg_mem' {f} hf := by intro n m h; simp [hf h]

/-- A single ring homomorphism transports finite sums, products and matrix
identities from the varying coefficient stages to the actual residue limit. -/
def retain : StageFamily →+* CompatibleScalars :=
  (RingHom.pi fun n => residue U cofinal n).codRestrict CompatibleScalars
    (fun f _ _ h => residue_compatible U cofinal h f)

end

end Research.DerivativeSwitch.RetainedCoefficients

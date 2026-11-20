import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.ConeInverse
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# Lane RC31, round 5: over a field, quasi-isomorphisms are homotopy equivalences

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451: over the residue
field a quasi-isomorphism of bounded complexes is a homotopy equivalence, so the finite models
compare to the genuine complexes by actual chain maps and homotopies) and the support triangle
(5.6) (tex 5398–5424).

* `homotopyEquiv_of_quasiIso_field`: over a field `k`, a quasi-isomorphism `f : K → L` of cochain
  complexes of `k`-modules, both strictly concentrated in degrees `≥ a`, is the forward map of a
  homotopy equivalence. Every `k`-module is injective, so both complexes are K-injective.
* `homotopyEquiv_of_quasiIso_field_le`: the dual form, for complexes strictly concentrated in
  degrees `≤ b` (every `k`-module is projective, so both complexes are K-projective).
* `natCx_toCC_isStrictlyGE`: the extension by zero of an `ℕ`-indexed complex is strictly
  concentrated in degrees `≥ 0`; `natCx_homotopyEquiv_of_quasiIso` applies the first item.
* `inverse_quasiIso_of_quasiIso_field`: the reverse quasi-isomorphism (model to genuine).
* `HomotopyEquiv.inv_comp_homotopy`: a strictly commuting square of homotopy equivalences
  `ι ≫ e_L = e_U ≫ ι'` gives a homotopy `e_U⁻¹ ≫ ι ∼ ι' ≫ e_L⁻¹`.

Kinds: PROVED and definitions.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory Limits

universe u

section Field

variable {k : Type u} [Field k]

/-- Every term of a complex of modules over a field is an injective object (tex 4391–4451).
Kind: PROVED. -/
theorem injective_X_field (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ) :
    Injective (K.X n) := by
  have := Module.injective_of_isSemisimpleRing k (K.X n)
  exact Module.injective_object_of_injective_module k (K.X n)

/-- Every term of a complex of modules over a field is a projective object (tex 4391–4451).
Kind: PROVED. -/
theorem projective_X_field (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ) :
    Projective (K.X n) := by
  have := Module.projective_of_isSemisimpleRing k (K.X n)
  exact ModuleCat.projective_of_categoryTheory_projective (K.X n)

/-- A complex of modules over a field strictly concentrated in degrees `≥ a` is K-injective
(tex 4391–4451). Kind: PROVED. -/
theorem isKInjective_field (K : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : K.IsKInjective := by
  have : ∀ n, Injective (K.X n) := injective_X_field K
  exact CochainComplex.isKInjective_of_injective K a

/-- A complex of modules over a field strictly concentrated in degrees `≤ b` is K-projective
(tex 4391–4451). Kind: PROVED. -/
theorem isKProjective_field (K : CochainComplex (ModuleCat.{u} k) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : K.IsKProjective := by
  have : ∀ n, Projective (K.X n) := projective_X_field K
  exact CochainComplex.isKProjective_of_projective K b

/-- **Over a field, a quasi-isomorphism of bounded-below complexes is a homotopy equivalence**
(tex 4391–4451): for complexes `K`, `L` of `k`-modules strictly concentrated in degrees `≥ a`,
every quasi-isomorphism `f : K → L` is the forward map of a homotopy equivalence.
Kind: PROVED. -/
theorem homotopyEquiv_of_quasiIso_field {K L : CochainComplex (ModuleCat.{u} k) ℤ} (a : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE a] (f : K ⟶ L) [QuasiIso f] :
    ∃ e : HomotopyEquiv K L, e.hom = f := by
  have := isKInjective_field K a
  have := isKInjective_field L a
  exact (CochainComplex.IsKInjective.quasiIso_iff f).1 inferInstance

/-- **The dual form** (tex 4391–4451): for complexes `K`, `L` of `k`-modules strictly
concentrated in degrees `≤ b`, every quasi-isomorphism `f : K → L` is the forward map of a
homotopy equivalence. Kind: PROVED. -/
theorem homotopyEquiv_of_quasiIso_field_le {K L : CochainComplex (ModuleCat.{u} k) ℤ} (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] (f : K ⟶ L) [QuasiIso f] :
    ∃ e : HomotopyEquiv K L, e.hom = f := by
  have := isKProjective_field K b
  have := isKProjective_field L b
  exact (CochainComplex.IsKProjective.quasiIso_iff f).1 inferInstance

/-- **Model to genuine** (tex 4391–4451): over a field, a quasi-isomorphism `f : K → L` of
complexes strictly concentrated in degrees `≥ a` has a reverse quasi-isomorphism `g : L → K`
with `f ≫ g ∼ 1` and `g ≫ f ∼ 1`. Kind: PROVED. -/
theorem inverse_quasiIso_of_quasiIso_field {K L : CochainComplex (ModuleCat.{u} k) ℤ} (a : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE a] (f : K ⟶ L) [QuasiIso f] :
    ∃ g : L ⟶ K, QuasiIso g ∧ Nonempty (Homotopy (f ≫ g) (𝟙 K)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 L)) := by
  obtain ⟨e, rfl⟩ := homotopyEquiv_of_quasiIso_field a f
  exact ⟨e.inv, inferInstance, ⟨e.homotopyHomInvId⟩, ⟨e.homotopyInvHomId⟩⟩

end Field

/-! ### Extension by zero of `ℕ`-indexed complexes -/

section Nat

variable {k : Type u} [CommRing k]

/-- **The extension by zero is strictly concentrated in degrees `≥ 0`** (tex 3455–3463, the
genuine continuous cochain complexes): its terms in negative degrees are zero. Kind: PROVED. -/
theorem natCx_toCC_isStrictlyGE (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    (SelmerComplex.natCx K).toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rcases i with n | m
  · rw [Int.ofNat_eq_natCast] at hi
    omega
  · change IsZero (ModuleCat.of k PUnit.{u + 1})
    exact ModuleCat.isZero_of_subsingleton _

/-- **Genuine complexes over a field** (tex 4391–4451): a quasi-isomorphism between extensions
by zero of `ℕ`-indexed complexes of `k`-modules is the forward map of a homotopy equivalence.
Kind: PROVED. -/
theorem natCx_homotopyEquiv_of_quasiIso {F : Type u} [Field F]
    {K L : CochainComplex (ModuleCat.{u} F) ℕ}
    (f : (SelmerComplex.natCx K).toCC ⟶ (SelmerComplex.natCx L).toCC) [QuasiIso f] :
    ∃ e : HomotopyEquiv (SelmerComplex.natCx K).toCC (SelmerComplex.natCx L).toCC, e.hom = f := by
  have := natCx_toCC_isStrictlyGE K
  have := natCx_toCC_isStrictlyGE L
  exact homotopyEquiv_of_quasiIso_field 0 f

end Nat

/-! ### Compatibility of homotopy inverses with strictly commuting squares -/

section Compat

variable {ι : Type*} {V : Type*} [Category V] [Preadditive V] {c : ComplexShape ι}

/-- **Homotopy inverses of a strictly commuting square** (tex 4438–4451, 5398–5424): for
homotopy equivalences `e_L : L ≃ L'`, `e_U : U ≃ U'` and chain maps `ι : U → L`, `ι' : U' → L'`
with `ι ≫ e_L = e_U ≫ ι'`, the homotopy inverses satisfy `e_U⁻¹ ≫ ι ∼ ι' ≫ e_L⁻¹`.
Kind: definition (a homotopy). -/
def HomotopyEquiv.inv_comp_homotopy {L L' U U' : HomologicalComplex V c}
    (eL : HomotopyEquiv L L') (eU : HomotopyEquiv U U') (i : U ⟶ L) (i' : U' ⟶ L')
    (hsq : i ≫ eL.hom = eU.hom ≫ i') :
    Homotopy (eU.inv ≫ i) (i' ≫ eL.inv) := by
  have H1 : Homotopy (eU.inv ≫ i ≫ eL.hom ≫ eL.inv) (eU.inv ≫ i) :=
    ((eL.homotopyHomInvId.compLeft i).trans (Homotopy.ofEq (Category.comp_id i))).compLeft eU.inv
  have heq : eU.inv ≫ i ≫ eL.hom ≫ eL.inv = (eU.inv ≫ eU.hom) ≫ i' ≫ eL.inv := by
    rw [← Category.assoc i, hsq]
    simp only [Category.assoc]
  have H2 : Homotopy ((eU.inv ≫ eU.hom) ≫ i' ≫ eL.inv) (𝟙 U' ≫ i' ≫ eL.inv) :=
    eU.homotopyInvHomId.compRight _
  exact ((H1.symm.trans (Homotopy.ofEq heq)).trans H2).trans
    (Homotopy.ofEq (Category.id_comp _))

end Compat

end ZInQ.Manuscript.RC.Limits

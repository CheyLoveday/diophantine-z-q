import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.ReductionInjective

/-!
# A fragment of (R): reduction is equivariant for the decomposition group

`ModularWeil/ReductionInjective.lean` proves that reduction at good reduction is injective on
prime-to-`p` torsion. The other missing part of the reduction comparison (R) of
`ModularWeil/FrobeniusTrace.lean` is Galois-equivariance: an element `σ` of the decomposition
group of the valuation subring `A` acts compatibly with reduction, `σ(P)` reducing to `σ̄(P̃)`,
where `σ̄` is the induced automorphism of the residue field. In particular an arithmetic Frobenius
(`σ̄ : z ↦ z^p`) acts on reduced coordinates as `x ↦ x^p`.

This file proves that, over any field `L` with a valuation subring `A` and a Weierstrass curve `W`
with coefficients in `A` and good reduction, for `σ ∈ A.decompositionSubgroup K` (`K` any base
field of `L`):

* `reducePoint_some_apply_of_mem_decompositionSubgroup` (PROVED): if `x ∈ A`, the reduction of
  `(σ x, σ y)` is `(σ̄ x̃, σ̄ ỹ)`;
* `reducePoint_some_apply_of_mem_decompositionSubgroup_of_notMem` (PROVED): if `x ∉ A`, both
  `(x, y)` and `(σ x, σ y)` reduce to the point at infinity;
* `reducePoint_some_apply_of_frobenius` (PROVED): if `σ̄` is `z ↦ z^p` on the residue field, the
  reduction of `(σ x, σ y)` is `(x̃^p, ỹ^p)`.

This generalizes the inertia case `WeierstrassCurve.reducePoint_some_apply_of_mem_inertia`
(where `σ̄ = 1`) of the vendored library
`ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT` (vendored from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, licence Apache-2.0), whose reduction map
`WeierstrassCurve.reducePoint` and decomposition-group lemmas are used as infrastructure.

**What remains of (R).** The integral model of `E` over the valuation subring of `\bar ℚ_p`, the
identification of its residue field with `\bar 𝔽_p` and of the reduced curve with the reduction
of `E` base changed to `\bar 𝔽_p`, and the identification of the induced residue automorphism of
an arithmetic Frobenius (`IsArithmeticFrobeniusOnClosureQ`) with `z ↦ z^p`.

**Classification.** PROVED (from the vendored library).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open WeierstrassCurve IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
  (hΔ : (W.map (residue A)).Δ ≠ 0) {K : Type*} [Field K] [Algebra K L]

/-- **Reduction commutes with the decomposition group** (PROVED). For `σ` in the decomposition
group of `A` and a point `(x, y)` with `x ∈ A`, the reduction of `(σ x, σ y)` is `(σ̄ x̃, σ̄ ỹ)`,
where `σ̄` is the action of `σ` on the residue field. -/
theorem reducePoint_some_apply_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) (hx : x ∈ A) :
    ∃ h'' : (W.map (residue A)).toAffine.Nonsingular
        ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A ⟨x, hx⟩)
        ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩),
      reducePoint hΔ (.some (σ x) (σ y) h') = .some _ _ h'' := by
  have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
  have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
  have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy
  have ex : residue A (⟨σ x, hσx⟩ : A) =
      (⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A ⟨x, hx⟩ := rfl
  have ey : residue A (⟨σ y, hσy⟩ : A) =
      (⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A ⟨y, hy⟩ := rfl
  have hns : (W.map (residue A)).toAffine.Nonsingular (residue A (⟨σ x, hσx⟩ : A))
      (residue A (⟨σ y, hσy⟩ : A)) :=
    Affine.nonsingular_residue W hΔ (x := ⟨σ x, hσx⟩) (y := ⟨σ y, hσy⟩) h'.1
  rw [ex, ey] at hns
  refine ⟨hns, ?_⟩
  rw [reducePoint_some_of_mem _ _ hσx, Affine.Point.some.injEq]
  exact ⟨ex, ey⟩

/-- Points outside the valuation ring reduce to the point at infinity, before and after `σ`
(PROVED). -/
theorem reducePoint_some_apply_of_mem_decompositionSubgroup_of_notMem {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) (hx : x ∉ A) :
    reducePoint hΔ (.some (σ x) (σ y) h') = 0 ∧ reducePoint hΔ (.some x y h) = 0 := by
  have hσx : σ x ∉ A := fun hmem => hx (by
    simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
  exact ⟨reducePoint_some_of_notMem _ _ hσx, reducePoint_some_of_notMem _ _ hx⟩

/-- **An arithmetic Frobenius acts as `x ↦ x^p` on reduced coordinates** (PROVED). If `σ` lies in
the decomposition group and acts on the residue field as `z ↦ z^p`, the reduction of
`(σ x, σ y)` is `(x̃^p, ỹ^p)`. -/
theorem reducePoint_some_apply_of_frobenius {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    {p : ℕ} (hfrob : ∀ z : ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • z = z ^ p)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) (hx : x ∈ A) :
    ∃ h'' : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩ ^ p)
        (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩ ^ p),
      reducePoint hΔ (.some (σ x) (σ y) h') = .some _ _ h'' := by
  obtain ⟨h'', e⟩ := reducePoint_some_apply_of_mem_decompositionSubgroup hΔ hσ h h' hx
  have key : ∀ {a b a' b' : ResidueField A} (ha : a = a') (hb : b = b')
      (hab : (W.map (residue A)).toAffine.Nonsingular a b),
      reducePoint hΔ (.some (σ x) (σ y) h') = .some a b hab →
        ∃ hab' : (W.map (residue A)).toAffine.Nonsingular a' b',
          reducePoint hΔ (.some (σ x) (σ y) h') = .some a' b' hab' := by
    rintro a b a' b' rfl rfl hab e
    exact ⟨hab, e⟩
  exact key (hfrob _) (hfrob _) h'' e

end ZInQ.Contrib.CloudB3RC53.ModularWeil

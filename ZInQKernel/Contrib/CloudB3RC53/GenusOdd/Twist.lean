import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-!
# GenusOdd: the twist embedding (PROVED)

* `twistEmb_injective`: `ψ_s : E^{(d)}(ℚ) → E(H)` is injective.
* `twistEmb_some`: in coordinates `ψ_s(X, Y) = (X / s², Y / s³)`.
* `map_twistEmb`: `g(ψ_s P) = ψ_{g s} P` for every `g : H →ₐ[ℚ] H`.
* `twistEmb_neg`: `ψ_{-s} = -ψ_s`.
Hence `g(ψ_s P) = ε_s(g) ψ_s P` with `ε_s(g) = ±1` according as `g s = ±s`
(`map_twistEmb_eq_ite`): the image of `E^{(d)}(ℚ)` lies in the `ε_s`-eigenspace.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

variable {H : Type*} [Field H] [Algebra ℚ H] [DecidableEq H]
variable (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (d : ℚ)

theorem twistEmb_injective (s : H)
    (heq : twistVC s • E.baseChange H = (qtwist E d).baseChange H) :
    Function.Injective (twistEmb E d s heq) := by
  intro a b hab
  unfold twistEmb at hab
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply] at hab
  exact (WeierstrassCurve.Affine.Point.equivBaseChangeSelf _).injective
    (WeierstrassCurve.Affine.Point.map_injective _ ((AddEquiv.cast _).injective
      ((WeierstrassCurve.Affine.Point.addEquivVariableChange _ _).injective hab)))

theorem twistEmb_zero (s : H)
    (heq : twistVC s • E.baseChange H = (qtwist E d).baseChange H) :
    twistEmb E d s heq 0 = 0 := map_zero _

omit [Algebra ℚ H] [DecidableEq H] in
theorem exists_some_eq {W : WeierstrassCurve H} {A B A' B' : H} (p : W.toAffine.Nonsingular A B)
    (hA : A = A') (hB : B = B') :
    ∃ h' : W.toAffine.Nonsingular A' B', (WeierstrassCurve.Affine.Point.some A B p) = .some A' B' h' := by
  subst hA hB; exact ⟨p, rfl⟩

include h₁ h₃ in
/-- `ψ_s(X, Y) = (X / s², Y / s³)` (PROVED). -/
theorem twistEmb_some {s : H} (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d)
    {X Y : ℚ} (h : (qtwist E d).toAffine.Nonsingular X Y) :
    ∃ h' : (E.baseChange H).toAffine.Nonsingular ((algebraMap ℚ H X) / s ^ 2)
        ((algebraMap ℚ H Y) / s ^ 3),
      twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) (.some X Y h) = .some _ _ h' := by
  unfold twistEmb
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
    WeierstrassCurve.Affine.Point.equivBaseChangeSelf_some, WeierstrassCurve.Affine.Point.map_some,
    AddEquiv.cast_apply]
  rw [WeierstrassCurve.Affine.Point.cast_some, WeierstrassCurve.Affine.Point.coe_addEquivVariableChange,
    WeierstrassCurve.Affine.Point.equivVariableChange_some]
  apply exists_some_eq
  · simp only [twistVC, dif_neg hs, Units.val_mk0, Algebra.ofId_apply]
    field_simp
    simp
  · simp only [twistVC, dif_neg hs, Units.val_mk0, Algebra.ofId_apply]
    field_simp
    simp
  · exact (twistVC_smul E h₁ h₃ hs hsd).symm

include h₁ h₃ in
/-- **Galois equivariance of the twist embedding** (PROVED): `g(ψ_s P) = ψ_{g s} P`. -/
theorem map_twistEmb (g : H →ₐ[ℚ] H) {s : H} (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d)
    (hs' : g s ≠ 0) (hsd' : g s ^ 2 = algebraMap ℚ H d) (P : (qtwist E d).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g
        (twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P) =
      twistEmb E d (g s) (twistVC_smul E h₁ h₃ hs' hsd') P := by
  rcases P with _ | ⟨X, Y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero, map_zero]
  · obtain ⟨h', e⟩ := twistEmb_some E h₁ h₃ d hs hsd h
    obtain ⟨h'', e'⟩ := twistEmb_some E h₁ h₃ d hs' hsd' h
    rw [e, e', WeierstrassCurve.Affine.Point.map_some]
    simp only [map_div₀, map_pow, AlgHom.commutes]

include h₁ h₃ in
/-- `ψ_{-s} = -ψ_s` (PROVED). -/
theorem twistEmb_neg {s : H} (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d)
    (hs' : -s ≠ 0) (hsd' : (-s) ^ 2 = algebraMap ℚ H d) (P : (qtwist E d).toAffine.Point) :
    twistEmb E d (-s) (twistVC_smul E h₁ h₃ hs' hsd') P =
      -twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P := by
  rcases P with _ | ⟨X, Y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def, map_zero, map_zero, neg_zero]
  · obtain ⟨h', e⟩ := twistEmb_some E h₁ h₃ d hs hsd h
    obtain ⟨h'', e'⟩ := twistEmb_some E h₁ h₃ d hs' hsd' h
    rw [e, e', WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.negY,
      WeierstrassCurve.baseChange, WeierstrassCurve.map, h₁, h₃, map_zero, zero_mul, sub_zero]
    congr 1 <;> ring

include h₁ h₃ in
/-- **The image of `E^{(d)}(ℚ)` is in the `ε_s`-eigenspace** (PROVED): if `g s = ±s` then
`g(ψ_s P) = ±ψ_s P`. -/
theorem map_twistEmb_eq_ite (g : H →ₐ[ℚ] H) {s : H} (hs : s ≠ 0)
    (hsd : s ^ 2 = algebraMap ℚ H d) (hg : g s = s ∨ g s = -s) (P : (qtwist E d).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g
        (twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P) =
      if g s = s then twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P
        else -twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P := by
  have hs' : g s ≠ 0 := by rcases hg with h | h <;> rw [h] <;> simpa using hs
  have hsd' : g s ^ 2 = algebraMap ℚ H d := by rcases hg with h | h <;> rw [h] <;> simp [hsd]
  rw [map_twistEmb E h₁ h₃ d g hs hsd hs' hsd']
  split_ifs with h
  · simp only [h]
  · have hneg : g s = -s := hg.resolve_left h
    have hs'' : -s ≠ 0 := by simpa using hs
    have hsd'' : (-s) ^ 2 = algebraMap ℚ H d := by simp [hsd]
    rw [← twistEmb_neg E h₁ h₃ d hs hsd hs'' hsd'']
    simp only [hneg]

end ZInQ.Contrib.CloudB3RC53.GenusOdd

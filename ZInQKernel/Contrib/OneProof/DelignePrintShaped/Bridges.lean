import ZInQKernel.Contrib.OneProof.DelignePrintShaped.Prints

/-! # The row `deligneCanonicalModelY3EveryPrint` from its print-shaped statements: bridges

Proved here (standard axioms only):

* **the level marking** (`levelObj`, `isLevelTorusAt_levelObj`): on `(A_τ, ι_τ)` the points
  `η_w(a) = Φu(ℓ_τ(a w)/3)` form a full level-3 structure in the kernel's sense when `w` is a unit modulo `3`
  (the lattice computation behind Shimura 1961, Prop. 4.1);
* `exists_invModThree`: every `u ∈ 𝒪̂^×` has a `w ∈ 𝒪` with `w ≡ u⁻¹ (mod 3)`;
* `exists_levelPoint_unit`: from T2a, the moduli object of `[τ, u]` (`τ ∈ ℍ`, `u ∈ 𝒪̂^×`) exists and is in the
  print's `H₁` form `Y3Hodge.IsHodgeH1Print` (through the proved dictionary `Y3Hodge.print_of_lattice`);
* **B2.4** (`recip_kernel_of_cv`): Cornut–Vatsal's normalization (`σ = rec_K(λ)`, uniformizers to geometric
  Frobenius) gives the kernel's (`ArtinCondC`, arithmetic) with the sign `−ε`;
* **B2.2 and the discharge** (`deligneCanonicalModelY3EveryPrint_of_prints`): T2a, T2b and W-a give the row on
  every witness, with `Ψ := f⁻¹ ∘ ψ`.
-/

set_option autoImplicit false

noncomputable section

namespace DelignePS

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)
open Y3Hodge (HPM DCRelPM toPM)
open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj

/-! ## 1. Small facts on `𝒪̂^×`, `K₃` and `DCRelPM` -/

theorem one_mem_OhatU : (1 : BAQˣ) ∈ OhatU :=
  ⟨by simpa using OhatQ_one, by simpa using OhatQ_one⟩

theorem dcRelPM_refl (z : HPM) (g : BAQˣ) : DCRelPM z g z g := by
  have h1 : ShimuraGlue.nrdQ ℚ (1 : B) ≠ 0 := by simp [ShimuraGlue.nrdQ_apply]
  refine ⟨1, h1, ?_, 1, K3Q_one, by simp⟩
  rw [Y3Hodge.iotaGL_eq_one h1 rfl, Y3Hodge.mobPM_one]

theorem K3Q_mul {k k' : BAQˣ} (hk : k ∈ K3Q) (hk' : k' ∈ K3Q) : k * k' ∈ K3Q := by
  obtain ⟨h1, h2, y, hy, hky⟩ := hk
  obtain ⟨h1', h2', y', hy', hky'⟩ := hk'
  refine ⟨?_, ?_, y + y' + 3 * y * y', ?_, ?_⟩
  · simpa only [Units.val_mul] using OhatQ_mul h1 h1'
  · rw [mul_inv_rev]
    simpa only [Units.val_mul] using OhatQ_mul h2' h2
  · exact OhatQ_add (OhatQ_add hy hy') (OhatQ_mul (OhatQ_mul (by exact_mod_cast OhatQ_natCast 3) hy) hy')
  · simp only [Units.val_mul, hky, hky']
    noncomm_ring

theorem K3Q_inv {k : BAQˣ} (hk : k ∈ K3Q) : k⁻¹ ∈ K3Q := by
  obtain ⟨h1, h2, y, hy, hky⟩ := hk
  refine ⟨h2, by simpa only [inv_inv] using h1, -(y * ((k⁻¹ : BAQˣ) : BAQ)), OhatQ_neg (OhatQ_mul hy h2), ?_⟩
  have e : (k : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) = 1 := by simp
  rw [hky] at e
  calc ((k⁻¹ : BAQˣ) : BAQ) = (1 + 3 * y) * ((k⁻¹ : BAQˣ) : BAQ) - 3 * (y * ((k⁻¹ : BAQˣ) : BAQ)) := by
        noncomm_ring
    _ = 1 + 3 * -(y * ((k⁻¹ : BAQˣ) : BAQ)) := by rw [e]; noncomm_ring

/-- `DCRelPM` is symmetric. -/
theorem dcRelPM_symm {z z' : HPM} {g g' : BAQˣ} (h : DCRelPM z g z' g') : DCRelPM z' g' z g := by
  obtain ⟨gm, hγ, hmob, k, hk, hg⟩ := h
  have hb : ShimuraGlue.nrdQ ℚ (binv gm) ≠ 0 := nrd_ne_zero_of_mul (binv_mul hγ)
  refine ⟨binv gm, hb, ?_, k⁻¹, K3Q_inv hk, ?_⟩
  · rw [← hmob, ← Y3Hodge.mobPM_mul, ← Y3Hodge.iotaGL_mul _ _ hb hγ (Y3Hodge.nrd_mul_ne _ _ hb hγ),
      Y3Hodge.iotaGL_eq_one _ (binv_mul hγ), Y3Hodge.mobPM_one]
  · rw [hg]
    have e1 : bEmb (binv gm) * bEmb gm = 1 := by rw [← map_mul, binv_mul hγ, map_one]
    have e2 : (k : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) = 1 := by simp
    calc (g : BAQ) = (bEmb (binv gm) * bEmb gm) * (g : BAQ) * ((k : BAQ) * ((k⁻¹ : BAQˣ) : BAQ)) := by
          rw [e1, e2, _root_.one_mul, _root_.mul_one]
      _ = bEmb (binv gm) * (bEmb gm * (g : BAQ) * (k : BAQ)) * ((k⁻¹ : BAQˣ) : BAQ) := by noncomm_ring

/-- `DCRelPM` is transitive. -/
theorem dcRelPM_trans {z₁ z₂ z₃ : HPM} {g₁ g₂ g₃ : BAQˣ} (h₁ : DCRelPM z₁ g₁ z₂ g₂)
    (h₂ : DCRelPM z₂ g₂ z₃ g₃) : DCRelPM z₁ g₁ z₃ g₃ := by
  obtain ⟨a, ha, hma, k, hk, hg⟩ := h₁
  obtain ⟨b, hb, hmb, k', hk', hg'⟩ := h₂
  have hab : ShimuraGlue.nrdQ ℚ (b * a) ≠ 0 := Y3Hodge.nrd_mul_ne _ _ hb ha
  refine ⟨b * a, hab, ?_, k * k', K3Q_mul hk hk', ?_⟩
  · rw [Y3Hodge.iotaGL_mul _ _ hb ha hab, Y3Hodge.mobPM_mul, hma, hmb]
  · rw [hg', hg, Units.val_mul, map_mul]
    noncomm_ring

/-! ## 2. `w ≡ u⁻¹ (mod 3)` -/

theorem ofQ_add (m n : Fin 4 → AQ) :
    ShimuraGlue.ofQ (m + n) = ShimuraGlue.ofQ m + ShimuraGlue.ofQ n := by
  ext <;> simp [ShimuraGlue.ofQ] <;> ring

theorem ofQ_three_mul (n : Fin 4 → AQ) :
    ShimuraGlue.ofQ (fun i => (3 : AQ) * n i) = 3 * ShimuraGlue.ofQ n := by
  have h := natCast_mul_ofQ 3 n
  push_cast at h
  exact h.symm

/-- Every `u ∈ 𝒪̂^×` has `w ∈ 𝒪` with `w u ∈ 1 + 3𝒪̂`: approximate the coordinates of `u⁻¹ ∈ 𝒪̂` by integers
modulo `3` (`RayClassCFT.exists_int_approx`). -/
theorem exists_invModThree {u : BAQˣ} (hu : u ∈ OhatU) : ∃ w : O, InvModThree u w := by
  obtain ⟨n, hn, he⟩ := hu.2
  choose m b hb hab using fun i => exists_int_approx (hn i) 3 (by norm_num)
  refine ⟨⟨LeafQM.ofInt m, ⟨m, rfl⟩⟩, -(ShimuraGlue.ofQ b * (u : BAQ)), ?_, ?_⟩
  · exact OhatQ_neg (OhatQ_mul ⟨b, hb, rfl⟩ hu.1)
  · have hinv : ((u⁻¹ : BAQˣ) : BAQ) =
        bEmb (LeafQM.ofInt m) + 3 * ShimuraGlue.ofQ b := by
      rw [he, bEmb_ofInt, ← ofQ_three_mul, ← ofQ_add]
      congr 1
      funext i
      simp only [Pi.add_apply]
      rw [hab i]
      norm_num
    have h1 : bEmb (LeafQM.ofInt m) = ((u⁻¹ : BAQˣ) : BAQ) - 3 * ShimuraGlue.ofQ b := by
      rw [hinv]; noncomm_ring
    show bEmb (LeafQM.ofInt m) * (u : BAQ) = 1 + 3 * -(ShimuraGlue.ofQ b * (u : BAQ))
    rw [h1, sub_mul, Units.inv_mul]
    noncomm_ring

/-! ## 3. The level marking on `(A_τ, ι_τ)` (the lattice computation behind Shimura 1961, Prop. 4.1) -/

section Marking

variable {A : PkgI3.AbVar ℂ} {q : QMStr A} {τ : UpperHalfPlane} {Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)}

/-- `ℓ_τ(b) = ι(b)(τ, 1)ᵀ` on `B`. -/
abbrev ell (τ : UpperHalfPlane) (b : B) : Fin 2 → ℂ := Y3Fix.ellE τ (BPAnalytic.QM.iota b)

theorem ell_add (b c : B) : ell τ (b + c) = ell τ b + ell τ c := by
  simp only [ell, RayClassCFT.iota_add, map_add]

theorem ell_zero : ell τ (0 : B) = 0 := by
  have h := ell_add (τ := τ) (0 : B) 0
  simp only [add_zero] at h
  exact left_eq_add.1 h

theorem ell_ratSmul (r : ℚ) (b : B) : ell τ (r • b) = (r : ℂ) • ell τ b := by
  simp only [ell, RayClassCFT.iota_smul, map_smul]
  rw [← Complex.coe_smul]
  norm_cast

theorem ell_mul (a : O) (b : B) : ell τ ((a : B) * b) = (qmMat a).mulVec (ell τ b) := by
  simp only [ell, RayClassCFT.iota_mul]
  exact Y3Fix.ellE_iota τ a _

/-- `ℓ_τ(b) ∈ Λ_τ` iff `b ∈ 𝒪`. -/
theorem ell_mem_iff (b : B) : ell τ b ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔ b ∈ O := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ _).1 h
    have h1 : BPAnalytic.QM.latVec b (τ : ℂ) = BPAnalytic.QM.latVec c (τ : ℂ) := by
      rw [Y3Fix.latVec_eq]; exact he
    have := RayClassCFT.iota_eig_inj τ.im_pos.ne' h1
    rw [this]; exact hc
  · intro hb
    exact (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ _).2 ⟨b, hb, (Y3Fix.latVec_eq τ b).symm⟩

theorem third_smul_ell (b : B) : (3 : ℂ)⁻¹ • ell τ b = ell τ ((3 : ℚ)⁻¹ • b) := by
  rw [ell_ratSmul]; norm_num

theorem three_mul_inv_smul_B (y : B) : (3 : B) * ((3 : ℚ)⁻¹ • y) = y := by
  rw [mul_smul_comm, show (3 : B) * y = (3 : ℚ) • y by rw [Algebra.smul_def, map_ofNat], smul_smul]
  norm_num

theorem inv_smul_three_mul_BAQ (Z : BAQ) : (3 : ℚ)⁻¹ • ((3 : BAQ) * Z) = Z := by
  rw [show (3 : BAQ) * Z = (3 : ℚ) • Z by rw [Algebra.smul_def, map_ofNat], smul_smul]
  norm_num

/-- If `w u ∈ 1 + 3𝒪̂` with `u ∈ 𝒪̂^×`, then `a w ∈ 3𝒪` forces `a ∈ 3𝒪`: `a = a w u − 3 a y`. -/
theorem mem_three_of_mul {u : BAQˣ} (hu : u ∈ OhatU) {w : O} (hw : InvModThree u w) (a : O)
    (h : (3 : ℚ)⁻¹ • ((a : B) * (w : B)) ∈ O) : ∃ b : O, a = 3 * b := by
  obtain ⟨y, hy, hwu⟩ := hw
  set x : B := (3 : ℚ)⁻¹ • ((a : B) * (w : B)) with hx
  have h3x : (a : B) * (w : B) = 3 * x := by rw [hx, three_mul_inv_smul_B]
  have e2 : bEmb (a : B) * bEmb (w : B) = 3 * bEmb x := by
    rw [← map_mul, h3x, map_mul, map_ofNat]
  have e1 : bEmb (a : B) = 3 * (bEmb x * (u : BAQ) - bEmb (a : B) * y) := by
    calc bEmb (a : B) = bEmb (a : B) * (bEmb (w : B) * (u : BAQ)) - bEmb (a : B) * (3 * y) := by
          rw [hwu]; noncomm_ring
      _ = (bEmb (a : B) * bEmb (w : B)) * (u : BAQ) - bEmb (a : B) * (3 * y) := by noncomm_ring
      _ = 3 * (bEmb x * (u : BAQ) - bEmb (a : B) * y) := by rw [e2]; noncomm_ring
  have key : bEmb ((3 : ℚ)⁻¹ • (a : B)) = bEmb x * (u : BAQ) - bEmb (a : B) * y := by
    rw [map_smul]
    conv_lhs => rw [e1]
    rw [inv_smul_three_mul_BAQ]
  have hmem : bEmb ((3 : ℚ)⁻¹ • (a : B)) ∈ OhatQ := by
    rw [key, sub_eq_add_neg]
    exact OhatQ_add (OhatQ_mul (bEmb_mem_of_inO h) hu.1) (OhatQ_neg (OhatQ_mul (bEmb_mem_of_inO a.2) hy))
  refine ⟨⟨(3 : ℚ)⁻¹ • (a : B), inO_of_bEmb_mem hmem⟩, Subtype.ext ?_⟩
  show (a : B) = ((3 : O) : B) * ((3 : ℚ)⁻¹ • (a : B))
  rw [show ((3 : O) : B) = (3 : B) from rfl, three_mul_inv_smul_B]

/-- **The level points `η_w(a) = Φu(ℓ_τ(a w)/3)`** on `ℂ²/Λ_τ`. -/
def etaW (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu) (w : O) :
    O →+ Additive (A.Pt ℂ) where
  toFun a := Additive.ofMul (Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))))
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, zero_mul, ell_zero, smul_zero]
    rw [(hU.2.1 0).2 (Submodule.zero_mem _)]
    rfl
  map_add' a b := by
    simp only [Subring.coe_add, add_mul, ell_add, smul_add]
    rw [hU.1]
    rfl

theorem etaW_apply (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu) (w a : O) :
    Additive.toMul (etaW hU w a) = Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) := rfl

theorem etaW_linear (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hι : ∀ (a : O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (q.iota a).hom) (w a b : O) :
    Additive.toMul (etaW hU w (a * b)) = Additive.toMul (etaW hU w b) ≫ (q.iota a).hom := by
  rw [etaW_apply, etaW_apply, Subring.coe_mul, _root_.mul_assoc, ell_mul, ← Matrix.mulVec_smul]
  exact hι a _

theorem etaW_eq_zero_iff (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    {u : BAQˣ} (hu : u ∈ OhatU) {w : O} (hw : InvModThree u w) (a : O) :
    etaW hU w a = 0 ↔ ∃ b : O, a = 3 * b := by
  have h0 : etaW hU w a = 0 ↔ Φu ((3 : ℂ)⁻¹ • ell τ ((a : B) * (w : B))) = 1 := Iff.rfl
  rw [h0, hU.2.1, third_smul_ell, ell_mem_iff]
  constructor
  · exact mem_three_of_mul hu hw a
  · rintro ⟨b, rfl⟩
    have e : (3 : ℚ)⁻¹ • (((3 * b : O) : B) * (w : B)) = (b : B) * (w : B) := by
      rw [Subring.coe_mul, show ((3 : O) : B) = (3 : B) from rfl, _root_.mul_assoc,
        show (3 : B) * ((b : B) * (w : B)) = (3 : ℚ) • ((b : B) * (w : B)) by rw [Algebra.smul_def, map_ofNat],
        smul_smul]
      norm_num
    rw [e]
    exact (b * w).2

end Marking


/-! ## 4. The moduli objects `(ℂ²/Λ_τ, ι_τ, η_w)` and the moduli clause at units -/

/-- The level structure `η_w` on `(A_τ, ι_τ)`, for `w ≡ u⁻¹ (mod 3)`, `u ∈ 𝒪̂^×`. -/
def levelW {A : PkgI3.AbVar ℂ} {q : QMStr A} {τ : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hι : ∀ (a : O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (q.iota a).hom)
    {u : BAQˣ} (hu : u ∈ OhatU) (w : O) (hw : InvModThree u w) : Level3 q where
  eta := etaW hU w
  linear a b := by
    apply Additive.toMul.injective
    rw [etaW_linear hU hι]
    rfl
  ker a := etaW_eq_zero_iff hU hu hw a

/-- **The moduli object of `[τ, u]`** from a presentation `(A, ι) ≅ (A_τ, ι_τ)`. -/
def levelObj {A : PkgI3.AbVar ℂ} (hA : A.dim = 2) {q : QMStr A} {τ : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hι : ∀ (a : O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (q.iota a).hom)
    {u : BAQˣ} (hu : u ∈ OhatU) (w : O) (hw : InvModThree u w) : QML3 ℂ :=
  ⟨A, hA, q, levelW hU hι hu w hw⟩

theorem isLevelTorusAt_levelObj {A : PkgI3.AbVar ℂ} (hA : A.dim = 2) {q : QMStr A} {τ : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hι : ∀ (a : O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (q.iota a).hom)
    {u : BAQˣ} (hu : u ∈ OhatU) (w : O) (hw : InvModThree u w) :
    IsLevelTorusAt (levelObj hA hU hι hu w hw) τ w :=
  ⟨Φu, hU, hι, fun a => by rw [Subring.coe_mul]; rfl⟩

/-- **The moduli object of `[τ, u]` exists, and it is in the print's `H₁` form** (T2a's first clause, the level
marking, and the proved dictionary `Y3Hodge.print_of_lattice`). -/
theorem exists_levelPoint_unit (hV : VoightQMComplexModuliPrint) (τ : UpperHalfPlane) {u : BAQˣ}
    (hu : u ∈ OhatU) : ∃ P : QML3 ℂ, IsLevelPoint P (toPM τ) u ∧ Y3Hodge.IsHodgeH1Print P τ := by
  obtain ⟨A, hA, q, Φu, hU, hι⟩ := hV.1 τ
  obtain ⟨w, hw⟩ := exists_invModThree hu
  refine ⟨levelObj hA hU hι hu w hw, ⟨τ, u, w, hu, dcRelPM_refl _ _, hw,
    isLevelTorusAt_levelObj hA hU hι hu w hw⟩, ?_⟩
  exact Y3Hodge.print_of_lattice uniformizationLeafAll_proof hU hι

/-- Every point of `ℍ^± × (B ⊗ 𝔸_f)^×` is related to some `(τ, u)` with `τ ∈ ℍ` and `u ∈ 𝒪̂^×`
(`Y3Hodge.exists_upper` and class number one, `RayClassCFT.classNumberOneB_proof`). -/
theorem exists_unit_rep (z : HPM) (g : BAQˣ) :
    ∃ (τ : UpperHalfPlane) (u : BAQˣ), u ∈ OhatU ∧ DCRelPM z g (toPM τ) u := by
  obtain ⟨τ₀, g₀, h₀⟩ := Y3Hodge.exists_upper z g
  obtain ⟨gam, hgam, u, hu, hg⟩ := exists_pos_decomp classNumberOneB_proof g₀
  exact ⟨_, u, hu, dcRelPM_trans h₀ ((Y3Hodge.dcRelPM_iff _ _ _ _).2 (dcRel_of_decomp hgam τ₀ hg))⟩

/-- **The moduli object of every point `[z, g]` exists** (T2a's first clause). -/
theorem exists_levelPoint (hV : VoightQMComplexModuliPrint) (z : HPM) (g : BAQˣ) :
    ∃ P : QML3 ℂ, IsLevelPoint P z g := by
  obtain ⟨τ, u, hu, hr⟩ := exists_unit_rep z g
  obtain ⟨P, ⟨τ', u', w, hu', hr', hw, hT⟩, -⟩ := exists_levelPoint_unit hV τ hu
  exact ⟨P, τ', u', w, hu', dcRelPM_trans hr hr', hw, hT⟩

/-! ## 4b. B2.1: the complex clauses on every witness from the level-3 classification over `ℂ` -/

/-- **Every complex QM surface with full level-3 structure is the moduli object of some point** (the onto half of
the level-3 classification over `ℂ`; from T2a's second clause and the classification of level structures on
`ℂ²/Λ_τ`). -/
def LevelOnto : Prop := ∀ P : QML3 ℂ, ∃ (z : HPM) (g : BAQˣ), IsLevelPoint P z g

/-- **Two moduli objects are isomorphic exactly when their points are in one double coset** (the fibre half of the
level-3 classification over `ℂ`). -/
def LevelClassification : Prop :=
  ∀ (P P' : QML3 ℂ) (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ), IsLevelPoint P z g → IsLevelPoint P' z' g' →
    (M3.mk P = M3.mk P' ↔ DCRelPM z g z' g')

/-- **B2.1.** On every `ℚ`-scheme `Y` with moduli bijections `Φ`, `Ψ := (Φ ℂ)⁻¹ ∘ [X]` (`X(z, g)` the moduli object
of `[z, g]`) is onto, has fibres exactly the double cosets (both directions, so cmj's reverse fibre clause at CM
points too), sends `[z, g]` to the class of its moduli object, and satisfies the moduli clause in the print's
`H₁` form at `g = 1` and at every `u ∈ 𝒪̂^×`. No model identification is used. -/
theorem moduli_clauses_of_print (hV : VoightQMComplexModuliPrint) (hO : LevelOnto) (hC : LevelClassification)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    ∃ Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y),
      (∀ y : fieldPt ℂ ⟶ Y, ∃ z g, Ψ z g = y) ∧
      (∀ z g z' g', Ψ z g = Ψ z' g' ↔ DCRelPM z g z' g') ∧
      (∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (Ψ z g) = M3.mk P) ∧
      (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ (toPM τ) 1) = M3.mk P ∧ Y3Hodge.IsHodgeH1Print P τ) ∧
      Y3Hodge.ModuliAtUnitsHP Y Φ Ψ := by
  choose X hX using exists_levelPoint hV
  have hmk : ∀ z g (P : QML3 ℂ), IsLevelPoint P z g → M3.mk (X z g) = M3.mk P := fun z g P hP =>
    (hC _ _ _ _ _ _ (hX z g) hP).2 (dcRelPM_refl z g)
  refine ⟨fun z g => (Φ ℂ).symm (M3.mk (X z g)), fun y => ?_, fun z g z' g' => ?_, fun z g P hP => ?_,
    fun τ => ?_, fun u hu τ => ?_⟩
  · obtain ⟨z, g, hP⟩ := hO (Quotient.out (Φ ℂ y))
    refine ⟨z, g, ?_⟩
    show (Φ ℂ).symm (M3.mk (X z g)) = y
    rw [hmk z g _ hP, show M3.mk (Quotient.out ((Φ ℂ) y)) = (Φ ℂ) y from Quotient.out_eq _,
      Equiv.symm_apply_apply]
  · rw [(Φ ℂ).symm.injective.eq_iff]
    exact hC _ _ _ _ _ _ (hX z g) (hX z' g')
  · rw [Equiv.apply_symm_apply, hmk z g P hP]
  · obtain ⟨P, hP, hH⟩ := exists_levelPoint_unit hV τ one_mem_OhatU
    exact ⟨P, by rw [Equiv.apply_symm_apply, hmk _ _ P hP], hH⟩
  · obtain ⟨P, hP, hH⟩ := exists_levelPoint_unit hV τ hu
    exact ⟨P, by rw [Equiv.apply_symm_apply, hmk _ _ P hP], hH⟩

/-! ## 5. B2.4: Cornut–Vatsal's normalization versus the kernel's -/

/-- **B2.4.** Cornut–Vatsal's `σ = rec_K(λ)` (uniformizers to geometric Frobenius) is the kernel's
`ArtinCondC κ σ λ⁻¹` (Tau Ceti's `art_K`, uniformizers to arithmetic Frobenius), so their `λ^ε` is the kernel's
`q̂(s)^{−ε}` for `σ = art_K(s)`. -/
theorem recip_kernel_of_cv {M : Over (Spec (CommRingCat.of ℚ))} {ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)}
    {ε : ℤˣ} {δ : Bool} (h : CVReciprocityAt M ψ ε δ) :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] B) (z : UpperHalfPlane),
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
    ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
    ∀ g : BAQˣ, galPt σ (ψ (toPM z) g) = ψ (toPM z) (qHatU q s ^ ((-ε : ℤˣ) : ℤ) * g) := by
  intro K _ _ _ hK κ q z hz σ s hs g
  have h1 := h K hK κ q z hz σ s⁻¹ (by rwa [inv_inv]) g
  rw [h1, map_inv, inv_zpow, Units.val_neg, zpow_neg]

/-! ## 6. B2.2 and the discharge -/

/-- **The discharge.** T2a (its first clause: every period gives a QM surface), T2b (Cornut–Vatsal at `K₃`) and the
GLUE W-a give `Y3Hodge.DeligneCanonicalModelY3EveryPrint`. On a witness `(Y, Φ)`, W-a gives `f : Y ≅ M` with
`ψ = f ∘ Ψ_mod`; put `Ψ := f⁻¹ ∘ ψ`. Onto, the fibres and holomorphy come from Cornut–Vatsal §3.1.1 (through
`f`, `Y3ABUPrint.isHolFamily_comp`); the moduli clause at every `u ∈ 𝒪̂^×` from T2a and the level marking; the
reciprocity law from Lemma 3.11 through B2.4 (with `−ε`). -/
theorem deligneCanonicalModelY3EveryPrint_of_prints (hV : VoightQMComplexModuliPrint)
    (hB : CornutVatsalCMReciprocityPrint) (hW : FineModuliCanonicalModelGlue) :
    Y3Hodge.DeligneCanonicalModelY3EveryPrint := by
  intro Y Φ hY
  obtain ⟨M, ψ, hsm, hunif, ε, δ, hrec⟩ := hB
  obtain ⟨f, hf⟩ := hW M ψ hsm hunif ⟨ε, δ, hrec⟩ Y Φ hY
  have hΨ : ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (ψ z g ≫ f.inv) = M3.mk P := by
    intro z g P hP
    rw [hf z g P hP, Category.assoc, Iso.hom_inv_id, Category.comp_id, Equiv.apply_symm_apply]
  have hhol : ∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (ψ (toPM τ) g ≫ f.inv).left) :=
    fun g => Y3ABUPrint.isHolFamily_comp f.inv.left (hunif.2.2 g)
  refine ⟨fun z g => ψ z g ≫ f.inv, ⟨fun y => ?_, fun z g z' g' => ?_, hhol, ⟨fun τ => ?_, hhol 1⟩, ?_⟩,
    fun u hu τ => ?_⟩
  · obtain ⟨z, g, h⟩ := hunif.1 (y ≫ f.hom)
    exact ⟨z, g, by show ψ z g ≫ f.inv = y; rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  · rw [← hunif.2.1]
    constructor
    · intro h
      simpa using congrArg (· ≫ f.hom) h
    · intro h
      show ψ z g ≫ f.inv = ψ z' g' ≫ f.inv
      rw [h]
  · obtain ⟨P, hP, hH⟩ := exists_levelPoint_unit hV τ one_mem_OhatU
    exact ⟨P, hΨ _ _ P hP, hH⟩
  · refine ⟨-ε, δ, fun K _ _ _ hK κ q z hz σ s hs g => ?_⟩
    show fieldMap _ ≫ ψ (toPM z) g ≫ f.inv = ψ (toPM z) _ ≫ f.inv
    rw [← Category.assoc]
    exact congrArg (· ≫ f.inv) (recip_kernel_of_cv hrec K hK κ q z hz σ s hs g)
  · obtain ⟨P, hP, hH⟩ := exists_levelPoint_unit hV τ hu
    exact ⟨P, hΨ _ _ P hP, hH⟩

/-! ## 7. T2c gives the kernel's fine-moduli leaf -/

/-- Boutot–Carayol's statement (T2c) gives a witness of the printed fine-moduli clause list, i.e. the existing leaf
`Y3Fix.Y3FineModuliAbP`. -/
theorem y3FineModuliAbP_of_boutotCarayol (h : BoutotCarayolModuliPrint) : Y3Fix.Y3FineModuliAbP := by
  obtain ⟨S, ΦS, hS, -⟩ := h
  exact ⟨S, ΦS, hS⟩

end DelignePS

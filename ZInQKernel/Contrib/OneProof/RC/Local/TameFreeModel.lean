import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Triangular
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange

/-!
# Lane RC31, round 5: Elliot's tame local free model (4.4), its splitting, and the two-place block

Manuscript `diophantine_zq.tex`, tex 3470–3480: "At a tame split prime the local free model has
`d⁰(v) = (Av, Cv)`, `d¹(v, w) = −Cv + Dw`, `A = Φ − 1`, `C = g − 1`, `D = Φ − N_q(g)`,
`N_q(g) = (q+1)/2 + (q−1)/2 g`, `DC = CA` (4.4). At augmentation `g = 1`, this is the direct sum
of the unramified complex `[Φ − 1]` in degrees zero and one and the singular quotient `[Φ − q]` in
degrees one and two."

This file is the ALGEBRA of the model (all PROVED), over any commutative ring `A` and any
`A`-module `M` (in the application `A = A_i` a coefficient stage, or `Λ`, and `M` the stage
module at the place):

* `cx3`, `cx3Hom`: three-term complexes in degrees `0, 1, 2` and their maps;
* `freeModel A C D (hDC : D C = C A)`: `M --(A, C)--> M × M --(−C, D)--> M`;
* `tameNorm q g = (q+1)/2 + (q−1)/2 g` and `tame_DC_CA`: for commuting `Φ, g` with `g² = 1` and
  `q` odd, `D C = C A`; hence `tameFreeModel Φ g q` (Elliot's (4.4));
* at `g = 1` (`tameFreeModel1`): `tameNorm_one` (`N_q(1) = q`), the unramified complex
  `unrCx Φ = [M --Φ−1--> M]` (degrees 0, 1) and the singular block `singCx Φ q = [M --Φ−q--> M]`
  (degrees 1, 2); the chain maps `unrIncl`, `singProj`, `unrRetr`, `singSect` exhibit the model
  as the direct sum (`tame_split_directSum`), and the quotient by the unramified part is the
  singular block (`tame_split_exact_one`, `tame_split_exact_zero_two`);
* `tameNewPlace`: the model at `g = 1` as the new-place data `UnramifiedNewPlace` of the support
  change;
* the cohomology of the model at `g = 1`: `H⁰ = ker(Φ − 1)` (`cohD0_eq_zero_iff`),
  `H¹ ≅ coker(Φ − 1) × ker(Φ − q)` (`tameH1Equiv`), `H² = coker(Φ − q)` (`cohD1_range`);
* two conjugate places with Frobenius values `z`, `z⁻¹` on `M = A²` and Frobenius matrix `F`:
  the two singular blocks together (`twoSingCx`) have the differential matrix
  `twoPlaceBlock F q z z⁻¹` in the standard basis of the two places (`twoSing_matrix`), the block
  of the common-coordinate support triangle (tex 4176–4184);
* naturality in `M` (`tameFreeModelMap`) and compatibility with stage transitions
  (`twoPlaceBlock_map`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable {A : Type} [CommRing A]

/-! ### Three-term complexes in degrees `0, 1, 2` -/

section Cx3

variable (X0 X1 X2 : Type) [AddCommGroup X0] [Module A X0] [AddCommGroup X1] [Module A X1]
  [AddCommGroup X2] [Module A X2]

/-- The terms of a three-term complex in degrees `0, 1, 2` (zero elsewhere). Kind:
definition. -/
def cx3X : ℤ → ModuleCat A
  | .ofNat 0 => ModuleCat.of A X0
  | .ofNat 1 => ModuleCat.of A X1
  | .ofNat 2 => ModuleCat.of A X2
  | _ => ModuleCat.of A PUnit

variable {X0 X1 X2}

/-- The differentials of a three-term complex. Kind: definition. -/
def cx3D (d0 : X0 →ₗ[A] X1) (d1 : X1 →ₗ[A] X2) :
    ∀ a b : ℤ, a + 1 = b → (cx3X (A := A) X0 X1 X2 a →ₗ[A] cx3X (A := A) X0 X1 X2 b)
  | .ofNat 0, .ofNat 1, _ => d0
  | .ofNat 1, .ofNat 2, _ => d1
  | _, _, _ => 0

/-- The differentials vanish outside degrees `0 → 1` and `1 → 2`. Kind: PROVED. -/
theorem cx3D_eq_zero (d0 : X0 →ₗ[A] X1) (d1 : X1 →ₗ[A] X2) (a b : ℤ) (h : a + 1 = b)
    (h0 : a ≠ 0) (h1 : a ≠ 1) : cx3D d0 d1 a b h = 0 := by
  rcases a with (_ | _ | a) | a
  · exact absurd rfl h0
  · exact absurd rfl h1
  · rcases b with (_ | _ | _ | b) | b <;> rfl
  · rcases b with (_ | _ | _ | b) | b <;> rfl

/-- **A three-term complex** `X0 --d0--> X1 --d1--> X2` in degrees `0, 1, 2`. Kind: definition
(PROVED `d² = 0`). -/
def cx3 (d0 : X0 →ₗ[A] X1) (d1 : X1 →ₗ[A] X2) (h : ∀ x, d1 (d0 x) = 0) : GCx A where
  X := cx3X X0 X1 X2
  d := cx3D d0 d1
  d_d a b c hab hbc x := by
    by_cases h0 : a = 0
    · subst h0
      obtain rfl : b = 1 := by omega
      obtain rfl : c = 2 := by omega
      exact h x
    · by_cases h1 : a = 1
      · subst h1
        obtain rfl : b = 2 := by omega
        rw [cx3D_eq_zero d0 d1 2 c hbc (by decide) (by decide)]
        rfl
      · rw [cx3D_eq_zero d0 d1 a b hab h0 h1, LinearMap.zero_apply, map_zero]

/-- The differential of `cx3` from degree `0`. Kind: PROVED (definitional). -/
theorem cx3_d0 (d0 : X0 →ₗ[A] X1) (d1 : X1 →ₗ[A] X2) (h : ∀ x, d1 (d0 x) = 0) (x : X0) :
    (cx3 d0 d1 h).d 0 1 rfl x = d0 x :=
  rfl

/-- The differential of `cx3` from degree `1`. Kind: PROVED (definitional). -/
theorem cx3_d1 (d0 : X0 →ₗ[A] X1) (d1 : X1 →ₗ[A] X2) (h : ∀ x, d1 (d0 x) = 0) (x : X1) :
    (cx3 d0 d1 h).d 1 2 rfl x = d1 x :=
  rfl

/-- The components of a map of three-term complexes. Kind: definition. -/
def cx3HomF {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module A Y0] [AddCommGroup Y1] [Module A Y1]
    [AddCommGroup Y2] [Module A Y2] (f0 : X0 →ₗ[A] Y0) (f1 : X1 →ₗ[A] Y1) (f2 : X2 →ₗ[A] Y2) :
    ∀ n : ℤ, cx3X (A := A) X0 X1 X2 n →ₗ[A] cx3X (A := A) Y0 Y1 Y2 n
  | .ofNat 0 => f0
  | .ofNat 1 => f1
  | .ofNat 2 => f2
  | _ => 0

/-- **A map of three-term complexes** from three maps commuting with the differentials. Kind:
definition (PROVED chain property). -/
def cx3Hom {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module A Y0] [AddCommGroup Y1] [Module A Y1]
    [AddCommGroup Y2] [Module A Y2] {d0 : X0 →ₗ[A] X1} {d1 : X1 →ₗ[A] X2}
    {h : ∀ x, d1 (d0 x) = 0} {e0 : Y0 →ₗ[A] Y1} {e1 : Y1 →ₗ[A] Y2} {h' : ∀ y, e1 (e0 y) = 0}
    (f0 : X0 →ₗ[A] Y0) (f1 : X1 →ₗ[A] Y1) (f2 : X2 →ₗ[A] Y2)
    (c0 : ∀ x, f1 (d0 x) = e0 (f0 x)) (c1 : ∀ x, f2 (d1 x) = e1 (f1 x)) :
    GHom (cx3 d0 d1 h) (cx3 e0 e1 h') where
  f i j hij := by
    subst hij
    exact cx3HomF f0 f1 f2 i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    by_cases e0' : i = 0
    · subst e0'
      obtain rfl : i₁ = 1 := by omega
      exact c0 x
    · by_cases e1' : i = 1
      · subst e1'
        obtain rfl : i₁ = 2 := by omega
        exact c1 x
      · have z1 : cx3D d0 d1 i i₁ h₁ = 0 := cx3D_eq_zero d0 d1 i i₁ h₁ e0' e1'
        have z2 : cx3D e0 e1 i i₁ h₂ = 0 := cx3D_eq_zero e0 e1 i i₁ h₂ e0' e1'
        change cx3HomF f0 f1 f2 i₁ (cx3D d0 d1 i i₁ h₁ x) =
          cx3D e0 e1 i i₁ h₂ (cx3HomF f0 f1 f2 i x)
        rw [z1, z2]
        exact (map_zero _).trans rfl

/-- The degree-zero component of `cx3Hom`. Kind: PROVED (definitional). -/
theorem cx3Hom_f0 {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module A Y0] [AddCommGroup Y1]
    [Module A Y1] [AddCommGroup Y2] [Module A Y2] {d0 : X0 →ₗ[A] X1} {d1 : X1 →ₗ[A] X2}
    {h : ∀ x, d1 (d0 x) = 0} {e0 : Y0 →ₗ[A] Y1} {e1 : Y1 →ₗ[A] Y2} {h' : ∀ y, e1 (e0 y) = 0}
    (f0 : X0 →ₗ[A] Y0) (f1 : X1 →ₗ[A] Y1) (f2 : X2 →ₗ[A] Y2) (c0 c1) (x : X0) :
    (cx3Hom (h := h) (h' := h') f0 f1 f2 c0 c1).f 0 0 rfl x = f0 x :=
  rfl

/-- The degree-one component of `cx3Hom`. Kind: PROVED (definitional). -/
theorem cx3Hom_f1 {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module A Y0] [AddCommGroup Y1]
    [Module A Y1] [AddCommGroup Y2] [Module A Y2] {d0 : X0 →ₗ[A] X1} {d1 : X1 →ₗ[A] X2}
    {h : ∀ x, d1 (d0 x) = 0} {e0 : Y0 →ₗ[A] Y1} {e1 : Y1 →ₗ[A] Y2} {h' : ∀ y, e1 (e0 y) = 0}
    (f0 : X0 →ₗ[A] Y0) (f1 : X1 →ₗ[A] Y1) (f2 : X2 →ₗ[A] Y2) (c0 c1) (x : X1) :
    (cx3Hom (h := h) (h' := h') f0 f1 f2 c0 c1).f 1 1 rfl x = f1 x :=
  rfl

/-- The degree-two component of `cx3Hom`. Kind: PROVED (definitional). -/
theorem cx3Hom_f2 {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module A Y0] [AddCommGroup Y1]
    [Module A Y1] [AddCommGroup Y2] [Module A Y2] {d0 : X0 →ₗ[A] X1} {d1 : X1 →ₗ[A] X2}
    {h : ∀ x, d1 (d0 x) = 0} {e0 : Y0 →ₗ[A] Y1} {e1 : Y1 →ₗ[A] Y2} {h' : ∀ y, e1 (e0 y) = 0}
    (f0 : X0 →ₗ[A] Y0) (f1 : X1 →ₗ[A] Y1) (f2 : X2 →ₗ[A] Y2) (c0 c1) (x : X2) :
    (cx3Hom (h := h) (h' := h') f0 f1 f2 c0 c1).f 2 2 rfl x = f2 x :=
  rfl

end Cx3

/-! ### The free model (4.4) -/

section FreeModel

variable {M : Type} [AddCommGroup M] [Module A M]

/-- The first differential `d⁰(v) = (Av, Cv)` of the free model (tex 3470–3474). Kind:
definition. -/
def freeD0 (Aop Cop : M →ₗ[A] M) : M →ₗ[A] M × M := Aop.prod Cop

/-- The second differential `d¹(v, w) = −Cv + Dw` of the free model (tex 3470–3474). Kind:
definition. -/
def freeD1 (Cop Dop : M →ₗ[A] M) : M × M →ₗ[A] M := (-Cop).coprod Dop

/-- `d¹ d⁰ = 0` when `D C = C A` (tex 3474). Kind: PROVED. -/
theorem freeD1_freeD0 (Aop Cop Dop : M →ₗ[A] M) (hDC : Dop ∘ₗ Cop = Cop ∘ₗ Aop) (v : M) :
    freeD1 Cop Dop (freeD0 Aop Cop v) = 0 := by
  have e := LinearMap.congr_fun hDC v
  change -Cop (Aop v) + Dop (Cop v) = 0
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
  rw [e, neg_add_cancel]

/-- **The local free model** `M --(A, C)--> M × M --(−C, D)--> M` in degrees `0, 1, 2`, for
`D C = C A` (tex 3470–3474). Kind: definition. -/
def freeModel (Aop Cop Dop : M →ₗ[A] M) (hDC : Dop ∘ₗ Cop = Cop ∘ₗ Aop) : GCx A :=
  cx3 (freeD0 Aop Cop) (freeD1 Cop Dop) (freeD1_freeD0 Aop Cop Dop hDC)

/-- **The tame norm** `N_q(g) = (q+1)/2 + (q−1)/2 · g` (tex 3472; for `g² = 1` and `q` odd it is
`1 + g + ⋯ + g^{q−1}`). Kind: definition. -/
def tameNorm (q : ℕ) (g : M →ₗ[A] M) : M →ₗ[A] M :=
  ((q + 1) / 2 : ℕ) • LinearMap.id + ((q - 1) / 2 : ℕ) • g

/-- For `g² = 1` and `q` odd, `N_q(g) (g − 1) = g − 1`. Kind: PROVED. -/
theorem tameNorm_comp_sub (q : ℕ) (hq : Odd q) (g : M →ₗ[A] M) (hg : g ∘ₗ g = LinearMap.id) :
    tameNorm q g ∘ₗ (g - LinearMap.id) = g - LinearMap.id := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  apply LinearMap.ext
  intro v
  have hv : g (g v) = v := LinearMap.congr_fun hg v
  simp only [tameNorm, h1, h2, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sub, hv]
  rw [add_smul, one_smul, add_smul, one_smul]
  abel

/-- **`D C = C A` for the tame model** (tex 3472–3474): for commuting `Φ, g` with `g² = 1` and
`q` odd, `(Φ − N_q(g))(g − 1) = (g − 1)(Φ − 1)`. Kind: PROVED. -/
theorem tame_DC_CA (Φ g : M →ₗ[A] M) (q : ℕ) (hq : Odd q) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hg : g ∘ₗ g = LinearMap.id) :
    (Φ - tameNorm q g) ∘ₗ (g - LinearMap.id) = (g - LinearMap.id) ∘ₗ (Φ - LinearMap.id) := by
  rw [LinearMap.sub_comp, tameNorm_comp_sub q hq g hg, LinearMap.comp_sub, LinearMap.comp_sub,
    LinearMap.sub_comp, LinearMap.sub_comp, hcomm]
  simp only [LinearMap.comp_id, LinearMap.id_comp]

/-- **Elliot's tame local free model** (4.4) (tex 3470–3474): `A = Φ − 1`, `C = g − 1`,
`D = Φ − N_q(g)`. Kind: definition. -/
def tameFreeModel (Φ g : M →ₗ[A] M) (q : ℕ) (hq : Odd q) (hcomm : Φ ∘ₗ g = g ∘ₗ Φ)
    (hg : g ∘ₗ g = LinearMap.id) : GCx A :=
  freeModel (Φ - LinearMap.id) (g - LinearMap.id) (Φ - tameNorm q g)
    (tame_DC_CA Φ g q hq hcomm hg)

/-- At `g = 1` the tame norm is `q`. Kind: PROVED. -/
theorem tameNorm_one (q : ℕ) (hq : Odd q) :
    tameNorm q (LinearMap.id : M →ₗ[A] M) = (q : A) • LinearMap.id := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [tameNorm, h1, h2, ← add_smul, Nat.cast_smul_eq_nsmul]
  congr 1
  omega

end FreeModel

/-! ### At augmentation `g = 1`: the unramified complex and the singular block -/

section Augmentation

variable {M : Type} [AddCommGroup M] [Module A M] (Φ : M →ₗ[A] M) (q : ℕ) (hq : Odd q)

/-- `Φ − 1`. Kind: definition. -/
abbrev frobOne : M →ₗ[A] M := Φ - LinearMap.id

/-- `Φ − q`. Kind: definition. -/
abbrev frobQ : M →ₗ[A] M := Φ - (q : A) • LinearMap.id

omit hq in
/-- `Φ` commutes with the identity. Kind: PROVED. -/
theorem comm_id : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ := by
  rw [LinearMap.comp_id, LinearMap.id_comp]

/-- The identity is an involution. Kind: PROVED. -/
theorem id_invol : (LinearMap.id : M →ₗ[A] M) ∘ₗ LinearMap.id = LinearMap.id :=
  LinearMap.id_comp _

include hq in
/-- `D C = C A` at `g = 1`. Kind: PROVED. -/
theorem tame_DC_CA_one :
    (Φ - tameNorm q LinearMap.id) ∘ₗ (LinearMap.id - LinearMap.id) =
      (LinearMap.id - LinearMap.id) ∘ₗ (Φ - LinearMap.id) :=
  tame_DC_CA Φ LinearMap.id q hq (comm_id Φ) id_invol

/-- The tame free model at augmentation `g = 1` (tex 3478–3480). Kind: definition. -/
abbrev tameFreeModel1 : GCx A :=
  tameFreeModel Φ LinearMap.id q hq (comm_id Φ) id_invol

/-- **The unramified complex** `[M --Φ−1--> M]` in degrees zero and one (tex 3478–3480; the
inflated cochains of `G_w / I_w`). Kind: definition. -/
def unrCx : GCx A :=
  cx3 (frobOne Φ) (0 : M →ₗ[A] PUnit) (fun _ => rfl)

/-- **The singular block** `[M --Φ−q--> M]` in degrees one and two (tex 3478–3480; the singular
quotient of the full by the unramified local condition, `[Φ − q]` of (5.9), tex 5317–5322).
Kind: definition. -/
def singCx : GCx A :=
  cx3 (0 : PUnit →ₗ[A] M) (frobQ Φ q) (fun _ => by simp)

/-- The model differential from degree zero at `g = 1`: `v ↦ ((Φ − 1) v, 0)`. Kind: PROVED. -/
theorem tameFreeModel1_d0 (v : M) :
    (tameFreeModel1 Φ q hq).d 0 1 rfl v = (frobOne Φ v, (0 : M)) := by
  change (frobOne Φ v, (LinearMap.id - LinearMap.id : M →ₗ[A] M) v) = _
  rw [sub_self, LinearMap.zero_apply]

/-- The model differential from degree one at `g = 1`: `(v, w) ↦ (Φ − q) w`. Kind: PROVED. -/
theorem tameFreeModel1_d1 (v w : M) :
    (tameFreeModel1 Φ q hq).d 1 2 rfl ((v, w) : M × M) = frobQ Φ q w := by
  change -(LinearMap.id - LinearMap.id : M →ₗ[A] M) v +
    (Φ - tameNorm q (LinearMap.id : M →ₗ[A] M)) w = _
  rw [sub_self, LinearMap.zero_apply, neg_zero, zero_add, tameNorm_one q hq]

/-- **The inclusion of the unramified complex** `v ↦ v`, `v ↦ (v, 0)` (tex 3478–3480). Kind:
definition (PROVED chain property). -/
def unrIncl : GHom (unrCx Φ) (tameFreeModel1 Φ q hq) :=
  cx3Hom (h := fun _ => rfl) (h' := freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq))
    LinearMap.id (LinearMap.inl A M M) 0
    (fun v => (tameFreeModel1_d0 Φ q hq v).symm)
    (fun v => by
      change (0 : M) = (tameFreeModel1 Φ q hq).d 1 2 rfl ((v, 0) : M × M)
      rw [tameFreeModel1_d1, map_zero])

/-- **The projection onto the singular block** `(v, w) ↦ w` (tex 3478–3480). Kind: definition
(PROVED chain property). -/
def singProj : GHom (tameFreeModel1 Φ q hq) (singCx Φ q) :=
  cx3Hom (h := freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq)) (h' := fun _ => by simp)
    0 (LinearMap.snd A M M) LinearMap.id
    (fun v => by
      change ((tameFreeModel1 Φ q hq).d 0 1 rfl v).2 = (0 : M)
      rw [tameFreeModel1_d0])
    (fun z => by
      obtain ⟨v, w⟩ := z
      change (tameFreeModel1 Φ q hq).d 1 2 rfl ((v, w) : M × M) = frobQ Φ q w
      rw [tameFreeModel1_d1])

/-- The retraction onto the unramified complex `v ↦ v`, `(v, w) ↦ v`. Kind: definition (PROVED
chain property). -/
def unrRetr : GHom (tameFreeModel1 Φ q hq) (unrCx Φ) :=
  cx3Hom (h := freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq)) (h' := fun _ => rfl)
    LinearMap.id (LinearMap.fst A M M) 0
    (fun v => by
      change ((tameFreeModel1 Φ q hq).d 0 1 rfl v).1 = frobOne Φ v
      rw [tameFreeModel1_d0])
    (fun _ => rfl)

/-- The section of the singular block `w ↦ (0, w)`. Kind: definition (PROVED chain property). -/
def singSect : GHom (singCx Φ q) (tameFreeModel1 Φ q hq) :=
  cx3Hom (h := fun _ => by simp) (h' := freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq))
    0 (LinearMap.inr A M M) LinearMap.id
    (fun _ => by
      change ((0 : M), (0 : M)) = (tameFreeModel1 Φ q hq).d 0 1 rfl 0
      rw [map_zero]
      rfl)
    (fun w => by
      change frobQ Φ q w = (tameFreeModel1 Φ q hq).d 1 2 rfl ((0, w) : M × M)
      rw [tameFreeModel1_d1])

/-- The degree-zero component of `unrIncl` is the identity (tex 3478–3480). Kind: PROVED. -/
theorem unrIncl_f0 (v : M) : (unrIncl Φ q hq).f 0 0 rfl v = v := rfl
/-- The degree-one component of `unrIncl` is `v ↦ (v, 0)` (tex 3478–3480). Kind: PROVED. -/
theorem unrIncl_f1 (v : M) : (unrIncl Φ q hq).f 1 1 rfl v = ((v, 0) : M × M) := rfl
/-- The degree-zero component of `unrRetr` is the identity (tex 3478–3480). Kind: PROVED. -/
theorem unrRetr_f0 (v : M) : (unrRetr Φ q hq).f 0 0 rfl v = v := rfl
/-- The degree-one component of `unrRetr` is `(v, w) ↦ v` (tex 3478–3480). Kind: PROVED. -/
theorem unrRetr_f1 (x : M × M) : (unrRetr Φ q hq).f 1 1 rfl x = x.1 := rfl
/-- The degree-one component of `singProj` is `(v, w) ↦ w` (tex 3478–3480). Kind: PROVED. -/
theorem singProj_f1 (x : M × M) : (singProj Φ q hq).f 1 1 rfl x = x.2 := rfl
/-- The degree-two component of `singProj` is the identity (tex 3478–3480). Kind: PROVED. -/
theorem singProj_f2 (x : M) : (singProj Φ q hq).f 2 2 rfl x = x := rfl
/-- The degree-one component of `singSect` is `w ↦ (0, w)` (tex 3478–3480). Kind: PROVED. -/
theorem singSect_f1 (w : M) : (singSect Φ q hq).f 1 1 rfl w = ((0, w) : M × M) := rfl
/-- The degree-two component of `singSect` is the identity (tex 3478–3480). Kind: PROVED. -/
theorem singSect_f2 (w : M) : (singSect Φ q hq).f 2 2 rfl w = w := rfl

/-- **At augmentation the model is the direct sum of the unramified complex and the singular
block** (tex 3478–3480): in degrees `0, 1, 2`, `r ∘ ι = 1`, `π ∘ s = 1`, `π ∘ ι = 0`, `r ∘ s = 0`
and `ι ∘ r + s ∘ π = 1`. Kind: PROVED. -/
theorem tame_split_directSum :
    (∀ v : M, (unrRetr Φ q hq).f 0 0 rfl ((unrIncl Φ q hq).f 0 0 rfl v) = v) ∧
    (∀ v : M, (unrRetr Φ q hq).f 1 1 rfl ((unrIncl Φ q hq).f 1 1 rfl v) = v) ∧
    (∀ w : M, (singProj Φ q hq).f 1 1 rfl ((singSect Φ q hq).f 1 1 rfl w) = w) ∧
    (∀ w : M, (singProj Φ q hq).f 2 2 rfl ((singSect Φ q hq).f 2 2 rfl w) = w) ∧
    (∀ v : M, (singProj Φ q hq).f 1 1 rfl ((unrIncl Φ q hq).f 1 1 rfl v) = 0) ∧
    (∀ w : M, (unrRetr Φ q hq).f 1 1 rfl ((singSect Φ q hq).f 1 1 rfl w) = 0) ∧
    (∀ x : M × M, (unrIncl Φ q hq).f 1 1 rfl ((unrRetr Φ q hq).f 1 1 rfl x) +
      (singSect Φ q hq).f 1 1 rfl ((singProj Φ q hq).f 1 1 rfl x) = x) ∧
    (∀ x : M, (unrIncl Φ q hq).f 0 0 rfl ((unrRetr Φ q hq).f 0 0 rfl x) = x) ∧
    (∀ x : M, (singSect Φ q hq).f 2 2 rfl ((singProj Φ q hq).f 2 2 rfl x) = x) := by
  refine ⟨fun v => ?_, fun v => ?_, fun w => ?_, fun w => ?_, fun v => ?_, fun w => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [unrIncl_f0, unrRetr_f0]
  · rw [unrIncl_f1, unrRetr_f1]
  · rw [singSect_f1, singProj_f1]
  · rw [singSect_f2, singProj_f2]
  · rw [unrIncl_f1, singProj_f1]
    rfl
  · rw [singSect_f1, unrRetr_f1]
    rfl
  · rw [unrRetr_f1, unrIncl_f1, singProj_f1, singSect_f1]
    exact Prod.ext (add_zero _) (zero_add _)
  · rw [unrRetr_f0, unrIncl_f0]
  · rw [singProj_f2, singSect_f2]

/-- **The quotient of the model by the unramified complex is the singular block, degree one**
(tex 3478–3480): `M --ι--> M × M --π--> M` is exact with `ι` injective and `π` surjective.
Kind: PROVED. -/
theorem tame_split_exact_one :
    Function.Injective ((unrIncl Φ q hq).f 1 1 rfl) ∧
      Function.Surjective ((singProj Φ q hq).f 1 1 rfl) ∧
      ∀ x : M × M, (singProj Φ q hq).f 1 1 rfl x = 0 ↔ ∃ v, (unrIncl Φ q hq).f 1 1 rfl v = x := by
  refine ⟨fun v v' h => ?_, fun w => ⟨((0 : M), w), rfl⟩, fun x => ?_⟩
  · have h' : (((v : M), (0 : M)) : M × M) = ((v' : M), (0 : M)) := h
    exact congrArg Prod.fst h'
  · rw [singProj_f1]
    constructor
    · intro hx
      exact ⟨x.1, by rw [unrIncl_f1]; exact Prod.ext rfl hx.symm⟩
    · rintro ⟨v, rfl⟩
      rfl

/-- **Degrees zero and two of the splitting**: in degree zero the unramified complex is the whole
model, in degree two the singular block is. Kind: PROVED. -/
theorem tame_split_exact_zero_two :
    Function.Bijective ((unrIncl Φ q hq).f 0 0 rfl) ∧
      Function.Bijective ((singProj Φ q hq).f 2 2 rfl) :=
  ⟨⟨fun v v' h => (h : (v : M) = v'), fun v => ⟨v, rfl⟩⟩,
    ⟨fun v v' h => (h : (v : M) = v'), fun v => ⟨v, rfl⟩⟩⟩

/-- The model terms outside degrees `0, 1, 2` are subsingletons. Kind: PROVED. -/
theorem cx3X_subsingleton {X0 X1 X2 : Type} [AddCommGroup X0] [Module A X0] [AddCommGroup X1]
    [Module A X1] [AddCommGroup X2] [Module A X2] (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1)
    (h2 : n ≠ 2) : Subsingleton (cx3X (A := A) X0 X1 X2 n) := by
  rcases n with (_ | _ | _ | n) | n
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact inferInstanceAs (Subsingleton PUnit)
  · exact inferInstanceAs (Subsingleton PUnit)

/-- **The tame model at augmentation as the new-place data of the support change**
(tex 3470–3480; `UnramifiedNewPlace` of the support-change retention): the full local complex is
the tame free model at `g = 1`, the local condition the unramified complex, `ι_q` the inclusion of
the unramified summand. This is the model `T` that the genuine local complexes at a tame place
are compared with. Kind: definition (PROVED fields). -/
def tameNewPlace (Mq : ModuleCat.{0} A) (Φ : Mq →ₗ[A] Mq) (q : ℕ) (hq : Odd q) :
    ZInQ.Contrib.CloudB3RC53.SelmerDuality.UnramifiedNewPlace A where
  M := Mq
  Φ := Φ
  q := q
  q_odd := hq
  Lq := tameFreeModel1 Φ q hq
  Uq := unrCx Φ
  ιq := unrIncl Φ q hq
  eL0 := LinearEquiv.refl A Mq
  eL1 := LinearEquiv.refl A (Mq × Mq)
  eL2 := LinearEquiv.refl A Mq
  Lq_zero n h0 h1 h2 := cx3X_subsingleton n h0 h1 h2
  Lq_d0 x := (tameFreeModel1_d0 Φ q hq x).trans rfl
  Lq_d1 y := (tameFreeModel1_d1 Φ q hq y.1 y.2).trans rfl
  eU0 := LinearEquiv.refl A Mq
  eU1 := LinearEquiv.refl A Mq
  Uq_zero n h0 h1 := by
    by_cases h2 : n = 2
    · subst h2
      exact inferInstanceAs (Subsingleton PUnit)
    · exact cx3X_subsingleton n h0 h1 h2
  Uq_d x := rfl
  ιq_0 x := rfl
  ιq_1 x := rfl

end Augmentation

/-! ### The cohomology of the model at augmentation -/

section Cohomology

variable {M : Type} [AddCommGroup M] [Module A M] (Φ : M →ₗ[A] M) (q : ℕ) (hq : Odd q)

/-- The model differential from degree zero at `g = 1`, as a plain map `v ↦ ((Φ − 1) v, 0)`.
Kind: definition. -/
def cohD0 : M →ₗ[A] M × M := (frobOne Φ).prod 0

/-- The model differential from degree one at `g = 1`, as a plain map `(v, w) ↦ (Φ − q) w`.
Kind: definition. -/
def cohD1 : M × M →ₗ[A] M := frobQ Φ q ∘ₗ LinearMap.snd A M M

/-- The model differential from degree zero is `cohD0`. Kind: PROVED. -/
theorem tameFreeModel1_d0_eq : (tameFreeModel1 Φ q hq).d 0 1 rfl = cohD0 Φ :=
  LinearMap.ext fun v => tameFreeModel1_d0 Φ q hq v

/-- The model differential from degree one is `cohD1`. Kind: PROVED. -/
theorem tameFreeModel1_d1_eq : (tameFreeModel1 Φ q hq).d 1 2 rfl = cohD1 Φ q :=
  LinearMap.ext fun x => tameFreeModel1_d1 Φ q hq x.1 x.2

/-- The coordinates of a one-cocycle: `(v, w) ↦ ([v], w) ∈ coker(Φ − 1) × ker(Φ − q)`. Kind:
definition. -/
def tameH1Coord :
    LinearMap.ker (cohD1 Φ q) →ₗ[A]
      (M ⧸ LinearMap.range (frobOne Φ)) × LinearMap.ker (frobQ Φ q) :=
  ((LinearMap.range (frobOne Φ)).mkQ ∘ₗ LinearMap.fst A M M ∘ₗ
      (LinearMap.ker (cohD1 Φ q)).subtype).prod
    (LinearMap.codRestrict (LinearMap.ker (frobQ Φ q))
      (LinearMap.snd A M M ∘ₗ (LinearMap.ker (cohD1 Φ q)).subtype)
      (fun x => x.2))

/-- The cocycle coordinates are surjective. Kind: PROVED. -/
theorem tameH1Coord_surjective : Function.Surjective (tameH1Coord Φ q) := by
  rintro ⟨c, ⟨w, hw⟩⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨⟨(v, w), hw⟩, rfl⟩

/-- The kernel of the cocycle coordinates is the space of coboundaries. Kind: PROVED. -/
theorem tameH1Coord_ker :
    LinearMap.ker (tameH1Coord Φ q) =
      (LinearMap.range (cohD0 Φ)).comap (LinearMap.ker (cohD1 Φ q)).subtype := by
  ext ⟨⟨v, w⟩, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun y => (y.2 : M)) h
    change Submodule.Quotient.mk v = (0 : M ⧸ LinearMap.range (frobOne Φ)) at h1
    change w = 0 at h2
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    change (frobOne Φ m, (0 : M)) = (v, w)
    rw [hm, h2]
  · rintro ⟨m, hm⟩
    have hm' : ((frobOne Φ m, (0 : M)) : M × M) = (v, w) := hm
    have h1 : frobOne Φ m = v := congrArg Prod.fst hm'
    have h2 : (0 : M) = w := congrArg Prod.snd hm'
    refine Prod.ext ?_ (Subtype.ext h2.symm)
    change Submodule.Quotient.mk v = (0 : M ⧸ LinearMap.range (frobOne Φ))
    rw [Submodule.Quotient.mk_eq_zero, ← h1]
    exact LinearMap.mem_range_self _ m

/-- **The degree-one cohomology of the model at augmentation** (tex 3478–3480, 3298–3306):
`H¹ ≅ coker(Φ − 1) × ker(Φ − q)`, `[(v, w)] ↦ ([v], w)` — the target of the actual unramified
tame coordinates `[z] ↦ (z(φ) mod (Φ − 1), z(σ))`. Kind: definition (PROVED bijectivity). -/
def tameH1Equiv :
    ZInQ.Manuscript.RC.Limits.subquotientOf (cohD0 Φ) (cohD1 Φ q) ≃ₗ[A]
      (M ⧸ LinearMap.range (frobOne Φ)) × LinearMap.ker (frobQ Φ q) :=
  (Submodule.quotEquivOfEq _ _ (tameH1Coord_ker Φ q).symm).trans
    ((tameH1Coord Φ q).quotKerEquivOfSurjective (tameH1Coord_surjective Φ q))

/-- Evaluation of the degree-one cohomology equivalence. Kind: PROVED (definitional). -/
theorem tameH1Equiv_mk (x : LinearMap.ker (cohD1 Φ q)) :
    tameH1Equiv Φ q (Submodule.Quotient.mk x) = tameH1Coord Φ q x :=
  rfl

/-- **The degree-zero cohomology of the model at augmentation**: the zero-cocycles are
`ker(Φ − 1)` (tex 3478–3480). Kind: PROVED. -/
theorem cohD0_eq_zero_iff (v : M) : cohD0 Φ v = 0 ↔ frobOne Φ v = 0 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    change (frobOne Φ v, (0 : M)) = 0
    rw [h]
    rfl

/-- **The degree-two coboundaries of the model at augmentation** are the image of `Φ − q`, so
`H² = coker(Φ − q)` (tex 3478–3480). Kind: PROVED. -/
theorem cohD1_range : LinearMap.range (cohD1 Φ q) = LinearMap.range (frobQ Φ q) := by
  ext w
  constructor
  · rintro ⟨⟨v, w'⟩, rfl⟩
    exact ⟨w', rfl⟩
  · rintro ⟨w', rfl⟩
    exact ⟨((0 : M), w'), rfl⟩

end Cohomology

/-! ### Two conjugate places: the two-place singular block -/

section TwoPlaces

/-- The direct sum of two complexes. Kind: definition. -/
def prodGCx (X Y : GCx A) : GCx A where
  X n := ModuleCat.of A (X.X n × Y.X n)
  d a b h := (X.d a b h).prodMap (Y.d a b h)
  d_d a b c hab hbc z := by
    obtain ⟨x, y⟩ := z
    exact Prod.ext (X.d_d a b c hab hbc x) (Y.d_d a b c hab hbc y)

/-- The differential of a direct sum. Kind: PROVED (definitional). -/
theorem prodGCx_d_apply (X Y : GCx A) (a b : ℤ) (h : a + 1 = b) (x : X.X a) (y : Y.X a) :
    (prodGCx X Y).d a b h ((x, y) : X.X a × Y.X a) = (X.d a b h x, Y.d a b h y) :=
  rfl

variable (F : Matrix (Fin 2) (Fin 2) A) (q : ℕ) (z zi : A)

/-- **The two singular blocks at the conjugate places** `w`, `w̄` of an unused split prime, for
the stage module `M = A²` with Frobenius `z F` at `w` and `z⁻¹ F` at `w̄` (`zi = z⁻¹`):
`[M --zF−q--> M] ⊕ [M --z⁻¹F−q--> M]` in degrees one and two (tex 4176–4184, 3478–3480).
Kind: definition. -/
def twoSingCx : GCx A :=
  prodGCx (singCx (Matrix.toLin' (z • F)) q) (singCx (Matrix.toLin' (zi • F)) q)

/-- The coordinates `A^(2 ⊕ 2) ≃ A² × A²` of the two places. Kind: definition. -/
abbrev twoPlaceCoord : (Fin 2 ⊕ Fin 2 → A) ≃ₗ[A] (Fin 2 → A) × (Fin 2 → A) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) A A

/-- The degree-one-to-two differential of the two singular blocks in the coordinates of the two
places. Kind: definition. -/
def twoSingD12 : (Fin 2 ⊕ Fin 2 → A) →ₗ[A] (Fin 2 ⊕ Fin 2 → A) :=
  (twoPlaceCoord (A := A)).symm.toLinearMap ∘ₗ
    ((frobQ (Matrix.toLin' (z • F)) q).prodMap (frobQ (Matrix.toLin' (zi • F)) q)) ∘ₗ
      (twoPlaceCoord (A := A)).toLinearMap

/-- `twoSingD12` is the differential of `twoSingCx` transported to the coordinates. Kind: PROVED
(definitional). -/
theorem twoSingD12_eq (v : Fin 2 ⊕ Fin 2 → A) :
    twoPlaceCoord (twoSingD12 F q z zi v) =
      (twoSingCx F q z zi).d 1 2 rfl (twoPlaceCoord v) := by
  rw [twoSingD12, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- `Φ − q` for a matrix Frobenius is the matrix `N − q`. Kind: PROVED. -/
theorem frobQ_toLin' (N : Matrix (Fin 2) (Fin 2) A) (x : Fin 2 → A) :
    frobQ (Matrix.toLin' N) q x = (N - (q : A) • (1 : Matrix (Fin 2) (Fin 2) A)) *ᵥ x := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The differential of the two singular blocks is multiplication by `twoPlaceBlock`. Kind:
PROVED. -/
theorem twoSingD12_apply (v : Fin 2 ⊕ Fin 2 → A) :
    twoSingD12 F q z zi v =
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F (q : A) z zi *ᵥ v := by
  rw [ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock, ← Sum.elim_comp_inl_inr v,
    Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  funext k
  rcases k with k | k
  · change frobQ (Matrix.toLin' (z • F)) q (v ∘ Sum.inl) k = _
    rw [frobQ_toLin']
    simp
  · change frobQ (Matrix.toLin' (zi • F)) q (v ∘ Sum.inr) k = _
    rw [frobQ_toLin']
    simp

/-- **The two-place singular block is `twoPlaceBlock`** (tex 4176–4184: the two quotient
determinants `δ_q = det(zFr_q − q) · det(z⁻¹Fr_q − q)`): in the standard basis of the two places,
the matrix of the differential of the two singular blocks is
`twoPlaceBlock F q z z⁻¹ = diag(zF − q, z⁻¹F − q)`. Kind: PROVED. -/
theorem twoSing_matrix :
    LinearMap.toMatrix' (twoSingD12 F q z zi) =
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F (q : A) z zi := by
  have e : twoSingD12 F q z zi =
      Matrix.toLin' (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F (q : A) z zi) :=
    LinearMap.ext fun v => (twoSingD12_apply F q z zi v).trans (Matrix.toLin'_apply _ _).symm
  rw [e, LinearMap.toMatrix'_toLin']

/-- **Stage transitions**: the two-place block is compatible with coefficient ring maps. Kind:
PROVED. -/
theorem twoPlaceBlock_map {B : Type} [CommRing B] (φ : A →+* B) :
    (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F (q : A) z zi).map φ =
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock (F.map φ) (q : B) (φ z) (φ zi) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock, Matrix.fromBlocks,
      Matrix.one_apply, Matrix.sub_apply]
  all_goals split_ifs <;> simp

end TwoPlaces

/-! ### Naturality in the module -/

section Naturality

variable {M M' : Type} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  (Φ g : M →ₗ[A] M) (Φ' g' : M' →ₗ[A] M') (q : ℕ) (hq : Odd q)
  (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hg : g ∘ₗ g = LinearMap.id)
  (hcomm' : Φ' ∘ₗ g' = g' ∘ₗ Φ') (hg' : g' ∘ₗ g' = LinearMap.id)

/-- An equivariant map commutes with the tame norms. Kind: PROVED. -/
theorem tameNorm_natural (f : M →ₗ[A] M') (hfg : f ∘ₗ g = g' ∘ₗ f) (v : M) :
    f (tameNorm q g v) = tameNorm q g' (f v) := by
  have e := LinearMap.congr_fun hfg v
  simp only [LinearMap.comp_apply] at e
  simp only [tameNorm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
    map_nsmul, e]

/-- **Naturality of the free model in the module** (tex 3470–3474): an `A`-linear map commuting
with Frobenius and the tame generator induces a map of free models, the map itself in every slot.
Kind: definition (PROVED chain property). -/
def tameFreeModelMap (f : M →ₗ[A] M') (hfΦ : f ∘ₗ Φ = Φ' ∘ₗ f) (hfg : f ∘ₗ g = g' ∘ₗ f) :
    GHom (tameFreeModel Φ g q hq hcomm hg) (tameFreeModel Φ' g' q hq hcomm' hg') :=
  cx3Hom (h := freeD1_freeD0 _ _ _ (tame_DC_CA Φ g q hq hcomm hg))
    (h' := freeD1_freeD0 _ _ _ (tame_DC_CA Φ' g' q hq hcomm' hg'))
    f (f.prodMap f) f
    (fun v => by
      have e1 := LinearMap.congr_fun hfΦ v
      have e2 := LinearMap.congr_fun hfg v
      simp only [LinearMap.comp_apply] at e1 e2
      change ((f ((Φ - LinearMap.id : M →ₗ[A] M) v)), f ((g - LinearMap.id : M →ₗ[A] M) v)) =
        ((Φ' - LinearMap.id : M' →ₗ[A] M') (f v), (g' - LinearMap.id : M' →ₗ[A] M') (f v))
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, e1, e2])
    (fun x => by
      obtain ⟨v, w⟩ := x
      have e1 := LinearMap.congr_fun hfΦ w
      have e2 := LinearMap.congr_fun hfg v
      simp only [LinearMap.comp_apply] at e1 e2
      change f (-(g - LinearMap.id : M →ₗ[A] M) v + (Φ - tameNorm q g : M →ₗ[A] M) w) =
        -(g' - LinearMap.id : M' →ₗ[A] M') (f v) + (Φ' - tameNorm q g' : M' →ₗ[A] M') (f w)
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_add, map_neg, e1, e2,
        tameNorm_natural g g' q f hfg])

end Naturality

end ZInQ.Manuscript.RC.Local

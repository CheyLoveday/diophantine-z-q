import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 3: descend once, before twisting; the multiplier `L`

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 4 "Descend once, before twisting" (tex 3004–3032), paragraph 5 "Integral local descent
at the old places" (tex 3034–3086), and the corestriction compatibility of `d_a`
(tex 3281–3288).

* (H8)–(H9): the inflation–restriction sequence (Nekovář, (4.1.4.1); `PRINT`, see
  `Interfaces.lean`) enters as abstract exactness data `FiveTerm`.  When the outer terms are
  killed by `2^e` (by (H2)), `d_a(c) = 2^e b` for any `b` with `res b = 2^e c` is well defined,
  additive, natural (coefficient reduction, transport of the field diagram, corestriction in
  Cartesian squares), restricts to `2^{2e} c`, and sends every restricted class `res b` to
  `2^{2e} b`.  When the relative group is trivial (`I = ∅`) restriction is an isomorphism onto the
  invariants, and `d_a(c) = 2^{2e} c` with `c` read in `H¹(B, V)` through it
  (`FiveTerm.descend_trivial`; restated by Lane RC27 over a general `FiveTerm A B C D`, so that the
  genuine sequence, whose third term `H¹(M, V)^Γ` is a different group from `H¹(B, V)`, is an
  instance).  All `PROVED`.
* (H10) and the Kummer descent: from `c_B H¹(Gal(F'/F), B(F')) = 0` (Lang's theorem and the
  formal-group filtration: `PRINT`/`GLUE`, see `Interfaces.lean`), a class that becomes Kummer
  over the unramified `F'` becomes Kummer over `F` after multiplication by `c_B`: `PROVED`
  diagram chase.
* (H11): `L = m₀ C_π C_bad 2^{2e}` and `b_{I,a} = m₀ C_bad d_a(c_{I,a})` restricts to
  `δ_a(L D_I y_{f n_I})`: `PROVED`.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

/-! ## (H8)–(H9): the descent map `d_a` -/

/-- The five-term inflation–restriction sequence (H8) as exactness data:
`0 → H¹(Γ, V^{G_M}) → H¹(B, V) → H¹(M, V)^Γ → H²(Γ, V^{G_M})`. -/
structure FiveTerm (A B C D : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] where
  /-- inflation `H¹(Γ, V^{G_M}) → H¹(B, V)` -/
  inf : A →+ B
  /-- restriction `H¹(B, V) → H¹(M, V)^Γ` -/
  res : B →+ C
  /-- transgression `H¹(M, V)^Γ → H²(Γ, V^{G_M})` -/
  tg : C →+ D
  inf_injective : Function.Injective inf
  exact_B : ∀ b, res b = 0 ↔ ∃ x, inf x = b
  exact_C : ∀ c, tg c = 0 ↔ ∃ b, res b = c

section Descent

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable (S : FiveTerm A B C D) (e : ℕ)

/-- tex 3017: since `2^e` kills `H²(Γ, V^{G_M})` (by (H2)), `2^e c` lifts. -/
theorem FiveTerm.lift_exists (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) :
    ∃ b, S.res b = ((2 : ℤ) ^ e) • c := by
  rw [← S.exact_C, map_zsmul]; exact hD _

/-- (H9), tex 3017–3019: `d_a(c) = 2^e b` for a chosen `b` with `res b = 2^e c`. -/
noncomputable def FiveTerm.descend (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) : B :=
  ((2 : ℤ) ^ e) • Classical.choose (S.lift_exists e hD c)

/-- (H9) is independent of the choice, tex 3021–3022, `PROVED`: any two lifts differ by an
inflated class, which `2^e` kills (by (H2)). -/
theorem FiveTerm.descend_eq (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) (b : B) (hb : S.res b = ((2 : ℤ) ^ e) • c) :
    S.descend e hD c = ((2 : ℤ) ^ e) • b := by
  have h0 := Classical.choose_spec (S.lift_exists e hD c)
  have hdiff : S.res (Classical.choose (S.lift_exists e hD c) - b) = 0 := by
    rw [map_sub, h0, hb, sub_self]
  obtain ⟨x, hx⟩ := (S.exact_B _).mp hdiff
  have : ((2 : ℤ) ^ e) • (Classical.choose (S.lift_exists e hD c) - b) = 0 := by
    rw [← hx, ← map_zsmul, hA, map_zero]
  rw [FiveTerm.descend, ← sub_eq_zero, ← smul_sub, this]

/-- (H9), tex 3024, `PROVED`: the restriction of `d_a(c)` is exactly `2^{2e} c`. -/
theorem FiveTerm.res_descend (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) :
    S.res (S.descend e hD c) = ((2 : ℤ) ^ (2 * e)) • c := by
  rw [FiveTerm.descend, map_zsmul, Classical.choose_spec (S.lift_exists e hD c), smul_smul,
    ← pow_add, two_mul]

/-- (H9) is additive, tex 3022–3023, `PROVED`. -/
theorem FiveTerm.descend_add (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c c' : C) :
    S.descend e hD (c + c') = S.descend e hD c + S.descend e hD c' := by
  have h := Classical.choose_spec (S.lift_exists e hD c)
  have h' := Classical.choose_spec (S.lift_exists e hD c')
  rw [S.descend_eq e hA hD (c + c') (Classical.choose (S.lift_exists e hD c) +
      Classical.choose (S.lift_exists e hD c')) (by rw [map_add, h, h', smul_add]),
    smul_add]
  rfl

/-- (H9) as an additive map. -/
noncomputable def FiveTerm.descendHom (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) : C →+ B where
  toFun := S.descend e hD
  map_zero' := by
    rw [S.descend_eq e hA hD 0 0 (by simp), smul_zero]
  map_add' := S.descend_add e hA hD

/-- (H9) is natural, tex 3022–3024 and 3281–3288, `PROVED`: for any map of the data commuting with
restriction (coefficient reduction, transport of the whole field diagram, or corestriction in the
Cartesian class-field squares, where `res ∘ cor = cor ∘ res`), `d_a` commutes with it. -/
theorem FiveTerm.descend_natural {A' B' C' D' : Type*} [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [AddCommGroup D'] (S' : FiveTerm A' B' C' D')
    (hA' : ∀ x : A', ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (hD' : ∀ x : D', ((2 : ℤ) ^ e) • x = 0)
    (α : B →+ B') (γ : C →+ C') (hcomm : ∀ b, S'.res (α b) = γ (S.res b)) (c : C) :
    S'.descend e hD' (γ c) = α (S.descend e hD c) := by
  have h := Classical.choose_spec (S.lift_exists e hD c)
  rw [S'.descend_eq e hA' hD' (γ c) (α (Classical.choose (S.lift_exists e hD c)))
      (by rw [hcomm, h, map_zsmul]), FiveTerm.descend, map_zsmul]

/-- tex 3281–3288, `PROVED`: compatibility of `d_a` with corestriction in a Cartesian square
(`res ∘ cor = cor ∘ res`): "if `b` lifts `2^e c`, its corestriction lifts `2^e` times the
corestricted class; uniqueness after the second multiplication by `2^e` proves the required
compatibility". -/
theorem FiveTerm.descend_cor {A' B' C' D' : Type*} [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [AddCommGroup D'] (S' : FiveTerm A' B' C' D')
    (hA' : ∀ x : A', ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (hD' : ∀ x : D', ((2 : ℤ) ^ e) • x = 0)
    (cor : B →+ B') (corM : C →+ C') (hsq : ∀ b, S'.res (cor b) = corM (S.res b)) (c : C) :
    S'.descend e hD' (corM c) = cor (S.descend e hD c) :=
  S.descend_natural e S' hA' hD hD' cor corM hsq c

/-- (H9) on restricted classes, tex 3021–3024 and 3030–3032, `PROVED`: for every class `b` of
`H¹(B, V)`, `d_a(res b) = 2^{2e} b`.  Indeed `2^e b` is a lift of `2^e res b`, and the choice of
the lift does not matter (`descend_eq`).  This identity holds for every five-term sequence, with no
condition on the relative group; it is what "this same definition gives `d_a(c) = 2^{2e} c`"
(tex 3031) computes once the invariant class `c` is a restriction, which for `I = ∅` every invariant
class is (`descend_trivial`).  Non-vacuity: the hypotheses hold for the genuine sequence (the
interface `infResInputGenuine` of the `CloudB3RC53` layer) and for `FiveTerm.ofTrivialRelative`. -/
theorem FiveTerm.descend_res (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (b : B) :
    S.descend e hD (S.res b) = ((2 : ℤ) ^ (2 * e)) • b := by
  rw [S.descend_eq e hA hD (S.res b) (((2 : ℤ) ^ e) • b) (map_zsmul S.res _ b), smul_smul,
    ← pow_add, two_mul]

/-- A trivial relative group makes restriction an isomorphism, tex 3030, `PROVED`: when the outer
terms `H¹(Γ, V^{G_M})` and `H²(Γ, V^{G_M})` of (H8) vanish (as they do for `Γ` trivial, the case
`I = ∅`), exactness at `H¹(B, V)` and at `H¹(M, V)^Γ` makes `res : H¹(B, V) → H¹(M, V)^Γ`
bijective.  Non-vacuity: the genuine sequence for `N = ⊤` meets these hypotheses
(`GlueSweep.Heeg.explicitResConj1_top_bijective`), and so does `FiveTerm.ofTrivialRelative`
(outer terms `Unit`). -/
theorem FiveTerm.res_bijective_of_subsingleton [Subsingleton A] [Subsingleton D] :
    Function.Bijective S.res := by
  refine ⟨(injective_iff_map_eq_zero S.res).mpr fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨x, rfl⟩ := (S.exact_B b).mp hb
    rw [Subsingleton.elim x 0, map_zero]
  · exact (S.exact_C c).mp (Subsingleton.elim _ _)

/-- tex 3030–3032, `PROVED`: "For `I = ∅`, the relative group is trivial and this same definition
gives `d_a(c) = 2^{2e} c`."  For `I = ∅` (`M_∅ = B`) restriction `H¹(B, V) → H¹(M, V)^Γ` is an
isomorphism onto the invariants (`hres`; it follows from the triviality of the relative group by
`res_bijective_of_subsingleton`); reading the invariant class `c` in `H¹(B, V)` through it, the
same definition (H9) gives `d_a(c) = 2^{2e} c`.  The `2^e`-vanishing of `H¹(Γ, V^{G_M})` is not
assumed: it follows from `hres`.  The multiplier `2^{2e}` is the one of `res_descend`, the same for
the primitive class and its derivatives.

Restated by Lane RC27 over a general `FiveTerm A B C D`: the earlier form required the third term
to be the second one with `res = id`, which the genuine sequence (third term
`H1ConjInvariants G M ⊤`, restriction `explicitResConj1 G M ⊤`) cannot satisfy.  DEPARTURE (form
only): the text identifies `H¹(M_∅, V)^Γ` with `H¹(B, V)` (they coincide for `M_∅ = B`); here
that identification is the isomorphism `res`, made explicit, because the genuine third term is a
different group from `H¹(B, V)`.  Non-vacuity: the hypotheses hold for the genuine sequence at `N = ⊤`
(`GlueSweep.Heeg.descend_trivial_top`, `GlueSweep.Heeg.descend_trivial_torsion_top`) and for the
toy data `FiveTerm.ofTrivialRelative` (`FiveTerm.descend_trivial_nonvacuous`, where the
conclusion is `d_a(1) = 4 ≠ 0` in `ℤ/16`). -/
theorem FiveTerm.descend_trivial (hres : Function.Bijective S.res)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) :
    S.descend e hD c = ((2 : ℤ) ^ (2 * e)) • (AddEquiv.ofBijective S.res hres).symm c := by
  have hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0 := fun x => by
    have h0 : S.inf x = 0 :=
      hres.1 (by rw [map_zero]; exact (S.exact_B _).mpr ⟨x, rfl⟩)
    rw [S.inf_injective (h0.trans (map_zero S.inf).symm), smul_zero]
  conv_lhs => rw [← AddEquiv.ofBijective_apply_symm_apply (n := c) S.res hres]
  exact S.descend_res e hA hD _

end Descent

/-! ## Non-vacuity of `descend_trivial`: the five-term data of a trivial relative group -/

/-- The five-term data of a trivial relative group in identified form: zero outer terms and
restriction the identity of `B` (the literal picture of tex 3030 for `I = ∅`, `M_∅ = B`).  A toy
instance for the non-vacuity of `FiveTerm.descend_trivial` and `H11_empty`. -/
def FiveTerm.ofTrivialRelative (B : Type*) [AddCommGroup B] : FiveTerm Unit B B Unit where
  inf := 0
  res := AddMonoidHom.id B
  tg := 0
  inf_injective _ _ _ := Subsingleton.elim _ _
  exact_B b := by
    simp only [AddMonoidHom.id_apply, AddMonoidHom.zero_apply, exists_const]
    exact eq_comm
  exact_C c := ⟨fun _ => ⟨c, rfl⟩, fun _ => Subsingleton.elim _ _⟩

/-- The restriction of the trivial-relative-group data is bijective, `PROVED`. -/
theorem FiveTerm.ofTrivialRelative_res_bijective (B : Type*) [AddCommGroup B] :
    Function.Bijective (FiveTerm.ofTrivialRelative B).res :=
  Function.bijective_id

/-- `descend_trivial` for the trivial-relative-group data, `PROVED`: `d_a(c) = 2^{2e} c`. -/
theorem FiveTerm.descend_ofTrivialRelative (B : Type*) [AddCommGroup B] (e : ℕ) (c : B) :
    (FiveTerm.ofTrivialRelative B).descend e (fun _ => Subsingleton.elim _ _) c =
      ((2 : ℤ) ^ (2 * e)) • c := by
  rw [FiveTerm.descend_trivial _ e (FiveTerm.ofTrivialRelative_res_bijective B)]
  congr 1
  exact (AddEquiv.ofBijective _ _).symm_apply_eq.mpr rfl

/-- Non-vacuity of `descend_trivial`, `PROVED`: its hypotheses hold for the trivial-relative-group
data over `ℤ/16` with `e = 1`, and the conclusion is not trivial: `d_a(1) = 4 ≠ 0`. -/
theorem FiveTerm.descend_trivial_nonvacuous :
    (FiveTerm.ofTrivialRelative (ZMod 16)).descend 1 (fun _ => Subsingleton.elim _ _) 1 = 4 ∧
      (4 : ZMod 16) ≠ 0 := by
  refine ⟨?_, by decide⟩
  rw [FiveTerm.descend_ofTrivialRelative]
  decide

/-! ## (H10): integral local descent at the old places -/

/-- tex 3058–3062, `PROVED` (diagram chase).  `κ : B(F) → H¹(F, B[2^a])` and
`j : H¹(F, B[2^a]) → H¹(F, B)` form the Kummer sequence over `F` (exact at the middle); likewise
over `F'`; `res` commutes with `j`; the kernel of `res : H¹(F, B) → H¹(F', B)` is the image of
inflation from `H¹(Gal(F'/F), B(F'))`, which `c_B` kills by (H10).  If `v` becomes Kummer over
`F'`, then `c_B v` is Kummer over `F`. -/
theorem kummer_descent {Pt Pt' HV HV' HB HB' Hinf : Type*} [AddCommGroup Pt] [AddCommGroup Pt']
    [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB'] [AddCommGroup Hinf]
    (κ : Pt →+ HV) (j : HV →+ HB) (exK : ∀ v, j v = 0 → ∃ x, κ x = v)
    (κ' : Pt' →+ HV') (j' : HV' →+ HB') (hκ' : ∀ x', j' (κ' x') = 0)
    (res : HV →+ HV') (resB : HB →+ HB') (hcomm : ∀ v, j' (res v) = resB (j v))
    (infl : Hinf →+ HB) (exInf : ∀ w, resB w = 0 → ∃ z, infl z = w)
    (cB : ℤ) (hH10 : ∀ z : Hinf, cB • z = 0)
    (v : HV) (hv : ∃ x', res v = κ' x') : ∃ x, κ x = cB • v := by
  obtain ⟨x', hx'⟩ := hv
  have h1 : resB (j v) = 0 := by rw [← hcomm, hx', hκ']
  obtain ⟨z, hz⟩ := exInf _ h1
  apply exK
  rw [map_zsmul, ← hz, ← map_zsmul, hH10, map_zero]

/-! ## (H11): the single multiplier -/

/-- The multiplier `L = m₀ C_π C_bad 2^{2e}` of (H11), tex 3074; it depends only on the fixed
integers `m₀, C_π, C_bad, e`, not on `K, f, I, m, b, G`. -/
def Lmult (m0 Cπ Cbad e : ℕ) : ℤ := m0 * Cπ * Cbad * 2 ^ (2 * e)

/-- (H11), tex 3074–3081, `PROVED`: `b_{I,a} = m₀ C_bad d_a(c_{I,a})`, with
`c_{I,a} = δ_a(C_π D_I y_{f n_I})`, restricts to `δ_a(L D_I y_{f n_I})`. -/
theorem H11_restriction {A B C D P : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup P] (S : FiveTerm A B C D) (e : ℕ)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (δa : P →+ C) (m0 Cπ Cbad : ℕ) (x : P) :
    S.res (((m0 * Cbad : ℕ) : ℤ) • S.descend e hD (δa ((Cπ : ℤ) • x))) =
      δa (Lmult m0 Cπ Cbad e • x) := by
  rw [map_zsmul, S.res_descend, ← map_zsmul, ← map_zsmul, smul_smul, smul_smul, Lmult]
  congr 2
  push_cast; ring

/-- (H11), tex 3080, `PROVED`: `b_{I,a}` is Kummer at an old place `v | 2N`.  Its restriction to
the unramified local field `F' = (M_I)_w` is the Kummer class `δ_a(L D_I y)`, so by
`kummer_descent` the class `C_bad · d_a(c)` (and then `m₀ C_bad d_a(c)`) is Kummer over
`F = (H_f)_v`.  Here the local images are abstracted: `locB` and `locM` are the localizations,
compatible with restriction, and `δ_a(L D_I y)` localizes to a Kummer class over `F'`. -/
theorem H11_kummer_at_old {Pt Pt' HV HV' HB HB' Hinf : Type*} [AddCommGroup Pt] [AddCommGroup Pt']
    [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB'] [AddCommGroup Hinf]
    (κ : Pt →+ HV) (j : HV →+ HB) (exK : ∀ v, j v = 0 → ∃ x, κ x = v)
    (κ' : Pt' →+ HV') (j' : HV' →+ HB') (hκ' : ∀ x', j' (κ' x') = 0)
    (res : HV →+ HV') (resB : HB →+ HB') (hcomm : ∀ v, j' (res v) = resB (j v))
    (infl : Hinf →+ HB) (exInf : ∀ w, resB w = 0 → ∃ z, infl z = w)
    (Cbad : ℤ) (hH10 : ∀ z : Hinf, Cbad • z = 0) (m0 : ℤ)
    (v : HV) (hv : ∃ x', res v = κ' x') : ∃ x, κ x = (m0 * Cbad) • v := by
  obtain ⟨x, hx⟩ := kummer_descent κ j exK κ' j' hκ' res resB hcomm infl exInf Cbad hH10 v hv
  exact ⟨m0 • x, by rw [map_zsmul, hx, smul_smul]⟩

end ZInQ.Manuscript.RC.HeegnerAlgebra

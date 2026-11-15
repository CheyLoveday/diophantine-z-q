import ZInQKernel.Contrib.OneProof.ElkiesX6Star

namespace HDec.QMSplit.Moduli.ElkiesCoord

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

section FF

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem gen_specializes (g : Z ≅ Z) : g.hom (genericPoint Z) ⤳ genericPoint Z := by
  rw [genericPoint_eq_of_isOpenImmersion g.hom]

/-- The comorphism `g^* : ℚ(Z) → ℚ(Z)`, `φ ↦ φ ∘ g`, of an automorphism `g` of an integral scheme on
its function field (the stalk at the generic point; `g` fixes the generic point). -/
noncomputable def ffPullback (g : Z ≅ Z) : Z.functionField →+* Z.functionField :=
  (Z.presheaf.stalkSpecializes (gen_specializes g) ≫ g.hom.stalkMap (genericPoint Z)).hom

theorem ffPullback_germ (g : Z ≅ Z) (A : Z.Opens) (hA : genericPoint Z ∈ A)
    (hA' : genericPoint Z ∈ g.hom ⁻¹ᵁ A) (s : Γ(Z, A)) :
    ffPullback g (Z.presheaf.germ A _ hA s) = Z.presheaf.germ (g.hom ⁻¹ᵁ A) _ hA' (g.hom.app A s) := by
  unfold ffPullback
  rw [CommRingCat.comp_apply, ← ConcreteCategory.comp_apply (Z.presheaf.germ A _ hA),
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap_apply]

/-- Sections over two opens with the same germ at the generic point agree on the intersection. -/
theorem res_eq_of_germ_eq {A B : Z.Opens} (hA : genericPoint Z ∈ A) (hB : genericPoint Z ∈ B)
    (a : Γ(Z, A)) (b : Γ(Z, B)) (h : Z.presheaf.germ A _ hA a = Z.presheaf.germ B _ hB b) :
    Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a =
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b := by
  have hAB : genericPoint Z ∈ A ⊓ B := ⟨hA, hB⟩
  apply germ_injective_of_isIntegral Z (genericPoint Z) hAB
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact h

end FF

/-! ## Values of sections at field points -/

section Ev

variable {Z : Scheme.{0}} {K : Type} [Field K]

theorem pt_comp {Z' : Scheme.{0}} (h : Z ⟶ Z') (y : Spec (CommRingCat.of K) ⟶ Z) :
    (Scheme.SpecToEquivOfField K Z' (y ≫ h)).1 = h (Scheme.SpecToEquivOfField K Z y).1 := by
  rw [_root_.LeafQM.AV.specToEquivOfField_comp_right]

theorem ev_comp_hom {Z' : Scheme.{0}} (h : Z ⟶ Z') (A : Z'.Opens) (y : Spec (CommRingCat.of K) ⟶ Z)
    (hA : (Scheme.SpecToEquivOfField K Z' (y ≫ h)).1 ∈ A)
    (hA' : (Scheme.SpecToEquivOfField K Z y).1 ∈ h ⁻¹ᵁ A) (s : Γ(Z', A)) :
    X6Glue.ev A (y ≫ h) hA s = X6Glue.ev (h ⁻¹ᵁ A) y hA' (h.app A s) := by
  rw [X6Glue.ev_apply, X6Glue.ev_apply]
  generalize hp : Scheme.SpecToEquivOfField K Z' (y ≫ h) = p at hA
  rw [_root_.LeafQM.AV.specToEquivOfField_comp_right] at hp
  subst hp
  rw [ConcreteCategory.comp_apply, Scheme.evaluation_naturality_apply]

theorem ev_res {A A' : Z.Opens} (i : A' ⟶ A) (y : Spec (CommRingCat.of K) ⟶ Z)
    (h' : (Scheme.SpecToEquivOfField K Z y).1 ∈ A') (s : Γ(Z, A)) :
    X6Glue.ev A' y h' (Z.presheaf.map i.op s) = X6Glue.ev A y (i.le h') s := by
  rw [X6Glue.ev_apply, X6Glue.ev_apply]
  congr 1
  simp only [Scheme.evaluation, ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ev_eq_of_germ_eq [IsIntegral Z] {A B : Z.Opens} (hA : genericPoint Z ∈ A)
    (hB : genericPoint Z ∈ B) (a : Γ(Z, A)) (b : Γ(Z, B))
    (h : Z.presheaf.germ A _ hA a = Z.presheaf.germ B _ hB b)
    (y : Spec (CommRingCat.of K) ⟶ Z) (hyA : (Scheme.SpecToEquivOfField K Z y).1 ∈ A)
    (hyB : (Scheme.SpecToEquivOfField K Z y).1 ∈ B) :
    X6Glue.ev A y hyA a = X6Glue.ev B y hyB b := by
  have hAB : (Scheme.SpecToEquivOfField K Z y).1 ∈ A ⊓ B := ⟨hyA, hyB⟩
  have e1 := ev_res (homOfLE (inf_le_left : A ⊓ B ≤ A)) y hAB a
  have e2 := ev_res (homOfLE (inf_le_right : A ⊓ B ≤ B)) y hAB b
  rw [res_eq_of_germ_eq hA hB a b h] at e1
  exact e1.symm.trans e2

theorem ev_mul_eq_one_of_germ [IsIntegral Z] {A B : Z.Opens} (hA : genericPoint Z ∈ A)
    (hB : genericPoint Z ∈ B) (a : Γ(Z, A)) (b : Γ(Z, B))
    (h : Z.presheaf.germ A _ hA a * Z.presheaf.germ B _ hB b = 1)
    (y : Spec (CommRingCat.of K) ⟶ Z) (hyA : (Scheme.SpecToEquivOfField K Z y).1 ∈ A)
    (hyB : (Scheme.SpecToEquivOfField K Z y).1 ∈ B) :
    X6Glue.ev A y hyA a * X6Glue.ev B y hyB b = 1 := by
  have hAB : (Scheme.SpecToEquivOfField K Z y).1 ∈ A ⊓ B := ⟨hyA, hyB⟩
  have hη : genericPoint Z ∈ A ⊓ B := ⟨hA, hB⟩
  have e : Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a *
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b = 1 := by
    apply germ_injective_of_isIntegral Z _ hη
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact h
  have := congrArg (X6Glue.ev (A ⊓ B) y hAB) e
  rw [map_mul, map_one, ev_res, ev_res] at this
  exact this

end Ev

/-! ## Elkies' ring: points and sign automorphisms -/

section Ring

open X6Glue

theorem exists_sq_eq (a : Qbar) : ∃ b : Qbar, b ^ 2 = a :=
  IsAlgClosed.exists_pow_nat_eq a two_pos

theorem eS_ne_zero : (eS : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  intro h
  have := congrArg (elkiesLift (K := Qbar) (-1) 1 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_S, map_zero] at this
  exact one_ne_zero this

theorem eT_ne_zero : (eT : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  intro h
  have := congrArg (elkiesLift (K := Qbar) (-1) 1 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_T, map_zero] at this
  exact neg_ne_zero.mpr one_ne_zero this

theorem eR_ne_zero : (eR : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-3)
  intro h
  have := congrArg (elkiesLift (K := Qbar) 0 0 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_R, map_zero] at this
  subst this
  norm_num at hb

theorem two_ne_zero' : (2 : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-3)
  intro h
  have := congrArg (elkiesLift (K := Qbar) 0 0 b (by ring) (by linear_combination hb)) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

/-- `s ↦ −s` on Elkies' ring. -/
noncomputable def negSHom : ElkiesRing →+* ElkiesRing :=
  elkiesLift (K := ElkiesRing) eT (-eS) eR (by linear_combination rel1) (by linear_combination rel2)

/-- `r ↦ −r` on Elkies' ring. -/
noncomputable def negRHom : ElkiesRing →+* ElkiesRing :=
  elkiesLift (K := ElkiesRing) eT eS (-eR) (by linear_combination rel1) (by linear_combination rel2)

theorem negSHom_invol : negSHom.comp negSHom = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [negSHom, elkiesLift_S]
  · simp [negSHom, elkiesLift_R]

theorem negRHom_invol : negRHom.comp negRHom = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [negRHom, elkiesLift_S]
  · simp [negRHom, elkiesLift_R]

noncomputable def negS : ElkiesRing ≃+* ElkiesRing :=
  RingEquiv.ofRingHom negSHom negSHom negSHom_invol negSHom_invol

noncomputable def negR : ElkiesRing ≃+* ElkiesRing :=
  RingEquiv.ofRingHom negRHom negRHom negRHom_invol negRHom_invol

theorem negS_T : negS eT = eT := by
  show negSHom eT = _; simp [negSHom, elkiesLift_T]
theorem negS_S : negS eS = -eS := by
  show negSHom eS = _; simp [negSHom, elkiesLift_S]
theorem negS_R : negS eR = eR := by
  show negSHom eR = _; simp [negSHom, elkiesLift_R]
theorem negR_T : negR eT = eT := by
  show negRHom eT = _; simp [negRHom, elkiesLift_T]
theorem negR_S : negR eS = eS := by
  show negRHom eS = _; simp [negRHom, elkiesLift_S]
theorem negR_R : negR eR = -eR := by
  show negRHom eR = _; simp [negRHom, elkiesLift_R]

end Ring

theorem unit_cast_sq {R : Type*} [Ring R] (c : ℤˣ) : ((c : ℤ) : R) ^ 2 = 1 := by
  rcases Int.units_eq_one_or c with rfl | rfl <;> simp

/-- Sign changes `(s, r) ↦ (c s, d r)` on the conic's `ℚ̄`-points (on the points at infinity
`b ↦ c d b`, since `b = r/s`). -/
noncomputable def signAct (c d : ℤˣ) : HDec.X6Kummer.ConicPt → HDec.X6Kummer.ConicPt
  | Sum.inl p => Sum.inl ⟨(((c : ℤ) : Qbar) * p.1.1, ((d : ℤ) : Qbar) * p.1.2), by
      have hc : ((c : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have hd : ((d : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have := p.2
      simp only at this ⊢
      linear_combination (p.1.2 ^ 2) * hd + 3 * p.1.1 ^ 2 * hc + this⟩
  | Sum.inr b => Sum.inr ⟨((((c * d : ℤˣ)) : ℤ) : Qbar) * b.1, by
      have hc : ((((c * d : ℤˣ)) : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have := b.2
      linear_combination (b.1 ^ 2) * hc + this⟩


/-! ## The charts: rational functions `t, s, r` and the action of a `t`-preserving automorphism -/

section Charts

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left} [IsIntegral X.left]

/-- `ElkiesRing → Γ(t.U) → ℚ(X)`. -/
noncomputable abbrev jU (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (hηU : genericPoint X.left ∈ t.U) :
    ElkiesRing →+* X.left.functionField :=
  (X.left.presheaf.germ t.U _ hηU).hom.comp (φU : ElkiesRing →+* Γ(X.left, t.U))

/-- `ElkiesRing → Γ(t.V) → ℚ(X)`. -/
noncomputable abbrev jV (φV : ElkiesRing ≃+* Γ(X.left, t.V)) (hηV : genericPoint X.left ∈ t.V) :
    ElkiesRing →+* X.left.functionField :=
  (X.left.presheaf.germ t.V _ hηV).hom.comp (φV : ElkiesRing →+* Γ(X.left, t.V))

variable (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))
  (hηU : genericPoint X.left ∈ t.U) (hηV : genericPoint X.left ∈ t.V)

theorem jU_injective : Function.Injective (jU φU hηU) :=
  (germ_injective_of_isIntegral X.left _ hηU).comp φU.injective

theorem germ_inv_rel (hT : φU eT = t.f) (hTg : φV eT = t.g) : jU φU hηU eT * jV φV hηV eT = 1 := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) t.inv
  rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV, hT, hTg] using this

theorem germ_glue1
    (hg1 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1) :
    jU φU hηU eS * jV φV hηV eS = 1 := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) hg1
  rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV] using this

theorem germ_glue2
    (hg2 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR)) :
    jU φU hηU eR * jV φV hηV eS = jV φV hηV eR := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) hg2
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV] using this

theorem sigma_inv_of {F : Type*} [Field F] (σ : F →+* F) (a b : F) (c : ℤˣ)
    (hS : σ a = ((c : ℤ) : F) * a) (h1 : a * b = 1) : σ b = ((c : ℤ) : F) * b := by
  have e := congrArg σ h1
  rw [map_mul, map_one, hS] at e
  have hc := unit_cast_sq (R := F) c
  linear_combination (((c : ℤ) : F) * b) * e - σ b * ((c : ℤ) : F) ^ 2 * h1 - σ b * hc

theorem mem_preimage_gen (g : X.left ≅ X.left) {A : X.left.Opens} (h : genericPoint X.left ∈ A) :
    genericPoint X.left ∈ g.hom ⁻¹ᵁ A := by
  show g.hom (genericPoint X.left) ∈ A
  rw [genericPoint_eq_of_isOpenImmersion g.hom]
  exact h

omit [IsIntegral X.left] in
theorem mem_preimage_pt (g : X.left ≅ X.left) {A : X.left.Opens} (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (h : (Scheme.SpecToEquivOfField Qbar X.left (y ≫ g.hom)).1 ∈ A) :
    (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ g.hom ⁻¹ᵁ A := by
  show g.hom _ ∈ A
  rw [← pt_comp]
  exact h

theorem pullback_jU (g : X.left ≅ X.left) (a : ElkiesRing) :
    ffPullback g (jU φU hηU a) =
      X.left.presheaf.germ (g.hom ⁻¹ᵁ t.U) _ (mem_preimage_gen g hηU) (g.hom.app t.U (φU a)) := by
  simp only [jU, RingHom.comp_apply, RingHom.coe_coe]
  exact ffPullback_germ g t.U hηU _ _

theorem pullback_jV (g : X.left ≅ X.left) (a : ElkiesRing) :
    ffPullback g (jV φV hηV a) =
      X.left.presheaf.germ (g.hom ⁻¹ᵁ t.V) _ (mem_preimage_gen g hηV) (g.hom.app t.V (φV a)) := by
  simp only [jV, RingHom.comp_apply, RingHom.coe_coe]
  exact ffPullback_germ g t.V hηV _ _

variable {φU φV}

include hηV in
/-- A `t`-preserving automorphism maps `t.U = {t ≠ ∞}` onto itself (on `ℚ̄`-points). -/
theorem memU_comp_iff (hT : φU eT = t.f) (hTg : φV eT = t.g) (g : X.left ≅ X.left)
    (hτ : ffPullback g (jU φU hηU eT) = jU φU hηU eT) (y : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    pt (X := X) (y ≫ g.hom) ∈ t.U ↔ pt (X := X) y ∈ t.U := by
  have hinv := germ_inv_rel φU φV hηU hηV hT hTg
  have hτ' : ffPullback g (jV φV hηV eT) = jV φV hηV eT := by
    have e := congrArg (ffPullback g) hinv
    rw [map_mul, map_one, hτ] at e
    rw [eq_inv_of_mul_eq_one_right e, eq_inv_of_mul_eq_one_right hinv]
  have gf : X.left.presheaf.germ t.U _ hηU t.f = jU φU hηU eT := by simp [jU, hT]
  have gg : X.left.presheaf.germ t.V _ hηV t.g = jV φV hηV eT := by simp [jV, hTg]
  constructor
  · intro h'
    by_contra h
    have hv := memV_of_not_memU (X := X) (t := t) y h
    have h0 := ev_g_eq_zero (X := X) (t := t) y h hv
    have hm := mem_preimage_pt g y h'
    have key := ev_mul_eq_one_of_germ (mem_preimage_gen g hηU) hηV (g.hom.app t.U t.f) t.g
      (by rw [← ffPullback_germ g t.U hηU, gf, gg, hτ, hinv]) y hm hv
    rw [h0, mul_zero] at key
    exact zero_ne_one key
  · intro h
    by_contra h'
    have hv := memV_of_not_memU (X := X) (t := t) (y ≫ g.hom) h'
    have h0 := ev_g_eq_zero (X := X) (t := t) (y ≫ g.hom) h' hv
    have hm := mem_preimage_pt g y hv
    rw [ev_comp_hom g.hom t.V y hv hm] at h0
    have key := ev_mul_eq_one_of_germ (mem_preimage_gen g hηV) hηU (g.hom.app t.V t.g) t.f
      (by rw [← ffPullback_germ g t.V hηV, gf, gg, hτ', mul_comm, hinv]) y hm h
    rw [h0, zero_mul] at key
    exact zero_ne_one key

end Charts

/-- `ℚ(X₆)^W`: the rational functions on `X₆` fixed by every `g ∈ W` (`g^*φ = φ`). -/
def fixedByW {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set X.left.functionField :=
  {φ | ∀ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, ffPullback (Z := X.left) ((Over.forget _).mapIso g) φ = φ}

/-- LEAF draft. -/
def ElkiesX6StarFF : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∃ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
      fixedByW Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

end HDec.QMSplit.Moduli.ElkiesCoord

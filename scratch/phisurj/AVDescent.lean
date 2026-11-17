import ZInQKernel.Contrib.OneProof.PhiSurjDescent
import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.MumfordSquareMulN

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj.AVDesc

open PicDict PkgI3 PkgI3.AbVar PicDict.Transport WeilProof WeilProof.Theta

variable {k : Type} [Field k]

/-- `[n]` is étale, surjective and proper (from weil-proof's `divisibleAC` argument). -/
theorem mul_props [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Etale (AC.mul X n).left ∧ Surjective (AC.mul X n).left ∧ IsProper (AC.mul X n).left := by
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have hP : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  refine ⟨hE', ⟨fun y => ?_⟩, hP⟩
  have : y ∈ Set.range f := by rw [hrange]; trivial
  exact this

/-- `[n]` generates an fpqc covering. -/
theorem mul_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Sieve.ofArrows (fun _ : PUnit.{1} => X.X.left) (fun _ => (AC.mul X n).left) ∈
      Scheme.fpqcTopology X.X.left := by
  obtain ⟨hE, hS, hP⟩ := mul_props X n hnk
  change Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage _)

lemma tr_left_comp_mul {X : AbVar k} {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) :
    (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
  rw [← Over.comp_left, AC.tr_comp_mul x hx]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n]`, are open immersions. -/
theorem sec_isOpenImmersion [IsAlgClosed k] {X : AbVar k} {n : ℕ} [hF : Fact ((n : k) ≠ 0)] (x : AC.Kpt X) (hx : x ^ n = 1) :
    IsOpenImmersion (Desc.sec (AC.mul X n).left (tr_left_comp_mul x hx)) := by
  obtain ⟨hE, -, -⟩ := mul_props X n (Fact.out)
  exact ZInQ.Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section _
    (pullback.fst (AC.mul X n).left (AC.mul X n).left) (pullback.lift_fst _ _ _)

lemma kpt_comp_tr {X : AbVar k} (y x : AC.Kpt X) : y ≫ AC.tr x = y * x := by
  simp only [AC.tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (y ≫ CartesianMonoidalCategory.toUnit X.X) (𝟙 _),
    Category.id_comp]

lemma kpt_comp_mul {X : AbVar k} (y : AC.Kpt X) (n : ℕ) : y ≫ AC.mul X n = y ^ n := by
  simp only [AC.mul]
  rw [MonObj.comp_pow, Category.comp_id]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n](k)`, cover `X ×_{[n],X,[n]} X` (on points). -/
theorem sec_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (y : (pullback (AC.mul X n).left (AC.mul X n).left : Scheme)) :
    ∃ i : {x : AC.Kpt X // x ^ n = 1},
      y ∈ Set.range (Desc.sec (AC.mul X n).left (tr_left_comp_mul i.1 i.2)).base := by
  obtain ⟨hE, -, -⟩ := mul_props X n hnk
  let m := (AC.mul X n).left
  have hmw : m ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  let str : pullback m m ⟶ Spec (CommRingCat.of k) := pullback.fst m m ≫ X.X.hom
  have : LocallyOfFiniteType str := by dsimp [str]; infer_instance
  have : JacobsonSpace (pullback m m : Scheme) := LocallyOfFiniteType.jacobsonSpace str
  by_contra hy
  push_neg at hy
  let V : Set (pullback m m : Scheme) :=
    ⋃ i : {x : AC.Kpt X // x ^ n = 1}, Set.range (Desc.sec m (tr_left_comp_mul i.1 i.2)).base
  have hVo : IsOpen V := by
    refine isOpen_iUnion fun i => ?_
    have := sec_isOpenImmersion (n := n) (hF := ⟨hnk⟩) i.1 i.2
    exact (Desc.sec m (tr_left_comp_mul i.1 i.2)).isOpenEmbedding.isOpen_range
  have hZ : (Vᶜ).Nonempty := ⟨y, by simpa [V] using hy⟩
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints hZ hVo.isClosed_compl.isLocallyClosed
  let σ := pointOfClosedPoint str z hzc
  have hσ : σ ≫ str = 𝟙 _ := pointOfClosedPoint_comp str z hzc
  let x1 : AC.Kpt X := Over.homMk (σ ≫ pullback.fst m m) (by
    change (σ ≫ pullback.fst m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc]; exact hσ)
  let x2 : AC.Kpt X := Over.homMk (σ ≫ pullback.snd m m) (by
    change (σ ≫ pullback.snd m m) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc, ← hmw, ← Category.assoc (pullback.snd m m), ← pullback.condition, Category.assoc,
      hmw]
    exact hσ)
  have hx12 : x1 ≫ AC.mul X n = x2 ≫ AC.mul X n := by
    apply Over.OverMorphism.ext
    change (σ ≫ pullback.fst m m) ≫ m = (σ ≫ pullback.snd m m) ≫ m
    rw [Category.assoc, Category.assoc, pullback.condition]
  rw [kpt_comp_mul, kpt_comp_mul] at hx12
  let x := x1⁻¹ * x2
  have hx : x ^ n = 1 := by
    simp only [x, mul_pow, inv_pow, hx12, inv_mul_cancel]
  apply hzZ
  refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
  have hsec : x1.left ≫ Desc.sec m (tr_left_comp_mul x hx) = σ := by
    apply pullback.hom_ext
    · simp [x1]
    · have h2 : (x1 ≫ AC.tr x).left = x2.left := by
        rw [kpt_comp_tr]
        congr 1
        simp only [x, mul_inv_cancel_left]
      simp only [Category.assoc, pullback.lift_snd]
      exact h2
  refine ⟨x1.left (IsLocalRing.closedPoint k), ?_⟩
  have e := congrArg (fun f : Spec (CommRingCat.of k) ⟶ (pullback m m : Scheme) =>
    f.base (IsLocalRing.closedPoint k)) hsec
  simp only [Scheme.Hom.comp_base] at e
  have hσz : σ.base (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply str z hzc _
  rw [hσz] at e
  exact e

/-- A trivialization of `n^*M` exists when `n^*c = 1`. -/
theorem nonempty_triv_ac {X : AbVar k} {n : ℕ} {c : X.X.left.Pic}
    (h : Scheme.Pic.map (AC.mul X n).left c = 1) : Nonempty (AC.Triv X n c) := by
  obtain ⟨e⟩ := Scheme.Pic.eq_iff_nonempty_iso.1 h
  exact ⟨(Scheme.Pic.oneIso).symm ≪≫ e.symm ≪≫ Scheme.Pic.mkIso _⟩

/-- **The right kernel of Mumford's pairing is trivial** (Mumford §20, the descent half): over `k = k̄`, for `n`
invertible, if `ψ : 𝒪 ≅ n^*M` has Mumford's formula `1` at every `x ∈ X[n](k)`, then `M ≅ 𝒪`. -/
theorem formula_nondeg_right [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0)
    (c : X.X.left.Pic) (ψ : AC.Triv X n c)
    (h : ∀ (x : AC.Kpt X) (hx : x ^ n = 1), AC.formula x hx c ψ = 1) : c = 1 := by
  have hF : Fact ((n : k) ≠ 0) := ⟨hnk⟩
  have hM : (AC.modX c).IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent c.isInvertible
  have hsurj : ⨆ i : {x : AC.Kpt X // x ^ n = 1},
      @Scheme.Hom.opensRange _ _ (Desc.sec (AC.mul X n).left (tr_left_comp_mul i.1 i.2))
        (sec_isOpenImmersion i.1 i.2) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := sec_cover X n hnk y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hinv : ∀ i : {x : AC.Kpt X // x ^ n = 1},
      (pOU (AC.tr i.1).left).inv ≫ (Scheme.Modules.pullback (AC.tr i.1).left).map ψ.hom ≫
        (Scheme.Modules.pullbackComp (AC.tr i.1).left (AC.mul X n).left).hom.app (AC.modX c) ≫
        (Scheme.Modules.pullbackCongr (tr_left_comp_mul i.1 i.2)).hom.app (AC.modX c) ≫ ψ.inv = 𝟙 _ := by
    intro i
    have hi := h i.1 i.2
    unfold AC.formula at hi
    rw [wf_eq_alpha] at hi
    apply (Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit _)).injective
    rw [Scheme.Modules.unitHomAddEquiv_apply, Scheme.Modules.unitHomAddEquiv_apply]
    exact hi.trans rfl
  obtain ⟨e⟩ := @Desc.nonempty_iso_of_invariant X.X.left (AC.mul X n).left (mul_cover X n hnk)
    {x : AC.Kpt X // x ^ n = 1} (fun i => (AC.tr i.1).left) (fun i => tr_left_comp_mul i.1 i.2)
    (fun i => sec_isOpenImmersion i.1 i.2) hsurj (AC.modX c) hM ψ hinv
  exact Scheme.Pic.eq_iff_nonempty_iso.2 ⟨e.symm ≪≫ (Scheme.Pic.oneIso).symm⟩

/-! ## Counting `X̂[n]` -/

/-- `X(k)[n]`. -/
def torsK (X : AbVar k) (n : ℕ) : Subgroup (AC.Kpt X) := (powMonoidHom n : AC.Kpt X →* AC.Kpt X).ker

lemma mem_torsK {X : AbVar k} {n : ℕ} {x : AC.Kpt X} : x ∈ torsK X n ↔ x ^ n = 1 := by
  simp [torsK]

/-- `Spec L` over itself, as the unit object. -/
def unitIsoL (L : Type) [Field L] : PkgI2.specOver L L ≅ 𝟙_ (Over (Spec (CommRingCat.of L))) :=
  Over.isoMk (Iso.refl _) (by simp [PkgI2.specOver])

/-- `X(k)[n] ≅ (ℤ/n)^{2g}` from Mumford's theorem (the textbook leaf), transported to `k`-points. -/
theorem exists_torsK_addEquiv [IsAlgClosed k] (hT : AvSplit.MumfordTorsionAlgClosed) (X : AbVar k)
    (g n : ℕ) (hg : topologicalKrullDim X.X.left = g) (hn : 0 < n) (hnk : (n : k) ≠ 0) :
    Nonempty (Additive (torsK X n) ≃+ (Fin (2 * g) → ZMod n)) := by
  have := isAV X
  obtain ⟨e, he⟩ := hT k (grpOf X) g n hg hn hnk
  let φ : AC.Kpt X ≃ PkgI2.Pts (grpOf X) k :=
    { toFun := fun x => (unitIsoL k).hom ≫ x
      invFun := fun z => (unitIsoL k).inv ≫ z
      left_inv := fun x => by simp
      right_inv := fun z => by simp }
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := fun x y => by
    change (unitIsoL k).hom ≫ (x * y) = ((unitIsoL k).hom ≫ x) * ((unitIsoL k).hom ≫ y)
    exact MonObj.comp_mul _ _ _
  have hφpow : ∀ x (m : ℕ), φ (x ^ m) = φ x ^ m := fun x m => by
    change (unitIsoL k).hom ≫ (x ^ m) = ((unitIsoL k).hom ≫ x) ^ m
    exact MonObj.comp_pow _ _ _
  have hφone : φ 1 = 1 := by simpa using hφpow 1 0
  let ψ : torsK X n ≃ PkgI2.torsion (grpOf X) k n :=
    Equiv.subtypeEquiv φ (by
      intro x
      change x ∈ torsK X n ↔ φ x ^ n = 1
      rw [mem_torsK, ← hφpow, ← hφone, φ.injective.eq_iff])
  refine ⟨AddEquiv.mk' (Additive.toMul.trans (ψ.trans e)) ?_⟩
  intro x y
  have hmem : (ψ (Additive.toMul x)).1 * (ψ (Additive.toMul y)).1 ∈ PkgI2.torsion (grpOf X) k n := by
    have h := (ψ (Additive.toMul (x + y))).2
    have e1 : (ψ (Additive.toMul (x + y))).1 = (ψ (Additive.toMul x)).1 * (ψ (Additive.toMul y)).1 :=
      hφmul _ _
    rwa [e1] at h
  have e2 : ψ (Additive.toMul (x + y)) = ⟨_, hmem⟩ := Subtype.ext (hφmul _ _)
  simp only [Equiv.trans_apply]
  rw [e2, he]

/-- Homomorphisms out of `(ℤ/n)^m` into a finite group: at most `#M^m`. -/
theorem card_hom_le {G : Type*} [AddCommGroup G] {M : Type*} [AddCommGroup M] [Finite M] {n m : ℕ}
    [NeZero n] (E : G ≃+ (Fin m → ZMod n)) : Nat.card (G →+ M) ≤ Nat.card M ^ m := by
  classical
  let basis : Fin m → G := fun i => E.symm (Pi.single i 1)
  have hspan : ∀ x : G, x = ∑ i, (E x i).val • basis i := by
    intro x
    apply E.injective
    rw [map_sum]
    simp only [map_nsmul, basis, AddEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    · intro i _ hij
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hinj : Function.Injective (fun f : G →+ M => fun i => f (basis i)) := by
    intro f f' h
    ext x
    rw [hspan x, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, map_nsmul]
    exact congrArg _ (congrFun h i)
  calc Nat.card (G →+ M) ≤ Nat.card (Fin m → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ m := by simp [Nat.card_fun]

lemma const_injective [IsAlgClosed k] (X : AbVar k) : Function.Injective (AC.const X) := by
  have : Nonempty (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : Nonempty X.X.left := ⟨η[X.X].left (Nonempty.some inferInstance)⟩
  have : Nonempty (⊤ : X.X.left.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  exact (X.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).injective

end PhiSurj.AVDesc

#print axioms PhiSurj.AVDesc.formula_nondeg_right

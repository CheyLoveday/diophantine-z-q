import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel

/-!
# Consistency of the new-local model

The GLUE input `NewLocalModel b dK hK cE tK` is used as a hypothesis (`clearingModel_of_newLocal`).
This file checks that its fields are jointly satisfiable (`newLocalModel_trivial`, PROVED): the
trivial pre-cancellation complex (no Smith disks, no new places, `D¹ = H₁`, `D² = H₂`, all
differentials zero), with Selmer data `G = C`, `U = L = 0` for the family, the trivial support
change (old part into the full complex) at augmentation, and central ranks `(0, 1, 1, 0)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks aug)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.RankCounts.SmithCx

/-! ### The central counts for Smith data without disks -/

section Budget

variable {S : Type} [CommRing S] (B : SmithBlocks S OO) (hn : B.n = 3) (hm : ∀ i, B.m i = 0)

include hn hm in
theorem dd_empty (i : ℕ) : dd B i = 0 := by
  unfold dd
  split_ifs
  · exact hm i
  · rfl

include hn hm in
theorem subsingleton_centralH_three_empty : Subsingleton ((centralH B) fr₀ 3) := by
  have e := Hequiv (f := fr₀) (σ B) (σ_ne B) 3
  have : Subsingleton ((Fin (fr₀ 3) → ℤ_[2]) × Q (σ B) 3) := by
    have h1 : Subsingleton (Fin (fr₀ 3) → ℤ_[2]) :=
      ⟨fun a b => funext fun j => (show Fin 0 from j).elim0⟩
    have h2 : Subsingleton (Q (σ B) 3) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
      congr 1
      funext j
      have hj : db (dd B) 3 = 0 := dd_empty B hn hm 2
      exact (Fin.cast hj j).elim0
    infer_instance
  exact e.toEquiv.subsingleton

include hn hm in
theorem sum_val_σ_empty (i : ℕ) : ∑ j, ((σ B) i j).valuation = 0 := by
  have : IsEmpty (Fin (dd B i)) := by rw [dd_empty B hn hm]; infer_instance
  simp

include hn hm in
/-- **The (5.7) counts for Smith data without disks**, with all constants `0`. -/
theorem budgetInputs_of_empty : BudgetInputs B 0 0 0 0 := by
  have hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0 := fun i _ _ => hm i
  have hmTot : B.mTot = 0 := by simp [SmithBlocks.mTot, hm]
  refine ⟨fr₀, ?_, (centralH B) fr₀ 1, (centralH B) fr₀ 2, PUnit, PUnit, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, LinearEquiv.refl _ _, LinearMap.id, 0, 0, 0,
    ⟨Function.injective_id, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sum_finrank_centralCx B fr₀ hamp, hmTot, Fin.sum_univ_four]
    simp [fr₀]
  · intro x; simp
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x; exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · intro x
    have := subsingleton_centralH_three_empty B hn hm
    exact ⟨0, Subsingleton.elim _ _⟩
  · rw [length_torsion_H (σ B) (σ_ne B) 1, length_Q_succ (σ B) (σ_ne B) 0,
      sum_val_σ_empty B hn hm]
  · simp
  · rw [length_torsion_H (σ B) (σ_ne B) 2, length_Q_succ (σ B) (σ_ne B) 1,
      sum_val_σ_empty B hn hm]
  · simp
  · simp [finrank_centralH, fr₀]
  · simp [finrank_centralH, fr₀]

end Budget

/-! ### Selmer data with only a global complex -/

section TrivSel

variable {S : Type} [CommRing S]

/-- Selmer data `G --0--> 0 <--0-- 0`. -/
def trivSelG (G : GCx S) : SelData S where
  G := G
  U := zeroGCx S
  L := zeroGCx S
  res := zeroGHom _ _
  ι := zeroGHom _ _

/-- `G^n ≅ G^n ⊕ 0 ⊕ 0`. -/
def trivSelGEquiv (G : GCx S) (n : ℤ) : G.X n ≃ₗ[S] selT (trivSelG G) n :=
  letI : Unique (PUnit.{1} × PUnit.{1}) :=
    { default := ⟨PUnit.unit, PUnit.unit⟩, uniq := fun _ => Subsingleton.elim _ _ }
  (LinearEquiv.prodUnique (R := S) (M := G.X n) (M₂ := PUnit × PUnit)).symm

/-- The isomorphism of `G` with the Selmer complex of `trivSelG G`. -/
def trivSelGIso (G : GCx S) : G.toCC ≅ (selCx (trivSelG G)).toCC := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (trivSelGEquiv G n).toModuleIso) ?_
  intro i j hij
  change i + 1 = j at hij
  subst hij
  ext x
  change ((selCx (trivSelG G)).toCC.d i (i + 1)).hom (trivSelGEquiv G i x) =
    trivSelGEquiv G (i + 1) ((G.toCC.d i (i + 1)).hom x)
  refine (GCx.toCC_d_hom _ i (i + 1) rfl _).trans ?_
  refine Eq.trans ?_ (congrArg (trivSelGEquiv G (i + 1)) (GCx.toCC_d_hom G i (i + 1) rfl x)).symm
  exact Prod.ext rfl (Prod.ext rfl rfl)

theorem trivSelG_qis (G : GCx S) : QuasiIso (trivSelGIso G).hom := quasiIso_of_isIso _

/-- The support change along a chain map `g : G → G⁺` with zero local data. -/
def trivSupportChange (G Gp : GCx S) (g : GHom G Gp) : SelmerDuality.SupportChangeData S where
  D := trivSelG G
  Dp := trivSelG Gp
  g := g
  lam := zeroGHom _ _
  mu := zeroGHom _ _
  r := zeroGHom _ _
  hres _ _ _ _ := rfl
  hι _ _ _ _ := rfl

theorem trivSupportChange_square (G Gp : GCx S) (g : GHom G Gp) :
    (trivSelGIso G).hom ≫ SelmerDuality.GHom.toCC
        (SelmerDuality.supportMap (trivSupportChange G Gp g)) =
      SelmerDuality.GHom.toCC g ≫ (trivSelGIso Gp).hom := by
  ext n x
  change ((g.f n n rfl x, 0 + 0, 0) : Gp.X n × PUnit × PUnit) = (g.f n n rfl x, 0, 0)
  rfl

end TrivSel

/-! ### The trivial new-local model -/

variable {b : ℕ}

/-- The trivial pre-cancellation complex over `Λ[G]`. -/
def preTriv (b : ℕ) : PreComplex (MonoidAlgebra Lam (SignGroup b)) where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Empty
  c0 := 0
  X := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := 0
  c1_c0 := by simp
  c2_c1 := by simp

instance : IsEmpty (preTriv b).N := inferInstanceAs (IsEmpty Empty)

/-- The (empty) new local blocks. -/
def ATriv : Empty → Matrix Empty Empty Lam := fun q => q.elim

def eTriv (b : ℕ) : (preTriv b).N ≃ Empty × Empty := Equiv.equivOfIsEmpty _ _

theorem hdetTriv : ∀ q : Empty, (ATriv q).det =
    (PowerSeries.X : Lam) ^ (fun q : Empty => (q.elim : ℕ)) q *
      ((fun q : Empty => (q.elim : Lamˣ)) q : Lam) + 2 * (fun q : Empty => (q.elim : Lam)) q :=
  fun q => q.elim

theorem hB0Triv : ((preTriv b).B.submatrix (eTriv b).symm (eTriv b).symm).map aug =
    Matrix.blockDiagonal ATriv := by
  ext i; exact i.1.elim

theorem hYTriv : (preTriv b).Y.map (augR b) = 0 := by
  ext i; exact (show Empty from i).elim

theorem hTTriv : (preTriv b).T.map (augR b) = 0 := by
  ext i; exact (show Empty from i).elim

/-- The remaining complex of the trivial model. -/
abbrev remTriv (b : ℕ) : BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  remOf ATriv (fun q => q.elim) (fun q => q.elim) (fun q => q.elim) (fun q => q.elim) hdetTriv
    (preTriv b) (eTriv b) hB0Triv

theorem preTriv_old_mi (i : ℕ) : (((preTriv b).map (augR b)).old hYTriv hTTriv).mi i = 0 := by
  rcases i with _ | _ | _ | i <;> rfl

/-- **Consistency of the new-local model** (PROVED): the trivial model satisfies every field. -/
def newLocalModel_trivial (b : ℕ) : NewLocalModel b 0 0 0 0 where
  Qn := Empty
  ιn := Empty
  A := ATriv
  dq := fun q => q.elim
  hd := fun q => q.elim
  v := fun q => q.elim
  w := fun q => q.elim
  hdet := hdetTriv
  C := preTriv b
  eN := eTriv b
  hB0 := hB0Triv
  hT0 := hTTriv
  hY0 := hYTriv
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central := fun i => by
    ext j
    have h1 := preTriv_old_mi (b := b) i
    have h2 := j.2
    omega
  budget := budgetInputs_of_empty _ rfl fun i => by rcases i with _ | _ | _ | i <;> rfl
  sel := trivSelG _
  ψ := (trivSelGIso _).hom
  qis := trivSelG_qis _
  sc := trivSupportChange _ _ (((preTriv b).map (augR b)).oldIncl hYTriv hTTriv)
  ψ0 := (trivSelGIso _).hom
  qis0 := trivSelG_qis _
  ψold := (trivSelGIso _).hom
  qisOld := trivSelG_qis _
  square := trivSupportChange_square _ _ _

theorem newLocalModel_nonempty (b : ℕ) : Nonempty (NewLocalModel b 0 0 0 0) :=
  ⟨newLocalModel_trivial b⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

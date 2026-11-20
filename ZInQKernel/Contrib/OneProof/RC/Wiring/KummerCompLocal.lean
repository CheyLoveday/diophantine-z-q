import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge

/-!
# Theorem 5.3, Lane RC37: local Kummer theory for the coefficient comparison

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, the local Kummer condition
(tex 3413–3438): for the local twist over `F = K_v` the condition `U_F = B(F)^∧_2[−1]` of the
compact Kummer complex reduces modulo `2^a` to the finite Kummer condition, with
`B(F)/2^a B(F)` in degree one. The coefficient comparison uses both directions of this reduction
at the level of cochains, for the integral Kummer lattice
`localKummerLattice W hFull v = tateKummerZ W hFull v ⊔ B¹_cont` inside the continuous
`1`-cochains of `G_{K_v}` with values in `T₂E`, and the level-`m` coordinates
`localTatePoint W v m : T₂E → E(K̄_v)`.

* `kcLevelTrivial W v m`: the `ℤ₂`-submodule of local cochains whose level-`m` coordinate is a
  Galois coboundary `σ ↦ σ R − R` of one point `R ∈ E(K̄_v)`.
* `kcLattice_coboundary` (B1): every cochain of the integral Kummer lattice is level-trivial at
  every level `m` (`kcLattice_le_levelTrivial`): a Kummer cocycle gives the point `R_m` of its
  tower, a coboundary `d c` the level-`m` point of `c`, and `a • y` the point `(a mod 2^m) • R`
  (the level-`m` coordinate is `2^m`-torsion).
* `kcDivide_of_level`: a local cochain with vanishing level-`m` coordinates is `2^m` times a
  continuous cochain.
* `kcLattice_lift` (B2): conversely, if the level-`m` coordinate of `φ` is the coboundary of
  `R ∈ E(K̄_v)`, then `φ = u + d c + 2^m w` with `u` in the integral Kummer lattice: `2^m R` is
  `G_{K_v}`-fixed, hence a point `P₀ ∈ E(K_v)` (Galois descent), `u` is the Kummer cocycle of
  `P₀`, and `D_m − R` (for the chosen tower `D` of `P₀`) is the level-`m` coordinate of some
  `t ∈ T₂E` (full `2`-power torsion), with `c` the constant cochain `−t`.
* `kcLocalKummer_iff` (B3): finite-level local Kummer exactness: a continuous `1`-cochain with
  values in `E(K̄_v)[2^m]` is a Galois coboundary in `E(K̄_v)` iff it lies in the finite Kummer
  condition `kummerZ ⊔ B¹_cont` (`kcFiniteTrivial`, `kcFinite_le_finiteTrivial`); no cocycle
  hypothesis is needed.

Kinds: definitions and PROVED. The only hypothesis is the full `2`-power torsion `hFull` already
carried by the compact Kummer complex.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Manuscript.RC

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Manuscript.RC53Assist.CentralKummer ZInQ.Contrib.RC53Assist.CalibrationShape
  ZInQ.Contrib.RC53Assist.Finiteness

section LocalKummerComparison

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

attribute [local instance] levTop continuousSMul_lev

/-- The local integral cochains whose level-`m` coordinate, read in `E(K̄_v)`, is the Galois
coboundary `σ ↦ σ R − R` of a single point `R ∈ E(K̄_v)`. Kind: definition. -/
def kcLevelTrivial (m : ℕ) : Submodule ℤ_[2] (localTateCochain (S := S) W v 1) where
  carrier := {y | ∃ R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)),
    ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
      cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ)) = σ • R - R}
  zero_mem' := ⟨0, fun σ => by
    rw [smul_zero, sub_self]
    exact map_zero (localTatePoint W v m)⟩
  add_mem' := by
    rintro y₁ y₂ ⟨R₁, h₁⟩ ⟨R₂, h₂⟩
    refine ⟨R₁ + R₂, fun σ => ?_⟩
    change localTatePoint W v m
      ((show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y₁ (fun _ => σ)) +
        (show TateS K S W from
          cfun (M := ResMod (locMap K S v) (TateS K S W)) y₂ (fun _ => σ))) = _
    rw [map_add, h₁, h₂, smul_add]
    abel
  smul_mem' := by
    rintro a y ⟨R, h⟩
    refine ⟨resN m a • R, fun σ => ?_⟩
    change localTatePoint W v m
      (a • (show TateS K S W from
        cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ))) = _
    rw [localTatePoint_apply, TateS.pt_padicSmul, map_nsmul, ← localTatePoint_apply, h,
      smul_sub, smul_comm σ (resN m a) R]

/-- Membership in `kcLevelTrivial`. Kind: PROVED. -/
theorem kcLevelTrivial_mem_iff (m : ℕ) (y : localTateCochain (S := S) W v 1) :
    y ∈ kcLevelTrivial W v m ↔
      ∃ R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)),
        ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
          cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ)) = σ • R - R :=
  Iff.rfl

/-- The `2`-adic Kummer cocycle of a local point is level-trivial: its level-`m` coordinate is
the Galois coboundary of the `m`-th point of the chosen tower. Kind: PROVED. -/
theorem kcTateKummerCocycle_mem_levelTrivial (m : ℕ)
    (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) :
    tateKummerCocycle W hFull v P ∈ kcLevelTrivial W v m :=
  ⟨divTower _ _ P m, fun σ =>
    localTatePoint_kummer W hFull v (isDivTower_divTower _ _ P) m (fun _ => σ)⟩

/-- A continuous coboundary is level-trivial: its level-`m` coordinate is the Galois coboundary
of the level-`m` point of its degree-zero value. Kind: PROVED. -/
theorem kcBoundary_mem_levelTrivial (m : ℕ) (c : localTateCochain (S := S) W v 0) :
    contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c ∈
      kcLevelTrivial W v m :=
  ⟨_, fun σ => localTatePoint_boundary W v c m (fun _ => σ)⟩

/-- The integral Kummer lattice is level-trivial at every level. Kind: PROVED. -/
theorem kcLattice_le_levelTrivial (m : ℕ) :
    localKummerLattice W hFull v ≤ kcLevelTrivial W v m := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨P, rfl⟩
    exact kcTateKummerCocycle_mem_levelTrivial W hFull v m P
  · intro b hb
    obtain ⟨c, rfl⟩ := (mem_contB1_iff b).1 hb
    exact kcBoundary_mem_levelTrivial W v m c

/-- **(B1)** The level-`m` reduction of the integral Kummer lattice is locally trivial in
`H¹(K_v, E(K̄_v))`: the level-`m` coordinate of every cochain of the lattice is a Galois
coboundary of a point of `E(K̄_v)`. Kind: PROVED. -/
theorem kcLattice_coboundary (m : ℕ) (y : localTateCochain (S := S) W v 1)
    (hy : y ∈ localKummerLattice W hFull v) :
    ∃ R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)),
      ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
        cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ)) = σ • R - R :=
  kcLattice_le_levelTrivial W hFull v m hy

omit [W.IsElliptic] [DecidableEq (v.adicCompletion K)] in
/-- A local cochain whose level-`m` coordinates vanish is `2^m` times a continuous cochain
(division of each value in the Tate module, continuous for the inverse-limit topology).
Kind: PROVED. -/
theorem kcDivide_of_level (m : ℕ) (ψ : localTateCochain (S := S) W v 1)
    (hψ : ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
      cfun (M := ResMod (locMap K S v) (TateS K S W)) ψ (fun _ => σ)) = 0) :
    ∃ w : localTateCochain (S := S) W v 1, ψ = (2 : ℤ_[2]) ^ m • w := by
  have h0 : ∀ x : Fin 1 → Gloc K v,
      (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) ψ x).pt m = 0 := by
    intro x
    have hx : (fun _ : Fin 1 => x 0) = x := by
      funext j
      fin_cases j
      rfl
    apply compPt_injective W v
    have h := hψ (x 0)
    rw [hx] at h
    rw [map_zero]
    exact h
  refine ⟨⟨(fun x => (show ResMod (locMap K S v) (TateS K S W) from
      tateShift m (show TateS K S W from
        cfun (M := ResMod (locMap K S v) (TateS K S W)) ψ x) (h0 x)) :
      (Fin 1 → Gloc K v) → ResMod (locMap K S v) (TateS K S W)),
    continuous_tateShift m (fun x => (show TateS K S W from
      cfun (M := ResMod (locMap K S v) (TateS K S W)) ψ x)) ψ.2 h0⟩, ?_⟩
  apply Subtype.ext
  funext x
  exact (two_pow_smul_tateShift m _ (h0 x)).symm

/-- **(B2)** The converse lifting: if the level-`m` coordinate of a local cochain `φ` is the
Galois coboundary of `R ∈ E(K̄_v)`, then `φ` is a cochain of the integral Kummer lattice plus a
continuous coboundary plus `2^m` times a continuous cochain. (`2^m R` is `G_{K_v}`-fixed, hence
a point `P₀ ∈ E(K_v)`; `u` is the Kummer cocycle of `P₀`; `D_m − R` is a `2^m`-torsion point,
the level-`m` coordinate of some `t ∈ T₂E`, and `c` is the constant cochain `−t`.)
Kind: PROVED. -/
theorem kcLattice_lift (m : ℕ) (φ : localTateCochain (S := S) W v 1)
    (R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)))
    (hR : ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
      cfun (M := ResMod (locMap K S v) (TateS K S W)) φ (fun _ => σ)) = σ • R - R) :
    ∃ u ∈ localKummerLattice W hFull v, ∃ (c : localTateCochain (S := S) W v 0)
      (w : localTateCochain (S := S) W v 1),
      φ = u + contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c +
        (2 : ℤ_[2]) ^ m • w := by
  have htors : ∀ t : TateS K S W, (2 ^ m : ℕ) • localTatePoint W v m t = 0 := by
    intro t
    have h : (2 ^ m : ℕ) • t.pt m = 0 := two_pow_nsmul_lev (projLev m t)
    rw [localTatePoint_apply, ← map_nsmul, h, map_zero]
  have hfix : ∀ σ : Gloc K v, σ • ((2 ^ m : ℕ) • R) = (2 ^ m : ℕ) • R := by
    intro σ
    rw [smul_comm, ← sub_eq_zero, ← smul_sub, ← hR σ]
    exact htors _
  obtain ⟨P₀, hP₀⟩ := exists_basePt_of_fixed hfix
  have hD := isDivTower_divTower (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) P₀
  have hX : divTower _ _ P₀ m - R ∈ AddSubgroup.torsionBy
      (PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))) ((2 ^ m : ℕ) : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, hD.two_pow_smul m, hP₀, sub_self]
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  obtain ⟨t, ht⟩ := projLev_surjective (K := K) (S := S) (W := W) m
    ((compTorsEquiv W (2 ^ m) (hFull m) v).symm ⟨divTower _ _ P₀ m - R, hX⟩)
  have hXt : localTatePoint W v m t = divTower _ _ P₀ m - R := by
    have h1 : compTors W (2 ^ m) v (projLev m t) = ⟨divTower _ _ P₀ m - R, hX⟩ := by
      rw [ht, ← compTorsEquiv_apply W (2 ^ m) (hFull m), AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  obtain ⟨c, hc⟩ : ∃ c : localTateCochain (S := S) W v 0,
      (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) c default) = -t :=
    ⟨constCochain (k := ℤ_[2]) (G := Gloc K v)
      (show ResMod (locMap K S v) (TateS K S W) from -t), rfl⟩
  have hψ : ∀ σ : Gloc K v, localTatePoint W v m (show TateS K S W from
      cfun (M := ResMod (locMap K S v) (TateS K S W))
        (φ - tateKummerCocycle W hFull v P₀ -
          contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c)
        (fun _ => σ)) = 0 := by
    intro σ
    change localTatePoint W v m
      ((show TateS K S W from
          cfun (M := ResMod (locMap K S v) (TateS K S W)) φ (fun _ => σ)) -
        (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W))
          (tateKummerCocycleOf W hFull v hD) (fun _ => σ)) -
        (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W))
          (contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c)
          (fun _ => σ))) = 0
    rw [map_sub, map_sub, hR, localTatePoint_kummer W hFull v hD m,
      localTatePoint_boundary W v c m, hc, map_neg, hXt]
    change σ • R - R - (σ • divTower _ _ P₀ m - divTower _ _ P₀ m) -
      (σ • -(divTower _ _ P₀ m - R) - -(divTower _ _ P₀ m - R)) = 0
    rw [smul_neg, smul_sub]
    abel
  obtain ⟨w, hw⟩ := kcDivide_of_level W v m _ hψ
  refine ⟨tateKummerCocycle W hFull v P₀, tateKummerCocycle_mem_lattice W hFull v P₀, c, w, ?_⟩
  rw [← hw]
  abel

/-- The continuous `1`-cochains with values in `E(K̄_v)[2^m]` which are Galois coboundaries
`σ ↦ σ R − R` of a single point `R ∈ E(K̄_v)`. Kind: definition. -/
def kcFiniteTrivial (m : ℕ) : Submodule ℤ (contCochain ℤ (Gloc K v)
    (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) 1) where
  carrier := {f | ∃ R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)),
    ∀ σ : Gloc K v, ((cfun f (fun _ => σ) : TorsAlg _ _ (2 ^ m)) : PtAlg _ _) = σ • R - R}
  zero_mem' := ⟨0, fun σ => by
    rw [smul_zero, sub_self]
    rfl⟩
  add_mem' := by
    rintro f₁ f₂ ⟨R₁, h₁⟩ ⟨R₂, h₂⟩
    refine ⟨R₁ + R₂, fun σ => ?_⟩
    change (cfun f₁ (fun _ => σ)).val + (cfun f₂ (fun _ => σ)).val = _
    rw [h₁, h₂, smul_add]
    abel
  smul_mem' := by
    rintro a f ⟨R, h⟩
    refine ⟨a • R, fun σ => ?_⟩
    change a • (cfun f (fun _ => σ)).val = _
    rw [h, smul_sub, smul_comm σ a R]

/-- A finite-level Kummer cocycle is the Galois coboundary of its chosen division point.
Kind: PROVED. -/
theorem kcKummerCocycle_mem_finiteTrivial (m : ℕ)
    (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) :
    kummerCocycle (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m) P ∈
      kcFiniteTrivial W v m :=
  ⟨divPt _ _ (2 ^ m) P, fun _ => rfl⟩

omit [W.IsElliptic] [DecidableEq (v.adicCompletion K)] in
/-- A continuous coboundary with values in `E(K̄_v)[2^m]` is the Galois coboundary of its
degree-zero value. Kind: PROVED. -/
theorem kcBoundary_mem_finiteTrivial (m : ℕ) (c : contCochain ℤ (Gloc K v)
      (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) 0) :
    contD ℤ (Gloc K v)
        (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) 0 c ∈
      kcFiniteTrivial W v m :=
  ⟨((cfun c default : TorsAlg _ _ (2 ^ m)) : PtAlg _ _), fun σ => by
    rw [contD_zero_apply]
    rfl⟩

/-- The finite-level Kummer condition `kummerZ ⊔ B¹_cont` consists of Galois coboundaries in
`E(K̄_v)`. Kind: PROVED. -/
theorem kcFinite_le_finiteTrivial (m : ℕ) :
    kummerZ (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m) ⊔
        contB1 ℤ (Gloc K v)
          (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) ≤
      kcFiniteTrivial W v m := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨P, rfl⟩
    exact kcKummerCocycle_mem_finiteTrivial W v m P
  · intro b hb
    obtain ⟨c, rfl⟩ := (mem_contB1_iff b).1 hb
    exact kcBoundary_mem_finiteTrivial W v m c

/-- **(B3)** Finite-level local Kummer exactness: a continuous `1`-cochain with values in
`E(K̄_v)[2^m]` is a Galois coboundary `σ ↦ σ R − R` of a point `R ∈ E(K̄_v)` iff it lies in the
finite-level Kummer condition `kummerZ ⊔ B¹_cont`. (If `f σ = σ R − R` then `2^m R` is
`G_{K_v}`-fixed, hence a point `P₀ ∈ E(K_v)`, and `f` is the Kummer cocycle of the division
point `R` of `P₀`.) No cocycle hypothesis is needed. Kind: PROVED. -/
theorem kcLocalKummer_iff (m : ℕ)
    (f : contCochain ℤ (Gloc K v)
      (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) 1) :
    (∃ R : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)),
      ∀ σ : Gloc K v, ((cfun f (fun _ => σ) : TorsAlg _ _ (2 ^ m)) : PtAlg _ _) = σ • R - R) ↔
      f ∈ kummerZ (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m) ⊔
        contB1 ℤ (Gloc K v)
          (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ m)) := by
  refine ⟨fun ⟨R, hR⟩ => ?_, fun hf => kcFinite_le_finiteTrivial W v m hf⟩
  have hfix : ∀ σ : Gloc K v, σ • ((2 ^ m : ℕ) • R) = (2 ^ m : ℕ) • R := by
    intro σ
    rw [smul_comm, ← sub_eq_zero, ← smul_sub, ← hR σ]
    exact AddSubgroup.torsionBy.nsmul_iff.1 (cfun f (fun _ => σ)).2
  obtain ⟨P₀, hP₀⟩ := exists_basePt_of_fixed hfix
  have hf : f = kummerCocycleOf (v.adicCompletion K) (W.baseChange (v.adicCompletion K))
      (2 ^ m) hP₀.symm := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    have hg : (fun _ : Fin 1 => g 0) = g := by
      funext j
      fin_cases j
      rfl
    have h := hR (g 0)
    rw [hg] at h
    exact h
  rw [hf]
  exact kummerCocycleOf_mem_sup _ _ _ _

end LocalKummerComparison

end ZInQ.Manuscript.RC

import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.MackeyCor

/-!
# HeegnerCohomology, part 13: the old Kummer conditions survive the coefficient push

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3257–3267:

"At `2N`, the deformation character `Ψ` is trivial locally; the fixed quadratic character need
not be trivial.  Under the fixed quadratic-twist identification, the local map is the ordinary
integral norm on Kummer classes.  One can see this without a projector: the sum
`∑_δ χ(δ) δ Q` is a point of the quadratic twist over the lower field, and Kummer of this sum
equals the cohomological transfer.  The extra `A` coefficients take finite linear combinations of
such maps.  Thus the old Kummer conditions proved in paragraph 5 survive (H20), also in the
universal family with its common local quadratic type."

Setting (as in `MackeyCor.lean`): `G = G_K`, `H = G_{H_f}`, the twisted action `R = θ ρ` on a module
`M` that contains the division points (for `E(K̄) ⊗ A`); `D` the decomposition group at a place
`v ∣ 2N` of `K`, `O = D δ₀` the orbit of a place `w` of `H_f` above `v`, `D₀` its stabilizer,
`s` a lift of `δ₀`, `H_w = s⁻¹ D₀ s ⊆ H` the decomposition group of `w`.  The class `b` (values
killed by `k = 2^m`) satisfies the old Kummer condition at `w`: `b(h) = h Q̃ - Q̃` on `H_w` for a
division point `Q̃` of a local point `Q = k Q̃`.  Then (all `PROVED`):

* `bTrans_kummer`: the transported cocycle is the Kummer cocycle of `R(s) Q̃`;
* `old_kummer_survives`: the orbit term of the pushed class (the localization of (H21) at `v`,
  restricted to the orbit, for any global section) is *exactly* the Kummer cocycle
  `d ↦ R(d) P̃ - P̃` of a point `P̃` with `k P̃ = ∑_u R(t_u s) Q = ∑_{δ ∈ O} θ(r_δ)ρ(r_δ) Q`
  (compatible representatives), the twisted local norm `∑_δ χ(δ) δ Q`;
* `twisted_norm_fixed`: if `Q` is a local point at `w` (fixed by `H_w`), the twisted norm is fixed
  by `D` under `R`: it is a point of the twist over the lower local field;
* `KummerCond`, `KummerCond.add`, `KummerCond.smul`, `KummerCond.sum`: the Kummer condition
  ("Kummer cocycle of a point whose `k`-multiple lies in an `A`-submodule `S` of local points") is
  stable under finite `A`-linear combinations (the extra `A` coefficients).

That `θ` restricted to `D` is the fixed quadratic character (`Ψ` locally trivial) is not used: the
statements hold for any character `θ`; the identification of `M(θ)|_D` with the quadratic twist
is the standard one and enters only through the reading of `R = θρ` on `D`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset TauCeti TauCeti.ContCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)
  (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
  {D : Subgroup G} {δ₀ : G ⧸ H}

theorem smul_TwM_val (x : stab H D δ₀) (m : TwM H ρ θ) :
    (x • m).val = R H ρ θ (((x : D) : G)) m.val := rfl

/-- **The transported cocycle of a Kummer cocycle is a Kummer cocycle** (tex 3258–3262), `PROVED`:
if `b(h) = h Q̃ - Q̃` on `H_w = s⁻¹ D₀ s`, then `b_s(x) = x • R(s) Q̃ - R(s) Q̃` on `D₀`. -/
theorem bTrans_kummer (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (Qt : M)
    (hK : ∀ x : stab H D δ₀, b ⟨s⁻¹ * ((x : D) : G) * s, conj_mem_of_stab H s hs x⟩ =
      ρ (s⁻¹ * ((x : D) : G) * s) Qt - Qt) (x : stab H D δ₀) :
    bTrans H ρ θ s hs b x = x • (⟨R H ρ θ s Qt⟩ : TwM H ρ θ) - ⟨R H ρ θ s Qt⟩ := by
  apply TwM.ext'
  rw [TwM.val_sub, smul_TwM_val]
  show R H ρ θ s (b _) = _
  rw [hK x, map_sub, ← R_of_mem H ρ θ (conj_mem_of_stab H s hs x), ← Module.End.mul_apply,
    ← R_mul, ← Module.End.mul_apply, ← R_mul]
  congr 3
  group

variable [(stab H D δ₀).FiniteIndex] (t : D ⧸ stab H D δ₀ → D)
  (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ stab H D δ₀) = u)

include ht in
/-- **The old Kummer conditions survive the coefficient push** (tex 3257–3267), `PROVED`: for a
cocycle `b` with values killed by `k` satisfying the Kummer condition at `w`
(`b(h) = h Q̃ - Q̃` on `H_w`), the orbit term of the pushed class at `v` is, for any global section,
exactly the Kummer cocycle `d ↦ R(d) P̃ - P̃` of a point `P̃` with
`k P̃ = ∑_u R(t_u s) (k Q̃)`: "Kummer of this sum equals the cohomological transfer". -/
theorem old_kummer_survives [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀)
    (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) (k : ℤ) (hbk : ∀ x, k • b x = 0)
    (Qt : M)
    (hK : ∀ x : stab H D δ₀, b ⟨s⁻¹ * ((x : D) : G) * s, conj_mem_of_stab H s hs x⟩ =
      ρ (s⁻¹ * ((x : D) : G) * s) Qt - Qt) :
    ∃ Pt : M, k • Pt = ∑ u, R H ρ θ (((t u : D) : G) * s) (k • Qt) ∧
      ∀ d : D, orbitTerm H ρ θ r hr (univ.image (phi H t)) b d = R H ρ θ d Pt - Pt := by
  obtain ⟨w, hwk, hw⟩ := orbitTerm_eq_cor_add_coboundary H ρ θ r hr t ht s hs b hb
  have hbT : bTrans H ρ θ s hs b = d0 (stab H D δ₀) (TwM H ρ θ) ⟨R H ρ θ s Qt⟩ := by
    funext x
    rw [bTrans_kummer H ρ θ s hs b Qt hK x, d0_apply]
  refine ⟨∑ u, R H ρ θ (((t u : D) : G) * s) Qt + w, ?_, fun d => ?_⟩
  · rw [smul_add, hwk k hbk, add_zero, smul_sum]
    exact sum_congr rfl fun u _ => (map_zsmul _ _ _).symm
  · rw [hw d, hbT, cochainsCor1_d0, d0_apply, TwM.val_sub, Subgroup.smul_def, TwM.val_smul,
      TwM.val_sum]
    have e : ∀ u, (t u • (⟨R H ρ θ s Qt⟩ : TwM H ρ θ)).val =
        R H ρ θ (((t u : D) : G) * s) Qt := fun u => by
      rw [Subgroup.smul_def, TwM.val_smul, R_mul, Module.End.mul_apply]
    simp only [e, map_add, map_sub]
    abel

include ht in
/-- **The twisted local norm is a point over the lower field** (tex 3259–3261: "the sum
`∑_δ χ(δ) δ Q` is a point of the quadratic twist over the lower field"), `PROVED`: if `Q` is fixed
by `H_w = s⁻¹ D₀ s` (a local point at `w`), then `∑_u R(t_u s) Q` is fixed by `R(d)` for `d ∈ D`. -/
theorem twisted_norm_fixed (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (Q : M)
    (hQ : ∀ x : stab H D δ₀, ρ (s⁻¹ * ((x : D) : G) * s) Q = Q) (d : D) :
    R H ρ θ d (∑ u, R H ρ θ (((t u : D) : G) * s) Q) = ∑ u, R H ρ θ (((t u : D) : G) * s) Q := by
  have hmem : (⟨R H ρ θ s Q⟩ : TwM H ρ θ) ∈ H0 (stab H D δ₀) (TwM H ρ θ) := by
    rw [FixedPoints.mem_addSubgroup]
    intro x
    apply TwM.ext'
    rw [smul_TwM_val, ← Module.End.mul_apply, ← R_mul,
      show ((x : D) : G) * s = s * (s⁻¹ * ((x : D) : G) * s) by group, R_mul, Module.End.mul_apply,
      R_of_mem H ρ θ (conj_mem_of_stab H s hs x), hQ x]
  have h := sum_transversal_smul_mem_H0 D (TwM H ρ θ) (stab H D δ₀) t ht hmem
  have e : ∀ u, (t u • (⟨R H ρ θ s Q⟩ : TwM H ρ θ)).val = R H ρ θ (((t u : D) : G) * s) Q :=
    fun u => by rw [Subgroup.smul_def, TwM.val_smul, R_mul, Module.End.mul_apply]
  have hd := congrArg TwM.val ((FixedPoints.mem_addSubgroup _ _ _).mp h d)
  rw [Subgroup.smul_def, TwM.val_smul, TwM.val_sum] at hd
  simpa only [e] using hd

/-! ## The `A`-linear combinations -/

/-- The Kummer condition for a `D`-cochain `c` with values in `M(θ)`: `c = d(X)` for some `X`
whose `k`-multiple lies in the `A`-submodule `S` (local points of the twist over the lower field). -/
def KummerCond (k : ℤ) (S : Submodule A M) (c : D → M) : Prop :=
  ∃ X : M, k • X ∈ S ∧ ∀ d : D, c d = R H ρ θ d X - X

theorem KummerCond.add {k : ℤ} {S : Submodule A M} {c c' : D → M}
    (h : KummerCond H ρ θ k S c) (h' : KummerCond H ρ θ k S c') :
    KummerCond H ρ θ k S (c + c') := by
  obtain ⟨X, hX, hc⟩ := h
  obtain ⟨Y, hY, hc'⟩ := h'
  refine ⟨X + Y, by rw [smul_add]; exact S.add_mem hX hY, fun d => ?_⟩
  simp only [Pi.add_apply, hc d, hc' d, map_add]
  abel

theorem KummerCond.smul {k : ℤ} {S : Submodule A M} {c : D → M} (a : A)
    (h : KummerCond H ρ θ k S c) : KummerCond H ρ θ k S (a • c) := by
  obtain ⟨X, hX, hc⟩ := h
  refine ⟨a • X, by rw [smul_comm]; exact S.smul_mem a hX, fun d => ?_⟩
  simp only [Pi.smul_apply, hc d, map_smul, smul_sub]

theorem KummerCond.zero (k : ℤ) (S : Submodule A M) : KummerCond H ρ θ k S (D := D) 0 :=
  ⟨0, by simp, fun d => by simp⟩

/-- **Finite `A`-linear combinations of Kummer cocycles are Kummer** (tex 3262–3263: "the extra
`A` coefficients take finite linear combinations of such maps"), `PROVED`. -/
theorem KummerCond.sum {ι : Type*} (s : Finset ι) {k : ℤ} {S : Submodule A M} (a : ι → A)
    (c : ι → D → M) (h : ∀ i ∈ s, KummerCond H ρ θ k S (c i)) :
    KummerCond H ρ θ k S (∑ i ∈ s, a i • c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using KummerCond.zero H ρ θ k S
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (KummerCond.smul H ρ θ (a i) (h i (mem_insert_self i s))).add H ρ θ
      (ih fun j hj => h j (mem_insert_of_mem hj))

end TwistedTransfer

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Node: the old Kummer conditions survive the coefficient push**, tex 3257–3267, `PROVED`: in
the setting of `MackeyCorNode`, if the class `b` (values killed by `k`) satisfies the Kummer
condition at the place `w` (`b(h) = h Q̃ - Q̃` on `H_w = s⁻¹ D₀ s`) for a local point `Q = k Q̃` at
`w` (fixed by `H_w`), and `S` is an `A`-submodule of `M` containing the twisted local norm of `Q`,
then the orbit term of the pushed class at the place below satisfies the Kummer condition for the
twist over the lower local field (`KummerCond` with `S`). -/
def OldKummerSurvivesNode : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (r : G ⧸ H → G)
    (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (D : Subgroup G) (δ₀ : G ⧸ H)
    [(TwistedTransfer.stab H D δ₀).FiniteIndex] [DecidableEq (G ⧸ H)]
    (t : D ⧸ TwistedTransfer.stab H D δ₀ → D)
    (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ TwistedTransfer.stab H D δ₀) = u)
    (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (_hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) (k : ℤ) (_hbk : ∀ x, k • b x = 0) (Qt : M)
    (_hK : ∀ x : TwistedTransfer.stab H D δ₀,
      b ⟨s⁻¹ * ((x : D) : G) * s, TwistedTransfer.conj_mem_of_stab H s hs x⟩ =
        ρ (s⁻¹ * ((x : D) : G) * s) Qt - Qt)
    (S : Submodule A M)
    (_hS : ∑ u, TwistedTransfer.R H ρ θ (((t u : D) : G) * s) (k • Qt) ∈ S),
    TwistedTransfer.KummerCond H ρ θ k S
      (TwistedTransfer.orbitTerm H ρ θ r hr (Finset.univ.image (TwistedTransfer.phi H t)) b ∘
        (fun d : D => (d : G)))

theorem oldKummerSurvivesNode_proof : OldKummerSurvivesNode := by
  intro G _ H _ r hr A M _ _ _ ρ θ D δ₀ _ _ t ht s hs b hb k hbk Qt hK S hS
  obtain ⟨Pt, hPt, hP⟩ :=
    TwistedTransfer.old_kummer_survives H ρ θ r hr t ht s hs b hb k hbk Qt hK
  exact ⟨Pt, by rw [hPt]; exact hS, fun d => hP d⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

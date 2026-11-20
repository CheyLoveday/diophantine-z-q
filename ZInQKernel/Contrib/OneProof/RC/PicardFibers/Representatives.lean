import ZInQKernel.Contrib.OneProof.RC.PicardFibers.LocalConjugacy
import ZInQKernel.Contrib.OneProof.RC.Eichler.Stabilizer

/-! Tex 9150–9160: rationally frame the actual support orbits and form
their admissible integral representatives. On-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler O7Actual O7Orbits Visibility

set_option maxHeartbeats 1200000

section Patching

variable {a b : ℚ} {R : Order a b}

/-- The rational affine generator is integral in every completed conjugate
of the chosen order. -/
def AdelicAdmissible (α : B a b) (z : Adelic.FiniteUnits R) : Prop :=
  ∀ p : Adelic.Prime, unitConjRing (z.val p)⁻¹ (toLocal p.val α) ∈ R.completion p.val

/-- Local witnesses at all primes can be patched with identity outside
the labeled primes and the finite set of denominators. -/
theorem patch_admissible_adele (R : Order a b) (α : B a b) (S : Finset Adelic.Prime)
    (P : (p : Adelic.Prime) → (Bp p.val a b)ˣ → Prop)
    (h : ∀ p : Adelic.Prime, ∃ u : (Bp p.val a b)ˣ,
      unitConjRing u⁻¹ (toLocal p.val α) ∈ R.completion p.val ∧ (p ∈ S → P p u)) :
    ∃ z : Adelic.FiniteUnits R, AdelicAdmissible α z ∧ ∀ p ∈ S, P p (z.val p) := by
  classical
  let T := (S : Set Adelic.Prime) ∪ {p | toLocal p.val α ∉ R.completion p.val}
  have hT : T.Finite := S.finite_toSet.union (Adelic.finite_not_mem_completion R α)
  let z (p : Adelic.Prime) := if p ∈ T then (h p).choose else 1
  let z₀ : Adelic.FiniteUnits R := ⟨z, hT.subset fun p hp => by
    by_contra hn
    apply hp
    simpa only [z, ite_eq_right hn] using (Adelic.localUnits R p).one_mem⟩
  refine ⟨z₀, ?_, ?_⟩
  · intro p
    change unitConjRing (z p)⁻¹ (toLocal p.val α) ∈ R.completion p.val
    by_cases hp : p ∈ T
    · simpa only [z, ite_eq_left hp] using (h p).choose_spec.1
    · have hi : toLocal p.val α ∈ R.completion p.val :=
        not_not.mp fun hn => hp (Or.inr hn)
      simpa only [z, ite_eq_right hp, inv_one, unitConjRing_apply, Units.val_one, one_mul, mul_one]
        using hi
  · intro p hp
    change P p (z p)
    simpa only [z, ite_eq_left (show p ∈ T from Or.inl hp)] using (h p).choose_spec.2 hp

private theorem transport_local {B : Type*} [Ring B] (u z r : Bˣ) (x : B) :
    unitConjRing (u * z * r)⁻¹ (unitConjRing u x) =
      unitConjRing r⁻¹ (unitConjRing z⁻¹ x) := by
  simp only [unitConjRing_mul]
  congr 1
  group

/-- Integral local conjugation preserves membership in the completed order. -/
theorem local_mem_conj_iff (p : Adelic.Prime) (u : Adelic.localUnits R p) (y : Bp p.val a b) :
    unitConjRing u.val y ∈ R.completion p.val ↔ y ∈ R.completion p.val := by
  constructor
  · intro hy
    have h : unitConjRing u.val⁻¹ (unitConjRing u.val y) = y := by
      rw [unitConjRing_mul, inv_mul_cancel, unitConjRing_apply]
      simp
    rw [← h]
    have hu := u.prop
    rw [unitConjRing_apply, inv_inv]
    exact (R.completion p.val).mul_mem ((R.completion p.val).mul_mem hu.2 hy) hu.1
  · intro h
    rw [unitConjRing_apply]
    exact (R.completion p.val).mul_mem ((R.completion p.val).mul_mem u.prop.1 h) u.prop.2

/-- The ideal class reached by an adelic representative. -/
def adelicClass (z : Adelic.FiniteUnits R) : ClassSet R :=
  Adelic.idealsEquiv R (Quotient.mk _ z)

/-- Choose a rational translation from the given representative to the
one used by the visibility stage. -/
theorem exists_frame (z : Adelic.FiniteUnits R) :
    ∃ (g : (B a b)ˣ) (r : Adelic.integralUnits R),
      Adelic.classRepresentative (adelicClass z) = Adelic.diagonal R g * z * r.val := by
  have h : (Quotient.mk (Adelic.doubleCosetRel R) z) =
      Quotient.mk _ (Adelic.classRepresentative (adelicClass z)) := by
    rw [← Adelic.classesEquiv_classRepresentative]
    exact (Adelic.idealsEquiv R).symm_apply_apply _ |>.symm
  exact Quotient.exact h

end Patching

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- Transport a rational root from an admissible adelic representative to
the chosen left order in its ideal class, using the very same right unit
as in the adelic relation. -/
def supportFromFrame (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0) (hn : nrd x₀ = index s D)
    {z : Adelic.FiniteUnits (ActualOrder s)} (hz : AdelicAdmissible α z)
    {c : ClassSet (ActualOrder s)} (g : (B (-1) (-(s.ell : ℚ)))ˣ)
    (r : Adelic.integralUnits (ActualOrder s))
    (hr : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z * r.val) :
    ActualSupport s D c := by
  let x := unitConjRing g x₀
  have hrx : x.re = 0 := (quat_re_conj g x₀).trans hx
  have hnx : nrd x = index s D := (nrd_conj g x₀).trans hn
  refine ⟨x, hrx, hnx, (H c x hrx hnx).mpr ?_⟩
  let t := unitConjRing g α
  have ht : t ∈ (classOrder s.weights.ha s.weights.hb c).ring := by
    apply (classOrder_mem_adelic s.weights.ha s.weights.hb c t).mpr
    intro p
    change unitConjRing ((Adelic.classRepresentative c).val p)⁻¹
      (toLocal p.val (unitConjRing g α)) ∈ (ActualOrder s).completion p.val
    rw [hr, unitConjRing_map]
    let u := Units.map (toLocal p.val).toMonoidHom g
    change unitConjRing (u * z.val p * r.val.val p)⁻¹
      (unitConjRing u (toLocal p.val α)) ∈ _
    rw [transport_local]
    exact (local_mem_conj_iff p (⟨r.val.val p, r.prop p⟩ : Adelic.localUnits (ActualOrder s) p)⁻¹
      _).mpr (hz p)
  refine ⟨⟨t, ht⟩, ?_⟩
  change 2 * unitConjRing g α - 1 = unitConjRing g x₀
  rw [← hα, map_sub, map_mul, map_ofNat, map_one]

/-- A representative with a fixed rational embedding gives a weighted
support orbit; choice of frame is removed by the left order action. -/
def orbitFromRep (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0) (hn : nrd x₀ = index s D)
    (z : {z : Adelic.FiniteUnits (ActualOrder s) // AdelicAdmissible α z}) :
    OrbitSet s.visibility (index s D) :=
  let g := (exists_frame z.val).choose
  let r := (exists_frame z.val).choose_spec.choose
  ⟨adelicClass z.val, Quotient.mk _ (supportFromFrame s H hα hx hn z.prop g r
    (exists_frame z.val).choose_spec.choose_spec)⟩


private theorem adelicClass_eq_of_translate {a b : ℚ} {R : Order a b} {z w : Adelic.FiniteUnits R}
    (g : (B a b)ˣ) (r : Adelic.integralUnits R)
    (h : w = Adelic.diagonal R g * z * r.val) :
    adelicClass z = adelicClass w :=
  congrArg (Adelic.idealsEquiv R) (Quotient.sound ⟨g, r, h⟩)

private theorem class_stabilizer_iff {a b : ℚ} {R : Order a b} (ha : a < 0) (hb : b < 0)
    (c : ClassSet R) (k : (B a b)ˣ) :
    k ∈ classG ha hb c ↔ ∃ b : Adelic.integralUnits R,
      Adelic.classRepresentative c = Adelic.diagonal R k * Adelic.classRepresentative c * b.val := by
  rw [← Adelic.fromAdelic_translate_iff, Adelic.fromAdelic_classRepresentative, eq_comm]
  exact RightIdeal.mem_G_iff_translate ha hb _ k

private theorem frame_cancel_forward {A G : Type*} [Group A] [Group G]
    (δ : A →* G) {q z w r t b : G} {g j k : A}
    (hg : q = δ g * z * r) (hj : q = δ j * w * t) (hk : q = δ k * q * b) :
    w = δ (j⁻¹ * k * g) * z * (r * b * t⁻¹) := by
  calc
    w = (δ j)⁻¹ * q * t⁻¹ := by rw [hj]; group
    _ = (δ j)⁻¹ * (δ k * q * b) * t⁻¹ := congrArg (fun q' => (δ j)⁻¹ * q' * t⁻¹) hk
    _ = _ := by rw [hg, map_mul, map_mul, map_inv]; group

private theorem frame_cancel_backward {A G : Type*} [Group A] [Group G]
    (δ : A →* G) {q z w r t b : G} {g j k : A}
    (hg : q = δ g * z * r) (hj : q = δ j * w * t) (hk : w = δ k * z * b) :
    q = δ (j * k * g⁻¹) * q * (r⁻¹ * b * t) := by
  calc
    q = δ j * w * t := hj
    _ = δ j * (δ k * z * b) * t := by rw [hk]
    _ = δ (j * k * g⁻¹) * (δ g * z * r) * (r⁻¹ * b * t) := by
      rw [map_mul, map_mul, map_inv]
      group
    _ = _ := by rw [← hg]

private theorem conj_value_commute {B : Type*} [Ring B] (u x : Bˣ) :
    unitConjRing u x.val = x.val ↔ Commute u x := by
  constructor
  · intro h
    apply Units.ext
    change (u : B) * (x : B) = (x : B) * (u : B)
    calc
      _ = (unitConjRing u x.val) * (u : B) := by
        rw [unitConjRing_apply, Units.inv_mul_cancel_right]
      _ = _ := by rw [h]
  · intro h
    have he : (u : B) * (x : B) = (x : B) * (u : B) := congrArg Units.val h.eq
    rw [unitConjRing_apply, he, Units.mul_inv_cancel_right]

private theorem same_class_orbit_iff (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    {z w : Adelic.FiniteUnits (ActualOrder s)} (hz : AdelicAdmissible α z)
    (hw : AdelicAdmissible α w) (c : ClassSet (ActualOrder s))
    (g j : (B (-1) (-(s.ell : ℚ)))ˣ)
    (r t : Adelic.integralUnits (ActualOrder s))
    (hg : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z * r.val)
    (hj : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) j * w * t.val) :
    Quotient.mk (@MulAction.orbitRel (s.visibility.G c) (s.visibility.supp c (index s D))
      _ (ThetaStage.conjAction s.visibility c (index s D)))
      (supportFromFrame s H hα hx hn hz g r hg) =
      Quotient.mk _ (supportFromFrame s H hα hx hn hw j t hj) ↔
    ∃ k : (B (-1) (-(s.ell : ℚ)))ˣ, Commute k x₀ ∧ ∃ b : Adelic.integralUnits (ActualOrder s),
      w = Adelic.diagonal (ActualOrder s) k * z * b.val := by
  let : MulAction (s.visibility.G c) (ActualSupport s D c) :=
    ThetaStage.conjAction s.visibility c (index s D)
  rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk⟩
    let k' := (k : (B (-1) (-(s.ell : ℚ)))ˣ)
    have he : unitConjRing k' (unitConjRing g x₀.val) = unitConjRing j x₀.val :=
      congrArg Subtype.val hk
    have hcomm : Commute (j⁻¹ * k' * g) x₀ := by
      apply (conj_value_commute _ _).mp
      calc
        _ = unitConjRing j⁻¹ (unitConjRing k' (unitConjRing g x₀.val)) := by
          simp only [unitConjRing_mul, mul_assoc]
        _ = _ := by rw [he, unitConjRing_mul, inv_mul_cancel, unitConjRing_apply]; simp
    obtain ⟨b, hb⟩ := (class_stabilizer_iff s.weights.ha s.weights.hb c k').mp k.prop
    exact ⟨_, hcomm, r * b * t⁻¹, frame_cancel_forward _ hg hj hb⟩
  · rintro ⟨k, hk, b, hb⟩
    let l := j * k * g⁻¹
    have hl : l ∈ classG s.weights.ha s.weights.hb c :=
      (class_stabilizer_iff s.weights.ha s.weights.hb c l).mpr
        ⟨r⁻¹ * b * t, frame_cancel_backward _ hg hj hb⟩
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    change unitConjRing l (unitConjRing g x₀.val) = unitConjRing j x₀.val
    have hl' : l * g = j * k := by dsimp [l]; group
    rw [unitConjRing_mul, hl', ← unitConjRing_mul, (conj_value_commute _ _).mpr hk]

/-- The only identifications in the support orbit are left rational
centralizer units and right integral order units. -/
theorem orbitFromRep_eq_iff (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (z w : {z : Adelic.FiniteUnits (ActualOrder s) // AdelicAdmissible α z}) :
    orbitFromRep s H hα hx hn z = orbitFromRep s H hα hx hn w ↔
      ∃ k : (B (-1) (-(s.ell : ℚ)))ˣ, Commute k x₀ ∧
        ∃ b : Adelic.integralUnits (ActualOrder s), w.val = Adelic.diagonal (ActualOrder s) k * z.val * b.val := by
  let g := (exists_frame z.val).choose
  let r := (exists_frame z.val).choose_spec.choose
  let j := (exists_frame w.val).choose
  let t := (exists_frame w.val).choose_spec.choose
  generalize hcz : adelicClass z.val = c
  have hg : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z.val * r.val := by
    rw [← hcz]; exact (exists_frame z.val).choose_spec.choose_spec
  generalize hcw : adelicClass w.val = d
  have hj : Adelic.classRepresentative d = Adelic.diagonal (ActualOrder s) j * w.val * t.val := by
    rw [← hcw]; exact (exists_frame w.val).choose_spec.choose_spec
  have hez : orbitFromRep s H hα hx hn z =
      ⟨c, Quotient.mk _ (supportFromFrame s H hα hx hn z.prop g r hg)⟩ := by
    subst c
    rfl
  have hew : orbitFromRep s H hα hx hn w =
      ⟨d, Quotient.mk _ (supportFromFrame s H hα hx hn w.prop j t hj)⟩ := by
    subst d
    rfl
  rw [hez, hew]
  by_cases hc : c = d
  · clear hcz hcw
    subst d
    have hi := same_class_orbit_iff s H x₀ hα hx hn z.prop w.prop c g j r t hg hj
    constructor
    · intro h
      exact hi.mp (eq_of_heq (Sigma.ext_iff.mp h).2)
    · intro h
      exact congrArg (fun q => (⟨c, q⟩ : OrbitSet s.visibility (index s D))) (hi.mpr h)
  · constructor
    · intro he
      exact (hc (congrArg Sigma.fst he)).elim
    · rintro ⟨k, _, b, hb⟩
      exact (hc (hcz.symm.trans ((adelicClass_eq_of_translate k b hb).trans hcw))).elim


private theorem adelicClass_classRepresentative {a b : ℚ} {R : Order a b} (c : ClassSet R) :
    adelicClass (Adelic.classRepresentative c) = c := by
  change Adelic.idealsEquiv R _ = _
  rw [← Adelic.classesEquiv_classRepresentative]
  exact (Adelic.idealsEquiv R).apply_symm_apply c

private theorem orbitFromRep_eq_frame (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (z : {z : Adelic.FiniteUnits (ActualOrder s) // AdelicAdmissible α z})
    (c : ClassSet (ActualOrder s)) (g : (B (-1) (-(s.ell : ℚ)))ˣ)
    (r : Adelic.integralUnits (ActualOrder s))
    (hg : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z.val * r.val) :
    orbitFromRep s H hα hx hn z =
      ⟨c, Quotient.mk _ (supportFromFrame s H hα hx hn z.prop g r hg)⟩ := by
  let j := (exists_frame z.val).choose
  let t := (exists_frame z.val).choose_spec.choose
  have he : adelicClass z.val = c :=
    (adelicClass_eq_of_translate g r hg).trans (adelicClass_classRepresentative c)
  revert hg
  subst c
  intro hg
  exact congrArg (fun q => (⟨adelicClass z.val, q⟩ : OrbitSet s.visibility (index s D)))
    ((same_class_orbit_iff s H x₀ hα hx hn z.prop z.prop _ j g t r
      (exists_frame z.val).choose_spec.choose_spec hg).mpr ⟨1, Commute.one_left _, 1, by simp⟩)

/-- A common rational embedding supplies a representative for every
actual support orbit by rational conjugacy. -/
theorem orbitFromRep_surjective (s : StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D) :
    Function.Surjective (orbitFromRep s H hα hx hn) := by
  rintro ⟨c, q⟩
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨g, hg⟩ := rational_conjugacy s.weights.ha s.weights.hb hx x.prop.1 x₀.ne_zero
      (hn.trans x.prop.2.1.symm)
    change unitConjRing g x₀.val = x.val at hg
    obtain ⟨t, ht⟩ := H.half c x
    have he : unitConjRing g α = t.val := by
      rw [← ht, ← hα, map_sub, map_mul, map_one, map_ofNat] at hg
      have htwo : IsUnit (2 : B (-1) (-(s.ell : ℚ))) := by
        simpa only [map_ofNat] using
          (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map
            (algebraMap ℚ (B (-1) (-(s.ell : ℚ))))
      exact htwo.mul_left_cancel (sub_left_inj.mp hg)
    let z := reframe s c g
    have hz : AdelicAdmissible α z := by
      intro p
      have hm := (classOrder_mem_adelic s.weights.ha s.weights.hb c t.val).mp t.prop p
      rw [← he] at hm
      change unitConjRing ((Adelic.classRepresentative c).val p)⁻¹
        (toLocal p.val (unitConjRing g α)) ∈ _ at hm
      rw [unitConjRing_map, unitConjRing_mul] at hm
      let k := Units.map (toLocal p.val).toMonoidHom g
      let v := (Adelic.classRepresentative c).val p
      change unitConjRing (k⁻¹ * v)⁻¹ (toLocal p.val α) ∈ _
      rw [show (k⁻¹ * v)⁻¹ = v⁻¹ * k by group]
      exact hm
    have hf : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z *
        (1 : Adelic.integralUnits (ActualOrder s)).val := by
      simp [z, reframe, ← mul_assoc]
    let Z : {z : Adelic.FiniteUnits (ActualOrder s) // AdelicAdmissible α z} := ⟨z, hz⟩
    have hsup : supportFromFrame s H hα hx hn Z.prop g 1 hf = x := Subtype.ext hg
    refine ⟨Z, ?_⟩
    rw [orbitFromRep_eq_frame s H x₀ hα hx hn Z c g 1 hf, hsup]

private theorem reframe_frame (s : StageAt O N M hN m)
    {c z g r} (h : Adelic.classRepresentative c = Adelic.diagonal (ActualOrder s) g * z *
      (r : Adelic.integralUnits (ActualOrder s)).val) :
    reframe s c g = z * r.val := by
  rw [reframe, h, map_inv]
  group

private theorem cancel_right_factor {G : Type*} [Group G] {H U : Subgroup G}
    {z w : G} (r t : U) :
    (∃ g : H, ∃ b : U, w * t.val = g.val * (z * r.val) * b.val) ↔
      ∃ g : H, ∃ b : U, w = g.val * z * b.val := by
  constructor
  · rintro ⟨g, b, h⟩
    refine ⟨g, r * b * t⁻¹, ?_⟩
    calc
      w = (w * t.val) * t.val⁻¹ := by group
      _ = _ := by rw [h]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rintro ⟨g, b, rfl⟩
    exact ⟨g, r⁻¹ * b * t, by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group⟩

/-- The actual orientation agrees precisely along the adelic centralizer
orbit, after allowing right integral units. -/
theorem orbitFromRep_orientation_iff (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (x₀ : (B (-1) (-(s.ell : ℚ)))ˣ) {α : B (-1) (-(s.ell : ℚ))}
    (hα : 2 * α - 1 = x₀.val) (hx : x₀.val.re = 0) (hn : nrd x₀.val = index s D)
    (z w : {z : Adelic.FiniteUnits (ActualOrder s) // AdelicAdmissible α z}) :
    orientation s H (orbitFromRep s H hα hx hn z) =
      orientation s H (orbitFromRep s H hα hx hn w) ↔
      ∃ g : adelicCentralizer (ActualOrder s) (Adelic.diagonal (ActualOrder s) x₀).val,
        ∃ r : Adelic.integralUnits (ActualOrder s), w.val = g.val * z.val * r.val := by
  let g := (exists_frame z.val).choose
  let r := (exists_frame z.val).choose_spec.choose
  let j := (exists_frame w.val).choose
  let t := (exists_frame w.val).choose_spec.choose
  let x := supportFromFrame s H hα hx hn z.prop g r (exists_frame z.val).choose_spec.choose_spec
  let y := supportFromFrame s H hα hx hn w.prop j t (exists_frame w.val).choose_spec.choose_spec
  change generatorOrientation s H (adelicClass z.val) x =
    generatorOrientation s H (adelicClass w.val) y ↔ _
  rw [actual_orientation_factor_iff s A H hh x₀ _ _ x y g j rfl rfl,
    reframe_frame s (exists_frame z.val).choose_spec.choose_spec,
    reframe_frame s (exists_frame w.val).choose_spec.choose_spec]
  exact cancel_right_factor r t

end ZInQ.Manuscript.RC.PicardFibers

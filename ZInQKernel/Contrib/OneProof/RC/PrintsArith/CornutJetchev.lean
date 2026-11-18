import Mathlib

/-!
# Cornut–Jetchev, Theorem 3.1: the one printed statement (Lanes RC9, RC12, RC27)

**The print.** C. Cornut and D. Jetchev, *Liftings of reduction maps for quaternion algebras*,
preprint, 17 pp., arXiv:1012.0725v1 [math.NT] (3 December 2010); the same text is the PDF on the first
author's web page cited by the manuscript (tex 11191–11193). Published version: Bull. London Math.
Soc. 45 (2013), 370–386, doi:10.1112/blms/bds098 (not read; its numbering is UNVERIFIED). Locators
(read in the preprint):
* Lemma 2.1 (§2.2, p. 4): the local counts `N(n', n'', δ)`, cases (i)–(iv);
* §3.1 (pp. 4–5): hypotheses H.1 (`Ram_f B ∩ S = ∅`), H.2 (`|S| + |Ram_f B| + [F : ℚ]` even),
  H.3 (every `v ∈ S` is inert or ramified in `K`);
* §3.2 (pp. 5–6): `θ_S = π_S⁻¹ ∘ φ_S : CM(G,H) → CM(G_S,H_S)` is a `Gal_K^ab`-equivariant map of
  discrete `Gal_K^ab`-sets (the action is left multiplication by `T(𝔸_f) = 𝔸_{K,f}^×` through
  `Art_K`); on orbit spaces it is the product (8) of local maps, bijective at `v ∉ S`;
* §3.3 (pp. 6–7): the fine conductors `c_f`, `c_{S,f}` ((10)) and the square (12): the conductor of
  `θ_S(x)` is the prime-to-`S` part of that of `x`;
* §3.4 (p. 8): `S' ⊆ S` the places inert in `K`, the sign maps `φ_{S'} = ψ_{S'} ∘ θ_S` with values in
  `(ℤ/2)^{|S'|}`, and formula (14), which defines `e_{S'}(c', c'')`;
* §3.5 (p. 9): **Theorem 3.1** and Corollary 3.2.

**The statement (Theorem 3.1, p. 9).** *Fix `(c', c'')` such that `v(c') − v(c'') ≡ v(𝔫) (mod 2)` for
every `v ∈ S'`. Let `c = c' ∩ c''` and
`κ = |Gal(K[c]/K[c_S])| ∏_{v ∈ S} N_v(v(c'), v(c''), v(𝔫))`. By restriction, the map `θ_S` induces a
surjective `κ`-to-1 correspondence `θ_S : c_f⁻¹(c', c'') → c_{S,f}⁻¹(c'_S, c''_S) ∩ ψ_{S'}⁻¹(e_{S'}(c', c''))`.*

**Lean form.** `CM(G,H)`, adelic quaternion groups, ring class fields and the Artin map are not in
Mathlib, so the objects are bundled abstractly in `CJSetting` (§§3.1–3.4); `CJSetting.Thm31` is the
single PRINT statement of Cornut–Jetchev in the project, with general `κ` given by the printed formula
(`CJSetting.kappa`, from the encoding `cjN` of Lemma 2.1). It is not used by
`restrictedConverseGenuine_of_leaves`: the headline's Cornut–Jetchev input is the pointwise
reduction identity, field `Visibility.ComparisonCore.reduction` (in `RC/Visibility/Models.lean`,
carried by the field `hcore` of `OddInstance` in `RC/Wiring/OddModels.lean`; kind ELLIOT citing
Theorem 3.1/Corollary 3.2 and §§4.9–4.10), which is not derived from `Thm31`. Lane RC12's `Odd.CornutJetchevThm31` is this
definition; lane RC9's `CJReductionData.Thm3_1KappaOne` (the `κ = 1` bijection of class-group
torsors) is DERIVED from it (`CJReductionData.thm3_1KappaOne_of_print`, `PrintsArith/Heegner.lean`).

DEPARTURE (of form, two readings, both forced):
1. "`κ`-to-1" is encoded as: every point of the target has exactly `κ` preimages in `c_f⁻¹(c', c'')`
   (`ENat.card` of the fibre, so the fibre is finite). The word "surjective" is not imposed
   separately: for `κ ≥ 1` it follows (`Thm31.exists_preimage`). For `κ = 0` (which occurs, e.g. at
   `v ∈ S'` with `v(𝔫) = 0` and `v(c') ≠ v(c'')`, Lemma 2.1) the source fibre is empty by Lemma 3.4(i)
   while the target can be nonempty by Lemma 3.4(ii); the literal word would then be false, so it is
   read as the fibre count. The manuscript uses only `κ = 1`.
2. The `Gal_K^ab`-equivariance of `θ_S` (§3.2, p. 6, part of the definition of the map in the
   theorem) is included as the first clause; the abstract acting group `Gal` stands for `T(𝔸_f)`
   acting through `Art_K`.

**Non-vacuity.** `cjToySetting_thm31`: an instance (two points, the manuscript's shape
`|S| + |Ram_f B| + [F : ℚ] = 1 + 0 + 1`, one inert place, `κ = 1`) satisfying `Thm31` together with
H.1–H.3 (satisfiable). `not_thm31_cjCollapseSetting`: an instance satisfying H.1–H.3 for which
`Thm31` is false (a non-injective `θ` with `κ = 1`), so the statement has content.
-/

namespace ZInQ.Manuscript.RC.PrintsArith

/-! ### Lemma 2.1 (p. 4): the local counts -/

/-- The local type of a finite place `v` of `F` in the quadratic algebra `K` (print §2: `K_v/F_v`
unramified, ramified, or `K_v ≅ F_v × F_v`). -/
inductive CJLocalType
  | inert
  | ramified
  | split
  deriving DecidableEq

/-- **Cornut–Jetchev, Lemma 2.1 (p. 4), the unramified case** (`K_v/F_v` unramified, residue field
of order `q`): `N(n', n'', δ)` is `1` if `δ = |n' - n''|`, `(q - 1) q^{r-1}` if
`δ = |n' - n''| + 2r` with `0 < r < min(n', n'')` (case i), `q^{min(n', n'')}` if `δ = n' + n''`
(case ii), and `0` otherwise. (Lane RC9's encoding, unchanged.) -/
def cjNUnram (q n₁ n₂ δ : ℕ) : ℕ :=
  if δ = n₁ + n₂ then q ^ min n₁ n₂
  else if max n₁ n₂ - min n₁ n₂ ≤ δ ∧ (δ - (max n₁ n₂ - min n₁ n₂)) % 2 = 0 ∧
      (δ - (max n₁ n₂ - min n₁ n₂)) / 2 < min n₁ n₂ then
    (if δ = max n₁ n₂ - min n₁ n₂ then 1
      else (q - 1) * q ^ ((δ - (max n₁ n₂ - min n₁ n₂)) / 2 - 1))
  else 0

/-- **`N_{ℓ₀}(0, 0, 0) = 1`** (App. F tex 9238–9242, "which also follows directly from
[Lemma 2.1(ii)]"), PROVED from the encoding of Lemma 2.1. -/
theorem cjNUnram_zero (q : ℕ) : cjNUnram q 0 0 0 = 1 := by
  simp [cjNUnram]

/-- **Lemma 2.1 (p. 4), the ramified case** (`K_v/F_v` ramified): case (i) as above, and case (iii):
`δ = n' + n'' + s`, `s ∈ {0, 1}`, gives `q^{min(n', n'')}` if `s = 1` or `min(n', n'') = 0`, and
`(q - 1) q^{min(n', n'') - 1}` if `s = 0 < min(n', n'')`; `0` otherwise. -/
def cjNRam (q n₁ n₂ δ : ℕ) : ℕ :=
  if max n₁ n₂ - min n₁ n₂ ≤ δ ∧ (δ - (max n₁ n₂ - min n₁ n₂)) % 2 = 0 ∧
      (δ - (max n₁ n₂ - min n₁ n₂)) / 2 < min n₁ n₂ then
    (if δ = max n₁ n₂ - min n₁ n₂ then 1
      else (q - 1) * q ^ ((δ - (max n₁ n₂ - min n₁ n₂)) / 2 - 1))
  else if δ = n₁ + n₂ + 1 then q ^ min n₁ n₂
  else if δ = n₁ + n₂ then
    (if min n₁ n₂ = 0 then 1 else (q - 1) * q ^ (min n₁ n₂ - 1))
  else 0

/-- **Lemma 2.1 (p. 4), the split case** (`K_v ≅ F_v × F_v`): case (i) as above, and case (iv):
`δ = n' + n'' + s`, `s ∈ ℕ`, gives `1` if `min = 0 = s`, `2` if `min = 0 < s`,
`(q - 2) q^{min - 1}` if `min > 0 = s`, `2 (q - 1) q^{min - 1}` if `min, s > 0`; `0` otherwise. -/
def cjNSplit (q n₁ n₂ δ : ℕ) : ℕ :=
  if max n₁ n₂ - min n₁ n₂ ≤ δ ∧ (δ - (max n₁ n₂ - min n₁ n₂)) % 2 = 0 ∧
      (δ - (max n₁ n₂ - min n₁ n₂)) / 2 < min n₁ n₂ then
    (if δ = max n₁ n₂ - min n₁ n₂ then 1
      else (q - 1) * q ^ ((δ - (max n₁ n₂ - min n₁ n₂)) / 2 - 1))
  else if n₁ + n₂ ≤ δ then
    (if min n₁ n₂ = 0 then (if δ = n₁ + n₂ then 1 else 2)
      else if δ = n₁ + n₂ then (q - 2) * q ^ (min n₁ n₂ - 1)
      else 2 * (q - 1) * q ^ (min n₁ n₂ - 1))
  else 0

/-- **`N_v(n', n'', δ)` of Lemma 2.1 (p. 4)**, by the local type of `v` (`q = N(v)`). -/
def cjN : CJLocalType → ℕ → ℕ → ℕ → ℕ → ℕ
  | .inert => cjNUnram
  | .ramified => cjNRam
  | .split => cjNSplit

/-! ### The objects of §§3.1–3.4 and Theorem 3.1 -/

/-- **The objects of Cornut–Jetchev §§3.1–3.4 (interface).**
* `Pl`: the finite places of `F`; `S`, `RamB` (`Ram_f B`), `degF` (`[F : ℚ]`); `ty v` the local type
  of `v` in `K`, `q v = N(v)`, `vn v = v(𝔫)` (`𝔫` the level of the Eichler order `R`, §3.3);
* `Gal`: the group acting (`T(𝔸_f)` through `Art_K`, §3.2); `X = CM(G, H)`, `Y = CM(G_S, H_S)` with
  their Galois actions, and `θ = θ_S` (§3.2);
* `C = I(Ram_f B)²`, `CS = I(Ram_f B_S)²`; `val₁ c v`, `val₂ c v` the valuations `v(c')`, `v(c'')` of
  `c = (c', c'')`; `primeToS` the map `( )_S` of (12); `galIdx c = |Gal(K[c' ∩ c'']/K[c_S])|`;
* `cf = c_f`, `cSf = c_{S,f}` (§3.3, (10)); `Sg = (ℤ/2)^{|S'|}`, `ψ = ψ_{S'}` and `e = e_{S'}` defined by
  the right side of (14) (§3.4).
ABSTRACT: no field is constructed from `B`, `K` or `S` here. -/
structure CJSetting where
  /-- The finite places of `F`. -/
  Pl : Type
  [decEqPl : DecidableEq Pl]
  /-- The finite set of places `S`. -/
  S : Finset Pl
  /-- `Ram_f B`. -/
  RamB : Finset Pl
  /-- `[F : ℚ]`. -/
  degF : ℕ
  /-- The local type of `v` in `K`. -/
  ty : Pl → CJLocalType
  /-- `N(v)`, the order of the residue field of `F` at `v`. -/
  q : Pl → ℕ
  /-- `v(𝔫)`. -/
  vn : Pl → ℕ
  /-- The group acting on CM points (`T(𝔸_f)` through `Art_K`). -/
  Gal : Type
  [groupGal : Group Gal]
  /-- `CM(G, H)`. -/
  X : Type
  [actX : MulAction Gal X]
  /-- `CM(G_S, H_S)`. -/
  Y : Type
  [actY : MulAction Gal Y]
  /-- `θ_S`. -/
  θ : X → Y
  /-- `I(Ram_f B)²`. -/
  C : Type
  /-- `I(Ram_f B_S)²`. -/
  CS : Type
  /-- `v(c')`. -/
  val₁ : C → Pl → ℕ
  /-- `v(c'')`. -/
  val₂ : C → Pl → ℕ
  /-- `(c', c'') ↦ (c'_S, c''_S)`. -/
  primeToS : C → CS
  /-- `|Gal(K[c]/K[c_S])|`. -/
  galIdx : C → ℕ
  /-- The fine conductor `c_f`. -/
  cf : X → C
  /-- The fine conductor `c_{S,f}`. -/
  cSf : Y → CS
  /-- `(ℤ/2)^{|S'|}`. -/
  Sg : Type
  /-- The sign map `ψ_{S'}`. -/
  ψ : Y → Sg
  /-- `e_{S'}`, the right side of (14). -/
  e : C → Sg

attribute [instance] CJSetting.decEqPl CJSetting.groupGal CJSetting.actX CJSetting.actY

namespace CJSetting

variable (P : CJSetting)

/-- **H.1** (§3.1, p. 5): `B` is unramified at every `v ∈ S`. -/
def H1 : Prop := Disjoint P.RamB P.S

/-- **H.2** (§3.1, p. 5): `|S| + |Ram_f B| + [F : ℚ]` is even. -/
def H2 : Prop := Even (P.S.card + P.RamB.card + P.degF)

/-- **H.3** (§3.1, p. 5): every `v ∈ S` is inert or ramified in `K`. -/
def H3 : Prop := ∀ v ∈ P.S, P.ty v = .inert ∨ P.ty v = .ramified

/-- **The parity condition of §3.5** (p. 9): `v(c') − v(c'') ≡ v(𝔫) (mod 2)` at every `v ∈ S'`, the
places of `S` inert in `K` (written with a sum, which has the same parity). -/
def Parity (c : P.C) : Prop :=
  ∀ v ∈ P.S, P.ty v = .inert → Even (P.val₁ c v + P.val₂ c v + P.vn v)

/-- **The integer `κ` of §3.5** (p. 9):
`κ = |Gal(K[c]/K[c_S])| ∏_{v ∈ S} N_v(v(c'), v(c''), v(𝔫))`, `N_v` from Lemma 2.1 with `q = N(v)`. -/
def kappa (c : P.C) : ℕ :=
  P.galIdx c * ∏ v ∈ P.S, cjN (P.ty v) (P.q v) (P.val₁ c v) (P.val₂ c v) (P.vn v)

/-- **Cornut–Jetchev, Theorem 3.1 (PRINT; arXiv:1012.0725v1, §3.5, p. 9), general `κ`.** Under
H.1–H.3 (§3.1, p. 5): the map `θ_S` is `Gal_K^ab`-equivariant (§3.2, p. 6), and for every `c = (c', c'')`
with the parity condition, `θ_S` maps `c_f⁻¹(c)` into `c_{S,f}⁻¹(c_S) ∩ ψ_{S'}⁻¹(e_{S'}(c))` (the
square (12) and `φ_{S'} = ψ_{S'} ∘ θ_S` with (14)) and every point of that target has exactly `κ(c)`
preimages in `c_f⁻¹(c)`. The print: *"By restriction, the map `θ_S` induces a surjective `κ`-to-1
correspondence `θ_S : c_f⁻¹(c', c'') → c_{S,f}⁻¹(c'_S, c''_S) ∩ ψ_{S'}⁻¹(e_{S'}(c', c''))`."* Corollary 3.2
(p. 9) is the restriction to a fibre `π⁻¹(s)` of the target. DEPARTURE of form (module docstring): the
fibre-count reading of "surjective `κ`-to-1", and the equivariance of §3.2 as a clause. Used in the
manuscript at `κ = 1`: tex 2522–2533 ((3.8)) and App. F tex 9195–9272. -/
def Thm31 : Prop :=
  P.H1 → P.H2 → P.H3 →
    (∀ (g : P.Gal) (x : P.X), P.θ (g • x) = g • P.θ x) ∧
    ∀ c : P.C, P.Parity c →
      (∀ x : P.X, P.cf x = c → P.cSf (P.θ x) = P.primeToS c ∧ P.ψ (P.θ x) = P.e c) ∧
      ∀ y : P.Y, P.cSf y = P.primeToS c → P.ψ y = P.e c →
        ENat.card {x : P.X // P.cf x = c ∧ P.θ x = y} = (P.kappa c : ℕ∞)

variable {P}

/-- **PROVED.** The target of Theorem 3.1 at `c`: `c_{S,f}⁻¹(c_S) ∩ ψ_{S'}⁻¹(e_{S'}(c))`. -/
def Target (c : P.C) : Set P.Y := {y | P.cSf y = P.primeToS c ∧ P.ψ y = P.e c}

/-- **PROVED.** "Surjective" in Theorem 3.1 when `κ(c) ≥ 1`: every target point has a preimage. -/
theorem Thm31.exists_preimage (hP : P.Thm31) (h1 : P.H1) (h2 : P.H2) (h3 : P.H3) {c : P.C}
    (hc : P.Parity c) (hκ : 0 < P.kappa c) {y : P.Y} (hy : y ∈ Target c) :
    ∃ x : P.X, P.cf x = c ∧ P.θ x = y := by
  have hcard := ((hP h1 h2 h3).2 c hc).2 y hy.1 hy.2
  by_contra hne
  have hE : IsEmpty {x : P.X // P.cf x = c ∧ P.θ x = y} := ⟨fun x => hne ⟨x.1, x.2.1, x.2.2⟩⟩
  rw [(ENat.card_eq_zero_iff_empty _).mpr hE] at hcard
  have : (P.kappa c : ℕ∞) ≠ 0 := by exact_mod_cast hκ.ne'
  exact this hcard.symm

/-- **PROVED.** With `κ(c) = 1`, Theorem 3.1 says that `θ_S` restricts to a bijection
`c_f⁻¹(c) → c_{S,f}⁻¹(c_S) ∩ ψ_{S'}⁻¹(e_{S'}(c))` (one sign fibre, tex 9245–9263). -/
theorem Thm31.bijOn_of_kappa_eq_one (hP : P.Thm31) (h1 : P.H1) (h2 : P.H2) (h3 : P.H3) {c : P.C}
    (hc : P.Parity c) (hκ : P.kappa c = 1) :
    Set.BijOn P.θ {x | P.cf x = c} (Target c) := by
  obtain ⟨-, hmaps⟩ := hP h1 h2 h3
  obtain ⟨hinto, hfib⟩ := hmaps c hc
  refine ⟨fun x hx => hinto x hx, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ h
    have hcard := hfib (P.θ x₁) (hinto x₁ hx₁).1 (hinto x₁ hx₁).2
    rw [hκ, Nat.cast_one, ENat.card_eq_one_iff_unique] at hcard
    obtain ⟨u⟩ := hcard
    have hs : (⟨x₁, hx₁, rfl⟩ : {x : P.X // P.cf x = c ∧ P.θ x = P.θ x₁}) = ⟨x₂, hx₂, h.symm⟩ :=
      (u.uniq _).trans (u.uniq _).symm
    exact congrArg Subtype.val hs
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hP.exists_preimage h1 h2 h3 hc (by rw [hκ]; exact one_pos) hy
    exact ⟨x, hx, hxy⟩

/-- **PROVED.** The equivariance clause (§3.2, p. 6). -/
theorem Thm31.equivariant (hP : P.Thm31) (h1 : P.H1) (h2 : P.H2) (h3 : P.H3) (g : P.Gal)
    (x : P.X) : P.θ (g • x) = g • P.θ x :=
  (hP h1 h2 h3).1 g x

end CJSetting

/-! ### Non-vacuity: a satisfying instance and a refuting instance -/

/-- The translation action of `ℤ/2` (written multiplicatively) on itself, used by the toy instances. -/
abbrev cjToyAction : MulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul g x := Multiplicative.toAdd g + x
  one_smul x := zero_add x
  mul_smul _ _ _ := add_assoc _ _ _

/-- A toy setting of the manuscript's shape (`|S| + |Ram_f B| + [F : ℚ] = 1 + 0 + 1`, one inert place,
both conductors trivial, `κ = 1 · N(0, 0, 0) = 1`): two CM points permuted by `ℤ/2`, `θ = id`. -/
def cjToySetting : CJSetting where
  Pl := Unit
  S := {()}
  RamB := ∅
  degF := 1
  ty := fun _ => .inert
  q := fun _ => 3
  vn := fun _ => 0
  Gal := Multiplicative (ZMod 2)
  X := ZMod 2
  actX := cjToyAction
  Y := ZMod 2
  actY := cjToyAction
  θ := id
  C := Unit
  CS := Unit
  val₁ := fun _ _ => 0
  val₂ := fun _ _ => 0
  primeToS := id
  galIdx := fun _ => 1
  cf := fun _ => ()
  cSf := fun _ => ()
  Sg := Unit
  ψ := fun _ => ()
  e := fun _ => ()

/-- **Non-vacuity (satisfiable), PROVED.** The toy setting satisfies H.1–H.3 and Theorem 3.1. -/
theorem cjToySetting_thm31 :
    cjToySetting.H1 ∧ cjToySetting.H2 ∧ cjToySetting.H3 ∧ cjToySetting.Thm31 := by
  refine ⟨Finset.disjoint_empty_left _, ⟨1, by decide⟩,
    fun v _ => Or.inl rfl, fun _ _ _ => ⟨fun _ _ => rfl, fun c _ => ⟨fun _ _ => ⟨rfl, rfl⟩, ?_⟩⟩⟩
  intro y _ _
  have hk : cjToySetting.kappa c = 1 := by
    simp [CJSetting.kappa, cjToySetting, cjN, cjNUnram_zero]
  rw [hk, Nat.cast_one, ENat.card_eq_one_iff_unique]
  exact ⟨{ default := ⟨y, rfl, rfl⟩
           uniq := fun z => Subtype.ext z.2.2 }⟩

/-- A toy setting satisfying H.1–H.3 with `κ = 1` but a non-injective `θ` (two points onto one). -/
def cjCollapseSetting : CJSetting where
  Pl := Unit
  S := ∅
  RamB := ∅
  degF := 0
  ty := fun _ => .inert
  q := fun _ => 2
  vn := fun _ => 0
  Gal := Unit
  X := Bool
  Y := Unit
  θ := fun _ => ()
  C := Unit
  CS := Unit
  val₁ := fun _ _ => 0
  val₂ := fun _ _ => 0
  primeToS := id
  galIdx := fun _ => 1
  cf := fun _ => ()
  cSf := fun _ => ()
  Sg := Unit
  ψ := fun _ => ()
  e := fun _ => ()

/-- **Content (a refutation), PROVED.** H.1–H.3 hold for `cjCollapseSetting` but Theorem 3.1 fails
there: the fibre over the target point has two elements while `κ = 1`. -/
theorem not_thm31_cjCollapseSetting :
    cjCollapseSetting.H1 ∧ cjCollapseSetting.H2 ∧ cjCollapseSetting.H3 ∧
      ¬ cjCollapseSetting.Thm31 := by
  refine ⟨Finset.disjoint_empty_left _, ⟨0, rfl⟩,
    fun v hv => absurd hv (Finset.notMem_empty v), fun h => ?_⟩
  have h1 : cjCollapseSetting.H1 := Finset.disjoint_empty_left _
  have h3 : cjCollapseSetting.H3 := fun v hv => absurd hv (Finset.notMem_empty v)
  have hpar : cjCollapseSetting.Parity () := fun v hv => absurd hv (Finset.notMem_empty v)
  have hcard := ((h h1 ⟨0, rfl⟩ h3).2 () hpar).2 () rfl rfl
  have hk : cjCollapseSetting.kappa () = 1 := by simp [CJSetting.kappa, cjCollapseSetting]
  rw [hk, Nat.cast_one, ENat.card_eq_one_iff_unique] at hcard
  obtain ⟨u⟩ := hcard
  have hs : (⟨true, rfl, rfl⟩ : {x : cjCollapseSetting.X //
      cjCollapseSetting.cf x = () ∧ cjCollapseSetting.θ x = ()}) = ⟨false, rfl, rfl⟩ :=
    (u.uniq _).trans (u.uniq _).symm
  exact Bool.noConfusion (congrArg Subtype.val hs)

end ZInQ.Manuscript.RC.PrintsArith

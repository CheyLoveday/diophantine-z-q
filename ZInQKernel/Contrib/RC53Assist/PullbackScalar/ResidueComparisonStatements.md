# Exact theorem types and axiom reports

The following types are copied from the successful scratch compiler output for
`ResidueComparisonProof.lean`. They include every explicitly written theorem in the
proof port, its private helpers, and the two exact-interface checks. No source-level
assumption is suppressed. All 445 reports contain exactly
`[propext, Classical.choice, Quot.sound]`.

Private declaration names below are compiler-generated mathematical declaration names.
The proof-source prefix of the audit was byte-identical to the final source, SHA256
`03374bdaac5d9deac7b4751c35b57ec8b8fa9ecd30fc36c598a0c8e90ae1a574`.

## 1. `TauCeti.sum_fin_product_eq_sum_antidiagonal`

```lean
TauCeti.sum_fin_product_eq_sum_antidiagonal.{u_1} {M : Type u_1} [AddCommMonoid M] {n d : ℕ} (hd : d < n)
  (f : Fin n × Fin n → M) (g : ℕ × ℕ → M) (hfg : ∀ (l : Fin n × Fin n), ↑l.1 + ↑l.2 = d → f l = g (↑l.1, ↑l.2)) :
  ∑ l with ↑l.1 + ↑l.2 = d, f l = ∑ l ∈ Finset.HasAntidiagonal.antidiagonal d, g l
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 2. `TauCeti.prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag`

```lean
TauCeti.prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag.{u_1, u_2} {ι : Type u_1} {M : Type u_2} [PartialOrder ι]
  [Fintype ι] [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) :
  ∏ i, ∏ j ≥ i, f i j = (∏ i, ∏ j > i, f i j) * ∏ i, f i i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 3. `TauCeti.prod_prod_Ioi_eq_of_two`

```lean
TauCeti.prod_prod_Ioi_eq_of_two.{u_1} {M : Type u_1} [CommMonoid M] {m : ℕ} (f : Fin (m + 2) → Fin (m + 2) → M) :
  ∏ i, ∏ j > i, f i j =
    f 0 1 * ((∏ k, f 0 k.succ.succ) * ∏ k, f 1 k.succ.succ) * ∏ i, ∏ j > i, f i.succ.succ j.succ.succ
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 4. `TauCeti.prod_prod_Ioi_three`

```lean
TauCeti.prod_prod_Ioi_three.{u_1} {M : Type u_1} [CommMonoid M] (f : Fin 3 → Fin 3 → M) :
  ∏ i, ∏ j > i, f i j = f 0 1 * f 0 2 * f 1 2
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 5. `TauCeti.prod_prod_Ioi_four`

```lean
TauCeti.prod_prod_Ioi_four.{u_1} {M : Type u_1} [CommMonoid M] (f : Fin 4 → Fin 4 → M) :
  ∏ i, ∏ j > i, f i j = f 0 1 * f 0 2 * f 0 3 * f 1 2 * f 1 3 * f 2 3
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 6. `TauCeti.prod_prod_Ioi_snoc`

```lean
TauCeti.prod_prod_Ioi_snoc.{u_1, u_2} {A : Type u_1} {M : Type u_2} [CommMonoid M] {n : ℕ} (f : A → A → M)
  (w : Fin n → A) (a : A) :
  ∏ i, ∏ j > i, f (Fin.snoc w a i) (Fin.snoc w a j) = (∏ i, ∏ j > i, f (w i) (w j)) * ∏ i, f (w i) a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 7. `TauCeti.prod_prod_Ioi_append`

```lean
TauCeti.prod_prod_Ioi_append.{u_1, u_2} {A : Type u_1} {M : Type u_2} [CommMonoid M] {n m : ℕ} (f : A → A → M)
  (w : Fin n → A) (v : Fin m → A) :
  ∏ i, ∏ j > i, f (Fin.append w v i) (Fin.append w v j) =
    ((∏ i, ∏ j > i, f (w i) (w j)) * ∏ i, ∏ j > i, f (v i) (v j)) * ∏ i, ∏ j, f (w i) (v j)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 8. `TauCeti.prod_prod_Ioi_append_of_mul`

```lean
TauCeti.prod_prod_Ioi_append_of_mul.{u_1, u_2} {A : Type u_1} {M : Type u_2} [CommMonoid A] [CommMonoid M]
  (F : A → A → M) (hone_left : ∀ (b : A), F 1 b = 1) (hone_right : ∀ (a : A), F a 1 = 1)
  (hmul_left : ∀ (a b c : A), F (a * b) c = F a c * F b c) (hmul_right : ∀ (a b c : A), F a (b * c) = F a b * F a c)
  {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
  ∏ i, ∏ j > i, F (Fin.append p q i) (Fin.append p q j) =
    ((∏ i, ∏ j > i, F (p i) (p j)) * ∏ i, ∏ j > i, F (q i) (q j)) * F (∏ i, p i) (∏ j, q j)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 9. `TauCeti.sum_sum_Ioi_append_of_mul`

```lean
TauCeti.sum_sum_Ioi_append_of_mul.{u_1, u_2} {A : Type u_1} {M : Type u_2} [CommMonoid A] [AddCommMonoid M]
  (F : A → A → M) (hone_left : ∀ (b : A), F 1 b = 0) (hone_right : ∀ (a : A), F a 1 = 0)
  (hmul_left : ∀ (a b c : A), F (a * b) c = F a c + F b c) (hmul_right : ∀ (a b c : A), F a (b * c) = F a b + F a c)
  {m n : ℕ} (p : Fin m → A) (q : Fin n → A) :
  ∑ i, ∑ j > i, F (Fin.append p q i) (Fin.append p q j) =
    ∑ i, ∑ j > i, F (p i) (p j) + ∑ i, ∑ j > i, F (q i) (q j) + F (∏ i, p i) (∏ j, q j)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 10. `TauCeti.prod_prod_Ioi_scale`

```lean
TauCeti.prod_prod_Ioi_scale.{u_1, u_2} {A : Type u_1} {M : Type u_2} [CommMonoid A] [CommMonoid M] (F : A → A → M)
  {s : A} (hmul_right : ∀ (a b c : A), F a (b * c) = F a b * F a c) (hcomm : ∀ (a b : A), F a b = F b a) (a : A)
  (hself : F a a = F a s) {n : ℕ} (w : Fin n → A) :
  ∏ i, ∏ j > i, F (a * w i) (a * w j) = (∏ i, ∏ j > i, F (w i) (w j)) * F a s ^ n.choose 2 * F a (∏ i, w i) ^ (n - 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 11. `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`

```lean
TauCeti.sum_univ_prod_eq_sum_lt_add_swap.{u_1, u_2} {l : Type u_1} [Fintype l] [LinearOrder l] {M : Type u_2}
  [AddCommMonoid M] (F : l × l → M) (hdiag : ∀ (a : l), F (a, a) = 0) :
  ∑ ij, F ij = ∑ ij with ij.1 < ij.2, (F ij + F ij.swap)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 12. `TauCeti.prod_prod_Ioi_comp_perm`

```lean
TauCeti.prod_prod_Ioi_comp_perm.{u_1, u_2} {ι : Type u_1} {M : Type u_2} [LinearOrder ι] [Fintype ι]
  [LocallyFiniteOrderTop ι] [CommMonoid M] (f : ι → ι → M) (σ : Equiv.Perm ι) (hf : ∀ (i j : ι), f i j = f j i) :
  ∏ i, ∏ j > i, f (σ i) (σ j) = ∏ i, ∏ j > i, f i j
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 13. `TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty`

```lean
TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty.{u_2} (k : Type u_2) [Field k] :
  (TauCeti.Place.orderSystem ⋯).divisorClass
      (-2 • TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (TauCeti.Place.infty k)) =
    TauCeti.canonicalClass ⋯ ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 14. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.exists_isGreatest_ratFuncWeilDifferential`

```lean
TauCeti.exists_isGreatest_ratFuncWeilDifferential.{u_2} (k : Type u_2) [Field k] :
  ∃ ω ∈ TauCeti.weilDifferentialSpace k (RatFunc k),
    IsGreatest {D | ω ∈ TauCeti.weilDifferentialFiltration D}
        (-2 • TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (TauCeti.Place.infty k)) ∧
      (TauCeti.repartitionDualComponent ω (TauCeti.Place.infty k)) RatFunc.X⁻¹ = -1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 15. `TauCeti.ratFuncWeilDifferential_mem`

```lean
TauCeti.ratFuncWeilDifferential_mem.{u_2} (k : Type u_2) [Field k] :
  TauCeti.ratFuncWeilDifferential k ∈ TauCeti.weilDifferentialSpace k (RatFunc k)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 16. `TauCeti.isGreatest_ratFuncWeilDifferential`

```lean
TauCeti.isGreatest_ratFuncWeilDifferential.{u_2} (k : Type u_2) [Field k] :
  IsGreatest {D | TauCeti.ratFuncWeilDifferential k ∈ TauCeti.weilDifferentialFiltration D}
    (-2 • TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (TauCeti.Place.infty k))
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 17. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_inv_X`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_inv_X.{u_2} (k : Type u_2) [Field k] :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.infty k)) RatFunc.X⁻¹ = -1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 18. `TauCeti.ratFuncWeilDifferential_ne_zero`

```lean
TauCeti.ratFuncWeilDifferential_ne_zero.{u_2} (k : Type u_2) [Field k] : TauCeti.ratFuncWeilDifferential k ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 19. `TauCeti.weilDifferentialDivisor_ratFuncWeilDifferential`

```lean
TauCeti.weilDifferentialDivisor_ratFuncWeilDifferential.{u_2} (k : Type u_2) [Field k] :
  TauCeti.weilDifferentialDivisor ⋯ ⋯ ⋯ ⋯ = -2 • TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (TauCeti.Place.infty k)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 20. `TauCeti.eq_ratFuncWeilDifferential`

```lean
TauCeti.eq_ratFuncWeilDifferential.{u_1} {k : Type u_1} [Field k]
  {ω : Module.Dual k ↥(TauCeti.repartitionSpace k (RatFunc k))} (hmem : ω ∈ TauCeti.weilDifferentialSpace k (RatFunc k))
  (hgreat :
    IsGreatest {D | ω ∈ TauCeti.weilDifferentialFiltration D}
      (-2 • TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (TauCeti.Place.infty k)))
  (hnorm : (TauCeti.repartitionDualComponent ω (TauCeti.Place.infty k)) RatFunc.X⁻¹ = -1) :
  ω = TauCeti.ratFuncWeilDifferential k
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 21. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty.{u_1} {k : Type u_1} [Field k]
  {P : TauCeti.Place k (RatFunc k)} (hP : P ≠ TauCeti.Place.infty k) {z : RatFunc k} (hz : z ∈ P.integers) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) P) z = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 22. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_algebraMap`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_algebraMap.{u_1} {k : Type u_1} [Field k] (p : Polynomial k) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.infty k))
      ((algebraMap (Polynomial k) (RatFunc k)) p) =
    0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 23. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_zpow`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_zpow.{u_2} (k : Type u_2) [Field k] (n : ℤ) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.infty k)) (RatFunc.X ^ n) =
    if n = -1 then -1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 24. `TauCeti.weilDifferentialOfSeparating_def`

```lean
TauCeti.weilDifferentialOfSeparating_def.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] {x : F}
  (hF : TauCeti.IsFunctionField k F) (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  have x_1 := ⋯;
  have x_2 := ⋯;
  have x_3 := ⋯;
  TauCeti.weilDifferentialOfSeparating hF hx =
    (TauCeti.weilDifferentialCotrace k F ⋯ hF) ⟨TauCeti.ratFuncWeilDifferential k, ⋯⟩
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 25. `TauCeti.weilDifferentialOfSeparating_ne_zero`

```lean
TauCeti.weilDifferentialOfSeparating_ne_zero.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] {x : F}
  (hF : TauCeti.IsFunctionField k F) (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  TauCeti.weilDifferentialOfSeparating hF hx ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 26. `TauCeti.coe_weilDifferentialOfSeparating_ne_zero`

```lean
TauCeti.coe_weilDifferentialOfSeparating_ne_zero.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {x : F} (hF : TauCeti.IsFunctionField k F) (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  ↑(TauCeti.weilDifferentialOfSeparating hF hx) ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 27. `TauCeti.weilDifferentialBasisOfSeparating_apply`

```lean
TauCeti.weilDifferentialBasisOfSeparating_apply.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {x : F} (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] (i : Unit) :
  (TauCeti.weilDifferentialBasisOfSeparating hF hex hx) i = TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 28. `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self`

```lean
TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] {x : F} (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] :
  (TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ((KaehlerDifferential.D k F) x) =
    TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 29. `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_symm_weilDifferentialOfSeparating`

```lean
TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_symm_weilDifferentialOfSeparating.{u, v} {k : Type u}
  {F : Type v} [Field k] [Field F] [Algebra k F] {x : F} (hF : TauCeti.IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  (TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm
      (TauCeti.weilDifferentialOfSeparating hF hx) =
    (KaehlerDifferential.D k F) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 30. `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D`

```lean
TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] {x : F} (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] (y : F) :
  (TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ((KaehlerDifferential.D k F) y) =
    (TauCeti.derivativeOfSeparating hx) y • TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 31. `TauCeti.coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating`

```lean
TauCeti.coord_kaehlerDifferentialEquivWeilDifferentialOfSeparating.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] {x : F} (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] (ω : Ω[F⁄k]) :
  ((TauCeti.weilDifferentialBasisOfSeparating hF hex hx).coord ())
      ((TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ω) =
    ((TauCeti.kaehlerBasisOfSeparating hx).coord ()) ω
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 32. `TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero`

```lean
TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [Algebra.IsSeparable (RatFunc k) F] (hF : TauCeti.IsFunctionField k F) :
  ↑((TauCeti.weilDifferentialCotrace k F ⋯ hF) ⟨TauCeti.ratFuncWeilDifferential k, ⋯⟩) ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 33. `TauCeti.weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential`

```lean
TauCeti.weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential.{u, v} {k : Type u} {F : Type v}
  [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F] (hF : TauCeti.IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F) :
  TauCeti.weilDifferentialDivisor hF hex ⋯ ⋯ =
    -2 • TauCeti.Divisor.poles hF ((Units.map ↑(algebraMap (RatFunc k) F)) (Units.mk0 RatFunc.X ⋯)) +
      TauCeti.Divisor.different k F ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 34. `TauCeti.divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass`

```lean
TauCeti.divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass.{u, v} {k : Type u} {F : Type v} [Field k]
  [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  [Algebra.IsSeparable (RatFunc k) F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
  -(2 •
          (TauCeti.Place.orderSystem hF).divisorClass
            (TauCeti.Divisor.poles hF ((Units.map ↑(algebraMap (RatFunc k) F)) (Units.mk0 RatFunc.X ⋯)))) +
      (TauCeti.Place.orderSystem hF).divisorClass (TauCeti.Divisor.different k F ⋯) =
    TauCeti.canonicalClass hF hex
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 35. `TauCeti.weilDifferentialDivisor_weilDifferentialOfSeparating`

```lean
TauCeti.weilDifferentialDivisor_weilDifferentialOfSeparating.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] {x : F} (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] :
  TauCeti.weilDifferentialDivisor hF hex ⋯ ⋯ =
    -2 • TauCeti.Divisor.poles hF (Units.mk0 x ⋯) + TauCeti.Divisor.different k F ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 36. `TauCeti.weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero`

```lean
TauCeti.weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {t : F} (ht : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] {P : TauCeti.Place k F} [Algebra.IsSeparable k P.ResidueField] (htP : P.ord t = 1) :
  TauCeti.weilDifferentialOrder hF hex ⋯ ⋯ P = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 37. `TauCeti.residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly`

```lean
TauCeti.residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly.{u_1, u_2, u_3, u_4} (A : Type u_1)
  (K : Type u_2) (L : Type u_3) (B : Type u_4) [CommRing A] [Field K] [Field L] [CommRing B] [Algebra A K] [Algebra B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A]
  [IsFractionRing A K] [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : B) (hx : A[x] = ⊤) :
  differentIdeal A B = Ideal.span {(Polynomial.aeval x) (Polynomial.derivative (minpoly A x))}
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 38. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.exists_smul_mem_traceDual_of_mem_traceDual`

```lean
TauCeti.exists_smul_mem_traceDual_of_mem_traceDual.{uR, uRm, uS, uSm, uK, uL} {R : Type uR} {Rₘ : Type uRm}
  {S : Type uS} {Sₘ : Type uSm} {K : Type uK} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ]
  [Field K] [Field L] {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R K]
  [Algebra Rₘ K] [IsScalarTower R Rₘ K] [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L] [Algebra Sₘ L]
  [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L]
  [IsLocalization M Rₘ] [Module.Finite R S] {x : L} (hx : x ∈ Submodule.traceDual Rₘ K 1) :
  ∃ b, (algebraMap R K) ↑b • x ∈ Submodule.traceDual R K 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 39. `TauCeti.span_traceDual_one_eq_traceDual_one`

```lean
TauCeti.span_traceDual_one_eq_traceDual_one.{uR, uRm, uS, uSm, uK, uL} {R : Type uR} {Rₘ : Type uRm} {S : Type uS}
  {Sₘ : Type uSm} {K : Type uK} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
  {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R S Sₘ]
  [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K] [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L]
  [Algebra Sₘ L] [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L]
  [IsScalarTower S Sₘ L] [IsScalarTower R Sₘ L] [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [Module.Finite R S] :
  Submodule.span Sₘ ↑(Submodule.traceDual R K 1) = Submodule.traceDual Rₘ K 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 40. `TauCeti.extended_dual_one_eq_dual_one`

```lean
TauCeti.extended_dual_one_eq_dual_one.{uR, uRm, uS, uSm, uK, uL} {R : Type uR} {Rₘ : Type uRm} {S : Type uS}
  {Sₘ : Type uSm} {K : Type uK} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
  {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R S Sₘ]
  [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K] [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L]
  [Algebra Sₘ L] [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L]
  [IsScalarTower S Sₘ L] [IsScalarTower R Sₘ L] [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [Module.Finite R S] [IsDomain R] [IsFractionRing R K]
  [IsFractionRing S L] [IsIntegrallyClosed R] [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDomain S] :
  have x := ⋯;
  have hM := ⋯;
  have x := ⋯;
  have hMS := ⋯;
  have x_1 := ⋯;
  have x_2 := ⋯;
  have x_3 := ⋯;
  have x_4 := ⋯;
  FractionalIdeal.extended L ⋯ (FractionalIdeal.dual R K 1) = FractionalIdeal.dual Rₘ K 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 41. `TauCeti.map_differentIdeal_eq_differentIdeal`

```lean
TauCeti.map_differentIdeal_eq_differentIdeal.{uR, uRm, uS, uSm, uK, uL} {R : Type uR} {Rₘ : Type uRm} {S : Type uS}
  {Sₘ : Type uSm} {K : Type uK} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
  {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R S Sₘ]
  [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K] [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L]
  [Algebra Sₘ L] [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L]
  [IsScalarTower S Sₘ L] [IsScalarTower R Sₘ L] [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [Module.Finite R S] [IsDomain R] [IsFractionRing R K]
  [IsFractionRing S L] [IsIntegrallyClosed R] [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDedekindDomain S] :
  have x := ⋯;
  have hM := ⋯;
  have x_1 := ⋯;
  have hMS := ⋯;
  have x_2 := ⋯;
  have x_3 := ⋯;
  have x_4 := ⋯;
  have x_5 := ⋯;
  have x_6 := ⋯;
  have x_7 := ⋯;
  have x := ⋯;
  have x_8 := ⋯;
  have x := ⋯;
  Ideal.map (algebraMap S Sₘ) (differentIdeal R S) = differentIdeal Rₘ Sₘ
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 42. `TauCeti.multiplicity_differentIdeal_eq_multiplicity_under`

```lean
TauCeti.multiplicity_differentIdeal_eq_multiplicity_under.{uR, uRm, uS, uSm, uK, uL} {R : Type uR} {Rₘ : Type uRm}
  {S : Type uS} {Sₘ : Type uSm} {K : Type uK} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ]
  [Field K] [Field L] {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ]
  [IsScalarTower R S Sₘ] [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K] [Algebra K L] [Algebra R L] [Algebra Rₘ L]
  [Algebra S L] [Algebra Sₘ L] [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L]
  [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L] [IsScalarTower R Sₘ L] [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [Module.Finite R S] [IsDomain R] [IsFractionRing R K]
  [IsFractionRing S L] [IsIntegrallyClosed R] [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree R S] [Module.IsTorsionFree Rₘ Sₘ]
  [IsDedekindDomain S] [IsDomain Rₘ] [IsDedekindDomain Sₘ] {P : Ideal Sₘ} [P.IsPrime] (hP : P ≠ ⊥) :
  multiplicity P (differentIdeal Rₘ Sₘ) = multiplicity (Ideal.under S P) (differentIdeal R S)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 43. `TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure`

```lean
TauCeti.isLocalization_algebraMapSubmonoid_of_isIntegralClosure.{uR, uRm, uS, uSm, uL} {R : Type uR} {Rₘ : Type uRm}
  {S : Type uS} {Sₘ : Type uSm} {L : Type uL} [CommRing R] [CommRing Rₘ] [CommSemiring S] [CommSemiring Sₘ] [CommRing L]
  {M : Submonoid R} [Algebra R Rₘ] [Algebra R S] [Algebra R L] [Algebra Rₘ L] [Algebra S Sₘ] [Algebra S L]
  [Algebra Sₘ L] [IsScalarTower R Rₘ L] [IsScalarTower R S L] [IsScalarTower S Sₘ L] [IsIntegralClosure S R L]
  [IsIntegralClosure Sₘ Rₘ L] [IsLocalization M Rₘ] : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 44. `TauCeti.Place.differentExponent_eq_multiplicity_center`

```lean
TauCeti.Place.differentExponent_eq_multiplicity_center.{u, u', v, v', u_1, u_2} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra k F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  {B : Type u_1} {C : Type u_2} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F] [CommRing C]
  [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F'] [Algebra B C] [Algebra B F'] [IsScalarTower B C F']
  [IsScalarTower B F F'] [IsIntegralClosure C B F'] [Module.IsTorsionFree B C] (P' : TauCeti.Place k' F')
  (hC : ∀ (c : C), (algebraMap C F') c ∈ P'.integers) :
  TauCeti.Place.differentExponent k F P' = multiplicity (P'.center hC).asIdeal (differentIdeal B C)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 45. `TauCeti.Place.differentExponent_le_ord_aeval_derivative`

```lean
TauCeti.Place.differentExponent_le_ord_aeval_derivative.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v)
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  {P' : TauCeti.Place k' F'} {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : Polynomial F} (hψ : ψ.Monic)
  (hcoeff : ∀ (i : ℕ), ψ.coeff i ∈ (TauCeti.Place.restrict k F P').integers) (hy : (Polynomial.aeval y) ψ = 0)
  (hψ' : (Polynomial.aeval y) (Polynomial.derivative ψ) ≠ 0) :
  ↑(TauCeti.Place.differentExponent k F P') ≤ P'.ord ((Polynomial.aeval y) (Polynomial.derivative ψ))
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 46. `TauCeti.Place.differentExponent_le_ord_two_mul_add`

```lean
TauCeti.Place.differentExponent_le_ord_two_mul_add.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v)
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  {P' : TauCeti.Place k' F'} {u v : F} (hu : (algebraMap F F') u ∈ P'.integers) (hv : (algebraMap F F') v ∈ P'.integers)
  {z : F'} (hgen : F⟮z⟯ = ⊤) (hz : z ^ 2 + (algebraMap F F') u * z - (algebraMap F F') v = 0)
  (hne : 2 * z + (algebraMap F F') u ≠ 0) :
  ↑(TauCeti.Place.differentExponent k F P') ≤ P'.ord (2 * z + (algebraMap F F') u)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 47. `TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly`

```lean
TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v)
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  {P' : TauCeti.Place k' F'} {x : ↥(integralClosure (↥(TauCeti.Place.restrict k F P').integers) F')}
  (hx : (↥(TauCeti.Place.restrict k F P').integers)[x] = ⊤) :
  ↑(TauCeti.Place.differentExponent k F P') =
    P'.ord
      ((Polynomial.aeval ((algebraMap (↥(integralClosure (↥(TauCeti.Place.restrict k F P').integers) F')) F') x))
        (Polynomial.derivative
          (minpoly F ((algebraMap (↥(integralClosure (↥(TauCeti.Place.restrict k F P').integers) F')) F') x))))
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 48. `TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly_of_isIntegralClosure`

```lean
TauCeti.Place.differentExponent_eq_ord_aeval_derivative_minpoly_of_isIntegralClosure.{u, u', v, v', u_1, u_2}
  (k : Type u) {k' : Type u'} (F : Type v) {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k']
  [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {B : Type u_1} {C : Type u_2} [CommRing B] [IsDedekindDomain B]
  [Algebra B F] [IsFractionRing B F] [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F'] [IsScalarTower B C F']
  [IsScalarTower B F F'] [IsIntegralClosure C B F'] (P' : TauCeti.Place k' F')
  (hC : ∀ (c : C), (algebraMap C F') c ∈ P'.integers) {y : C} (hy : B[y] = ⊤) :
  ↑(TauCeti.Place.differentExponent k F P') =
    P'.ord ((Polynomial.aeval ((algebraMap C F') y)) (Polynomial.derivative (minpoly F ((algebraMap C F') y))))
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 49. `TauCeti.Place.differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one`

```lean
TauCeti.Place.differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one.{u, u', v, v'} (k : Type u) {k' : Type u'}
  (F : Type v) {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F']
  [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] {P' : TauCeti.Place k' F'} {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : Polynomial F} (hψ : ψ.Monic)
  (hcoeff : ∀ (i : ℕ), ψ.coeff i ∈ (TauCeti.Place.restrict k F P').integers) (hy : (Polynomial.aeval y) ψ = 0)
  (hψ' : P'.valuation ((Polynomial.aeval y) (Polynomial.derivative ψ)) = 1) : TauCeti.Place.differentExponent k F P' = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 50. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.WeierstrassCurve.Affine.isScalarTower_polynomial_ratFunc`

```lean
WeierstrassCurve.Affine.isScalarTower_polynomial_ratFunc.{u_1} {F : Type u_1} [Field F]
  (W : WeierstrassCurve.Affine F) : IsScalarTower (Polynomial F) (RatFunc F) W.FunctionField
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 51. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.WeierstrassCurve.Affine.genericY_sq_add_eq`

```lean
WeierstrassCurve.Affine.genericY_sq_add_eq.{u_1} {F : Type u_1} [Field F] (W : WeierstrassCurve.Affine F) :
  W.genericY ^ 2 + (algebraMap F W.FunctionField) W.a₁ * W.genericX * W.genericY +
      (algebraMap F W.FunctionField) W.a₃ * W.genericY =
    W.genericX ^ 3 + (algebraMap F W.FunctionField) W.a₂ * W.genericX ^ 2 +
        (algebraMap F W.FunctionField) W.a₄ * W.genericX +
      (algebraMap F W.FunctionField) W.a₆
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 52. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.WeierstrassCurve.Affine.differentExponent_le`

```lean
WeierstrassCurve.Affine.differentExponent_le.{u_1} {F : Type u_1} [Field F] (W : WeierstrassCurve.Affine F)
  [WeierstrassCurve.IsElliptic W] (P : TauCeti.Place F W.FunctionField) :
  ↑(TauCeti.Place.differentExponent F (RatFunc F) P) ≤
    P.ord W.invariantDifferentialDenom + 2 * max (-P.ord W.genericX) 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 53. `WeierstrassCurve.Affine.kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential`

```lean
WeierstrassCurve.Affine.kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential.{u_1} {F : Type u_1}
  [Field F] (W : WeierstrassCurve.Affine F) [WeierstrassCurve.IsElliptic W] :
  (TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating ⋯ ⋯ ⋯) W.invariantDifferential =
    W.invariantDifferentialDenom⁻¹ • TauCeti.weilDifferentialOfSeparating ⋯ ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 54. `WeierstrassCurve.Affine.kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero`

```lean
WeierstrassCurve.Affine.kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero.{u_1}
  {F : Type u_1} [Field F] (W : WeierstrassCurve.Affine F) [WeierstrassCurve.IsElliptic W] :
  ↑((TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating ⋯ ⋯ ⋯) W.invariantDifferential) ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 55. `WeierstrassCurve.Affine.weilDifferentialDivisor_invariantDifferential`

```lean
WeierstrassCurve.Affine.weilDifferentialDivisor_invariantDifferential.{u_1} {F : Type u_1} [Field F]
  (W : WeierstrassCurve.Affine F) [WeierstrassCurve.IsElliptic W] : TauCeti.weilDifferentialDivisor ⋯ ⋯ ⋯ ⋯ = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 56. `TauCeti.frobeniusPowers_toSubfield`

```lean
TauCeti.frobeniusPowers_toSubfield.{u_1, u_2} (k : Type u_1) (F : Type u_2) [Field k] [Field F] [Algebra k F] (p : ℕ)
  [ExpChar k p] [PerfectRing k p] (n : ℕ) :
  (TauCeti.frobeniusPowers k F p n).toSubfield = (iterateFrobenius F p n).fieldRange
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 57. `TauCeti.mem_frobeniusPowers`

```lean
TauCeti.mem_frobeniusPowers.{u_1, u_2} (k : Type u_1) (F : Type u_2) [Field k] [Field F] [Algebra k F] (p : ℕ)
  [ExpChar k p] [PerfectRing k p] (n : ℕ) (z : F) : z ∈ TauCeti.frobeniusPowers k F p n ↔ ∃ x, x ^ p ^ n = z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 58. `TauCeti.coe_iterateFrobeniusEquivPowers`

```lean
TauCeti.coe_iterateFrobeniusEquivPowers.{u_1, u_2} (k : Type u_1) (F : Type u_2) [Field k] [Field F] [Algebra k F]
  (p : ℕ) [ExpChar k p] [PerfectRing k p] (n : ℕ) (x : F) :
  ↑((TauCeti.iterateFrobeniusEquivPowers k F p n) x) = x ^ p ^ n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 59. `TauCeti.iterateFrobeniusEquivPowers_algebraMap`

```lean
TauCeti.iterateFrobeniusEquivPowers_algebraMap.{u_1, u_2} (k : Type u_1) (F : Type u_2) [Field k] [Field F]
  [Algebra k F] (p : ℕ) [ExpChar k p] [PerfectRing k p] (n : ℕ) (c : k) :
  (TauCeti.iterateFrobeniusEquivPowers k F p n) ((algebraMap k F) c) =
    (algebraMap k ↥(TauCeti.frobeniusPowers k F p n)) ((iterateFrobeniusEquiv k p n) c)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 60. `TauCeti.finiteDimensional_of_constantCompositum_eq_top`

```lean
TauCeti.finiteDimensional_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) : FiniteDimensional F F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 61. `TauCeti.finiteDimensional_base_of_constantCompositum_eq_top`

```lean
TauCeti.finiteDimensional_base_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : TauCeti.constantCompositum F k' F' = ⊤) : FiniteDimensional k k'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 62. `TauCeti.isSeparable_of_constantCompositum_eq_top`

```lean
TauCeti.isSeparable_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hcomp : TauCeti.constantCompositum F k' F' = ⊤) : Algebra.IsSeparable F F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 63. `TauCeti.isPurelyInseparable_of_constantCompositum_eq_top`

```lean
TauCeti.isPurelyInseparable_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [IsPurelyInseparable k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) : IsPurelyInseparable F F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 64. `TauCeti.separableClosure_eq_bot_of_constantCompositum_eq_top`

```lean
TauCeti.separableClosure_eq_bot_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : TauCeti.constantCompositum F k' F' = ⊤) : separableClosure k' F' = ⊥
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 65. `TauCeti.adjoin_image_eq_top_of_constantCompositum_eq_top`

```lean
TauCeti.adjoin_image_eq_top_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] {S : Set F} (hS : IntermediateField.adjoin k S = ⊤)
  (h : TauCeti.constantCompositum F k' F' = ⊤) : IntermediateField.adjoin k' (⇑(algebraMap F F') '' S) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 66. `TauCeti.isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top`

```lean
TauCeti.isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  (h : TauCeti.constantCompositum F k' F' = ⊤) {x : F} [Algebra.IsSeparable (↥k⟮x⟯) F] :
  Algebra.IsSeparable (↥k'⟮(algebraMap F F') x⟯) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 67. `TauCeti.exists_finiteDimensional_lt_card_constantCompositum_eq_top`

```lean
TauCeti.exists_finiteDimensional_lt_card_constantCompositum_eq_top.{u, v} (k : Type u) (F : Type v) [Field k] [Field F]
  [Algebra k F] (n : ℕ) :
  ∃ F' k', FiniteDimensional k ↥k' ∧ ↑n < ENat.card ↥k' ∧ TauCeti.constantCompositum F ↥k' ↥F' = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 68. `TauCeti.exists_finiteDimensional_normal_splits_constantCompositum_eq_top`

```lean
TauCeti.exists_finiteDimensional_normal_splits_constantCompositum_eq_top.{u, v} {k : Type u} (F : Type v) [Field k]
  [Field F] [Algebra k F] (f : Polynomial k) :
  ∃ F' k',
    FiniteDimensional k ↥k' ∧
      Normal k ↥k' ∧
        (Polynomial.map (algebraMap k ↥k') f).Splits ∧
          Polynomial.IsSplittingField k (↥k') f ∧ TauCeti.constantCompositum F ↥k' ↥F' = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 69. `TauCeti.isAlgebraic_constantCompositum`

```lean
TauCeti.isAlgebraic_constantCompositum.{u, u', v, v'} {k : Type u} {F : Type v} {F' : Type v'} [Field k] [Field F]
  [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] {k' : Type u'} [CommRing k']
  [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k'] :
  Algebra.IsAlgebraic F ↥(TauCeti.constantCompositum F k' F')
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 70. `TauCeti.isAlgebraic_of_constantCompositum_eq_top`

```lean
TauCeti.isAlgebraic_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {F : Type v} {F' : Type v'} [Field k]
  [Field F] [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] {k' : Type u'} [CommRing k']
  [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) : Algebra.IsAlgebraic F F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 71. `TauCeti.essFiniteType_of_constantCompositum_eq_top`

```lean
TauCeti.essFiniteType_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.EssFiniteType k F]
  (h : TauCeti.constantCompositum F k' F' = ⊤) : Algebra.EssFiniteType k' F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 72. `TauCeti.IsFunctionField.of_constantCompositum_eq_top`

```lean
TauCeti.IsFunctionField.of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsAlgebraic k k']
  (hF : TauCeti.IsFunctionField k F) (h : TauCeti.constantCompositum F k' F' = ⊤) : TauCeti.IsFunctionField k' F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 73. `TauCeti.adjoin_range_algebraMap_of_constantCompositum_eq_top`

```lean
TauCeti.adjoin_range_algebraMap_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) : Algebra.adjoin F (Set.range ⇑(algebraMap k' F')) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 74. `TauCeti.span_range_algebraMap_comp_of_constantCompositum_eq_top`

```lean
TauCeti.span_range_algebraMap_comp_of_constantCompositum_eq_top.{u, u', v, v', u_1} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) {ι : Type u_1} (b : Module.Basis ι k k') :
  Submodule.span F (Set.range (⇑(algebraMap k' F') ∘ ⇑b)) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 75. `TauCeti.finrank_le_finrank_of_constantCompositum_eq_top`

```lean
TauCeti.finrank_le_finrank_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  (h : TauCeti.constantCompositum F k' F' = ⊤) : Module.finrank F F' ≤ Module.finrank k k'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 76. `TauCeti.linearDisjoint_fieldRange_of_finrank_constantCompositum_eq`

```lean
TauCeti.linearDisjoint_fieldRange_of_finrank_constantCompositum_eq.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  (h : Module.finrank F ↥(TauCeti.constantCompositum F k' F') = Module.finrank k k') :
  (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 77. `TauCeti.linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq`

```lean
TauCeti.linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsAlgebraic k k']
  (h :
    ∀ (M : IntermediateField k k'),
      FiniteDimensional k ↥M → Module.finrank F ↥(TauCeti.constantCompositum F (↥M) F') = Module.finrank k ↥M) :
  (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 78. `TauCeti.constantBasis_apply`

```lean
TauCeti.constantBasis_apply.{u, u', v, v', u_1} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'} [Field k]
  [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) {ι : Type u_1} (b : Module.Basis ι k k') (i : ι) :
  (TauCeti.constantBasis hex h b) i = (algebraMap k' F') (b i)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 79. `TauCeti.coe_constantBasis`

```lean
TauCeti.coe_constantBasis.{u, u', v, v', u_1} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'} [Field k]
  [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) {ι : Type u_1} (b : Module.Basis ι k k') :
  ⇑(TauCeti.constantBasis hex h b) = ⇑(algebraMap k' F') ∘ ⇑b
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 80. `TauCeti.constantBasis_repr_algebraMap`

```lean
TauCeti.constantBasis_repr_algebraMap.{u, u', v, v', u_1} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) {ι : Type u_1} (b : Module.Basis ι k k') (c : k') (i : ι) :
  ((TauCeti.constantBasis hex h b).repr ((algebraMap k' F') c)) i = (algebraMap k F) ((b.repr c) i)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 81. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.constantBasis_mapPowExpCharPowOfIsSeparable_repr_pow`

```lean
TauCeti.constantBasis_mapPowExpCharPowOfIsSeparable_repr_pow.{u, u', v, v', u_1} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : TauCeti.constantCompositum F k' F' = ⊤) (q n : ℕ) [ExpChar k q] [ExpChar F' q]
  {ι : Type u_1} (b : Module.Basis ι k k') (z : F') (i : ι) :
  ((TauCeti.constantBasis hex h (Module.Basis.mapPowExpCharPowOfIsSeparable q n b)).repr (z ^ q ^ n)) i =
    ((TauCeti.constantBasis hex h b).repr z) i ^ q ^ n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 82. `IsIntegrallyClosedIn.of_constantCompositum_eq_top`

```lean
IsIntegrallyClosedIn.of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) : IsIntegrallyClosedIn k' F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 83. `TauCeti.trace_algebraMap_of_constantCompositum_eq_top`

```lean
TauCeti.trace_algebraMap_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : TauCeti.constantCompositum F k' F' = ⊤) [FiniteDimensional k k'] (c : k') :
  (Algebra.trace F F') ((algebraMap k' F') c) = (algebraMap k F) ((Algebra.trace k k') c)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 84. `TauCeti.traceDual_constantBasis`

```lean
TauCeti.traceDual_constantBasis.{u, u', v, v', u_1} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'} [Field k]
  [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) [FiniteDimensional k k'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] {ι : Type u_1} [Finite ι] [DecidableEq ι] (b : Module.Basis ι k k') :
  (TauCeti.constantBasis hex h b).traceDual = TauCeti.constantBasis hex h b.traceDual
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 85. `TauCeti.constantCompositum_mono`

```lean
TauCeti.constantCompositum_mono.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'} [Field k]
  [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F'] {L M : IntermediateField k k'}
  (h : L ≤ M) : TauCeti.constantCompositum F (↥L) F' ≤ TauCeti.constantCompositum F (↥M) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 86. `TauCeti.constantCompositum_eq_iSup_adjoin_finset`

```lean
TauCeti.constantCompositum_eq_iSup_adjoin_finset.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F'] :
  TauCeti.constantCompositum F k' F' = ⨆ S, TauCeti.constantCompositum F (↥(IntermediateField.adjoin k ↑S)) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 87. `TauCeti.exists_finset_of_mem_constantCompositum`

```lean
TauCeti.exists_finset_of_mem_constantCompositum.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F'] {x : F'}
  (hx : x ∈ TauCeti.constantCompositum F k' F') :
  ∃ S, x ∈ TauCeti.constantCompositum F (↥(IntermediateField.adjoin k ↑S)) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 88. `TauCeti.exists_finiteDimensional_constantSubfield_of_mem_constantCompositum`

```lean
TauCeti.exists_finiteDimensional_constantSubfield_of_mem_constantCompositum.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F']
  [Algebra.IsAlgebraic k k'] {x : F'} (hx : x ∈ TauCeti.constantCompositum F k' F') :
  ∃ L, FiniteDimensional k ↥L ∧ x ∈ TauCeti.constantCompositum F (↥L) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 89. `TauCeti.exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum`

```lean
TauCeti.exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum.{u, u', v, v'} {k : Type u}
  {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F']
  [Algebra F F'] [Algebra.IsAlgebraic k k'] (S : Finset F') (hS : ∀ x ∈ S, x ∈ TauCeti.constantCompositum F k' F') :
  ∃ L, FiniteDimensional k ↥L ∧ ∀ x ∈ S, x ∈ TauCeti.constantCompositum F (↥L) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 90. `TauCeti.exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum`

```lean
TauCeti.exists_finiteDimensional_constantSubfield_of_fg_le_constantCompositum.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F']
  [Algebra.IsAlgebraic k k'] {E : IntermediateField F F'} (hE : E.FG) (hle : E ≤ TauCeti.constantCompositum F k' F') :
  ∃ L, FiniteDimensional k ↥L ∧ E ≤ TauCeti.constantCompositum F (↥L) F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 91. `TauCeti.Place.isIntegralBasis_constantBasis`

```lean
TauCeti.Place.isIntegralBasis_constantBasis.{u, u', v, v', u_1} {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) {ι : Type u_1} [Finite ι] (b : Module.Basis ι k k')
  (P : TauCeti.Place k F) : TauCeti.Place.IsIntegralBasis F' P (TauCeti.constantBasis hex h b)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 92. `TauCeti.constantCompositum_ratFunc_eq_top`

```lean
TauCeti.constantCompositum_ratFunc_eq_top.{u_1, u_2} {k : Type u_1} {k' : Type u_2} [Field k] [Field k']
  [Algebra (RatFunc k) (RatFunc k')] (hX : (algebraMap (RatFunc k) (RatFunc k')) RatFunc.X = RatFunc.X) :
  TauCeti.constantCompositum (RatFunc k) k' (RatFunc k') = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 93. `TauCeti.Place.restrict_ratFunc_eq_infty_iff`

```lean
TauCeti.Place.restrict_ratFunc_eq_infty_iff.{u_1, u_2} {k : Type u_1} {k' : Type u_2} [Field k] [Field k']
  [Algebra k k'] [FiniteDimensional k k'] [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]
  (hX : (algebraMap (RatFunc k) (RatFunc k')) RatFunc.X = RatFunc.X) (P' : TauCeti.Place k' (RatFunc k')) :
  TauCeti.Place.restrict k (RatFunc k) P' = TauCeti.Place.infty k ↔ P' = TauCeti.Place.infty k'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 94. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_finiteDimensional`

```lean
TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_finiteDimensional.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  [FiniteDimensional k k'] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') :
  Submodule.span (TauCeti.Place.restrict k F P').ResidueField (Set.range ⇑(algebraMap k' P'.ResidueField)) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 95. `TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`

```lean
TauCeti.Place.span_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u}
  {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F]
  [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsSeparable k k'] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') :
  Submodule.span (TauCeti.Place.restrict k F P').ResidueField (Set.range ⇑(algebraMap k' P'.ResidueField)) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 96. `TauCeti.Place.adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top`

```lean
TauCeti.Place.adjoin_range_algebraMap_residueField_eq_top_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u}
  {k' : Type u'} {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F]
  [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsSeparable k k'] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  (h : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') :
  IntermediateField.adjoin (TauCeti.Place.restrict k F P').ResidueField (Set.range ⇑(algebraMap k' P'.ResidueField)) = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 97. `TauCeti.Place.degree_eq_one_of_constantCompositum_eq_top`

```lean
TauCeti.Place.degree_eq_one_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k'] [Normal k k']
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (h : TauCeti.constantCompositum F k' F' = ⊤)
  (P' : TauCeti.Place k' F') (φ : (TauCeti.Place.restrict k F P').ResidueField →ₐ[k] k') : P'.degree = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 98. `TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one`

```lean
TauCeti.Place.exists_constantCompositum_eq_top_and_forall_degree_eq_one.{u, v} {k : Type u} {F : Type v} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (P : TauCeti.Place k F)
  [Algebra.IsSeparable k P.ResidueField] :
  ∃ F' k',
    FiniteDimensional k ↥k' ∧
      Algebra.IsSeparable k ↥k' ∧
        TauCeti.constantCompositum F ↥k' ↥F' = ⊤ ∧
          ∀ (P' : TauCeti.Place ↥k' ↥F'), TauCeti.Place.restrict k F P' = P → P'.degree = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 99. `TauCeti.Place.isTotallyRamified_iff`

```lean
TauCeti.Place.isTotallyRamified_iff.{u', v, v'} {k' : Type u'} (F : Type v) {F' : Type v'} [Field k'] [Field F]
  [Field F'] [Algebra k' F'] [Algebra F F'] {P' : TauCeti.Place k' F'} :
  TauCeti.Place.IsTotallyRamified F P' ↔ TauCeti.Place.ramificationIdx F P' = Module.finrank F F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 100. `TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified`

```lean
TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v)
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] {P' : TauCeti.Place k' F'}
  (h : TauCeti.Place.IsTotallyRamified F P') : TauCeti.Place.relativeDegree k F P' = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 101. `TauCeti.Place.eq_of_isTotallyRamified`

```lean
TauCeti.Place.eq_of_isTotallyRamified.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v) {F' : Type v'} [Field k]
  [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] {P' Q' : TauCeti.Place k' F'}
  (h : TauCeti.Place.IsTotallyRamified F P') (hQ : TauCeti.Place.restrict k F Q' = TauCeti.Place.restrict k F P') :
  Q' = P'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 102. `TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified`

```lean
TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified.{u, u', v, v'} (k : Type u) {k' : Type u'}
  (F : Type v) {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F']
  [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  {P' : TauCeti.Place k' F'} (h : TauCeti.Place.IsTotallyRamified F P') :
  {Q' | TauCeti.Place.restrict k F Q' = TauCeti.Place.restrict k F P'} = {P'}
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 103. `TauCeti.Place.adjoin_eq_top_of_isTotallyRamified_of_ord_eq_one`

```lean
TauCeti.Place.adjoin_eq_top_of_isTotallyRamified_of_ord_eq_one.{u', v, v'} {k' : Type u'} (F : Type v) {F' : Type v'}
  [Field k'] [Field F] [Field F'] [Algebra k' F'] [Algebra F F'] [FiniteDimensional F F'] {P' : TauCeti.Place k' F'}
  {t : F'} (h : TauCeti.Place.IsTotallyRamified F P') (ht : P'.ord t = 1) : F⟮t⟯ = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 104. `TauCeti.Place.IsEisensteinAt.natDegree_pos`

```lean
TauCeti.Place.IsEisensteinAt.natDegree_pos.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {P : TauCeti.Place k F} {φ : Polynomial F} (h : P.IsEisensteinAt φ) : 0 < φ.natDegree
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 105. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.mem_maximalIdeal_sq_of_two_le_ord`

```lean
TauCeti.Place.mem_maximalIdeal_sq_of_two_le_ord.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {f : ↥P.integers} (h : 2 ≤ P.ord ↑f) : f ∈ IsLocalRing.maximalIdeal ↥P.integers ^ 2
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 106. `TauCeti.Place.isEisensteinAt_map`

```lean
TauCeti.Place.isEisensteinAt_map.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {ψ : Polynomial ↥P.integers} (hdeg : 0 < ψ.natDegree)
  (h : ψ.IsEisensteinAt (IsLocalRing.maximalIdeal ↥P.integers)) :
  P.IsEisensteinAt (Polynomial.map (algebraMap (↥P.integers) F) ψ)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 107. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.valuation_lt_of_ord_lt`

```lean
TauCeti.Place.valuation_lt_of_ord_lt.{u', v'} {k' : Type u'} {F' : Type v'} [Field k'] [Field F'] [Algebra k' F']
  {P' : TauCeti.Place k' F'} {a b : F'} (hb : b ≠ 0) (h : a ≠ 0 → P'.ord b < P'.ord a) : P'.valuation a < P'.valuation b
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 108. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.sum_ne_zero_of_forall_valuation_lt`

```lean
TauCeti.Place.sum_ne_zero_of_forall_valuation_lt.{u', v', u_1} {k' : Type u'} {F' : Type v'} [Field k'] [Field F']
  [Algebra k' F'] (Q' : TauCeti.Place k' F') {ι : Type u_1} {s : Finset ι} {T : ι → F'} {j : ι} (hj : j ∈ s)
  (hTj : T j ≠ 0) (hlt : ∀ i ∈ s, i ≠ j → Q'.valuation (T i) < Q'.valuation (T j)) : ∑ i ∈ s, T i ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 109. `TauCeti.Place.natDegree_mul_ord_eq_ramificationIdx`

```lean
TauCeti.Place.natDegree_mul_ord_eq_ramificationIdx.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v)
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] {P' : TauCeti.Place k' F'} [Algebra.IsIntegral F F']
  {φ : Polynomial F} (hφ : (TauCeti.Place.restrict k F P').IsEisensteinAt φ) {y : F'}
  (hy : (Polynomial.aeval y) φ = 0) : ↑φ.natDegree * P'.ord y = ↑(TauCeti.Place.ramificationIdx F P')
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 110. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.ramificationIdx_eq_and_ord_eq_one`

```lean
TauCeti.Place.ramificationIdx_eq_and_ord_eq_one.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v) {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] {P' : TauCeti.Place k' F'} [Algebra.IsIntegral F F']
  [FiniteDimensional F F'] {y : F'} (htop : F⟮y⟯ = ⊤)
  (hφ : (TauCeti.Place.restrict k F P').IsEisensteinAt (minpoly F y)) :
  TauCeti.Place.IsTotallyRamified F P' ∧ P'.ord y = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 111. `TauCeti.Place.isTotallyRamified_of_isEisensteinAt`

```lean
TauCeti.Place.isTotallyRamified_of_isEisensteinAt.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v) {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] {P' : TauCeti.Place k' F'} [Algebra.IsIntegral F F']
  [FiniteDimensional F F'] {y : F'} (htop : F⟮y⟯ = ⊤)
  (hφ : (TauCeti.Place.restrict k F P').IsEisensteinAt (minpoly F y)) : TauCeti.Place.IsTotallyRamified F P'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 112. `TauCeti.Place.ord_eq_one_of_isEisensteinAt`

```lean
TauCeti.Place.ord_eq_one_of_isEisensteinAt.{u, u', v, v'} (k : Type u) {k' : Type u'} (F : Type v) {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] {P' : TauCeti.Place k' F'} [Algebra.IsIntegral F F']
  [FiniteDimensional F F'] {y : F'} (htop : F⟮y⟯ = ⊤)
  (hφ : (TauCeti.Place.restrict k F P').IsEisensteinAt (minpoly F y)) : P'.ord y = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 113. `TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top`

```lean
TauCeti.Place.differentExponent_eq_zero_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] (hcomp : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') :
  TauCeti.Place.differentExponent k F P' = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 114. `TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`

```lean
TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'} {F : Type v}
  {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
  (hcomp : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') :
  Algebra.IsUnramifiedAt (↥(TauCeti.Place.restrict k F P').integers)
    (TauCeti.Place.centerIntegralClosure k F P').asIdeal
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 115. `TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`

```lean
TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hcomp : TauCeti.constantCompositum F k' F' = ⊤) (P' : TauCeti.Place k' F') : TauCeti.Place.ramificationIdx F P' = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 116. `TauCeti.isIntegrallyClosedIn_of_isTotallyRamified`

```lean
TauCeti.isIntegrallyClosedIn_of_isTotallyRamified.{u, v, v'} {k : Type u} {F : Type v} {F' : Type v'} [Field k]
  [Field F] [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] (hex : IsIntegrallyClosedIn k F) {P' : TauCeti.Place k F'}
  (hP' : TauCeti.Place.IsTotallyRamified F P') : IsIntegrallyClosedIn k F'
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 117. `TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one`

```lean
TauCeti.Place.finite_setOf_forall_ord_sub_algebraMap_ne_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (hF : TauCeti.IsFunctionField k F) {x : F} (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  {P | P.degree = 1 ∧ 0 ≤ P.ord x ∧ ∀ (a : k), P.ord (x - (algebraMap k F) a) ≠ 1}.Finite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 118. `TauCeti.Place.finite_setOf_forall_irreducible_ord_aeval_ne_one`

```lean
TauCeti.Place.finite_setOf_forall_irreducible_ord_aeval_ne_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) {x : F} (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] :
  {P | 0 ≤ P.ord x ∧ ∀ (q : Polynomial k), Irreducible q → P.ord ((Polynomial.aeval x) q) ≠ 1}.Finite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 119. `TauCeti.Place.infinite_setOf_isSeparable_residueField`

```lean
TauCeti.Place.infinite_setOf_isSeparable_residueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (hF : TauCeti.IsFunctionField k F) {x : F} (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  {P | Algebra.IsSeparable k P.ResidueField}.Infinite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 120. `TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential`

```lean
TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential.{u_1, u_2} {k : Type u_1} {k' : Type u_2} [Field k] [Field k']
  [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Algebra (RatFunc k) (RatFunc k')]
  [IsScalarTower k (RatFunc k) (RatFunc k')] (hX : (algebraMap (RatFunc k) (RatFunc k')) RatFunc.X = RatFunc.X) :
  (TauCeti.weilDifferentialCotrace k' (RatFunc k') ⋯ ⋯) ⟨TauCeti.ratFuncWeilDifferential k, ⋯⟩ =
    ⟨TauCeti.ratFuncWeilDifferential k', ⋯⟩
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 121. `TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating`

```lean
TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating.{u_1, u_2, u_3, u_4} {k : Type u_1} {k' : Type u_2}
  {F : Type u_3} {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] (h : TauCeti.constantCompositum F k' F' = ⊤) (hF : TauCeti.IsFunctionField k F) {x : F}
  (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] :
  (TauCeti.weilDifferentialCotrace k' F' hF ⋯) (TauCeti.weilDifferentialOfSeparating hF hx) =
    TauCeti.weilDifferentialOfSeparating ⋯ ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 122. `TauCeti.Place.completionEmbedding_apply`

```lean
TauCeti.Place.completionEmbedding_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (x : F) : P.completionEmbedding x = ↑(WithVal.toVal P.valuation x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 123. `TauCeti.Place.valuation_completionEmbedding`

```lean
TauCeti.Place.valuation_completionEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (x : F) : Valued.v (P.completionEmbedding x) = P.valuation x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 124. `TauCeti.Place.denseRange_completionEmbedding`

```lean
TauCeti.Place.denseRange_completionEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) : DenseRange ⇑P.completionEmbedding
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 125. `TauCeti.Place.completionPlace_valuation`

```lean
TauCeti.Place.completionPlace_valuation.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (x : P.Completion) : P.completionPlace.valuation x = Valued.v x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 126. `TauCeti.Place.ord_completionEmbedding`

```lean
TauCeti.Place.ord_completionEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (x : F) : P.completionPlace.ord (P.completionEmbedding x) = P.ord x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 127. `TauCeti.Place.isUniformizer_completionEmbedding_iff`

```lean
TauCeti.Place.isUniformizer_completionEmbedding_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (x : F) :
  P.completionPlace.valuation.IsUniformizer (P.completionEmbedding x) ↔ P.valuation.IsUniformizer x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 128. `TauCeti.Place.completionEmbedding_mem_filtration_iff`

```lean
TauCeti.Place.completionEmbedding_mem_filtration_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {a : ℤ} {x : F} :
  P.completionEmbedding x ∈ P.completionPlace.filtration a ↔ x ∈ P.filtration a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 129. `TauCeti.Place.isClosed_completionPlace_filtration`

```lean
TauCeti.Place.isClosed_completionPlace_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (a : ℤ) : IsClosed ↑(P.completionPlace.filtration a)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 130. `TauCeti.Place.exists_forall_sub_mem_completionPlace_filtration`

```lean
TauCeti.Place.exists_forall_sub_mem_completionPlace_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {g : ℕ → P.Completion}
  (hg : ∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.completionPlace.filtration ↑m) :
  ∃ x, ∀ (n : ℕ), x - g n ∈ P.completionPlace.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 131. `TauCeti.Place.exists_sub_completionEmbedding_mem_filtration`

```lean
TauCeti.Place.exists_sub_completionEmbedding_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (x : P.Completion) (b : ℤ) :
  ∃ y, x - P.completionEmbedding y ∈ P.completionPlace.filtration b
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 132. `TauCeti.Place.exists_filtration_sub_completionEmbedding_mem`

```lean
TauCeti.Place.exists_filtration_sub_completionEmbedding_mem.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {a b : ℤ} (hab : a ≤ b) (x : ↥(P.completionPlace.filtration a)) :
  ∃ y, ↑x - P.completionEmbedding ↑y ∈ P.completionPlace.filtration b
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 133. `TauCeti.Place.completionFiltrationMap_apply`

```lean
TauCeti.Place.completionFiltrationMap_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (a : ℤ) (x : ↥(P.filtration a)) :
  ↑((P.completionFiltrationMap a) x) = P.completionEmbedding ↑x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 134. `TauCeti.Place.completionFiltrationQuotientEquiv_apply_mk`

```lean
TauCeti.Place.completionFiltrationQuotientEquiv_apply_mk.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {a b : ℤ} (hab : a ≤ b) (x : ↥(P.filtration a)) :
  (P.completionFiltrationQuotientEquiv hab) (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk ((P.completionFiltrationMap a) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 135. `TauCeti.Place.completionIntegersEmbedding_apply`

```lean
TauCeti.Place.completionIntegersEmbedding_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (x : ↥P.integers) :
  ↑(P.completionIntegersEmbedding x) = P.completionEmbedding ↑x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 136. `TauCeti.Place.residueFieldEquivCompletion_apply_residue`

```lean
TauCeti.Place.residueFieldEquivCompletion_apply_residue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (x : ↥P.integers) :
  P.residueFieldEquivCompletion ((IsLocalRing.residue ↥P.integers) x) =
    (IsLocalRing.residue ↥P.completionPlace.integers) (P.completionIntegersEmbedding x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 137. `TauCeti.Place.residueFieldEquivCompletion_symm_residue_completionIntegersEmbedding`

```lean
TauCeti.Place.residueFieldEquivCompletion_symm_residue_completionIntegersEmbedding.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) (x : ↥P.integers) :
  P.residueFieldEquivCompletion.symm
      ((IsLocalRing.residue ↥P.completionPlace.integers) (P.completionIntegersEmbedding x)) =
    (IsLocalRing.residue ↥P.integers) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 138. `TauCeti.Place.degree_completionPlace`

```lean
TauCeti.Place.degree_completionPlace.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) : P.completionPlace.degree = P.degree
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 139. `Ideal.Quotient.powLift_mk`

```lean
Ideal.Quotient.powLift_mk.{u_1} {B : Type u_1} [CommRing B] (p : ℕ) [hp : Fact (Nat.Prime p)] (hpB : ↑p = 0)
  {I : Ideal B} (hI : I ^ 2 = ⊥) (b : B) : (Ideal.Quotient.powLift p hpB hI) ((Ideal.Quotient.mk I) b) = b ^ p
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 140. `Ideal.Quotient.mk_powLift`

```lean
Ideal.Quotient.mk_powLift.{u_1} {B : Type u_1} [CommRing B] (p : ℕ) [hp : Fact (Nat.Prime p)] (hpB : ↑p = 0)
  {I : Ideal B} (hI : I ^ 2 = ⊥) (z : B ⧸ I) : (Ideal.Quotient.mk I) ((Ideal.Quotient.powLift p hpB hI) z) = z ^ p
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 141. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.directed_carrier`

```lean
TauCeti.PartialLift.directed_carrier.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K] [Field L]
  [Algebra K L] [CommRing B] [Algebra K B] {c : Set (TauCeti.PartialLift K L B)}
  (hc : IsChain (fun x1 x2 => x1 ≤ x2) c) : Directed (fun x1 x2 => x1 ≤ x2) fun i => (↑i).carrier
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 142. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.emb_compat`

```lean
TauCeti.PartialLift.emb_compat.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K] [Field L]
  [Algebra K L] [CommRing B] [Algebra K B] {c : Set (TauCeti.PartialLift K L B)} (hc : IsChain (fun x1 x2 => x1 ≤ x2) c)
  (i j : ↑c) (h : (↑i).carrier.toSubalgebra ≤ (↑j).carrier.toSubalgebra) :
  (↑i).emb = (↑j).emb.comp (Subalgebra.inclusion h)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 143. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.union_emb_of_mem`

```lean
TauCeti.PartialLift.union_emb_of_mem.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K] [Field L]
  [Algebra K L] [CommRing B] [Algebra K B] {c : Set (TauCeti.PartialLift K L B)} (hc : IsChain (fun x1 x2 => x1 ≤ x2) c)
  [Nonempty ↑c] (x : ↥(TauCeti.PartialLift.union c hc).carrier) {φ : TauCeti.PartialLift K L B} (hφ : φ ∈ c)
  (hx : ↑x ∈ φ.carrier) : (TauCeti.PartialLift.union c hc).emb x = φ.emb ⟨↑x, hx⟩
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 144. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.le_union`

```lean
TauCeti.PartialLift.le_union.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K] [Field L]
  [Algebra K L] [CommRing B] [Algebra K B] {c : Set (TauCeti.PartialLift K L B)} (hc : IsChain (fun x1 x2 => x1 ≤ x2) c)
  [Nonempty ↑c] {φ : TauCeti.PartialLift K L B} (hφ : φ ∈ c) : φ ≤ TauCeti.PartialLift.union c hc
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 145. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.exists_mem_of_mem_union`

```lean
TauCeti.PartialLift.exists_mem_of_mem_union.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K]
  [Field L] [Algebra K L] [CommRing B] [Algebra K B] {c : Set (TauCeti.PartialLift K L B)}
  (hc : IsChain (fun x1 x2 => x1 ≤ x2) c) [Nonempty ↑c] (x : ↥(TauCeti.PartialLift.union c hc).carrier) :
  ∃ φ ∈ c, ↑x ∈ φ.carrier
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 146. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.exists_le_of_pow_mem`

```lean
TauCeti.PartialLift.exists_le_of_pow_mem.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K]
  [Field L] [Algebra K L] [CommRing B] [Algebra K B] (p : ℕ) [Fact (Nat.Prime p)] [CharP L p]
  (φ : TauCeti.PartialLift K L B) {a : L} (ha : a ∉ φ.carrier) (hap : a ^ p ∈ φ.carrier) {b : B}
  (hb : φ.emb ⟨a ^ p, hap⟩ = b ^ p) :
  ∃ φ',
    φ ≤ φ' ∧
      φ'.carrier = IntermediateField.restrictScalars K (↥φ.carrier)⟮a⟯ ∧ ∃ (h : a ∈ φ'.carrier), φ'.emb ⟨a, h⟩ = b
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 147. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.PartialLift.mk_emb_of_le`

```lean
TauCeti.PartialLift.mk_emb_of_le.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {B : Type u_3} [Field K] [Field L]
  [Algebra K L] [CommRing B] [Algebra K B] {I : Ideal B} {f : L →ₐ[K] B ⧸ I} {φ φ' : TauCeti.PartialLift K L B}
  (hφφ' : φ ≤ φ') {a : L} (hcarrier : φ'.carrier = IntermediateField.restrictScalars K (↥φ.carrier)⟮a⟯)
  (ha : a ∈ φ'.carrier) (hφa : (Ideal.Quotient.mk I) (φ'.emb ⟨a, ha⟩) = f a)
  (hφ : ∀ (x : ↥φ.carrier), (Ideal.Quotient.mk I) (φ.emb x) = f ↑x) (x : ↥φ'.carrier) :
  (Ideal.Quotient.mk I) (φ'.emb x) = f ↑x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 148. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.powFieldRingHom_apply`

```lean
TauCeti.powFieldRingHom_apply.{u_1, u_2, u_3} (p : ℕ) [Fact (Nat.Prime p)] {K : Type u_1} {L : Type u_2} [Field K]
  [Field L] [Algebra K L] [CharP K p] [PerfectField K] {B : Type u_3} [CommRing B] [Algebra K B] (hpB : ↑p = 0)
  {I : Ideal B} (hI : I ^ 2 = ⊥) (f : L →ₐ[K] B ⧸ I) (x : L) :
  (TauCeti.powFieldRingHom p hpB hI f) ((TauCeti.iterateFrobeniusEquivPowers K L p 1) x) =
    (Ideal.Quotient.powLift p hpB hI) (f x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 149. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.powFieldLift_apply`

```lean
TauCeti.powFieldLift_apply.{u_1, u_2, u_3} (p : ℕ) [Fact (Nat.Prime p)] {K : Type u_1} {L : Type u_2} [Field K]
  [Field L] [Algebra K L] [CharP K p] [PerfectField K] {B : Type u_3} [CommRing B] [Algebra K B] (hpB : ↑p = 0)
  {I : Ideal B} (hI : I ^ 2 = ⊥) (f : L →ₐ[K] B ⧸ I) (x : L) :
  (TauCeti.powFieldLift p hpB hI f) ((TauCeti.iterateFrobeniusEquivPowers K L p 1) x) =
    (Ideal.Quotient.powLift p hpB hI) (f x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 150. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.mk_powFieldLift`

```lean
TauCeti.mk_powFieldLift.{u_1, u_2, u_3} (p : ℕ) [Fact (Nat.Prime p)] {K : Type u_1} {L : Type u_2} [Field K] [Field L]
  [Algebra K L] [CharP K p] [PerfectField K] {B : Type u_3} [CommRing B] [Algebra K B] (hpB : ↑p = 0) {I : Ideal B}
  (hI : I ^ 2 = ⊥) (f : L →ₐ[K] B ⧸ I) (y : ↥(TauCeti.frobeniusPowers K L p 1)) :
  (Ideal.Quotient.mk I) ((TauCeti.powFieldLift p hpB hI f) y) = f ↑y
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 151. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.exists_comp_eq_of_charP`

```lean
TauCeti.exists_comp_eq_of_charP.{u_1, u_2, u_3} (p : ℕ) [Fact (Nat.Prime p)] {K : Type u_1} {L : Type u_2} [Field K]
  [Field L] [Algebra K L] [CharP K p] [PerfectField K] {B : Type u_3} [CommRing B] [Algebra K B] (hpB : ↑p = 0)
  {I : Ideal B} (hI : I ^ 2 = ⊥) [CharP L p] (f : L →ₐ[K] B ⧸ I) : ∃ g, (Ideal.Quotient.mkₐ K I).comp g = f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 152. `TauCeti.residue_residueFieldSection`

```lean
TauCeti.residue_residueFieldSection.{u_1, u_2} (k : Type u_1) (R : Type u_2) [CommRing k] [CommRing R] [IsLocalRing R]
  [Algebra k R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
  (a : IsLocalRing.ResidueField R) : (IsLocalRing.residue R) ((TauCeti.residueFieldSection k R) a) = a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 153. `TauCeti.eq_residueFieldSection`

```lean
TauCeti.eq_residueFieldSection.{u_1, u_2} (k : Type u_1) (R : Type u_2) [CommRing k] [CommRing R] [IsLocalRing R]
  [Algebra k R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra.FormallySmooth k (IsLocalRing.ResidueField R)]
  [Algebra.FormallyUnramified k (IsLocalRing.ResidueField R)] {s : IsLocalRing.ResidueField R →ₐ[k] R}
  (hs : ∀ (a : IsLocalRing.ResidueField R), (IsLocalRing.residue R) (s a) = a) : s = TauCeti.residueFieldSection k R
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 154. `TauCeti.exists_residueFieldSection`

```lean
TauCeti.exists_residueFieldSection.{u_1, u_2} (k : Type u_1) (R : Type u_2) [Field k] [CommRing R] [IsLocalRing R]
  [Algebra k R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
  ∃ s, ∀ (a : IsLocalRing.ResidueField R), (IsLocalRing.residue R) (s a) = a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 155. `TauCeti.Place.exists_completionResidueFieldSection`

```lean
TauCeti.Place.exists_completionResidueFieldSection.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) :
  ∃ s, ∀ (a : P.ResidueField), (IsLocalRing.residue ↥P.completionPlace.integers) (s a) = P.residueFieldEquivCompletion a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 156. `TauCeti.Place.completionResidueFieldSection_apply`

```lean
TauCeti.Place.completionResidueFieldSection_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (a : P.ResidueField) :
  P.completionResidueFieldSection a =
    (TauCeti.residueFieldSection k ↥P.completionPlace.integers) (P.residueFieldEquivCompletion a)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 157. `TauCeti.Place.residue_completionResidueFieldSection`

```lean
TauCeti.Place.residue_completionResidueFieldSection.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (a : P.ResidueField) :
  (IsLocalRing.residue ↥P.completionPlace.integers) (P.completionResidueFieldSection a) =
    P.residueFieldEquivCompletion a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 158. `TauCeti.Place.eq_completionResidueFieldSection`

```lean
TauCeti.Place.eq_completionResidueFieldSection.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {s : P.ResidueField →ₐ[k] ↥P.completionPlace.integers}
  (hs :
    ∀ (a : P.ResidueField), (IsLocalRing.residue ↥P.completionPlace.integers) (s a) = P.residueFieldEquivCompletion a) :
  s = P.completionResidueFieldSection
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 159. `TauCeti.Place.sub_completionResidueFieldSection_mem_filtration_one`

```lean
TauCeti.Place.sub_completionResidueFieldSection_mem_filtration_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  (x : ↥P.completionPlace.integers) :
  ↑x -
      ↑(P.completionResidueFieldSection
          (P.residueFieldEquivCompletion.symm ((IsLocalRing.residue ↥P.completionPlace.integers) x))) ∈
    P.completionPlace.filtration 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 160. `TauCeti.Place.completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one`

```lean
TauCeti.Place.completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  (x : ↥P.integers) :
  P.completionEmbedding ↑x - ↑(P.completionResidueFieldSection ((IsLocalRing.residue ↥P.integers) x)) ∈
    P.completionPlace.filtration 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 161. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.div_uniformizer_mem_filtration_iff`

```lean
TauCeti.Place.div_uniformizer_mem_filtration_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) (a : ℤ) (x : F) :
  x / t ∈ P.filtration a ↔ x ∈ P.filtration (a + 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 162. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.constant_sub_mem_filtration_one_iff`

```lean
TauCeti.Place.constant_sub_mem_filtration_one_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (c d : k) : (algebraMap k F) c - (algebraMap k F) d ∈ P.filtration 1 ↔ c = d
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 163. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.exists_sub_sum_mem_filtration`

```lean
TauCeti.Place.exists_sub_sum_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : F) (hx : x ∈ P.integers) :
  ∃ c, x - ∑ i, (algebraMap k F) (c i) * t ^ ↑i ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 164. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.sum_mem_filtration_iff`

```lean
TauCeti.Place.sum_mem_filtration_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) (n : ℕ) (c : Fin n → k) :
  ∑ i, (algebraMap k F) (c i) * t ^ ↑i ∈ P.filtration ↑n ↔ c = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 165. `TauCeti.Place.existsUnique_sub_sum_mem_filtration`

```lean
TauCeti.Place.existsUnique_sub_sum_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : F)
  (hx : x ∈ P.integers) : ∃! c, x - ∑ i, (algebraMap k F) (c i) * t ^ ↑i ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 166. `TauCeti.Place.sub_sum_truncatedExpansion_mem_filtration`

```lean
TauCeti.Place.sub_sum_truncatedExpansion_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) :
  ↑x - ∑ i, (algebraMap k F) (P.truncatedExpansion hP ht n x i) * t ^ ↑i ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 167. `TauCeti.Place.truncatedExpansion_eq_iff`

```lean
TauCeti.Place.truncatedExpansion_eq_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) (c : Fin n → k) :
  P.truncatedExpansion hP ht n x = c ↔ ↑x - ∑ i, (algebraMap k F) (c i) * t ^ ↑i ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 168. `TauCeti.Place.truncatedExpansion_zero`

```lean
TauCeti.Place.truncatedExpansion_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) : P.truncatedExpansion hP ht n 0 = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 169. `TauCeti.Place.truncatedExpansion_add`

```lean
TauCeti.Place.truncatedExpansion_add.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x y : ↥P.integers) :
  P.truncatedExpansion hP ht n (x + y) = P.truncatedExpansion hP ht n x + P.truncatedExpansion hP ht n y
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 170. `TauCeti.Place.truncatedExpansion_smul`

```lean
TauCeti.Place.truncatedExpansion_smul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (c : k) (x : ↥P.integers) :
  P.truncatedExpansion hP ht n (c • x) = c • P.truncatedExpansion hP ht n x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 171. `TauCeti.Place.truncatedExpansion_neg`

```lean
TauCeti.Place.truncatedExpansion_neg.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) :
  P.truncatedExpansion hP ht n (-x) = -P.truncatedExpansion hP ht n x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 172. `TauCeti.Place.truncatedExpansion_sub`

```lean
TauCeti.Place.truncatedExpansion_sub.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x y : ↥P.integers) :
  P.truncatedExpansion hP ht n (x - y) = P.truncatedExpansion hP ht n x - P.truncatedExpansion hP ht n y
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 173. `TauCeti.Place.truncatedExpansion_one`

```lean
TauCeti.Place.truncatedExpansion_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
  P.truncatedExpansion hP ht n 1 = fun i => if ↑i = 0 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 174. `TauCeti.Place.truncatedExpansion_algebraMap`

```lean
TauCeti.Place.truncatedExpansion_algebraMap.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (c : k) :
  P.truncatedExpansion hP ht n ((algebraMap k ↥P.integers) c) = fun i => if ↑i = 0 then c else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 175. `TauCeti.Place.truncatedExpansion_uniformizer`

```lean
TauCeti.Place.truncatedExpansion_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
  P.truncatedExpansion hP ht n ⟨t, ⋯⟩ = fun i => if ↑i = 1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 176. `TauCeti.Place.truncatedExpansion_mul`

```lean
TauCeti.Place.truncatedExpansion_mul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x y : ↥P.integers) (i : Fin n) :
  P.truncatedExpansion hP ht n (x * y) i =
    ∑ j with ↑j.1 + ↑j.2 = ↑i, P.truncatedExpansion hP ht n x j.1 * P.truncatedExpansion hP ht n y j.2
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 177. `TauCeti.Place.truncatedExpansion_castSucc`

```lean
TauCeti.Place.truncatedExpansion_castSucc.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) (i : Fin n) :
  P.truncatedExpansion hP ht (n + 1) x i.castSucc = P.truncatedExpansion hP ht n x i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 178. `TauCeti.Place.truncatedExpansion_castLE`

```lean
TauCeti.Place.truncatedExpansion_castLE.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {n m : ℕ} (hnm : n ≤ m) (x : ↥P.integers)
  (i : Fin n) : P.truncatedExpansion hP ht m x (Fin.castLE hnm i) = P.truncatedExpansion hP ht n x i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 179. `TauCeti.Place.truncatedExpansion_eq_iff_sub_mem_filtration`

```lean
TauCeti.Place.truncatedExpansion_eq_iff_sub_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x y : ↥P.integers) :
  P.truncatedExpansion hP ht n x = P.truncatedExpansion hP ht n y ↔ ↑x - ↑y ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 180. `TauCeti.Place.linearMap_ext_zpow`

```lean
TauCeti.Place.linearMap_ext_zpow.{u_1, u_2, u_3} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} {M : Type u_3} [AddCommGroup M] [Module k M] (hP : P.degree = 1) (ht : P.ord t = 1)
  {m : ℤ} {f g : F →ₗ[k] M} (hfg : ∀ z ∈ P.filtration m, f z = g z) (h : ∀ j < m, f (t ^ j) = g (t ^ j)) : f = g
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 181. `TauCeti.Place.coeff_powerSeriesExpansion`

```lean
TauCeti.Place.coeff_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) (i : Fin n) :
  (PowerSeries.coeff ↑i) ((P.powerSeriesExpansion hP ht) x) = P.truncatedExpansion hP ht n x i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 182. `TauCeti.Place.sub_sum_coeff_powerSeriesExpansion_mem_filtration`

```lean
TauCeti.Place.sub_sum_coeff_powerSeriesExpansion_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ)
  (x : ↥P.integers) :
  ↑x - ∑ i, (algebraMap k F) ((PowerSeries.coeff ↑i) ((P.powerSeriesExpansion hP ht) x)) * t ^ ↑i ∈ P.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 183. `TauCeti.Place.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero`

```lean
TauCeti.Place.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ)
  (x : ↥P.integers) : ↑x ∈ P.filtration ↑n ↔ ∀ i < n, (PowerSeries.coeff i) ((P.powerSeriesExpansion hP ht) x) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 184. `TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansion`

```lean
TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ)
  (x : ↥P.integers) : ↑x ∈ P.filtration ↑n ↔ ↑n ≤ ((P.powerSeriesExpansion hP ht) x).order
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 185. `TauCeti.Place.powerSeriesExpansion_injective`

```lean
TauCeti.Place.powerSeriesExpansion_injective.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  Function.Injective ⇑(P.powerSeriesExpansion hP ht)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 186. `TauCeti.Place.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq`

```lean
TauCeti.Place.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ)
  (x y : ↥P.integers) :
  ↑x - ↑y ∈ P.filtration ↑n ↔
    ∀ i < n,
      (PowerSeries.coeff i) ((P.powerSeriesExpansion hP ht) x) =
        (PowerSeries.coeff i) ((P.powerSeriesExpansion hP ht) y)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 187. `TauCeti.Place.powerSeriesExpansion_uniformizer`

```lean
TauCeti.Place.powerSeriesExpansion_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  (P.powerSeriesExpansion hP ht) ⟨t, ⋯⟩ = PowerSeries.X
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 188. `TauCeti.Place.powerSeriesExpansion_surjective`

```lean
TauCeti.Place.powerSeriesExpansion_surjective.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (hcomplete :
    ∀ (g : ℕ → F), (∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.filtration ↑m) → ∃ x, ∀ (n : ℕ), x - g n ∈ P.filtration ↑n) :
  Function.Surjective ⇑(P.powerSeriesExpansion hP ht)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 189. `TauCeti.Place.order_powerSeriesExpansion`

```lean
TauCeti.Place.order_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (x : ↥P.integers) (hx : x ≠ 0) :
  ((P.powerSeriesExpansion hP ht) x).order = ↑(P.ord ↑x).toNat
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 190. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.algebraMap_residueField_completion`

```lean
TauCeti.Place.algebraMap_residueField_completion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (a : P.ResidueField) :
  (algebraMap P.ResidueField P.Completion) a = ↑(P.completionResidueFieldSection a)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 191. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.residueFieldPlace_valuation`

```lean
TauCeti.Place.residueFieldPlace_valuation.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] :
  P.residueFieldPlace.valuation = P.completionPlace.valuation
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 192. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.mem_residueFieldPlace_filtration_iff`

```lean
TauCeti.Place.mem_residueFieldPlace_filtration_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {a : ℤ} {x : P.Completion} :
  x ∈ P.residueFieldPlace.filtration a ↔ x ∈ P.completionPlace.filtration a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 193. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.ord_residueFieldPlace`

```lean
TauCeti.Place.ord_residueFieldPlace.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (x : P.Completion) :
  P.residueFieldPlace.ord x = P.completionPlace.ord x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 194. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.residueFieldPlace_integers`

```lean
TauCeti.Place.residueFieldPlace_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] :
  P.residueFieldPlace.integers = P.completionPlace.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 195. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.coe_integersEquivResidueFieldPlace`

```lean
TauCeti.Place.coe_integersEquivResidueFieldPlace.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (x : ↥P.completionPlace.integers) :
  ↑(P.integersEquivResidueFieldPlace x) = ↑x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 196. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.coe_integersEquivResidueFieldPlace_symm`

```lean
TauCeti.Place.coe_integersEquivResidueFieldPlace_symm.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] (x : ↥P.residueFieldPlace.integers) :
  ↑(P.integersEquivResidueFieldPlace.symm x) = ↑x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 197. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.residue_integersEquivResidueFieldPlace_eq_iff`

```lean
TauCeti.Place.residue_integersEquivResidueFieldPlace_eq_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {y z : ↥P.completionPlace.integers} :
  (IsLocalRing.residue ↥P.residueFieldPlace.integers) (P.integersEquivResidueFieldPlace y) =
      (IsLocalRing.residue ↥P.residueFieldPlace.integers) (P.integersEquivResidueFieldPlace z) ↔
    (IsLocalRing.residue ↥P.completionPlace.integers) y = (IsLocalRing.residue ↥P.completionPlace.integers) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 198. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.integersEquivResidueFieldPlace_completionResidueFieldSection`

```lean
TauCeti.Place.integersEquivResidueFieldPlace_completionResidueFieldSection.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  (a : P.ResidueField) :
  P.integersEquivResidueFieldPlace (P.completionResidueFieldSection a) =
    (algebraMap P.ResidueField ↥P.residueFieldPlace.integers) a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 199. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.degree_residueFieldPlace`

```lean
TauCeti.Place.degree_residueFieldPlace.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] : P.residueFieldPlace.degree = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 200. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.ord_residueFieldPlace_uniformizer`

```lean
TauCeti.Place.ord_residueFieldPlace_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) : P.residueFieldPlace.ord t = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 201. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.bijective_residueFieldPlace_powerSeriesExpansion`

```lean
TauCeti.Place.bijective_residueFieldPlace_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) : Function.Bijective ⇑(P.residueFieldPlace.powerSeriesExpansion ⋯ ⋯)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 202. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_apply`

```lean
TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) :
  (P.completionIntegersEquivPowerSeriesResidueField ht) x =
    (P.residueFieldPlace.powerSeriesExpansion ⋯ ⋯) (P.integersEquivResidueFieldPlace x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 203. `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff`

```lean
TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_eq_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) (f : PowerSeries P.ResidueField) :
  (P.completionIntegersEquivPowerSeriesResidueField ht) x = f ↔
    ∀ (n : ℕ),
      ↑x - ∑ i, ↑(P.completionResidueFieldSection ((PowerSeries.coeff ↑i) f)) * t ^ ↑i ∈ P.completionPlace.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 204. `TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration`

```lean
TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_mem_filtration.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) (n : ℕ) :
  ↑x -
      ∑ i,
        ↑(P.completionResidueFieldSection
              ((PowerSeries.coeff ↑i) ((P.completionIntegersEquivPowerSeriesResidueField ht) x))) *
          t ^ ↑i ∈
    P.completionPlace.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 205. `TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_symm_mem_filtration`

```lean
TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeriesResidueField_symm_mem_filtration.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (f : PowerSeries P.ResidueField) (n : ℕ) :
  ↑((P.completionIntegersEquivPowerSeriesResidueField ht).symm f) -
      ∑ i, ↑(P.completionResidueFieldSection ((PowerSeries.coeff ↑i) f)) * t ^ ↑i ∈
    P.completionPlace.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 206. `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection`

```lean
TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_completionResidueFieldSection.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (a : P.ResidueField) :
  (P.completionIntegersEquivPowerSeriesResidueField ht) (P.completionResidueFieldSection a) = PowerSeries.C a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 207. `TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_uniformizer`

```lean
TauCeti.Place.completionIntegersEquivPowerSeriesResidueField_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) : (P.completionIntegersEquivPowerSeriesResidueField ht) ⟨t, ⋯⟩ = PowerSeries.X
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 208. `TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField`

```lean
TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) :
  PowerSeries.constantCoeff ((P.completionIntegersEquivPowerSeriesResidueField ht) x) =
    P.residueFieldEquivCompletion.symm ((IsLocalRing.residue ↥P.completionPlace.integers) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 209. `TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding`

```lean
TauCeti.Place.constantCoeff_completionIntegersEquivPowerSeriesResidueField_completionIntegersEmbedding.{u_1, u_2}
  {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F)
  [Algebra.IsSeparable k P.ResidueField] {t : P.Completion} (ht : P.completionPlace.ord t = 1) (x : ↥P.integers) :
  PowerSeries.constantCoeff ((P.completionIntegersEquivPowerSeriesResidueField ht) (P.completionIntegersEmbedding x)) =
    (IsLocalRing.residue ↥P.integers) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 210. `TauCeti.Place.mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField`

```lean
TauCeti.Place.mem_filtration_iff_le_order_completionIntegersEquivPowerSeriesResidueField.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (n : ℕ) (x : ↥P.completionPlace.integers) :
  ↑x ∈ P.completionPlace.filtration ↑n ↔ ↑n ≤ ((P.completionIntegersEquivPowerSeriesResidueField ht) x).order
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 211. `TauCeti.Place.order_completionIntegersEquivPowerSeriesResidueField`

```lean
TauCeti.Place.order_completionIntegersEquivPowerSeriesResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) (hx : x ≠ 0) :
  ((P.completionIntegersEquivPowerSeriesResidueField ht) x).order = ↑(P.completionPlace.ord ↑x).toNat
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 212. `TauCeti.Place.completionPlace_powerSeriesExpansion_surjective`

```lean
TauCeti.Place.completionPlace_powerSeriesExpansion_surjective.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  Function.Surjective ⇑(P.completionPlace.powerSeriesExpansion ⋯ ⋯)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 213. `TauCeti.Place.completionIntegersEquivPowerSeries_apply`

```lean
TauCeti.Place.completionIntegersEquivPowerSeries_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (x : ↥P.completionPlace.integers) :
  (P.completionIntegersEquivPowerSeries hP ht) x = (P.completionPlace.powerSeriesExpansion ⋯ ⋯) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 214. `TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration`

```lean
TauCeti.Place.sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1)
  (ht : P.ord t = 1) (f : PowerSeries k) (n : ℕ) :
  ↑((P.completionIntegersEquivPowerSeries hP ht).symm f) -
      ∑ i, (algebraMap k P.Completion) ((PowerSeries.coeff ↑i) f) * P.completionEmbedding t ^ ↑i ∈
    P.completionPlace.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 215. `TauCeti.Place.completionIntegersEquivPowerSeries_completionIntegersEmbedding`

```lean
TauCeti.Place.completionIntegersEquivPowerSeries_completionIntegersEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (x : ↥P.integers) :
  (P.completionIntegersEquivPowerSeries hP ht) (P.completionIntegersEmbedding x) = (P.powerSeriesExpansion hP ht) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 216. `TauCeti.Place.completionIntegersEquivPowerSeries_uniformizer`

```lean
TauCeti.Place.completionIntegersEquivPowerSeries_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  (P.completionIntegersEquivPowerSeries hP ht) (P.completionIntegersEmbedding ⟨t, ⋯⟩) = PowerSeries.X
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 217. `TauCeti.Place.continuous_completionIntegersEquivPowerSeries`

```lean
TauCeti.Place.continuous_completionIntegersEquivPowerSeries.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [TopologicalSpace k]
  [DiscreteTopology k] : Continuous ⇑(P.completionIntegersEquivPowerSeries hP ht)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 218. `TauCeti.Place.continuous_completionIntegersEquivPowerSeries_symm`

```lean
TauCeti.Place.continuous_completionIntegersEquivPowerSeries_symm.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [TopologicalSpace k]
  [DiscreteTopology k] : Continuous ⇑(P.completionIntegersEquivPowerSeries hP ht).symm
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 219. `TauCeti.Place.completionIntegersHomeomorphPowerSeries_apply`

```lean
TauCeti.Place.completionIntegersHomeomorphPowerSeries_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [TopologicalSpace k]
  [DiscreteTopology k] (x : ↥P.completionPlace.integers) :
  (P.completionIntegersHomeomorphPowerSeries hP ht) x = (P.completionIntegersEquivPowerSeries hP ht) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 220. `TauCeti.Place.completionIntegersHomeomorphPowerSeries_symm_apply`

```lean
TauCeti.Place.completionIntegersHomeomorphPowerSeries_symm_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [TopologicalSpace k]
  [DiscreteTopology k] (f : PowerSeries k) :
  (P.completionIntegersHomeomorphPowerSeries hP ht).symm f = (P.completionIntegersEquivPowerSeries hP ht).symm f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 221. `PowerSeries.derivative_map`

```lean
PowerSeries.derivative_map.{u_1, u_2} {R : Type u_1} {S : Type u_2} [CommSemiring R] [CommSemiring S]
  (φ : PowerSeries R) (f : R →+* S) :
  PowerSeries.derivative ((PowerSeries.map f) φ) = (PowerSeries.map f) (PowerSeries.derivative φ)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 222. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.PowerSeries.coeff_succ_pow_succ_eq_of_hasUniqueDiv`

```lean
PowerSeries.coeff_succ_pow_succ_eq_of_hasUniqueDiv.{u_1} {R : Type u_1} [CommSemiring R] [HasUniqueDiv R]
  (v : PowerSeries R) (n : ℕ) :
  (PowerSeries.coeff (n + 1)) (v ^ (n + 1)) = (PowerSeries.coeff n) (v ^ n * PowerSeries.derivative v)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 223. `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`

```lean
PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative.{u_1} {R : Type u_1} [CommSemiring R] (v : PowerSeries R)
  (n : ℕ) : (PowerSeries.coeff (n + 1)) (v ^ (n + 1)) = (PowerSeries.coeff n) (v ^ n * PowerSeries.derivative v)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 224. `TauCeti.LaurentSeries.coeff_algebraMap_mul`

```lean
TauCeti.LaurentSeries.coeff_algebraMap_mul.{u_1} {R : Type u_1} [CommSemiring R] (c : R) (f : LaurentSeries R) (n : ℤ) :
  ((algebraMap R (LaurentSeries R)) c * f).coeff n = c * f.coeff n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 225. `TauCeti.LaurentSeries.valuation_coe_of_isUnit`

```lean
TauCeti.LaurentSeries.valuation_coe_of_isUnit.{u_2} {K : Type u_2} [Field K] {h : PowerSeries K} (hh : IsUnit h) :
  Valued.v ((HahnSeries.ofPowerSeries ℤ K) h) = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 226. `TauCeti.LaurentSeries.isUnit_powerSeriesPart`

```lean
TauCeti.LaurentSeries.isUnit_powerSeriesPart.{u_2} {K : Type u_2} [Field K] {f : LaurentSeries K} (hf : f ≠ 0) :
  IsUnit f.powerSeriesPart
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 227. `TauCeti.LaurentSeries.valuation_eq_exp_neg_order`

```lean
TauCeti.LaurentSeries.valuation_eq_exp_neg_order.{u_2} {K : Type u_2} [Field K] {f : LaurentSeries K} (hf : f ≠ 0) :
  Valued.v f = WithZero.exp (-HahnSeries.order f)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 228. `TauCeti.LaurentSeries.valuation_coe`

```lean
TauCeti.LaurentSeries.valuation_coe.{u_2} {K : Type u_2} [Field K] {g : PowerSeries K} (hg : g ≠ 0) :
  Valued.v ((HahnSeries.ofPowerSeries ℤ K) g) = WithZero.exp (-↑g.order.toNat)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 229. `TauCeti.laurentSeries_algebraMap_mul_eq_smul`

```lean
TauCeti.laurentSeries_algebraMap_mul_eq_smul.{u_1, u_2} {R : Type u_1} {A : Type u_2} [CommSemiring R] [CommSemiring A]
  [Algebra R A] (c : R) (f : LaurentSeries A) : (algebraMap R (LaurentSeries A)) c * f = c • f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 230. `PowerSeries.coe_derivative`

```lean
PowerSeries.coe_derivative.{u_1} {R : Type u_1} [CommRing R] (f : PowerSeries R) :
  (HahnSeries.ofPowerSeries ℤ R) (PowerSeries.derivative f) =
    (LaurentSeries.derivative R) ((HahnSeries.ofPowerSeries ℤ R) f)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 231. `LaurentSeries.derivative_single_mul`

```lean
LaurentSeries.derivative_single_mul.{u_1} {R : Type u_1} [CommRing R] (m : ℤ) (c : R) (f : LaurentSeries R) :
  (LaurentSeries.derivative R) ((HahnSeries.single m) c * f) =
    (HahnSeries.single (m - 1)) (↑m * c) * f + (HahnSeries.single m) c * (LaurentSeries.derivative R) f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 232. `LaurentSeries.derivative_single_mul_coe`

```lean
LaurentSeries.derivative_single_mul_coe.{u_1} {R : Type u_1} [CommRing R] (m : ℤ) (c : R) (φ : PowerSeries R) :
  (LaurentSeries.derivative R) ((HahnSeries.single m) c * (HahnSeries.ofPowerSeries ℤ R) φ) =
    (HahnSeries.single (m - 1)) (↑m * c) * (HahnSeries.ofPowerSeries ℤ R) φ +
      (HahnSeries.single m) c * (HahnSeries.ofPowerSeries ℤ R) (PowerSeries.derivative φ)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 233. `LaurentSeries.derivative_mul`

```lean
LaurentSeries.derivative_mul.{u_1} {R : Type u_1} [CommRing R] (f g : LaurentSeries R) :
  (LaurentSeries.derivative R) (f * g) = (LaurentSeries.derivative R) f * g + f * (LaurentSeries.derivative R) g
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 234. `LaurentSeries.coeff_derivative_sub_zsmul_single_mul`

```lean
LaurentSeries.coeff_derivative_sub_zsmul_single_mul.{u_1} {R : Type u_1} [CommRing R] (m n : ℤ) (f : LaurentSeries R) :
  ((LaurentSeries.derivative R) f - m • ((HahnSeries.single (-1)) 1 * f)).coeff n = ↑(n + 1 - m) * f.coeff (n + 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 235. `LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le`

```lean
LaurentSeries.valuation_derivative_sub_zsmul_single_mul_le.{u_2} {K : Type u_2} [Field K] {m : ℤ} {f : LaurentSeries K}
  (hf : Valued.v f ≤ WithZero.exp (-m)) :
  Valued.v ((LaurentSeries.derivative K) f - m • ((HahnSeries.single (-1)) 1 * f)) ≤ WithZero.exp (-m)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 236. `PowerSeries.coeff_neg_one_coe_zpow_mul_derivative`

```lean
PowerSeries.coeff_neg_one_coe_zpow_mul_derivative.{u_1} {k : Type u_1} [Field k] {φ : PowerSeries k} (hφ : φ.order = 1)
  (n : ℤ) :
  ((HahnSeries.ofPowerSeries ℤ k) φ ^ n * (LaurentSeries.derivative k) ((HahnSeries.ofPowerSeries ℤ k) φ)).coeff (-1) =
    if n = -1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 237. `LaurentSeries.coeff_neg_one_map_mul_derivative`

```lean
LaurentSeries.coeff_neg_one_map_mul_derivative.{u_1} {K : Type u_1} [Field K] (ψ : LaurentSeries K →+* LaurentSeries K)
  (hC : ∀ (c : K), ψ (HahnSeries.C c) = HahnSeries.C c)
  (hψ : ∀ (f : LaurentSeries K), Valued.v f ≤ 1 → Valued.v (ψ f) ≤ 1) {φ : PowerSeries K} (hφ : φ.order = 1)
  (hX : ψ ((HahnSeries.single 1) 1) = (HahnSeries.ofPowerSeries ℤ K) φ) (f : LaurentSeries K) :
  (ψ f * (LaurentSeries.derivative K) ((HahnSeries.ofPowerSeries ℤ K) φ)).coeff (-1) = f.coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 238. `TauCeti.Place.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers`

```lean
TauCeti.Place.exists_powerSeries_eq_algEquivOfAlgEquiv_iff_mem_integers.{u_1, u_2, u_3} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {A : Type u_3} [Field A] [Algebra k A]
  (e : ↥P.completionPlace.integers ≃ₐ[k] PowerSeries A) (z : P.Completion) :
  (∃ f, (HahnSeries.ofPowerSeries ℤ A) f = (IsFractionRing.algEquivOfAlgEquiv e) z) ↔ z ∈ P.completionPlace.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 239. `TauCeti.Place.valuation_algEquivOfAlgEquiv`

```lean
TauCeti.Place.valuation_algEquivOfAlgEquiv.{u_1, u_2, u_3} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {A : Type u_3} [Field A] [Algebra k A]
  (e : ↥P.completionPlace.integers ≃ₐ[k] PowerSeries A) (x : P.Completion) :
  Valued.v ((IsFractionRing.algEquivOfAlgEquiv e) x) = P.completionPlace.valuation x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 240. `TauCeti.Place.completionEquivLaurentSeries_apply_integer`

```lean
TauCeti.Place.completionEquivLaurentSeries_apply_integer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (x : ↥P.completionPlace.integers) :
  (P.completionEquivLaurentSeries hP ht) ↑x =
    (HahnSeries.ofPowerSeries ℤ k) ((P.completionIntegersEquivPowerSeries hP ht) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 241. `TauCeti.Place.completionEquivLaurentSeries_symm_apply_powerSeries`

```lean
TauCeti.Place.completionEquivLaurentSeries_symm_apply_powerSeries.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (f : PowerSeries k) :
  (P.completionEquivLaurentSeries hP ht).symm ((HahnSeries.ofPowerSeries ℤ k) f) =
    ↑((P.completionIntegersEquivPowerSeries hP ht).symm f)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 242. `TauCeti.Place.exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers`

```lean
TauCeti.Place.exists_powerSeries_eq_completionEquivLaurentSeries_iff_mem_integers.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1)
  (ht : P.ord t = 1) (z : P.Completion) :
  (∃ f, (HahnSeries.ofPowerSeries ℤ k) f = (P.completionEquivLaurentSeries hP ht) z) ↔ z ∈ P.completionPlace.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 243. `TauCeti.Place.completionEquivLaurentSeries_uniformizer`

```lean
TauCeti.Place.completionEquivLaurentSeries_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  (P.completionEquivLaurentSeries hP ht) (P.completionEmbedding t) = (HahnSeries.ofPowerSeries ℤ k) PowerSeries.X
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 244. `TauCeti.Place.valuation_completionEquivLaurentSeries`

```lean
TauCeti.Place.valuation_completionEquivLaurentSeries.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (x : P.Completion) :
  Valued.v ((P.completionEquivLaurentSeries hP ht) x) = P.completionPlace.valuation x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 245. `TauCeti.Place.ord_completionEquivLaurentSeries`

```lean
TauCeti.Place.ord_completionEquivLaurentSeries.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (x : P.Completion) :
  (have this := Valued.v;
        this).ord
      ((P.completionEquivLaurentSeries hP ht) x) =
    P.completionPlace.ord x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 246. `TauCeti.Place.completionLaurentCoeff_apply`

```lean
TauCeti.Place.completionLaurentCoeff_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ) (z : P.Completion) :
  (P.completionLaurentCoeff hP ht n) z = ((P.completionEquivLaurentSeries hP ht) z).coeff n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 247. `TauCeti.Place.completionLaurentCoeff_ext_iff`

```lean
TauCeti.Place.completionLaurentCoeff_ext_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {x y : P.Completion} :
  x = y ↔ ∀ (n : ℤ), (P.completionLaurentCoeff hP ht n) x = (P.completionLaurentCoeff hP ht n) y
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 248. `TauCeti.Place.completionLaurentCoeff_completionEquivLaurentSeries_symm_single`

```lean
TauCeti.Place.completionLaurentCoeff_completionEquivLaurentSeries_symm_single.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (m n : ℤ)
  (c : k) :
  (P.completionLaurentCoeff hP ht n) ((P.completionEquivLaurentSeries hP ht).symm ((HahnSeries.single m) c)) =
    if n = m then c else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 249. `TauCeti.Place.completionLaurentCoeff_coe_integer_eq_zero`

```lean
TauCeti.Place.completionLaurentCoeff_coe_integer_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : ↥P.completionPlace.integers)
  {n : ℤ} (hn : n < 0) : (P.completionLaurentCoeff hP ht n) ↑z = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 250. `TauCeti.Place.completionResidue_apply`

```lean
TauCeti.Place.completionResidue_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : P.Completion) :
  (P.completionResidue hP ht) z = ((P.completionEquivLaurentSeries hP ht) z).coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 251. `TauCeti.Place.completionResidue_coe_integer_eq_zero`

```lean
TauCeti.Place.completionResidue_coe_integer_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (z : ↥P.completionPlace.integers) : (P.completionResidue hP ht) ↑z = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 252. `TauCeti.Place.completionResidue_completionEquivLaurentSeries_symm_derivative`

```lean
TauCeti.Place.completionResidue_completionEquivLaurentSeries_symm_derivative.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  (f : LaurentSeries k) :
  (P.completionResidue hP ht) ((P.completionEquivLaurentSeries hP ht).symm ((LaurentSeries.derivative k) f)) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 253. `TauCeti.Place.laurentSeriesExpansion_apply`

```lean
TauCeti.Place.laurentSeriesExpansion_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : F) :
  (P.laurentSeriesExpansion hP ht) z = (P.completionEquivLaurentSeries hP ht) (P.completionEmbedding z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 254. `TauCeti.Place.laurentCoeff_apply`

```lean
TauCeti.Place.laurentCoeff_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ) (z : F) :
  (P.laurentCoeff hP ht n) z = ((P.laurentSeriesExpansion hP ht) z).coeff n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 255. `TauCeti.Place.completionLaurentCoeff_completionEmbedding`

```lean
TauCeti.Place.completionLaurentCoeff_completionEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ) (z : F) :
  (P.completionLaurentCoeff hP ht n) (P.completionEmbedding z) = (P.laurentCoeff hP ht n) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 256. `TauCeti.Place.laurentSeriesExpansion_coe`

```lean
TauCeti.Place.laurentSeriesExpansion_coe.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (x : ↥P.integers) :
  (P.laurentSeriesExpansion hP ht) ↑x = (HahnSeries.ofPowerSeries ℤ k) ((P.powerSeriesExpansion hP ht) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 257. `TauCeti.Place.laurentSeriesExpansion_zpow_uniformizer`

```lean
TauCeti.Place.laurentSeriesExpansion_zpow_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ) :
  (P.laurentSeriesExpansion hP ht) (t ^ n) = (HahnSeries.single n) 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 258. `TauCeti.Place.laurentSeriesExpansion_uniformizer`

```lean
TauCeti.Place.laurentSeriesExpansion_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) :
  (P.laurentSeriesExpansion hP ht) t = (HahnSeries.single 1) 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 259. `TauCeti.Place.valuation_laurentSeriesExpansion`

```lean
TauCeti.Place.valuation_laurentSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : F) :
  Valued.v ((P.laurentSeriesExpansion hP ht) z) = P.valuation z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 260. `TauCeti.Place.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration`

```lean
TauCeti.Place.coeff_laurentSeriesExpansion_eq_zero_of_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {m : ℤ} {z : F}
  (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) : ((P.laurentSeriesExpansion hP ht) z).coeff i = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 261. `TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration`

```lean
TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {m : ℤ} {z w : F}
  (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
  ((P.laurentSeriesExpansion hP ht) z).coeff i = ((P.laurentSeriesExpansion hP ht) w).coeff i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 262. `TauCeti.Place.coeff_laurentSeriesExpansion_sum`

```lean
TauCeti.Place.coeff_laurentSeriesExpansion_sum.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (s : Finset ℤ) (c : ℤ → k)
  (i : ℤ) :
  ((P.laurentSeriesExpansion hP ht) (∑ j ∈ s, (algebraMap k F) (c j) * t ^ j)).coeff i = if i ∈ s then c i else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 263. `TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration`

```lean
TauCeti.Place.coeff_laurentSeriesExpansion_eq_of_sub_sum_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {m : ℤ}
  {z : F} (s : Finset ℤ) (c : ℤ → k) (h : z - ∑ j ∈ s, (algebraMap k F) (c j) * t ^ j ∈ P.filtration m) {i : ℤ}
  (hi : i < m) : ((P.laurentSeriesExpansion hP ht) z).coeff i = if i ∈ s then c i else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 264. `TauCeti.Place.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion`

```lean
TauCeti.Place.coeff_laurentSeriesExpansion_eq_coeff_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ)
  {z : F} (hz : t ^ n * z ∈ P.integers) (i : ℕ) :
  ((P.laurentSeriesExpansion hP ht) z).coeff (↑i - n) =
    (PowerSeries.coeff i) ((P.powerSeriesExpansion hP ht) ⟨t ^ n * z, hz⟩)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 265. `TauCeti.Place.laurentCoeff_ext_iff`

```lean
TauCeti.Place.laurentCoeff_ext_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {x y : F} :
  x = y ↔ ∀ (n : ℤ), (P.laurentCoeff hP ht n) x = (P.laurentCoeff hP ht n) y
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 266. `TauCeti.Place.residue_apply`

```lean
TauCeti.Place.residue_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : F) :
  (P.residue hP ht) z = ((P.laurentSeriesExpansion hP ht) z).coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 267. `TauCeti.Place.completionResidue_completionEmbedding`

```lean
TauCeti.Place.completionResidue_completionEmbedding.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (z : F) :
  (P.completionResidue hP ht) (P.completionEmbedding z) = (P.residue hP ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 268. `TauCeti.Place.residue_eq_zero_of_mem_integers`

```lean
TauCeti.Place.residue_eq_zero_of_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {z : F} (hz : z ∈ P.integers) :
  (P.residue hP ht) z = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 269. `TauCeti.Place.residue_eq_of_sub_mem_integers`

```lean
TauCeti.Place.residue_eq_of_sub_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) {z w : F} (h : z - w ∈ P.integers) :
  (P.residue hP ht) z = (P.residue hP ht) w
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 270. `TauCeti.Place.residue_zpow_uniformizer`

```lean
TauCeti.Place.residue_zpow_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℤ) :
  (P.residue hP ht) (t ^ n) = if n = -1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 271. `TauCeti.Place.residue_inv_uniformizer`

```lean
TauCeti.Place.residue_inv_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) : (P.residue hP ht) t⁻¹ = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 272. `TauCeti.Place.residue_eq_coeff_powerSeriesExpansion`

```lean
TauCeti.Place.residue_eq_coeff_powerSeriesExpansion.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) {z : F}
  (hz : t ^ (n + 1) * z ∈ P.integers) :
  (P.residue hP ht) z = (PowerSeries.coeff n) ((P.powerSeriesExpansion hP ht) ⟨t ^ (n + 1) * z, hz⟩)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 273. `TauCeti.Place.completionEquivLaurentSeriesResidueField_apply_integer`

```lean
TauCeti.Place.completionEquivLaurentSeriesResidueField_apply_integer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : ↥P.completionPlace.integers) :
  (P.completionEquivLaurentSeriesResidueField ht) ↑x =
    (HahnSeries.ofPowerSeries ℤ P.ResidueField) ((P.completionIntegersEquivPowerSeriesResidueField ht) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 274. `TauCeti.Place.exists_powerSeries_eq_completionEquivLaurentSeriesResidueField_iff_mem_integers`

```lean
TauCeti.Place.exists_powerSeries_eq_completionEquivLaurentSeriesResidueField_iff_mem_integers.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (z : P.Completion) :
  (∃ f, (HahnSeries.ofPowerSeries ℤ P.ResidueField) f = (P.completionEquivLaurentSeriesResidueField ht) z) ↔
    z ∈ P.completionPlace.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 275. `TauCeti.Place.completionEquivLaurentSeriesResidueField_uniformizer`

```lean
TauCeti.Place.completionEquivLaurentSeriesResidueField_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) : (P.completionEquivLaurentSeriesResidueField ht) t = (HahnSeries.single 1) 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 276. `TauCeti.Place.completionEquivLaurentSeriesResidueField_completionResidueFieldSection`

```lean
TauCeti.Place.completionEquivLaurentSeriesResidueField_completionResidueFieldSection.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : P.Completion} (ht : P.completionPlace.ord t = 1) (a : P.ResidueField) :
  (P.completionEquivLaurentSeriesResidueField ht) ↑(P.completionResidueFieldSection a) = HahnSeries.C a
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 277. `TauCeti.Place.valuation_completionEquivLaurentSeriesResidueField`

```lean
TauCeti.Place.valuation_completionEquivLaurentSeriesResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : P.Completion}
  (ht : P.completionPlace.ord t = 1) (x : P.Completion) :
  Valued.v ((P.completionEquivLaurentSeriesResidueField ht) x) = P.completionPlace.valuation x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 278. `TauCeti.Place.powerSeriesExpansionResidueField_apply`

```lean
TauCeti.Place.powerSeriesExpansionResidueField_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (x : ↥P.integers) :
  (P.powerSeriesExpansionResidueField ht) x =
    (P.completionIntegersEquivPowerSeriesResidueField ⋯) (P.completionIntegersEmbedding x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 279. `TauCeti.Place.constantCoeff_powerSeriesExpansionResidueField`

```lean
TauCeti.Place.constantCoeff_powerSeriesExpansionResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (x : ↥P.integers) :
  PowerSeries.constantCoeff ((P.powerSeriesExpansionResidueField ht) x) = (IsLocalRing.residue ↥P.integers) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 280. `TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansionResidueField`

```lean
TauCeti.Place.mem_filtration_iff_le_order_powerSeriesExpansionResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F}
  (ht : P.ord t = 1) (n : ℕ) (x : ↥P.integers) :
  ↑x ∈ P.filtration ↑n ↔ ↑n ≤ ((P.powerSeriesExpansionResidueField ht) x).order
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 281. `TauCeti.Place.powerSeriesExpansionResidueField_uniformizer`

```lean
TauCeti.Place.powerSeriesExpansionResidueField_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) :
  (P.powerSeriesExpansionResidueField ht) ⟨t, ⋯⟩ = PowerSeries.X
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 282. `TauCeti.Place.exists_trunc_powerSeriesExpansionResidueField_eq`

```lean
TauCeti.Place.exists_trunc_powerSeriesExpansionResidueField_eq.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (g : PowerSeries P.ResidueField) (n : ℕ) :
  ∃ x, (PowerSeries.trunc n) ((P.powerSeriesExpansionResidueField ht) x) = (PowerSeries.trunc n) g
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 283. `TauCeti.Place.laurentSeriesExpansionResidueField_apply`

```lean
TauCeti.Place.laurentSeriesExpansionResidueField_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (z : F) :
  (P.laurentSeriesExpansionResidueField ht) z = (P.completionEquivLaurentSeriesResidueField ⋯) (P.completionEmbedding z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 284. `TauCeti.Place.laurentSeriesExpansionResidueField_coe`

```lean
TauCeti.Place.laurentSeriesExpansionResidueField_coe.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (x : ↥P.integers) :
  (P.laurentSeriesExpansionResidueField ht) ↑x =
    (HahnSeries.ofPowerSeries ℤ P.ResidueField) ((P.powerSeriesExpansionResidueField ht) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 285. `TauCeti.Place.laurentSeriesExpansionResidueField_zpow_uniformizer`

```lean
TauCeti.Place.laurentSeriesExpansionResidueField_zpow_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (n : ℤ) : (P.laurentSeriesExpansionResidueField ht) (t ^ n) = (HahnSeries.single n) 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 286. `TauCeti.Place.laurentSeriesExpansionResidueField_uniformizer`

```lean
TauCeti.Place.laurentSeriesExpansionResidueField_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) :
  (P.laurentSeriesExpansionResidueField ht) t = (HahnSeries.single 1) 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 287. `TauCeti.Place.valuation_laurentSeriesExpansionResidueField`

```lean
TauCeti.Place.valuation_laurentSeriesExpansionResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (z : F) :
  Valued.v ((P.laurentSeriesExpansionResidueField ht) z) = P.valuation z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 288. `TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration`

```lean
TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_zero_of_mem_filtration.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {t : F} (ht : P.ord t = 1) {m : ℤ} {z : F} (hz : z ∈ P.filtration m) {i : ℤ} (hi : i < m) :
  ((P.laurentSeriesExpansionResidueField ht) z).coeff i = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 289. `TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_of_sub_mem_filtration`

```lean
TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_of_sub_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F}
  (ht : P.ord t = 1) {m : ℤ} {z w : F} (h : z - w ∈ P.filtration m) {i : ℤ} (hi : i < m) :
  ((P.laurentSeriesExpansionResidueField ht) z).coeff i = ((P.laurentSeriesExpansionResidueField ht) w).coeff i
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 290. `TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField`

```lean
TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_coeff_powerSeriesExpansionResidueField.{u_1, u_2}
  {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F)
  [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (n : ℤ) {z : F} (hz : t ^ n * z ∈ P.integers)
  (i : ℕ) :
  ((P.laurentSeriesExpansionResidueField ht) z).coeff (↑i - n) =
    (PowerSeries.coeff i) ((P.powerSeriesExpansionResidueField ht) ⟨t ^ n * z, hz⟩)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 291. `TauCeti.Place.coeff_zero_laurentSeriesExpansionResidueField`

```lean
TauCeti.Place.coeff_zero_laurentSeriesExpansionResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (x : ↥P.integers) : ((P.laurentSeriesExpansionResidueField ht) ↑x).coeff 0 = (IsLocalRing.residue ↥P.integers) x
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 292. `TauCeti.Place.residueResidueField_apply`

```lean
TauCeti.Place.residueResidueField_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (z : F) :
  (P.residueResidueField ht) z = ((P.laurentSeriesExpansionResidueField ht) z).coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 293. `TauCeti.Place.residueResidueField_eq_zero_of_mem_integers`

```lean
TauCeti.Place.residueResidueField_eq_zero_of_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) {z : F}
  (hz : z ∈ P.integers) : (P.residueResidueField ht) z = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 294. `TauCeti.Place.residueResidueField_eq_of_sub_mem_integers`

```lean
TauCeti.Place.residueResidueField_eq_of_sub_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) {z w : F}
  (h : z - w ∈ P.integers) : (P.residueResidueField ht) z = (P.residueResidueField ht) w
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 295. `TauCeti.Place.residueResidueField_zpow_uniformizer`

```lean
TauCeti.Place.residueResidueField_zpow_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (n : ℤ) :
  (P.residueResidueField ht) (t ^ n) = if n = -1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 296. `TauCeti.Place.residueResidueField_inv_uniformizer`

```lean
TauCeti.Place.residueResidueField_inv_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) :
  (P.residueResidueField ht) t⁻¹ = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 297. `TauCeti.Place.residueResidueField_eq_coeff_powerSeriesExpansionResidueField`

```lean
TauCeti.Place.residueResidueField_eq_coeff_powerSeriesExpansionResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F}
  (ht : P.ord t = 1) (n : ℕ) {z : F} (hz : t ^ (n + 1) * z ∈ P.integers) :
  (P.residueResidueField ht) z = (PowerSeries.coeff n) ((P.powerSeriesExpansionResidueField ht) ⟨t ^ (n + 1) * z, hz⟩)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 298. `TauCeti.Place.residueResidueField_mul_inv_uniformizer`

```lean
TauCeti.Place.residueResidueField_mul_inv_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (u : ↥P.integers) : (P.residueResidueField ht) (↑u * t⁻¹) = (IsLocalRing.residue ↥P.integers) u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 299. `TauCeti.Place.traceResidue_apply`

```lean
TauCeti.Place.traceResidue_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (z : F) :
  (P.traceResidue ht) z = (Algebra.trace k P.ResidueField) ((P.residueResidueField ht) z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 300. `TauCeti.Place.traceResidue_mul_inv_uniformizer`

```lean
TauCeti.Place.traceResidue_mul_inv_uniformizer.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (u : ↥P.integers) :
  (P.traceResidue ht) (↑u * t⁻¹) = (Algebra.trace k P.ResidueField) ((IsLocalRing.residue ↥P.integers) u)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 301. `TauCeti.Place.powerSeriesExpansionResidueField_eq_map`

```lean
TauCeti.Place.powerSeriesExpansionResidueField_eq_map.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (hP : P.degree = 1) (x : ↥P.integers) :
  (P.powerSeriesExpansionResidueField ht) x =
    (PowerSeries.map (algebraMap k P.ResidueField)) ((P.powerSeriesExpansion hP ht) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 302. `TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_algebraMap`

```lean
TauCeti.Place.coeff_laurentSeriesExpansionResidueField_eq_algebraMap.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (hP : P.degree = 1) (z : F) (n : ℤ) :
  ((P.laurentSeriesExpansionResidueField ht) z).coeff n =
    (algebraMap k P.ResidueField) (((P.laurentSeriesExpansion hP ht) z).coeff n)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 303. `TauCeti.Place.residueResidueField_eq_algebraMap_residue`

```lean
TauCeti.Place.residueResidueField_eq_algebraMap_residue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1)
  (hP : P.degree = 1) (z : F) : (P.residueResidueField ht) z = (algebraMap k P.ResidueField) ((P.residue hP ht) z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 304. `TauCeti.Place.traceResidue_eq_residue`

```lean
TauCeti.Place.traceResidue_eq_residue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (hP : P.degree = 1)
  (z : F) : (P.traceResidue ht) z = (P.residue hP ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 305. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_infty`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_infty.{u_1} {k : Type u_1} [Field k] (z : RatFunc k) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.infty k)) z =
    -((TauCeti.Place.infty k).residue ⋯ ⋯) (RatFunc.X ^ 2 * z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 306. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.zpow_X_sub_C_mem_integers`

```lean
TauCeti.zpow_X_sub_C_mem_integers.{u_1} {k : Type u_1} [Field k] {a : k} {P : TauCeti.Place k (RatFunc k)}
  (ha : P ≠ TauCeti.Place.adicOfIrreducible ⋯) (hinf : P ≠ TauCeti.Place.infty k) (n : ℤ) :
  (RatFunc.X - RatFunc.C a) ^ n ∈ P.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 307. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.residue_infty_X_sq_mul_X_sub_C_zpow`

```lean
TauCeti.residue_infty_X_sq_mul_X_sub_C_zpow.{u_1} {k : Type u_1} [Field k] (a : k) {n : ℤ} (hn : n < 0) :
  ((TauCeti.Place.infty k).residue ⋯ ⋯) (RatFunc.X ^ 2 * (RatFunc.X - RatFunc.C a) ^ n) = if n = -1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 308. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow.{u_1} {k : Type u_1} [Field k] (a : k) (n : ℤ) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.adicOfIrreducible ⋯))
      ((RatFunc.X - RatFunc.C a) ^ n) =
    if n = -1 then 1 else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 309. `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`

```lean
TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C.{u_1} {k : Type u_1} [Field k]
  (a : k) (z : RatFunc k) :
  (TauCeti.repartitionDualComponent (TauCeti.ratFuncWeilDifferential k) (TauCeti.Place.adicOfIrreducible ⋯)) z =
    ((TauCeti.Place.adicOfIrreducible ⋯).residue ⋯ ⋯) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 310. `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`

```lean
TauCeti.finsum_residue_adicOfIrreducible_X_sub_C.{u_1} {k : Type u_1} [Field k] {z : RatFunc k}
  (hz : ∀ (P : TauCeti.Place k (RatFunc k)), P.degree ≠ 1 → z ∈ P.integers) :
  ∑ᶠ (a : k), ((TauCeti.Place.adicOfIrreducible ⋯).residue ⋯ ⋯) z =
    ((TauCeti.Place.infty k).residue ⋯ ⋯) (RatFunc.X ^ 2 * z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 311. `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed`

```lean
TauCeti.finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed.{u_1} {k : Type u_1} [Field k] [IsAlgClosed k]
  (z : RatFunc k) :
  ∑ᶠ (a : k), ((TauCeti.Place.adicOfIrreducible ⋯).residue ⋯ ⋯) z =
    ((TauCeti.Place.infty k).residue ⋯ ⋯) (RatFunc.X ^ 2 * z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 312. `PowerSeries.trunc_eq_zero_iff_le_order`

```lean
PowerSeries.trunc_eq_zero_iff_le_order.{u_1} {R : Type u_1} [Semiring R] {m : ℕ} {φ : PowerSeries R} :
  (PowerSeries.trunc m) φ = 0 ↔ ↑m ≤ φ.order
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 313. `PowerSeries.coeff_sum_C_mul_X_pow`

```lean
PowerSeries.coeff_sum_C_mul_X_pow.{u_1} {R : Type u_1} [Semiring R] {m : ℕ} (a : Fin m → R) (n : ℕ) :
  (PowerSeries.coeff n) (∑ i, PowerSeries.C (a i) * PowerSeries.X ^ ↑i) = if h : n < m then a ⟨n, h⟩ else 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 314. `TauCeti.Algebra.trace_quotient_map_mk`

```lean
TauCeti.Algebra.trace_quotient_map_mk.{u_1, u_2} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S] (I : Ideal R) (x : S) :
  (Algebra.trace (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) x) =
    (Ideal.Quotient.mk I) ((Algebra.trace R S) x)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 315. `TauCeti.Algebra.trace_mem_of_mem_map`

```lean
TauCeti.Algebra.trace_mem_of_mem_map.{u_1, u_2} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S] {I : Ideal R} {x : S} (hx : x ∈ Ideal.map (algebraMap R S) I) :
  (Algebra.trace R S) x ∈ I
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 316. `TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem`

```lean
TauCeti.Algebra.trace_sub_sum_mem_of_forall_mul_sub_sum_mem.{u_1, u_2, u_3} {R : Type u_1} {S : Type u_2} [CommRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {ι : Type u_3} [Fintype ι] {I : Ideal R} {w z : S}
  {b : ι → S} {a : ι → ι → R} (hwb : ∀ (j : ι), w * b j - b j ∈ Ideal.map (algebraMap R S) I)
  (hspan : ∀ (s : S), ∃ c, w * s - ∑ j, (algebraMap R S) (c j) * b j ∈ Ideal.map (algebraMap R S) I)
  (hindep : ∀ (c : ι → R), ∑ j, (algebraMap R S) (c j) * b j ∈ Ideal.map (algebraMap R S) I → ∀ (j : ι), c j ∈ I)
  (hz : z * w - z ∈ Ideal.map (algebraMap R S) I)
  (hzb : ∀ (j : ι), z * b j - ∑ l, (algebraMap R S) (a j l) * b l ∈ Ideal.map (algebraMap R S) I) :
  (Algebra.trace R S) z - ∑ j, a j j ∈ I
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 317. `TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem`

```lean
TauCeti.Algebra.trace_sub_one_mem_of_mul_self_sub_mem.{u_1, u_2} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S]
  [Algebra R S] [Module.Free R S] [Module.Finite R S] {I : Ideal R} {w : S}
  (hw : w * w - w ∈ Ideal.map (algebraMap R S) I)
  (hspan : ∀ (b : S), ∃ c, w * b - (algebraMap R S) c * w ∈ Ideal.map (algebraMap R S) I)
  (hinj : ∀ (c : R), (algebraMap R S) c * w ∈ Ideal.map (algebraMap R S) I → c ∈ I) : (Algebra.trace R S) w - 1 ∈ I
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 318. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.ord_algebraMap_uniformizer`

```lean
TauCeti.Place.ord_algebraMap_uniformizer.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2} (F : Type u_3)
  {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] (P' : TauCeti.Place k' F')
  {x : F} (hx : (TauCeti.Place.restrict k F P').ord x = 1) :
  P'.ord ((algebraMap F F') x) = ↑(TauCeti.Place.ramificationIdx F P')
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 319. `TauCeti.Place.exists_sub_algebraMap_mem_filtration`

```lean
TauCeti.Place.exists_sub_algebraMap_mem_filtration.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2} (F : Type u_3)
  {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] (P' : TauCeti.Place k' F')
  (he : TauCeti.Place.ramificationIdx F P' = 1) (hf : TauCeti.Place.relativeDegree k F P' = 1) (n : ℕ) {z : F'}
  (hz : z ∈ P'.integers) : ∃ a ∈ (TauCeti.Place.restrict k F P').integers, z - (algebraMap F F') a ∈ P'.filtration ↑n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 320. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.exists_sub_mem_filtration_and_forall_mem_filtration`

```lean
TauCeti.Place.exists_sub_mem_filtration_and_forall_mem_filtration.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2}
  (F : Type u_3) {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F']
  [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  (P' : TauCeti.Place k' F') (y : F') (m : ℕ) :
  ∃ w,
    w - y ∈ P'.filtration (↑(TauCeti.Place.ramificationIdx F P') * ↑m) ∧
      ∀ (Q' : TauCeti.Place k' F'),
        TauCeti.Place.restrict k F Q' = TauCeti.Place.restrict k F P' →
          Q' ≠ P' → w ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * ↑m)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 321. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.mem_span_pow_of_mem_filtration`

```lean
TauCeti.Place.mem_span_pow_of_mem_filtration.{u_1, u_3} {k : Type u_1} {F : Type u_3} [Field k] [Field F] [Algebra k F]
  {P : TauCeti.Place k F} {x : ↥P.integers} (hx : P.ord ↑x = 1) {m : ℕ} {c : ↥P.integers} (hc : ↑c ∈ P.filtration ↑m) :
  c ∈ Ideal.span {x ^ m}
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 322. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.zpow_mem_filtration`

```lean
TauCeti.Place.zpow_mem_filtration.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2} (F : Type u_3) {F' : Type u_4}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] {P : TauCeti.Place k F} {x : F}
  (hx : P.ord x = 1) {Q' : TauCeti.Place k' F'} (hQ' : TauCeti.Place.restrict k F Q' = P) (j : ℤ) :
  (algebraMap F F') x ^ j ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * j)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 323. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.mem_map_span_pow_of_forall_mem_filtration`

```lean
TauCeti.Place.mem_map_span_pow_of_forall_mem_filtration.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2}
  (F : Type u_3) {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F']
  [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsIntegral k k'] (hF' : TauCeti.IsFunctionField k' F') {P : TauCeti.Place k F} {x : ↥P.integers}
  (hx : P.ord ↑x = 1) (m : ℕ) (s : ↥(integralClosure (↥P.integers) F'))
  (hs :
    ∀ (Q' : TauCeti.Place k' F'),
      TauCeti.Place.restrict k F Q' = P → ↑s ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * ↑m)) :
  s ∈ Ideal.map (algebraMap ↥P.integers ↥(integralClosure (↥P.integers) F')) (Ideal.span {x ^ m})
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 324. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.Place.mem_filtration_of_mem_map_span_pow`

```lean
TauCeti.Place.mem_filtration_of_mem_map_span_pow.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2} (F : Type u_3)
  {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsIntegral k k']
  (hF' : TauCeti.IsFunctionField k' F') {P : TauCeti.Place k F} {x : ↥P.integers} (hx : P.ord ↑x = 1) {m : ℕ}
  {s : ↥(integralClosure (↥P.integers) F')}
  (hs : s ∈ Ideal.map (algebraMap ↥P.integers ↥(integralClosure (↥P.integers) F')) (Ideal.span {x ^ m}))
  {Q' : TauCeti.Place k' F'} (hQ' : TauCeti.Place.restrict k F Q' = P) :
  ↑s ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * ↑m)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 325. `TauCeti.Place.algebraMap_trace_sub_mem_filtration`

```lean
TauCeti.Place.algebraMap_trace_sub_mem_filtration.{u_1, u_2, u_3, u_4} (k : Type u_1) {k' : Type u_2} (F : Type u_3)
  {F' : Type u_4} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']
  [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F'] (P' : TauCeti.Place k' F')
  [Algebra.IsIntegral k k'] [Algebra.IsSeparable F F'] (hF' : TauCeti.IsFunctionField k' F')
  (he : TauCeti.Place.ramificationIdx F P' = 1) (hf : TauCeti.Place.relativeDegree k F P' = 1) (m : ℕ) {z : F'}
  (hz : z ∈ P'.integers)
  (hzQ :
    ∀ (Q' : TauCeti.Place k' F'),
      TauCeti.Place.restrict k F Q' = TauCeti.Place.restrict k F P' →
        Q' ≠ P' → z ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * ↑m)) :
  (algebraMap F F') ((Algebra.trace F F') z) - z ∈ P'.filtration ↑m
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 326. `TauCeti.Place.trace_sub_sum_mem_filtration`

```lean
TauCeti.Place.trace_sub_sum_mem_filtration.{u_5, u_6, u_7} {k : Type u_5} {F : Type u_6} {F' : Type u_7} [Field k]
  [Field F] [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] (P' : TauCeti.Place k F') [Algebra.IsSeparable k P'.ResidueField] {P : TauCeti.Place k F}
  (hPP' : TauCeti.Place.restrict k F P' = P) {t : F} (ht : P.ord t = 1) (ht' : P'.ord ((algebraMap F F') t) = 1)
  (hF' : TauCeti.IsFunctionField k F') (hP : P.degree = 1) (m : ℕ) (z : ↥P'.integers)
  (hzQ :
    ∀ (Q' : TauCeti.Place k F'),
      TauCeti.Place.restrict k F Q' = P → Q' ≠ P' → ↑z ∈ Q'.filtration (↑(TauCeti.Place.ramificationIdx F Q') * ↑m)) :
  (Algebra.trace F F') ↑z -
      ∑ i,
        (algebraMap k F)
            ((Algebra.trace k P'.ResidueField) ((PowerSeries.coeff ↑i) ((P'.powerSeriesExpansionResidueField ht') z))) *
          t ^ ↑i ∈
    P.filtration ↑m
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 327. `TauCeti.Place.residue_trace`

```lean
TauCeti.Place.residue_trace.{u_5, u_6, u_7} {k : Type u_5} {F : Type u_6} {F' : Type u_7} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P' : TauCeti.Place k F') [Algebra.IsSeparable k P'.ResidueField] {P : TauCeti.Place k F}
  (hPP' : TauCeti.Place.restrict k F P' = P) {t : F} (ht : P.ord t = 1) (ht' : P'.ord ((algebraMap F F') t) = 1)
  (hF' : TauCeti.IsFunctionField k F') (hP : P.degree = 1) {v : F'}
  (hv : ∀ (Q' : TauCeti.Place k F'), TauCeti.Place.restrict k F Q' = P → Q' ≠ P' → v ∈ Q'.integers) :
  (P.residue hP ht) ((Algebra.trace F F') v) = (P'.traceResidue ht') v
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 328. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.ramificationIdx_eq_one_and_ord_X_sub_C_eq_one`

```lean
TauCeti.ramificationIdx_eq_one_and_ord_X_sub_C_eq_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  {P : TauCeti.Place k F} {a : k} (ht : P.ord ((algebraMap (RatFunc k) F) (RatFunc.X - RatFunc.C a)) = 1) :
  TauCeti.Place.ramificationIdx (RatFunc k) P = 1 ∧
    (TauCeti.Place.restrict k (RatFunc k) P).ord (RatFunc.X - RatFunc.C a) = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 329. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.restrict_eq_adicOfIrreducible_X_sub_C`

```lean
TauCeti.restrict_eq_adicOfIrreducible_X_sub_C.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] {P : TauCeti.Place k F}
  {a : k} (ht : P.ord ((algebraMap (RatFunc k) F) (RatFunc.X - RatFunc.C a)) = 1) :
  TauCeti.Place.restrict k (RatFunc k) P = TauCeti.Place.adicOfIrreducible ⋯
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 330. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.exists_sub_mem_integers_forall_mem_integers`

```lean
TauCeti.exists_sub_mem_integers_forall_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  {P : TauCeti.Place k F} (u : F) :
  ∃ v,
    v - u ∈ P.integers ∧
      ∀ (Q : TauCeti.Place k F),
        TauCeti.Place.restrict k (RatFunc k) Q = TauCeti.Place.restrict k (RatFunc k) P → Q ≠ P → v ∈ Q.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 331. `TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue`

```lean
TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential_eq_traceResidue.{u_1, u_2}
  {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  (hF : TauCeti.IsFunctionField k F) {P : TauCeti.Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
  (ht : P.ord ((algebraMap (RatFunc k) F) (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
  (TauCeti.repartitionDualComponent
        (↑((TauCeti.weilDifferentialCotrace k F ⋯ hF) ⟨TauCeti.ratFuncWeilDifferential k, ⋯⟩)) P)
      u =
    (P.traceResidue ht) u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 332. `TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential`

```lean
TauCeti.repartitionDualComponent_weilDifferentialCotrace_ratFuncWeilDifferential.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F] (hF : TauCeti.IsFunctionField k F)
  {P : TauCeti.Place k F} (hP : P.degree = 1) {a : k}
  (ht : P.ord ((algebraMap (RatFunc k) F) (RatFunc.X - RatFunc.C a)) = 1) (u : F) :
  (TauCeti.repartitionDualComponent
        (↑((TauCeti.weilDifferentialCotrace k F ⋯ hF) ⟨TauCeti.ratFuncWeilDifferential k, ⋯⟩)) P)
      u =
    (P.residue hP ht) u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 333. `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue`

```lean
TauCeti.repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) {t : F} (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] {P : TauCeti.Place k F} [Algebra.IsSeparable k P.ResidueField] {a : k}
  (ht : P.ord (t - (algebraMap k F) a) = 1) (u : F) :
  (TauCeti.repartitionDualComponent (↑(TauCeti.weilDifferentialOfSeparating hF htr)) P) u = (P.traceResidue ht) u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 334. `TauCeti.repartitionDualComponent_weilDifferentialOfSeparating`

```lean
TauCeti.repartitionDualComponent_weilDifferentialOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) {t : F} (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] {P : TauCeti.Place k F} (hP : P.degree = 1) {a : k}
  (ht : P.ord (t - (algebraMap k F) a) = 1) (u : F) :
  (TauCeti.repartitionDualComponent (↑(TauCeti.weilDifferentialOfSeparating hF htr)) P) u = (P.residue hP ht) u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 335. `TauCeti.RatFunc.finrank_adjoin_X_pow`

```lean
TauCeti.RatFunc.finrank_adjoin_X_pow.{u_1} (K : Type u_1) [Field K] (n : ℕ) :
  Module.finrank (↥K⟮RatFunc.X ^ n⟯) (RatFunc K) = n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 336. `TauCeti.relfinrank_adjoin_pow_adjoin`

```lean
TauCeti.relfinrank_adjoin_pow_adjoin.{u_1, u_2} {k : Type u_1} [Field k] {F : Type u_2} [Field F] [Algebra k F] {x : F}
  (hx : Transcendental k x) (n : ℕ) : k⟮x ^ n⟯.relfinrank k⟮x⟯ = n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 337. `Valuation.ord_iterateFrobenius`

```lean
Valuation.ord_iterateFrobenius.{u} {F : Type u} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ))) (p : ℕ)
  [ExpChar F p] (n : ℕ) (z : F) : v.ord ((iterateFrobenius F p n) z) = ↑p ^ n * v.ord z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 338. `Valuation.natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius`

```lean
Valuation.natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius.{u} {F : Type u} [Field F]
  (v : Valuation F (WithZero (Multiplicative ℤ))) (p : ℕ) [ExpChar F p] (n : ℕ) {z : F}
  (hz : z ∈ (iterateFrobenius F p n).fieldRange) : ↑p ^ n ∣ v.ord z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 339. `Valuation.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord`

```lean
Valuation.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord.{u} {F : Type u} [Field F]
  (v : Valuation F (WithZero (Multiplicative ℤ))) (p : ℕ) [ExpChar F p] (n : ℕ) {z : F} (hz : ¬↑p ^ n ∣ v.ord z) :
  z ∉ (iterateFrobenius F p n).fieldRange
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 340. `Valuation.natCast_dvd_ord_pow_sub_pow`

```lean
Valuation.natCast_dvd_ord_pow_sub_pow.{u} {F : Type u} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ))) (p : ℕ)
  [ExpChar F p] (z b : F) : ↑p ∣ v.ord (z ^ p - b ^ p)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 341. `TauCeti.IsFunctionField.finrank_fieldRange_frobenius`

```lean
TauCeti.IsFunctionField.finrank_fieldRange_frobenius.{u, v} {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  [PerfectField k] (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] :
  Module.finrank (↥(frobenius F p).fieldRange) F = p
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 342. `TauCeti.IsFunctionField.D_eq_zero_iff_mem_fieldRange_frobenius`

```lean
TauCeti.IsFunctionField.D_eq_zero_iff_mem_fieldRange_frobenius.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact (Nat.Prime p)] (x : F) :
  (KaehlerDifferential.D k F) x = 0 ↔ x ∈ (frobenius F p).fieldRange
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 343. `TauCeti.IsFunctionField.isSeparable_adjoin_iff_notMem_fieldRange_frobenius`

```lean
TauCeti.IsFunctionField.isSeparable_adjoin_iff_notMem_fieldRange_frobenius.{u, v} {k : Type u} {F : Type v} [Field k]
  [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact (Nat.Prime p)]
  (x : F) : Algebra.IsSeparable (↥k⟮x⟯) F ↔ x ∉ (frobenius F p).fieldRange
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 344. `TauCeti.IsFunctionField.exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable`

```lean
TauCeti.IsFunctionField.exists_pow_eq_and_adjoin_eq_top_of_finrank_prime_of_not_isSeparable.{u, v} {k : Type u}
  {F : Type v} [Field k] [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (p : ℕ)
  [ExpChar F p] {x : F} (hx : Transcendental k x) (hprime : Nat.Prime (Module.finrank (↥k⟮x⟯) F))
  (hsep : ¬Algebra.IsSeparable (↥k⟮x⟯) F) : ∃ y, y ^ p = x ∧ k⟮y⟯ = ⊤
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 345. `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`

```lean
TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_dvd_ord.{u, v} {k : Type u} {F : Type v} [Field k]
  [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F)
  (v : Valuation F (WithZero (Multiplicative ℤ))) (p : ℕ) [ExpChar F p] {x : F} (hx : ¬↑p ∣ v.ord x) :
  Transcendental k x ∧ Algebra.IsSeparable (↥k⟮x⟯) F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 346. `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`

```lean
TauCeti.Place.transcendental_and_isSeparable_adjoin_of_not_dvd_ord.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (P : TauCeti.Place k F) {x : F}
  (hx : ¬↑(ringChar F) ∣ P.ord x) : Transcendental k x ∧ Algebra.IsSeparable (↥k⟮x⟯) F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 347. `TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one`

```lean
TauCeti.Place.transcendental_and_isSeparable_adjoin_of_ord_eq_one.{u, v} {k : Type u} {F : Type v} [Field k] [Field F]
  [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) :
  Transcendental k t ∧ Algebra.IsSeparable (↥k⟮t⟯) F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 348. `TauCeti.hahnSeries_leadingCoeff_pow`

```lean
TauCeti.hahnSeries_leadingCoeff_pow.{u_1, u_2} {Γ : Type u_1} {R : Type u_2} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Semiring R] [NoZeroDivisors R] (n : ℕ) {f : HahnSeries Γ R} :
  (f ^ n).leadingCoeff = f.leadingCoeff ^ n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 349. `TauCeti.hahnSeries_orderTop_pow`

```lean
TauCeti.hahnSeries_orderTop_pow.{u_1, u_2} {Γ : Type u_1} {R : Type u_2} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Semiring R] [NoZeroDivisors R] [Nontrivial R] (n : ℕ) {f : HahnSeries Γ R} :
  (f ^ n).orderTop = n • f.orderTop
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 350. `TauCeti.laurentSeriesDerivation_apply`

```lean
TauCeti.laurentSeriesDerivation_apply.{u_1} (R : Type u_1) [CommRing R] (f : LaurentSeries R) :
  (TauCeti.laurentSeriesDerivation R) f = (LaurentSeries.derivative R) f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 351. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.Derivation.laurentSeries_module_eq_algebraModule`

```lean
Derivation.laurentSeries_module_eq_algebraModule.{u_1} {R : Type u_1} [CommRing R] : inferInstance = Algebra.toModule
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 352. `Derivation.laurentSeries_commutator_apply`

```lean
Derivation.laurentSeries_commutator_apply.{u_1} {R : Type u_1} [CommRing R]
  (δ ε : Derivation R (LaurentSeries R) (LaurentSeries R)) (f : LaurentSeries R) : ⁅δ, ε⁆ f = δ (ε f) - ε (δ f)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 353. `LaurentSeries.lie_smul_laurentSeriesDerivation`

```lean
LaurentSeries.lie_smul_laurentSeriesDerivation.{u_1} {R : Type u_1} [CommRing R] (a b : LaurentSeries R) :
  ⁅a • TauCeti.laurentSeriesDerivation R, b • TauCeti.laurentSeriesDerivation R⁆ =
    (a * (TauCeti.laurentSeriesDerivation R) b - b * (TauCeti.laurentSeriesDerivation R) a) •
      TauCeti.laurentSeriesDerivation R
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 354. `LaurentSeries.coeff_derivative`

```lean
LaurentSeries.coeff_derivative.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V] [Module R V]
  (f : LaurentSeries V) (n : ℤ) : ((LaurentSeries.derivative R) f).coeff n = (n + 1) • f.coeff (n + 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 355. `LaurentSeries.coeff_derivative_sub_one`

```lean
LaurentSeries.coeff_derivative_sub_one.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V]
  [Module R V] (f : LaurentSeries V) (n : ℤ) : ((LaurentSeries.derivative R) f).coeff (n - 1) = n • f.coeff n
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 356. `LaurentSeries.coeff_derivative_order_sub_one`

```lean
LaurentSeries.coeff_derivative_order_sub_one.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V]
  [Module R V] (f : LaurentSeries V) :
  ((LaurentSeries.derivative R) f).coeff (HahnSeries.order f - 1) = HahnSeries.order f • HahnSeries.leadingCoeff f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 357. `LaurentSeries.orderTop_le_orderTop_derivative_add_one`

```lean
LaurentSeries.orderTop_le_orderTop_derivative_add_one.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R]
  [AddCommGroup V] [Module R V] (f : LaurentSeries V) :
  HahnSeries.orderTop f ≤ HahnSeries.orderTop ((LaurentSeries.derivative R) f) + 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 358. `LaurentSeries.orderTop_derivative_eq_sub_one`

```lean
LaurentSeries.orderTop_derivative_eq_sub_one.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V]
  [Module R V] {f : LaurentSeries V} {n : ℤ} (hn : n • f.coeff n ≠ 0) (hlt : ∀ m < n, m • f.coeff m = 0) :
  HahnSeries.orderTop ((LaurentSeries.derivative R) f) = ↑(n - 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 359. `LaurentSeries.orderTop_derivative_eq_order_sub_one`

```lean
LaurentSeries.orderTop_derivative_eq_order_sub_one.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R]
  [AddCommGroup V] [Module R V] {f : LaurentSeries V} (h : HahnSeries.order f • HahnSeries.leadingCoeff f ≠ 0) :
  HahnSeries.orderTop ((LaurentSeries.derivative R) f) = ↑(HahnSeries.order f - 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 360. `LaurentSeries.derivative_eq_zero_iff`

```lean
LaurentSeries.derivative_eq_zero_iff.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V] [Module R V]
  {f : LaurentSeries V} : (LaurentSeries.derivative R) f = 0 ↔ ∀ (n : ℤ), n • f.coeff n = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 361. `LaurentSeries.derivative_eq_zero_iff_eq_single`

```lean
LaurentSeries.derivative_eq_zero_iff_eq_single.{u_1, u_2} {R : Type u_1} {V : Type u_2} [Semiring R] [AddCommGroup V]
  [Module R V] [IsAddTorsionFree V] {f : LaurentSeries V} :
  (LaurentSeries.derivative R) f = 0 ↔ f = (HahnSeries.single 0) (f.coeff 0)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 362. `LaurentSeries.orderTop_derivative_eq_order_sub_one_of_cast_ne_zero`

```lean
LaurentSeries.orderTop_derivative_eq_order_sub_one_of_cast_ne_zero.{u_1} {R : Type u_1} [Ring R] [NoZeroDivisors R]
  {f : LaurentSeries R} (hf : f ≠ 0) (h : ↑(HahnSeries.order f) ≠ 0) :
  HahnSeries.orderTop ((LaurentSeries.derivative R) f) = ↑(HahnSeries.order f - 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 363. `LaurentSeries.derivative_eq_zero_iff_exists_C`

```lean
LaurentSeries.derivative_eq_zero_iff_exists_C.{u_1} {R : Type u_1} [Ring R] [IsAddTorsionFree R] {f : LaurentSeries R} :
  (LaurentSeries.derivative R) f = 0 ↔ ∃ c, HahnSeries.C c = f
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 364. `LaurentSeries.derivative_inv`

```lean
LaurentSeries.derivative_inv.{u_1} {K : Type u_1} [Field K] (f : LaurentSeries K) :
  (LaurentSeries.derivative K) f⁻¹ = -(f⁻¹ ^ 2 * (LaurentSeries.derivative K) f)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 365. `LaurentSeries.derivative_div`

```lean
LaurentSeries.derivative_div.{u_1} {K : Type u_1} [Field K] (f g : LaurentSeries K) :
  (LaurentSeries.derivative K) (f / g) =
    ((LaurentSeries.derivative K) f * g - f * (LaurentSeries.derivative K) g) / g ^ 2
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 366. `LaurentSeries.valuation_derivative_le`

```lean
LaurentSeries.valuation_derivative_le.{u_1} {K : Type u_1} [Field K] {m : ℤ} {f : LaurentSeries K}
  (hf : Valued.v f ≤ WithZero.exp (-m)) : Valued.v ((LaurentSeries.derivative K) f) ≤ WithZero.exp (-(m - 1))
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 367. `LaurentSeries.continuous_derivative`

```lean
LaurentSeries.continuous_derivative.{u_1} {K : Type u_1} [Field K] : Continuous ⇑(LaurentSeries.derivative K)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 368. `TauCeti.Place.residue_eq_coeff_laurentSeriesExpansion_mul_derivative`

```lean
TauCeti.Place.residue_eq_coeff_laurentSeriesExpansion_mul_derivative.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (hs : P.ord s = 1)
  (z : F) :
  (P.residue hP hs) z =
    ((P.laurentSeriesExpansion hP ht) z * (LaurentSeries.derivative k) ((P.laurentSeriesExpansion hP ht) s)).coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 369. `TauCeti.Place.residue_eq_residue_mul`

```lean
TauCeti.Place.residue_eq_residue_mul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (hs : P.ord s = 1) {w : F}
  (hw : (P.laurentSeriesExpansion hP ht) w = (LaurentSeries.derivative k) ((P.laurentSeriesExpansion hP ht) s))
  (z : F) : (P.residue hP hs) z = (P.residue hP ht) (z * w)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 370. `TauCeti.Place.coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative`

```lean
TauCeti.Place.coeff_neg_one_completionEquivLaurentSeriesResidueField_mul_derivative.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) [Algebra.IsSeparable k P.ResidueField]
  {s t : P.Completion} (hs : P.completionPlace.ord s = 1) (ht : P.completionPlace.ord t = 1) (z : P.Completion) :
  ((P.completionEquivLaurentSeriesResidueField ht) z *
          (LaurentSeries.derivative P.ResidueField) ((P.completionEquivLaurentSeriesResidueField ht) s)).coeff
      (-1) =
    ((P.completionEquivLaurentSeriesResidueField hs) z).coeff (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 371. `TauCeti.Place.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative`

```lean
TauCeti.Place.residueResidueField_eq_coeff_laurentSeriesExpansionResidueField_mul_derivative.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1)
  [Algebra.IsSeparable k P.ResidueField] (hs : P.ord s = 1) (z : F) :
  (P.residueResidueField hs) z =
    ((P.laurentSeriesExpansionResidueField ht) z *
          (LaurentSeries.derivative P.ResidueField) ((P.laurentSeriesExpansionResidueField ht) s)).coeff
      (-1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 372. `TauCeti.Place.residueResidueField_eq_residueResidueField_mul`

```lean
TauCeti.Place.residueResidueField_eq_residueResidueField_mul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (hs : P.ord s = 1) {w : F}
  (hw :
    (P.laurentSeriesExpansionResidueField ht) w =
      (LaurentSeries.derivative P.ResidueField) ((P.laurentSeriesExpansionResidueField ht) s))
  (z : F) : (P.residueResidueField hs) z = (P.residueResidueField ht) (z * w)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 373. `TauCeti.Place.traceResidue_eq_traceResidue_mul`

```lean
TauCeti.Place.traceResidue_eq_traceResidue_mul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (hs : P.ord s = 1) {w : F}
  (hw :
    (P.laurentSeriesExpansionResidueField ht) w =
      (LaurentSeries.derivative P.ResidueField) ((P.laurentSeriesExpansionResidueField ht) s))
  (z : F) : (P.traceResidue hs) z = (P.traceResidue ht) (z * w)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 374. `TauCeti.algHom_derivativeOfSeparating`

```lean
TauCeti.algHom_derivativeOfSeparating.{u_1, u_2, u_3} {k : Type u_1} {F : Type u_2} {A : Type u_3} [Field k] [Field F]
  [Algebra k F] [CommRing A] [Algebra k A] {t : F} (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F]
  {e : F →ₐ[k] LaurentSeries A} (he : e t = (HahnSeries.single 1) 1) (z : F) :
  e ((TauCeti.derivativeOfSeparating htr) z) = (LaurentSeries.derivative A) (e z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 375. `TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating`

```lean
TauCeti.Place.laurentSeriesExpansion_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (z : F) :
  (P.laurentSeriesExpansion hP ht) ((TauCeti.derivativeOfSeparating htr) z) =
    (LaurentSeries.derivative k) ((P.laurentSeriesExpansion hP ht) z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 376. `TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating`

```lean
TauCeti.Place.residue_eq_residue_mul_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1) (z : F) :
  (P.residue hP hs) z = (P.residue hP ht) (z * (TauCeti.derivativeOfSeparating htr) s)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 377. `TauCeti.Place.residue_derivativeOfSeparating`

```lean
TauCeti.Place.residue_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) : (P.residue hP ht) ((TauCeti.derivativeOfSeparating htr) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 378. `TauCeti.Place.laurentSeriesExpansionResidueField_derivativeOfSeparating`

```lean
TauCeti.Place.laurentSeriesExpansionResidueField_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1)
  [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (z : F) :
  (P.laurentSeriesExpansionResidueField ht) ((TauCeti.derivativeOfSeparating htr) z) =
    (LaurentSeries.derivative P.ResidueField) ((P.laurentSeriesExpansionResidueField ht) z)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 379. `TauCeti.Place.derivativeOfSeparating_sub_zsmul_mem_filtration`

```lean
TauCeti.Place.derivativeOfSeparating_sub_zsmul_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] {m : ℤ} {z : F} (hz : z ∈ P.filtration m) :
  (TauCeti.derivativeOfSeparating htr) z - m • (t⁻¹ * z) ∈ P.filtration m
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 380. `TauCeti.Place.derivativeOfSeparating_mem_integers`

```lean
TauCeti.Place.derivativeOfSeparating_mem_integers.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] {z : F} (hz : z ∈ P.integers) :
  (TauCeti.derivativeOfSeparating htr) z ∈ P.integers
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 381. `TauCeti.Place.derivativeOfSeparating_mem_filtration`

```lean
TauCeti.Place.derivativeOfSeparating_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] {m : ℤ} {z : F} (hz : z ∈ P.filtration m) :
  (TauCeti.derivativeOfSeparating htr) z ∈ P.filtration (m - 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 382. `TauCeti.Place.iterate_derivativeOfSeparating_mem_filtration`

```lean
TauCeti.Place.iterate_derivativeOfSeparating_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] {m : ℤ} {z : F} (hz : z ∈ P.filtration m) (i : ℕ) :
  (⇑(TauCeti.derivativeOfSeparating htr))^[i] z ∈ P.filtration (m - ↑i)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 383. `TauCeti.Place.iterate_derivativeOfSeparating_sub_zsmul_mem_filtration`

```lean
TauCeti.Place.iterate_derivativeOfSeparating_sub_zsmul_mem_filtration.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] {m : ℤ} {z : F} (hz : z ∈ P.filtration m) (i : ℕ) :
  (⇑(TauCeti.derivativeOfSeparating htr))^[i] z - Polynomial.eval m (descPochhammer ℤ i) • (t⁻¹ ^ i * z) ∈
    P.filtration (m - ↑i + 1)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 384. `TauCeti.Place.kaehlerResidue_apply`

```lean
TauCeti.Place.kaehlerResidue_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) :
  (P.kaehlerResidue hP ht htr) ω = (P.residue hP ht) (((TauCeti.kaehlerBasisOfSeparating htr).coord ()) ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 385. `TauCeti.Place.kaehlerResidue_smul_D`

```lean
TauCeti.Place.kaehlerResidue_smul_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (z : F) :
  (P.kaehlerResidue hP ht htr) (z • (KaehlerDifferential.D k F) t) = (P.residue hP ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 386. `TauCeti.Place.kaehlerResidue_D`

```lean
TauCeti.Place.kaehlerResidue_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) : (P.kaehlerResidue hP ht htr) ((KaehlerDifferential.D k F) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 387. `TauCeti.Place.kaehlerResidue_eq_kaehlerResidue`

```lean
TauCeti.Place.kaehlerResidue_eq_kaehlerResidue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {s t : F} (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1) (hstr : Transcendental k s) [Algebra.IsSeparable (↥k⟮s⟯) F] :
  P.kaehlerResidue hP hs hstr = P.kaehlerResidue hP ht htr
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 388. `TauCeti.Place.kaehlerResidueOfPerfectField_eq_kaehlerResidue`

```lean
TauCeti.Place.kaehlerResidueOfPerfectField_eq_kaehlerResidue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [PerfectField k]
  (hF : TauCeti.IsFunctionField k F) (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] :
  P.kaehlerResidueOfPerfectField hP hF = P.kaehlerResidue hP ht htr
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 389. `TauCeti.Place.kaehlerResidueOfPerfectField_smul_D`

```lean
TauCeti.Place.kaehlerResidueOfPerfectField_smul_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1) [PerfectField k]
  (hF : TauCeti.IsFunctionField k F) (z : F) :
  (P.kaehlerResidueOfPerfectField hP hF) (z • (KaehlerDifferential.D k F) t) = (P.residue hP ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 390. `TauCeti.Place.kaehlerResidueOfPerfectField_D`

```lean
TauCeti.Place.kaehlerResidueOfPerfectField_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) (hP : P.degree = 1) [PerfectField k] (hF : TauCeti.IsFunctionField k F) (y : F) :
  (P.kaehlerResidueOfPerfectField hP hF) ((KaehlerDifferential.D k F) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 391. `TauCeti.Place.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating`

```lean
TauCeti.Place.residueResidueField_eq_residueResidueField_mul_derivativeOfSeparating.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1)
  [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1)
  (z : F) : (P.residueResidueField hs) z = (P.residueResidueField ht) (z * (TauCeti.derivativeOfSeparating htr) s)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 392. `TauCeti.Place.traceResidue_eq_traceResidue_mul_derivativeOfSeparating`

```lean
TauCeti.Place.traceResidue_eq_traceResidue_mul_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1) (z : F) :
  (P.traceResidue hs) z = (P.traceResidue ht) (z * (TauCeti.derivativeOfSeparating htr) s)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 393. `TauCeti.Place.residueResidueField_derivativeOfSeparating`

```lean
TauCeti.Place.residueResidueField_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) :
  (P.residueResidueField ht) ((TauCeti.derivativeOfSeparating htr) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 394. `TauCeti.Place.traceResidue_derivativeOfSeparating`

```lean
TauCeti.Place.traceResidue_derivativeOfSeparating.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) :
  (P.traceResidue ht) ((TauCeti.derivativeOfSeparating htr) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 395. `TauCeti.Place.kaehlerResidueResidueField_apply`

```lean
TauCeti.Place.kaehlerResidueResidueField_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) :
  (P.kaehlerResidueResidueField ht htr) ω =
    (P.residueResidueField ht) (((TauCeti.kaehlerBasisOfSeparating htr).coord ()) ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 396. `TauCeti.Place.kaehlerResidueResidueField_smul_D`

```lean
TauCeti.Place.kaehlerResidueResidueField_smul_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (z : F) :
  (P.kaehlerResidueResidueField ht htr) (z • (KaehlerDifferential.D k F) t) = (P.residueResidueField ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 397. `TauCeti.Place.kaehlerResidueResidueField_D`

```lean
TauCeti.Place.kaehlerResidueResidueField_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) : (P.kaehlerResidueResidueField ht htr) ((KaehlerDifferential.D k F) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 398. `TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField`

```lean
TauCeti.Place.kaehlerResidueResidueField_eq_kaehlerResidueResidueField.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1)
  [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1)
  (hstr : Transcendental k s) [Algebra.IsSeparable (↥k⟮s⟯) F] :
  P.kaehlerResidueResidueField hs hstr = P.kaehlerResidueResidueField ht htr
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 399. `TauCeti.Place.kaehlerTraceResidue_apply`

```lean
TauCeti.Place.kaehlerTraceResidue_apply.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) :
  (P.kaehlerTraceResidue ht htr) ω = (Algebra.trace k P.ResidueField) ((P.kaehlerResidueResidueField ht htr) ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 400. `TauCeti.Place.kaehlerTraceResidue_smul_D`

```lean
TauCeti.Place.kaehlerTraceResidue_smul_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (z : F) :
  (P.kaehlerTraceResidue ht htr) (z • (KaehlerDifferential.D k F) t) = (P.traceResidue ht) z
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 401. `TauCeti.Place.kaehlerTraceResidue_D`

```lean
TauCeti.Place.kaehlerTraceResidue_D.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (P : TauCeti.Place k F) {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (y : F) : (P.kaehlerTraceResidue ht htr) ((KaehlerDifferential.D k F) y) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 402. `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue`

```lean
TauCeti.Place.kaehlerTraceResidue_eq_kaehlerTraceResidue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {s t : F} (ht : P.ord t = 1) [Algebra.IsSeparable k P.ResidueField]
  (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (hs : P.ord s = 1) (hstr : Transcendental k s)
  [Algebra.IsSeparable (↥k⟮s⟯) F] : P.kaehlerTraceResidue hs hstr = P.kaehlerTraceResidue ht htr
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 403. `TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue`

```lean
TauCeti.Place.kaehlerTraceResidue_eq_kaehlerResidue.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)
  [Algebra.IsSeparable k P.ResidueField] (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] :
  P.kaehlerTraceResidue ht htr = P.kaehlerResidue hP ht htr
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 404. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.exists_repartitionDualComponent_ne_zero`

```lean
TauCeti.exists_repartitionDualComponent_ne_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (P : TauCeti.Place k F) :
  ∃ ω ∈ TauCeti.weilDifferentialSpace k F, TauCeti.repartitionDualComponent ω P ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 405. `TauCeti.repartitionDualComponent_ne_zero`

```lean
TauCeti.repartitionDualComponent_ne_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {ω : Module.Dual k ↥(TauCeti.repartitionSpace k F)} (hω : ω ∈ TauCeti.weilDifferentialSpace k F) (hω0 : ω ≠ 0)
  (P : TauCeti.Place k F) : TauCeti.repartitionDualComponent ω P ≠ 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 406. `TauCeti.repartitionDualComponent_eq_zero_iff`

```lean
TauCeti.repartitionDualComponent_eq_zero_iff.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {ω : Module.Dual k ↥(TauCeti.repartitionSpace k F)} (hω : ω ∈ TauCeti.weilDifferentialSpace k F)
  (P : TauCeti.Place k F) : TauCeti.repartitionDualComponent ω P = 0 ↔ ω = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 407. `TauCeti.repartitionDualComponent_inj`

```lean
TauCeti.repartitionDualComponent_inj.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {ω η : Module.Dual k ↥(TauCeti.repartitionSpace k F)} (hω : ω ∈ TauCeti.weilDifferentialSpace k F)
  (hη : η ∈ TauCeti.weilDifferentialSpace k F) (P : TauCeti.Place k F) :
  TauCeti.repartitionDualComponent ω P = TauCeti.repartitionDualComponent η P ↔ ω = η
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 408. `TauCeti.repartitionDualComponent_eq_traceResidue_coord`

```lean
TauCeti.repartitionDualComponent_eq_traceResidue_coord.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {P : TauCeti.Place k F}
  [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) [Algebra.IsSeparable (↥k⟮t⟯) F]
  (ω : ↥(TauCeti.weilDifferentialSpace k F)) (u : F) :
  have htr := ⋯;
  (TauCeti.repartitionDualComponent (↑ω) P) u =
    (P.traceResidue ht) (((TauCeti.weilDifferentialBasisOfSeparating hF hex htr).coord ()) ω * u)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 409. `TauCeti.finite_support_traceResidue_coord`

```lean
TauCeti.finite_support_traceResidue_coord.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ (P : TauCeti.Place k F), Algebra.IsSeparable k P.ResidueField] (t : TauCeti.Place k F → F)
  (ht : ∀ (P : TauCeti.Place k F), P.ord (t P) = 1) [∀ (P : TauCeti.Place k F), Algebra.IsSeparable (↥k⟮t P⟯) F]
  (ω : ↥(TauCeti.weilDifferentialSpace k F)) (a : ↥(TauCeti.repartitionSpace k F)) :
  have htr := ⋯;
  (Function.support fun P =>
      (P.traceResidue ⋯) (((TauCeti.weilDifferentialBasisOfSeparating hF hex ⋯).coord ()) ω * ↑a P)).Finite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 410. `TauCeti.finsum_traceResidue_coord_eq_zero`

```lean
TauCeti.finsum_traceResidue_coord_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F]
  (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ (P : TauCeti.Place k F), Algebra.IsSeparable k P.ResidueField] (t : TauCeti.Place k F → F)
  (ht : ∀ (P : TauCeti.Place k F), P.ord (t P) = 1) [∀ (P : TauCeti.Place k F), Algebra.IsSeparable (↥k⟮t P⟯) F]
  (ω : ↥(TauCeti.weilDifferentialSpace k F)) (u : F) :
  have htr := ⋯;
  ∑ᶠ (P : TauCeti.Place k F),
      (P.traceResidue ⋯) (((TauCeti.weilDifferentialBasisOfSeparating hF hex ⋯).coord ()) ω * u) =
    0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 411. `TauCeti.Place.isIntegrallyClosedIn_of_degree_eq_one`

```lean
TauCeti.Place.isIntegrallyClosedIn_of_degree_eq_one.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (hP : P.degree = 1) : IsIntegrallyClosedIn k F
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 412. `TauCeti.Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one`

```lean
TauCeti.Place.exists_ord_sub_algebraMap_eq_one_of_ord_aeval_eq_one.{u, u', v, v'} {k : Type u} {k' : Type u'}
  {F : Type v} {F' : Type v'} [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
  [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  {P' : TauCeti.Place k' F'} (hdeg : P'.degree = 1) (he : TauCeti.Place.ramificationIdx F P' = 1) {z : F}
  (hz : 0 ≤ (TauCeti.Place.restrict k F P').ord z) {q : Polynomial k} (hq : q.Separable)
  (hqz : (TauCeti.Place.restrict k F P').ord ((Polynomial.aeval z) q) = 1) :
  ∃ a, P'.ord ((algebraMap F F') z - (algebraMap k' F') a) = 1
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 413. `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one`

```lean
TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_ord_eq_one.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {x y : F} (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] (hy : Transcendental k y)
  [Algebra.IsSeparable (↥k⟮y⟯) F] {P : TauCeti.Place k F} (hP : P.degree = 1) {a b : k}
  (hxa : P.ord (x - (algebraMap k F) a) = 1) (hyb : P.ord (y - (algebraMap k F) b) = 1) :
  TauCeti.weilDifferentialOfSeparating hF hy =
    (TauCeti.derivativeOfSeparating hx) y • TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 414. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum`

```lean
TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul_of_constantCompositum.{u_1, u_2, u_3, u_4}
  {k : Type u_1} {F : Type u_2} [Field k] [Field F] [Algebra k F] {k' : Type u_3} {F' : Type u_4} [Field k'] [Field F']
  [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [FiniteDimensional F F']
  (h : TauCeti.constantCompositum F k' F' = ⊤) (hF : TauCeti.IsFunctionField k F) {x y : F} (hx : Transcendental k x)
  [Algebra.IsSeparable (↥k⟮x⟯) F] (hy : Transcendental k y) [Algebra.IsSeparable (↥k⟮y⟯) F] {P' : TauCeti.Place k' F'}
  (hdeg : P'.degree = 1) (hx0 : 0 ≤ (TauCeti.Place.restrict k F P').ord x)
  (hy0 : 0 ≤ (TauCeti.Place.restrict k F P').ord y) {q r : Polynomial k} (hq : q.Separable) (hr : r.Separable)
  (hqx : (TauCeti.Place.restrict k F P').ord ((Polynomial.aeval x) q) = 1)
  (hry : (TauCeti.Place.restrict k F P').ord ((Polynomial.aeval y) r) = 1) :
  TauCeti.weilDifferentialOfSeparating hF hy =
    (TauCeti.derivativeOfSeparating hx) y • TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 415. `TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`

```lean
TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
  (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] (hy : Transcendental k y) [Algebra.IsSeparable (↥k⟮y⟯) F] :
  TauCeti.weilDifferentialOfSeparating hF hy =
    (TauCeti.derivativeOfSeparating hx) y • TauCeti.weilDifferentialOfSeparating hF hx
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 416. `TauCeti.Place.ord_derivativeOfSeparating_eq_sub`

```lean
TauCeti.Place.ord_derivativeOfSeparating_eq_sub.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] (P : TauCeti.Place k F) (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
  (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] (hy : Transcendental k y) [Algebra.IsSeparable (↥k⟮y⟯) F] :
  P.ord ((TauCeti.derivativeOfSeparating hx) y) =
    TauCeti.weilDifferentialOrder hF hex ⋯ ⋯ P - TauCeti.weilDifferentialOrder hF hex ⋯ ⋯ P
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 417. `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq`

```lean
TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x y : F}
  (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] (hy : Transcendental k y) [Algebra.IsSeparable (↥k⟮y⟯) F] :
  TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx =
    TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hy
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 418. `TauCeti.Place.traceResidue_coord_smul_eq_repartitionDualComponent`

```lean
TauCeti.Place.traceResidue_coord_smul_eq_repartitionDualComponent.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
  (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] {P : TauCeti.Place k F}
  [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) (u : F) :
  (P.traceResidue ht) (((TauCeti.kaehlerBasisOfSeparating htr).coord ()) (u • ω)) =
    (TauCeti.repartitionDualComponent (↑((TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ω)) P)
      u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 419. `TauCeti.Place.kaehlerResidue_eq_traceResidue_coord`

```lean
TauCeti.Place.kaehlerResidue_eq_traceResidue_coord.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] {P : TauCeti.Place k F} (hP : P.degree = 1) [Algebra.IsSeparable k P.ResidueField] {t : F}
  (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) :
  (P.kaehlerResidue hP ht htr) ω = (P.traceResidue ht) (((TauCeti.kaehlerBasisOfSeparating htr).coord ()) ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 420. `TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating`

```lean
TauCeti.repartitionDualComponent_kaehlerDifferentialEquivWeilDifferentialOfSeparating.{u_1, u_2} {k : Type u_1}
  {F : Type u_2} [Field k] [Field F] [Algebra k F] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] {P : TauCeti.Place k F} (hP : P.degree = 1) {t : F}
  (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) (u : F) :
  (TauCeti.repartitionDualComponent (↑((TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ω)) P)
      u =
    (P.kaehlerResidue hP ht htr) (u • ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 421. `TauCeti.Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord`

```lean
TauCeti.Place.kaehlerResidueOfPerfectField_eq_traceResidue_coord.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) {P : TauCeti.Place k F}
  (hP : P.degree = 1) [Algebra.IsSeparable k P.ResidueField] {t : F} (ht : P.ord t = 1) (htr : Transcendental k t)
  [Algebra.IsSeparable (↥k⟮t⟯) F] (ω : Ω[F⁄k]) :
  (P.kaehlerResidueOfPerfectField hP hF) ω = (P.traceResidue ht) (((TauCeti.kaehlerBasisOfSeparating htr).coord ()) ω)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 422. `TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent`

```lean
TauCeti.Place.kaehlerResidueOfPerfectField_smul_eq_repartitionDualComponent.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable (↥k⟮x⟯) F] {P : TauCeti.Place k F} (hP : P.degree = 1)
  (ω : Ω[F⁄k]) (u : F) :
  (P.kaehlerResidueOfPerfectField hP hF) (u • ω) =
    (TauCeti.repartitionDualComponent (↑((TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx) ω)) P)
      u
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 423. `TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord`

```lean
TauCeti.finite_support_traceResidue_kaehlerBasisOfSeparating_coord.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ (P : TauCeti.Place k F), Algebra.IsSeparable k P.ResidueField] (t : TauCeti.Place k F → F)
  (ht : ∀ (P : TauCeti.Place k F), P.ord (t P) = 1) [∀ (P : TauCeti.Place k F), Algebra.IsSeparable (↥k⟮t P⟯) F]
  (ω : Ω[F⁄k]) :
  have htr := ⋯;
  (Function.support fun P => (P.traceResidue ⋯) (((TauCeti.kaehlerBasisOfSeparating ⋯).coord ()) ω)).Finite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 424. `TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero`

```lean
TauCeti.finsum_traceResidue_kaehlerBasisOfSeparating_coord_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k]
  [Field F] [Algebra k F] [PerfectField k] (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
  [∀ (P : TauCeti.Place k F), Algebra.IsSeparable k P.ResidueField] (t : TauCeti.Place k F → F)
  (ht : ∀ (P : TauCeti.Place k F), P.ord (t P) = 1) [∀ (P : TauCeti.Place k F), Algebra.IsSeparable (↥k⟮t P⟯) F]
  (ω : Ω[F⁄k]) :
  have htr := ⋯;
  ∑ᶠ (P : TauCeti.Place k F), (P.traceResidue ⋯) (((TauCeti.kaehlerBasisOfSeparating ⋯).coord ()) ω) = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 425. `_private.ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonAudit.0.TauCeti.finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero`

```lean
TauCeti.finite_support_and_finsum_kaehlerResidueOfPerfectField_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2}
  [Field k] [Field F] [Algebra k F] [IsAlgClosed k] (hF : TauCeti.IsFunctionField k F) (ω : Ω[F⁄k]) :
  (Function.support fun P => (P.kaehlerResidueOfPerfectField ⋯ hF) ω).Finite ∧
    ∑ᶠ (P : TauCeti.Place k F), (P.kaehlerResidueOfPerfectField ⋯ hF) ω = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 426. `TauCeti.finite_support_kaehlerResidueOfPerfectField`

```lean
TauCeti.finite_support_kaehlerResidueOfPerfectField.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] [IsAlgClosed k] (hF : TauCeti.IsFunctionField k F) (ω : Ω[F⁄k]) :
  (Function.support fun P => (P.kaehlerResidueOfPerfectField ⋯ hF) ω).Finite
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 427. `TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero`

```lean
TauCeti.finsum_kaehlerResidueOfPerfectField_eq_zero.{u_1, u_2} {k : Type u_1} {F : Type u_2} [Field k] [Field F]
  [Algebra k F] [IsAlgClosed k] (hF : TauCeti.IsFunctionField k F) (ω : Ω[F⁄k]) :
  ∑ᶠ (P : TauCeti.Place k F), (P.kaehlerResidueOfPerfectField ⋯ hF) ω = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 428. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter_transcendental`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter_transcendental {K : Type} [Field K]
  [Algebra ℚ K] (hK : TauCeti.IsFunctionField ℚ K) :
  Transcendental ℚ (ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter hK)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 429. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter_isSeparable`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter_isSeparable {K : Type} [Field K]
  [Algebra ℚ K] (hK : TauCeti.IsFunctionField ℚ K) :
  Algebra.IsSeparable (↥ℚ⟮ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.separatingParameter hK⟯) K
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 430. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.isSeparable_adjoin_transcendental`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.isSeparable_adjoin_transcendental {K : Type} [Field K]
  [Algebra ℚ K] (hK : TauCeti.IsFunctionField ℚ K) {x : K} (hx : Transcendental ℚ x) : Algebra.IsSeparable (↥ℚ⟮x⟯) K
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 431. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_D`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_D {K : Type} [Field K] [Algebra ℚ K]
  (hK : TauCeti.IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) {f : K} (hf : Transcendental ℚ f) :
  (ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison hK hex)
      ((KaehlerDifferential.D ℚ K) f) =
    TauCeti.weilDifferentialOfSeparating hK hf
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 432. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.kaehlerMap_smul`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.kaehlerMap_smul {K L : Type} [Field K] [Field L] [Algebra ℚ K]
  [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (c : K)
  (η : Ω[K⁄ℚ]) : (KaehlerDifferential.map ℚ ℚ K L) (c • η) = (algebraMap K L) c • (KaehlerDifferential.map ℚ ℚ K L) η
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 433. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.cotrace_separating`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.cotrace_separating {K L : Type} [Field K] [Field L]
  [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (hK : TauCeti.IsFunctionField ℚ K) (hL : TauCeti.IsFunctionField ℚ L) {x : K} (hx : Transcendental ℚ x)
  (hxL : Transcendental ℚ ((algebraMap K L) x)) [Algebra.IsSeparable (↥ℚ⟮x⟯) K]
  [Algebra.IsSeparable (↥ℚ⟮(algebraMap K L) x⟯) L] :
  (TauCeti.weilDifferentialCotrace ℚ L hK hL) (TauCeti.weilDifferentialOfSeparating hK hx) =
    TauCeti.weilDifferentialOfSeparating hL hxL
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 434. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_cotrace`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_cotrace {K L : Type} [Field K] [Field L]
  [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (hK : TauCeti.IsFunctionField ℚ K) (hL : TauCeti.IsFunctionField ℚ L) (hexK : IsIntegrallyClosedIn ℚ K)
  (hexL : IsIntegrallyClosedIn ℚ L) (η : Ω[K⁄ℚ]) :
  (ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison hL hexL)
      ((KaehlerDifferential.map ℚ ℚ K L) η) =
    (TauCeti.weilDifferentialCotrace ℚ L hK hL)
      ((ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison hK hexK) η)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 435. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily_cotraceCompatible`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily_cotraceCompatible :
  ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.CotraceCompatibility
    ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 436. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_local_D`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_local_D (K : Type) [Field K] [Algebra ℚ K]
  (hK : TauCeti.IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) (P : TauCeti.Place ℚ K) (f g : K)
  (hf : f ∈ P.integers) (hg : g ∈ P.integers) :
  (TauCeti.repartitionDualComponent
        (↑((ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison hK hex)
            ((KaehlerDifferential.D ℚ K) f)))
        P)
      g =
    0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 437. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily_localExactRegularity`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily_localExactRegularity :
  ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.LocalExactRegularity
    ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.comparisonFamily
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 438. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.rationalResidueComparisonFact`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.rationalResidueComparisonFact :
  ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.ResidueComparisonFact
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 439. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.regular_divisor_zero`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.regular_divisor_zero {K : Type} [Field K] [Algebra ℚ K]
  (hK : TauCeti.IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) (hg : TauCeti.genus ℚ K = 1)
  {ω : Module.Dual ℚ ↥(TauCeti.repartitionSpace ℚ K)} (hm : ω ∈ TauCeti.weilDifferentialSpace ℚ K) (hne : ω ≠ 0)
  (hr : ω ∈ TauCeti.weilDifferentialFiltration 0) : TauCeti.weilDifferentialDivisor hK hex hm hne = 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 440. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.constant_regular_multiple`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.constant_regular_multiple {K : Type} [Field K] [Algebra ℚ K]
  (hK : TauCeti.IsFunctionField ℚ K) (hex : IsIntegrallyClosedIn ℚ K) (hg : TauCeti.genus ℚ K = 1)
  {ω : Module.Dual ℚ ↥(TauCeti.repartitionSpace ℚ K)} (hr : ω ∈ TauCeti.weilDifferentialFiltration 0) (hne : ω ≠ 0)
  (c : K) (hc : ((TauCeti.repartitionDualMul hK) c) ω ∈ TauCeti.weilDifferentialFiltration 0) :
  c ∈ Set.range ⇑(algebraMap ℚ K)
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 441. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_invariant_regular`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison_invariant_regular
  (W : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic W] :
  ↑((ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.normalizedComparison ⋯ ⋯) W.invariantDifferential) ∈
    TauCeti.weilDifferentialFiltration 0
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 442. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.pullbackCoefficientConstantGlue_proof`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.pullbackCoefficientConstantGlue_proof :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.PullbackCoefficientConstantGlue
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 443. `ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.isogenyScalarRationalGlue_proof`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.isogenyScalarRationalGlue_proof :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.IsogenyScalarRationalGlue
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 444. `ZInQ.Contrib.RC53Assist.PullbackScalar.residueComparisonFact_type_eq`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.residueComparisonFact_type_eq :
  ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.ResidueComparisonFact =
    ZInQ.Contrib.RC53Assist.PullbackScalar.RationalResidueComparisonFact
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.

## 445. `ZInQ.Contrib.RC53Assist.PullbackScalar.rationalResidueComparisonFact_proof`

```lean
ZInQ.Contrib.RC53Assist.PullbackScalar.rationalResidueComparisonFact_proof :
  ZInQ.Contrib.RC53Assist.PullbackScalar.RationalResidueComparisonFact
```

Scratch axiom report: `[propext, Classical.choice, Quot.sound]`.


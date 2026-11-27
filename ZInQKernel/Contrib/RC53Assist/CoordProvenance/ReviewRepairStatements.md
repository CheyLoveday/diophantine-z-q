# Exact declarations and individual axiom reports
There are 72 theorems: 12 recorded independent-review obstructions and 60 further repair, scope and normalization results. The audit covers all 122 explicitly named declarations plus 5 record constructors.
The written type header preserves source annotations. The elaborated rendering includes full names, universes, binder types and proofs, without printer ellipses. Implicit typeclass and argument parameters remain implicit, as in the complete source declarations in this bundle.

# EndpointObstructions.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_endpoint_every_scalar`

theorem; source line 37.

Written type header:

```lean
theorem free_endpoint_every_scalar {R : Type} [CommRing R] (u : R) :
    ∃ (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (z w : Fin (m + 1) → R), IsCoordOn D z w u
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_endpoint_every_scalar : ∀ {R : Type}
  [inst : CommRing.{0} R] (u : R),
  Exists.{1} fun (m : Nat) =>
    Exists.{1} fun (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) R) =>
      Exists.{1} fun (z : Fin (HAdd.hAdd.{0, 0, 0} m 1) → R) =>
        Exists.{1} fun (w : Fin (HAdd.hAdd.{0, 0, 0} m 1) → R) =>
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_endpoint_every_scalar' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_endpoint_zero_witness`

theorem; source line 47.

Written type header:

```lean
theorem exact_endpoint_zero_witness {R : Type} [CommRing R] (u : R) :
    ∃ (n : ℕ)
      (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) R)
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → R), IsCoordOn D z w u
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_endpoint_zero_witness : ∀ {R : Type}
  [inst : CommRing.{0} R] (u : R),
  Exists.{1} fun (n : Nat) =>
    Exists.{1}
      fun
        (D :
          Matrix.{0, 0, 0} (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)))
            (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2))) R) =>
      Exists.{1} fun (z : Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) → R) =>
        Exists.{1} fun (w : Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) → R) =>
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_endpoint_zero_witness' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_regular_endpoint_every_scalar`

theorem; source line 55.

Written type header:

```lean
theorem free_regular_endpoint_every_scalar {K : Type} [Field K] (u : K) :
    ∃ (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      (z w : Fin (m + 1) → K),
      D.adjugate ≠ 0 ∧ D *ᵥ z = 0 ∧ w ᵥ* D = 0 ∧ IsCoordOn D z w u
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_regular_endpoint_every_scalar : ∀ {K : Type}
  [inst : Field.{0} K] (u : K),
  Exists.{1} fun (m : Nat) =>
    Exists.{1} fun (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K) =>
      Exists.{1} fun (z : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K) =>
        Exists.{1} fun (w : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K) =>
          And (Ne.{1} (Matrix.adjugate.{0, 0} D) 0)
            (And (Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0)
              (And (Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0)
                (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.free_regular_endpoint_every_scalar' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_fixed_cycle_forces_scalar_zero`

theorem; source line 70.

Written type header:

```lean
theorem zero_fixed_cycle_forces_scalar_zero {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι K) (w : ι → K) (u : K) (hadj : D.adjugate ≠ 0)
    (hu : IsCoordOn D 0 w u) : u = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_fixed_cycle_forces_scalar_zero : ∀ {K : Type}
  [inst : Field.{0} K] {ι : Type} [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι] (D : Matrix.{0, 0, 0} ι ι K)
  (w : ι → K) (u : K),
  Ne.{1} (Matrix.adjugate.{0, 0} D) 0 → ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D 0 w u → Eq.{1} u 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_fixed_cycle_forces_scalar_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_adjugate_loophole`

theorem; source line 77.

Written type header:

```lean
theorem zero_adjugate_loophole {K : Type} [Field K] (u : K) :
    IsCoordOn (0 : Matrix (Fin 2) (Fin 2) K) 0 0 u
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_adjugate_loophole : ∀ {K : Type} [inst : Field.{0} K]
  (u : K), ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} 0 0 0 u
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.zero_adjugate_loophole' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.retained_basis_iff_coordinate_equality`

theorem; source line 93.

Written type header:

```lean
theorem retained_basis_iff_coordinate_equality
    (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0)
    (hnz : kmCoord D zD lD hzD hlD σD ≠ 0) :
    (torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) ↔
      kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.retained_basis_iff_coordinate_equality : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3'] [inst_9 : DecidableEq.{1} ι0] [inst_10 : DecidableEq.{1} ι1]
  [inst_11 : DecidableEq.{1} ι2] [inst_12 : DecidableEq.{1} ι3] [inst_13 : DecidableEq.{1} ι0']
  [inst_14 : DecidableEq.{1} ι1'] [inst_15 : DecidableEq.{1} ι2'] [inst_16 : DecidableEq.{1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0)
  (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))
  (σD : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0' Unit) ι2') (Sum.{0, 0} ι1' (Sum.{0, 0} ι3' Unit))),
  Ne.{1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H hzC hlC hzD hlD))
        (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
      0 →
    Ne.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} D zD lD hzD hlD σD) 0 →
      Iff
        (Eq.{1}
          (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0,
                  0, 0}
                H hzC hlC hzD hlD))
            (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
          (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))))
        (Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC lC hzC hlC σC)
          (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} D zD lD hzD hlD σD))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.retained_basis_iff_coordinate_equality' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.same_disk_numeric_counterexample`

theorem; source line 118.

Written type header:

```lean
theorem same_disk_numeric_counterexample : (2 : ℚ)⁻¹ * 1 ≠ (2 : ℚ) * 1
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.same_disk_numeric_counterexample : Ne.{1}
  (HMul.hMul.{0, 0, 0} (Inv.inv.{0} 2) 1) (HMul.hMul.{0, 0, 0} 2 1)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.same_disk_numeric_counterexample' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_half_disk`

theorem; source line 122.

Written type header:

```lean
theorem no_integral_half_disk :
    ¬ ∃ E : Matrix (Fin 1) (Fin 1) ℤ,
      E.map (Int.castRingHom ℚ) =
        (Matrix.map (fun _ _ => (2 : ℤ) : Matrix (Fin 1) (Fin 1) ℤ) (Int.castRingHom ℚ))⁻¹
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_half_disk : Not
  (Exists.{1} fun (E : Matrix.{0, 0, 0} (Fin 1) (Fin 1) Int) =>
    Eq.{1} (Matrix.map.{0, 0, 0, 0} E ⇑(Int.castRingHom.{0} Rat))
      (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} (fun (x x_1 : Fin 1) => 2) ⇑(Int.castRingHom.{0} Rat))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_half_disk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.poleDisk`

def; source line 144.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.poleDisk : Matrix.{0, 0, 0} (Fin 1) (Fin 1)
  ZInQ.Manuscript.RC.Determinant.Lam
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.poleDisk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_X_inverse_disk`

theorem; source line 147.

Written type header:

```lean
theorem no_integral_X_inverse_disk :
    ¬ ∃ E : Matrix (Fin 1) (Fin 1) Lam,
      E.map integralToLaurent = (poleDisk.map integralToLaurent)⁻¹
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_X_inverse_disk : Not
  (Exists.{1} fun (E : Matrix.{0, 0, 0} (Fin 1) (Fin 1) ZInQ.Manuscript.RC.Determinant.Lam) =>
    Eq.{1} (Matrix.map.{0, 0, 0, 0} E ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent)
      (Inv.inv.{0}
        (Matrix.map.{0, 0, 0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.poleDisk
          ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.no_integral_X_inverse_disk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex`

abbrev; source line 173.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex : Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot`

def; source line 175.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot : ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot' depends on axioms: [propext]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix`

def; source line 178.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix : (R : Type) →
  [CommRing.{0} R] →
    Matrix.{0, 0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex
      ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.EndpointIndex R
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix' depends on axioms: [propext,
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpoint_adjugate`

theorem; source line 182.

Written type header:

```lean
theorem freeEndpoint_adjugate (R : Type) [CommRing R] :
    (freeEndpointMatrix R).adjugate = Matrix.diagonal (Pi.single endpointPivot (1 : R))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpoint_adjugate : ∀ (R : Type) [inst : CommRing.{0} R],
  Eq.{1} (Matrix.adjugate.{0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix R))
    (Matrix.diagonal.{0, 0}
      (Pi.single.{0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot 1))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpoint_adjugate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_free_regular_endpoint_every_scalar`

theorem; source line 199.

Written type header:

```lean
theorem exact_free_regular_endpoint_every_scalar (R : Type) [CommRing R] [Nontrivial R] (u : R) :
    ∃ (n : ℕ) (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) R)
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → R), IsCoordOn D z w u ∧ D.adjugate ≠ 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_free_regular_endpoint_every_scalar : ∀ (R : Type)
  [inst : CommRing.{0} R] [Nontrivial.{0} R] (u : R),
  Exists.{1} fun (n : Nat) =>
    Exists.{1}
      fun
        (D :
          Matrix.{0, 0, 0} (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)))
            (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2))) R) =>
      Exists.{1} fun (z : Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) → R) =>
        Exists.{1} fun (w : Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) → R) =>
          And (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u) (Ne.{1} (Matrix.adjugate.{0, 0} D) 0)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.exact_free_regular_endpoint_every_scalar' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.fixed_free_endpoint_closed`

theorem; source line 214.

Written type header:

```lean
theorem fixed_free_endpoint_closed (R : Type) [CommRing R] (u : R) :
    freeEndpointMatrix R *ᵥ Pi.single endpointPivot u = 0 ∧
      Pi.single endpointPivot (1 : R) ᵥ* freeEndpointMatrix R = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.fixed_free_endpoint_closed : ∀ (R : Type)
  [inst : CommRing.{0} R] (u : R),
  And
    (Eq.{1}
      (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix R)
        (Pi.single.{0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot u))
      0)
    (Eq.{1}
      (Matrix.vecMul.{0, 0, 0}
        (Pi.single.{0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.endpointPivot 1)
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.freeEndpointMatrix R))
      0)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions.fixed_free_endpoint_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# BoundEndpoint.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData`

structure; source line 43.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData : {A : Type} →
  [CommRing.{0} A] → Matrix.{0, 0, 0} (Fin 2) (Fin 2) A → A → A → A → A → A → A → A → A → (A → Prop) → (A → Prop) → Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.Index`

abbrev; source line 71.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.Index : {A : Type} →
  [inst : CommRing.{0} A] →
    {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
      {q qi a z zi uP uR eps : A} →
        {unitR unitP : A → Prop} →
          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP → Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.Index' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.toActualStep`

theorem; source line 76.

Written type header:

```lean
theorem StepData.toActualStep {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (s : StepData F q qi a z zi uP uR eps unitR unitP) :
    ActualStep F q qi a z zi uP uR eps unitR unitP
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.toActualStep : ∀ {A : Type} [inst : CommRing.{0} A]
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP),
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.ActualStep F q qi a z zi uP uR eps unitR unitP
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.toActualStep' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected_data_exists`

theorem; source line 84.

Written type header:

```lean
theorem selected_data_exists {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
    {unitR unitP : A → Prop} (h : ActualStep F q qi a z zi uP uR eps unitR unitP) :
    Nonempty (StepData F q qi a z zi uP uR eps unitR unitP)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected_data_exists : ∀ {A : Type} [inst : CommRing.{0} A]
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop},
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.ActualStep F q qi a z zi uP uR eps unitR unitP →
    Nonempty.{1} (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected_data_exists' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected`

def; source line 93.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected : {A : Type} →
  [inst : CommRing.{0} A] →
    {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
      {q qi a z zi uP uR eps : A} →
        {unitR unitP : A → Prop} →
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.ActualStep F q qi a z zi uP uR eps unitR unitP →
            ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.selected' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.adjugate_ne_zero`

theorem; source line 100.

Written type header:

```lean
theorem StepData.adjugate_ne_zero [IsDomain A]
    {F : Matrix (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
    (s : StepData F q qi a z zi uP uR eps unitR unitP)
    (hB : (twoPlaceBlock F q z zi).det ≠ 0) : s.DR.adjugate ≠ 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.adjugate_ne_zero : ∀ {A : Type} [inst : CommRing.{0} A]
  [IsDomain.{0} A] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP),
  Ne.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock.{0} F q z zi)) 0 →
    Ne.{1} (Matrix.adjugate.{0, 0} s.DR) 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.adjugate_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift`

structure; source line 115.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift : {A : Type} →
  [inst : CommRing.{0} A] →
    {R : Type} →
      [inst_1 : CommRing.{0} R] →
        {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
          {q qi a z zi uP uR eps : A} →
            {unitR unitP : A → Prop} →
              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP →
                RingHom.{0, 0} R A → Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.stored_coordinate`

theorem; source line 124.

Written type header:

```lean
theorem CommonLift.stored_coordinate (E : CommonLift s f) :
    IsCoordOn (E.D.map f) (f ∘ E.z) (f ∘ E.w) uR
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.stored_coordinate : ∀ {A : Type}
  [inst : CommRing.{0} A] {R : Type} [inst_1 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (f : RingHom.{0, 0} R A) (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s f),
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} E.D ⇑f)
    (Function.comp.{1, 1, 1} (⇑f) E.z) (Function.comp.{1, 1, 1} (⇑f) E.w) uR
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.stored_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.relabel_readback`

theorem; source line 130.

Written type header:

```lean
theorem CommonLift.relabel_readback {κ : Type} (e : κ ≃ s.Index) (E : CommonLift s f) :
    (E.D.submatrix e e).map f = s.DR.submatrix e e ∧
      f ∘ (E.z ∘ e) = s.zR ∘ e ∧ f ∘ (E.w ∘ e) = s.wR ∘ e
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.relabel_readback : ∀ {A : Type}
  [inst : CommRing.{0} A] {R : Type} [inst_1 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (f : RingHom.{0, 0} R A) {κ : Type} (e : Equiv.{1, 1} κ s.Index)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s f),
  And
    (Eq.{1} (Matrix.map.{0, 0, 0, 0} (Matrix.submatrix.{0, 0, 0, 0, 0} E.D ⇑e ⇑e) ⇑f)
      (Matrix.submatrix.{0, 0, 0, 0, 0} s.DR ⇑e ⇑e))
    (And (Eq.{1} (Function.comp.{1, 1, 1} (⇑f) (Function.comp.{1, 1, 1} E.z ⇑e)) (Function.comp.{1, 1, 1} s.zR ⇑e))
      (Eq.{1} (Function.comp.{1, 1, 1} (⇑f) (Function.comp.{1, 1, 1} E.w ⇑e)) (Function.comp.{1, 1, 1} s.wR ⇑e)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.relabel_readback' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.common_fraction`

theorem; source line 139.

Written type header:

```lean
theorem CommonLift.common_fraction {K : Type} [Field K] (hf : Function.Injective f)
    (g : R →+* K) (hg : Function.Injective g) (E : CommonLift s f)
    (hadj : E.D.adjugate ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ f den * uR = f num ∧
      IsCoordOn (E.D.map g) (g ∘ E.z) (g ∘ E.w) (g num / g den)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.common_fraction : ∀ {A : Type} [inst : CommRing.{0} A]
  {R : Type} [inst_1 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} {q qi a z zi uP uR eps : A}
  {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (f : RingHom.{0, 0} R A) {K : Type} [inst_2 : Field.{0} K],
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s f),
          Ne.{1} (Matrix.adjugate.{0, 0} E.D) 0 →
            Exists.{1} fun (num : R) =>
              Exists.{1} fun (den : R) =>
                And (Ne.{1} den 0)
                  (And (Eq.{1} (HMul.hMul.{0, 0, 0} (f den) uR) (f num))
                    (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} E.D ⇑g)
                      (Function.comp.{1, 1, 1} (⇑g) E.z) (Function.comp.{1, 1, 1} (⇑g) E.w)
                      (HDiv.hDiv.{0, 0, 0} (g num) (g den))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.common_fraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX`

abbrev; source line 154.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX : (R : Type) →
  [inst : CommRing.{0} R] → Type → Int → ModuleCat.{0, 0} R
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX' depends on axioms: [Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD`

def; source line 159.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD : {R : Type} →
  [inst : CommRing.{0} R] →
    {ι : Type} →
      [Fintype.{0} ι] →
        Matrix.{0, 0, 0} ι ι R →
          (i : Int) →
            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
              ↑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX R ι i)
              ↑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX R ι (HAdd.hAdd.{0, 0, 0} i 1))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD_square`

theorem; source line 164.

Written type header:

```lean
theorem coreD_square (D : Matrix ι ι R) (i : ℤ) (v : coreX R ι i) :
    coreD D (i + 1) (coreD D i v) = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD_square : ∀ {R : Type} [inst : CommRing.{0} R] {ι : Type}
  [inst_1 : Fintype.{0} ι] (D : Matrix.{0, 0, 0} ι ι R) (i : Int)
  (v : ↑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreX R ι i)),
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD D (HAdd.hAdd.{0, 0, 0} i 1))
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD D i) v))
    0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreD_square' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreCx`

def; source line 175.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreCx : {R : Type} →
  [inst : CommRing.{0} R] →
    {ι : Type} → [Fintype.{0} ι] → Matrix.{0, 0, 0} ι ι R → ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} R
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreCx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt`

abbrev; source line 186.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt : {b : Nat} →
  MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int) →
    RingHom.{0, 0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))
      (PowerSeries.{0} (Padic 2))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding`

structure; source line 206.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} →
                  {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)} →
                    {unitR unitP : PowerSeries.{0} (Padic 2) → Prop} →
                      (s :
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR
                            unitP) →
                        (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int)) →
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
                              (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ) →
                            (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                              (zActual :
                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                Eq.{1}
                                    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                                      zActual)
                                    0 →
                                  {Dp :
                                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                    (P :
                                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp) →
                                      (tr :
                                          LinearMap.{0, 0, 0, 0}
                                            (RingHom.id.{0}
                                              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                3))
                                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                              (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                        (∀
                                            (c :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                  2)),
                                            Eq.{1}
                                              (tr
                                                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                        P))
                                                    2 3 rfl.{1})
                                                  c))
                                              0) →
                                          (zc :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1)) →
                                            Eq.{1}
                                                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
                                                    rfl.{1})
                                                  zc)
                                                0 →
                                              Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.classMap`

abbrev; source line 227.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.classMap : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} →
                  {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)} →
                    {unitR unitP : PowerSeries.{0} (Padic 2) → Prop} →
                      (s :
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR
                            unitP) →
                        (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int)) →
                          (E :
                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) →
                            (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                              (zActual :
                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                (hzActual :
                                    Eq.{1}
                                      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                                        zActual)
                                      0) →
                                  {Dp :
                                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                    (P :
                                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp) →
                                      (tr :
                                          LinearMap.{0, 0, 0, 0}
                                            (RingHom.id.{0}
                                              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                3))
                                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                              (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                        (htr :
                                            ∀
                                              (c :
                                                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                        P))
                                                    2)),
                                              Eq.{1}
                                                (tr
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                          P))
                                                      2 3 rfl.{1})
                                                    c))
                                                0) →
                                          (zc :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1)) →
                                            (hzc :
                                                Eq.{1}
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
                                                      rfl.{1})
                                                    zc)
                                                  0) →
                                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E
                                                  M zActual hzActual P tr htr zc hzc →
                                                LinearMap.{0, 0, 0, 0}
                                                  (RingHom.id.{0}
                                                    (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                      (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                                  (s.Index →
                                                    MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                      (ZInQ.Manuscript.RC.Determinant.SignGroup b))
                                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.classMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functionalMap`

abbrev; source line 231.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functionalMap : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} →
                  {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)} →
                    {unitR unitP : PowerSeries.{0} (Padic 2) → Prop} →
                      (s :
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR
                            unitP) →
                        (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int)) →
                          (E :
                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) →
                            (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                              (zActual :
                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                (hzActual :
                                    Eq.{1}
                                      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                                        zActual)
                                      0) →
                                  {Dp :
                                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                    (P :
                                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp) →
                                      (tr :
                                          LinearMap.{0, 0, 0, 0}
                                            (RingHom.id.{0}
                                              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                3))
                                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                              (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                        (htr :
                                            ∀
                                              (c :
                                                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                        P))
                                                    2)),
                                              Eq.{1}
                                                (tr
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                          P))
                                                      2 3 rfl.{1})
                                                    c))
                                                0) →
                                          (zc :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1)) →
                                            (hzc :
                                                Eq.{1}
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
                                                      rfl.{1})
                                                    zc)
                                                  0) →
                                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E
                                                  M zActual hzActual P tr htr zc hzc →
                                                LinearMap.{0, 0, 0, 0}
                                                  (RingHom.id.{0}
                                                    (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                      (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                                  (s.Index →
                                                    MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                      (ZInQ.Manuscript.RC.Determinant.SignGroup b))
                                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functionalMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.readback`

theorem; source line 236.

Written type header:

```lean
theorem SelmerBinding.readback (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    E.D.map (scalarAt χ) = s.DR ∧ scalarAt χ ∘ E.z = s.zR ∧ scalarAt χ ∘ E.w = s.wR ∧
    B.classMap s χ E M zActual hzActual P tr htr zc hzc (φO b ∘ E.z) - zActual =
      (familyCx M).d 0 1 rfl B.boundary ∧
    ∀ v, (φO b ∘ E.w) ⬝ᵥ v = rightFunctional P tr zc
      (B.functionalMap s χ E M zActual hzActual P tr htr zc hzc v)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.readback : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  And (Eq.{1} (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) s.DR)
    (And
      (Eq.{1} (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) E.z) s.zR)
      (And
        (Eq.{1} (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) E.w)
          s.wR)
        (And
          (Eq.{1}
            (HSub.hSub.{0, 0, 0}
              ((ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.classMap s χ E M zActual hzActual P
                  tr htr zc hzc B)
                (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.z))
              zActual)
            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0 1 rfl.{1})
              B.boundary))
          (∀
            (v :
              s.Index →
                MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
            Eq.{1}
              (dotProduct.{0, 0} (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.w) v)
              ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.rightFunctional P tr zc)
                ((ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functionalMap s χ E M zActual
                    hzActual P tr htr zc hzc B)
                  v))))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.readback' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.class_not_zero`

theorem; source line 245.

Written type header:

```lean
theorem SelmerBinding.class_not_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (hnonboundary : ∀ c : (familyCx M).X 0, zActual ≠ (familyCx M).d 0 1 rfl c) :
    E.z ≠ 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.class_not_zero : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  (∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0)),
      Ne.{1} zActual
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0 1 rfl.{1})
          c)) →
    Ne.{1} E.z 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.class_not_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.zero_row_kills_actual_cycles`

theorem; source line 259.

Written type header:

```lean
theorem SelmerBinding.zero_row_kills_actual_cycles
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) (hw : E.w = 0)
    (v : (familyCx M).X 2) (hv : (familyCx M).d 2 3 rfl v = 0) :
    rightFunctional P tr zc v = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.zero_row_kills_actual_cycles : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  Eq.{1} E.w 0 →
    ∀
      (v :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2 3 rfl.{1})
            v)
          0 →
        Eq.{1} ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.rightFunctional P tr zc) v) 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.zero_row_kills_actual_cycles' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_matrix_readback`

theorem; source line 284.

Written type header:

```lean
theorem CommonLift.laurent_matrix_readback :
    (E.D.map (signToCommon χ)).map toLaurent = s.DR.map powerSeriesToLaurent
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_matrix_readback : ∀ {b : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)),
  Eq.{1}
    (Matrix.map.{0, 0, 0, 0}
      (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ))
      ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
    (Matrix.map.{0, 0, 0, 0} s.DR ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_matrix_readback' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_vector_readbacks`

theorem; source line 290.

Written type header:

```lean
theorem CommonLift.laurent_vector_readbacks :
    toLaurent ∘ (signToCommon χ ∘ E.z) = powerSeriesToLaurent ∘ s.zR ∧
      toLaurent ∘ (signToCommon χ ∘ E.w) = powerSeriesToLaurent ∘ s.wR
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_vector_readbacks : ∀ {b : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)),
  And
    (Eq.{1}
      (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
        (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.z))
      (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent) s.zR))
    (Eq.{1}
      (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
        (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.w))
      (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent) s.wR))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.laurent_vector_readbacks' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.clearing_readbacks`

theorem; source line 300.

Written type header:

```lean
theorem CommonLift.clearing_readbacks :
    (E.D.map (signToCommon χ)).map toClearing = (E.D.map (φO b)).map (evK χ) ∧
      toClearing ∘ (signToCommon χ ∘ E.z) = evK χ ∘ (φO b ∘ E.z) ∧
      toClearing ∘ (signToCommon χ ∘ E.w) = evK χ ∘ (φO b ∘ E.w)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.clearing_readbacks : ∀ {b : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)),
  And
    (Eq.{1}
      (Matrix.map.{0, 0, 0, 0}
        (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ))
        ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
      (Matrix.map.{0, 0, 0, 0} (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
        ⇑(ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ)))
    (And
      (Eq.{1}
        (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
          (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.z))
        (Function.comp.{1, 1, 1} (⇑(ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ))
          (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.z)))
      (Eq.{1}
        (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
          (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.w))
        (Function.comp.{1, 1, 1} (⇑(ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ))
          (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.w))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.clearing_readbacks' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.fixed_laurent_coordinate`

theorem; source line 308.

Written type header:

```lean
theorem CommonLift.fixed_laurent_coordinate :
    IsCoordOn ((E.D.map (signToCommon χ)).map toLaurent)
      (toLaurent ∘ (signToCommon χ ∘ E.z)) (toLaurent ∘ (signToCommon χ ∘ E.w))
      (powerSeriesToLaurent uR)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.fixed_laurent_coordinate : ∀ {b : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)),
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0}
    (Matrix.map.{0, 0, 0, 0}
      (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ))
      ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
    (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
      (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.z))
    (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
      (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) E.w))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent uR)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.fixed_laurent_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.bindingOfNativeComparison`

def; source line 323.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.bindingOfNativeComparison : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} →
                  {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)} →
                    {unitR unitP : PowerSeries.{0} (Padic 2) → Prop} →
                      (s :
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR
                            unitP) →
                        (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int)) →
                          (E :
                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)) →
                            (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                              (zActual :
                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                (hzActual :
                                    Eq.{1}
                                      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                                        zActual)
                                      0) →
                                  {Dp :
                                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                    (P :
                                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp) →
                                      (tr :
                                          LinearMap.{0, 0, 0, 0}
                                            (RingHom.id.{0}
                                              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                3))
                                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                              (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                        (htr :
                                            ∀
                                              (c :
                                                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                        P))
                                                    2)),
                                              Eq.{1}
                                                (tr
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                          P))
                                                      2 3 rfl.{1})
                                                    c))
                                                0) →
                                          (zc :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1)) →
                                            (hzc :
                                                Eq.{1}
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
                                                      rfl.{1})
                                                    zc)
                                                  0) →
                                              (J :
                                                  Quiver.Hom.{0, 1}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreCx
                                                        (Matrix.map.{0, 0, 0, 0} E.D
                                                          ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))))
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.modelCx M))) →
                                                QuasiIso.{0, 1, 0} J →
                                                  Eq.{1}
                                                      (Matrix.mulVec.{0, 0, 0}
                                                        (Matrix.map.{0, 0, 0, 0} E.D
                                                          ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
                                                        (Function.comp.{1, 1, 1}
                                                          (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.z))
                                                      0 →
                                                    (a_1 :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx
                                                              M)
                                                            0)) →
                                                      Eq.{1}
                                                          (HSub.hSub.{0, 0, 0}
                                                            ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.modelMap1
                                                                M)
                                                              ((have this :=
                                                                  ModuleCat.Hom.hom.{0, 0}
                                                                    (HomologicalComplex.Hom.f.{0, 1, 0} J 1);
                                                                this)
                                                                (Function.comp.{1, 1, 1}
                                                                  (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
                                                                  E.z)))
                                                            zActual)
                                                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx
                                                                M)
                                                              0 1 rfl.{1})
                                                            a_1) →
                                                        (∀
                                                            (v :
                                                              s.Index →
                                                                MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                                  (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
                                                            Eq.{1}
                                                              (dotProduct.{0, 0}
                                                                (Function.comp.{1, 1, 1}
                                                                  (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
                                                                  E.w)
                                                                v)
                                                              (dotProduct.{0, 0}
                                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.pairedRow
                                                                  M P tr zc)
                                                                ((have this :=
                                                                    ModuleCat.Hom.hom.{0, 0}
                                                                      (HomologicalComplex.Hom.f.{0, 1, 0} J 2);
                                                                  this)
                                                                  v))) →
                                                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding
                                                            s χ E M zActual hzActual P tr htr zc hzc
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.bindingOfNativeComparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functional_not_zero`

theorem; source line 347.

Written type header:

```lean
theorem SelmerBinding.functional_not_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (v : (familyCx M).X 2) (hv : (familyCx M).d 2 3 rfl v = 0)
    (hne : rightFunctional P tr zc v ≠ 0) : E.w ≠ 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functional_not_zero : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
  (v :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2)),
  Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2 3 rfl.{1})
        v)
      0 →
    Ne.{1} ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.rightFunctional P tr zc) v) 0 → Ne.{1} E.w 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.functional_not_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.integralCompletion_injective`

theorem; source line 355.

Written type header:

```lean
theorem integralCompletion_injective : Function.Injective (φO b)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.integralCompletion_injective : ∀ {b : Nat},
  Function.Injective.{1, 1} ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.integralCompletion_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.completed_row_closed`

theorem; source line 365.

Written type header:

```lean
theorem SelmerBinding.completed_row_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    (φO b ∘ E.w) ᵥ* E.D.map (φO b) = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.completed_row_closed : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  Eq.{1}
    (Matrix.vecMul.{0, 0, 0} (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.w)
      (Matrix.map.{0, 0, 0, 0} E.D ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)))
    0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.completed_row_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_closed`

theorem; source line 385.

Written type header:

```lean
theorem SelmerBinding.integral_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    E.D *ᵥ E.z = 0 ∧ E.w ᵥ* E.D = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_closed : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  And (Eq.{1} (Matrix.mulVec.{0, 0, 0} E.D E.z) 0) (Eq.{1} (Matrix.vecMul.{0, 0, 0} E.w E.D) 0)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_closed`

theorem; source line 402.

Written type header:

```lean
theorem SelmerBinding.stored_closed
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc) :
    s.DR *ᵥ s.zR = 0 ∧ s.wR ᵥ* s.DR = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_closed : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc),
  And (Eq.{1} (Matrix.mulVec.{0, 0, 0} s.DR s.zR) 0) (Eq.{1} (Matrix.vecMul.{0, 0, 0} s.wR s.DR) 0)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.actual_boundary_forces_class_zero`

theorem; source line 421.

Written type header:

```lean
theorem SelmerBinding.actual_boundary_forces_class_zero
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (c : (familyCx M).X 0) (hc : zActual = (familyCx M).d 0 1 rfl c) : E.z = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.actual_boundary_forces_class_zero : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
  (c :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0)),
  Eq.{1} zActual
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0 1 rfl.{1})
        c) →
    Eq.{1} E.z 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.actual_boundary_forces_class_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_scalar_zero_of_actual_boundary`

theorem; source line 443.

Written type header:

```lean
theorem SelmerBinding.stored_scalar_zero_of_actual_boundary
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (c : (familyCx M).X 0) (hc : zActual = (familyCx M).d 0 1 rfl c)
    (hlocal : (twoPlaceBlock F q z zi).det ≠ 0) : uR = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_scalar_zero_of_actual_boundary : ∀
  {N : Type} [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
  (c :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0)),
  Eq.{1} zActual
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0 1 rfl.{1})
        c) →
    Ne.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock.{0} F q z zi)) 0 → Eq.{1} uR 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.stored_scalar_zero_of_actual_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_h3_cycles_are_boundaries`

theorem; source line 462.

Written type header:

```lean
theorem SelmerBinding.integral_h3_cycles_are_boundaries
    (B : SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
    (v : (familyCx M).X 3) (hv : (familyCx M).d 3 4 rfl v = 0) :
    ∃ a : (familyCx M).X 2, v = (familyCx M).d 2 3 rfl a
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_h3_cycles_are_boundaries : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
  (v :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 3)),
  Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 3 4 rfl.{1})
        v)
      0 →
    Exists.{1}
      fun
        (a :
          ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2)) =>
      Eq.{1} v
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2 3 rfl.{1})
          a)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.integral_h3_cycles_are_boundaries' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.no_integral_twoTerm_binding_of_nonzero_h3`

theorem; source line 480.

Written type header:

```lean
theorem no_integral_twoTerm_binding_of_nonzero_h3
    (v : (familyCx M).X 3) (hv : (familyCx M).d 3 4 rfl v = 0)
    (hn : ∀ a : (familyCx M).X 2, v ≠ (familyCx M).d 2 3 rfl a) :
    ¬ Nonempty (SelmerBinding s χ E M zActual hzActual P tr htr zc hzc)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.no_integral_twoTerm_binding_of_nonzero_h3 : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)}
  {unitR unitP : PowerSeries.{0} (Padic 2) → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int))
  (E :
    ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ))
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (v :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 3)),
  Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 3 4 rfl.{1})
        v)
      0 →
    (∀
        (a :
          ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2)),
        Ne.{1} v
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 2 3 rfl.{1})
            a)) →
      Not
        (Nonempty.{1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding s χ E M zActual hzActual P tr htr zc
            hzc))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.no_integral_twoTerm_binding_of_nonzero_h3' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.mk`

Record constructor.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.mk : {A : Type} →
  [inst : CommRing.{0} A] →
    {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
      {q qi a z zi uP uR eps : A} →
        {unitR unitP : A → Prop} →
          (n : Nat) →
            (DP PP QP : Matrix.{0, 0, 0} (Fin n) (Fin n) A) →
              (DR PR QR :
                  Matrix.{0, 0, 0} (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)))
                    (Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2))) A) →
                (X : Matrix.{0, 0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) A) →
                  (zP wP : Fin n → A) →
                    (zR wR : Sum.{0, 0} (Fin n) (Sum.{0, 0} (Fin 2) (Fin 2)) → A) →
                      IsUnit.{0} (Matrix.det.{0, 0} PP) →
                        IsUnit.{0} (Matrix.det.{0, 0} QP) →
                          IsUnit.{0} (Matrix.det.{0, 0} PR) →
                            IsUnit.{0} (Matrix.det.{0, 0} QR) →
                              Eq.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} PR DR) QR)
                                  (Matrix.fromBlocks.{0, 0, 0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} PP DP) QP) X 0
                                    (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock.{0} F q z zi)) →
                                (∀ (i : Fin n),
                                    Eq.{1} (Matrix.mulVec.{0, 0, 0} (Inv.inv.{0} QR) zR (Sum.inl.{0, 0} i))
                                      (HMul.hMul.{0, 0, 0} (ZInQ.Manuscript.RC.Central.pointFactor.{0} a z zi)
                                        (Matrix.mulVec.{0, 0, 0} (Inv.inv.{0} QP) zP i))) →
                                  (∀ (i : Fin n),
                                      Eq.{1} (Matrix.vecMul.{0, 0, 0} wR (Inv.inv.{0} PR) (Sum.inl.{0, 0} i))
                                        (HMul.hMul.{0, 0, 0} (ZInQ.Manuscript.RC.Central.pointFactor.{0} a z zi)
                                          (Matrix.vecMul.{0, 0, 0} wP (Inv.inv.{0} PP) i))) →
                                    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} DR zR wR uR →
                                      ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} DP zP wP uP →
                                        Ne.{1}
                                            (Matrix.adjugate.{0, 0}
                                              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} PP DP) QP))
                                            0 →
                                          unitR (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} PR) (Matrix.det.{0, 0} QR)) →
                                            unitP (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} PP) (Matrix.det.{0, 0} QP)) →
                                              Eq.{1} eps
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} qi 4)
                                                      (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} PR)
                                                        (Matrix.det.{0, 0} QR)))
                                                    (Ring.inverse.{0}
                                                      (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} PP)
                                                        (Matrix.det.{0, 0} QP)))) →
                                                ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a
                                                  z zi uP uR eps unitR unitP
```

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData.mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.mk`

Record constructor.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.mk : {A : Type} →
  [inst : CommRing.{0} A] →
    {R : Type} →
      [inst_1 : CommRing.{0} R] →
        {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
          {q qi a z zi uP uR eps : A} →
            {unitR unitP : A → Prop} →
              {s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP} →
                {f : RingHom.{0, 0} R A} →
                  (D : Matrix.{0, 0, 0} s.Index s.Index R) →
                    (z_1 w : s.Index → R) →
                      Eq.{1} (Matrix.map.{0, 0, 0, 0} D ⇑f) s.DR →
                        Eq.{1} (Function.comp.{1, 1, 1} (⇑f) z_1) s.zR →
                          Eq.{1} (Function.comp.{1, 1, 1} (⇑f) w) s.wR →
                            ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s f
```

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift.mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.mk`

Record constructor.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.mk : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (PowerSeries.{0} (Padic 2))} →
                  {q qi a z zi uP uR eps : PowerSeries.{0} (Padic 2)} →
                    {unitR unitP : PowerSeries.{0} (Padic 2) → Prop} →
                      {s :
                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR
                            unitP} →
                        {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} Int)} →
                          {E :
                              ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.scalarAt χ)} →
                            {M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK} →
                              {zActual :
                                  ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)} →
                                {hzActual :
                                    Eq.{1}
                                      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                                        zActual)
                                      0} →
                                  {Dp :
                                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                    {P :
                                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp} →
                                      {tr :
                                          LinearMap.{0, 0, 0, 0}
                                            (RingHom.id.{0}
                                              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                                                3))
                                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                              (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                        {htr :
                                            ∀
                                              (c :
                                                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                        P))
                                                    2)),
                                              Eq.{1}
                                                (tr
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                          P))
                                                      2 3 rfl.{1})
                                                    c))
                                                0} →
                                          {zc :
                                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1)} →
                                            {hzc :
                                                Eq.{1}
                                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
                                                      rfl.{1})
                                                    zc)
                                                  0} →
                                              (ψ :
                                                  Quiver.Hom.{0, 1}
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.coreCx
                                                        (Matrix.map.{0, 0, 0, 0} E.D
                                                          ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))))
                                                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx
                                                        M))) →
                                                QuasiIso.{0, 1, 0} ψ →
                                                  Eq.{1}
                                                      (Matrix.mulVec.{0, 0, 0}
                                                        (Matrix.map.{0, 0, 0, 0} E.D
                                                          ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
                                                        (Function.comp.{1, 1, 1}
                                                          (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.z))
                                                      0 →
                                                    (boundary :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx
                                                              M)
                                                            0)) →
                                                      Eq.{1}
                                                          (HSub.hSub.{0, 0, 0}
                                                            ((have this :=
                                                                ModuleCat.Hom.hom.{0, 0}
                                                                  (HomologicalComplex.Hom.f.{0, 1, 0} ψ 1);
                                                              this)
                                                              (Function.comp.{1, 1, 1}
                                                                (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) E.z))
                                                            zActual)
                                                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                              (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx
                                                                M)
                                                              0 1 rfl.{1})
                                                            boundary) →
                                                        (∀
                                                            (v :
                                                              s.Index →
                                                                MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                                  (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
                                                            Eq.{1}
                                                              (dotProduct.{0, 0}
                                                                (Function.comp.{1, 1, 1}
                                                                  (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
                                                                  E.w)
                                                                v)
                                                              ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.rightFunctional
                                                                  P tr zc)
                                                                ((have this :=
                                                                    ModuleCat.Hom.hom.{0, 0}
                                                                      (HomologicalComplex.Hom.f.{0, 1, 0} ψ 2);
                                                                  this)
                                                                  v))) →
                                                          ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding
                                                            s χ E M zActual hzActual P tr htr zc hzc
```

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.SelmerBinding.mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# ConeDeterminant.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_block_swap`

theorem; source line 32.

Written type header:

```lean
theorem det_block_swap :
    (fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det =
      (-1 : K) ^ Fintype.card ι
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_block_swap : ∀ {K : Type} [inst : Field.{0} K] {ι : Type}
  [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι],
  Eq.{1} (Matrix.det.{0, 0} (Matrix.fromBlocks.{0, 0, 0, 0, 0} 0 1 1 0)) (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} ι))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_block_swap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_cross`

theorem; source line 44.

Written type header:

```lean
theorem det_cross (A B : Matrix ι ι K) :
    (fromBlocks 0 A B 0).det = (-1 : K) ^ Fintype.card ι * A.det * B.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_cross : ∀ {K : Type} [inst : Field.{0} K] {ι : Type}
  [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι] (A B : Matrix.{0, 0, 0} ι ι K),
  Eq.{1} (Matrix.det.{0, 0} (Matrix.fromBlocks.{0, 0, 0, 0, 0} 0 A B 0))
    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} ι)) (Matrix.det.{0, 0} A))
      (Matrix.det.{0, 0} B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_cross' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso`

structure; source line 60.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [DecidableEq.{1} κe] →
            [DecidableEq.{1} κo] →
              ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo →
                ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo → Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneContraction`

def; source line 69.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneContraction : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              {C D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                (I : ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso C D) →
                  ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{0, 0, 0}
                    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} I.f)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneContraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_oriented_cross`

theorem; source line 100.

Written type header:

```lean
theorem det_oriented_cross (A : Matrix κo κo K) (B : Matrix κe κe K) (σ : κe ≃ κo) :
    ((fromBlocks 0 A B 0).submatrix (σ.sumCongr σ.symm) id).det =
      (-1 : K) ^ Fintype.card κo * A.det * B.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_oriented_cross : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : DecidableEq.{1} κe]
  [inst_4 : DecidableEq.{1} κo] (A : Matrix.{0, 0, 0} κo κo K) (B : Matrix.{0, 0, 0} κe κe K) (σ : Equiv.{1, 1} κe κo),
  Eq.{1}
    (Matrix.det.{0, 0}
      (Matrix.submatrix.{0, 0, 0, 0, 0} (Matrix.fromBlocks.{0, 0, 0, 0, 0} 0 A B 0)
        (⇑(Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} σ))) id.{1}))
    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} κo)) (Matrix.det.{0, 0} A))
      (Matrix.det.{0, 0} B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.det_oriented_cross' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneMatrix_det`

theorem; source line 111.

Written type header:

```lean
theorem BasedIso.coneMatrix_det (I : BasedIso C D) (σ : κe ≃ κo) :
    ((fromBlocks D.dOE I.f.fO I.g.fE (-C.dEO)).submatrix (σ.sumCongr σ.symm) id).det =
      (-1 : K) ^ Fintype.card κo * I.f.fO.det * I.g.fE.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneMatrix_det : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : DecidableEq.{1} κe]
  [inst_4 : DecidableEq.{1} κo] {C D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  (I : ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso C D) (σ : Equiv.{1, 1} κe κo),
  Eq.{1}
    (Matrix.det.{0, 0}
      (Matrix.submatrix.{0, 0, 0, 0, 0}
        (Matrix.fromBlocks.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dOE.{0, 0, 0} D)
          (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} I.f)
          (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} I.g)
          (Neg.neg.{0} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0} C)))
        (⇑(Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} σ))) id.{1}))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} κo))
        (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} I.f)))
      (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} I.g)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.coneMatrix_det' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.cone_torsion`

theorem; source line 144.

Written type header:

```lean
theorem BasedIso.cone_torsion (I : BasedIso C D) (σ : κe ≃ κo) :
    torsion (BasedCx.cone I.f) (σ.sumCongr σ.symm) =
      (-1 : K) ^ Fintype.card κo * I.f.fO.det * I.g.fE.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.cone_torsion : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : DecidableEq.{1} κe]
  [inst_4 : DecidableEq.{1} κo] {C D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  (I : ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso C D) (σ : Equiv.{1, 1} κe κo),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} I.f)
      (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} σ)))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} κo))
        (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} I.f)))
      (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} I.g)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisForward`

def; source line 165.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisForward : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) →
                  ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C
                    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisForward' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisBackward`

def; source line 178.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisBackward : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) →
                  ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0}
                    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P) C
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisBackward' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisIso`

def; source line 190.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisIso : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) →
                  ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso C
                    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basis_cone_torsion`

theorem; source line 199.

Written type header:

```lean
theorem basis_cone_torsion (P : GradedBasisChange C) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (basisForward C P)) (σ.sumCongr σ.symm) =
      (-1 : K) ^ Fintype.card κo * P.Po.det * P.Qe.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basis_cone_torsion : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : DecidableEq.{1} κe]
  [inst_4 : DecidableEq.{1} κo] (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo)
  (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) (σ : Equiv.{1, 1} κe κo),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basisForward C P))
      (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} σ)))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} κo))
        (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Po.{0, 0, 0} P)))
      (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Qe.{0, 0, 0} P)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basis_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk`

abbrev; source line 215.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk : {K : Type} →
  [inst : Field.{0} K] →
    {ν : Type} →
      [inst_1 : Fintype.{0} ν] →
        [DecidableEq.{1} ν] → Matrix.{0, 0, 0} ν ν K → ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K ν ν
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basedIdentity`

def; source line 217.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basedIdentity : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [DecidableEq.{1} κe] →
            [DecidableEq.{1} κo] →
              (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} D D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basedIdentity' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.identityIso`

def; source line 225.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.identityIso : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso D D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.identityIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection`

def; source line 235.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo ν : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} ν] →
            [DecidableEq.{1} κe] →
              [DecidableEq.{1} κo] →
                [inst_6 : DecidableEq.{1} ν] →
                  (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                    (B : Matrix.{0, 0, 0} ν ν K) →
                      ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0}
                        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0} D
                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk B))
                        D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_reindex`

theorem; source line 259.

Written type header:

```lean
theorem splitProjection_cone_reindex :
    (BasedCx.cone (splitProjection D B)).reindex (Equiv.sumAssoc κe κo ν).symm
      (Equiv.sumAssoc κo κe ν).symm =
      (BasedCx.cone (basedIdentity D)).sum (diskM 0 (by decide) (-B))
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_reindex : ∀ {K : Type}
  [inst : Field.{0} K] {κe κo ν : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} ν]
  [inst_4 : DecidableEq.{1} κe] [inst_5 : DecidableEq.{1} κo] [inst_6 : DecidableEq.{1} ν]
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) (B : Matrix.{0, 0, 0} ν ν K),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.reindex.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection D B))
      (Equiv.symm.{1, 1} (Equiv.sumAssoc.{0, 0, 0} κe κo ν)) (Equiv.symm.{1, 1} (Equiv.sumAssoc.{0, 0, 0} κo κe ν)))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.basedIdentity D))
      (ZInQ.Contrib.CloudB3RC53.ClearingComplex.diskM.{0, 0} 0 (of_decide_eq_true (id.{0} (Eq.refl.{1} Bool.true)))
        (Neg.neg.{0} B)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_reindex' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_orientation`

theorem; source line 281.

Written type header:

```lean
theorem splitProjection_orientation (σ : κe ≃ κo) :
    (Equiv.sumAssoc κe κo ν).trans
      ((σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm).trans (Equiv.sumAssoc κo κe ν).symm) =
      (σ.sumCongr σ.symm).sumCongr (Equiv.refl ν)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_orientation : ∀ {κe κo ν : Type}
  (σ : Equiv.{1, 1} κe κo),
  Eq.{1}
    (Equiv.trans.{1, 1, 1} (Equiv.sumAssoc.{0, 0, 0} κe κo ν)
      (Equiv.trans.{1, 1, 1}
        (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.refl.{1} ν))))
        (Equiv.symm.{1, 1} (Equiv.sumAssoc.{0, 0, 0} κo κe ν))))
    (Equiv.sumCongr.{0, 0, 0, 0} (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} σ)) (Equiv.refl.{1} ν))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_orientation' depends on axioms: [propext,
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_torsion`

theorem; source line 290.

Written type header:

```lean
theorem splitProjection_cone_torsion (hB : IsUnit B.det) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (splitProjection D B))
      (σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm) =
      (-1 : K) ^ Fintype.card (κo ⊕ ν) * B.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_torsion : ∀ {K : Type}
  [inst : Field.{0} K] {κe κo ν : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} ν]
  [inst_4 : DecidableEq.{1} κe] [inst_5 : DecidableEq.{1} κo] [inst_6 : DecidableEq.{1} ν]
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) (B : Matrix.{0, 0, 0} ν ν K),
  IsUnit.{0} (Matrix.det.{0, 0} B) →
    ∀ (σ : Equiv.{1, 1} κe κo),
      Eq.{1}
        (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection D B))
          (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.refl.{1} ν)))))
        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} κo ν))) (Matrix.det.{0, 0} B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermForward`

def; source line 317.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermForward : {K : Type} →
  [inst : Field.{0} K] →
    {n : Nat} →
      (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K) →
        IsUnit.{0} (Matrix.det.{0, 0} Q) →
          ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D)
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} P D) Q))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermForward' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermBackward`

def; source line 328.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermBackward : {K : Type} →
  [inst : Field.{0} K] →
    {n : Nat} →
      (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K) →
        IsUnit.{0} (Matrix.det.{0, 0} P) →
          ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} P D) Q))
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermBackward' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_cycle`

theorem; source line 343.

Written type header:

```lean
theorem twoTerm_target_cycle : (P * D * Q) *ᵥ (Q⁻¹ *ᵥ z) = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_cycle : ∀ {K : Type} [inst : Field.{0} K]
  {n : Nat} (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K),
  IsUnit.{0} (Matrix.det.{0, 0} Q) →
    ∀ (z : Fin n → K),
      Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0 →
        Eq.{1}
          (Matrix.mulVec.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} P D) Q)
            (Matrix.mulVec.{0, 0, 0} (Inv.inv.{0} Q) z))
          0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_cycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_functional`

theorem; source line 349.

Written type header:

```lean
theorem twoTerm_target_functional : (w ᵥ* P⁻¹) ᵥ* (P * D * Q) = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_functional : ∀ {K : Type} [inst : Field.{0} K]
  {n : Nat} (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K),
  IsUnit.{0} (Matrix.det.{0, 0} P) →
    ∀ (w : Fin n → K),
      Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0 →
        Eq.{1}
          (Matrix.vecMul.{0, 0, 0} (Matrix.vecMul.{0, 0, 0} w (Inv.inv.{0} P))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} P D) Q))
          0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_functional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermAugIso`

def; source line 354.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermAugIso : {K : Type} →
  [inst : Field.{0} K] →
    {n : Nat} →
      (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K) →
        (hP : IsUnit.{0} (Matrix.det.{0, 0} P)) →
          (hQ : IsUnit.{0} (Matrix.det.{0, 0} Q)) →
            (z w : Fin n → K) →
              (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0) →
                (hw : Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0) →
                  ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso
                    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0}
                      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{0, 0, 0, 0, 0}
                        (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D) z w hz hw))
                    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0}
                      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{0, 0, 0, 0, 0}
                        (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} P D) Q))
                        (Matrix.mulVec.{0, 0, 0} (Inv.inv.{0} Q) z) (Matrix.vecMul.{0, 0, 0} w (Inv.inv.{0} P))
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_cycle D P Q hQ z hz)
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_target_functional D P Q hP w
                          hw)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermAugIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_cone_torsion`

theorem; source line 386.

Written type header:

```lean
theorem twoTerm_basis_cone_torsion :
    torsion (BasedCx.cone (twoTermAugIso D P Q hP hQ z w hz hw).f)
      ((σ₀ n).sumCongr (σ₀ n).symm) =
      (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) * (P.det * Q.det)⁻¹
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_cone_torsion : ∀ {K : Type} [inst : Field.{0} K]
  {n : Nat} (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K) (hP : IsUnit.{0} (Matrix.det.{0, 0} P))
  (hQ : IsUnit.{0} (Matrix.det.{0, 0} Q)) (z w : Fin n → K) (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0)
  (hw : Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermAugIso D P Q hP hQ z w hz hw).f)
      (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ n)
        (Equiv.symm.{1, 1} (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ n))))
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} (Fin n) (Sum.{0, 0} Empty Unit))))
      (Inv.inv.{0} (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} P) (Matrix.det.{0, 0} Q))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_factor`

theorem; source line 406.

Written type header:

```lean
theorem twoTerm_basis_factor :
    (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) *
      (torsion (BasedCx.cone (twoTermAugIso D P Q hP hQ z w hz hw).f)
        ((σ₀ n).sumCongr (σ₀ n).symm))⁻¹ = P.det * Q.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_factor : ∀ {K : Type} [inst : Field.{0} K]
  {n : Nat} (D P Q : Matrix.{0, 0, 0} (Fin n) (Fin n) K) (hP : IsUnit.{0} (Matrix.det.{0, 0} P))
  (hQ : IsUnit.{0} (Matrix.det.{0, 0} Q)) (z w : Fin n → K) (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0)
  (hw : Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0),
  Eq.{1}
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} (Fin n) (Sum.{0, 0} Empty Unit))))
      (Inv.inv.{0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTermAugIso D P Q hP hQ z w hz hw).f)
          (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ n)
            (Equiv.symm.{1, 1} (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ n))))))
    (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} P) (Matrix.det.{0, 0} Q))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.twoTerm_basis_factor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource`

def; source line 424.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo κe' κo' : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} κe'] →
            [inst_4 : Fintype.{0} κo'] →
              {C C' : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'} →
                  Eq.{1} C C' →
                    ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C' D →
                      ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource_cone`

theorem; source line 432.

Written type header:

```lean
theorem transportSource_cone (h : C = C') (f : ChainMapB C' D)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion (BasedCx.cone (transportSource h f)) (σD.sumCongr σC.symm) =
      torsion (BasedCx.cone f) (σD.sumCongr σC.symm)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource_cone : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo κe' κo' : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} κe']
  [inst_4 : Fintype.{0} κo'] [inst_5 : DecidableEq.{1} κe] [inst_6 : DecidableEq.{1} κo] [inst_7 : DecidableEq.{1} κe']
  [inst_8 : DecidableEq.{1} κo'] {C C' : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'} (h : Eq.{1} C C')
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C' D) (σD : Equiv.{1, 1} κe' κo')
  (σC : Equiv.{1, 1} κe κo),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource h f))
      (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} f)
      (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource_cone' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainMap_ext`

theorem; source line 440.

Written type header:

```lean
theorem chainMap_ext {f g : ChainMapB C D} (hE : f.fE = g.fE) (hO : f.fO = g.fO) : f = g
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainMap_ext : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo κe' κo' : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} κe']
  [inst_4 : Fintype.{0} κo'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'}
  {f g : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D},
  Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} f)
      (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} g) →
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} f)
        (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} g) →
      Eq.{1} f g
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainMap_ext' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainComp`

def; source line 447.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainComp : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo κe' κo' : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} κe'] →
            [inst_4 : Fintype.{0} κo'] →
              {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'} →
                  {κe'' κo'' : Type} →
                    [inst_5 : Fintype.{0} κe''] →
                      [inst_6 : Fintype.{0} κo''] →
                        [DecidableEq.{1} κe''] →
                          [DecidableEq.{1} κo''] →
                            {T : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe'' κo''} →
                              ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D →
                                ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} D T →
                                  ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C T
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.chainComp' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased`

def; source line 460.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo κe' κo' : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} κe'] →
            [inst_4 : Fintype.{0} κo'] →
              [inst_5 : DecidableEq.{1} κe] →
                [inst_6 : DecidableEq.{1} κo] →
                  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                    {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'} →
                      ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D →
                        (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) →
                          ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0}
                            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P) D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis`

def; source line 481.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo κe' κo' : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} κe'] →
            [inst_4 : Fintype.{0} κo'] →
              [inst_5 : DecidableEq.{1} κe] →
                [inst_6 : DecidableEq.{1} κo] →
                  [inst_7 : DecidableEq.{1} κe'] →
                    [inst_8 : DecidableEq.{1} κo'] →
                      {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                        {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'} →
                          (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D) →
                            ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C →
                              ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0}
                                (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} f)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis_rebase`

theorem; source line 518.

Written type header:

```lean
theorem sourceConeBasis_rebase (f : ChainMapB C D) (P : GradedBasisChange C) :
    (BasedCx.cone f).rebase (sourceConeBasis f P) = BasedCx.cone (sourceRebased f P)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis_rebase : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo κe' κo' : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} κe']
  [inst_4 : Fintype.{0} κo'] [inst_5 : DecidableEq.{1} κe] [inst_6 : DecidableEq.{1} κo] [inst_7 : DecidableEq.{1} κe']
  [inst_8 : DecidableEq.{1} κo'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'}
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D)
  (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} f)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis f P))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased f P))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceConeBasis_rebase' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.source_basis_cone_torsion`

theorem; source line 534.

Written type header:

```lean
theorem source_basis_cone_torsion (f : ChainMapB C D) (P : GradedBasisChange C)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion (BasedCx.cone (sourceRebased f P)) (σD.sumCongr σC.symm) =
      P.Pe.det * torsion (BasedCx.cone f) (σD.sumCongr σC.symm) * P.Qo.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.source_basis_cone_torsion : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo κe' κo' : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} κe']
  [inst_4 : Fintype.{0} κo'] [inst_5 : DecidableEq.{1} κe] [inst_6 : DecidableEq.{1} κo] [inst_7 : DecidableEq.{1} κe']
  [inst_8 : DecidableEq.{1} κo'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe' κo'}
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D)
  (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) (σD : Equiv.{1, 1} κe' κo')
  (σC : Equiv.{1, 1} κe κo),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased f P))
      (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Pe.{0, 0, 0} P))
        (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0} f)
          (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC))))
      (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Qo.{0, 0, 0} P)))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.source_basis_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection`

def; source line 552.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo ν : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : Fintype.{0} ν] →
            [inst_4 : DecidableEq.{1} κe] →
              [inst_5 : DecidableEq.{1} κo] →
                [inst_6 : DecidableEq.{1} ν] →
                  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} κe ν) (Sum.{0, 0} κo ν)) →
                    (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) →
                      (B : Matrix.{0, 0, 0} ν ν K) →
                        (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C) →
                          Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P)
                              (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0} D
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk B)) →
                            ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_source`

theorem; source line 555.

Written type header:

```lean
theorem rebasedProjection_source :
    sourceRebased (rebasedProjection C D B P hsplit) P = transportSource hsplit (splitProjection D B)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_source : ∀ {K : Type} [inst : Field.{0} K]
  {κe κo ν : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} ν]
  [inst_4 : DecidableEq.{1} κe] [inst_5 : DecidableEq.{1} κo] [inst_6 : DecidableEq.{1} ν]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} κe ν) (Sum.{0, 0} κo ν))
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) (B : Matrix.{0, 0, 0} ν ν K)
  (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C)
  (hsplit :
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P)
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0} D
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk B))),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.sourceRebased
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection C D B P hsplit) P)
    (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.transportSource hsplit
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.splitProjection D B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_source' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_cone_torsion`

theorem; source line 565.

Written type header:

```lean
theorem rebasedProjection_cone_torsion (hB : IsUnit B.det)
    (hPe : P.Pe.det = 1) (hQo : P.Qo.det = 1) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (rebasedProjection C D B P hsplit))
      (σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm) =
      (-1 : K) ^ Fintype.card (κo ⊕ ν) * B.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_cone_torsion : ∀ {K : Type}
  [inst : Field.{0} K] {κe κo ν : Type} [inst_1 : Fintype.{0} κe] [inst_2 : Fintype.{0} κo] [inst_3 : Fintype.{0} ν]
  [inst_4 : DecidableEq.{1} κe] [inst_5 : DecidableEq.{1} κo] [inst_6 : DecidableEq.{1} ν]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} κe ν) (Sum.{0, 0} κo ν))
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo) (B : Matrix.{0, 0, 0} ν ν K)
  (P : ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C)
  (hsplit :
    Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C P)
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0} D
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk B))),
  IsUnit.{0} (Matrix.det.{0, 0} B) →
    Eq.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Pe.{0, 0, 0} P)) 1 →
      Eq.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Qo.{0, 0, 0} P)) 1 →
        ∀ (σ : Equiv.{1, 1} κe κo),
          Eq.{1}
            (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
              (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection C D B P hsplit))
              (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.symm.{1, 1} (Equiv.sumCongr.{0, 0, 0, 0} σ (Equiv.refl.{1} ν)))))
            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} κo ν))) (Matrix.det.{0, 0} B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.rebasedProjection_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis`

def; source line 588.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis : {K : Type} →
  [inst : Field.{0} K] →
    {α β ν : Type} →
      [inst_1 : Fintype.{0} α] →
        [inst_2 : Fintype.{0} β] →
          [inst_3 : Fintype.{0} ν] →
            [inst_4 : DecidableEq.{1} α] →
              [inst_5 : DecidableEq.{1} β] →
                [inst_6 : DecidableEq.{1} ν] →
                  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} α ν) (Sum.{0, 0} β ν)) →
                    (∀ (v : ν),
                        Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degO.{0, 0, 0} C (Sum.inr.{0, 0} v)) 1) →
                      (∀ (v : ν),
                          Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degE.{0, 0, 0} C (Sum.inr.{0, 0} v)) 2) →
                        ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.{0, 0, 0} C
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_even_det`

theorem; source line 622.

Written type header:

```lean
theorem oddCancelBasis_even_det : (oddCancelBasis C ho he).Pe.det = 1
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_even_det : ∀ {K : Type} [inst : Field.{0} K]
  {α β ν : Type} [inst_1 : Fintype.{0} α] [inst_2 : Fintype.{0} β] [inst_3 : Fintype.{0} ν] [inst_4 : DecidableEq.{1} α]
  [inst_5 : DecidableEq.{1} β] [inst_6 : DecidableEq.{1} ν]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} α ν) (Sum.{0, 0} β ν))
  (ho : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degO.{0, 0, 0} C (Sum.inr.{0, 0} v)) 1)
  (he : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degE.{0, 0, 0} C (Sum.inr.{0, 0} v)) 2),
  Eq.{1}
    (Matrix.det.{0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Pe.{0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis C ho he)))
    1
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_even_det' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_inverse_odd_det`

theorem; source line 626.

Written type header:

```lean
theorem oddCancelBasis_inverse_odd_det : (oddCancelBasis C ho he).Qo.det = 1
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_inverse_odd_det : ∀ {K : Type}
  [inst : Field.{0} K] {α β ν : Type} [inst_1 : Fintype.{0} α] [inst_2 : Fintype.{0} β] [inst_3 : Fintype.{0} ν]
  [inst_4 : DecidableEq.{1} α] [inst_5 : DecidableEq.{1} β] [inst_6 : DecidableEq.{1} ν]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} α ν) (Sum.{0, 0} β ν))
  (ho : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degO.{0, 0, 0} C (Sum.inr.{0, 0} v)) 1)
  (he : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degE.{0, 0, 0} C (Sum.inr.{0, 0} v)) 2),
  Eq.{1}
    (Matrix.det.{0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Qo.{0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis C ho he)))
    1
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_inverse_odd_det' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_split`

theorem; source line 631.

Written type header:

```lean
theorem oddCancelBasis_split :
    C.rebase (oddCancelBasis C ho he) = (schurO C 1 ho he hB).sum (oddMatrixDisk C.dEO.toBlocks₂₂)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_split : ∀ {K : Type} [inst : Field.{0} K]
  {α β ν : Type} [inst_1 : Fintype.{0} α] [inst_2 : Fintype.{0} β] [inst_3 : Fintype.{0} ν] [inst_4 : DecidableEq.{1} α]
  [inst_5 : DecidableEq.{1} β] [inst_6 : DecidableEq.{1} ν]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} α ν) (Sum.{0, 0} β ν))
  (ho : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degO.{0, 0, 0} C (Sum.inr.{0, 0} v)) 1)
  (he : ∀ (v : ν), Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degE.{0, 0, 0} C (Sum.inr.{0, 0} v)) 2)
  (hB :
    IsUnit.{0}
      (Matrix.det.{0, 0}
        (Matrix.toBlocks₂₂.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0} C)))),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0} C
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis C ho he))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.ClearingComplex.schurO.{0, 0, 0, 0} C 1 ho he hB)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk
        (Matrix.toBlocks₂₂.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0} C))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis_split' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD1Decidable`

instance; source line 657.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD1Decidable : {K : Type} →
  [inst : Field.{0} K] → {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} → DecidableEq.{1} C.D1
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD1Decidable' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD2Decidable`

instance; source line 658.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD2Decidable : {K : Type} →
  [inst : Field.{0} K] → {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} → DecidableEq.{1} C.D2
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullD2Decidable' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullNDecidable`

instance; source line 659.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullNDecidable : {K : Type} →
  [inst : Field.{0} K] → {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} → DecidableEq.{1} C.N
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullNDecidable' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullRemaining`

abbrev; source line 662.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullRemaining : {K : Type} →
  [inst : Field.{0} K] →
    {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) →
        (z : Sum.{0, 0} C.D1 C.N → K) →
          (lam : Sum.{0, 0} C.D2 C.N → K) →
            Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0 →
              Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour))
                  0 →
                ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K (Sum.{0, 0} (Sum.{0, 0} (Fin C.m0) Unit) C.D2)
                  (Sum.{0, 0} C.D1 (Sum.{0, 0} (Fin C.m2) Unit))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullRemaining' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.full_actual_split`

theorem; source line 666.

Written type header:

```lean
theorem full_actual_split :
    (Xf z lam hz hlam).rebase (oddCancelBasis (Xf z lam hz hlam)
      (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam)) =
      (fullRemaining hB z lam hz hlam).sum (oddMatrixDisk C.B)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.full_actual_split : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B))
  (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf z lam hz hlam)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddCancelBasis
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf z lam hz hlam)
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf_degO z lam hz hlam)
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf_degE z lam hz hlam)))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.sum.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullRemaining hB z lam hz hlam)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.oddMatrixDisk C.B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.full_actual_split' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection`

def; source line 677.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection : {K : Type} →
  [inst : Field.{0} K] →
    {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} →
      (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) →
        (z : Sum.{0, 0} C.D1 C.N → K) →
          (lam : Sum.{0, 0} C.D2 C.N → K) →
            (hz :
                Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z)
                  0) →
              (hlam :
                  Eq.{1}
                    (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour))
                    0) →
                ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0}
                  (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf z lam hz hlam)
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.fullRemaining hB z lam hz hlam)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_cone_torsion`

theorem; source line 685.

Written type header:

```lean
theorem actualFullProjection_cone_torsion :
    torsion (BasedCx.cone (actualFullProjection hB z lam hz hlam))
      ((σBlock C.m0 C.m1 C.m2).sumCongr
        ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl C.N)).symm) =
      (-1 : K) ^ Fintype.card ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) * C.B.det
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_cone_torsion : ∀ {K : Type}
  [inst : Field.{0} K] {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection hB z lam hz hlam))
      (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.σBlock C.m0 C.m1 C.m2)
        (Equiv.symm.{1, 1}
          (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.σBlock C.m0 C.m1 C.m2)
            (Equiv.refl.{1} C.N)))))
    (HMul.hMul.{0, 0, 0}
      (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} (Sum.{0, 0} C.D1 (Sum.{0, 0} (Fin C.m2) Unit)) C.N)))
      (Matrix.det.{0, 0} C.B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_cone_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_even_matrix`

theorem; source line 699.

Written type header:

```lean
theorem actualFullProjection_even_matrix :
    (actualFullProjection hB z lam hz hlam).fE =
      fromCols 1 (-((Xf z lam hz hlam).dEO.toBlocks₁₂ * C.B⁻¹))
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_even_matrix : ∀ {K : Type}
  [inst : Field.{0} K] {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection hB z lam hz hlam))
    (Matrix.fromCols.{0, 0, 0, 0} 1
      (Neg.neg.{0}
        (HMul.hMul.{0, 0, 0}
          (Matrix.toBlocks₁₂.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0}
              (ZInQ.Contrib.CloudB3RC53.ClearingComplex.Xf z lam hz hlam)))
          (Inv.inv.{0} C.B))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_even_matrix' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_odd_matrix`

theorem; source line 708.

Written type header:

```lean
theorem actualFullProjection_odd_matrix : (actualFullProjection hB z lam hz hlam).fO = fromCols 1 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_odd_matrix : ∀ {K : Type}
  [inst : Field.{0} K] {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection hB z lam hz hlam))
    (Matrix.fromCols.{0, 0, 0, 0} 1 0)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_odd_matrix' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_factor`

theorem; source line 716.

Written type header:

```lean
theorem actualFullProjection_factor :
    (-1 : K) ^ Fintype.card ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) *
      (torsion (BasedCx.cone (actualFullProjection hB z lam hz hlam))
        ((σBlock C.m0 C.m1 C.m2).sumCongr
          ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl C.N)).symm))⁻¹ = C.B.det⁻¹
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_factor : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.FullPreComplex K} (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B))
  (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} (Sum.{0, 0} C.D1 (Sum.{0, 0} (Fin C.m2) Unit)) C.N)))
      (Inv.inv.{0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection hB z lam hz hlam))
          (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.σBlock C.m0 C.m1 C.m2)
            (Equiv.symm.{1, 1}
              (Equiv.sumCongr.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.σBlock C.m0 C.m1 C.m2)
                (Equiv.refl.{1} C.N)))))))
    (Inv.inv.{0} (Matrix.det.{0, 0} C.B))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.actualFullProjection_factor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.mk`

Record constructor.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.mk : {K : Type} →
  [inst : Field.{0} K] →
    {κe κo : Type} →
      [inst_1 : Fintype.{0} κe] →
        [inst_2 : Fintype.{0} κo] →
          [inst_3 : DecidableEq.{1} κe] →
            [inst_4 : DecidableEq.{1} κo] →
              {C D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K κe κo} →
                (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} C D) →
                  (g : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{0, 0, 0, 0, 0} D C) →
                    Eq.{1}
                        (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} f)
                          (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} g))
                        1 →
                      Eq.{1}
                          (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} f)
                            (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} g))
                          1 →
                        Eq.{1}
                            (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} g)
                              (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fE.{0, 0, 0, 0, 0} f))
                            1 →
                          Eq.{1}
                              (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} g)
                                (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.fO.{0, 0, 0, 0, 0} f))
                              1 →
                            ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso C D
```

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant.BasedIso.mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# FibreEndpoint.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K`

abbrev; source line 35.

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K : Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.finiteCore`

def; source line 41.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.finiteCore : {ι : Type} →
  [inst : Fintype.{0} ι] →
    Matrix.{0, 0, 0} ι ι ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K →
      ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
        Empty ι ι Empty
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.finiteCore' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative`

def; source line 61.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                  (zActual :
                      ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                    Eq.{1}
                        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                          zActual)
                        0 →
                      Sum.{0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).D1
                          (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).N →
                        MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                          (ZInQ.Manuscript.RC.Determinant.SignGroup b)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_closed`

theorem; source line 65.

Written type header:

```lean
theorem actualClassRepresentative_closed :
    (M.C.map (φO b)).toFour.d1 *ᵥ actualClassRepresentative M zActual hzActual = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_closed : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0),
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
        (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).toFour)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative M zActual hzActual))
    0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_readback`

theorem; source line 69.

Written type header:

```lean
theorem actualClassRepresentative_readback :
    ∃ a : (familyCx M).X 0,
      modelMap1 M (actualClassRepresentative M zActual hzActual) - zActual =
        (familyCx M).d 0 1 rfl a
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_readback : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0),
  Exists.{1}
    fun
      (a :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0)) =>
    Eq.{1}
      (HSub.hSub.{0, 0, 0}
        ((ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.modelMap1 M)
          (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative M zActual hzActual))
        zActual)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 0 1 rfl.{1})
        a)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.actualClassRepresentative_readback' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx`

abbrev; source line 76.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                  ZInQ.Manuscript.RC.Addr b →
                    ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0}
                      ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K (Fin M.C.m0) (Sum.{0, 0} M.C.D1 M.C.N)
                      (Sum.{0, 0} M.C.D2 M.C.N) (Fin M.C.m2)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass`

abbrev; source line 80.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                  (zActual :
                      ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                    Eq.{1}
                        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                            (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
                          zActual)
                        0 →
                      ZInQ.Manuscript.RC.Addr b →
                        Sum.{0, 0} M.C.D1 M.C.N → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass_closed`

theorem; source line 83.

Written type header:

```lean
theorem sourceClass_closed (x : ZInQ.Manuscript.RC.Addr b) :
    (sourceCx M x).d1 *ᵥ sourceClass M zActual hzActual x = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass_closed : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  (x : ZInQ.Manuscript.RC.Addr b),
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass M zActual hzActual x))
    0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix`

abbrev; source line 108.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix : {A R : Type} →
  [inst : CommRing.{0} A] →
    [inst_1 : CommRing.{0} R] →
      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
        {q qi a z zi uP uR eps : A} →
          {unitR unitP : A → Prop} →
            (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP) →
              (fScalar : RingHom.{0, 0} R A) →
                RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K →
                  ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar →
                    Matrix.{0, 0, 0} s.Index s.Index ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass`

abbrev; source line 109.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass : {A R : Type} →
  [inst : CommRing.{0} A] →
    [inst_1 : CommRing.{0} R] →
      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
        {q qi a z zi uP uR eps : A} →
          {unitR unitP : A → Prop} →
            (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP) →
              (fScalar : RingHom.{0, 0} R A) →
                RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K →
                  ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar →
                    s.Index → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow`

abbrev; source line 110.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow : {A R : Type} →
  [inst : CommRing.{0} A] →
    [inst_1 : CommRing.{0} R] →
      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
        {q qi a z zi uP uR eps : A} →
          {unitR unitP : A → Prop} →
            (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP) →
              (fScalar : RingHom.{0, 0} R A) →
                RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K →
                  ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar →
                    s.Index → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow`

abbrev; source line 111.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK) →
                  {Dp :
                      ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                          (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                    (P :
                        ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp) →
                      LinearMap.{0, 0, 0, 0}
                          (RingHom.id.{0}
                            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                              (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                          (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                              3))
                          (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                            (ZInQ.Manuscript.RC.Determinant.SignGroup b)) →
                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1) →
                          ZInQ.Manuscript.RC.Addr b →
                            Sum.{0, 0} M.C.D2 M.C.N → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow_closed`

theorem; source line 115.

Written type header:

```lean
theorem sourceRow_closed (x : ZInQ.Manuscript.RC.Addr b) : sourceRow M P tr zc x ᵥ* (sourceCx M x).d1 = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow_closed : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  (∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0) →
    ∀
      (zc :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
              1 2 rfl.{1})
            zc)
          0 →
        ∀ (x : ZInQ.Manuscript.RC.Addr b),
          Eq.{1}
            (Matrix.vecMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow M P tr zc x)
              (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x)))
            0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding`

structure; source line 121.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {A R : Type} →
                  [inst_4 : CommRing.{0} A] →
                    [inst_5 : CommRing.{0} R] →
                      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
                        {q qi a z zi uP uR eps : A} →
                          {unitR unitP : A → Prop} →
                            (s :
                                ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps
                                  unitR unitP) →
                              (fScalar : RingHom.{0, 0} R A) →
                                RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K →
                                  ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar →
                                    ZInQ.Manuscript.RC.Addr b →
                                      (M :
                                          ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE
                                            tK) →
                                        (zActual :
                                            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                          Eq.{1}
                                              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2
                                                  rfl.{1})
                                                zActual)
                                              0 →
                                            {Dp :
                                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                                  (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                    (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                              (P :
                                                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M)
                                                    Dp) →
                                                (tr :
                                                    LinearMap.{0, 0, 0, 0}
                                                      (RingHom.id.{0}
                                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                                      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                              P))
                                                          3))
                                                      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                        (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                                  (∀
                                                      (c :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                P))
                                                            2)),
                                                      Eq.{1}
                                                        (tr
                                                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                  P))
                                                              2 3 rfl.{1})
                                                            c))
                                                        0) →
                                                    (zc :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
                                                            1)) →
                                                      Eq.{1}
                                                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1
                                                              2 rfl.{1})
                                                            zc)
                                                          0 →
                                                        Type
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.comparison`

def; source line 144.

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.comparison : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {A R : Type} →
                  [inst_4 : CommRing.{0} A] →
                    [inst_5 : CommRing.{0} R] →
                      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
                        {q qi a z zi uP uR eps : A} →
                          {unitR unitP : A → Prop} →
                            (s :
                                ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps
                                  unitR unitP) →
                              (fScalar : RingHom.{0, 0} R A) →
                                (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K) →
                                  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) →
                                    (x : ZInQ.Manuscript.RC.Addr b) →
                                      (M :
                                          ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE
                                            tK) →
                                        (zActual :
                                            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)) →
                                          (hzActual :
                                              Eq.{1}
                                                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2
                                                    rfl.{1})
                                                  zActual)
                                                0) →
                                            {Dp :
                                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                                  (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                    (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                              (P :
                                                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M)
                                                    Dp) →
                                                (tr :
                                                    LinearMap.{0, 0, 0, 0}
                                                      (RingHom.id.{0}
                                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                                      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                              P))
                                                          3))
                                                      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                        (ZInQ.Manuscript.RC.Determinant.SignGroup b))) →
                                                  (htr :
                                                      ∀
                                                        (c :
                                                          ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                  P))
                                                              2)),
                                                        Eq.{1}
                                                          (tr
                                                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                    P))
                                                                2 3 rfl.{1})
                                                              c))
                                                          0) →
                                                    (zc :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
                                                            1)) →
                                                      (hzc :
                                                          Eq.{1}
                                                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
                                                                1 2 rfl.{1})
                                                              zc)
                                                            0) →
                                                        ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding
                                                            s fScalar g E x M zActual hzActual P tr htr zc hzc →
                                                          ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy.HomotopyComparison.{0,
                                                              0, 0, 0, 0, 0, 0, 0, 0}
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx
                                                              M x)
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.finiteCore
                                                              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix
                                                                s fScalar g E))
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass
                                                              M zActual hzActual x)
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow
                                                              M P tr zc x)
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass
                                                              s fScalar g E)
                                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow
                                                              s fScalar g E)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.readback`

theorem; source line 155.

Written type header:

```lean
theorem FibreBinding.readback (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) :
    E.D.map fScalar = s.DR ∧ fScalar ∘ E.z = s.zR ∧ fScalar ∘ E.w = s.wR ∧
      B.f.f1 *ᵥ sourceClass M zActual hzActual x = targetClass s fScalar g E ∧
      targetRow s fScalar g E ᵥ* B.f.f2 = sourceRow M P tr zc x +
        B.functionalPrimitive ᵥ* (sourceCx M x).d2
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.readback : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc),
  And (Eq.{1} (Matrix.map.{0, 0, 0, 0} E.D ⇑fScalar) s.DR)
    (And (Eq.{1} (Function.comp.{1, 1, 1} (⇑fScalar) E.z) s.zR)
      (And (Eq.{1} (Function.comp.{1, 1, 1} (⇑fScalar) E.w) s.wR)
        (And
          (Eq.{1}
            (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{0, 0, 0, 0, 0, 0, 0, 0, 0} B.f)
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass M zActual hzActual x))
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass s fScalar g E))
          (Eq.{1}
            (Matrix.vecMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow s fScalar g E)
              (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{0, 0, 0, 0, 0, 0, 0, 0, 0} B.f))
            (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow M P tr zc x)
              (Matrix.vecMul.{0, 0, 0} B.functionalPrimitive
                (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0, 0, 0, 0, 0}
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))))))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.readback' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.fixed_fractional_coordinate`

theorem; source line 165.

Written type header:

```lean
theorem FibreBinding.fixed_fractional_coordinate [IsDomain A]
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (hlocal : (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F q z zi).det ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ fScalar den * uR = fScalar num ∧
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn (targetMatrix s fScalar g E)
        (targetClass s fScalar g E) (targetRow s fScalar g E) (g num / g den)
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.fixed_fractional_coordinate : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  [IsDomain.{0} A]
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc),
  Ne.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock.{0} F q z zi)) 0 →
    Exists.{1} fun (num : R) =>
      Exists.{1} fun (den : R) =>
        And (Ne.{1} den 0)
          (And (Eq.{1} (HMul.hMul.{0, 0, 0} (fScalar den) uR) (fScalar num))
            (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix s fScalar g E)
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass s fScalar g E)
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow s fScalar g E)
              (HDiv.hDiv.{0, 0, 0} (g num) (g den))))
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.fixed_fractional_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_class_forces_native_boundary`

theorem; source line 181.

Written type header:

```lean
theorem FibreBinding.zero_class_forces_native_boundary
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) (hz : E.z = 0) :
    ∃ c : Fin M.C.m0 → K, sourceClass M zActual hzActual x = (sourceCx M x).d0 *ᵥ c
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_class_forces_native_boundary : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc),
  Eq.{1} E.z 0 →
    Exists.{1} fun (c : Fin M.C.m0 → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K) =>
      Eq.{1} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass M zActual hzActual x)
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))
          c)
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_class_forces_native_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.class_not_zero`

theorem; source line 203.

Written type header:

```lean
theorem FibreBinding.class_not_zero
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (hne : ∀ c : Fin M.C.m0 → K, sourceClass M zActual hzActual x ≠ (sourceCx M x).d0 *ᵥ c) :
    E.z ≠ 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.class_not_zero : ∀ {N : Type} [inst : Field.{0} N]
  [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc),
  (∀ (c : Fin M.C.m0 → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K),
      Ne.{1} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass M zActual hzActual x)
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))
          c)) →
    Ne.{1} E.z 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.class_not_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_row_kills_native_cycles`

theorem; source line 213.

Written type header:

```lean
theorem FibreBinding.zero_row_kills_native_cycles
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc) (hw : E.w = 0)
    (v : M.C.D2 ⊕ M.C.N → K) (hv : (sourceCx M x).d2 *ᵥ v = 0) :
    sourceRow M P tr zc x ⬝ᵥ v = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_row_kills_native_cycles : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc),
  Eq.{1} E.w 0 →
    ∀ (v : Sum.{0, 0} M.C.D2 M.C.N → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K),
      Eq.{1}
          (Matrix.mulVec.{0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0, 0, 0, 0, 0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))
            v)
          0 →
        Eq.{1} (dotProduct.{0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow M P tr zc x) v) 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.zero_row_kills_native_cycles' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.scalar_zero_of_native_boundary`

theorem; source line 228.

Written type header:

```lean
theorem FibreBinding.scalar_zero_of_native_boundary [IsDomain A]
    (B : FibreBinding s fScalar g E x M zActual hzActual P tr htr zc hzc)
    (c : Fin M.C.m0 → K)
    (hc : sourceClass M zActual hzActual x = (sourceCx M x).d0 *ᵥ c)
    (hlocal : (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock F q z zi).det ≠ 0) : uR = 0
```

Elaborated type:

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.scalar_zero_of_native_boundary : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : LE.le.{0} S S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {b dK hK cE tK : Nat} {A R : Type}
  [inst_4 : CommRing.{0} A] [inst_5 : CommRing.{0} R] {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A}
  {q qi a z zi uP uR eps : A} {unitR unitP : A → Prop}
  (s : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps unitR unitP)
  (fScalar : RingHom.{0, 0} R A) (g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K)
  (E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar) (x : ZInQ.Manuscript.RC.Addr b)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE tK)
  (zActual :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1))
  (hzActual :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2 rfl.{1})
        zActual)
      0)
  {Dp :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))}
  (P :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M) Dp)
  (tr :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (htr :
    ∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 rfl.{1})
            c))
        0)
  (zc :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1))
  (hzc :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp) 1 2
          rfl.{1})
        zc)
      0)
  [IsDomain.{0} A]
  (B :
    ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding s fScalar g E x M zActual hzActual P tr htr zc
      hzc)
  (c : Fin M.C.m0 → ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K),
  Eq.{1} (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass M zActual hzActual x)
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx M x))
        c) →
    Ne.{1} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.CommonCoordinate.twoPlaceBlock.{0} F q z zi)) 0 → Eq.{1} uR 0
```

Individual axiom report:

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.scalar_zero_of_native_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.mk`

Record constructor.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.mk : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : LE.le.{0} S S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {b dK hK cE tK : Nat} →
                {A R : Type} →
                  [inst_4 : CommRing.{0} A] →
                    [inst_5 : CommRing.{0} R] →
                      {F : Matrix.{0, 0, 0} (Fin 2) (Fin 2) A} →
                        {q qi a z zi uP uR eps : A} →
                          {unitR unitP : A → Prop} →
                            {s :
                                ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.StepData F q qi a z zi uP uR eps
                                  unitR unitP} →
                              {fScalar : RingHom.{0, 0} R A} →
                                {g : RingHom.{0, 0} R ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K} →
                                  {E : ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint.CommonLift s fScalar} →
                                    {x : ZInQ.Manuscript.RC.Addr b} →
                                      {M :
                                          ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification3 N S S' hS b dK hK cE
                                            tK} →
                                        {zActual :
                                            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1)} →
                                          {hzActual :
                                              Eq.{1}
                                                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyCx M) 1 2
                                                    rfl.{1})
                                                  zActual)
                                                0} →
                                            {Dp :
                                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0}
                                                  (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                    (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                              {P :
                                                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull.familyData M)
                                                    Dp} →
                                                {tr :
                                                    LinearMap.{0, 0, 0, 0}
                                                      (RingHom.id.{0}
                                                        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                          (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
                                                      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                              P))
                                                          3))
                                                      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                                        (ZInQ.Manuscript.RC.Determinant.SignGroup b))} →
                                                  {htr :
                                                      ∀
                                                        (c :
                                                          ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                  P))
                                                              2)),
                                                        Eq.{1}
                                                          (tr
                                                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                                                                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                                                                    P))
                                                                2 3 rfl.{1})
                                                              c))
                                                          0} →
                                                    {zc :
                                                        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                                            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
                                                            1)} →
                                                      {hzc :
                                                          Eq.{1}
                                                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                                                                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} Dp)
                                                                1 2 rfl.{1})
                                                              zc)
                                                            0} →
                                                        Function.Injective.{1, 1} ⇑fScalar →
                                                          Function.Injective.{1, 1} ⇑g →
                                                            (f :
                                                                ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0,
                                                                    0, 0, 0, 0}
                                                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx
                                                                    M x)
                                                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.finiteCore
                                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix
                                                                      s fScalar g E))) →
                                                              QuasiIso.{0, 1, 0}
                                                                  (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy.quadMap
                                                                      f)) →
                                                                Eq.{1}
                                                                    (Matrix.mulVec.{0, 0, 0}
                                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix
                                                                        s fScalar g E)
                                                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass
                                                                        s fScalar g E))
                                                                    0 →
                                                                  Eq.{1}
                                                                      (Matrix.vecMul.{0, 0, 0}
                                                                        (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow
                                                                          s fScalar g E)
                                                                        (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetMatrix
                                                                          s fScalar g E))
                                                                      0 →
                                                                    Eq.{1}
                                                                        (Matrix.mulVec.{0, 0, 0}
                                                                          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{0,
                                                                              0, 0, 0, 0, 0, 0, 0, 0}
                                                                            f)
                                                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceClass
                                                                            M zActual hzActual x))
                                                                        (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetClass
                                                                          s fScalar g E) →
                                                                      (functionalPrimitive :
                                                                          Fin M.C.m2 →
                                                                            ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.K) →
                                                                        Eq.{1}
                                                                            (Matrix.vecMul.{0, 0, 0}
                                                                              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.targetRow
                                                                                s fScalar g E)
                                                                              (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{0,
                                                                                  0, 0, 0, 0, 0, 0, 0, 0}
                                                                                f))
                                                                            (HAdd.hAdd.{0, 0, 0}
                                                                              (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceRow
                                                                                M P tr zc x)
                                                                              (Matrix.vecMul.{0, 0, 0}
                                                                                functionalPrimitive
                                                                                (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0,
                                                                                    0, 0, 0, 0}
                                                                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.sourceCx
                                                                                    M x)))) →
                                                                          ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding
                                                                            s fScalar g E x M zActual hzActual P tr htr
                                                                            zc hzc
```

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint.FibreBinding.mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

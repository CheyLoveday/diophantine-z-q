import Research.DerivativeSwitch.ConjugateLocalH1

/-!
# Unspecialized tame transport on genuine first group cohomology

This uses the existing representation-derived transport and Mathlib's H¹
projection. It adds no assumed normalization or coefficient-system equality.
-/

namespace Research.DerivativeSwitch.ConjugateLocalTransport.LocalData

open groupCohomology

universe u
variable {R G V : Type u} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V]
  {H : Subgroup G} [H.Normal] {T : G →* Module.End R V} {alpha : H →* Rˣ}

theorem h1_local_transport_tame (D : LocalData H T alpha)
    (z : H1 (Rep.of (twist H T alpha))) :
    D.conjugateH1Coordinates
        (h1Pullback (twist H T alpha) (conjugation H D.tau) z) =
      ((D.transportUnit : R) • (D.h1Coordinates z).1,
       (D.transportUnit : R) • ((D.ell : R) • (D.h1Coordinates z).2)) := by
  induction z using H1_induction_on with
  | h p =>
    rw [h1Pullback_projection, D.conjugateH1Coordinates_projection,
      D.h1Coordinates_projection]
    apply D.coordinates_rawConjugate p
    intro g h
    have hp := (mem_cocycles₁_iff _).mp p.2 g h
    change p.1 (g * h) = (twist H T alpha) g (p.1 h) + p.1 g at hp
    change p.1 (g * h) = p.1 g + (twist H T alpha) g (p.1 h)
    exact hp.trans (add_comm _ _)

end Research.DerivativeSwitch.ConjugateLocalTransport.LocalData

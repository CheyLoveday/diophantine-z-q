import ZInQKernel.Contrib.CloudB3E1RingClass.Inertia
import ZInQKernel.Contrib.CloudB3E2Norm.RingClassDelta

/-!
# The interface's `inertia_eq` for the genuine ring class field

Manuscript `diophantine_zq.tex`, tex 3679–3681.

The genuine moving data (`GenuineMovingData.lean`) take as input the GLUE field
`inertia_eq : setupInertia C r = (δ r v).range`. For the connecting map `δ = deltaR` at a split
prime (`RingClassDelta.lean`, whose exactness is `deltaR_exact_setup`) this holds as soon as the
chosen place over `r` lies over `r`:

* **`setupInertia_eq_ker_setupPi`** (PROVED): the genuine inertia group at the chosen place over a
  split prime `r` is the kernel of `π r : Gal(H_r/K) → Cl(K)`.
* **`setupInertia_eq_range_deltaR`** (PROVED): it is the range of `deltaR`.

Kinds: PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3E2.RingClassDelta

namespace ZInQ.Contrib.CloudB3E1RingClass

variable {K : Type} [Field K] [NumberField K] {s : ℕ}

/-- **The genuine inertia group of the setup at a split prime is `ker π`** (tex 3679–3681): for
`K` quadratic, `max r 1` prime and split as `𝔯 𝔯̄`, and the chosen place over `r` containing `r`.
Kind: PROVED. -/
theorem setupInertia_eq_ker_setupPi (C : RingClassSetup K s) {r : ℕ} (hr : (max r 1).Prime)
    (sp : SplitPair K (max r 1)) (hK : Module.finrank ℚ K = 2)
    (hover : ((max r 1 : ℕ) : 𝓞 K) ∈ (C.placeR r).asIdeal) :
    setupInertia C r = (setupPi C r).ker := by
  ext z
  have h : inertiaGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.placeR r) =
      (galToClassGroup (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)).ker :=
    inertiaGal_eq_ker_galToClassGroup_of_mem hK hr sp.ne sp.span_eq (C.Sr r) (C.hSr r) hover
  change Additive.toMul z ∈ inertiaGal (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
    (C.placeR r) ↔ _
  rw [h, MonoidHom.mem_ker, AddMonoidHom.mem_ker, setupPi, MonoidHom.toAdditive_apply_apply]
  constructor
  · intro h1
    rw [h1, ofMul_one]
  · intro h1
    exact (ofMul_eq_zero (A := ClassGroup (𝓞 K))).mp h1

/-- **The interface's `inertia_eq` for `δ = deltaR`** (tex 3679–3681): the genuine inertia group
at the chosen place over a split prime `r` is the range of the connecting map
`deltaR : 𝐅_r^× → Gal(H_r/K)`. Kind: PROVED. -/
theorem setupInertia_eq_range_deltaR (C : RingClassSetup K s) {r : ℕ} (hr : (max r 1).Prime)
    (sp : SplitPair K (max r 1)) (hK : Module.finrank ℚ K = 2)
    (hover : ((max r 1 : ℕ) : 𝓞 K) ∈ (C.placeR r).asIdeal) :
    setupInertia C r = (deltaR hr sp hK (C.Sr r) (C.hSr r)).range := by
  rw [setupInertia_eq_ker_setupPi C hr sp hK hover]
  ext z
  rw [AddMonoidHom.mem_ker, deltaR_exact_setup C hr sp hK z, AddMonoidHom.mem_range]

end ZInQ.Contrib.CloudB3E1RingClass

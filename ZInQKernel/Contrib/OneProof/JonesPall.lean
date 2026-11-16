import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.JonesPall.Representation

/-!
# Exact `hJP`: Jones–Pall's squarefree 1-mod-8 representation

The statement is the unchanged defining constant in `TYZLemma29Mod2`.
The proof imports that defining module, never `ZInQKernel.OneProof.Main`.

The helper proof uses the genuine Mathlib-only Atlas/Ankeny three-square
supplier, Mathlib's two-square criterion, and a new integral quaternion
annihilator descent. Source/license/change notices are in `JonesPall/`.
-/

namespace ZInQ.Contrib.OneProof.JonesPall

/-- Exactly the open `hJP` proposition, without additional hypotheses. -/
theorem jonesPall_proof : ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16 :=
  jonesPall_representation

end ZInQ.Contrib.OneProof.JonesPall

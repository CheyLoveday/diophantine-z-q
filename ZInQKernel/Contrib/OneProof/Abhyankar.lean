import ZInQKernel.Contrib.OneProof.Abhyankar.Assembly
import ZInQKernel.Contrib.OneProof.Abhyankar.Transport
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBase
import ZInQKernel.Contrib.OneProof.Abhyankar.EtaleBranch
import ZInQKernel.Contrib.OneProof.Abhyankar.Descent
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnram
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBranchFinal

/-!
# abhyankar: `SGRDirect.NVLocal.TameBranchNormal`

Task abhyankar (docs/research/abhyankar.md). `TameBranchNormal` (nv-local; `SGRDirectNVLocal.lean`) is the
dimension-two case of Abhyankar's lemma in the form "at a closed point of the normalization of a tame cover
of a regular surface germ, ramified only along `fg = 0`, the branch of `f = 0` is unique and normal".

Proved here (standard axioms): `tameBranchNormal_of_kummerUnram : KummerUnram → TameBranchNormal`, through
the named steps of `Abhyankar/Defs.lean`, all proved except `KummerUnram`:
`tameBranchNormal_of_local` (localization), `tbnLocal_of_pieces` (Kummer field `Ω = L(f^{1/N}, g^{1/N})`,
purity `TPurity3.purityGlobalDim2'`), `kummerBase`, `etaleBranch`, `branchDescent`.
-/

set_option linter.all false

noncomputable section

namespace Abhyankar

/-- **`TameBranchNormal` from `KummerUnram`** (compiled). -/
theorem tameBranchNormal_of_kummerUnram (hU : KummerUnram) : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_local (tbnLocal_of_pieces kummerBase hU etaleBranch branchDescent)

/-- **`NVLocalInertia` from `KummerUnram`** (compiled). -/
theorem nvLocalInertia_of_kummerUnram (hU : KummerUnram) : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame (tameBranchNormal_of_kummerUnram hU)

/-- **`TameBranchNormal` from `KummerUnramBranch`** (compiled). -/
theorem tameBranchNormal_of_branch (hBr : KummerUnramBranch) : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_kummerUnram (kummerUnram_of_branch hBr)

/-- **`NVLocalInertia` from `KummerUnramBranch`** (compiled). -/
theorem nvLocalInertia_of_branch (hBr : KummerUnramBranch) : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame (tameBranchNormal_of_branch hBr)

/-- **`TameBranchNormal` is proved** (standard axioms). -/
theorem tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_branch kummerUnramBranch

/-- **`NVLocalInertia` is proved** (the glue field `nvLocalInertia` of sgr-fold; standard axioms). -/
theorem nvLocalInertia : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame tameBranchNormal

end Abhyankar

import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd.Compose

/-!
# heegner-32: the Heegner point of `C_d` without the canonical model of `X₀(32 d²)`

Task heegner-32 (2026-11-16). Report: `docs/research/heegner-32.md`; scratch and log: `scratch/heegner-32/`.

gz-heegner proved `GZHL3.HeegnerPointRationalCd` from `T5Glue.ShimuraMainCM` (`hCM`) and `GZHeegner.X0ModuliGaloisMero`
(the canonical model of `X₀(N)`), used at the level `32 d²` of the newform of `C_d`. This group of files removes the
canonical model:

* `HeegnerPointRationalCd/Used.lean`: the instance of `X0ModuliGaloisMero` actually used (`X0ModuliGaloisParamCd`)
  and `heegnerPointRationalCd_of_used (hCM) (hX)` (all `c`);
* `HeegnerPointRationalCd/Twist.lean`: the parametrization of `C_d` at `2Φ_d` as a twisted sum of points of `X₀(32)`
  (`weierPt_two_eichlerCd`), the Galois behaviour of the twisting maps, the even-`c` statement
  `HeegnerPointRationalCdEven`, its sufficiency for the chain (`grossZagierHeegnerCd_of_even`) and its reduction to the
  Galois statement `TwistTransportCd` on `X₀(32)`;
* `HeegnerPointRationalCd/Recip.lean`: `TwistTransportCd` from `hCM` and the lattice statement `TwistLatticeCd`;
* `HeegnerPointRationalCd/Compose.lean`: the conductor-`d` composition of Heegner forms, Chebotarev in the ring class
  field of conductor `d` (`ringClassJd`, proved), and `TwistTransportCd` from `hCM` and genus theory (`GenusSqrtD`).

The main theorem is `ZInQ.Heegner32.grossZagierHeegnerCd_of_genus'`. No `sorry`, no `axiom`.
-/

namespace ZInQ.Heegner32

/-- **`GZStatements.GrossZagierHeegnerCd` (the `C_d` form of `hL3`) from the main theorem of CM, genus theory
(`GenusSqrtD`) and the two printed Gross–Zagier statements.** -/
theorem grossZagierHeegnerCd_of_printed (hCM : T5Glue.ShimuraMainCM) (hG : GenusSqrtD)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_genus' hCM hG hGZ hGC

/-- **The even-`c` Heegner point of `C_d` from the main theorem of CM and genus theory.** -/
theorem heegnerPointRationalCdEven_of_printed (hCM : T5Glue.ShimuraMainCM) (hG : GenusSqrtD) :
    HeegnerPointRationalCdEven :=
  heegnerPointRationalCdEven_of_twist (twistTransportCd_of_genus hCM ringClassJd hG)

end ZInQ.Heegner32

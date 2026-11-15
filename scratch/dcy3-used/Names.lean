import ZInQKernel.Contrib.OneProof.RayClassShimura
open IsDedekindDomain NumberField
#check @HDec.ModelGlue.exists_qbarPt
#check @NumberField.IdeleGroup.ofFiniteIdele
#check @NumberField.IdeleGroup.toFiniteIdele_ofFiniteIdele
#check @FiniteAdeleRing.ext
#check @RayClassCFT.y4_rel
#check @ShimuraCFT.recip_hyp_nonempty
example : NumberField ShimuraGlue.Ray.K4 := inferInstance

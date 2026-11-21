import Breakdown.CertCell.AssemblyPotentialLeaf
import Breakdown.CertCell.AssemblyPotentialExpandLink
import Breakdown.CertCell.AssemblyPotentialModel
import Breakdown.CertCell.AssemblyPotentialModelTorusLong
import Breakdown.CertCell.AssemblyPotentialSharpLink
import Breakdown.CertCell.AssemblyPotentialStage
import Breakdown.CertCell.AssemblyPotentialStageTail
import Breakdown.CertCell.AssemblyPotentialTails
import Breakdown.CertCell.AssemblyPotentialGroupsStage
import Breakdown.CertCell.AssemblyPotentialGroupsCharge

namespace Breakdown.CertCell.Assembly

theorem Internal.ModelPart.torusLongStatement_holds : Internal.ModelPart.TorusLongStatement :=
  fun hT _m hm _Rs _T Sl Gl iSl iGl _lS _lG _L _ℓ _β N h1 h2 h3 h4 h5 hb hs X W =>
    Internal.ModelPart.LongPart.long_class_bound hT hm Sl Gl iSl iGl N h1 h2 h3 h4 h5 hb hs X W

theorem modelStageHolds : ModelStageHolds :=
  Internal.ModelPart.modelStage_of_point
    (fun hT hF => Internal.ModelPart.point_model_stage hT Internal.ModelPart.torusLongStatement_holds hF)
    Internal.torusFacts Internal.frameFacts

theorem potentialStageHolds_of (hSE : StretchExpansionHolds) (hSh : SharpStageHolds)
    (hEps : EpsResolvedStageHolds) (hGr : GroupStageHolds) (hCh : ChargeStageHolds) : PotentialStageHolds :=
  potentialStage_of_parts lowTailSplit_holds leafSplit_holds hSE stretchSplit hSh hEps modelStageHolds
    tailCrossStage_holds hGr hCh tailHighStage_holds splitIdentities_holds potentialAssembly_holds

theorem potentialStageHolds_of_sharpParts (hSE : StretchExpansionHolds)
    (hAb : Internal.Sharp.AbsorbSplitStatement) (hReg : Internal.Sharp.SharpRegularStatement)
    (hEps : EpsResolvedStageHolds) (hGr : GroupStageHolds) (hCh : ChargeStageHolds) : PotentialStageHolds :=
  potentialStageHolds_of hSE (Internal.Sharp.sharpStageHolds_of hAb hReg) hEps hGr hCh

theorem potentialStageHolds_of_epsGroupCharge (hEps : EpsResolvedStageHolds) (hGr : GroupStageHolds)
    (hCh : ChargeStageHolds) : PotentialStageHolds :=
  potentialStageHolds_of stretchExpansionHolds sharpStageHolds hEps hGr hCh

theorem potentialStageHolds_of_epsResolved (hEps : EpsResolvedStageHolds) : PotentialStageHolds :=
  potentialStageHolds_of_epsGroupCharge hEps groupStageHolds chargeStageHolds

end Breakdown.CertCell.Assembly

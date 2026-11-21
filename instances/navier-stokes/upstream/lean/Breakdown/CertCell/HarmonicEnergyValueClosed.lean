import Breakdown.CertCell.HarmonicEnergyValue
import Breakdown.CertCell.LocalEnergyValue
import Breakdown.CertCell.LocalStrainFace
import Breakdown.CertCell.LocalModeDataPair
import Breakdown.CertCell.LocalRadialTrace
import Breakdown.CertCell.LocalHeightWeak
import Breakdown.CertCell.LocalAngularFrame
import Breakdown.CertCell.LocalComponentRadial
import Breakdown.CertCell.LocalComponentHeight
import Breakdown.CertCell.LocalComponentAngular
import Breakdown.CertCell.EnergyAeCongr
import Breakdown.CertCell.HarmonicProfiles

namespace Breakdown.CertCell.CellCalculus

open LocalField

theorem harmonicEnergyFormValue_of_lift (h : HarmonicLiftStatement) : HarmonicEnergyFormValueStatement :=
  harmonicEnergyFormValue_of h localRepresents (localModeDataPair_of localRadialTrace localHeightModeWeak localAngularFrame)
    (localEnergyValue_of localComponentRadial localComponentHeight localComponentAngular) energyAeCongr

theorem harmonicEnergyFormValue : HarmonicEnergyFormValueStatement :=
  harmonicEnergyFormValue_of_lift harmonicLift_holds

end Breakdown.CertCell.CellCalculus

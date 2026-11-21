import Breakdown.Frac.TorusHeat
import Breakdown.Frac.TorusKernel
import Breakdown.Frac.TorusKernelBound
import Breakdown.Frac.TorusUnique
import Breakdown.Frac.TorusPlaneWave
import Breakdown.Frac.TorusSymmetry
import Breakdown.Frac.TorusCoef
import Breakdown.Frac.TorusMildForm
import Breakdown.Frac.TorusDrift
import Breakdown.Frac.TorusFinal
import Breakdown.Frac.OpExports

namespace Breakdown.Periodic

theorem fractionalBreakdownOnTorus_of_torusBlowup (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4)
    (hB : FracTorusBlowup α) : FractionalBreakdownOnTorus α := by
  have h3 : α < 3 / 2 := by linarith
  have hH := fracTorusHeatAlgebra α
  have hK := fracTorusKernelAlgebra α h1.le hH
  have hS := fracTorusKernelSharpBound_of α h1 hK
  have hC := coefFractional_of α (planeWaveEigen_of α h1 h3 (symbolScalar normalizer) normalizer)
    (periodicSymmetry_of α h1 h3 remainderBound)
  exact fractionalBreakdownOnTorus_of_blowup α (fracTorusMildUniqueness_of α h1 h2 hH hK hS)
    (fracTorusSmoothIsMild_of α h1 h2 hH hK hS hC) (fracTorusDrift α) hB

end Breakdown.Periodic

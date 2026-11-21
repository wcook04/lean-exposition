import Breakdown.Torus.Final
import Breakdown.Torus.Unique
import Breakdown.Torus.KernelBound
import Breakdown.Torus.Trilinear
import Breakdown.Torus.TrigHs
import Breakdown.Torus.VarConst
import Breakdown.Torus.MovingFrame
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.Advection
import Breakdown.Torus.TimeCoef

namespace Breakdown.Periodic

theorem kernelSharpBound_holds : KernelSharpBound :=
  kernelSharpBound (trilinearBound trigHs)

theorem smoothPeriodicIsMild_holds : SmoothPeriodicIsMild :=
  smoothPeriodicIsMild kernelSharpBound_holds coefDeriv coefSumSecondPartials coefGradient
    (freqTrSeriesSpec coefDeriv) (coefAdvection coefDeriv (freqTrSeriesSpec coefDeriv))
    coefTimeDeriv (toVContinuous coefDeriv (freqTrSeriesSpec coefDeriv))

theorem breakdownOnTorus_of_torusBlowup (hB : TorusBlowup) : BreakdownOnTorus :=
  breakdownOnTorus_of_blowup (mildUniqueness kernelSharpBound_holds) smoothPeriodicIsMild_holds
    movingFrameReduction hB

end Breakdown.Periodic

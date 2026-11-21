import Breakdown.CertTorus.KernelStatementsIntegral
import Breakdown.CertTorus.HeatKernelBounds
import Breakdown.CertTorus.HeatKernelPartials
import Breakdown.CertTorus.LerayKernelOdd
import Breakdown.CertTorus.KernelScaling
import Breakdown.CertTorus.IntervalIntegralL6
import Breakdown.CertTorus.LerayKernelBound
import Breakdown.CertTorus.LerayKernelContinuity
import Breakdown.CertTorus.LerayKernelC1
import Breakdown.CertTorus.LerayKernelDivFree
import Breakdown.CertTorus.KernelL1Bound
import Breakdown.CertTorus.KernelConvSup
import Breakdown.CertTorus.HeatConvTest
import Breakdown.CertTorus.HeatVelocity
import Breakdown.CertTorus.KernelContraction
import Breakdown.CertTorus.KernelConvTestDecay
import Breakdown.CertTorus.BilinTestKernel
import Breakdown.CertTorus.KernelConvL3Pointwise
import Breakdown.CertTorus.BilinKernel
import Breakdown.CertTorus.DuhamelVelocityAE
import Breakdown.CertTorus.DuhamelChangeOfVariables
import Breakdown.CertTorus.DuhamelContinuous
import Breakdown.CertTorus.HeatPartVanishes
import Breakdown.CertTorus.TruncTendsto

noncomputable section

namespace Breakdown.FarField

theorem lerayKernelBound_holds : LerayKernelBound :=
  lerayKernelBound_of_heatKernelBounds heatKernelBounds_holds

theorem lerayKernelMeasurable_holds : LerayKernelMeasurable :=
  (lerayKernel_continuous_measurable heatKernelBounds_holds).2

theorem lerayKernelJointContinuous_holds : LerayKernelJointContinuous :=
  (lerayKernel_continuous_measurable heatKernelBounds_holds).1

theorem lerayKernelC1_holds : LerayKernelC1 :=
  lerayKernelC1_of_heat heatKernelBounds_holds heatKernelPartials_holds

theorem lerayKernelDivFree_holds : LerayKernelDivFree :=
  lerayKernelDivFree_of_c1 heatKernelBounds_holds heatKernelPartials_holds lerayKernelC1_holds

theorem kernelL1Bound_holds : KernelL1Bound :=
  kernelL1Bound_of_bound lerayKernelBound_holds lerayKernelMeasurable_holds

theorem kernelConvSup_holds : KernelConvSup :=
  kernelConvSup_of_l1 kernelL1Bound_holds lerayKernelMeasurable_holds

theorem kernelConvTestDecay_holds : KernelConvTestDecay :=
  kernelConvTestDecay_of_kernel lerayKernelBound_holds lerayKernelMeasurable_holds
    lerayKernelC1_holds lerayKernelDivFree_holds

theorem integralEquationOfOrbit_holds : IntegralEquationOfOrbit :=
  integralEquationOfOrbit_of_kernel heatKernelBounds_holds heatKernelPartials_holds
    lerayKernelOdd_holds kernelScaling_holds intervalIntegralL6_holds
    lerayKernelBound_of_heatKernelBounds lerayKernel_continuous_measurable lerayKernelC1_of_heat
    lerayKernelDivFree_of_c1 kernelL1Bound_of_bound kernelConvSup_of_l1 heatConvTest_of_heat
    heatVelocity_of_heatConvTest kernelContraction_of_heat kernelConvTestDecay_of_kernel
    bilinTestKernel_of_kernel kernelConvL3Pointwise_of_bound
    (fun bt lp => bilinKernel_of_test_decay bt kernelConvTestDecay_holds lp)
    duhamelVelocityAE_holds duhamelChangeOfVariables_of_kernel duhamelContinuous_of_kernel
    heatPartVanishes_of_heat truncTendsto_of_kernel

end Breakdown.FarField

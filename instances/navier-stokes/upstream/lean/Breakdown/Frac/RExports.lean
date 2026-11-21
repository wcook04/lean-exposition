import Breakdown.Frac.RHeat
import Breakdown.Frac.RDilation
import Breakdown.Frac.RRotation
import Breakdown.Frac.RDecayEmbed
import Breakdown.Frac.RVelocityDilate
import Breakdown.Frac.RPhi
import Breakdown.Frac.RBilin
import Breakdown.Frac.RBilinShiftCont
import Breakdown.Frac.RBilinDilate
import Breakdown.Frac.RBilinRotate
import Breakdown.Frac.RBilinTestCompact
import Breakdown.Frac.RBilinH1
import Breakdown.Frac.RFrame

namespace Breakdown.Freq

theorem fracDilationAlgebra_holds (α : ℝ) (hα : 1 < α) : FracDilationAlgebra α :=
  fracDilationAlgebra α (by linarith) (fracHeatSemigroup α)

theorem fracPhi_holds (α : ℝ) (hα : 1 < α) : FracPhiBounds α ∧ FracPhiVelocity α :=
  fracPhiBoundsVelocity α hα (fracHeatSemigroup α)

theorem fracBilin_holds (α : ℝ) (hα : 1 < α) : FracBilinExists α ∧ FracBilinBound α :=
  fracBilinExistsBound α hα (fracPhi_holds α hα).1

theorem fracVelocityDilate_holds (α : ℝ) (hα : 1 < α) : FracVelocityDilate α :=
  fracVelocityDilate α (by linarith) (fracDilationAlgebra_holds α hα)
    (fracEmbedDilate α (by linarith) (fracDilationAlgebra_holds α hα) (decayFieldScale α (by linarith)))
    (decayFieldScale α (by linarith))

theorem fracFramework_holds (α : ℝ) (hα : 1 < α) : FracFrameworkSpec α ∧ FracCommutes α :=
  fracFramework_of α hα (fracHeatSemigroup α) (fracDilationAlgebra_holds α hα)
    (fracDilationContinuous α (by linarith) (fracDilationAlgebra_holds α hα))
    (fracBilin_holds α hα).1 (fracBilin_holds α hα).2
    (fracBilinContinuous α hα (fracBilin_holds α hα).1 (fracBilin_holds α hα).2
      (fracPhi_holds α hα).1 (fracPhi_holds α hα).2 (fracHeatSemigroup α))
    (fracBilinShift α (fracBilin_holds α hα).1 (fracHeatSemigroup α))
    (fracBilinDilate α hα (fracBilin_holds α hα).1 (fracDilationAlgebra_holds α hα)
      (fracVelocityDilate_holds α hα) (fracHeatSemigroup α))
    (fracBilinCompact α hα (fracBilinTestFormula α hα (fracBilin_holds α hα).1) (fracBilin_holds α hα).2)
    (fracRotationAlgebra α (by linarith) (fracHeatSemigroup α) (fracDilationAlgebra_holds α hα))
    (fracBilinRotate α (fracBilin_holds α hα).1
      (fracRotationAlgebra α (by linarith) (fracHeatSemigroup α) (fracDilationAlgebra_holds α hα)))

theorem fracBilinH1_holds (α : ℝ) (hα : 1 < α) : FracBilinH1Formula α :=
  fracBilinH1Formula α hα (fracBilin_holds α hα).1

end Breakdown.Freq

import Breakdown.FracCert.FreeSymbolExistsBasic
import Breakdown.FracCert.FreeSymbolExistsSmooth
import Breakdown.FracCert.FreeSymbolExistsEquation
import Breakdown.FracCert.FreeSymbolExistsClass
import Breakdown.FracCert.FreeSymbolExistsBound
import Breakdown.FracCert.FreeSymbolExistsExp
import Breakdown.FracCert.FreeSymbolExistsCore

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

open FreeSymbolExistsInternal in
theorem freeSymbolExists_of (h1 : FreeSolutionSmoothStatement) (h2 : FreeSolutionBoundStatement)
    (h3 : FreeSolutionEquationStatement) (h4 : FreeSolutionClassStatement) : FreeSymbolExistsStatement := by
  intro α hα1 hα2 a m s hs hcls
  refine ⟨freeSolution α a s, ⟨h1 α hα1 hα2 a s hs, support_zero (by linarith) hs, h2 α hα1 hα2 a s hs,
    conjSymmetric hs, divergence hs⟩, h4 α hα1 hα2 a m s hs hcls, h3 α hα1 hα2 a s hs⟩

theorem freeSymbolExists_of_small (h : FreeSolutionSmallBoundStatement) : FreeSymbolExistsStatement :=
  freeSymbolExists_of freeSolutionSmooth (freeSolutionBound_of h) freeSolutionEquation freeSolutionClass

theorem freeSymbolExists_of_core (h : FreeCoreBoundStatement) : FreeSymbolExistsStatement :=
  freeSymbolExists_of_small (freeSolutionSmallBound_of h freeExpBound)

theorem freeSymbolExists : FreeSymbolExistsStatement := freeSymbolExists_of_core freeCoreBound

end SteadyCert

end Breakdown

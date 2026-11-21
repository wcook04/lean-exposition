import Breakdown.FracCert.StDecay
import Breakdown.FreqTr.Realization

open MeasureTheory

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

theorem profileNonzero_of (h1 : SymbolL1OfMomentsStatement) (_h2 : FieldSmoothOfMomentsStatement) :
    ProfileNonzeroStatement := by
  intro U hU hm
  by_contra hz
  push Not at hz
  apply hU
  apply velocityInjective_holds
  filter_upwards [(h1 U hm).2] with y hy
  rw [hy]
  exact hz y

end Breakdown.FracCert

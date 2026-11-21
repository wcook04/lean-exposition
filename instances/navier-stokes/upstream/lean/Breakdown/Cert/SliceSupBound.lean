import Breakdown.Cert.Nodes
import Breakdown.Cert.SupBoundHalfSsp

open MeasureTheory

noncomputable section

namespace Breakdown.Cert

theorem sliceSupBoundHolds_of (h : GraphClosedHolds) : SliceSupBoundHolds :=
  fun q => sq_le_of_halfSsp (gradPart q) (secondPart q) (h q)

end Breakdown.Cert

import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpNormalizer
import Breakdown.Frac.OpIntegrable
import Breakdown.Frac.OpSymbolScalar
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.OpRemainderTransform
import Breakdown.Frac.OpRemainderProduct
import Breakdown.Frac.OpSymbolExchange
import Breakdown.Frac.OpSymbol
import Breakdown.Frac.OpSymmetry
import Breakdown.Frac.OpSymmetryRapid

namespace Breakdown

theorem remainderIntegrable : RemainderIntegrableStatement := remainderIntegrable_of remainderBound

theorem symbolExchange : SymbolExchangeStatement :=
  symbolExchange_of remainderTransform remainderProductIntegrable

theorem symbol : SymbolStatement := symbol_of symbolExchange (symbolScalar normalizer) normalizer

theorem symmetryCompact : SymmetryCompactStatement :=
  symmetryCompact_of remainderBound remainderIntegrable

theorem symmetryRapid : SymmetryRapidStatement :=
  symmetryRapid_of remainderBound remainderIntegrable

end Breakdown

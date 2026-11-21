import Breakdown.FracCert.KernelPiece
import Breakdown.FracCert.KernelDyadicPiece
import Breakdown.FracCert.KernelDyadicPieceFarBound

namespace Breakdown.FracCert

theorem dyadicPieceBound : DyadicPieceBoundStatement :=
  dyadicPieceBound_of_far pieceKernel (farPieceBound pieceKernel)

end Breakdown.FracCert

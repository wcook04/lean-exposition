import Breakdown.FracCert.HeldUniqueParts
import Breakdown.FracCert.QuadraticSquare
import Breakdown.FracCert.SecondOrderComplete

open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

theorem productSquare : ProductSquareStatement := by
  intro m u Gu Hu w Gw Hw hu hw
  have hs := secondOrderLinear m u w Gu Gw Hu Hw 1 hu hw
  have h1 := quadraticSquareIntegrable m _ _ _ hs
  have h2 := quadraticSquareIntegrable m _ _ _ hu
  have h3 := quadraticSquareIntegrable m _ _ _ hw
  have h := ((h1.sub h2).sub h3).const_smul (1 / 2 : ℝ)
  have he : symProduct u Gu w Gw = (1 / 2 : ℝ) • (((fun y => (Gu y + (1 : ℝ) • Gw y) (u y + (1 : ℝ) • w y)) -
      fun y => Gu y (u y)) - fun y => Gw y (w y)) := by
    funext y
    simp only [symProduct, Pi.smul_apply, Pi.sub_apply, one_smul, add_apply, map_add]
    congr 1
    abel
  rw [he]
  exact h

end SteadyCert

end Breakdown

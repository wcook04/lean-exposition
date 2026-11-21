import TorusEuler.PaperHierarchyInverse
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTN
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: unit-duration bound of the transverse constants

Generated copy (script `s53tools/mkcopy.py`) of the declarations transverseVelocityWordConstant_le_unit of
`TorusEuler/PaperHierarchyInverse.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

open TorusEuler.HierarchyTwistedProfile
noncomputable section

/-- A solve on an interval of length at most one has a common coefficient
for its initial-data and source bounds. -/
theorem transverseVelocityWordConstant_le_unit {n : ℕ} {r K Ccomm CJ CR B H : ℝ}
    (hr : r ≤ 1) (hK : 0 ≤ K) (hComm : 0 ≤ Ccomm) (hCJ : 0 ≤ CJ) (hCR : 0 ≤ CR)
    (hH : 0 ≤ H) :
    ((2 : ℝ) ^ n * CJ * (linearODEWordFactor Ccomm n *
      (K * ((2 : ℝ) ^ n * CR * B + r * ((2 : ℝ) ^ n * CR * H))))) ≤
      transverseVelocityWordConstant n 1 K Ccomm CJ CR * (B + H) := by
  have hWord := linearODEWordFactor_nonneg hComm n
  have hForce : 0 ≤ (2 : ℝ) ^ n * CR * H := by positivity
  calc
    _ ≤ (2 : ℝ) ^ n * CJ * (linearODEWordFactor Ccomm n *
        (K * ((2 : ℝ) ^ n * CR * B + 1 * ((2 : ℝ) ^ n * CR * H)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr hForce)) hK)
        hWord) (by positivity)
    _ = _ := by unfold transverseVelocityWordConstant; ring

end

end TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

namespace TorusEuler.Paper.Lib.S53.LocalizedAmplitude

open TorusEuler.LocalizedAmplitude
noncomputable section

end
end TorusEuler.Paper.Lib.S53.LocalizedAmplitude


import Breakdown.FracCell.UnresolvedRowClassSt
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts

namespace UnresolvedChargeFinite.Internal

theorem rect_measurable (K : CellBox) : MeasurableSet K.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem density_nonneg {k N : ℕ} (c : FracCellData k N) (S : CellScalars) (Cl : CellClasses)
    (x : FieldTuple k) (hw : ∀ i, 0 < Cl.rowWeight i) (n : ℤ) (p : ℝ × ℝ) :
    0 ≤ rowChargeDensity c S x Cl n p := by
  unfold rowChargeDensity
  split_ifs
  · exact le_rfl
  · refine Finset.sum_nonneg fun i _ => ?_
    have h0 := (hw i).le
    have hc : 0 ≤ curlSq (fun a b => gradMode c.order n x.2.1 a b p) := by unfold curlSq; positivity
    have hv : 0 ≤ vecSq (modeVec c.order n x.1 p.1 p.2) := by unfold vecSq; positivity
    positivity

end UnresolvedChargeFinite.Internal

open UnresolvedChargeFinite.Internal

theorem unresolvedChargeFinite_holds : UnresolvedChargeFiniteStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx F
  obtain ⟨-, hI, -, -, hS, -, hE⟩ := chargeRegular α h1 h2 c hc K S B Cl R hd hw x hx
  have hK : IsCellBox K := hd.box
  have hfun : (fun p : ℝ × ℝ => p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p)
      = fun p => ∑ n ∈ F, p.1 * rowChargeDensity c S x Cl n p := by
    funext p
    rw [Finset.mul_sum]
    rfl
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p)
      K.rect := by
    rw [hfun]
    exact integrable_finsetSum _ fun n _ => hI n
  refine ⟨hint, ?_⟩
  rw [hfun, integral_finsetSum _ fun n _ => hI n, hE]
  refine Summable.sum_le_tsum F (fun n _ => ?_) hS
  refine setIntegral_nonneg (rect_measurable K) fun p hp => ?_
  have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  exact mul_nonneg hp1 (density_nonneg c S Cl x (fun i => (hd.class_weights_pos i).2) n p)

end Breakdown.CellCert.CellAnalysis

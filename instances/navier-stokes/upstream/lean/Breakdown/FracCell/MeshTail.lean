import Breakdown.FracCell.MeshTailSt
import Breakdown.FracCell.MeshTailFinite

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTail

theorem weighted_tsum_le {O : Type} [Fintype O] (N : O → Finset ℤ) (a : O → ℝ) (ha : ∀ o, 0 ≤ a o)
    (f : O → ℤ → ℕ × ℕ → ℝ) (hf : ∀ o n x, 0 ≤ f o n x) (c : ℝ)
    (h : ∀ F : Finset (ℕ × ℕ), ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x ≤ c) :
    ∑ o, a o * ∑ n ∈ N o, ∑' x, f o n x ≤ c := by
  have hs : ∀ o, ∀ n ∈ N o, Summable (fun x => a o * f o n x) := by
    intro o n hn
    refine summable_of_sum_le (c := c) (fun x => mul_nonneg (ha o) (hf o n x)) (fun F => ?_)
    calc ∑ x ∈ F, a o * f o n x = a o * ∑ x ∈ F, f o n x := by rw [Finset.mul_sum]
      _ ≤ a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x :=
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun n => ∑ x ∈ F, f o n x)
            (fun n _ => Finset.sum_nonneg fun x _ => hf o n x) hn) (ha o)
      _ ≤ ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x :=
          Finset.single_le_sum (f := fun o => a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x)
            (fun o _ => mul_nonneg (ha o) (Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun x _ => hf o n x))
            (Finset.mem_univ o)
      _ ≤ c := h F
  have key : ∑ o, a o * ∑ n ∈ N o, ∑' x, f o n x = ∑' x, ∑ o, ∑ n ∈ N o, a o * f o n x := by
    rw [Summable.tsum_finsetSum (fun o _ => summable_sum (fun n hn => hs o n hn))]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Summable.tsum_finsetSum (fun n hn => hs o n hn), Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => tsum_mul_left.symm
  rw [key]
  refine Real.tsum_le_of_sum_le (fun x => Finset.sum_nonneg fun o _ => Finset.sum_nonneg fun n _ =>
    mul_nonneg (ha o) (hf o n x)) (fun F => ?_)
  calc ∑ x ∈ F, ∑ o, ∑ n ∈ N o, a o * f o n x = ∑ o, a o * ∑ n ∈ N o, ∑ x ∈ F, f o n x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ c := h F

end MeshTail

theorem tailMajorant_of (h : TailFiniteStatement) : TailMajorantStatement := by
  intro K B hK hB m hm D I O _ _ T hreg hb w
  unfold farCoefSum
  exact MeshTail.weighted_tsum_le T.outModes T.outWeight hb.outWeight_nonneg
    (fun o n jl => if D < max jl.1 jl.2 then ‖B.coef K (T.outputMode m B w o n) jl.1 jl.2‖ ^ 2 else 0)
    (fun o n jl => by split_ifs <;> positivity) (T.majorant w)
    (fun F => h K B hK hB m hm D T hreg hb w F)

theorem tailMajorant_holds : TailMajorantStatement := tailMajorant_of tailFinite_holds

end CellAnalysis

end CellCert

end Breakdown

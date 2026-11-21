import Breakdown.FracCell.MeshTailRadial
import Breakdown.FracCell.MeshTailHeight

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailSlice

theorem far_split (D : ℕ) (F : Finset (ℕ × ℕ)) (x : ℕ → ℕ → ℝ) (hx : ∀ j l, 0 ≤ x j l) :
    ∑ jl ∈ F, (if D < max jl.1 jl.2 then x jl.1 jl.2 else 0)
      ≤ ∑ j' ∈ F.image Prod.fst, ∑ l' ∈ F.image Prod.snd, (if D < j' then x j' l' else 0)
        + ∑ j' ∈ F.image Prod.fst, ∑ l' ∈ F.image Prod.snd, (if D < l' then x j' l' else 0) := by
  have hsub : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro q hq
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  simp only [← Finset.sum_add_distrib]
  rw [← Finset.sum_product' (f := fun j' l' =>
    (if D < j' then x j' l' else 0) + (if D < l' then x j' l' else 0))]
  calc ∑ jl ∈ F, (if D < max jl.1 jl.2 then x jl.1 jl.2 else 0)
      ≤ ∑ jl ∈ F, ((if D < jl.1 then x jl.1 jl.2 else 0) + (if D < jl.2 then x jl.1 jl.2 else 0)) := by
        refine Finset.sum_le_sum fun jl _ => ?_
        have h0 := hx jl.1 jl.2
        by_cases h1 : D < jl.1 <;> by_cases h2 : D < jl.2 <;>
          simp only [h1, h2, if_true, if_false, lt_max_iff, or_self, true_or, or_true] <;> linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun jl _ _ => by
        have h0 := hx jl.1 jl.2
        split_ifs <;> linarith

end MeshTailSlice

open MeshTailSlice in
theorem angleSlice_of (hR : RadialBranchStatement) (hH : HeightBranchStatement) : AngleSliceStatement := by
  intro K B hK hB m D I O _ _ T hreg hb w F θ hθ
  refine le_trans ?_ (add_le_add (hR K B hK hB m D T hreg hb w (F.image Prod.fst) (F.image Prod.snd) θ hθ)
    (hH K B hK hB m D T hreg hb w (F.image Prod.fst) (F.image Prod.snd) θ hθ))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (far_split D F (fun j l => ‖B.coef K (fun p => T.angleField m B w o p θ) j l‖ ^ 2) (fun j l => by positivity)) (hb.outWeight_nonneg o)

theorem angleSlice_holds : AngleSliceStatement := angleSlice_of radialBranch_holds heightBranch_holds

end CellAnalysis

end CellCert

end Breakdown

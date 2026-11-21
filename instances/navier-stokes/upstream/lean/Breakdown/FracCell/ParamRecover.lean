import Breakdown.FracCell.ParamDefs

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

private theorem decomp {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D)
    (hinj : Function.Injective P.solved) (u : D → ℂ) :
    u = P.freePart u + ∑ j, Pi.single (P.solved j) (u (P.solved j)) := by
  funext d
  simp only [Pi.add_apply, Finset.sum_apply, ParamData.freePart]
  by_cases hd : d ∈ P.solvedSet
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
    rw [if_pos hd, zero_add, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hinj.ne hb.symm]
    · simp
  · rw [if_neg hd]
    have hne : ∀ j, d ≠ P.solved j := fun j h =>
      hd (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
    simp [hne]

private theorem mulVec_sum_single {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D)
    (c : Fin P.relCount → ℂ) :
    P.relation *ᵥ (∑ j, Pi.single (P.solved j) (c j)) = P.solvedBlock *ᵥ c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, ParamData.solvedBlock]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Pi.single_apply]

theorem paramRecover : ParamRecoverStatement := by
  intro D _ _ P hP u hu
  set c : Fin P.relCount → ℂ := fun j => u (P.solved j) with hcdef
  have hdec := decomp P hP.solved_injective u
  have h0 : P.relation *ᵥ P.freePart u = -(P.solvedBlock *ᵥ c) := by
    have h1 := hu
    rw [hdec, Matrix.mulVec_add, mulVec_sum_single] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hc : P.solvedBlock⁻¹ *ᵥ (P.relation *ᵥ P.freePart u) = -c := by
    rw [h0, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hP.solvedBlock_invertible, Matrix.one_mulVec]
  unfold ParamData.param
  rw [hc]
  conv_rhs => rw [hdec]
  simp only [Pi.neg_apply, Pi.single_neg, Finset.sum_neg_distrib, sub_neg_eq_add, hcdef]

end Breakdown.CellCert.CellFormula

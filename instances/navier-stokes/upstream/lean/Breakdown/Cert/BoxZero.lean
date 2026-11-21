import Mathlib
import Breakdown.Cert.FixedPointBox

namespace Breakdown

open Matrix

namespace BoxZeroInternal

private theorem abs_mulVec_apply_le {k : ℕ} (N : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ)
    (i : Fin k) : |(N *ᵥ w) i| ≤ ∑ j, |N i j| * |w j| := by
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  exact abs_mul _ _

end BoxZeroInternal

theorem exists_zero_of_inclusion {k : ℕ} (center radius : Fin k → ℝ) (hr : ∀ i, 0 ≤ radius i)
    (M N : Matrix (Fin k) (Fin k) ℝ) (hNM : N * M = 1) (c : ℝ) (δ : Fin k → ℝ)
    (Φ : (Fin k → ℝ) → Fin k → ℝ) (hΦ : ContinuousOn Φ (Set.Icc (center - radius) (center + radius)))
    (hdev : ∀ p ∈ Set.Icc (center - radius) (center + radius), ∀ j,
      |Φ p j - (M.mulVec (p - center)) j| ≤ c + δ j)
    (hincl : ∀ i, ∑ j, |N i j| * (c + δ j) ≤ radius i) :
    ∃ p ∈ Set.Icc (center - radius) (center + radius), Φ p = 0 := by
  have hab : center - radius ≤ center + radius := by
    intro i
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith [hr i]
  have hMN : M * N = 1 := mul_eq_one_comm.mp hNM
  have hf : ContinuousOn (fun p => p - N *ᵥ Φ p) (Set.Icc (center - radius) (center + radius)) :=
    continuousOn_id.sub ((continuous_const.matrix_mulVec continuous_id).comp_continuousOn hΦ)
  have hid : ∀ p : Fin k → ℝ,
      p - N *ᵥ Φ p - center = -(N *ᵥ (Φ p - M *ᵥ (p - center))) := by
    intro p
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    abel
  have hmap : Set.MapsTo (fun p => p - N *ᵥ Φ p) (Set.Icc (center - radius) (center + radius))
      (Set.Icc (center - radius) (center + radius)) := by
    intro p hp
    have hb : ∀ i, |(p - N *ᵥ Φ p) i - center i| ≤ radius i := by
      intro i
      have h1 : (p - N *ᵥ Φ p) i - center i = -((N *ᵥ (Φ p - M *ᵥ (p - center))) i) := by
        have := congrFun (hid p) i
        simpa only [Pi.sub_apply, Pi.neg_apply] using this
      rw [h1, abs_neg]
      refine (BoxZeroInternal.abs_mulVec_apply_le N _ i).trans ((Finset.sum_le_sum ?_).trans (hincl i))
      intro j _
      exact mul_le_mul_of_nonneg_left (by simpa only [Pi.sub_apply] using hdev p hp j) (abs_nonneg _)
    constructor
    · intro i
      have := (abs_le.mp (hb i)).1
      simp only [Pi.sub_apply] at this ⊢
      linarith
    · intro i
      have := (abs_le.mp (hb i)).2
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      linarith
  obtain ⟨p, hp, hfix⟩ := exists_fixedPoint_box _ _ hab _ hf hmap
  refine ⟨p, hp, ?_⟩
  have h0 : N *ᵥ Φ p = 0 := by
    have : p - N *ᵥ Φ p = p - 0 := by simpa using hfix
    exact sub_right_injective this
  calc Φ p = (M * N) *ᵥ Φ p := by rw [hMN, Matrix.one_mulVec]
    _ = M *ᵥ (N *ᵥ Φ p) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

end Breakdown

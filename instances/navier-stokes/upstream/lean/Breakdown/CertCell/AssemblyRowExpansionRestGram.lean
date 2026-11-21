import Breakdown.CertCell.AssemblyRowExpansionRestTests

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus

theorem quadForm_inv_diagonal_scaled {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (s : n → ℝ)
    (hs : ∀ i, 0 < s i) (hG : ∀ i i', s i ≠ s i' → G i i' = 0) (t : n → ℂ) :
    quadForm (Matrix.of fun i i' => G i i' / ((s i : ℝ) : ℂ))⁻¹ t
      = quadForm G⁻¹ (fun i => ((Real.sqrt (s i) : ℝ) : ℂ) * t i) := by
  have hsq : ∀ i, Real.sqrt (s i) ≠ 0 := fun i => (Real.sqrt_pos.mpr (hs i)).ne'
  set S : Matrix n n ℂ := Matrix.diagonal (fun i => ((Real.sqrt (s i) : ℝ) : ℂ)) with hS
  set T : Matrix n n ℂ := Matrix.diagonal (fun i => (((Real.sqrt (s i))⁻¹ : ℝ) : ℂ)) with hT
  have hST : S * T = 1 := by
    rw [hT, hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hsq i), Complex.ofReal_one]
  have hM : (Matrix.of fun i i' => G i i' / ((s i : ℝ) : ℂ)) = T * G * T := by
    ext i i'
    rw [hT, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h : s i = s i'
    · rw [← h]
      have e : ((s i : ℝ) : ℂ) = ((Real.sqrt (s i) : ℝ) : ℂ) * ((Real.sqrt (s i) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hs i).le]
      have h0 : ((Real.sqrt (s i) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hsq i)
      rw [e, Complex.ofReal_inv]
      field_simp
    · rw [hG i i' h]
      simp
  have hTinv : T⁻¹ = S := Matrix.inv_eq_left_inv hST
  rw [hM, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv]
  unfold quadForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have e1 : S *ᵥ t = fun i => ((Real.sqrt (s i) : ℝ) : ℂ) * t i := by
    funext i
    rw [hS, Matrix.mulVec_diagonal]
  have e2 : star t ᵥ* S = star (fun i => ((Real.sqrt (s i) : ℝ) : ℂ) * t i) := by
    funext i
    rw [hS, Matrix.vecMul_diagonal]
    simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e1, e2]

section ScaledRows

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem inverseWeightedSq_scaled_rows_le (A : AssemblyEntry D R) (hC : RowConditions D R A) (K : Fin D.mesh.count)
    (c : ℤ × ℤ → ℝ) (hc : ∀ ℓ ∈ D.mesh.tested K, 0 < c ℓ)
    (f : ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hfm : ∀ ℓ ∈ D.mesh.tested K, ∀ a, AEStronglyMeasurable (fun p => f ℓ p a) (volume.restrict (D.mesh.box K).rect))
    (hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ a, IntegrableOn (fun p => p.1 * ‖f ℓ p a‖ ^ 2) (D.mesh.box K).rect)
    (t : Fin (A.blocks K).rowCount → ℂ)
    (ht : ∀ i, t i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ a, f ((A.blocks K).rowLabel i) p a * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p a)) :
    inverseWeightedSq (scaledRowGram D K (A.blocks K) c) t
      ≤ ∑ ℓ ∈ D.mesh.tested K, c ℓ * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖f ℓ p a‖ ^ 2 := by
  classical
  have hsc : scaledRowGram D K (A.blocks K) c = Matrix.of fun i i' => rowGram D K (A.blocks K) i i' / ((c ((A.blocks K).rowLabel i) : ℝ) : ℂ) := rfl
  have hblock : ∀ i i', c ((A.blocks K).rowLabel i) ≠ c ((A.blocks K).rowLabel i') → rowGram D K (A.blocks K) i i' = 0 := by
    intro i i' h
    unfold rowGram
    rw [if_neg]
    intro hl
    exact h (by rw [hl])
  unfold inverseWeightedSq
  rw [hsc, quadForm_inv_diagonal_scaled (rowGram D K (A.blocks K)) (fun i => c ((A.blocks K).rowLabel i))
    (fun i => hc _ (hC.label_tested K i)) hblock t]
  let f' : ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ := fun ℓ p a => ((Real.sqrt (c ℓ) : ℝ) : ℂ) * f ℓ p a
  have hn : ∀ ℓ ∈ D.mesh.tested K, ∀ p a, ‖f' ℓ p a‖ ^ 2 = c ℓ * ‖f ℓ p a‖ ^ 2 := by
    intro ℓ hℓ p a
    simp only [f', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hc ℓ hℓ).le]
  have hb := inverseWeightedSq_rows_le D R A hC K f'
    (fun ℓ hℓ a => aestronglyMeasurable_const.mul (hfm ℓ hℓ a))
    (fun ℓ hℓ a => by
      refine ((hfi ℓ hℓ a).const_mul (c ℓ)).congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hn ℓ hℓ]
      ring)
    (fun i => ((Real.sqrt (c ((A.blocks K).rowLabel i)) : ℝ) : ℂ) * t i) (by
      intro i
      rw [ht i, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [f', Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring)
  unfold inverseWeightedSq at hb
  refine hb.trans (le_of_eq (Finset.sum_congr rfl (fun ℓ hℓ => ?_)))
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [hn ℓ hℓ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

end ScaledRows

end Internal

end Assembly

end CertCell

end Breakdown

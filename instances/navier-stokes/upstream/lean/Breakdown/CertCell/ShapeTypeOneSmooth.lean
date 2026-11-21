import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem contDiff_one_of_off_origin {f : Space → Fin 3 → ℂ}
    (hoff : ContDiffOn ℝ 1 f {0}ᶜ) (h0 : DifferentiableAt ℝ f 0)
    (hball : ∃ δ > 0, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall 0 δ)) :
    ContDiff ℝ 1 f := by
  obtain ⟨δ, hδ, L, hL⟩ := hball
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y => ?_, continuous_iff_continuousAt.2 fun y => ?_⟩
  · by_cases hy : y = 0
    · subst hy
      exact h0
    · exact (hoff.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).differentiableAt (by norm_num)
  · by_cases hy : y = 0
    · subst hy
      exact hL.continuousOn.continuousAt (Metric.closedBall_mem_nhds 0 hδ)
    · exact ((hoff.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).fderiv_right
        (m := 0) (by norm_num)).continuousAt

theorem dist_le_of_far {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {g : E → F} {δ M : ℝ} (hδ : 0 < δ) {x y : E} (hx : ‖x‖ < δ / 2) (hy : δ < ‖y‖)
    (hgx : ‖g x‖ ≤ M) (hgy : ‖g y‖ ≤ M) :
    dist (g x) (g y) ≤ 4 * M / δ * dist x y := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hgx
  have hxy : δ / 2 ≤ dist x y := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  have h1 : dist (g x) (g y) ≤ 2 * M := by
    rw [dist_eq_norm]
    calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  calc dist (g x) (g y) ≤ 2 * M := h1
    _ = 4 * M / δ * (δ / 2) := by field_simp; ring
    _ ≤ 4 * M / δ * dist x y := by
      apply mul_le_mul_of_nonneg_left hxy
      positivity

theorem slope_bound_of_off_origin {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] {g : E → F} (hcont : Continuous g)
    (hK : ∀ K : Set E, IsCompact K → K ⊆ {0}ᶜ → ∃ L : NNReal, LipschitzOnWith L g K)
    (hball : ∃ δ > 0, ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 δ)) (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 R) := by
  obtain ⟨δ, hδ, L₁, hL₁⟩ := hball
  obtain ⟨L₂, hL₂⟩ := hK (Metric.closedBall 0 R \ Metric.ball 0 (δ / 2))
    ((isCompact_closedBall 0 R).diff Metric.isOpen_ball) (by
      intro y hy hy0
      apply hy.2
      rw [Set.mem_singleton_iff.1 hy0]
      exact Metric.mem_ball_self (by linarith))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hcont.continuousOn
  set M := max C 0 with hMdef
  have hCM : ∀ x ∈ Metric.closedBall (0 : E) R, ‖g x‖ ≤ M := fun x hx => le_trans (hC x hx) (le_max_left _ _)
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ))) ?_⟩
  intro x hx y hy
  have hd := dist_nonneg (x := x) (y := y)
  have hA : ∀ u : E, u ∈ Metric.closedBall (0 : E) δ ↔ ‖u‖ ≤ δ := fun u => by
    rw [Metric.mem_closedBall, dist_zero_right]
  have hB : ∀ u : E, u ∈ Metric.closedBall (0 : E) R \ Metric.ball 0 (δ / 2) ↔
      u ∈ Metric.closedBall (0 : E) R ∧ δ / 2 ≤ ‖u‖ := fun u => by
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
  have c1 : ‖x‖ ≤ δ → ‖y‖ ≤ δ → dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y :=
    fun h1 h2 => le_trans (hL₁.dist_le_mul x ((hA x).2 h1) y ((hA y).2 h2))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  have c2 : δ / 2 ≤ ‖x‖ → δ / 2 ≤ ‖y‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y :=
    fun h1 h2 => le_trans (hL₂.dist_le_mul x ((hB x).2 ⟨hx, h1⟩) y ((hB y).2 ⟨hy, h2⟩))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hd)
  have c3 : ‖x‖ < δ / 2 → δ < ‖y‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y :=
    fun h1 h2 => le_trans (dist_le_of_far hδ h1 h2 (hCM x hx) (hCM y hy))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hd)
  have c4 : ‖y‖ < δ / 2 → δ < ‖x‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y := by
    intro h1 h2
    rw [dist_comm (g x), dist_comm x]
    exact le_trans (dist_le_of_far hδ h1 h2 (hCM y hy) (hCM x hx))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) dist_nonneg)
  by_cases h1 : ‖x‖ ≤ δ <;> by_cases h2 : ‖y‖ ≤ δ
  · exact c1 h1 h2
  · by_cases h3 : δ / 2 ≤ ‖x‖
    · exact c2 h3 (by linarith)
    · exact c3 (by linarith) (by linarith)
  · by_cases h3 : δ / 2 ≤ ‖y‖
    · exact c2 (by linarith) h3
    · exact c4 (by linarith) (by linarith)
  · exact c2 (by linarith) (by linarith)

theorem isKeyFieldSmooth_of_off_origin {f : Space → Fin 3 → ℂ}
    (hoff : ContDiffOn ℝ 1 f {0}ᶜ)
    (hK : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) K)
    (h0 : DifferentiableAt ℝ f 0)
    (hball : ∃ δ > 0, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall 0 δ)) :
    IsKeyFieldSmooth f := by
  have hf := contDiff_one_of_off_origin hoff h0 hball
  exact ⟨hf, slope_bound_of_off_origin (hf.continuous_fderiv (by norm_num)) hK hball⟩

end Internal

theorem typeOneKeySmooth_of_off_origin
    (hoff : ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P →
      IsTimeFieldData D → κ ∈ D.keys → κ.label.1 ≠ 0 →
        ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) {0}ᶜ ∧
        ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
          ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) K)
    (horigin : ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P →
      IsTimeFieldData D → κ ∈ D.keys → κ.label.1 ≠ 0 →
        DifferentiableAt ℝ (keyVector P κ (D.amp κ) σ) 0 ∧
        ∃ δ > 0, ∃ L : NNReal,
          LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) (Metric.closedBall 0 δ)) :
    TypeOneKeySmooth := by
  intro P D κ σ hP hD hκ h1
  obtain ⟨ha, hb⟩ := hoff P D κ σ hP hD hκ h1
  obtain ⟨hc, hd⟩ := horigin P D κ σ hP hD hκ h1
  exact Internal.isKeyFieldSmooth_of_off_origin ha hb hc hd

end GivenShape

end CertCell

end Breakdown

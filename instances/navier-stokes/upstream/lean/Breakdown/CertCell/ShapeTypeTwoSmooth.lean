import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem contDiff_of_punctured_and_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} {ρ : ℝ} (hoff : ContDiffOn ℝ 1 f {0}ᶜ) (hball : ContDiffOn ℝ 1 f (Metric.ball 0 ρ))
    (hρ : 0 < ρ) : ContDiff ℝ 1 f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    exact hball.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  · exact hoff.contDiffAt (isOpen_compl_singleton.mem_nhds hy)

theorem slopeBoundOn_of_closed_cover {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace F] {g : E → F} {s A B : Set E} {K : NNReal}
    (hs : Convex ℝ s) (hA : IsClosed A) (hB : IsClosed B) (hcover : s ⊆ A ∪ B)
    (hgA : LipschitzOnWith K g A) (hgB : LipschitzOnWith K g B) : LipschitzOnWith K g s := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x ∈ A → y ∈ B → dist (g x) (g y) ≤ K * dist x y := by
    intro x hx y hy hxA hyB
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    obtain ⟨z, hz, hzA, hzB⟩ := (isPreconnected_closed_iff.mp (convex_segment x y).isPreconnected) A B hA hB
      (hseg.trans hcover) ⟨x, left_mem_segment ℝ x y, hxA⟩ ⟨y, right_mem_segment ℝ x y, hyB⟩
    calc dist (g x) (g y) ≤ dist (g x) (g z) + dist (g z) (g y) := dist_triangle _ _ _
      _ ≤ K * dist x z + K * dist z y := add_le_add (hgA.dist_le_mul x hxA z hzA) (hgB.dist_le_mul z hzB y hyB)
      _ = K * dist x y := by rw [← mul_add, dist_add_dist_of_mem_segment hz]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rcases hcover hx with hxA | hxB <;> rcases hcover hy with hyA | hyB
  · exact hgA.dist_le_mul x hxA y hyA
  · exact key x hx y hy hxA hyB
  · rw [dist_comm (g x), dist_comm x]
    exact key y hy x hx hyA hxB
  · exact hgB.dist_le_mul x hxB y hyB

theorem slopeBoundOn_closedBall_of_annuli_and_ball {F : Type*} [PseudoMetricSpace F] {g : Space → F} {ρ : ℝ}
    (hρ : 0 < ρ) (hann : ∀ r R : ℝ, 0 < r → ∃ L : NNReal, LipschitzOnWith L g {y | r ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    (hball : ∃ L : NNReal, LipschitzOnWith L g (Metric.ball 0 ρ)) (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 R) := by
  obtain ⟨L₁, h₁⟩ := hball
  obtain ⟨L₂, h₂⟩ := hann (ρ / 2) R (half_pos hρ)
  have hBc : IsClosed {y : Space | ρ / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ R} :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  refine ⟨max L₁ L₂, slopeBoundOn_of_closed_cover (convex_closedBall 0 R)
    (Metric.isClosed_closedBall (x := (0 : Space)) (ε := ρ / 2)) hBc ?_ ?_ ?_⟩
  · intro y hy
    by_cases h : ‖y‖ ≤ ρ / 2
    · left
      simpa using h
    · right
      refine ⟨le_of_lt (not_le.mp h), ?_⟩
      simpa using hy
  · refine (h₁.mono ?_).weaken (le_max_left _ _)
    exact Metric.closedBall_subset_ball (half_lt_self hρ)
  · exact h₂.weaken (le_max_right _ _)

theorem keyFieldSmooth_of_pieces {f : Space → Fin 3 → ℂ}
    (hoff : ContDiffOn ℝ 1 f {0}ᶜ ∧
      ∀ r R : ℝ, 0 < r → ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) {y | r ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    (horig : ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 1 f (Metric.ball 0 ρ) ∧
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) (Metric.ball 0 ρ)) :
    IsKeyFieldSmooth f := by
  obtain ⟨ρ, hρ, hC, hL⟩ := horig
  exact ⟨contDiff_of_punctured_and_ball hoff.1 hC hρ,
    slopeBoundOn_closedBall_of_annuli_and_ball hρ hoff.2 hL⟩

end Internal

theorem typeTwoKeySmooth_of
    (hoff : ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P →
      IsTimeFieldData D → κ ∈ D.keys → κ.label.1 = 0 →
        ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) {0}ᶜ ∧
          ∀ r R : ℝ, 0 < r → ∃ L : NNReal,
            LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) {y | r ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    (horig : ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P →
      IsTimeFieldData D → κ ∈ D.keys → κ.label.1 = 0 →
        ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) (Metric.ball 0 ρ) ∧
          ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) (Metric.ball 0 ρ)) :
    TypeTwoKeySmooth := fun P D κ σ hP hD hκ h0 =>
  Internal.keyFieldSmooth_of_pieces (hoff P D κ σ hP hD hκ h0) (horig P D κ σ hP hD hκ h0)

end GivenShape

end CertCell

end Breakdown

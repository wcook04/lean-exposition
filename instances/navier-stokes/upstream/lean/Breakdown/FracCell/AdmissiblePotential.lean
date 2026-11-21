import Breakdown.FracCert.Defs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert

namespace AdmissiblePotentialInternal

theorem right_zero_of_bad (q : Space → ℝ) (Q : Space → Space) (j : Fin 3)
    (hQ : ∀ φ, IsTestScalar φ → Integrable (fun y => φ y * inner ℝ (Q y) (unitVector j)))
    (hw : ∀ φ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j))
    (φ₀ : Space → ℝ) (h₀ : IsTestScalar φ₀)
    (hbad : ¬ AEStronglyMeasurable (fun y => fderiv ℝ φ₀ y (unitVector j) * q y) volume) :
    ∀ φ, IsTestScalar φ → ∫ y, φ y * inner ℝ (Q y) (unitVector j) = 0 := by
  have zero_of : ∀ ψ, IsTestScalar ψ →
      ¬ AEStronglyMeasurable (fun y => fderiv ℝ ψ y (unitVector j) * q y) volume →
      ∫ y, ψ y * inner ℝ (Q y) (unitVector j) = 0 := by
    intro ψ hψ hb
    have h1 := hw ψ hψ
    rw [integral_undef (fun hi => hb hi.aestronglyMeasurable)] at h1
    linarith
  intro φ hφ
  by_cases hg : AEStronglyMeasurable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume
  · have hsum : IsTestScalar (φ + φ₀) := ⟨hφ.1.add h₀.1, hφ.2.add h₀.2⟩
    have hb : ¬ AEStronglyMeasurable
        (fun y => fderiv ℝ (φ + φ₀) y (unitVector j) * q y) volume := by
      intro hm
      apply hbad
      have heq : (fun y => fderiv ℝ φ₀ y (unitVector j) * q y) =
          (fun y => fderiv ℝ (φ + φ₀) y (unitVector j) * q y) -
            (fun y => fderiv ℝ φ y (unitVector j) * q y) := by
        funext y
        have d1 : DifferentiableAt ℝ φ y := (hφ.1.differentiable (by simp)).differentiableAt
        have d2 : DifferentiableAt ℝ φ₀ y := (h₀.1.differentiable (by simp)).differentiableAt
        simp [fderiv_add d1 d2]
        ring
      rw [heq]
      exact hm.sub hg
    have e1 := zero_of _ hsum hb
    have e0 := zero_of _ h₀ hbad
    have : ∫ y, (φ + φ₀) y * inner ℝ (Q y) (unitVector j) =
        (∫ y, φ y * inner ℝ (Q y) (unitVector j)) + ∫ y, φ₀ y * inner ℝ (Q y) (unitVector j) := by
      rw [← integral_add (hQ φ hφ) (hQ φ₀ h₀)]
      congr 1
      funext y
      simp [add_mul]
    linarith
  · exact zero_of φ hφ hg

theorem test_mul_integrable (Q : Space → Space) (j : Fin 3)
    (hQ2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2)) (hQm : AEStronglyMeasurable Q volume)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) :
    Integrable (fun y => φ y * inner ℝ (Q y) (unitVector j)) := by
  have hK : IsCompact (tsupport φ) := hφ.2
  have hcont : Continuous φ := hφ.1.continuous
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hφ.2
  have hsub : Function.support (fun y => φ y * inner ℝ (Q y) (unitVector j)) ⊆ tsupport φ := by
    intro y hy
    apply subset_tsupport
    intro h0
    apply hy
    simp [h0]
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  have hI : IntegrableOn (fun y => C * (1 + ‖Q y‖ ^ 2)) (tsupport φ) := by
    have : IsFiniteMeasure (volume.restrict (tsupport φ)) := by
      rw [isFiniteMeasure_restrict]; exact hK.measure_lt_top.ne
    exact ((integrable_const (1 : ℝ)).add (hQ2 _ hK)).const_mul C
  refine hI.mono' ?_ ?_
  · exact (hcont.aestronglyMeasurable.mul
      ((hQm.inner aestronglyMeasurable_const))).restrict
  · refine Filter.Eventually.of_forall (fun y => ?_)
    have h1 : |inner ℝ (Q y) (unitVector j)| ≤ ‖Q y‖ := by
      calc |inner ℝ (Q y) (unitVector j)| ≤ ‖Q y‖ * ‖unitVector j‖ := abs_real_inner_le_norm _ _
        _ = ‖Q y‖ := by simp [unitVector]
    have h2 : ‖Q y‖ ≤ 1 + ‖Q y‖ ^ 2 := by nlinarith [norm_nonneg (Q y)]
    have h3 : ‖φ y‖ ≤ C := hC y
    rw [Real.norm_eq_abs, abs_mul]
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h3
    calc |φ y| * |inner ℝ (Q y) (unitVector j)| ≤ C * (1 + ‖Q y‖ ^ 2) := by
          apply mul_le_mul (by simpa [Real.norm_eq_abs] using h3) (h1.trans h2) (abs_nonneg _) hC0

theorem bad_exists (q : Space → ℝ) (j : Fin 3) (hm : ¬ AEStronglyMeasurable q volume) :
    ∃ φ, IsTestScalar φ ∧ ¬ AEStronglyMeasurable (fun y => fderiv ℝ φ y (unitVector j) * q y) volume := by
  by_contra hall
  push_neg at hall
  apply hm
  have hloc : ∀ n : ℕ, AEStronglyMeasurable q (volume.restrict (Metric.ball (0 : Space) (n + 1))) := by
    intro n
    let b : ContDiffBump (0 : Space) := ⟨n + 1, n + 2, by positivity, by linarith⟩
    let φ : Space → ℝ := fun y => y j * b y
    have hφ : IsTestScalar φ := by
      refine ⟨?_, ?_⟩
      · exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul b.contDiff
      · exact b.hasCompactSupport.mul_left
    have hder : ∀ y ∈ Metric.ball (0 : Space) (n + 1), fderiv ℝ φ y (unitVector j) = 1 := by
      intro y hy
      have hev : φ =ᶠ[nhds y] fun y => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
        have : b z = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
        simp [φ, this]
      rw [hev.fderiv_eq, ContinuousLinearMap.fderiv]
      simp [unitVector]
    have h := (hall φ hφ).restrict (s := Metric.ball (0 : Space) (n + 1))
    refine h.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    exact Filter.Eventually.of_forall (fun y hy => by simp [hder y hy])
  have hU : (⋃ n : ℕ, Metric.ball (0 : Space) (n + 1)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact Set.mem_iUnion.2 ⟨n, by simp; linarith⟩
  have := aestronglyMeasurable_iUnion_iff.2 hloc
  rwa [hU, Measure.restrict_univ] at this

end AdmissiblePotentialInternal

theorem admissiblePotential_holds (Q : Space → Space) (hG : IsGradientField Q) :
    ∃ q : Space → ℝ, AEStronglyMeasurable q volume ∧ IsLocalSquareIntegrable (fun y => q y ^ 2) ∧
      ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j) := by
  obtain ⟨q, hq2, hQ2, hQm, hw⟩ := hG
  by_cases hm : AEStronglyMeasurable q volume
  · exact ⟨q, hm, hq2, hw⟩
  · refine ⟨fun _ => 0, aestronglyMeasurable_const, ?_, ?_⟩
    · intro K _
      simp
    · intro φ hφ j
      obtain ⟨φ₀, h₀, hbad⟩ := AdmissiblePotentialInternal.bad_exists q j hm
      have := AdmissiblePotentialInternal.right_zero_of_bad q Q j
        (fun ψ hψ => AdmissiblePotentialInternal.test_mul_integrable Q j hQ2 hQm ψ hψ) (hw · · j) φ₀ h₀ hbad φ hφ
      simp [this]

end CellFormula

end CellCert

end Breakdown

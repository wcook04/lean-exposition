import Breakdown.CertCell.TopStatements
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.PlanePairInternal

open CellCert CellCert.CellCoordinates CellCert.CellFormula CellCert.CellAnalysis

theorem harmonicSin_at_zero {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (f : ℝ → Space → β) :
    CellCalculus.harmonicSin 0 f = 0 := by
  funext y
  simp [CellCalculus.harmonicSin]

theorem sinTuple_at_zero (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    CellCalculus.sinTuple 0 v G H Pg = ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) := by
  simp only [CellCalculus.sinTuple, harmonicSin_at_zero]

theorem isGradientField_zero : SteadyCert.IsGradientField (0 : Space → Space) :=
  ⟨fun _ => 0, by intro K _; simp, by intro K _; simp, aestronglyMeasurable_const, by intro φ _ j; simp⟩

theorem heightStrip_zero (c o lo hi : ℝ) (wt t : ℝ → ℝ) :
    heightStripMoment c o lo hi wt (fun _ => 0) (fun _ => 0) t = 0 := by
  simp [heightStripMoment]

theorem radialStrip_zero (c o lo hi : ℝ) (t : ℝ → ℝ) :
    radialStripMoment c o lo hi (fun _ => 0) (fun _ => 0) t = 0 := by
  simp [radialStripMoment]

theorem segMoment_zero (S : FaceSegment) (w : Bool) (d : ℕ) :
    S.moment w (fun _ => 0) (fun _ => 0) (fun _ => 0) d = 0 := by
  unfold FaceSegment.moment
  split_ifs <;> simp [radialStripMoment, heightStripMoment]

theorem segMoment_congr_ae (S : FaceSegment) (w : Bool) {F F' : ℝ × ℝ → ℂ} (dFr dFz : ℝ × ℝ → ℂ)
    (h : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), F p = F' p) (d : ℕ) :
    S.moment w F dFr dFz d = S.moment w F' dFr dFz d := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs
  all_goals
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with p hp
    rw [hp]

section ZeroTuple

variable (L : CellLayout)

theorem velMode_zeroTuple (n : ℤ) (a : Fin 3) :
    L.velMode n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a = fun _ => 0 := by
  funext p
  fin_cases a <;> simp [CellLayout.velMode, modeVec, frameVec]

theorem gradModeOf_zeroTuple (n : ℤ) (a b : Fin 3) :
    L.gradModeOf n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a b = fun _ => 0 := by
  funext p
  simp [CellLayout.gradModeOf, gradMode, modeMat, frameMat]

theorem secondModeOf_zeroTuple (n : ℤ) (a b c : Fin 3) :
    L.secondModeOf n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a b c = fun _ => 0 := by
  funext p
  simp [CellLayout.secondModeOf, modeThird, frameThird]

theorem pressureGradMode_zeroTuple (n : ℤ) (a : Fin 3) :
    L.pressureGradMode n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) a = fun _ => 0 := by
  funext p
  fin_cases a <;> simp [CellLayout.pressureGradMode, modeVec, frameVec]

theorem headPressure_zeroTuple (n : ℤ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), headPressure L n ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) p = 0 := by
  have hz : (0 : ℝ) • (0 : Space → Space) + (0 : ℝ) • (0 : Space → Space) = 0 := by simp
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.potential_affine 0 0 isGradientField_zero isGradientField_zero 0 0
  set e := ⨍ z in Metric.ball (0 : Space) 1, potentialOf (0 : Space → Space) z with he
  have hA := MeshDataAffineModes.gradient_modes_affine L.order 0 0 isGradientField_zero isGradientField_zero
    0 0 C 0 0 e hC n
  rw [hz] at hC hA
  have hC' : potentialOf (0 : Space → Space) =ᵐ[volume] fun _ => C := by
    filter_upwards [hC] with y hy
    rw [hy]; ring
  have hmean : e = C := by
    rw [he, setAverage_congr_fun measurableSet_ball (hC'.mono fun y hy _ => hy)]
    exact setAverage_const (Metric.measure_ball_pos volume (0 : Space) one_pos).ne' measure_ball_lt_top.ne C
  filter_upwards [hA] with p hp
  have h1 := hp.1
  rw [hmean] at h1
  simp only [zero_mul, add_zero, sub_self, Complex.ofReal_zero] at h1
  have hP : headPotential (0 : Space → Space) = fun y => potentialOf (0 : Space → Space) y - C := by
    funext y
    simp only [headPotential]
    rw [← he, hmean]
  simp only [headPressure]
  rw [hP]
  simpa using h1

theorem keyValue_zeroTuple (key : SkeletonKey) :
    keyValue L ((0, 0, 0, 0, 0) : Assembly.FieldTuple 0) key = 0 := by
  cases key with
  | velocity n rad lev lo hi t a d =>
      simp only [keyValue, velMode_zeroTuple, gradModeOf_zeroTuple, segMoment_zero]
  | gradient n rad lev lo hi t a d =>
      simp only [keyValue, gradModeOf_zeroTuple, secondModeOf_zeroTuple, segMoment_zero, ite_self]
  | pressure n rad lev lo hi t d =>
      simp only [keyValue]
      rw [segMoment_congr_ae _ _ _ _ (headPressure_zeroTuple L n), pressureGradMode_zeroTuple,
        pressureGradMode_zeroTuple, segMoment_zero]
  | corner n p a =>
      simp only [keyValue, velMode_zeroTuple, gradModeOf_zeroTuple, secondModeOf_zeroTuple]
      simp [cornerMoment]
  | stream p =>
      simp only [keyValue, velMode_zeroTuple, gradModeOf_zeroTuple, heightStrip_zero]
  | private_ =>
      rfl

end ZeroTuple

theorem keyHarmonic_at_zero (L : CellLayout) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (key : SkeletonKey) :
    keyHarmonic L 0 v G H Pg key = keyValue L (CellCalculus.cosTuple 0 v G H Pg) key := by
  simp only [keyHarmonic, sinTuple_at_zero, keyValue_zeroTuple, mul_zero, add_zero]

end Breakdown.CertCell.PlanePairInternal


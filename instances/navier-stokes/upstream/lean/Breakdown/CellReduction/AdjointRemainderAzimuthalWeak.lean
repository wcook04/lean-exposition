import Breakdown.CellReduction.AdjointRemainderAzimuthalParts

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

open CellCert.Reduction FracInternal.FrameInverseSquareParts

namespace Internal

def planarMap : Space →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)
    + (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)

theorem planarMap_apply (x : Space) : planarMap x = x 0 • unitVector 0 + x 1 • unitVector 1 := by
  simp [planarMap]

theorem planarMap_zero_coord (x : Space) : planarMap x 0 = x 0 := by
  simp [planarMap_apply, unitVector]

theorem planarMap_one_coord (x : Space) : planarMap x 1 = x 1 := by
  simp [planarMap_apply, unitVector]

theorem planarMap_two_coord (x : Space) : planarMap x 2 = 0 := by
  simp [planarMap_apply, unitVector]

theorem planarMap_norm_sq_le (x : Space) : ‖planarMap x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three,
    planarMap_zero_coord, planarMap_one_coord, planarMap_two_coord]
  simp only [norm_zero]
  nlinarith [sq_nonneg ‖x 2‖]

theorem planarMap_norm_le (x : Space) : ‖planarMap x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (planarMap_norm_sq_le x)

theorem squareSum_planar_le (M : Space →L[ℝ] Space) : matSq (planarMap.comp M) ≤ matSq M := by
  unfold matSq
  exact Finset.sum_le_sum fun i _ => by
    rw [ContinuousLinearMap.comp_apply]
    exact planarMap_norm_sq_le _

theorem squareSum_nonneg_planar (M : Space →L[ℝ] Space) : 0 ≤ matSq M :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem horizontal_planar (W : Space → Space) :
    horizontalPart (fun y => planarMap (W y)) = horizontalPart W := by
  funext y
  simp only [horizontalPart, planarMap_zero_coord, planarMap_one_coord]

theorem vertical_planar (W : Space → Space) :
    verticalPart (fun y => planarMap (W y)) = fun _ => 0 := by
  funext y
  simp only [verticalPart, planarMap_two_coord, Complex.ofReal_zero]

theorem angularMode_zero (k : ℤ) (ρ z : ℝ) : angularMode (fun _ => (0 : ℂ)) k ρ z = 0 := by
  simp [angularMode]

theorem weightedSide_planar (W : Space → Space) (k : ℤ) :
    modeWeightedSide (fun y => planarMap (W y)) k =
      ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart W) k := by
  unfold modeWeightedSide modeInverseSquare
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [horizontal_planar, vertical_planar, angularMode_zero, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  simp only [modeWeight, Int.cast_abs, norm_zero]
  ring

end Internal

open Internal

theorem modeInverseSquareWeak_of (h1 : SmoothModeInverseSquareHolds) (h2 : WeakClassApproxHolds)
    (h3 : GradientModeTotalHolds) : ModeInverseSquareWeakHolds := by
  intro V D hV hD hw h6 hfin
  obtain ⟨u, hu, hGrad, hLoc⟩ := h2 V D hV hD hw h6 hfin
  set V' : Space → Space := fun y => planarMap (V y) with hV'def
  set u' : ℕ → Space → Space := fun n y => planarMap (u n y) with hu'def
  set D' : Space → (Space →L[ℝ] Space) := fun y => planarMap.comp (D y) with hD'def
  have hV'm : AEStronglyMeasurable V' volume := planarMap.continuous.comp_aestronglyMeasurable hV
  have hD'm : AEStronglyMeasurable D' volume :=
    (ContinuousLinearMap.compL ℝ Space Space Space planarMap).continuous.comp_aestronglyMeasurable hD
  have hu'smooth : ∀ n, ContDiff ℝ ∞ (u' n) := fun n => planarMap.contDiff.comp (hu n).1
  have hu'supp : ∀ n, HasCompactSupport (u' n) := fun n => (hu n).2.comp_left planarMap.map_zero
  have hfd : ∀ n y, fderiv ℝ (u' n) y = planarMap.comp (fderiv ℝ (u n) y) := by
    intro n y
    have hd : DifferentiableAt ℝ (u n) y :=
      ((hu n).1.differentiable (by simp)).differentiableAt
    exact (planarMap.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  have hLoc' : ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R,
      ENNReal.ofReal (‖u' n y - V' y‖ ^ 2)) atTop (𝓝 0) := by
    intro R
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hLoc R) (fun _ => zero_le)
      (fun n => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_)
    simp only [hu'def, hV'def, ← map_sub]
    exact planarMap_norm_sq_le _
  have hGrad' : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (SteadyCert.entrySq (fderiv ℝ (u' n) y - D' y))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGrad (fun _ => zero_le)
      (fun n => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_)
    rw [hfd, hD'def]
    simp only
    rw [← ContinuousLinearMap.comp_sub]
    exact squareSum_planar_le _
  have hD'fin : ∫⁻ y, ENNReal.ofReal (matSq (D' y)) ≤ ∫⁻ y, ENNReal.ofReal (matSq (D y)) :=
    lintegral_mono fun y => ENNReal.ofReal_le_ofReal (squareSum_planar_le _)
  have hD'int : Integrable (fun y => SteadyCert.entrySq (D' y)) := by
    have hm : AEStronglyMeasurable (fun y => matSq (D' y)) volume := by
      have hc : Continuous (fun M : Space →L[ℝ] Space => matSq M) := by
        unfold matSq
        fun_prop
      exact hc.comp_aestronglyMeasurable hD'm
    refine ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => squareSum_nonneg_planar _)).2 ?_⟩
    exact lt_of_le_of_lt hD'fin hfin
  have hGm : ∀ n, AEStronglyMeasurable (fun y => fderiv ℝ (u' n) y) volume := fun n =>
    ((hu'smooth n).continuous_fderiv (by simp)).aestronglyMeasurable
  have hlim := FracInternal.FrameInverseSquareParts.modeGradientLimit D' (fun n y => fderiv ℝ (u' n) y)
    hD'm hGm hD'int hGrad'
  have hk : ∀ k : ℤ, ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart V) k ≤
      modeGradientSide D' k := by
    intro k
    have e1 := weightedSide_planar V k
    have hl := FracInternal.FrameInverseSquareParts.modeWeightedLower V' u' hV'm
      (fun n => (hu'smooth n).continuous) hLoc' k
    have hs : ∀ n, modeWeightedSide (u' n) k ≤ modeGradientSide (fun y => fderiv ℝ (u' n) y) k := by
      intro n
      have e2 := weightedSide_planar (u n) k
      have h := h1 (u' n) (hu'smooth n) (hu'supp n) k
      have e3 : horizontalPart (u' n) = horizontalPart (u n) := horizontal_planar (u n)
      rw [e3] at h
      exact e2.le.trans h
    have h3' : liminf (fun n => modeWeightedSide (u' n) k) atTop ≤
        liminf (fun n => modeGradientSide (fun y => fderiv ℝ (u' n) y) k) atTop :=
      liminf_le_liminf (Eventually.of_forall hs)
    rw [(hlim k).liminf_eq] at h3'
    rw [← e1]
    exact hl.trans h3'
  calc ∑' k : ℤ, ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart V) k
      ≤ ∑' k : ℤ, modeGradientSide D' k := ENNReal.tsum_le_tsum hk
    _ ≤ ∫⁻ y, ENNReal.ofReal (matSq (D' y)) := h3 D' hD'm
    _ ≤ ∫⁻ y, ENNReal.ofReal (matSq (D y)) := hD'fin

end AzimuthalParts

end AdjointDefect

end Breakdown

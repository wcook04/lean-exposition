import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenProfileBoundsFieldParts
import Breakdown.FracCell.FieldJointSmooth

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracCellInternal

open CellCert.GivenFields

private theorem weight_near {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ R) (A : ℝ) : A ≤ |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by
  have h1 : 0 < 1 + s := by linarith
  have h2 : 1 ≤ 1 + R := by linarith
  have hR : 0 < 1 + R := by linarith
  have e1 : (1 + R) ^ (-k) ≤ (1 + s) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
  have e2 : (1 + R) ^ k ≤ (1 + R) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2 hk3
  have e3 : (1 + R) ^ k * (1 + R) ^ (-k) = 1 := by
    rw [Real.rpow_neg hR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR k).ne']
  have e4 : 0 ≤ (1 + R) ^ (-k) := (Real.rpow_pos_of_pos hR _).le
  calc A ≤ |A| := le_abs_self A
    _ = |A| * ((1 + R) ^ k * (1 + R) ^ (-k)) := by rw [e3, mul_one]
    _ ≤ |A| * ((1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        exact mul_le_mul e2 e1 e4 (Real.rpow_pos_of_pos hR _).le
    _ = |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by ring

private theorem weight_far {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {s : ℝ} (hs : 1 ≤ s) (A : ℝ) :
    A * s ^ (-k) ≤ |A| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by
  have h0 : 0 < s := by linarith
  have h1 : 0 < (1 + s) / 2 := by linarith
  have e1 : s ^ (-k) ≤ ((1 + s) / 2) ^ (-k) :=
    Real.rpow_le_rpow_of_nonpos h1 (by linarith) (by linarith)
  have e2 : ((1 + s) / 2) ^ (-k) = (2 : ℝ) ^ k * (1 + s) ^ (-k) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have e3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk3
  have e5 : 0 ≤ (1 + s) ^ (-k) := (Real.rpow_pos_of_pos (by linarith) _).le
  have e6 : 0 ≤ s ^ (-k) := (Real.rpow_pos_of_pos h0 _).le
  calc A * s ^ (-k) ≤ |A| * s ^ (-k) := mul_le_mul_of_nonneg_right (le_abs_self A) e6
    _ ≤ |A| * ((2 : ℝ) ^ k * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        rw [← e2]
        exact e1
    _ ≤ |A| * ((2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg A)
        exact mul_le_mul_of_nonneg_right e3 e5
    _ = |A| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by ring

private theorem weight_near_sum {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ R) (A D : ℝ) :
    A ≤ (|A| * (1 + R) ^ (3 : ℝ) + |D| * (2 : ℝ) ^ (3 : ℝ)) * (1 + s) ^ (-k) := by
  have h := weight_near hk3 hk0 hs0 hs A
  have h' : 0 ≤ |D| * (2 : ℝ) ^ (3 : ℝ) * (1 + s) ^ (-k) := by positivity
  rw [add_mul]
  linarith

private theorem weight_far_sum {k : ℝ} (hk3 : k ≤ 3) (hk0 : 0 ≤ k) {R s : ℝ} (hR : 1 ≤ R)
    (hs : R ≤ s) (A D : ℝ) :
    D * s ^ (-k) ≤ (|A| * (1 + R) ^ (3 : ℝ) + |D| * (2 : ℝ) ^ (3 : ℝ)) * (1 + s) ^ (-k) := by
  have h := weight_far hk3 hk0 (hR.trans hs) D
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + R := by linarith
  have h' : 0 ≤ |A| * (1 + R) ^ (3 : ℝ) * (1 + s) ^ (-k) := by positivity
  rw [add_mul]
  linarith

private theorem divergence_zero_of_ae {f : Space → Space} (hf : ContDiff ℝ 1 f)
    (h : ∀ᵐ y ∂(volume : Measure Space), divergenceAt f y = 0) (y : Space) :
    divergenceAt f y = 0 := by
  have hc : Continuous (divergenceAt f) := by
    unfold divergenceAt
    refine continuous_finsetSum _ fun i _ => ?_
    exact (PiLp.continuous_apply 2 _ i).comp
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  exact congrFun ((Continuous.ae_eq_iff_eq volume hc continuous_const).1 h) y

private theorem fieldOf_contDiff_one (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) : ContDiff ℝ 1 (fieldOf P F β) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fieldOf_differentiable P hP F hF β, ?_⟩
  have h := (fieldOf_fderiv_joint_continuous P hP F hF).comp
    (continuous_const.prodMk continuous_id : Continuous fun y : Space => ((β, y) : ℝ × Space))
  exact h

private theorem fieldOf_near_bounds (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B R : ℝ) :
    ∃ C : ℝ, ∀ β : ℝ, |β| ≤ B → ∀ y : Space, ‖y‖ ≤ R →
      ‖fieldOf P F β y‖ ≤ C ∧ ‖fderiv ℝ (fieldOf P F β) y‖ ≤ C ∧
        LipschitzOnWith (Real.toNNReal C) (fderiv ℝ (fieldOf P F β)) (Metric.ball y 1) := by
  have hS : IsCompact (Set.Icc (-B) B ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C1, h1⟩ := hS.exists_bound_of_continuousOn (fieldOf_joint_continuous P hP F hF).continuousOn
  obtain ⟨C2, h2⟩ :=
    hS.exists_bound_of_continuousOn (fieldOf_fderiv_joint_continuous P hP F hF).continuousOn
  obtain ⟨K, hK⟩ := fieldOf_fderiv_slope_uniform P hP F hF B (R + 1)
  refine ⟨max (max C1 C2) (K : ℝ), fun β hβ y hy => ?_⟩
  have hq : ((β, y) : ℝ × Space) ∈ Set.Icc (-B) B ×ˢ Metric.closedBall (0 : Space) R := by
    refine ⟨abs_le.mp hβ, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy
  refine ⟨((h1 _ hq).trans (le_max_left C1 C2)).trans (le_max_left _ _),
    ((h2 _ hq).trans (le_max_right C1 C2)).trans (le_max_left _ _), ?_⟩
  have hsub : Metric.ball y 1 ⊆ Metric.closedBall (0 : Space) (R + 1) := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    rw [dist_eq_norm] at hz
    linarith
  refine ((hK β hβ).mono hsub).weaken ?_
  calc K = Real.toNNReal (K : ℝ) := (Real.toNNReal_coe).symm
    _ ≤ Real.toNNReal (max (max C1 C2) (K : ℝ)) := Real.toNNReal_le_toNNReal (le_max_right _ _)

theorem fieldOf_decay (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B : ℝ) :
    ∃ C : ℝ, ∀ β : ℝ, |β| ≤ B → ContDiff ℝ 1 (fieldOf P F β) ∧ ∀ y : Space,
      ‖fieldOf P F β y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
        ‖fderiv ℝ (fieldOf P F β) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * (1 + ‖y‖) ^ (-(3 : ℝ))))
            (fderiv ℝ (fieldOf P F β)) (Metric.ball y 1) := by
  obtain ⟨R0, Cf, hfar⟩ := fieldOf_far_bounds P hP F hF B
  obtain ⟨Cn, hnear⟩ := fieldOf_near_bounds P hP F hF B (max R0 1)
  have hR1 : 1 ≤ max R0 1 := le_max_right _ _
  refine ⟨|Cn| * (1 + max R0 1) ^ (3 : ℝ) + |Cf| * (2 : ℝ) ^ (3 : ℝ), fun β hβ =>
    ⟨fieldOf_contDiff_one P hP F hF β, fun y => ?_⟩⟩
  rcases le_total ‖y‖ (max R0 1) with h | h
  · obtain ⟨a1, a2, a3⟩ := hnear β hβ y h
    refine ⟨a1.trans (weight_near_sum (by norm_num) (by norm_num) (norm_nonneg y) h Cn Cf),
      a2.trans (weight_near_sum (by norm_num) (by norm_num) (norm_nonneg y) h Cn Cf),
      a3.weaken (Real.toNNReal_le_toNNReal
        (weight_near_sum (by norm_num) (by norm_num) (norm_nonneg y) h Cn Cf))⟩
  · obtain ⟨a1, a2, a3⟩ := hfar β hβ y ((le_max_left _ _).trans h)
    refine ⟨a1.trans (weight_far_sum (by norm_num) (by norm_num) hR1 h Cn Cf),
      a2.trans (weight_far_sum (by norm_num) (by norm_num) hR1 h Cn Cf),
      a3.weaken (Real.toNNReal_le_toNNReal
        (weight_far_sum (by norm_num) (by norm_num) hR1 h Cn Cf))⟩

theorem fieldOf_divergence (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) (y : Space) : divergenceAt (fieldOf P F β) y = 0 :=
  divergence_zero_of_ae (fieldOf_contDiff_one P hP F hF β) (fieldOf_div_ae P hP F hF β) y

private theorem fieldOf_joint_contDiffAt_ae (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (β₀ : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space),
      ContDiffAt ℝ 2 (fun q : ℝ × Space => fieldOf P F q.1 q.2) ((β₀, y) : ℝ × Space) := by
  have hS : ∀ S : Spline, ∀ᵐ y ∂(volume : Measure Space),
      chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks :=
    fun S => (FracInternal.ae_generic P hP.L0_pos S.mesh.tBreaks S.mesh.xBreaks).mono
      fun y h => ⟨h.2.2.2.1, h.2.2.2.2⟩
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ n ∈ F.modes,
      ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp, (F.amp n).swirlAmp],
        chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [hS (F.amp n).radialAmp, hS (F.amp n).polarAmp, hS (F.amp n).streamAmp,
      hS (F.amp n).swirlAmp] with y h1 h2 h3 h4
    intro S hS'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS'
    rcases hS' with rfl | rfl | rfl | rfl <;> assumption
  filter_upwards [FracInternal.ae_generic P hP.L0_pos [] [], hall] with y h0 hg
  have hy0 : y ≠ 0 := fun h => h0.2.1 (by simp [h])
  have hx0 : heightRatio y ≠ 0 := by
    unfold heightRatio
    exact div_ne_zero h0.2.2.1 (norm_ne_zero_iff.2 hy0)
  exact (FracInternal.FieldJoint.joint_fieldOf P hP F hy0 h0.2.1 hx0 hg β₀).of_le
    (WithTop.coe_le_coe.2 le_top)

private theorem phaseDeriv_div_of_smooth (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) (y : Space)
    (hC : ContDiffAt ℝ 2 (fun q : ℝ × Space => fieldOf P F q.1 q.2) ((β₀, y) : ℝ × Space)) :
    divergenceAt (fun y => deriv (fun β => fieldOf P F β y) β₀) y = 0 := by
  set G : ℝ × Space → Space := fun q => fieldOf P F q.1 q.2 with hG
  have hdiff : ∀ᶠ q in nhds ((β₀, y) : ℝ × Space), DifferentiableAt ℝ G q :=
    (hC.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ G) (β₀, y) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hC.isSymmSndFDerivAt (by simp)
  have hsl : ∀ b : ℝ, HasFDerivAt (fun y' : Space => ((b, y') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y := fun b =>
    (hasFDerivAt_const b y).prodMk (hasFDerivAt_id y)
  have hbl : ∀ z : Space,
      HasDerivAt (fun b : ℝ => ((b, z) : ℝ × Space)) ((1 : ℝ), (0 : Space)) β₀ :=
    fun z => (hasDerivAt_id' β₀).prodMk (hasDerivAt_const β₀ z)
  have hty : Filter.Tendsto (fun y' : Space => ((β₀, y') : ℝ × Space)) (nhds y) (nhds (β₀, y)) :=
    (hsl β₀).continuousAt.tendsto
  have htb : Filter.Tendsto (fun b : ℝ => ((b, y) : ℝ × Space)) (nhds β₀) (nhds (β₀, y)) :=
    (hbl y).continuousAt.tendsto
  have hgeq : (fun y' => deriv (fun β => fieldOf P F β y') β₀) =ᶠ[nhds y]
      fun y' => fderiv ℝ G (β₀, y') ((1 : ℝ), (0 : Space)) := by
    filter_upwards [hty.eventually hdiff] with y' hy'
    exact (hy'.hasFDerivAt.comp_hasDerivAt β₀ (hbl y')).deriv
  have hfd : ∀ v : Space, fderiv ℝ (fun y' => deriv (fun β => fieldOf P F β y') β₀) y v =
      fderiv ℝ (fderiv ℝ G) (β₀, y) ((0 : ℝ), v) ((1 : ℝ), (0 : Space)) := by
    intro v
    rw [hgeq.fderiv_eq]
    have h1 : HasFDerivAt (fun y' : Space => fderiv ℝ G (β₀, y') ((1 : ℝ), (0 : Space))) _ y :=
      (hD2.hasFDerivAt.comp y (hsl β₀)).clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) y)
    rw [h1.fderiv]
    simp
  set Λ : ((ℝ × Space) →L[ℝ] Space) →L[ℝ] ℝ := ∑ i : Fin 3,
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space ((0 : ℝ), unitVector i)) with hΛ
  have hΛa : ∀ L : (ℝ × Space) →L[ℝ] Space, Λ L = ∑ i : Fin 3, (L ((0 : ℝ), unitVector i)) i := by
    intro L
    simp [hΛ]
  have hzero : (fun b : ℝ => Λ (fderiv ℝ G (b, y))) =ᶠ[nhds β₀] fun _ => (0 : ℝ) := by
    filter_upwards [htb.eventually hdiff] with b hb
    have h2 : fderiv ℝ (fieldOf P F b) y =
        (fderiv ℝ G (b, y)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) :=
      (hb.hasFDerivAt.comp y (hsl b)).fderiv
    have hdz := fieldOf_divergence P hP F hF b y
    unfold divergenceAt at hdz
    rw [h2] at hdz
    rw [hΛa]
    simpa using hdz
  have hder : HasDerivAt (fun b : ℝ => Λ (fderiv ℝ G (b, y)))
      (Λ (fderiv ℝ (fderiv ℝ G) (β₀, y) ((1 : ℝ), (0 : Space)))) β₀ :=
    Λ.hasFDerivAt.comp_hasDerivAt β₀ (hD2.hasFDerivAt.comp_hasDerivAt β₀ (hbl y))
  have hval : Λ (fderiv ℝ (fderiv ℝ G) (β₀, y) ((1 : ℝ), (0 : Space))) = 0 := by
    rw [← hder.deriv, hzero.deriv_eq]
    simp
  rw [hΛa] at hval
  unfold divergenceAt
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hval
  rw [hfd, hsym ((0 : ℝ), unitVector i) ((1 : ℝ), (0 : Space))]

theorem fieldOf_phaseDeriv_regular (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) :
    ContDiff ℝ 1 (fun y => deriv (fun β => fieldOf P F β y) β₀) ∧
      (∀ y, divergenceAt (fun y => deriv (fun β => fieldOf P F β y) β₀) y = 0) ∧
        ∃ C : ℝ, ∀ y, ‖deriv (fun β => fieldOf P F β y) β₀‖ ≤ C * (1 + ‖y‖)⁻¹ ∧
          ‖fderiv ℝ (fun y => deriv (fun β => fieldOf P F β y) β₀) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
  have hc := phaseDeriv_contDiff P hP F hF β₀
  refine ⟨hc, divergence_zero_of_ae hc ?_, ?_⟩
  · filter_upwards [fieldOf_joint_contDiffAt_ae P hP F β₀] with y hy
    exact phaseDeriv_div_of_smooth P hP F hF β₀ y hy
  obtain ⟨R0, Cf, hfar⟩ := phaseDeriv_far_bounds P hP F hF β₀
  have hR1 : 1 ≤ max R0 1 := le_max_right _ _
  obtain ⟨C1, h1⟩ := (isCompact_closedBall (0 : Space) (max R0 1)).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  obtain ⟨C2, h2⟩ := (isCompact_closedBall (0 : Space) (max R0 1)).exists_bound_of_continuousOn
    (hc.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨|max C1 C2| * (1 + max R0 1) ^ (3 : ℝ) + |Cf| * (2 : ℝ) ^ (3 : ℝ), fun y => ?_⟩
  have hp : 0 < 1 + ‖y‖ := by positivity
  rw [← Real.rpow_neg_one]
  rcases le_total ‖y‖ (max R0 1) with h | h
  · have hy : y ∈ Metric.closedBall (0 : Space) (max R0 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact h
    exact ⟨((h1 y hy).trans (le_max_left C1 C2)).trans
        (weight_near_sum (by norm_num) (by norm_num) (norm_nonneg y) h (max C1 C2) Cf),
      ((h2 y hy).trans (le_max_right C1 C2)).trans
        (weight_near_sum (by norm_num) (by norm_num) (norm_nonneg y) h (max C1 C2) Cf)⟩
  · obtain ⟨a1, a2⟩ := hfar y ((le_max_left _ _).trans h)
    exact ⟨a1.trans (weight_far_sum (by norm_num) (by norm_num) hR1 h (max C1 C2) Cf),
      a2.trans (weight_far_sum (by norm_num) (by norm_num) hR1 h (max C1 C2) Cf)⟩

end FracCellInternal

end Breakdown

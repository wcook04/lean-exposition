import Breakdown.CertCell.InstanceStatements

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox cylRadius cylHeight radialUnit angularUnit axialUnit)

namespace Internal.Regular

theorem pointAngle_measurable : Measurable pointAngle := by
  unfold pointAngle; fun_prop

theorem pointPlane_continuous : Continuous pointPlane := by
  unfold pointPlane; fun_prop

theorem solid_measurableSet (K : CellBox) : MeasurableSet K.solid := by
  have hr : Measurable cylRadius := by unfold cylRadius; fun_prop
  have hz : Measurable fun y : Space => |cylHeight y| := by unfold cylHeight; fun_prop
  exact (measurableSet_le measurable_const hr).inter ((measurableSet_le hr measurable_const).inter
    ((measurableSet_le measurable_const hz).inter (measurableSet_le hz measurable_const)))

theorem single_eq_smul_unit (i : Fin 3) (x : ℝ) : EuclideanSpace.single i x = x • unitVector i := by
  ext j
  by_cases h : j = i <;> simp [unitVector, h]

theorem frameUnit_continuous (a : Fin 3) : Continuous (fun θ => frameUnit θ a) := by
  fin_cases a <;> simp only [frameUnit, radialUnit, angularUnit, axialUnit, single_eq_smul_unit] <;> fun_prop

theorem frameUnit_norm_eq (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  fin_cases a <;> simp [frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three, PiLp.single_apply]

theorem frameTerm_continuous (a b : Fin 3) :
    Continuous (fun θ => (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)) :=
  (ContinuousLinearMap.smulRightL ℝ Space Space).continuous₂.comp
    (((innerSL ℝ).continuous.comp (frameUnit_continuous b)).prodMk (frameUnit_continuous a))

theorem cellPoly_continuous (K : CellBox) (P : CellPoly) : Continuous (P.eval K) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ; fun_prop

theorem frameSign_abs (a : Fin 3) : |frameSign a| = 1 := by
  unfold frameSign; split_ifs <;> simp

theorem labelPhase_periodic (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m ι (σ + 1) θ = labelPhase m ι σ θ := by
  unfold labelPhase
  have e : ((2 * Real.pi * (labelTime ι : ℝ) * (σ + 1) + (labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ) * Complex.I
        + (labelTime ι : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem labelPhase_norm (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) : ‖labelPhase m ι σ θ‖ = 1 := by
  unfold labelPhase; exact Complex.norm_exp_ofReal_mul_I _

theorem coef_abs_le (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) (v : ℂ) :
    |(labelPhase m ι σ θ * v).re| ≤ ‖v‖ := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, labelPhase_norm, one_mul]

theorem labelValueAt_measurable {count : ℕ} (box : Fin count → CellBox)
    (comp : Fin count → ℤ × ℤ → CellPoly) (K : Fin count) (ι : ℤ × ℤ) (s : ℝ) :
    Measurable (fun y : Space => labelValueAt box comp K ι s (pointPlane y)) := by
  unfold labelValueAt
  have h1 := cellPoly_continuous (box K) (comp K ι)
  have h2 := cellPoly_continuous (box K) (comp K (labelFlip ι))
  have hp := pointPlane_continuous
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le measurable_const (continuous_snd.comp hp).measurable
  · exact (h1.comp hp).measurable
  · have h3 : Continuous (fun y : Space => ((pointPlane y).1, -(pointPlane y).2)) :=
      (continuous_fst.comp hp).prodMk (continuous_snd.comp hp).neg
    exact (continuous_const.mul (h2.comp h3)).measurable

theorem coef_measurable {count : ℕ} (box : Fin count → CellBox)
    (comp : Fin count → ℤ × ℤ → CellPoly) (K : Fin count) (ι : ℤ × ℤ) (s : ℝ) (m : ℕ) :
    Measurable (fun z : ℝ × Space =>
      (labelPhase m ι z.1 (pointAngle z.2) * labelValueAt box comp K ι s (pointPlane z.2)).re) := by
  have hc : Continuous (fun p : ℝ × ℝ => labelPhase m ι p.1 p.2) := by unfold labelPhase; fun_prop
  have h1 : Measurable (fun z : ℝ × Space => labelPhase m ι z.1 (pointAngle z.2)) :=
    hc.measurable.comp (measurable_fst.prodMk (pointAngle_measurable.comp measurable_snd))
  have h2 : Measurable (fun z : ℝ × Space => labelValueAt box comp K ι s (pointPlane z.2)) :=
    (labelValueAt_measurable box comp K ι s).comp measurable_snd
  exact Complex.measurable_re.comp (h1.mul h2)

theorem labelValueAt_bound {count : ℕ} (box : Fin count → CellBox)
    (comp : Fin count → ℤ × ℤ → CellPoly) (K : Fin count) (ι : ℤ × ℤ) (s : ℝ) (hs : |s| ≤ 1) :
    ∃ C : ℝ, ∀ y ∈ (box K).solid, ‖labelValueAt box comp K ι s (pointPlane y)‖ ≤ C := by
  have hc : IsCompact (box K).rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₁, hC₁⟩ := hc.exists_bound_of_continuousOn (cellPoly_continuous (box K) (comp K ι)).continuousOn
  obtain ⟨C₂, hC₂⟩ :=
    hc.exists_bound_of_continuousOn (cellPoly_continuous (box K) (comp K (labelFlip ι))).continuousOn
  refine ⟨|C₁| + |C₂|, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy
  have hr : (pointPlane y).1 = cylRadius y := rfl
  have hz : (pointPlane y).2 = cylHeight y := rfl
  unfold labelValueAt
  split_ifs with h
  · have ha : |cylHeight y| = (pointPlane y).2 := by rw [hz] at h ⊢; exact abs_of_nonneg h
    have hm : pointPlane y ∈ (box K).rect :=
      Set.mem_prod.2 ⟨⟨hr ▸ h1, hr ▸ h2⟩, ⟨ha ▸ h3, ha ▸ h4⟩⟩
    exact ((hC₁ _ hm).trans (le_abs_self _)).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have ha : |cylHeight y| = -(pointPlane y).2 := by
      rw [hz] at h ⊢; exact abs_of_neg (not_le.1 h)
    have hm : ((pointPlane y).1, -(pointPlane y).2) ∈ (box K).rect :=
      Set.mem_prod.2 ⟨⟨hr ▸ h1, hr ▸ h2⟩, ⟨ha ▸ h3, ha ▸ h4⟩⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |s| * ‖(comp K (labelFlip ι)).eval (box K) ((pointPlane y).1, -(pointPlane y).2)‖
        ≤ 1 * |C₂| := mul_le_mul hs ((hC₂ _ hm).trans (le_abs_self _)) (norm_nonneg _) zero_le_one
      _ ≤ |C₁| + |C₂| := by rw [one_mul]; exact le_add_of_nonneg_left (abs_nonneg _)

theorem solid_norm_le (K : CellBox) (y : Space) (hy : y ∈ K.solid) : ‖y‖ ≤ |K.r₂| + |K.z₂| := by
  obtain ⟨-, h2, -, h4⟩ := hy
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hrsq : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hzsq : |cylHeight y| ^ 2 = y 2 ^ 2 := sq_abs _
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hr' : cylRadius y ≤ |K.r₂| := h2.trans (le_abs_self _)
  have hz' : |cylHeight y| ≤ |K.z₂| := h4.trans (le_abs_self _)
  have hz0 : 0 ≤ |cylHeight y| := abs_nonneg _
  have hsq : ‖y‖ ^ 2 ≤ (|K.r₂| + |K.z₂|) ^ 2 := by
    nlinarith [abs_nonneg K.r₂, abs_nonneg K.z₂, mul_le_mul hr' hr' hr0 (abs_nonneg K.r₂),
      mul_le_mul hz' hz' hz0 (abs_nonneg K.z₂)]
  nlinarith [norm_nonneg y, abs_nonneg K.r₂, abs_nonneg K.z₂]

theorem outside_solids {count : ℕ} (box : Fin count → CellBox) (y : Space) (K : Fin count)
    (hy : ∑ L, (|(box L).r₂| + |(box L).z₂|) < ‖y‖) : y ∉ (box K).solid := fun h =>
  absurd ((solid_norm_le _ y h).trans (Finset.single_le_sum (f := fun L => |(box L).r₂| + |(box L).z₂|)
    (fun L _ => by positivity) (Finset.mem_univ K))) (not_le.2 hy)

theorem period_finite (g : ℝ → Space → ℝ) (c R : ℝ) (hg : ∀ σ y, g σ y ≤ c)
    (hR : ∀ σ y, R < ‖y‖ → g σ y = 0) : periodLIntegral g < ⊤ := by
  unfold periodLIntegral
  have hin : ∀ σ, ∫⁻ y, ENNReal.ofReal (g σ y) ≤
      ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) := by
    intro σ
    calc ∫⁻ y, ENNReal.ofReal (g σ y)
        ≤ ∫⁻ y, (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal c) y := by
          refine lintegral_mono fun y => ?_
          by_cases h : y ∈ Metric.closedBall (0 : Space) R
          · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_le_ofReal (hg σ y)
          · rw [Set.indicator_of_notMem h]
            have hlt : R < ‖y‖ := by
              rw [Metric.mem_closedBall, dist_zero_right, not_le] at h; exact h
            rw [hR σ y hlt, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) :=
          lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
  have hfin : ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y)
      ≤ ∫⁻ _σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) :=
        lintegral_mono fun σ => hin σ
    _ = ENNReal.ofReal c * volume (Metric.closedBall (0 : Space) R) * volume (Set.Icc (0 : ℝ) 1) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top hfin (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

theorem matSq_le (G : Space →L[ℝ] Space) (B : ℝ) (h : ‖G‖ ≤ B) : matSq G ≤ 3 * B ^ 2 := by
  unfold matSq
  have hi : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ B ^ 2 := fun i => by
    have h1 : ‖G (unitVector i)‖ ≤ B := by
      refine (G.le_opNorm _).trans ?_
      rw [show ‖unitVector i‖ = 1 by simp [unitVector], mul_one]; exact h
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, B ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * B ^ 2 := by simp

theorem frameMap_norm_le (θ : ℝ) (x : Fin 3 → Fin 3 → ℝ) :
    ‖CellMatField.frameMap θ x‖ ≤ ∑ a, ∑ b, |x a b| := by
  unfold CellMatField.frameMap
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, frameUnit_norm_eq,
    frameUnit_norm_eq, Real.norm_eq_abs, mul_one, mul_one]

theorem vec_measurable (M : CellMesh) (F : CellVecField M.count) (m : ℕ) :
    Measurable (fun z : ℝ × Space => F.field M.box m z.1 z.2) := by
  unfold CellVecField.field
  refine Finset.measurable_sum _ fun K _ => Measurable.ite (measurable_snd (solid_measurableSet _)) ?_
    measurable_const
  refine Finset.measurable_sum _ fun ι _ => Finset.measurable_sum _ fun a _ => ?_
  exact (coef_measurable M.box (fun K ι => F.comp K ι a) K ι (frameSign a) m).smul
    ((frameUnit_continuous a).measurable.comp (pointAngle_measurable.comp measurable_snd))

theorem mat_measurable (M : CellMesh) (F : CellMatField M.count) (m : ℕ) :
    Measurable (fun z : ℝ × Space => F.field M.box m z.1 z.2) := by
  unfold CellMatField.field CellMatField.frameMap
  refine Finset.measurable_sum _ fun K _ => Measurable.ite (measurable_snd (solid_measurableSet _)) ?_
    measurable_const
  refine Finset.measurable_sum _ fun ι _ => Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun b _ => ?_
  exact (coef_measurable M.box (fun K ι => F.comp K ι a b) K ι (frameSign a * frameSign b) m).smul
    ((frameTerm_continuous a b).measurable.comp (pointAngle_measurable.comp measurable_snd))

theorem vec_periodic (M : CellMesh) (F : CellVecField M.count) (m : ℕ) :
    IsTimePeriodic (F.field M.box m) := by
  intro σ y
  simp only [CellVecField.field, labelPhase_periodic]

theorem mat_periodic (M : CellMesh) (F : CellMatField M.count) (m : ℕ) :
    IsTimePeriodic (F.field M.box m) := by
  intro σ y
  simp only [CellMatField.field, labelPhase_periodic]

theorem vec_bound (M : CellMesh) (F : CellVecField M.count) (m : ℕ) :
    ∃ B : ℝ, ∀ σ y, ‖F.field M.box m σ y‖ ≤ B := by
  have h : ∀ K ι a, ∃ C : ℝ, ∀ y ∈ (M.box K).solid, ‖F.planeValue M.box K ι a (pointPlane y)‖ ≤ C :=
    fun K ι a => labelValueAt_bound M.box (fun K ι => F.comp K ι a) K ι (frameSign a)
      (frameSign_abs a).le
  choose C hC using h
  refine ⟨∑ K, ∑ ι ∈ F.labels K, ∑ a : Fin 3, |C K ι a|, fun σ y => ?_⟩
  unfold CellVecField.field
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun K _ => ?_)
  by_cases hy : y ∈ (M.box K).solid
  · rw [Set.indicator_of_mem hy]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_smul, frameUnit_norm_eq, mul_one, Real.norm_eq_abs]
    exact (coef_abs_le _ _ _ _ _).trans ((hC K ι a y hy).trans (le_abs_self _))
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact Finset.sum_nonneg fun ι _ => Finset.sum_nonneg fun a _ => abs_nonneg _

theorem mat_bound (M : CellMesh) (F : CellMatField M.count) (m : ℕ) :
    ∃ B : ℝ, ∀ σ y, ‖F.field M.box m σ y‖ ≤ B := by
  have h : ∀ K ι a b, ∃ C : ℝ, ∀ y ∈ (M.box K).solid,
      ‖F.planeValue M.box K ι a b (pointPlane y)‖ ≤ C :=
    fun K ι a b => labelValueAt_bound M.box (fun K ι => F.comp K ι a b) K ι (frameSign a * frameSign b)
      (by rw [abs_mul, frameSign_abs, frameSign_abs, mul_one])
  choose C hC using h
  refine ⟨∑ K, ∑ ι ∈ F.labels K, ∑ a : Fin 3, ∑ b : Fin 3, |C K ι a b|, fun σ y => ?_⟩
  unfold CellMatField.field
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun K _ => ?_)
  by_cases hy : y ∈ (M.box K).solid
  · rw [Set.indicator_of_mem hy]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
    refine (frameMap_norm_le _ _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_)
    exact (coef_abs_le _ _ _ _ _).trans ((hC K ι a b y hy).trans (le_abs_self _))
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact Finset.sum_nonneg fun ι _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      abs_nonneg _

theorem vec_vanish (M : CellMesh) (F : CellVecField M.count) (m : ℕ) (σ : ℝ) (y : Space)
    (hy : ∑ K, (|(M.box K).r₂| + |(M.box K).z₂|) < ‖y‖) : F.field M.box m σ y = 0 := by
  unfold CellVecField.field
  exact Finset.sum_eq_zero fun K _ => Set.indicator_of_notMem (outside_solids M.box y K hy) _

theorem mat_vanish (M : CellMesh) (F : CellMatField M.count) (m : ℕ) (σ : ℝ) (y : Space)
    (hy : ∑ K, (|(M.box K).r₂| + |(M.box K).z₂|) < ‖y‖) : F.field M.box m σ y = 0 := by
  unfold CellMatField.field
  exact Finset.sum_eq_zero fun K _ => Set.indicator_of_notMem (outside_solids M.box y K hy) _

end Internal.Regular

open Internal.Regular in
theorem cellVecFieldRegular : CellVecFieldRegular := by
  intro M F m _
  obtain ⟨B, hB⟩ := vec_bound M F m
  refine ⟨(vec_measurable M F m).aestronglyMeasurable, vec_periodic M F m,
    ⟨B, ∑ K, (|(M.box K).r₂| + |(M.box K).z₂|), fun σ y => ⟨hB σ y, vec_vanish M F m σ y⟩⟩, ?_⟩
  refine period_finite _ (B ^ 2) (∑ K, (|(M.box K).r₂| + |(M.box K).z₂|)) (fun σ y => ?_)
    (fun σ y hy => ?_)
  · exact pow_le_pow_left₀ (norm_nonneg _) (hB σ y) 2
  · rw [vec_vanish M F m σ y hy, norm_zero]; norm_num

open Internal.Regular in
theorem cellMatFieldRegular : CellMatFieldRegular := by
  intro M F m _
  obtain ⟨B, hB⟩ := mat_bound M F m
  refine ⟨(mat_measurable M F m).aestronglyMeasurable, mat_periodic M F m,
    ⟨B, ∑ K, (|(M.box K).r₂| + |(M.box K).z₂|), fun σ y => ⟨hB σ y, mat_vanish M F m σ y⟩⟩, ?_⟩
  refine period_finite _ (3 * B ^ 2) (∑ K, (|(M.box K).r₂| + |(M.box K).z₂|))
    (fun σ y => matSq_le _ B (hB σ y)) (fun σ y hy => ?_)
  rw [mat_vanish M F m σ y hy]
  simp [matSq]

end Breakdown.CertCell.Instance

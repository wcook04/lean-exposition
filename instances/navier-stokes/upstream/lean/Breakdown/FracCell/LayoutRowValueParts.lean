import Breakdown.FracCell.StFormulaProof
import Breakdown.FracCell.ModelField

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace FracInternal

namespace LayoutRowParts

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly CellCert.ModelFieldInternal SteadyCert.HeldWeakProfilePartsInternal

def transportPart {k N : ℕ} (c : FracCellData k N) (α : ℝ) (x : FieldTuple k) (y : Space) : Space :=
  driftField α c.modelRate x.1 x.2.1 y + crossVec (curlOf (x.2.1 y)) (c.modelVelocity y)
    + crossVec (c.modelCurl y) (x.1 y)

def gradientPairing {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (a : Fin N) : ℝ :=
  ∫ y, entryInner (x.2.1 y) (fderiv ℝ (c.row a) y)

def strainSum {k N slots : ℕ} (c : FracCellData k N) (α : ℝ) (L : CellLayout) (R : CellRows N slots k)
    (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin 3 × Fin 3 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1),
    strainRowCoef c α L.box L.bases R a i.1.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 *
      L.bases.coef L.box (L.gradModeOf i.1 x i.2.1 i.2.2.1) i.2.2.2.1 i.2.2.2.2

def velocitySum {k N slots : ℕ} (c : FracCellData k N) (α : ℝ) (L : CellLayout) (R : CellRows N slots k)
    (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef,
    velocityRowCoef c α L.box L.bases R a i.1.1 i.2.1 i.2.2.1 i.2.2.2 *
      L.bases.coef L.box (L.velMode i.1 x i.2.1) i.2.2.1 i.2.2.2

def gradSideSum {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin L.segCount × Fin 3 × Fin (L.degSide + 1),
    gradSideRowCoef c L a i.1.1 i.2.1 i.2.2.1 i.2.2.2 *
      (if (L.segment i.2.1).radial then
        (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 0)
          (L.secondModeOf i.1 x i.2.2.1 0 0) (L.secondModeOf i.1 x i.2.2.1 0 2) i.2.2.2
      else (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 2)
          (L.secondModeOf i.1 x i.2.2.1 2 0) (L.secondModeOf i.1 x i.2.2.1 2 2) i.2.2.2)

def presSideSum {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin L.presCount × Fin L.degSide,
    presSideRowCoef c L a i.1.1 i.2.1 i.2.2 *
      (L.presSegment i.2.1).moment true (L.pressMode i.1 x)
        (L.pressureGradMode i.1 x 0) (L.pressureGradMode i.1 x 2) i.2.2


private theorem solid_meas (K : CellBox) : MeasurableSet K.solid := by
  have h0 : Continuous cylRadius := by unfold cylRadius; fun_prop
  have h2 : Continuous (fun y : Space => |cylHeight y|) := by unfold cylHeight; fun_prop
  have he : K.solid = ({y | K.r₁ ≤ cylRadius y} ∩ {y | cylRadius y ≤ K.r₂}) ∩
      ({y | K.z₁ ≤ |cylHeight y|} ∩ {y | |cylHeight y| ≤ K.z₂}) := by
    ext y; simp only [CellBox.solid, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [he]
  exact (((measurableSet_le measurable_const h0.measurable).inter (measurableSet_le h0.measurable measurable_const)).inter
    ((measurableSet_le measurable_const h2.measurable).inter (measurableSet_le h2.measurable measurable_const)))

private theorem row_bounded {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {R : CellRows N slots k} (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) : ∃ C, ∀ y, ‖c.row a y‖ ≤ C := by
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  have hb : Bornology.IsBounded K.solid := hc.cellRegion_bounded.subset hD.solid_in_region
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hb
  have hup : ∃ C, ∀ y ∈ K.solid, 0 ≤ cylHeight y → ‖c.row a y‖ ≤ C := by
    rcases (K.solid ∩ {y | 0 ≤ cylHeight y}).eq_empty_or_nonempty with he | ⟨y0, hy0⟩
    · refine ⟨0, fun y hy hz => ?_⟩
      have hm : y ∈ K.solid ∩ {y | 0 ≤ cylHeight y} := ⟨hy, hz⟩
      rw [he] at hm
      exact absurd hm (Set.notMem_empty y)
    · refine ⟨‖c.row a y0‖ + L * (r + r), fun y hy hz => ?_⟩
      have h1 := hL.dist_le_mul y ⟨hy, hz⟩ y0 hy0
      have h2 : dist y y0 ≤ r + r :=
        (dist_le_norm_add_norm y y0).trans (add_le_add (hr y hy) (hr y0 hy0.1))
      have h3 : (L : ℝ) * dist y y0 ≤ L * (r + r) := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      have h4 := dist_triangle (c.row a y) (c.row a y0) 0
      simp only [dist_zero_right] at h4
      linarith
  obtain ⟨C, hC⟩ := hup
  have hnm : ∀ v : Space, ‖mirror v‖ = ‖v‖ := by
    intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [mirror, Fin.sum_univ_three]
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ K.solid
  · rcases le_or_gt 0 (cylHeight y) with hz | hz
    · exact (hC y hy hz).trans (le_max_left _ _)
    · have hmy : mirror y ∈ K.solid := by
        simp only [CellBox.solid, Set.mem_ofPred_eq] at hy ⊢
        have e1 : cylRadius (mirror y) = cylRadius y := by simp [cylRadius, mirror]
        have e2 : |cylHeight (mirror y)| = |cylHeight y| := by simp [cylHeight, mirror, abs_neg]
        rw [e1, e2]; exact hy
      have hmz : 0 ≤ cylHeight (mirror y) := by
        have : cylHeight (mirror y) = -cylHeight y := by simp [cylHeight, mirror]
        rw [this]; linarith
      rw [hR.row_mirror a ha y hy hz, hnm]
      exact (hC _ hmy hmz).trans (le_max_left _ _)
  · rw [hD.rows_in_cell a ha y hy, norm_zero]
    exact le_max_right _ _

private theorem solid_finite {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {R : CellRows N slots k} (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) :
    volume K.solid < ⊤ :=
  (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top

private theorem inner_row_integrable {row F : Space → Space} {T : Set Space} (hT : MeasurableSet T)
    (hrow : AEStronglyMeasurable row volume) {C : ℝ} (hC : ∀ y, ‖row y‖ ≤ C) (hsupp : ∀ y ∉ T, row y = 0)
    (hF : AEStronglyMeasurable F volume) (hFi : IntegrableOn (fun y => ‖F y‖) T) :
    Integrable (fun y => inner ℝ (F y) (row y)) := by
  refine Integrable.mono' ((show IntegrableOn (fun y => C * ‖F y‖) T volume from hFi.const_mul C).integrable_indicator hT) (hF.inner hrow) ?_
  filter_upwards with y
  by_cases hy : y ∈ T
  · rw [Set.indicator_of_mem hy]
    calc ‖inner ℝ (F y) (row y)‖ ≤ ‖F y‖ * ‖row y‖ := norm_inner_le_norm _ _
      _ ≤ ‖F y‖ * C := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
      _ = C * ‖F y‖ := mul_comm _ _
  · rw [Set.indicator_of_notMem hy, hsupp y hy, inner_zero_right, norm_zero]

private theorem integrableOn_of_two {F : Space → Space} {T : Set Space} (hT : volume T < ⊤)
    (hF : AEStronglyMeasurable F volume) (h2 : IntegrableOn (fun y => ‖F y‖ ^ 2) T) :
    IntegrableOn (fun y => ‖F y‖) T := by
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.mpr hT.ne
  have hm : MemLp F 2 (volume.restrict T) := (memLp_two_iff_integrable_sq_norm hF.restrict).2 h2
  exact (hm.integrable one_le_two).norm


private theorem bound_on {T0 : Set Space} (h : IsCompact T0) {φ : Space → Space} (hφ : Continuous φ) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ T0, ‖φ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

private theorem transport_on {k N : ℕ} (c : FracCellData k N) (α : ℝ) (x : FieldTuple k) {T0 T : Set Space}
    (hT0 : IsCompact T0) (hT : MeasurableSet T) (hTT : T ⊆ T0)
    (hv : AEStronglyMeasurable x.1 volume) (h6 : MemLp x.1 6 volume)
    (hGm : AEStronglyMeasurable x.2.1 volume) (hG : Integrable (fun y => entrySq (x.2.1 y)))
    (hVm : AEStronglyMeasurable c.modelVelocity volume) (hWm : AEStronglyMeasurable c.modelCurl volume)
    {CM : ℝ} (hM : ∀ y ∈ T, ‖c.modelVelocity y‖ ≤ CM ∧ ‖c.modelCurl y‖ ≤ CM) :
    AEStronglyMeasurable (fun y => transportPart c α x y) volume ∧
      IntegrableOn (fun y => ‖transportPart c α x y‖) T := by
  obtain ⟨C1, hC10, hC1⟩ := bound_on hT0 (continuous_id (X := Space))
  obtain ⟨C2, hC20, hC2⟩ := bound_on hT0 turn_cont
  have hGL : MemLp x.2.1 2 volume := memLp_grad hGm hG
  have hGi : IntegrableOn (fun y => ‖x.2.1 y‖) T :=
    (show IntegrableOn (fun y => ‖x.2.1 y‖) T0 volume from ((hGL.locallyIntegrable (by norm_num)).integrableOn_isCompact hT0).norm).mono_set hTT
  have hvi : IntegrableOn (fun y => ‖x.1 y‖) T :=
    (show IntegrableOn (fun y => ‖x.1 y‖) T0 volume from ((li_v h6).integrableOn_isCompact hT0).norm).mono_set hTT
  have hmeas : AEStronglyMeasurable (fun y => transportPart c α x y) volume := by
    have m1 : AEStronglyMeasurable (fun y => (1 - 1 / (2 * α)) • x.1 y) volume :=
      hv.const_smul (1 - 1 / (2 * α))
    have m2 : AEStronglyMeasurable (fun y => (1 / (2 * α)) • x.2.1 y y) volume :=
      (aesm_apply hGm aestronglyMeasurable_id).const_smul (1 / (2 * α))
    have m3 : AEStronglyMeasurable (fun y => c.modelRate • (x.2.1 y (axialTurn y) - axialTurn (x.1 y))) volume :=
      ((aesm_apply hGm turn_cont.aestronglyMeasurable).sub (turn_cont.comp_aestronglyMeasurable hv)).const_smul c.modelRate
    have m4 : AEStronglyMeasurable (fun y => crossVec (curlOf (x.2.1 y)) (c.modelVelocity y)) volume :=
      aesm_cross (aesm_curl hGm) hVm
    have m5 : AEStronglyMeasurable (fun y => crossVec (c.modelCurl y) (x.1 y)) volume := aesm_cross hWm hv
    have m12 := m1.add m2
    have m123 := m12.add m3
    have m1234 := m123.add m4
    exact m1234.add m5
  refine ⟨hmeas, ?_⟩
  let A : ℝ := |1 - 1 / (2 * α)| + |c.modelRate| * ‖turnCLM‖ + CM
  let Bc : ℝ := |1 / (2 * α)| * C1 + |c.modelRate| * C2 + 27 * CM
  refine Integrable.mono' ((hvi.const_mul A).add (hGi.const_mul Bc)) hmeas.norm.restrict ?_
  refine (ae_restrict_iff' hT).2 (ae_of_all _ fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hy0 := hTT hy
  have e1 : ‖x.2.1 y y‖ ≤ ‖x.2.1 y‖ * C1 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hC1 y hy0) (norm_nonneg _))
  have e2 : ‖x.2.1 y (axialTurn y)‖ ≤ ‖x.2.1 y‖ * C2 :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hC2 y hy0) (norm_nonneg _))
  have e3 : ‖axialTurn (x.1 y)‖ ≤ ‖turnCLM‖ * ‖x.1 y‖ := by
    rw [← turnCLM_apply]; exact ContinuousLinearMap.le_opNorm _ _
  have e4 : ‖crossVec (curlOf (x.2.1 y)) (c.modelVelocity y)‖ ≤ 27 * ‖x.2.1 y‖ * CM :=
    (cross_le _ _).trans (mul_le_mul (curl_le _) (hM y hy).1 (norm_nonneg _) (by positivity))
  have e5 : ‖crossVec (c.modelCurl y) (x.1 y)‖ ≤ CM * ‖x.1 y‖ :=
    (cross_le _ _).trans (mul_le_mul_of_nonneg_right (hM y hy).2 (norm_nonneg _))
  unfold transportPart driftField
  calc _ ≤ ‖(1 - 1 / (2 * α)) • x.1 y‖ + ‖(1 / (2 * α)) • x.2.1 y y‖
          + ‖c.modelRate • (x.2.1 y (axialTurn y) - axialTurn (x.1 y))‖
          + ‖crossVec (curlOf (x.2.1 y)) (c.modelVelocity y)‖ + ‖crossVec (c.modelCurl y) (x.1 y)‖ := by
        have t1 := norm_add_le ((1 - 1 / (2 * α)) • x.1 y + (1 / (2 * α)) • x.2.1 y y
          + c.modelRate • (x.2.1 y (axialTurn y) - axialTurn (x.1 y))
          + crossVec (curlOf (x.2.1 y)) (c.modelVelocity y)) (crossVec (c.modelCurl y) (x.1 y))
        have t2 := norm_add_le ((1 - 1 / (2 * α)) • x.1 y + (1 / (2 * α)) • x.2.1 y y
          + c.modelRate • (x.2.1 y (axialTurn y) - axialTurn (x.1 y))) (crossVec (curlOf (x.2.1 y)) (c.modelVelocity y))
        have t3 := norm_add_le ((1 - 1 / (2 * α)) • x.1 y + (1 / (2 * α)) • x.2.1 y y)
          (c.modelRate • (x.2.1 y (axialTurn y) - axialTurn (x.1 y)))
        have t4 := norm_add_le ((1 - 1 / (2 * α)) • x.1 y) ((1 / (2 * α)) • x.2.1 y y)
        linarith
    _ ≤ |1 - 1 / (2 * α)| * ‖x.1 y‖ + |1 / (2 * α)| * (‖x.2.1 y‖ * C1)
          + |c.modelRate| * (‖x.2.1 y‖ * C2 + ‖turnCLM‖ * ‖x.1 y‖)
          + 27 * ‖x.2.1 y‖ * CM + CM * ‖x.1 y‖ := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add e2 e3)
    _ = A * ‖x.1 y‖ + Bc * ‖x.2.1 y‖ := by ring


private theorem trace_on {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {T : Set Space} (hTf : volume T < ⊤)
    (hHm : AEStronglyMeasurable H volume)
    (hH : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    AEStronglyMeasurable (fun y => secondTrace (H y)) volume ∧
      IntegrableOn (fun y => ‖secondTrace (H y)‖) T := by
  have hm : ∀ i j : Fin 3, AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume := fun i j =>
    aesm_apply ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous.comp_aestronglyMeasurable
      hHm) aestronglyMeasurable_const
  have hi : ∀ j : Fin 3, IntegrableOn (fun y => ‖H y (unitVector j) (unitVector j)‖) T := by
    intro j
    refine integrableOn_of_two hTf (hm j j) ?_
    refine Integrable.integrableOn (hH.mono' ((hm j j).norm.pow 2) (ae_of_all _ fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have a1 : ‖H y (unitVector j) (unitVector j)‖ ^ 2 ≤ ∑ j' : Fin 3, ‖H y (unitVector j) (unitVector j')‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖H y (unitVector j) (unitVector j')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have a2 : (∑ j' : Fin 3, ‖H y (unitVector j) (unitVector j')‖ ^ 2) ≤
        ∑ i : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    exact a1.trans a2
  have hmeas : AEStronglyMeasurable (fun y => secondTrace (H y)) volume := by
    have h01 := (hm 0 0).add (hm 1 1)
    have h012 := h01.add (hm 2 2)
    refine h012.congr (ae_of_all _ fun y => ?_)
    simp [secondTrace, Fin.sum_univ_three]
  refine ⟨hmeas, ?_⟩
  have hsum : IntegrableOn (fun y => ∑ j : Fin 3, ‖H y (unitVector j) (unitVector j)‖) T volume :=
    integrable_finsetSum Finset.univ fun j _ => hi j
  refine Integrable.mono' hsum hmeas.norm.restrict (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_sum_le _ _

private theorem pressure_on {Q : Space → Space} {T0 T : Set Space} (hT0 : IsCompact T0) (hTT : T ⊆ T0)
    (hTf : volume T < ⊤) (hQ : IsGradientField Q) :
    AEStronglyMeasurable Q volume ∧ IntegrableOn (fun y => ‖Q y‖) T := by
  obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
  exact ⟨hQm, integrableOn_of_two hTf hQm ((hQ2 T0 hT0).mono_set hTT)⟩


private theorem proj_cont (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (K.proj d d' F) := by
  unfold CellBox.proj
  split_ifs with h
  · obtain ⟨cf, hcf⟩ := h.choose_spec.1
    rw [show h.choose = fun p : ℝ × ℝ => ∑ j, ∑ l, cf j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) from
      funext hcf]
    fun_prop
  · exact continuous_const

private theorem angle_meas : Measurable cylAngle := by
  unfold cylAngle
  exact Complex.measurable_arg.comp (by fun_prop)

private theorem sign_meas (a : Fin 3) : Measurable (fun y => mirrorSign y a) := by
  unfold mirrorSign
  refine Measurable.ite ?_ measurable_const measurable_const
  have hc : Continuous cylHeight := by unfold cylHeight; fun_prop
  exact (measurableSet_lt hc.measurable measurable_const).inter (MeasurableSet.const _)

private theorem unit_cont (a : Fin 3) : Continuous (fun θ => frameUnit θ a) := by
  fin_cases a
  · exact ((single_cont 0).comp Real.continuous_cos).add ((single_cont 1).comp Real.continuous_sin)
  · exact ((single_cont 0).comp Real.continuous_sin.neg).add ((single_cont 1).comp Real.continuous_cos)
  · exact continuous_const

private theorem unit_le (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ ≤ 2 := by
  fin_cases a
  · simp only [frameUnit, radialUnit]
    refine (norm_add_le _ _).trans ?_
    simp only [PiLp.norm_single, Real.norm_eq_abs]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · simp only [frameUnit, angularUnit]
    refine (norm_add_le _ _).trans ?_
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_neg]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · simp [frameUnit, axialUnit]

private theorem op_term_cont (a b : Fin 3) :
    Continuous (fun θ => (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)) := by
  have h1 : Continuous (fun θ => innerSL ℝ (frameUnit θ b)) := (innerSL ℝ).continuous.comp (unit_cont b)
  exact isBoundedBilinearMap_smulRight.continuous.comp (h1.prodMk (unit_cont a))

private theorem op_le (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) : ‖cartOpOfFrame θ M‖ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |M a b| * 4 := by
  unfold cartOpOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b _ => ?_))
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have := unit_le θ a; have := unit_le θ b
  nlinarith [norm_nonneg (frameUnit θ a), norm_nonneg (frameUnit θ b)]

private theorem vec_le (θ : ℝ) (w : Fin 3 → ℝ) : ‖cartOfFrame θ w‖ ≤ ∑ a : Fin 3, |w a| * 2 := by
  unfold cartOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (unit_le θ a) (abs_nonneg _)


private theorem rho_cont : Continuous (fun y : Space => ((cylRadius y, |cylHeight y|) : ℝ × ℝ)) := by
  unfold cylRadius cylHeight; fun_prop

private theorem rho_mem (K : CellBox) {y : Space} (hy : y ∈ K.solid) : ((cylRadius y, |cylHeight y|) : ℝ × ℝ) ∈ K.rect :=
  ⟨⟨hy.1, hy.2.1⟩, ⟨hy.2.2.1, hy.2.2.2⟩⟩

private theorem sign_abs (y : Space) (a : Fin 3) : |mirrorSign y a| = 1 := by
  unfold mirrorSign; split_ifs <;> simp

private theorem wave_meas (m : ℕ) (n : ℤ) :
    Measurable (fun y => Complex.exp ((azimuth m n * cylAngle y : ℝ) * Complex.I)) :=
  Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul angle_meas)).mul measurable_const)

private theorem mode_sum_meas (m : ℕ) (s : Finset ℤ) (F : ℤ → ℝ × ℝ → ℂ) (hF : ∀ n, Continuous (F n)) :
    Measurable (fun y => (∑ n ∈ s, F n (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth m n * cylAngle y : ℝ) * Complex.I)).re) := by
  refine Complex.measurable_re.comp ?_
  exact Finset.measurable_sum _ fun n _ => ((hF n).comp rho_cont).measurable.mul (wave_meas m n)

private theorem mode_sum_bound (K : CellBox) (m : ℕ) (s : Finset ℤ) (F : ℤ → ℝ × ℝ → ℂ) (hF : ∀ n, Continuous (F n)) :
    ∃ B, ∀ y ∈ K.solid, |(∑ n ∈ s, F n (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth m n * cylAngle y : ℝ) * Complex.I)).re| ≤ B := by
  have hc : Continuous (fun p => ∑ n ∈ s, ‖F n p‖) := continuous_finsetSum _ fun n _ => (hF n).norm
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K.rect).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B, fun y hy => ?_⟩
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB _ (rho_mem K hy))))
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]


private theorem lowGrad_props {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (G : Space → (Space →L[ℝ] Space)) :
    AEStronglyMeasurable (lowGradField c K S G) volume ∧ ∃ B, ∀ y ∈ K.solid, ‖lowGradField c K S G y‖ ≤ B := by
  have hF : ∀ (a b : Fin 3) (n : ℤ), Continuous (K.lowStrain c.order n S.degHigh G a b) := fun a b n =>
    proj_cont K _ _ _
  constructor
  · refine Measurable.aestronglyMeasurable ?_
    unfold lowGradField cartOpOfFrame
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (((sign_meas a).mul (sign_meas b)).mul (mode_sum_meas c.order S.resolved _ (fun n => hF a b n))).smul
        ((op_term_cont a b).measurable.comp angle_meas)
  · choose B hB using fun ab : Fin 3 × Fin 3 =>
      mode_sum_bound K c.order S.resolved (fun n => K.lowStrain c.order n S.degHigh G ab.1 ab.2) (fun n => hF ab.1 ab.2 n)
    refine ⟨∑ a : Fin 3, ∑ b : Fin 3, |B (a, b)| * 4, fun y hy => ?_⟩
    unfold lowGradField
    refine (op_le _ _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
    rw [abs_mul, abs_mul, sign_abs, sign_abs, one_mul, one_mul]
    exact (hB (a, b) y hy).trans (le_abs_self _)

private theorem lowVel_props {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (v : Space → Space) :
    AEStronglyMeasurable (lowVelocityField c K S v) volume ∧ ∃ B, ∀ y ∈ K.solid, ‖lowVelocityField c K S v y‖ ≤ B := by
  have hF : ∀ (a : Fin 3) (n : ℤ), Continuous (K.lowVelocity c.order n S.degHigh v a) := fun a n =>
    proj_cont K _ _ _
  constructor
  · refine Measurable.aestronglyMeasurable ?_
    unfold lowVelocityField cartOfFrame
    exact Finset.measurable_sum _ fun a _ =>
      ((sign_meas a).mul (mode_sum_meas c.order S.resolved _ (fun n => hF a n))).smul
        ((unit_cont a).measurable.comp angle_meas)
  · choose B hB using fun a : Fin 3 =>
      mode_sum_bound K c.order S.resolved (fun n => K.lowVelocity c.order n S.degHigh v a) (fun n => hF a n)
    refine ⟨∑ a : Fin 3, |B a| * 2, fun y hy => ?_⟩
    unfold lowVelocityField
    refine (vec_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
    rw [abs_mul, sign_abs, one_mul]
    exact (hB a y hy).trans (le_abs_self _)


private theorem coupling_on {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    {T0 : Set Space} (hT0 : IsCompact T0) (hTT : K.solid ⊆ T0) (hTf : volume K.solid < ⊤)
    (hTm : MeasurableSet K.solid)
    (hv : AEStronglyMeasurable x.1 volume) (h6 : MemLp x.1 6 volume)
    (hGm : AEStronglyMeasurable x.2.1 volume) (hG : Integrable (fun y => entrySq (x.2.1 y)))
    (hVm : AEStronglyMeasurable c.modelVelocity volume) (hWm : AEStronglyMeasurable c.modelCurl volume)
    {CM : ℝ} (hM : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ CM ∧ ‖c.modelCurl y‖ ≤ CM) :
    AEStronglyMeasurable (fun y => highCouplingField c K S x.1 x.2.1 y) volume ∧
      IntegrableOn (fun y => ‖highCouplingField c K S x.1 x.2.1 y‖) K.solid := by
  obtain ⟨mLG, BG, hBG⟩ := lowGrad_props c K S x.2.1
  obtain ⟨mLV, BV, hBV⟩ := lowVel_props c K S x.1
  have m1 : AEStronglyMeasurable (fun y => x.2.1 y - lowGradField c K S x.2.1 y) volume := hGm.sub mLG
  have m2 : AEStronglyMeasurable (fun y => x.1 y - lowVelocityField c K S x.1 y) volume := hv.sub mLV
  have m3 : AEStronglyMeasurable (fun y => crossVec (curlOf (x.2.1 y - lowGradField c K S x.2.1 y))
      (c.modelVelocity y)) volume := aesm_cross (aesm_curl m1) hVm
  have m4 : AEStronglyMeasurable (fun y => crossVec (c.modelCurl y) (x.1 y - lowVelocityField c K S x.1 y)) volume :=
    aesm_cross hWm m2
  have hmeas : AEStronglyMeasurable (fun y => highCouplingField c K S x.1 x.2.1 y) volume := m3.add m4
  refine ⟨hmeas, ?_⟩
  have hGL : MemLp x.2.1 2 volume := memLp_grad hGm hG
  have hGi : IntegrableOn (fun y => ‖x.2.1 y‖) K.solid :=
    (show IntegrableOn (fun y => ‖x.2.1 y‖) T0 volume from
      ((hGL.locallyIntegrable (by norm_num)).integrableOn_isCompact hT0).norm).mono_set hTT
  have hvi : IntegrableOn (fun y => ‖x.1 y‖) K.solid :=
    (show IntegrableOn (fun y => ‖x.1 y‖) T0 volume from ((li_v h6).integrableOn_isCompact hT0).norm).mono_set hTT
  have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hTf.ne
  have hci : IntegrableOn (fun _ : Space => 27 * |BG| * |CM| + |CM| * |BV|) K.solid := integrable_const _
  refine Integrable.mono' (((hGi.const_mul (27 * |CM|)).add (hvi.const_mul |CM|)).add hci) hmeas.norm.restrict ?_
  refine (ae_restrict_iff' hTm).2 (ae_of_all _ fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV := (hM y hy).1
  have hW := (hM y hy).2
  have hCM : 0 ≤ CM := (norm_nonneg _).trans hV
  have e1 : ‖x.2.1 y - lowGradField c K S x.2.1 y‖ ≤ ‖x.2.1 y‖ + |BG| :=
    by linarith [norm_sub_le (x.2.1 y) (lowGradField c K S x.2.1 y), hBG y hy, le_abs_self BG]
  have e2 : ‖x.1 y - lowVelocityField c K S x.1 y‖ ≤ ‖x.1 y‖ + |BV| :=
    by linarith [norm_sub_le (x.1 y) (lowVelocityField c K S x.1 y), hBV y hy, le_abs_self BV]
  have e3 : ‖crossVec (curlOf (x.2.1 y - lowGradField c K S x.2.1 y)) (c.modelVelocity y)‖ ≤
      27 * (‖x.2.1 y‖ + |BG|) * CM :=
    (cross_le _ _).trans (mul_le_mul ((curl_le _).trans (by linarith)) hV (norm_nonneg _) (by positivity))
  have e4 : ‖crossVec (c.modelCurl y) (x.1 y - lowVelocityField c K S x.1 y)‖ ≤ CM * (‖x.1 y‖ + |BV|) :=
    (cross_le _ _).trans (mul_le_mul hW e2 (norm_nonneg _) hCM)
  have e5 := norm_add_le (crossVec (curlOf (x.2.1 y - lowGradField c K S x.2.1 y)) (c.modelVelocity y))
    (crossVec (c.modelCurl y) (x.1 y - lowVelocityField c K S x.1 y))
  unfold highCouplingField
  rw [abs_of_nonneg hCM]
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg (x.2.1 y), norm_nonneg (x.1 y), abs_nonneg BG, abs_nonneg BV]


theorem coupling_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    Integrable (fun y => inner ℝ (highCouplingField c K S x.1 x.2.1 y) (c.row a y)) := by
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hTm : MeasurableSet K.solid := solid_meas K
  have hTf : volume K.solid < ⊤ := solid_finite hc hD
  obtain ⟨C, hC⟩ := row_bounded hc hD hR ha
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hM : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ CM ∧ ‖c.modelCurl y‖ ≤ CM := fun y hy =>
    ⟨(hCM y (hD.solid_in_region hy)).1, (hCM y (hD.solid_in_region hy)).2.1⟩
  obtain ⟨m, i⟩ := coupling_on c K S x hT0 hTT hTf hTm hx.1.measurable_velocity hx.1.velocity_six
    hx.1.measurable_gradient hx.1.gradient_two hc.model_measurable.1 hc.model_measurable.2.1 hM
  exact inner_row_integrable hTm (hc.base.row_two a).aestronglyMeasurable hC (hD.rows_in_cell a ha) m i

theorem pairings_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    Integrable (fun y => inner ℝ (transportPart c α x y) (c.row a y)) ∧
      Integrable (fun y => inner ℝ (secondTrace (x.2.2.1 y)) (c.row a y)) ∧
      Integrable (fun y => inner ℝ (x.2.2.2.2 y) (c.row a y)) ∧
      Integrable (fun y => inner ℝ (highCouplingField c K S x.1 x.2.1 y) (c.row a y)) := by
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hTm : MeasurableSet K.solid := solid_meas K
  have hTf : volume K.solid < ⊤ := solid_finite hc hD
  obtain ⟨C, hC⟩ := row_bounded hc hD hR ha
  have hrow : AEStronglyMeasurable (c.row a) volume := (hc.base.row_two a).aestronglyMeasurable
  have hsupp : ∀ y ∉ K.solid, c.row a y = 0 := hD.rows_in_cell a ha
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hM : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ CM ∧ ‖c.modelCurl y‖ ≤ CM := fun y hy =>
    ⟨(hCM y (hD.solid_in_region hy)).1, (hCM y (hD.solid_in_region hy)).2.1⟩
  have hS := hx.1
  obtain ⟨m1, i1⟩ := transport_on c α x hT0 hTm hTT hS.measurable_velocity hS.velocity_six hS.measurable_gradient
    hS.gradient_two hc.model_measurable.1 hc.model_measurable.2.1 hM
  obtain ⟨m2, i2⟩ := trace_on hTf hS.measurable_second hS.second_two
  obtain ⟨m3, i3⟩ := pressure_on hT0 hTT hTf hx.2.1
  exact ⟨inner_row_integrable hTm hrow hC hsupp m1 i1, inner_row_integrable hTm hrow hC hsupp m2 i2,
    inner_row_integrable hTm hrow hC hsupp m3 i3, coupling_integrable hα1 hα2 hc hD hR hL hx ha⟩

theorem curlOf_sub (M M' : Space →L[ℝ] Space) : curlOf (M - M') = curlOf M - curlOf M' := by
  simp only [curlOf, entry, _root_.sub_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib,
    sub_smul]

theorem crossVec_sub_left (u u' w : Space) : crossVec (u - u') w = crossVec u w - crossVec u' w := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

theorem crossVec_sub_right (u w w' : Space) : crossVec u (w - w') = crossVec u w - crossVec u w' := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

def lowTransport {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (α : ℝ) (x : FieldTuple k)
    (y : Space) : Space :=
  driftField α c.modelRate x.1 x.2.1 y + crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)
    + crossVec (c.modelCurl y) (lowVelocityField c K S x.1 y)

theorem transport_sub_coupling_apply {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (α : ℝ)
    (x : FieldTuple k) (y : Space) :
    transportPart c α x y - highCouplingField c K S x.1 x.2.1 y = lowTransport c K S α x y := by
  simp only [transportPart, highCouplingField, lowTransport, curlOf_sub, crossVec_sub_left, crossVec_sub_right]
  abel

theorem transport_sub_coupling {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    Integrable (fun y => inner ℝ (lowTransport c K S α x y) (c.row a y)) ∧
      l2Pair (transportPart c α x) (c.row a) - l2Pair (highCouplingField c K S x.1 x.2.1) (c.row a) =
        l2Pair (lowTransport c K S α x) (c.row a) := by
  obtain ⟨hT, -, -, hH⟩ := pairings_integrable hα1 hα2 hc hD hR hL hx ha
  have e : (fun y => inner ℝ (lowTransport c K S α x y) (c.row a y)) =
      fun y => inner ℝ (transportPart c α x y) (c.row a y) - inner ℝ (highCouplingField c K S x.1 x.2.1 y) (c.row a y) := by
    funext y
    rw [← inner_sub_left, transport_sub_coupling_apply]
  refine ⟨e ▸ hT.sub hH, ?_⟩
  unfold l2Pair
  rw [← integral_sub hT hH, e]

theorem lowTransport_on {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) :
    AEStronglyMeasurable (lowTransport c K S α x) volume ∧
      IntegrableOn (fun y => ‖lowTransport c K S α x y‖) K.solid := by
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hTm : MeasurableSet K.solid := solid_meas K
  have hTf : volume K.solid < ⊤ := solid_finite hc hD
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hM : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ CM ∧ ‖c.modelCurl y‖ ≤ CM := fun y hy =>
    ⟨(hCM y (hD.solid_in_region hy)).1, (hCM y (hD.solid_in_region hy)).2.1⟩
  have hS := hx.1
  obtain ⟨m1, i1⟩ := transport_on c α x hT0 hTm hTT hS.measurable_velocity hS.velocity_six hS.measurable_gradient
    hS.gradient_two hc.model_measurable.1 hc.model_measurable.2.1 hM
  obtain ⟨m2, i2⟩ := coupling_on c K S x hT0 hTT hTf hTm hS.measurable_velocity hS.velocity_six
    hS.measurable_gradient hS.gradient_two hc.model_measurable.1 hc.model_measurable.2.1 hM
  have e : lowTransport c K S α x = fun y => transportPart c α x y - highCouplingField c K S x.1 x.2.1 y :=
    funext fun y => (transport_sub_coupling_apply c K S α x y).symm
  rw [e]
  refine ⟨m1.sub m2, Integrable.mono' (i1.add i2) (m1.sub m2).norm.restrict (ae_of_all _ fun y => ?_)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_sub_le _ _

theorem secondTrace_on {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) :
    AEStronglyMeasurable (fun y => secondTrace (x.2.2.1 y)) volume ∧
      IntegrableOn (fun y => ‖secondTrace (x.2.2.1 y)‖) K.solid :=
  trace_on (solid_finite hc hD) hx.1.measurable_second hx.1.second_two

end LayoutRowParts

end FracInternal

end Breakdown

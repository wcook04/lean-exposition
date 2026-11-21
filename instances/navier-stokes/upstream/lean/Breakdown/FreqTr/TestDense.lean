import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.TestDense

theorem fieldOp_eq_zero_or_realized (A : Space → Space) (F : Space → CSpace →L[ℝ] CSpace) :
    fieldOp A F = 0 ∨ IsRealizedBy (fieldOp A F) A F := by
  unfold fieldOp
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem ae_comp_neg {f f' : Space → CSpace} (h : f =ᵐ[volume] f') :
    (fun ξ => f (-ξ)) =ᵐ[volume] fun ξ => f' (-ξ) :=
  (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving.quasiMeasurePreserving.ae_eq_comp h

theorem mem_sig_of_ae (x : X) (g : Space → ℝ) (hg : ∀ ξ, g (-ξ) = g ξ) (y : L2C)
    (hy : (y : Space → CSpace) =ᵐ[volume] fun ξ => g ξ • (x : L2C) ξ) : y ∈ Sig := by
  have hx := x.2
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hx ⊢
  obtain ⟨e1, e2⟩ := hx
  refine ⟨?_, ?_⟩
  · rcases fieldOp_eq_zero_or_realized (fun ξ => -ξ) (fun _ => conjVec) with h0 | hR
    · have hr : reflConj = 0 := h0
      rw [hr] at e1 ⊢
      have hx0 : (x : L2C) = 0 := by simpa using e1.symm
      have hy0 : y = 0 := by
        apply Lp.ext
        filter_upwards [hy, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ h1 h2
        rw [h1, h2, hx0]
        simp
      simp [hy0]
    · apply Lp.ext
      filter_upwards [hR y, ae_comp_neg hy, hR (x : L2C), hy] with ξ h1 h2 h3 h4
      have h2' : y (-ξ) = g (-ξ) • (x : L2C) (-ξ) := h2
      have h3' : (reflConj (x : L2C)) ξ = conjVec ((x : L2C) (-ξ)) := h3
      rw [e1] at h3'
      have h1' : (reflConj y) ξ = conjVec (y (-ξ)) := h1
      rw [h1', h2', map_smul, hg, ← h3', h4]
  · rcases fieldOp_eq_zero_or_realized id longitudinal with h0 | hR
    · rw [h0]
      rfl
    · apply Lp.ext
      filter_upwards [hR y, hR (x : L2C), hy, Lp.coeFn_zero CSpace 2 (volume : Measure Space)]
        with ξ h1 h2 h3 h4
      rw [e2, h4] at h2
      rw [h1, h4, id, h3, map_smul]
      simp only [id] at h2
      rw [← h2]
      simp

theorem memLp_smul_of_bounded (x : L2C) (g : Space → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ ξ, |g ξ| ≤ C) : MemLp (fun ξ => g ξ • (x : Space → CSpace) ξ) 2 volume :=
  (Lp.memLp x).of_le_mul (c := C) (hg.aestronglyMeasurable.smul (Lp.aestronglyMeasurable x))
    (Filter.Eventually.of_forall fun ξ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

theorem norm_sub_toLp (a : L2C) {f : Space → CSpace} (hf : MemLp f 2 volume) :
    ‖a - hf.toLp f‖ = (eLpNorm (fun ξ => a ξ - f ξ) 2 volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub a (hf.toLp f), hf.coeFn_toLp] with ξ h1 h2
  rw [h1, Pi.sub_apply, h2]

theorem norm_toLp_sub (a : L2C) {f : Space → CSpace} (hf : MemLp f 2 volume) :
    ‖hf.toLp f - a‖ = (eLpNorm (fun ξ => f ξ - a ξ) 2 volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) a, hf.coeFn_toLp] with ξ h1 h2
  rw [h1, Pi.sub_apply, h2]

theorem continuous_sspFactor : Continuous sspFactor :=
  show Continuous fun ξ : Space => 4 * π ^ 2 * ‖ξ‖ ^ 2 from continuous_const.mul (continuous_norm.pow 2)

theorem testDenseGraph_of (h2 : NiceDense) (h3 : NiceApprox) : TestDenseGraph := by
  intro χ ψ hχψ ε hε
  obtain ⟨m, hm, hm1, hm2⟩ := h2 χ ψ hχψ (ε / 2) (half_pos hε)
  obtain ⟨φ, hφ, hφ1, hφ2⟩ := h3 m hm (ε / 2) (half_pos hε)
  have hmc : Continuous m := hm.1.continuous
  have hmL : MemLp m 2 volume := hmc.memLp_of_hasCompactSupport hm.2.1
  have hlc : Continuous (fun ξ => sspFactor ξ • m ξ) := continuous_sspFactor.smul hmc
  have hms : HasCompactSupport m := hm.2.1
  have hls : HasCompactSupport (fun ξ => sspFactor ξ • m ξ) :=
    HasCompactSupport.smul_left (f := sspFactor) hms
  have hlL : MemLp (fun ξ => sspFactor ξ • m ξ) 2 volume := hlc.memLp_of_hasCompactSupport hls
  refine ⟨φ, hφ, ?_, ?_⟩
  · change ‖(embedX φ : L2C) - (χ : L2C)‖ < ε
    calc ‖(embedX φ : L2C) - (χ : L2C)‖
        ≤ ‖(embedX φ : L2C) - hmL.toLp m‖ + ‖hmL.toLp m - (χ : L2C)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [norm_sub_toLp, norm_toLp_sub]
          exact add_lt_add hφ1 hm1
      _ = ε := add_halves ε
  · change ‖(embedX (negSsp φ) : L2C) - (ψ : L2C)‖ < ε
    calc ‖(embedX (negSsp φ) : L2C) - (ψ : L2C)‖
        ≤ ‖(embedX (negSsp φ) : L2C) - hlL.toLp _‖ + ‖hlL.toLp _ - (ψ : L2C)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [norm_sub_toLp, norm_toLp_sub]
          exact add_lt_add hφ2 hm2
      _ = ε := add_halves ε

theorem closedBall_indicator_even (R : ℝ) (f : Space → ℝ) (hf : ∀ ξ, f (-ξ) = f ξ) (ξ : Space) :
    (Metric.closedBall (0 : Space) R).indicator f (-ξ) =
      (Metric.closedBall (0 : Space) R).indicator f ξ := by
  simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right, norm_neg, hf]

theorem sspFactor_neg (ξ : Space) : sspFactor (-ξ) = sspFactor ξ := by
  simp only [sspFactor, norm_neg]

theorem testDense_of (hG : TestDenseGraph) : TestDense := by
  rw [TestDense, Metric.dense_iff]
  intro x ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨G, hGc, hGn, -, -⟩ := (Lp.memLp (x : L2C)).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.2 hε4).ne'
  obtain ⟨R, hR⟩ := hGc.isCompact.isBounded.subset_closedBall (0 : Space)
  have hGz : ∀ ξ, ξ ∉ Metric.closedBall (0 : Space) R → G ξ = 0 :=
    fun ξ hξ => image_eq_zero_of_notMem_tsupport (fun h => hξ (hR h))
  let g1 : Space → ℝ := (Metric.closedBall (0 : Space) R).indicator (fun _ => 1)
  let g2 : Space → ℝ := (Metric.closedBall (0 : Space) R).indicator sspFactor
  have hm1 : Measurable g1 :=
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  have hm2 : Measurable g2 :=
    continuous_sspFactor.measurable.indicator Metric.isClosed_closedBall.measurableSet
  have hb1 : ∀ ξ, |g1 ξ| ≤ 1 := by
    intro ξ
    by_cases h : ξ ∈ Metric.closedBall (0 : Space) R <;> simp [g1, h]
  have hb2 : ∀ ξ, |g2 ξ| ≤ 4 * π ^ 2 * R ^ 2 := by
    intro ξ
    by_cases h : ξ ∈ Metric.closedBall (0 : Space) R
    · have hn : ‖ξ‖ ≤ R := by simpa using h
      have hl : 0 ≤ sspFactor ξ := by unfold sspFactor; positivity
      rw [show g2 ξ = sspFactor ξ from Set.indicator_of_mem h _, abs_of_nonneg hl]
      unfold sspFactor
      have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith [pi_pos]
    · rw [show g2 ξ = 0 from Set.indicator_of_notMem h _, abs_zero]
      positivity
  have he1 : ∀ ξ, g1 (-ξ) = g1 ξ := closedBall_indicator_even R _ (fun _ => rfl)
  have he2 : ∀ ξ, g2 (-ξ) = g2 ξ := closedBall_indicator_even R _ sspFactor_neg
  have hL1 := memLp_smul_of_bounded (x : L2C) g1 hm1 1 hb1
  have hL2 := memLp_smul_of_bounded (x : L2C) g2 hm2 _ hb2
  let χ : X := ⟨hL1.toLp _, mem_sig_of_ae x g1 he1 _ hL1.coeFn_toLp⟩
  let ψ : X := ⟨hL2.toLp _, mem_sig_of_ae x g2 he2 _ hL2.coeFn_toLp⟩
  have hssp : IsSspOf χ ψ := by
    filter_upwards [hL1.coeFn_toLp, hL2.coeFn_toLp] with ξ h1 h2
    change (hL2.toLp _ : Space → CSpace) ξ = sspFactor ξ • (hL1.toLp _ : Space → CSpace) ξ
    rw [h1, h2]
    by_cases h : ξ ∈ Metric.closedBall (0 : Space) R <;> simp [g1, g2, h]
  obtain ⟨φ, hφ, hφ1, -⟩ := hG χ ψ hssp (ε / 2) (half_pos hε)
  have hχx : ‖χ - x‖ ≤ ε / 4 := by
    change ‖hL1.toLp _ - (x : L2C)‖ ≤ ε / 4
    rw [norm_toLp_sub]
    apply ENNReal.toReal_le_of_le_ofReal hε4.le
    refine le_trans (eLpNorm_mono fun ξ => ?_) hGn
    by_cases h : ξ ∈ Metric.closedBall (0 : Space) R
    · simp [g1, h]
    · simp [g1, h, hGz ξ h]
  refine ⟨embedX φ, ?_, Submodule.subset_span ⟨φ, hφ, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖embedX φ - x‖ ≤ ‖embedX φ - χ‖ + ‖χ - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 4 := add_lt_add_of_lt_of_le hφ1 hχx
    _ < ε := by linarith

end Internal.TestDense

open Internal.TestDense in
theorem testDenseGraphDense (_h1 : FieldOpRealized) (h2 : NiceDense) (h3 : NiceApprox) :
    TestDenseGraph ∧ TestDense :=
  ⟨testDenseGraph_of h2 h3, testDense_of (testDenseGraph_of h2 h3)⟩

end Breakdown.Freq

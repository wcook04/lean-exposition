import Breakdown.FracCell.StClauses

open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ModelRegular

open CellCert SteadyCert

private theorem coord_le (u : Space) (i : Fin 3) : |u i| ≤ ‖u‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le u i

private theorem expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

private theorem apply_norm_le (M : Space →L[ℝ] Space) (u : Space) :
    ‖M u‖ ≤ ‖u‖ * ∑ j : Fin 3, ‖M (unitVector j)‖ := by
  conv_lhs => rw [expand u]
  rw [map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (coord_le u j) (norm_nonneg _)

private theorem single_norm (i : Fin 3) (x : ℝ) : ‖(EuclideanSpace.single i x : Space)‖ = |x| := by
  simp

private theorem cross_norm_le (a b : Space) : ‖crossVec a b‖ ≤ 6 * (‖a‖ * ‖b‖) := by
  have h0 := coord_le a 0
  have h1 := coord_le a 1
  have h2 := coord_le a 2
  have k0 := coord_le b 0
  have k1 := coord_le b 1
  have k2 := coord_le b 2
  have t : ∀ i j k l : Fin 3, |a i * b j - a k * b l| ≤ 2 * (‖a‖ * ‖b‖) := by
    intro i j k l
    have := coord_le a i
    have := coord_le a k
    have := coord_le b j
    have := coord_le b l
    calc |a i * b j - a k * b l| ≤ |a i| * |b j| + |a k| * |b l| := by
          rw [← abs_mul, ← abs_mul]
          have := norm_sub_le (a i * b j) (a k * b l)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := by gcongr
      _ = 2 * (‖a‖ * ‖b‖) := by ring
  unfold crossVec
  refine norm_add₃_le.trans ?_
  rw [single_norm, single_norm, single_norm]
  linarith [t 1 2 2 1, t 2 0 0 2, t 0 1 1 0]

private theorem sign_abs_le (i j l : Fin 3) : |permSign i j l| ≤ 1 := by
  unfold permSign
  split_ifs <;> simp

private theorem curl_norm_le (M : Space →L[ℝ] Space) : ‖curlOf M‖ ≤ 9 * ∑ j : Fin 3, ‖M (unitVector j)‖ := by
  have hc : ∀ i : Fin 3, |∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j| ≤ 3 * ∑ j : Fin 3, ‖M (unitVector j)‖ := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ l : Fin 3, |permSign i j l * entry M l j| ≤ ‖M (unitVector j)‖ := by
      intro l
      rw [abs_mul]
      have := sign_abs_le i j l
      have := coord_le (M (unitVector j)) l
      unfold entry
      calc |permSign i j l| * |M (unitVector j) l| ≤ 1 * ‖M (unitVector j)‖ := by gcongr
        _ = _ := one_mul _
    calc ∑ l : Fin 3, |permSign i j l * entry M l j| ≤ ∑ _l : Fin 3, ‖M (unitVector j)‖ := Finset.sum_le_sum fun l _ => this l
      _ = 3 * ‖M (unitVector j)‖ := by simp
  unfold curlOf
  refine (norm_sum_le _ _).trans ?_
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := by intro i; simp [unitVector]
  calc ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j) • unitVector i‖
      ≤ ∑ _i : Fin 3, 3 * ∑ j : Fin 3, ‖M (unitVector j)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
        exact hc i
    _ = 9 * ∑ j : Fin 3, ‖M (unitVector j)‖ := by simp; ring

private theorem turn_norm_le (y : Space) : ‖axialTurn y‖ ≤ 2 * ‖y‖ := by
  unfold axialTurn
  refine (norm_add_le _ _).trans ?_
  rw [single_norm, single_norm, abs_neg]
  linarith [coord_le y 0, coord_le y 1]

private theorem trace_norm_le (H : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondTrace H‖ ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ := norm_sum_le _ _

private theorem single_eq (i : Fin 3) (x : ℝ) : (EuclideanSpace.single i x : Space) = x • unitVector i := by
  ext j
  simp [unitVector]

private theorem cross_continuous : Continuous fun q : Space × Space => crossVec q.1 q.2 := by
  simp only [crossVec, single_eq]
  fun_prop

private theorem curl_continuous : Continuous fun M : Space →L[ℝ] Space => curlOf M := by
  unfold curlOf entry
  fun_prop

private theorem turn_continuous : Continuous axialTurn := by
  have : axialTurn = fun y : Space => (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
    funext y
    simp only [axialTurn, single_eq]
  rw [this]
  fun_prop


private theorem trace_continuous : Continuous fun H : Space →L[ℝ] Space →L[ℝ] Space => secondTrace H := by
  unfold secondTrace
  fun_prop

private theorem apply_meas {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure Space}
    {f : Space → (Space →L[ℝ] F)} {g : Space → Space}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun y => f y (g y)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hf hg

private theorem cross_meas {μ : Measure Space} {f g : Space → Space}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun y => crossVec (f y) (g y)) μ :=
  cross_continuous.comp_aestronglyMeasurable₂ hf hg

private theorem grad_col_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (j : Fin 3) :
    MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    apply_meas hs.measurable_gradient aestronglyMeasurable_const
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hs.gradient_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i : Fin 3 => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

private theorem second_col_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (j : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume :=
    apply_meas (apply_meas hs.measurable_second aestronglyMeasurable_const) aestronglyMeasurable_const
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hs.second_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖H y (unitVector j) (unitVector j)‖ ^ 2
      ≤ ∑ l : Fin 3, ‖H y (unitVector j) (unitVector l)‖ ^ 2 :=
        Finset.single_le_sum (f := fun l : Fin 3 => ‖H y (unitVector j) (unitVector l)‖ ^ 2)
          (fun l _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, ‖H y (unitVector i) (unitVector l)‖ ^ 2 :=
        Finset.single_le_sum (f := fun i : Fin 3 => ∑ l : Fin 3, ‖H y (unitVector i) (unitVector l)‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun l _ => by positivity) (Finset.mem_univ j)

private theorem field_local {α : ℝ} {k N : ℕ} (c : FracCellData k N) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (κ : Fin k → ℝ)
    (hact : ∀ i, MemLp (c.modelActuator i) 2 volume)
    (hmV : AEStronglyMeasurable c.modelVelocity volume) (hmC : AEStronglyMeasurable c.modelCurl volume)
    {Cm : ℝ} (hb : ∀ y, ‖c.modelVelocity y‖ ≤ Cm ∧ ‖c.modelCurl y‖ ≤ Cm) :
    AEStronglyMeasurable (c.modelFieldOf α v G H κ) volume ∧
      IsLocalSquareIntegrable (fun y => ‖c.modelFieldOf α v G H κ y‖ ^ 2) := by
  have hv := hs.measurable_velocity
  have hG := hs.measurable_gradient
  have hH := hs.measurable_second
  have hGG : AEStronglyMeasurable (fun y => G y y) volume := apply_meas hG aestronglyMeasurable_id
  have hGT : AEStronglyMeasurable (fun y => G y (axialTurn y)) volume :=
    apply_meas hG turn_continuous.aestronglyMeasurable
  have hTv : AEStronglyMeasurable (fun y => axialTurn (v y)) volume := turn_continuous.comp_aestronglyMeasurable hv
  have hTr : AEStronglyMeasurable (fun y => secondTrace (H y)) volume := trace_continuous.comp_aestronglyMeasurable hH
  have hX1 : AEStronglyMeasurable (fun y => crossVec (curlOf (G y)) (c.modelVelocity y)) volume :=
    cross_meas (curl_continuous.comp_aestronglyMeasurable hG) hmV
  have hX2 : AEStronglyMeasurable (fun y => crossVec (c.modelCurl y) (v y)) volume := cross_meas hmC hv
  have hA : MemLp (fun y => ∑ i, κ i • c.modelActuator i y) 2 volume :=
    memLp_finsetSum _ fun i _ => (hact i).const_smul (κ i)
  have hgG : MemLp (fun y => ∑ j : Fin 3, ‖G y (unitVector j)‖) 2 volume :=
    memLp_finsetSum _ fun j _ => (grad_col_memLp hs j).norm
  have hgH : MemLp (fun y => ∑ j : Fin 3, ‖H y (unitVector j) (unitVector j)‖) 2 volume :=
    memLp_finsetSum _ fun j _ => (second_col_memLp hs j).norm
  have hmeas : AEStronglyMeasurable (c.modelFieldOf α v G H κ) volume := by
    have e1 : AEStronglyMeasurable (fun y => (1 - 1 / (2 * α)) • v y) volume := hv.const_smul (1 - 1 / (2 * α))
    have e2 : AEStronglyMeasurable (fun y => (1 / (2 * α)) • G y y) volume := hGG.const_smul (1 / (2 * α))
    have e3 : AEStronglyMeasurable (fun y => c.modelRate • (G y (axialTurn y) - axialTurn (v y))) volume :=
      (hGT.sub hTv).const_smul c.modelRate
    have e4 : AEStronglyMeasurable (fun y => c.splitVisc • secondTrace (H y)) volume := hTr.const_smul c.splitVisc
    have hD : AEStronglyMeasurable (fun y => driftField α c.modelRate v G y) volume := (e1.add e2).add e3
    exact (((hD.sub e4).add hX1).add hX2).add hA.1
  refine ⟨hmeas, fun K hK => ?_⟩
  have : IsFiniteMeasure (volume.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hKm := hK.measurableSet
  have hv2 : MemLp v 2 (volume.restrict K) := (hs.velocity_six.restrict K).mono_exponent (by norm_num)
  have hgGK := hgG.restrict K
  have hgHK := hgH.restrict K
  have gnn : ∀ y, ‖∑ j : Fin 3, ‖G y (unitVector j)‖‖ = ∑ j : Fin 3, ‖G y (unitVector j)‖ := fun y =>
    by rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
  have hnn : ∀ y, ‖∑ j : Fin 3, ‖H y (unitVector j) (unitVector j)‖‖ = ∑ j : Fin 3, ‖H y (unitVector j) (unitVector j)‖ :=
    fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
  have gpos : ∀ y, 0 ≤ ∑ j : Fin 3, ‖G y (unitVector j)‖ := fun y => Finset.sum_nonneg fun j _ => norm_nonneg _
  have T2 : MemLp (fun y => G y y) 2 (volume.restrict K) := by
    refine hgGK.of_le_mul (c := R) hGG.restrict ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y hy => ?_))
    rw [gnn]
    exact (apply_norm_le _ _).trans (mul_le_mul_of_nonneg_right (hR y hy) (gpos y))
  have T3 : MemLp (fun y => G y (axialTurn y)) 2 (volume.restrict K) := by
    refine hgGK.of_le_mul (c := 2 * R) hGT.restrict ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y hy => ?_))
    rw [gnn]
    refine (apply_norm_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (gpos y))
    exact (turn_norm_le y).trans (by linarith [hR y hy])
  have T3' : MemLp (fun y => axialTurn (v y)) 2 (volume.restrict K) :=
    hv2.of_le_mul (c := 2) hTv.restrict (Filter.Eventually.of_forall fun y => turn_norm_le _)
  have T4 : MemLp (fun y => secondTrace (H y)) 2 (volume.restrict K) :=
    hgHK.of_le_mul (c := 1) hTr.restrict (Filter.Eventually.of_forall fun y => by
      rw [hnn, one_mul]; exact trace_norm_le _)
  have T5 : MemLp (fun y => crossVec (curlOf (G y)) (c.modelVelocity y)) 2 (volume.restrict K) := by
    refine hgGK.of_le_mul (c := 54 * Cm) hX1.restrict (Filter.Eventually.of_forall fun y => ?_)
    rw [gnn]
    have h1 := cross_norm_le (curlOf (G y)) (c.modelVelocity y)
    have h2 := curl_norm_le (G y)
    have h3 := (hb y).1
    have h4 := norm_nonneg (curlOf (G y))
    have h5 := norm_nonneg (c.modelVelocity y)
    have h6 := gpos y
    have h7 : ‖curlOf (G y)‖ * ‖c.modelVelocity y‖ ≤ (9 * ∑ j : Fin 3, ‖G y (unitVector j)‖) * Cm :=
      mul_le_mul h2 h3 h5 (by linarith [h6])
    calc ‖crossVec (curlOf (G y)) (c.modelVelocity y)‖ ≤ 6 * (9 * (∑ j : Fin 3, ‖G y (unitVector j)‖) * Cm) :=
          h1.trans (by linarith)
      _ = 54 * Cm * ∑ j : Fin 3, ‖G y (unitVector j)‖ := by ring
  have T6 : MemLp (fun y => crossVec (c.modelCurl y) (v y)) 2 (volume.restrict K) := by
    refine hv2.of_le_mul (c := 6 * Cm) hX2.restrict (Filter.Eventually.of_forall fun y => ?_)
    have h1 := cross_norm_le (c.modelCurl y) (v y)
    have h3 := (hb y).2
    have h5 := norm_nonneg (v y)
    have h7 := mul_le_mul_of_nonneg_right h3 h5
    calc ‖crossVec (c.modelCurl y) (v y)‖ ≤ 6 * (Cm * ‖v y‖) := h1.trans (by linarith)
      _ = 6 * Cm * ‖v y‖ := by ring
  have hF : MemLp (c.modelFieldOf α v G H κ) 2 (volume.restrict K) := by
    have e1 : MemLp (fun y => (1 - 1 / (2 * α)) • v y) 2 (volume.restrict K) := hv2.const_smul (1 - 1 / (2 * α))
    have e2 : MemLp (fun y => (1 / (2 * α)) • G y y) 2 (volume.restrict K) := T2.const_smul (1 / (2 * α))
    have e3 : MemLp (fun y => c.modelRate • (G y (axialTurn y) - axialTurn (v y))) 2 (volume.restrict K) :=
      (T3.sub T3').const_smul c.modelRate
    have e4 : MemLp (fun y => c.splitVisc • secondTrace (H y)) 2 (volume.restrict K) := T4.const_smul c.splitVisc
    have hD : MemLp (fun y => driftField α c.modelRate v G y) 2 (volume.restrict K) := (e1.add e2).add e3
    exact (((hD.sub e4).add T5).add T6).add (hA.restrict K)
  exact (memLp_two_iff_integrable_sq_norm hF.1).1 hF


end ModelRegular

end FracInternal

namespace CellCert

open SteadyCert FracInternal.ModelRegular

private theorem model_bounded_all {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∃ C : ℝ, ∀ y, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.model_bounded
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ c.cellRegion
  · exact ⟨((hC y hy).1).trans (le_max_left _ _), ((hC y hy).2.1).trans (le_max_left _ _)⟩
  · obtain ⟨h1, h2⟩ := hc.model_in_cells y hy
    rw [h1, h2, norm_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem modelRegular_of (h1 : ChosenAgreeStatement) : ModelRegularStatement := by
  intro α _ _ k N c hc p _ v G H hs κ
  have hs' : IsSecondOrderField c.order v G H := hs
  obtain ⟨hGa, hHa⟩ := h1 c.order v G H hs'
  obtain ⟨Cm, hb⟩ := model_bounded_all hc
  obtain ⟨hm, hl⟩ := field_local (α := α) c hs' κ (fun i => (hc.modelActuator_data i).1)
    hc.model_measurable.1 hc.model_measurable.2.1 hb
  have he : c.modelFieldOf α v G H κ =ᵐ[volume] (c.toCertData α).modelField p v κ := by
    filter_upwards [hGa, hHa] with y hy1 hy2
    show _ = c.modelFieldOf α v (FracCellData.chosenGrad c.order v) (FracCellData.chosenSecond c.order v) κ y
    unfold FracCellData.modelFieldOf driftField
    rw [hy1, hy2]
  refine ⟨hm.congr he, fun K hK => (hl K hK).congr_fun_ae ?_⟩
  filter_upwards [ae_restrict_of_ae he] with y hy
  rw [hy]

end CellCert

end Breakdown

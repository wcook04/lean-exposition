import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

private theorem gapSup_window_le :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) ≤
      (volume : Measure (ℝ × Space)) := by
  calc (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
        = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod ((volume : Measure Space).restrict Set.univ) := by
          rw [Measure.restrict_univ]
    _ = ((volume : Measure ℝ).prod (volume : Measure Space)).restrict
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := Measure.prod_restrict _ _
    _ ≤ (volume : Measure ℝ).prod (volume : Measure Space) := Measure.restrict_le_self
    _ = volume := (Measure.volume_eq_prod ℝ Space).symm

private theorem gapSup_period_eq_window {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) volume) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  unfold periodLIntegral
  rw [lintegral_prod _ (hf.mono_measure gapSup_window_le)]

private theorem gapSup_trace_continuous :
    Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  fun_prop

private theorem gapSup_columnSum_continuous :
    Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  fun_prop

private theorem gapSup_columnSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem gapSup_energy_finite {Γ : Set Symmetry} {P w₀ : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hw : 0 < w₀) (hP : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) < ⊤ := by
  have ha : AEMeasurable
      (fun z : ℝ × Space => ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2)) volume :=
    ((gapSup_trace_continuous.comp_aestronglyMeasurable
      hP.measurable_secondDeriv).aemeasurable.norm.pow_const 2).ennreal_ofReal
  have hb : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) volume :=
    (gapSup_columnSum_continuous.comp_aestronglyMeasurable
      hP.measurable_gradient).aemeasurable.ennreal_ofReal
  have hsplit : ∀ z : ℝ × Space,
      ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2)) =
        ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) +
          ENNReal.ofReal w₀ * ENNReal.ofReal (matSq (G z.1 z.2)) := by
    intro z
    rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw.le (gapSup_columnSum_nonneg _)),
      ENNReal.ofReal_mul hw.le]
  have hsum : AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2))) volume :=
    (ha.add (hb.const_mul _)).congr (ae_of_all _ fun z => (hsplit z).symm)
  rw [gapSup_period_eq_window (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y))
    hsum]
  simp_rw [hsplit]
  rw [lintegral_add_left' (ha.mono_measure gapSup_window_le),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← gapSup_period_eq_window (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) ha,
    ← gapSup_period_eq_window (f := fun σ y => matSq (G σ y)) hb]
  exact ENNReal.add_lt_top.2 ⟨hP.sumSecondPartials_finite,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.gradient_finite⟩

theorem gapSupTerm_of (h0 : MatrixFactsHolds) (h3 : EnergyBoundsHolds) : GapSupTermHolds := by
  intro Γ P w₀ s v G H g δ hw hs hP hδ
  have hpt : ∀ σ y, ‖G σ y (δ σ y)‖ ^ 2 ≤ s ^ 2 * matSq (G σ y) := by
    intro σ y
    have h1 : ‖G σ y (δ σ y)‖ ≤ ‖G σ y‖ * s :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hδ σ y) (norm_nonneg _))
    have h2 : ‖G σ y‖ ^ 2 ≤ matSq (G σ y) := h0.1 (G σ y)
    calc ‖G σ y (δ σ y)‖ ^ 2 ≤ (‖G σ y‖ * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = s ^ 2 * ‖G σ y‖ ^ 2 := by ring
      _ ≤ s ^ 2 * matSq (G σ y) := mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
  have hmono : periodLIntegral (fun σ y => ‖G σ y (δ σ y)‖ ^ 2) ≤
      ENNReal.ofReal (s ^ 2) * periodLIntegral (fun σ y => matSq (G σ y)) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg s)]
    exact ENNReal.ofReal_le_ofReal (hpt σ y)
  have hE : w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal ≤
      weightedEnergy (fun _ => w₀) G H :=
    h3.2.2 w₀ G H hw (gapSup_energy_finite hw hP)
  refine hmono.trans ?_
  rw [← ENNReal.ofReal_toReal hP.gradient_finite.ne, ← ENNReal.ofReal_mul (sq_nonneg s)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : (s / Real.sqrt w₀) ^ 2 = s ^ 2 / w₀ := by rw [div_pow, Real.sq_sqrt hw.le]
  have hw0 : w₀ ≠ 0 := hw.ne'
  rw [hsq]
  calc s ^ 2 * (periodLIntegral (fun σ y => matSq (G σ y))).toReal
      = s ^ 2 / w₀ * (w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal) := by
        field_simp
    _ ≤ s ^ 2 / w₀ * weightedEnergy (fun _ => w₀) G H :=
        mul_le_mul_of_nonneg_left hE (div_nonneg (sq_nonneg s) hw.le)

end CertReduction

end Breakdown

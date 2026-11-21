import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

private theorem traceSecond_continuous : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

private theorem columnSquares_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem ofReal_integral_le_lintegral {f : Space → ℝ} (hf : ∀ y, 0 ≤ f y) :
    ENNReal.ofReal (∫ y, f y) ≤ ∫⁻ y, ENNReal.ofReal (f y) := by
  by_cases hi : Integrable f
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

private theorem ofReal_sliceEnergy_le (a b : Space → ℝ) {w₀ : ℝ} (hw : 0 ≤ w₀)
    (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) :
    ENNReal.ofReal ((∫ y, a y) + w₀ * (∫ y, b y)) ≤ ∫⁻ y, ENNReal.ofReal (a y + w₀ * b y) := by
  calc ENNReal.ofReal ((∫ y, a y) + w₀ * (∫ y, b y))
        ≤ ENNReal.ofReal (∫ y, a y) + ENNReal.ofReal w₀ * ENNReal.ofReal (∫ y, b y) := by
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_mul hw]
    _ ≤ (∫⁻ y, ENNReal.ofReal (a y)) + ENNReal.ofReal w₀ * (∫⁻ y, ENNReal.ofReal (b y)) := by
          gcongr
          · exact ofReal_integral_le_lintegral ha
          · exact ofReal_integral_le_lintegral hb
    _ = (∫⁻ y, ENNReal.ofReal (a y)) + (∫⁻ y, ENNReal.ofReal (w₀ * b y)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul hw]
    _ ≤ ∫⁻ y, (ENNReal.ofReal (a y) + ENNReal.ofReal (w₀ * b y)) := le_lintegral_add _ _
    _ = ∫⁻ y, ENNReal.ofReal (a y + w₀ * b y) := by
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_add (ha y) (mul_nonneg hw (hb y))]

private theorem periodEnergy_lt_top {Γ : Set Symmetry} {P w₀ : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hw : 0 ≤ w₀) (hp : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) < ⊤ := by
  have hjoint : AEStronglyMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H z.1 z.2)‖ ^ 2) volume :=
    (traceSecond_continuous.norm.pow 2).comp_aestronglyMeasurable hp.measurable_secondDeriv
  have hA : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hjoint.aemeasurable.ennreal_ofReal.lintegral_prod_right').restrict
  have hslice : ∀ᵐ σ, AEMeasurable (fun y => ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2)) volume := by
    filter_upwards [hjoint.prodMk_left] with σ hσ
    exact hσ.aemeasurable.ennreal_ofReal
  have hle : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) +
        ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y)) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hA]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hslice] with σ hσ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hσ]
    refine lintegral_mono fun y => ?_
    refine ENNReal.ofReal_add_le.trans ?_
    rw [ENNReal.ofReal_mul hw]
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2
    ⟨hp.sumSecondPartials_finite, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp.gradient_finite⟩)

private theorem norm_apply_sq_le (A : Space →L[ℝ] Space) (u : Space) :
    ‖A u‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [← mul_pow]
  gcongr
  exact A.le_opNorm u

private theorem cubicCoeff_sq_mul {w₀ : ℝ} (hw : 0 < w₀) (n : ℝ) :
    (2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2 * w₀ = 4 / 3 * n ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsp : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [mul_pow, div_pow, div_pow, h3, hs]
  field_simp
  ring

private theorem cube_rpow_two_thirds {n : ℝ} (hn : 0 ≤ n) :
    ENNReal.ofReal (n ^ 3) ^ ((2 : ℝ) / 3) = ENNReal.ofReal (n ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [← Real.rpow_natCast n 3, ← Real.rpow_mul hn,
    show ((3 : ℕ) : ℝ) * (2 / 3) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem gapGradTerm_of (h2 : PerturbationSliceHolds) (h3 : EnergyBoundsHolds)
    (h4 : CubicWeightProductHolds) (h5 : PeriodGlueHolds) : GapGradTermHolds := by
  intro Γ P w₀ n cubic v G H g D hw hn hp hD hbound
  have hfin := periodEnergy_lt_top hw.le hp
  have key : ∀ᵐ σ, (∫⁻ y, ENNReal.ofReal (‖D σ y (v σ y)‖ ^ 2)) ≤
      ENNReal.ofReal ((gapGradCoeff w₀ cubic * n) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
    cases cubic with
    | false =>
      have hk : gapGradCoeff w₀ false = supBoundFactor w₀ := by simp [gapGradCoeff]
      rw [hk]
      filter_upwards [h3.1 Γ P w₀ v G H g hw hp] with σ hσ
      have hb : (∫⁻ y, ENNReal.ofReal (‖D σ y‖ ^ 2)) ≤ ENNReal.ofReal (n ^ 2) := by
        have h := hbound σ
        simpa [PieceGradBound] using h
      calc (∫⁻ y, ENNReal.ofReal (‖D σ y (v σ y)‖ ^ 2))
            ≤ ∫⁻ y, ENNReal.ofReal (‖D σ y‖ ^ 2) * ENNReal.ofReal (supBoundFactor w₀ ^ 2 *
                ((∫ z, ‖secondDerivTrace (H σ z)‖ ^ 2) + w₀ * (∫ z, matSq (G σ z)))) := by
              refine lintegral_mono_ae ?_
              filter_upwards [hσ] with y hy
              rw [← ENNReal.ofReal_mul (sq_nonneg _)]
              refine ENNReal.ofReal_le_ofReal ((norm_apply_sq_le _ _).trans ?_)
              exact mul_le_mul_of_nonneg_left hy (sq_nonneg _)
        _ = (∫⁻ y, ENNReal.ofReal (‖D σ y‖ ^ 2)) * ENNReal.ofReal (supBoundFactor w₀ ^ 2 *
                ((∫ z, ‖secondDerivTrace (H σ z)‖ ^ 2) + w₀ * (∫ z, matSq (G σ z)))) :=
              lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (supBoundFactor w₀ ^ 2 *
                ((∫ z, ‖secondDerivTrace (H σ z)‖ ^ 2) + w₀ * (∫ z, matSq (G σ z)))) := by
              gcongr
        _ = ENNReal.ofReal ((supBoundFactor w₀ * n) ^ 2) *
              ENNReal.ofReal ((∫ z, ‖secondDerivTrace (H σ z)‖ ^ 2) + w₀ * (∫ z, matSq (G σ z))) := by
              rw [← ENNReal.ofReal_mul (sq_nonneg n), ← ENNReal.ofReal_mul (sq_nonneg _)]
              congr 1
              ring
        _ ≤ ENNReal.ofReal ((supBoundFactor w₀ * n) ^ 2) *
              ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
              gcongr
              exact ofReal_sliceEnergy_le (fun z => ‖secondDerivTrace (H σ z)‖ ^ 2)
                (fun z => matSq (G σ z)) hw.le (fun _ => sq_nonneg _) (fun _ => columnSquares_nonneg _)
    | true =>
      have hk : gapGradCoeff w₀ true = 2 / Real.sqrt 3 / Real.sqrt w₀ := by simp [gapGradCoeff]
      rw [hk]
      filter_upwards [h2 Γ P v G H g hp] with σ hσ
      obtain ⟨hg, _, h6, hG, _⟩ := hσ
      have hb : (∫⁻ y, ENNReal.ofReal (‖D σ y‖ ^ 3)) ≤ ENNReal.ofReal (n ^ 3) := by
        have h := hbound σ
        simpa [PieceGradBound] using h
      have hA : AEStronglyMeasurable (fun y => ‖D σ y‖) volume :=
        (hD.comp_measurable measurable_prodMk_left).norm.aestronglyMeasurable
      have hc4 := h4 (v σ) (G σ) (fun y => ‖D σ y‖) hg h6 hG hA
      have hpow : (∫⁻ y, ENNReal.ofReal (|‖D σ y‖| ^ 3)) ^ ((2 : ℝ) / 3) ≤
          ENNReal.ofReal (n ^ 2) := by
        simp_rw [abs_norm]
        rw [← cube_rpow_two_thirds hn]
        exact ENNReal.rpow_le_rpow hb (by norm_num)
      have hc : 0 ≤ (2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2 := sq_nonneg _
      calc (∫⁻ y, ENNReal.ofReal (‖D σ y (v σ y)‖ ^ 2))
            ≤ ∫⁻ y, ENNReal.ofReal (‖D σ y‖ ^ 2 * ‖v σ y‖ ^ 2) :=
              lintegral_mono fun y => ENNReal.ofReal_le_ofReal (norm_apply_sq_le _ _)
        _ ≤ ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (|‖D σ y‖| ^ 3)) ^ ((2 : ℝ) / 3) *
              (∫⁻ y, ENNReal.ofReal (matSq (G σ y))) := hc4
        _ ≤ ENNReal.ofReal (4 / 3) * ENNReal.ofReal (n ^ 2) *
              (∫⁻ y, ENNReal.ofReal (matSq (G σ y))) := by
              gcongr
        _ = ENNReal.ofReal ((2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2) *
              (ENNReal.ofReal w₀ * ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) := by
              rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc, ← ENNReal.ofReal_mul hc,
                cubicCoeff_sq_mul hw n]
        _ = ENNReal.ofReal ((2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2) *
              ∫⁻ y, ENNReal.ofReal (w₀ * matSq (G σ y)) := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              refine lintegral_congr fun y => ?_
              rw [ENNReal.ofReal_mul hw.le]
        _ ≤ ENNReal.ofReal ((2 / Real.sqrt 3 / Real.sqrt w₀ * n) ^ 2) *
              ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
              gcongr with y
              exact le_add_of_nonneg_left (sq_nonneg _)
  have hE : ENNReal.ofReal ((gapGradCoeff w₀ cubic * n) ^ 2 * weightedEnergy (fun _ => w₀) G H) =
      ENNReal.ofReal ((gapGradCoeff w₀ cubic * n) ^ 2) *
        periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    exact ENNReal.ofReal_toReal hfin.ne
  rw [hE]
  exact h5.2.2.2 _ _ _ (sq_nonneg _) key

end CertReduction

end Breakdown

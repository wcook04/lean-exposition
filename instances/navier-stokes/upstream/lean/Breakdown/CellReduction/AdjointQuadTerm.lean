import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace AdjointQuadInternal

theorem traceOfSecond_continuous : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem columnSquares_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coeff_nonneg {w₀ : ℝ} (hw : 0 < w₀) (b : Bool) : 0 ≤ adjointQuadCoeff w₀ b := by
  cases b
  · have h1 : 0 ≤ supBoundFactor w₀ := by unfold supBoundFactor; positivity
    have h2 : adjointQuadCoeff w₀ false = supBoundFactor w₀ / Real.sqrt w₀ := rfl
    rw [h2]
    positivity
  · have h2 : adjointQuadCoeff w₀ true = 2 / Real.sqrt 3 / w₀ := rfl
    rw [h2]
    positivity

theorem pairing_sq_le {f g : Space → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    (∫⁻ y, f y * g y) ^ 2 ≤ (∫⁻ y, f y ^ 2) * (∫⁻ y, g y ^ 2) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ y, f y * g y) ^ 2
        ≤ ((∫⁻ y, f y ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
    _ = (∫⁻ y, f y ^ 2) * (∫⁻ y, g y ^ 2) := by
          rw [mul_pow, hsq, hsq]

theorem ofReal_integral_le {f : Space → ℝ} (hf : ∀ y, 0 ≤ f y) :
    ENNReal.ofReal (∫ y, f y) ≤ ∫⁻ y, ENNReal.ofReal (f y) := by
  by_cases hi : Integrable f
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

theorem sliceEnergy_le (a b : Space → ℝ) {w₀ : ℝ} (hw : 0 ≤ w₀)
    (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) :
    ENNReal.ofReal ((∫ y, a y) + w₀ * (∫ y, b y)) ≤ ∫⁻ y, ENNReal.ofReal (a y + w₀ * b y) := by
  have e1 : ∫⁻ y, ENNReal.ofReal (a y + w₀ * b y) =
      ∫⁻ y, (ENNReal.ofReal (a y) + ENNReal.ofReal w₀ * ENNReal.ofReal (b y)) := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_add (ha y) (mul_nonneg hw (hb y)), ENNReal.ofReal_mul hw]
  rw [e1]
  refine le_trans ?_ (le_lintegral_add _ _)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.ofReal_add_le.trans ?_
  rw [ENNReal.ofReal_mul hw]
  gcongr
  · exact ofReal_integral_le ha
  · exact ofReal_integral_le hb

theorem energy_lt_top {Γ : Set Symmetry} {P w₀ : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hw : 0 ≤ w₀) (hp : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) < ⊤ := by
  have hj : AEStronglyMeasurable (fun p : ℝ × Space => ‖secondDerivTrace (H p.1 p.2)‖ ^ 2) volume :=
    (traceOfSecond_continuous.norm.pow 2).comp_aestronglyMeasurable hp.measurable_secondDeriv
  have hσm : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hj.aemeasurable.ennreal_ofReal.lintegral_prod_right').restrict
  have hs : ∀ᵐ σ, AEMeasurable (fun y => ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2)) volume := by
    filter_upwards [hj.prodMk_left] with σ hσ
    exact hσ.aemeasurable.ennreal_ofReal
  have hle : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) +
        ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y)) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hσm]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hs] with σ hσ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hσ]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hw]
    exact ENNReal.ofReal_add_le
  refine lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hp.sumSecondPartials_finite, ?_⟩)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp.gradient_finite

theorem columnSquares_le_energy (w₀ : ℝ) (hw : 0 ≤ w₀) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    ENNReal.ofReal w₀ * (∫⁻ y, ENNReal.ofReal (matSq (G y))) ≤
      ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2 + w₀ * matSq (G y)) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hw]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (sq_nonneg _))

theorem opNorm_sq_le_lintegral (h0 : OperatorSquareBoundHolds) (G : Space → (Space →L[ℝ] Space)) :
    (∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2)) ≤ ∫⁻ y, ENNReal.ofReal (matSq (G y)) :=
  lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h0 (G y))

theorem cube_rpow_twoThirds {n : ℝ} (hn : 0 ≤ n) :
    ENNReal.ofReal (n ^ 3) ^ ((2 : ℝ) / 3) = ENNReal.ofReal (n ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [← Real.rpow_natCast n 3, ← Real.rpow_mul hn, ← Real.rpow_natCast n 2]
  norm_num

theorem squareCoeff_noncubic {a w₀ z : ℝ} (hw : 0 < w₀) :
    (a / Real.sqrt w₀ * z) ^ 2 * w₀ = a ^ 2 * z ^ 2 := by
  have hs : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  have hsp : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  rw [mul_pow, div_pow, hs]
  field_simp

theorem squareCoeff_cubic {w₀ z : ℝ} (hw : 0 < w₀) :
    (2 / Real.sqrt 3 / w₀ * z) ^ 2 * w₀ * w₀ = 4 / 3 * z ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [mul_pow, div_pow, div_pow, h3]
  field_simp
  ring

end AdjointQuadInternal

open AdjointQuadInternal in
theorem adjointQuadTerm_of (h0 : MatrixFactsHolds) (h2 : PerturbationSliceHolds)
    (h3 : EnergyBoundsHolds) (h4 : CubicWeightProductHolds) (h5 : PeriodGlueHolds) :
    AdjointQuadTermHolds := by
  intro Γ P w₀ z cubic v G H g ζ hw hz hp hζ hsize
  have hfin := energy_lt_top hw.le hp
  have hc : 0 ≤ adjointQuadCoeff w₀ cubic * z := mul_nonneg (coeff_nonneg hw cubic) hz
  have key : ∀ᵐ σ, (∫⁻ y, ENNReal.ofReal (‖G σ y (v σ y)‖ * ‖ζ σ y‖)) ≤
      ENNReal.ofReal (adjointQuadCoeff w₀ cubic * z) *
        ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
    filter_upwards [h2 Γ P v G H g hp, h3.1 Γ P w₀ v G H g hw hp,
      hp.measurable_velocity.prodMk_left, hp.measurable_gradient.prodMk_left,
      hζ.prodMk_left] with σ hσ hsup hvs hGs hζs
    have hvm : AEStronglyMeasurable (fun y => v σ y) volume := hvs
    have hGm : AEStronglyMeasurable (fun y => G σ y) volume := hGs
    have hζm : AEStronglyMeasurable (fun y => ζ σ y) volume := hζs
    have hXY := columnSquares_le_energy w₀ hw.le (G σ) (H σ)
    have hGX := opNorm_sq_le_lintegral h0.1 (G σ)
    apply (ENNReal.pow_le_pow_left_iff two_ne_zero).1
    cases cubic with
    | false =>
      have hk : adjointQuadCoeff w₀ false = supBoundFactor w₀ / Real.sqrt w₀ := rfl
      rw [hk]
      have ha : 0 ≤ supBoundFactor w₀ := by unfold supBoundFactor; positivity
      have hcn : 0 ≤ supBoundFactor w₀ / Real.sqrt w₀ * z := by positivity
      have hb : (∫⁻ y, ENNReal.ofReal (‖ζ σ y‖ ^ 2)) ≤ ENNReal.ofReal (z ^ 2) := by
        have h := hsize σ
        simpa [AdjointSizeBound] using h
      have hE := sliceEnergy_le (fun y => ‖secondDerivTrace (H σ y)‖ ^ 2) (fun y => matSq (G σ y))
        hw.le (fun _ => sq_nonneg _) (fun _ => columnSquares_nonneg _)
      set E : ℝ := (∫ y, ‖secondDerivTrace (H σ y)‖ ^ 2) + w₀ * (∫ y, matSq (G σ y)) with hEdef
      set X : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) with hXdef
      set Y : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y))
        with hYdef
      have hmF : AEMeasurable (fun y => ENNReal.ofReal (‖G σ y‖ * ‖v σ y‖)) volume :=
        (hGm.norm.mul hvm.norm).aemeasurable.ennreal_ofReal
      have hmZ : AEMeasurable (fun y => ENNReal.ofReal ‖ζ σ y‖) volume :=
        hζm.norm.aemeasurable.ennreal_ofReal
      have hcs := pairing_sq_le hmF hmZ
      have hF2 : (∫⁻ y, ENNReal.ofReal (‖G σ y‖ * ‖v σ y‖) ^ 2) ≤
          X * ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) := by
        calc (∫⁻ y, ENNReal.ofReal (‖G σ y‖ * ‖v σ y‖) ^ 2)
              ≤ ∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2) * ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) := by
                refine lintegral_mono_ae ?_
                filter_upwards [hsup] with y hy
                rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (sq_nonneg _)]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [mul_pow]
                exact mul_le_mul_of_nonneg_left hy (sq_nonneg _)
          _ = (∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2)) * ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) :=
                lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
          _ ≤ X * ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) := by gcongr
      have hZ2 : (∫⁻ y, ENNReal.ofReal ‖ζ σ y‖ ^ 2) ≤ ENNReal.ofReal (z ^ 2) := by
        refine le_trans (le_of_eq ?_) hb
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
      have hk2 : ENNReal.ofReal ((supBoundFactor w₀ / Real.sqrt w₀ * z) ^ 2) * ENNReal.ofReal w₀ =
          ENNReal.ofReal (supBoundFactor w₀ ^ 2) * ENNReal.ofReal (z ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
          squareCoeff_noncubic hw]
      calc (∫⁻ y, ENNReal.ofReal (‖G σ y (v σ y)‖ * ‖ζ σ y‖)) ^ 2
            ≤ (∫⁻ y, ENNReal.ofReal (‖G σ y‖ * ‖v σ y‖) * ENNReal.ofReal ‖ζ σ y‖) ^ 2 := by
              gcongr with y
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              exact mul_le_mul_of_nonneg_right ((G σ y).le_opNorm _) (norm_nonneg _)
        _ ≤ (∫⁻ y, ENNReal.ofReal (‖G σ y‖ * ‖v σ y‖) ^ 2) * (∫⁻ y, ENNReal.ofReal ‖ζ σ y‖ ^ 2) :=
              hcs
        _ ≤ X * ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) * ENNReal.ofReal (z ^ 2) := by
              gcongr
        _ = ENNReal.ofReal (supBoundFactor w₀ ^ 2) * ENNReal.ofReal (z ^ 2) * X * ENNReal.ofReal E := by
              rw [ENNReal.ofReal_mul (sq_nonneg _)]
              ring
        _ = ENNReal.ofReal ((supBoundFactor w₀ / Real.sqrt w₀ * z) ^ 2) * (ENNReal.ofReal w₀ * X) *
              ENNReal.ofReal E := by
              rw [← hk2]
              ring
        _ ≤ ENNReal.ofReal ((supBoundFactor w₀ / Real.sqrt w₀ * z) ^ 2) * Y * Y := by
              gcongr
        _ = (ENNReal.ofReal (supBoundFactor w₀ / Real.sqrt w₀ * z) * Y) ^ 2 := by
              rw [ENNReal.ofReal_pow hcn]
              ring
    | true =>
      have hk : adjointQuadCoeff w₀ true = 2 / Real.sqrt 3 / w₀ := rfl
      rw [hk]
      have hcn : 0 ≤ 2 / Real.sqrt 3 / w₀ * z := by positivity
      have hb : (∫⁻ y, ENNReal.ofReal (‖ζ σ y‖ ^ 3)) ≤ ENNReal.ofReal (z ^ 3) := by
        have h := hsize σ
        simpa [AdjointSizeBound] using h
      obtain ⟨hwg, _, h6, hGf, _⟩ := hσ
      set X : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) with hXdef
      set Y : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y))
        with hYdef
      have hc4 := h4 (v σ) (G σ) (fun y => ‖ζ σ y‖) hwg h6 hGf hζm.norm
      have hpow : (∫⁻ y, ENNReal.ofReal (|‖ζ σ y‖| ^ 3)) ^ ((2 : ℝ) / 3) ≤
          ENNReal.ofReal (z ^ 2) := by
        simp_rw [abs_norm]
        rw [← cube_rpow_twoThirds hz]
        exact ENNReal.rpow_le_rpow hb (by norm_num)
      have hmF : AEMeasurable (fun y => ENNReal.ofReal ‖G σ y‖) volume :=
        hGm.norm.aemeasurable.ennreal_ofReal
      have hmZ : AEMeasurable (fun y => ENNReal.ofReal (‖ζ σ y‖ * ‖v σ y‖)) volume :=
        (hζm.norm.mul hvm.norm).aemeasurable.ennreal_ofReal
      have hcs := pairing_sq_le hmF hmZ
      have hF2 : (∫⁻ y, ENNReal.ofReal ‖G σ y‖ ^ 2) ≤ X := by
        refine le_trans (le_of_eq ?_) hGX
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
      have hZ2 : (∫⁻ y, ENNReal.ofReal (‖ζ σ y‖ * ‖v σ y‖) ^ 2) ≤
          ENNReal.ofReal (4 / 3) * ENNReal.ofReal (z ^ 2) * X := by
        calc (∫⁻ y, ENNReal.ofReal (‖ζ σ y‖ * ‖v σ y‖) ^ 2)
              = ∫⁻ y, ENNReal.ofReal ((fun y => ‖ζ σ y‖) y ^ 2 * ‖v σ y‖ ^ 2) := by
                refine lintegral_congr fun y => ?_
                rw [← ENNReal.ofReal_pow (by positivity), mul_pow]
          _ ≤ ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (|‖ζ σ y‖| ^ 3)) ^ ((2 : ℝ) / 3) *
                (∫⁻ y, ENNReal.ofReal (matSq (G σ y))) := hc4
          _ ≤ ENNReal.ofReal (4 / 3) * ENNReal.ofReal (z ^ 2) * X := by gcongr
      have hk2 : ENNReal.ofReal ((2 / Real.sqrt 3 / w₀ * z) ^ 2) * ENNReal.ofReal w₀ *
          ENNReal.ofReal w₀ = ENNReal.ofReal (4 / 3) * ENNReal.ofReal (z ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by norm_num), squareCoeff_cubic hw]
      calc (∫⁻ y, ENNReal.ofReal (‖G σ y (v σ y)‖ * ‖ζ σ y‖)) ^ 2
            ≤ (∫⁻ y, ENNReal.ofReal ‖G σ y‖ * ENNReal.ofReal (‖ζ σ y‖ * ‖v σ y‖)) ^ 2 := by
              gcongr with y
              rw [← ENNReal.ofReal_mul (norm_nonneg _)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ‖G σ y (v σ y)‖ * ‖ζ σ y‖ ≤ ‖G σ y‖ * ‖v σ y‖ * ‖ζ σ y‖ :=
                    mul_le_mul_of_nonneg_right ((G σ y).le_opNorm _) (norm_nonneg _)
                _ = ‖G σ y‖ * (‖ζ σ y‖ * ‖v σ y‖) := by ring
        _ ≤ (∫⁻ y, ENNReal.ofReal ‖G σ y‖ ^ 2) *
              (∫⁻ y, ENNReal.ofReal (‖ζ σ y‖ * ‖v σ y‖) ^ 2) := hcs
        _ ≤ X * (ENNReal.ofReal (4 / 3) * ENNReal.ofReal (z ^ 2) * X) := by gcongr
        _ = ENNReal.ofReal ((2 / Real.sqrt 3 / w₀ * z) ^ 2) * (ENNReal.ofReal w₀ * X) *
              (ENNReal.ofReal w₀ * X) := by
              rw [← hk2]
              ring
        _ ≤ ENNReal.ofReal ((2 / Real.sqrt 3 / w₀ * z) ^ 2) * Y * Y := by gcongr
        _ = (ENNReal.ofReal (2 / Real.sqrt 3 / w₀ * z) * Y) ^ 2 := by
              rw [ENNReal.ofReal_pow hcn]
              ring
  have hEq : ENNReal.ofReal (adjointQuadCoeff w₀ cubic * z * weightedEnergy (fun _ => w₀) G H) =
      ENNReal.ofReal (adjointQuadCoeff w₀ cubic * z) *
        periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
    rw [ENNReal.ofReal_mul hc]
    congr 1
    exact ENNReal.ofReal_toReal hfin.ne
  rw [hEq]
  exact h5.2.2.2 _ _ _ hc key

end CertReduction

end Breakdown

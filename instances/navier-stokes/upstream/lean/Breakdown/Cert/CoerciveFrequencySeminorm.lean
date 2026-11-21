import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveFrequencySeminormTransport
import Breakdown.Cert.CoerciveFrequencySeminormAngular
import Breakdown.Cert.CoerciveFrequencySeminormWeight

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

open Breakdown.Coercive.Internal.FieldModes

theorem int_abs_le_sq (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    rw [← sq_abs]
    nlinarith

theorem cnormSq_sub_half_le (a : Fin 3 → ℂ) (M : Fin 3 × Fin 3 → ℂ) (y : Space) :
    cnormSq (fun i => a i - (1 / 2 : ℂ) * ∑ j : Fin 3, M (i, j) * ((y j : ℝ) : ℂ)) ≤
      2 * cnormSq a + 1 / 2 * ‖y‖ ^ 2 * cnormSq M := by
  have hy : ‖y‖ ^ 2 = ∑ j : Fin 3, y j ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  have hrow : ∀ i : Fin 3, ‖∑ j : Fin 3, M (i, j) * ((y j : ℝ) : ℂ)‖ ^ 2 ≤
      (∑ j : Fin 3, ‖M (i, j)‖ ^ 2) * ‖y‖ ^ 2 := by
    intro i
    rw [hy]
    have h1 : ‖∑ j : Fin 3, M (i, j) * ((y j : ℝ) : ℂ)‖ ≤ ∑ j : Fin 3, ‖M (i, j)‖ * |y j| := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M (i, j)‖) (fun j => |y j|)
    simp only [sq_abs] at h2
    calc _ ≤ (∑ j : Fin 3, ‖M (i, j)‖ * |y j|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hcomp : ∀ i : Fin 3, ‖a i - (1 / 2 : ℂ) * ∑ j : Fin 3, M (i, j) * ((y j : ℝ) : ℂ)‖ ^ 2 ≤
      2 * ‖a i‖ ^ 2 + 1 / 2 * ((∑ j : Fin 3, ‖M (i, j)‖ ^ 2) * ‖y‖ ^ 2) := by
    intro i
    have h := hrow i
    set s := ∑ j : Fin 3, M (i, j) * ((y j : ℝ) : ℂ)
    have h3 : ‖a i - (1 / 2 : ℂ) * s‖ ≤ ‖a i‖ + 1 / 2 * ‖s‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      norm_num
    have h4 : 0 ≤ ‖a i - (1 / 2 : ℂ) * s‖ := norm_nonneg _
    have h5 := mul_le_mul h3 h3 h4 (by positivity)
    nlinarith [norm_nonneg (a i), norm_nonneg s, sq_nonneg (‖a i‖ - 1 / 2 * ‖s‖)]
  unfold cnormSq
  rw [Fintype.sum_prod_type]
  calc _ ≤ ∑ i : Fin 3, (2 * ‖a i‖ ^ 2 + 1 / 2 * ((∑ j : Fin 3, ‖M (i, j)‖ ^ 2) * ‖y‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hcomp i
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

theorem real_bound {a b c wt B K s t r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hK : 0 ≤ K) (hw0 : 0 ≤ wt) (hwB : wt ≤ B) (hwr : r * wt ≤ B)
    (h1 : s * a ≤ K * (2 * b + 1 / 2 * r * c)) (h2 : t * a ≤ 2 * a + 2 * r * c) :
    (s + t) * wt * a ≤ B * (2 * K + 4) * (b + c + a / (1 + r)) := by
  have hB0 : 0 ≤ B := hw0.trans hwB
  have hr1 : 0 < 1 + r := by linarith
  set d := a / (1 + r) with hd
  have hd0 : 0 ≤ d := div_nonneg ha hr1.le
  have had : a = (1 + r) * d := by rw [hd]; field_simp
  have e1 : s * a * wt ≤ K * (2 * b + 1 / 2 * r * c) * wt := mul_le_mul_of_nonneg_right h1 hw0
  have e2 : t * a * wt ≤ (2 * a + 2 * r * c) * wt := mul_le_mul_of_nonneg_right h2 hw0
  have e3 : wt * a ≤ 2 * B * d := by
    rw [had]
    have : wt * (1 + r) ≤ 2 * B := by linarith
    nlinarith
  have e4 : K * (2 * b + 1 / 2 * r * c) * wt ≤ 2 * K * B * b + 1 / 2 * K * B * c := by
    have q1 : K * b * wt ≤ K * b * B := mul_le_mul_of_nonneg_left hwB (mul_nonneg hK hb)
    have q2 : K * c * (r * wt) ≤ K * c * B := mul_le_mul_of_nonneg_left hwr (mul_nonneg hK hc)
    nlinarith
  have e5 : 2 * r * c * wt ≤ 2 * B * c := by nlinarith
  have f1 : 0 ≤ K * B * c := mul_nonneg (mul_nonneg hK hB0) hc
  have f2 : 0 ≤ K * B * d := mul_nonneg (mul_nonneg hK hB0) hd0
  have f3 : 0 ≤ B * b := mul_nonneg hB0 hb
  have f4 : 0 ≤ B * c := mul_nonneg hB0 hc
  have f5 : 0 ≤ B * d := mul_nonneg hB0 hd0
  nlinarith

theorem modeAverage_mul_left {β : Type*} (ι : ℤ × ℤ) (a : ℝ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι (fun τ φ c => a * f τ φ c) b = (a : ℂ) * modeAverage ι f b := by
  unfold modeAverage
  simp only [Complex.ofReal_mul]
  have e : ∀ τ : ℝ, (∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((a : ℂ) * (f τ φ b : ℂ))) =
      (a : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * (f τ φ b : ℂ) := by
    intro τ
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext φ
    ring
  simp only [e, intervalIntegral.integral_const_mul]
  ring

def dampedField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ • v σ y

theorem modeVel_dampedField (ι : ℤ × ℤ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeVel ι (dampedField v) σ y =
      fun i => (((Real.sqrt (1 + ‖y‖ ^ 2))⁻¹ : ℝ) : ℂ) * modeVel ι v σ y i := by
  funext i
  unfold modeVel dampedField
  rw [← modeAverage_mul_left]
  congr 1
  funext τ φ j
  rw [RotationInternal.axialRot_norm, RotationInternal.axialRot_map_smul, PiLp.smul_apply, smul_eq_mul]

theorem cnormSq_modeVel_dampedField (ι : ℤ × ℤ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (dampedField v) σ y) = cnormSq (modeVel ι v σ y) / (1 + ‖y‖ ^ 2) := by
  rw [modeVel_dampedField]
  have hpos : 0 < 1 + ‖y‖ ^ 2 := by positivity
  unfold cnormSq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt hpos.le, div_eq_inv_mul]

theorem norm_dampedField_sq (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ‖dampedField v σ y‖ ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖ ^ 2) := by
  have hpos : 0 < 1 + ‖y‖ ^ 2 := by positivity
  unfold dampedField
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hpos.le, div_eq_inv_mul]

theorem weightedFrequencySq_lt_top (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (wt : Space → ℝ)
    (hwt0 : ∀ y, 0 ≤ wt y) (hwtc : Continuous wt) (hwtB : ∃ B, ∀ y, wt y ≤ B ∧ ‖y‖ ^ 2 * wt y ≤ B) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt y * cnormSq (modeVel ι v σ y)) < ⊤ := by
  obtain ⟨B, hB⟩ := hwtB
  have hB0 : 0 ≤ B := (hwt0 0).trans (hB 0).1
  have hpi : 0 < Real.pi := Real.pi_pos
  set K : ℝ := (P / (2 * Real.pi)) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  set C : ℝ := B * (2 * K + 4) with hC
  have hC0 : 0 ≤ C := mul_nonneg hB0 (by linarith)
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => dampedField v z.1 z.2) volume := by
    have hc : Continuous (fun z : ℝ × Space => (Real.sqrt (1 + ‖z.2‖ ^ 2))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun z => ?_
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    exact hc.aestronglyMeasurable.smul hv.measurable_velocity
  have hXp : IsTimePeriodic (dampedField v) := fun σ y => by
    unfold dampedField
    rw [hv.periodic_velocity σ y]
  have hX2 : periodLIntegral (fun σ y => ‖dampedField v σ y‖ ^ 2) < ⊤ := by
    simp only [norm_dampedField_sq]
    exact weighted_velocity_lt_top hv
  have eg := hP.1 g hv.measurable_derivative hv.periodic_derivative hv.derivative_finite
  have eG := hP.2.1 G hv.measurable_gradient hv.periodic_gradient hv.gradient_finite
  have eX := hP.1 (dampedField v) hXm hXp hX2
  have hmode : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt y * cnormSq (modeVel ι v σ y))) ≤
      ENNReal.ofReal C * ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι g σ y)))
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)))
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) σ y))) := by
    intro ι
    have ma : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))) slab :=
      (continuous_cnormSq.measurable.comp_aemeasurable
        (aemeasurable_modeVel hv.measurable_derivative ι)).ennreal_ofReal
    have mb : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) slab :=
      (continuous_cnormSq.measurable.comp_aemeasurable
        (aemeasurable_modeGrad hv.measurable_gradient ι)).ennreal_ofReal
    have mc : AEMeasurable (fun z : ℝ × Space =>
        ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2))) slab :=
      (continuous_cnormSq.measurable.comp_aemeasurable (aemeasurable_modeVel hXm ι)).ennreal_ofReal
    have h1 := transport_mode_normSq hP hD hR hv hP0 ι
    have h2 := angular_mode_bound hP hD hR hv hP0 ι
    have hpt : ∀ᵐ z ∂slab, ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt z.2 *
        cnormSq (modeVel ι v z.1 z.2)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
          + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))
          + ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2))) := by
      rw [slab_eq]
      refine ae_restrict_of_ae ?_
      filter_upwards [h1, h2] with z hz1 hz2
      have ha := cnormSq_nonneg (modeVel ι v z.1 z.2)
      have hb := cnormSq_nonneg (modeVel ι g z.1 z.2)
      have hc := cnormSq_nonneg (modeGrad ι G z.1 z.2)
      rw [← ENNReal.ofReal_add hb hc, ← ENNReal.ofReal_add (add_nonneg hb hc) (cnormSq_nonneg _),
        ← ENNReal.ofReal_mul hC0, cnormSq_modeVel_dampedField]
      apply ENNReal.ofReal_le_ofReal
      have hs := cnormSq_sub_half_le (modeVel ι g z.1 z.2) (modeGrad ι G z.1 z.2) z.2
      have ht : (2 * Real.pi * ι.1 / P) ^ 2 * cnormSq (modeVel ι v z.1 z.2) ≤
          2 * cnormSq (modeVel ι g z.1 z.2) + 1 / 2 * ‖z.2‖ ^ 2 * cnormSq (modeGrad ι G z.1 z.2) := by
        nlinarith
      have hKι : K * (2 * Real.pi * ι.1 / P) ^ 2 = (ι.1 : ℝ) ^ 2 := by
        rw [hK]
        field_simp
      have h1' : (ι.1 : ℝ) ^ 2 * cnormSq (modeVel ι v z.1 z.2) ≤
          K * (2 * cnormSq (modeVel ι g z.1 z.2) + 1 / 2 * ‖z.2‖ ^ 2 * cnormSq (modeGrad ι G z.1 z.2)) := by
        rw [← hKι, mul_assoc]
        exact mul_le_mul_of_nonneg_left ht hK0
      exact real_bound ha hb hc (sq_nonneg ‖z.2‖) hK0 (hwt0 z.2) (hB z.2).1 (hB z.2).2 h1' hz2
    have hae := Measure.ae_ae_of_ae_prod hpt
    calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal C *
            (ENNReal.ofReal (cnormSq (modeVel ι g σ y)) + ENNReal.ofReal (cnormSq (modeGrad ι G σ y))
              + ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) σ y))) :=
          lintegral_mono_ae (hae.mono fun σ hσ => lintegral_mono_ae hσ)
      _ = ENNReal.ofReal C * ∫⁻ z, (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
            + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))
            + ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2))) ∂slab := by
          have hF : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal C *
              (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
                + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))
                + ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2)))) slab :=
            ((ma.add mb).add mc).const_mul _
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact (lintegral_prod _ hF).symm
      _ = _ := by
          have mab : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
              + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) slab := ma.add mb
          have e1 : ∫⁻ z, (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
              + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))
              + ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2))) ∂slab =
              (∫⁻ z, (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
                + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) ∂slab)
              + ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) z.1 z.2)) ∂slab :=
            lintegral_add_left' mab _
          have e2 : ∫⁻ z, (ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2))
              + ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) ∂slab =
              (∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι g z.1 z.2)) ∂slab)
              + ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) ∂slab :=
            lintegral_add_left' ma _
          rw [e1, e2, lintegral_prod _ ma, lintegral_prod _ mb, lintegral_prod _ mc]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hmode) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ← eg, ← eG, ← eX]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hv.derivative_finite, hv.gradient_finite⟩, hX2⟩)

theorem weightedFrequency_lt_top (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (wt : Space → ℝ)
    (hwt0 : ∀ y, 0 ≤ wt y) (hwtc : Continuous wt) (hwtB : ∃ B, ∀ y, wt y ≤ B ∧ ‖y‖ ^ 2 * wt y ≤ B) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y * cnormSq (modeVel ι v σ y)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (weightedFrequencySq_lt_top hP hD hR hv hP0 wt hwt0 hwtc hwtB)
  refine ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => ?_
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ wt y * cnormSq (modeVel ι v σ y) :=
    mul_nonneg (hwt0 y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h1 := int_abs_le_sq ι.1
  have h2 := int_abs_le_sq ι.2
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (add_le_add h1 h2) hc

end Internal

end FrequencySeminorm

end Coercive

end Breakdown

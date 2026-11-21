import Breakdown.Cert.CoerciveFrequencySeminorm
import Breakdown.Cert.CoerciveFrequencySeminormBoundSub
import Breakdown.Cert.CoerciveSmoothPressure

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencyBound

def boundConstant (P B : ℝ) : ℝ := 2 * B * (2 * (P / (2 * Real.pi)) ^ 2 + 4)

def fieldSize (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (g : ℝ → Space → Space) : ℝ≥0∞ :=
  periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) + periodLIntegral (fun σ y => matSq (G σ y))
    + periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)

namespace Internal

open Breakdown.Coercive.Internal.FieldModes
open Breakdown.Coercive.FrequencySeminorm.Internal

theorem dampedField_periodLIntegral_le (v : ℝ → Space → Space) :
    periodLIntegral (fun σ y => ‖dampedField v σ y‖ ^ 2) ≤
      2 * periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun y => ?_
  show ENNReal.ofReal (‖dampedField v σ y‖ ^ 2) ≤ 2 * ENNReal.ofReal (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
  rw [norm_dampedField_sq]
  suffices key : ‖v σ y‖ ^ 2 / (1 + ‖y‖ ^ 2) ≤ 2 * (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) by
    have h := ENNReal.ofReal_le_ofReal key
    rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at h
  have h0 : 0 < (1 + ‖y‖) ^ 2 := by positivity
  have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
  have h1 : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖y‖ - 1)]
  set q := ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have e : ‖v σ y‖ ^ 2 = q * (1 + ‖y‖) ^ 2 := by rw [hq]; field_simp
  rw [div_le_iff₀ h2, e]
  nlinarith [mul_le_mul_of_nonneg_left h1 hq0]

theorem weighted_le_damped (v : ℝ → Space → Space) :
    periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) ≤
      periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖ ^ 2)) := by
  refine periodLIntegral_mono fun σ y => ?_
  have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
  have h1 : 1 + ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
  exact div_le_div_of_nonneg_left (sq_nonneg _) h2 h1

theorem fieldSize_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) : fieldSize v G g < ⊤ := by
  unfold fieldSize
  refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hv.derivative_finite, hv.gradient_finite⟩, ?_⟩
  exact lt_of_le_of_lt (weighted_le_damped v) (weighted_velocity_lt_top hv)

theorem dampedField_square {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    AEStronglyMeasurable (fun z : ℝ × Space => dampedField v z.1 z.2) volume ∧
      IsTimePeriodic (dampedField v) ∧ periodLIntegral (fun σ y => ‖dampedField v σ y‖ ^ 2) < ⊤ := by
  refine ⟨?_, fun σ y => ?_, ?_⟩
  · have hc : Continuous (fun z : ℝ × Space => (Real.sqrt (1 + ‖z.2‖ ^ 2))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun z => ?_
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    exact hc.aestronglyMeasurable.smul hv.measurable_velocity
  · unfold dampedField
    rw [hv.periodic_velocity σ y]
  · simp only [norm_dampedField_sq]
    exact weighted_velocity_lt_top hv

theorem abs_freq_le {P a R : ℝ} (hP0 : 0 < P) (ha : |a| ≤ R) (ι : ℤ × ℤ) :
    |2 * Real.pi * ι.1 / P + ι.2 * a| ≤ (2 * Real.pi / P + R) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) := by
  have hpi : 0 < 2 * Real.pi / P := by positivity
  have hR0 : 0 ≤ R := (abs_nonneg _).trans ha
  have e1 : |2 * Real.pi * (ι.1 : ℝ) / P| = 2 * Real.pi / P * |(ι.1 : ℝ)| := by
    rw [show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul, abs_of_pos hpi]
  have e2 : |(ι.2 : ℝ) * a| ≤ |(ι.2 : ℝ)| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have h1 := int_abs_le_sq ι.1
  have h2 := int_abs_le_sq ι.2
  have s1 := sq_nonneg (ι.1 : ℝ)
  have s2 := sq_nonneg (ι.2 : ℝ)
  calc _ ≤ |2 * Real.pi * (ι.1 : ℝ) / P| + |(ι.2 : ℝ) * a| := abs_add_le _ _
    _ ≤ 2 * Real.pi / P * (ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2 * R := by
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left h1 hpi.le, mul_le_mul_of_nonneg_right h2 hR0]
    _ ≤ _ := by nlinarith [mul_nonneg hpi.le s2, mul_nonneg hR0 s1]

theorem two_mul_norm_le (x y : ℝ) {t : ℝ} (ht : 0 < t) : 2 * (x * y) ≤ t * x ^ 2 + y ^ 2 / t := by
  have h : 0 ≤ (t * x - y) ^ 2 / t := by positivity
  have e : (t * x - y) ^ 2 / t = t * x ^ 2 - 2 * (x * y) + y ^ 2 / t := by
    field_simp
    ring
  linarith

theorem cnormSq_add_le_split (a b : Fin 3 → ℂ) {t : ℝ} (ht : 0 < t) :
    cnormSq (a + b) ≤ (1 + t) * cnormSq a + (1 + 1 / t) * cnormSq b := by
  unfold cnormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(a + b) i‖ ≤ ‖a i‖ + ‖b i‖ := norm_add_le _ _
  have h2 := two_mul_norm_le ‖a i‖ ‖b i‖ ht
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : (1 + 1 / t) * ‖b i‖ ^ 2 = ‖b i‖ ^ 2 + ‖b i‖ ^ 2 / t := by ring
  have e2 : (‖a i‖ + ‖b i‖) ^ 2 = ‖a i‖ ^ 2 + 2 * (‖a i‖ * ‖b i‖) + ‖b i‖ ^ 2 := by ring
  rw [e]
  nlinarith

theorem cnormSq_sub_le_split (a b : Fin 3 → ℂ) {t : ℝ} (ht : 0 < t) :
    cnormSq (a - b) ≤ (1 + t) * cnormSq a + (1 + 1 / t) * cnormSq b := by
  unfold cnormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(a - b) i‖ ≤ ‖a i‖ + ‖b i‖ := norm_sub_le _ _
  have h2 := two_mul_norm_le ‖a i‖ ‖b i‖ ht
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : (1 + 1 / t) * ‖b i‖ ^ 2 = ‖b i‖ ^ 2 + ‖b i‖ ^ 2 / t := by ring
  have e2 : (‖a i‖ + ‖b i‖) ^ 2 = ‖a i‖ ^ 2 + 2 * (‖a i‖ * ‖b i‖) + ‖b i‖ ^ 2 := by ring
  rw [e]
  nlinarith

def modeSum (wt : ℤ × ℤ → Space → ℝ) (x : ℝ → Space → Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (wt ι y * cnormSq (modeVel ι x σ y))

theorem iter_le_of_ae {f a b : ℝ × Space → ℝ≥0∞} (ha : AEMeasurable a slab) (hb : AEMeasurable b slab)
    {c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤) (h : ∀ᵐ z ∂slab, f z ≤ c * a z + d * b z) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f (σ, y)) ≤
      c * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, a (σ, y)) + d * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, b (σ, y) := by
  have hae := Measure.ae_ae_of_ae_prod h
  calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (c * a (σ, y) + d * b (σ, y)) :=
        lintegral_mono_ae (hae.mono fun σ hσ => lintegral_mono_ae hσ)
    _ = ∫⁻ z, (c * a z + d * b z) ∂slab :=
        (lintegral_prod _ ((ha.const_mul c).add (hb.const_mul d))).symm
    _ = _ := by
        rw [lintegral_add_left' (ha.const_mul c), lintegral_const_mul' _ _ hc,
          lintegral_const_mul' _ _ hd, lintegral_prod _ ha, lintegral_prod _ hb]

theorem aemeasurable_weightedMode {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (wt : ℤ × ℤ → Space → ℝ)
    (hwtM : ∀ ι, Measurable (wt ι)) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι X z.1 z.2))) slab :=
  (((hwtM ι).comp measurable_snd).aemeasurable.mul
    (continuous_cnormSq.measurable.comp_aemeasurable (aemeasurable_modeVel hX ι))).ennreal_ofReal

theorem modeSum_split (hP : ModeSquareSumHolds) {Γ₁ Γ₂ : Set Symmetry} {P : ℝ}
    {u v : ℝ → Space → Space} {Gu G : ℝ → Space → (Space →L[ℝ] Space)}
    {Hu H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gu g : ℝ → Space → Space}
    (hu : IsPerturbation Γ₁ P u Gu Hu gu) (hv : IsPerturbation Γ₂ P v G H g)
    (wt : ℤ × ℤ → Space → ℝ) (hwt0 : ∀ ι y, 0 ≤ wt ι y) (hwtM : ∀ ι, Measurable (wt ι))
    {t : ℝ} (ht : 0 < t) :
    modeSum wt u ≤ ENNReal.ofReal (1 + t) * modeSum wt v
        + ENNReal.ofReal (1 + 1 / t) * modeSum wt (fun σ y => u σ y - v σ y) ∧
      modeSum wt v ≤ ENNReal.ofReal (1 + t) * modeSum wt u
        + ENNReal.ofReal (1 + 1 / t) * modeSum wt (fun σ y => u σ y - v σ y) := by
  have hd := isPerturbation_sub hu hv
  obtain ⟨huM, huP, hu2⟩ := dampedField_square hu
  obtain ⟨hvM, hvP, hv2⟩ := dampedField_square hv
  obtain ⟨hdM, hdP, hd2⟩ := dampedField_square hd
  have ht1 : 0 ≤ 1 + t := by linarith
  have ht2 : 0 ≤ 1 + 1 / t := by positivity
  have hsum : ∀ z : ℝ × Space, dampedField u z.1 z.2 =
      dampedField (fun σ y => u σ y - v σ y) z.1 z.2 + dampedField v z.1 z.2 := fun z => by
    unfold dampedField
    rw [← smul_add, sub_add_cancel]
  have hadd : ∀ ι : ℤ × ℤ, ∀ᵐ z ∂slab, modeVel ι (dampedField u) z.1 z.2 =
      modeVel ι (dampedField (fun σ y => u σ y - v σ y)) z.1 z.2 + modeVel ι (dampedField v) z.1 z.2 :=
    fun ι => modeVel_add_ae hP hdM hdP hd2 hvM hvP hv2 huM huP hu2 (ae_of_all _ hsum) ι
  have hpt : ∀ ι : ℤ × ℤ, ∀ z : ℝ × Space,
      modeVel ι (dampedField u) z.1 z.2 =
        modeVel ι (dampedField (fun σ y => u σ y - v σ y)) z.1 z.2 + modeVel ι (dampedField v) z.1 z.2 →
      cnormSq (modeVel ι u z.1 z.2) ≤ (1 + t) * cnormSq (modeVel ι v z.1 z.2)
          + (1 + 1 / t) * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) ∧
        cnormSq (modeVel ι v z.1 z.2) ≤ (1 + t) * cnormSq (modeVel ι u z.1 z.2)
          + (1 + 1 / t) * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) := by
    intro ι z hz
    have hr : 0 < 1 + ‖z.2‖ ^ 2 := by positivity
    have k1 := cnormSq_add_le_split (modeVel ι (dampedField v) z.1 z.2)
      (modeVel ι (dampedField (fun σ y => u σ y - v σ y)) z.1 z.2) ht
    have k2 := cnormSq_sub_le_split (modeVel ι (dampedField u) z.1 z.2)
      (modeVel ι (dampedField (fun σ y => u σ y - v σ y)) z.1 z.2) ht
    rw [add_comm] at hz
    rw [← hz] at k1
    rw [← eq_sub_of_add_eq hz.symm] at k2
    simp only [cnormSq_modeVel_dampedField] at k1 k2
    constructor
    · rw [div_le_iff₀ hr] at k1
      have e : ((1 + t) * (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖ ^ 2))
          + (1 + 1 / t) * (cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) / (1 + ‖z.2‖ ^ 2)))
          * (1 + ‖z.2‖ ^ 2) = (1 + t) * cnormSq (modeVel ι v z.1 z.2)
            + (1 + 1 / t) * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) := by
        field_simp
      linarith
    · rw [div_le_iff₀ hr] at k2
      have e : ((1 + t) * (cnormSq (modeVel ι u z.1 z.2) / (1 + ‖z.2‖ ^ 2))
          + (1 + 1 / t) * (cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) / (1 + ‖z.2‖ ^ 2)))
          * (1 + ‖z.2‖ ^ 2) = (1 + t) * cnormSq (modeVel ι u z.1 z.2)
            + (1 + 1 / t) * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2) := by
        field_simp
      linarith
  have mu := aemeasurable_weightedMode hu.measurable_velocity wt hwtM
  have mv := aemeasurable_weightedMode hv.measurable_velocity wt hwtM
  have md := aemeasurable_weightedMode (X := fun σ y => u σ y - v σ y) hd.measurable_velocity wt hwtM
  have key : ∀ ι : ℤ × ℤ, ∀ᵐ z ∂slab,
      ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι u z.1 z.2)) ≤
          ENNReal.ofReal (1 + t) * ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι v z.1 z.2))
          + ENNReal.ofReal (1 + 1 / t)
            * ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2)) ∧
        ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι v z.1 z.2)) ≤
          ENNReal.ofReal (1 + t) * ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι u z.1 z.2))
          + ENNReal.ofReal (1 + 1 / t)
            * ENNReal.ofReal (wt ι z.2 * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2)) := by
    intro ι
    filter_upwards [hadd ι] with z hz
    obtain ⟨k1, k2⟩ := hpt ι z hz
    have hw := hwt0 ι z.2
    have c1 := cnormSq_nonneg (modeVel ι u z.1 z.2)
    have c2 := cnormSq_nonneg (modeVel ι v z.1 z.2)
    have c3 := cnormSq_nonneg (modeVel ι (fun σ y => u σ y - v σ y) z.1 z.2)
    rw [← ENNReal.ofReal_mul ht1, ← ENNReal.ofReal_mul ht2, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul ht1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    constructor
    · apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left k1 hw]
    · apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left k2 hw]
  constructor
  · unfold modeSum
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun ι => iter_le_of_ae (mv ι) (md ι) ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top ((key ι).mono fun z hz => hz.1)
  · unfold modeSum
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun ι => iter_le_of_ae (mu ι) (md ι) ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top ((key ι).mono fun z hz => hz.2)

theorem toReal_split {x y d : ℝ≥0∞} (hy : y ≠ ⊤) (hd : d ≠ ⊤) {t : ℝ} (ht : 0 < t)
    (h : x ≤ ENNReal.ofReal (1 + t) * y + ENNReal.ofReal (1 + 1 / t) * d) :
    x.toReal ≤ (1 + t) * y.toReal + (1 + 1 / t) * d.toReal := by
  have h1 : ENNReal.ofReal (1 + t) * y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy
  have h2 : ENNReal.ofReal (1 + 1 / t) * d ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h
  rwa [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by positivity)] at this

theorem tendsto_of_split {a : ℕ → ℝ} {b : ℝ} {d : ℕ → ℝ} (hb : 0 ≤ b) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto d atTop (nhds 0))
    (h1 : ∀ n t, 0 < t → a n ≤ (1 + t) * b + (1 + 1 / t) * d n)
    (h2 : ∀ n t, 0 < t → b ≤ (1 + t) * a n + (1 + 1 / t) * d n) : Tendsto a atTop (nhds b) := by
  set s : ℕ → ℝ := fun n => Real.sqrt (d n) + 1 / ((n : ℝ) + 1) with hs
  have hs0 : ∀ n, 0 < s n := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := Real.sqrt_nonneg (d n)
    simp only [hs]
    linarith
  have hsq : Tendsto (fun n => Real.sqrt (d n)) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hd
    rw [Real.sqrt_zero] at h
    exact h
  have hsl : Tendsto s atTop (nhds 0) := by
    have h := hsq.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact h
  have hdiv : ∀ n, d n / s n ≤ Real.sqrt (d n) := fun n => by
    rw [div_le_iff₀ (hs0 n)]
    have e : d n = Real.sqrt (d n) * Real.sqrt (d n) := (Real.mul_self_sqrt (hd0 n)).symm
    have hle : Real.sqrt (d n) ≤ s n := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hs]
      linarith
    calc d n = Real.sqrt (d n) * Real.sqrt (d n) := e
      _ ≤ Real.sqrt (d n) * s n := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
  have hbound : ∀ n, |a n - b| ≤ s n * (3 * b + 2 * d n) + d n + Real.sqrt (d n) := by
    intro n
    have k1 := h1 n (s n) (hs0 n)
    have k2 := h2 n (s n) (hs0 n)
    have k3 := h1 n 1 one_pos
    have e : (1 + 1 / s n) * d n = d n + d n / s n := by ring
    rw [e] at k1 k2
    norm_num at k3
    have hq := hdiv n
    have hsn := (hs0 n).le
    have p1 := mul_le_mul_of_nonneg_left k3 hsn
    have p2 := mul_nonneg hsn hb
    have p3 := mul_nonneg hsn (hd0 n)
    rw [abs_le]
    constructor <;> nlinarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (Real.norm_eq_abs _).le.trans (hbound n)) ?_
  have h := ((hsl.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 3 * b) atTop (nhds (3 * b))).add
    (hd.const_mul 2))).add hd).add hsq
  simp only [zero_mul, add_zero] at h
  exact h

theorem tendsto_toReal_of_split {X : Type} {N : X → ℝ≥0∞} {v : X} {u e : ℕ → X}
    (hv : N v ≠ ⊤) (hu : ∀ n, N (u n) ≠ ⊤) (he : ∀ n, N (e n) ≠ ⊤)
    (hlim : Tendsto (fun n => N (e n)) atTop (nhds 0))
    (hs : ∀ n t, 0 < t → N (u n) ≤ ENNReal.ofReal (1 + t) * N v + ENNReal.ofReal (1 + 1 / t) * N (e n) ∧
      N v ≤ ENNReal.ofReal (1 + t) * N (u n) + ENNReal.ofReal (1 + 1 / t) * N (e n)) :
    Tendsto (fun n => (N (u n)).toReal) atTop (nhds (N v).toReal) := by
  have hd : Tendsto (fun n => (N (e n)).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at h
    exact h
  exact tendsto_of_split ENNReal.toReal_nonneg (fun n => ENNReal.toReal_nonneg) hd
    (fun n t ht => toReal_split hv (he n) ht (hs n t ht).1)
    (fun n t ht => toReal_split (hu n) (he n) ht (hs n t ht).2)

theorem tendsto_zero_of_le {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) (hab : ∀ n, a n ≤ c * b n)
    (hb : Tendsto b atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  have h := ENNReal.Tendsto.const_mul hb (Or.inr hc)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le) hab

end Internal

open _root_.Breakdown.Coercive.FrequencyBound.Internal
open Breakdown.Coercive.Internal.FieldModes
open Breakdown.Coercive.FrequencySeminorm.Internal

theorem weightedFrequencySq_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (wt : ℤ × ℤ → Space → ℝ)
    (hwt0 : ∀ ι y, 0 ≤ wt ι y) {B : ℝ} (hB : ∀ ι y, wt ι y ≤ B ∧ ‖y‖ ^ 2 * wt ι y ≤ B) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt ι y * cnormSq (modeVel ι v σ y)) ≤
      ENNReal.ofReal (boundConstant P B) * fieldSize v G g := by
  have hB0 : 0 ≤ B := (hwt0 (0, 0) 0).trans (hB (0, 0) 0).1
  have hpi : 0 < Real.pi := Real.pi_pos
  set K : ℝ := (P / (2 * Real.pi)) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  set C : ℝ := B * (2 * K + 4) with hC
  have hC0 : 0 ≤ C := mul_nonneg hB0 (by linarith)
  obtain ⟨hXm, hXp, hX2⟩ := dampedField_square hv
  have eg := hP.1 g hv.measurable_derivative hv.periodic_derivative hv.derivative_finite
  have eG := hP.2.1 G hv.measurable_gradient hv.periodic_gradient hv.gradient_finite
  have eX := hP.1 (dampedField v) hXm hXp hX2
  have hmode : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt ι y * cnormSq (modeVel ι v σ y))) ≤
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
    have hpt : ∀ᵐ z ∂slab, ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt ι z.2 *
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
      exact real_bound ha hb hc (sq_nonneg ‖z.2‖) hK0 (hwt0 ι z.2) (hB ι z.2).1 (hB ι z.2).2 h1' hz2
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
  have hV := dampedField_periodLIntegral_le v
  have hbc : boundConstant P B = 2 * C := by
    rw [hC, hK]
    unfold boundConstant
    ring
  calc _ ≤ ∑' ι : ℤ × ℤ, ENNReal.ofReal C *
        ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι g σ y)))
          + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)))
          + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (dampedField v) σ y))) :=
        ENNReal.tsum_le_tsum hmode
    _ = ENNReal.ofReal C * (periodLIntegral (fun σ y => ‖g σ y‖ ^ 2)
          + periodLIntegral (fun σ y => matSq (G σ y))
          + periodLIntegral (fun σ y => ‖dampedField v σ y‖ ^ 2)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ← eg, ← eG, ← eX]
    _ ≤ ENNReal.ofReal C * (2 * fieldSize v G g) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        unfold fieldSize
        rw [mul_add, mul_add]
        refine add_le_add (add_le_add ?_ ?_) hV
        · exact le_mul_of_one_le_left zero_le one_le_two
        · exact le_mul_of_one_le_left zero_le one_le_two
    _ = _ := by
        rw [hbc, ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
        ring

theorem weightedFrequencySq_sub_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {u v : ℝ → Space → Space}
    {Gu G : ℝ → Space → (Space →L[ℝ] Space)} {Hu H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {gu g : ℝ → Space → Space} (hu : IsPerturbation Γ₁ P u Gu Hu gu) (hv : IsPerturbation Γ₂ P v G H g)
    (hP0 : 0 < P) (wt : ℤ × ℤ → Space → ℝ)
    (hwt0 : ∀ ι y, 0 ≤ wt ι y) {B : ℝ} (hB : ∀ ι y, wt ι y ≤ B ∧ ‖y‖ ^ 2 * wt ι y ≤ B) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) * wt ι y
        * cnormSq (modeVel ι (fun σ y => u σ y - v σ y) σ y)) ≤
      ENNReal.ofReal (boundConstant P B) * fieldSize (fun σ y => u σ y - v σ y)
        (fun σ y => Gu σ y - G σ y) (fun σ y => gu σ y - g σ y) :=
  weightedFrequencySq_le hP hD hR (isPerturbation_sub hu hv) hP0 wt hwt0 hB

theorem frequencySeminormSq_le {C : Type} (m : ModeWeights C) (hP : ModeSquareSumHolds)
    (hD : ModeDerivativeHolds) (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B R : ℝ}
    (hmu : ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B) (hrate : ∀ c y, |m.rate c y| ≤ R) :
    m.frequencySeminormSq P v ≤
      ENNReal.ofReal (boundConstant P ((2 * Real.pi / P + R) * B)) * fieldSize v G g := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hrate (m.classOf 0) 0)
  have hpi : 0 < 2 * Real.pi / P := by positivity
  have hA0 : 0 ≤ 2 * Real.pi / P + R := by linarith
  refine le_trans ?_ (weightedFrequencySq_le hP hD hR hv hP0
    (fun ι y => (2 * Real.pi / P + R) * m.mu ι y) (fun ι y => mul_nonneg hA0 (abs_nonneg _))
    (fun ι y => ⟨mul_le_mul_of_nonneg_left (hmu _ y).1 hA0, ?_⟩))
  · unfold ModeWeights.frequencySeminormSq
    refine ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => ?_
    apply ENNReal.ofReal_le_ofReal
    have hdop : |m.dop P ι y| ≤ (2 * Real.pi / P + R) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) :=
      abs_freq_le hP0 (hrate (m.classOf ι) y) ι
    have hc := cnormSq_nonneg (modeVel ι v σ y)
    have hmu0 : 0 ≤ m.mu ι y := abs_nonneg _
    calc m.mu ι y * |m.dop P ι y| * cnormSq (modeVel ι v σ y) ≤
        m.mu ι y * ((2 * Real.pi / P + R) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2)) * cnormSq (modeVel ι v σ y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdop hmu0) hc
      _ = _ := by ring
  · rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hmu _ y).2 hA0

theorem pieceSeminormSq_le {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (hP : ModeSquareSumHolds)
    (hD : ModeDerivativeHolds) (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B : ℝ}
    (hwt0 : ∀ β y, 0 ≤ (m.muP β).wt y) (hdec : ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B) :
    m.seminormSq P v ≤
      ENNReal.ofReal (∑ β : Fin nM, boundConstant P ((2 * Real.pi / P + |(m.muP β).frame|) * B))
        * fieldSize v G g := by
  unfold PieceWeights.seminormSq
  rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => ?_), Finset.sum_mul]
  · refine Finset.sum_le_sum fun β _ => ?_
    have hpi : 0 < 2 * Real.pi / P := by positivity
    have hA0 : 0 ≤ 2 * Real.pi / P + |(m.muP β).frame| := by positivity
    refine le_trans ?_ (weightedFrequencySq_le hP hD hR hv hP0
      (fun _ y => (2 * Real.pi / P + |(m.muP β).frame|) * (m.muP β).wt y)
      (fun _ y => mul_nonneg hA0 (hwt0 β y))
      (fun _ y => ⟨mul_le_mul_of_nonneg_left (hdec β y).1 hA0, ?_⟩))
    · refine ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => ?_
      apply ENNReal.ofReal_le_ofReal
      have hs : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
        unfold PieceWeights.sgn
        split_ifs <;> simp
      have hf : |PieceWeights.frameFreq P (m.muP β).frame ι| ≤
          (2 * Real.pi / P + |(m.muP β).frame|) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2) := by
        have h := abs_freq_le hP0 (le_refl |(m.muP β).frame|) ι
        unfold PieceWeights.frameFreq
        rw [mul_comm ((m.muP β).frame)]
        exact h
      have hc := cnormSq_nonneg (modeVel ι v σ y)
      have hw := hwt0 β y
      have h1 : |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι| ≤
          1 * ((2 * Real.pi / P + |(m.muP β).frame|) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2)) :=
        mul_le_mul hs hf (abs_nonneg _) zero_le_one
      calc _ ≤ 1 * ((2 * Real.pi / P + |(m.muP β).frame|) * ((ι.1 : ℝ) ^ 2 + (ι.2 : ℝ) ^ 2))
            * (m.muP β).wt y * cnormSq (modeVel ι v σ y) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hw) hc
        _ = _ := by ring
    · rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hdec β y).2 hA0
  · have hB0 : 0 ≤ B := (hwt0 β 0).trans (hdec β 0).1
    unfold boundConstant
    positivity

theorem frequencySeminormSq_tendsto {C : Type} (m : ModeWeights C) (hP : ModeSquareSumHolds)
    (hD : ModeDerivativeHolds) (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B R : ℝ}
    (hmu : ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B) (hrate : ∀ c y, |m.rate c y| ≤ R)
    (hmuM : ∀ c, Measurable (m.muW c)) (hrateM : ∀ c, Measurable (m.rate c))
    {Γs : ℕ → Set Symmetry} {u : ℕ → ℝ → Space → Space} {Gu : ℕ → ℝ → Space → (Space →L[ℝ] Space)}
    {Hu : ℕ → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gu : ℕ → ℝ → Space → Space}
    (hu : ∀ n, IsPerturbation (Γs n) P (u n) (Gu n) (Hu n) (gu n))
    (hlim : Tendsto (fun n => fieldSize (fun σ y => u n σ y - v σ y) (fun σ y => Gu n σ y - G σ y)
      (fun σ y => gu n σ y - g σ y)) atTop (nhds 0)) :
    Tendsto (fun n => m.frequencySeminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) ∧
      Tendsto (fun n => (m.frequencySeminormSq P (u n)).toReal) atTop
        (nhds (m.frequencySeminormSq P v).toReal) := by
  have hbd : ∀ {x : ℝ → Space → Space} {Gx : ℝ → Space → (Space →L[ℝ] Space)}
      {Hx : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gx : ℝ → Space → Space} {Γx : Set Symmetry},
      IsPerturbation Γx P x Gx Hx gx → m.frequencySeminormSq P x ≠ ⊤ := fun hx =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fieldSize_lt_top hx).ne)
      (frequencySeminormSq_le m hP hD hR hx hP0 hmu hrate)
  have hlim0 : Tendsto (fun n => m.frequencySeminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) :=
    tendsto_zero_of_le ENNReal.ofReal_ne_top
      (fun n => frequencySeminormSq_le m hP hD hR (isPerturbation_sub (hu n) hv) hP0 hmu hrate) hlim
  refine ⟨hlim0, ?_⟩
  have hM : ∀ ι, Measurable (fun y => m.mu ι y * |m.dop P ι y|) := fun ι =>
    (continuous_abs.measurable.comp (hmuM _)).mul (continuous_abs.measurable.comp
      (measurable_const.add (measurable_const.mul (hrateM _))))
  have hW0 : ∀ ι y, 0 ≤ m.mu ι y * |m.dop P ι y| := fun ι y => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact tendsto_toReal_of_split (N := fun x => m.frequencySeminormSq P x) (hbd hv) (fun n => hbd (hu n))
    (fun n => hbd (isPerturbation_sub (hu n) hv)) hlim0
    (fun n t ht => modeSum_split hP (hu n) hv (fun ι y => m.mu ι y * |m.dop P ι y|) hW0 hM ht)

theorem pieceSeminormSq_tendsto {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds) (hR : ModeRotationHolds) {Γ : Set Symmetry}
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B : ℝ}
    (hwt0 : ∀ β y, 0 ≤ (m.muP β).wt y) (hdec : ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B)
    (hwtM : ∀ β, Measurable (m.muP β).wt)
    {Γs : ℕ → Set Symmetry} {u : ℕ → ℝ → Space → Space} {Gu : ℕ → ℝ → Space → (Space →L[ℝ] Space)}
    {Hu : ℕ → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gu : ℕ → ℝ → Space → Space}
    (hu : ∀ n, IsPerturbation (Γs n) P (u n) (Gu n) (Hu n) (gu n))
    (hlim : Tendsto (fun n => fieldSize (fun σ y => u n σ y - v σ y) (fun σ y => Gu n σ y - G σ y)
      (fun σ y => gu n σ y - g σ y)) atTop (nhds 0)) :
    Tendsto (fun n => m.seminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) ∧
      Tendsto (fun n => (m.seminormSq P (u n)).toReal) atTop (nhds (m.seminormSq P v).toReal) := by
  have hbd : ∀ {x : ℝ → Space → Space} {Gx : ℝ → Space → (Space →L[ℝ] Space)}
      {Hx : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gx : ℝ → Space → Space} {Γx : Set Symmetry},
      IsPerturbation Γx P x Gx Hx gx → m.seminormSq P x ≠ ⊤ := fun hx =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fieldSize_lt_top hx).ne)
      (pieceSeminormSq_le m hP hD hR hx hP0 hwt0 hdec)
  have hlim0 : Tendsto (fun n => m.seminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) :=
    tendsto_zero_of_le ENNReal.ofReal_ne_top
      (fun n => pieceSeminormSq_le m hP hD hR (isPerturbation_sub (hu n) hv) hP0 hwt0 hdec) hlim
  refine ⟨hlim0, ?_⟩
  set wtβ : Fin nM → ℤ × ℤ → Space → ℝ := fun β ι y =>
    |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y
    with hwtβ
  have hM : ∀ β ι, Measurable (wtβ β ι) := fun β ι => measurable_const.mul (hwtM β)
  have hW0 : ∀ β ι y, 0 ≤ wtβ β ι y := fun β ι y =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hwt0 β y)
  have hsem : ∀ x, m.seminormSq P x = ∑ β : Fin nM, modeSum (wtβ β) x := fun x => rfl
  refine tendsto_toReal_of_split (N := fun x => m.seminormSq P x) (hbd hv) (fun n => hbd (hu n))
    (fun n => hbd (isPerturbation_sub (hu n) hv)) hlim0 (fun n t ht => ?_)
  have hs := fun β => modeSum_split hP (hu n) hv (wtβ β) (hW0 β) (hM β) ht
  simp only [hsem]
  constructor
  · refine (Finset.sum_le_sum fun β _ => (hs β).1).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  · refine (Finset.sum_le_sum fun β _ => (hs β).2).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem fieldSize_tendsto_of_approximation {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space} (hA : IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => fieldSize (fun σ y => u n σ y - v σ y) (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => transportPart P (u n) σ y - g σ y)) atTop (nhds 0) := by
  unfold fieldSize
  have h := (hA.2.2.2.2.add hA.2.1).add hA.2.2.2.1
  simp only [add_zero] at h
  exact h

theorem frequencySeminormSq_tendsto_of_approximation {C : Type} (m : ModeWeights C)
    (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds) (hR : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B R : ℝ}
    (hmu : ∀ c y, |m.muW c y| ≤ B ∧ ‖y‖ ^ 2 * |m.muW c y| ≤ B) (hrate : ∀ c y, |m.rate c y| ≤ R)
    (hmuM : ∀ c, Measurable (m.muW c)) (hrateM : ∀ c, Measurable (m.rate c))
    {u : ℕ → ℝ → Space → Space} (hA : IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => m.frequencySeminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) ∧
      Tendsto (fun n => (m.frequencySeminormSq P (u n)).toReal) atTop
        (nhds (m.frequencySeminormSq P v).toReal) :=
  frequencySeminormSq_tendsto m hP hD hR hv hP0 hmu hrate hmuM hrateM (fun n => hSP P (u n) (hA.1 n))
    (fieldSize_tendsto_of_approximation hA)

theorem pieceSeminormSq_tendsto_of_approximation {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds) (hR : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) {B : ℝ}
    (hwt0 : ∀ β y, 0 ≤ (m.muP β).wt y) (hdec : ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B)
    (hwtM : ∀ β, Measurable (m.muP β).wt)
    {u : ℕ → ℝ → Space → Space} (hA : IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => m.seminormSq P (fun σ y => u n σ y - v σ y)) atTop (nhds 0) ∧
      Tendsto (fun n => (m.seminormSq P (u n)).toReal) atTop (nhds (m.seminormSq P v).toReal) :=
  pieceSeminormSq_tendsto m hP hD hR hv hP0 hwt0 hdec hwtM (fun n => hSP P (u n) (hA.1 n))
    (fieldSize_tendsto_of_approximation hA)

end FrequencyBound

end Coercive

end Breakdown

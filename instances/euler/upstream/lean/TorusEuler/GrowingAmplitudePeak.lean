import TorusEuler.AmplificationCrossing
import TorusEuler.GrowingAmplitudeBudget

/-! The peak normalization and crossing strength in Proposition 2.6 of the
frozen torus paper, using its growing reference amplitude of Lemma 2.5. -/

open Set

namespace TorusEuler.ReferenceAmplitude

open ReferenceRiccati ReferencePropagator
open AmplificationCrossing MovingAmplitude MovingWaveVector

/-- A positive amplitude satisfying (2.9) lies between the two exponential
multiples of the growing reference amplitude. -/
theorem reference_comparison_of_growing_log_bound {A Y : ℝ → ℝ} {ε t : ℝ}
    (hA : 0 < A t) (hlog : |Real.log (A t / growingFactor Y t)| ≤ ε) :
    Real.exp (-ε) * referenceV Y t ≤ A t ∧ A t ≤ Real.exp ε * referenceV Y t := by
  have hg := referenceV_pos Y t
  change |Real.log (A t / referenceV Y t)| ≤ ε at hlog
  have hratio := div_pos hA hg
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  exact ⟨(le_div_iff₀ hg).mp ((Real.le_log_iff_exp_le hratio).mp hl),
    (div_le_iff₀ hg).mp ((Real.log_le_iff_le_exp hratio).mp hu)⟩

/-- The wave-vector estimates of Lemma 2.3 bound the wave number, divided
by its initial scale, by constant multiples of the late clock. -/
theorem wave_norm_comparable_to_late_clock {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {ε t scale S : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (ht : 2 / ε ≤ t)
    (he : Orthonormal ℝ (e t)) (hscale : 0 < scale) (hS : 1 ≤ S)
    (hX : |X e k scale t - x ε t| ≤ 1 / 2)
    (hQ : |Q e k scale S t + ε * t| ≤ 1 / 2)
    (hZ : |Z e k scale t - 1| ≤ 1 / 2) :
    x ε t / 2 ≤ ‖k t‖ / scale ∧ ‖k t‖ / scale ≤ 3 * x ε t := by
  let X₁ := X e k scale t
  let Q₁ := Q e k scale S t
  let Z₁ := Z e k scale t
  let x₁ := x ε t
  have ht₂ : 2 ≤ t := (show (2 : ℝ) ≤ 2 / ε by
    apply (le_div_iff₀ hε).mpr
    linarith).trans ht
  have hεt : 2 ≤ ε * t := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp ht
  have htx : t ≤ x₁ := by
    unfold x₁ x
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr hεt)]
  have hεtx : ε * t ≤ x₁ := by
    unfold x₁ x
    nlinarith [mul_nonneg (show 0 ≤ ε * t by positivity) (sub_nonneg.mpr ht₂)]
  have hx : 1 ≤ x₁ := by linarith
  change |X₁ - x₁| ≤ 1 / 2 at hX
  change |Q₁ + ε * t| ≤ 1 / 2 at hQ
  change |Z₁ - 1| ≤ 1 / 2 at hZ
  obtain ⟨hXlo, hXhi⟩ := abs_le.mp hX
  obtain ⟨hQlo, hQhi⟩ := abs_le.mp hQ
  obtain ⟨hZlo, hZhi⟩ := abs_le.mp hZ
  have hXS : |X₁| ≤ (3 / 2) * x₁ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hQS : |Q₁| ≤ (3 / 2) * x₁ :=
    abs_le.mpr ⟨by linarith, by linarith [show 0 ≤ ε * t by positivity]⟩
  have hZS : |Z₁| ≤ (3 / 2) * x₁ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hQdiv : |Q₁ / S| ≤ (3 / 2) * x₁ := by
    rw [abs_div, abs_of_pos hSpos]
    exact (div_le_self (abs_nonneg Q₁) hS).trans hQS
  have hsq : (‖k t‖ / scale) ^ 2 = X₁ ^ 2 + (Q₁ / S) ^ 2 + Z₁ ^ 2 := by
    rw [div_pow, wave_norm_sq_eq he hscale.ne' hSpos.ne', mul_div_cancel_left₀ _ (pow_ne_zero _ hscale.ne')]
    rw [normFactor, div_pow]
  have hXlower : (x₁ / 2) ^ 2 ≤ X₁ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hXsq := pow_le_pow_left₀ (abs_nonneg _) hXS 2
  have hQsq := pow_le_pow_left₀ (abs_nonneg _) hQdiv 2
  have hZsq := pow_le_pow_left₀ (abs_nonneg _) hZS 2
  rw [sq_abs] at hXsq hQsq hZsq
  exact ⟨le_of_sq_le_sq (by nlinarith [sq_nonneg (Q₁ / S), sq_nonneg Z₁])
      (div_nonneg (norm_nonneg _) hscale.le),
    le_of_sq_le_sq (by nlinarith) (by linarith)⟩

private theorem sqrt_clock_bounds_at_crossing {ε next t : ℝ} (hε : 0 < ε) (hn : 0 < next)
    (hlo : 1 / (4 * next) ≤ x ε t) (hhi : x ε t ≤ 3 / (2 * next)) :
    (Real.sqrt (ε * next))⁻¹ / 2 ≤ Real.sqrt (x ε t / ε) ∧
      Real.sqrt (x ε t / ε) ≤ 2 * (Real.sqrt (ε * next))⁻¹ := by
  have hp := mul_pos hε hn
  have hx := x_nonneg hε.le t
  have hd : 0 ≤ x ε t / ε := div_nonneg hx hε.le
  have hlo' : (ε * next * 4)⁻¹ ≤ x ε t / ε := by
    apply (le_div_iff₀ hε).mpr
    calc
      _ = 1 / (4 * next) := by field_simp
      _ ≤ _ := hlo
  have hhi' : x ε t / ε ≤ 4 / (ε * next) := by
    apply (div_le_iff₀ hε).mpr
    calc
      _ ≤ 3 / (2 * next) := hhi
      _ ≤ (4 / (ε * next)) * ε := by
        have h := (show (3 : ℝ) / 2 ≤ 4 by norm_num)
        calc
          _ = (3 / 2) / next := by ring
          _ ≤ 4 / next := div_le_div_of_nonneg_right h hn.le
          _ = _ := by field_simp
  constructor
  · apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hd]
    refine le_trans ?_ hlo'
    rw [div_pow, inv_pow, Real.sq_sqrt hp.le]
    exact le_of_eq (by ring)
  · apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt hd, mul_pow, inv_pow, Real.sq_sqrt hp.le]
    simpa [div_eq_mul_inv, show (2 : ℝ) ^ 2 = 4 by norm_num] using hhi'

/-- Proposition 2.6 follows from the amplitude bound (2.9), the late part of
(2.10), and the wave-vector comparison in Lemma 2.3. The maximum here is the
maximum of the physical amplitude on the whole closed interval. -/
theorem growing_amplitude_crossing_strength_and_gain
    {ε next T scale S : ℝ} {Y ρ : ℝ → ℝ} {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    (hε : 0 < ε) (hεsmall : 2 * ε ≤ 1) (hn : 0 < next) (hnsmall : next ≤ ε / 32)
    (hT : crossingHorizon ε next ≤ T) (hscale : 0 < scale) (hS : 1 ≤ S)
    (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Ici 0, HasDerivWithinAt Y (rhs ε r (Y r)) (Ici 0) r)
    (ha : ContinuousOn a (Icc 0 T)) (ha₀ : ∀ r ∈ Icc 0 T, a r ≠ 0)
    (hlog : ∀ r ∈ Icc 0 T, |Real.log (‖a r‖ / growingFactor Y r)| ≤ ε)
    (he : ∀ r ∈ Icc (2 / ε) T, Orthonormal ℝ (e r))
    (hX : ∀ r ∈ Icc (2 / ε) T, |X e k scale r - x ε r| ≤ 1 / 2)
    (hQ : ∀ r ∈ Icc (2 / ε) T, |Q e k scale S r + ε * r| ≤ 1 / 2)
    (hZ : ∀ r ∈ Icc (2 / ε) T, |Z e k scale r - 1| ≤ 1 / 2)
    (hρ : ContinuousOn ρ (Icc 0 T))
    (hcomp : ∀ r ∈ Icc (Real.sqrt 2 / ε) T, s ε r / 2 ≤ ρ r ∧ ρ r ≤ 3 / 2 * s ε r) :
    ∃ τm ∈ Icc (2 / ε) (3 / ε), Y τm = 0 ∧
      ∃ peak : ℝ, IsGreatest ((fun r => ‖a r‖) '' Icc 0 T) peak ∧
        (Real.exp (-ε) * growingFactor Y τm ≤ peak ∧
          peak ≤ Real.exp ε * growingFactor Y τm) ∧
        (∃ τ ∈ Ioo τm (crossingHorizon ε next), ρ τ = next) ∧
        (∀ τ ∈ Icc τm (crossingHorizon ε next), ρ τ = next →
          (Real.exp (-1) / 4) * (Real.sqrt (ε * next))⁻¹ ≤
            ‖a τ‖ * ‖k τ‖ / (scale * peak) ∧
          ‖a τ‖ * ‖k τ‖ / (scale * peak) ≤
            18 * Real.exp 3 * (Real.sqrt (ε * next))⁻¹) ∧
        (∀ τ ∈ Icc 0 1, ‖a τ‖ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * peak) := by
  have hε₁ : ε ≤ 1 := by linarith
  have hYc := HasDerivWithinAt.continuousOn hY
  have hform := (referenceY_deviation ε Y).symm
  have hdev := riccati_deviation_bounds_Ici hε hY₀ hY
  obtain ⟨τm, hm, hzero, hpos, hneg⟩ := riccati_turning_time hε hε₁ hY hform hdev
  have hmh : τm ≤ crossingHorizon ε next := (hm.2.trans
    (div_le_div_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 8) hε.le)).trans
      (eight_div_le_crossingHorizon hε hn hnsmall)
  have htm : τm ∈ Icc 0 T :=
    ⟨(by positivity : 0 ≤ 2 / ε).trans hm.1, hmh.trans hT⟩
  have hbefore (r : ℝ) (hr : r ∈ Icc 0 τm) : 0 ≤ Y r := by
    rcases hr.2.lt_or_eq with hlt | rfl
    · exact (hpos r ⟨hr.1, hlt⟩).le
    · rw [hzero]
  have hafter (r : ℝ) (hr : r ∈ Ici τm) : Y r ≤ 0 := by
    rcases (mem_Ici.mp hr).lt_or_eq with hlt | heq
    · exact (hneg r hlt).le
    · rw [← heq, hzero]
  have hpeak := referenceV_le_at_turning_time htm.1 hYc hbefore hafter
  have hgain := riccati_gain_bound hε hε₁ hm.1 hform hdev hYc hbefore
  have hcap (r : ℝ) (hr : r ∈ Ici 0) : Y r ≤ 1 :=
    (abs_le.mp (riccati_abs_le_one hε hε₁ hY₀ hY r hr)).2
  let A (r : ℝ) := ‖a r‖
  have hcompare (r : ℝ) (hr : r ∈ Icc 0 T) :
      Real.exp (-ε) * referenceV Y r ≤ A r ∧ A r ≤ Real.exp ε * referenceV Y r :=
    reference_comparison_of_growing_log_bound (norm_pos_iff.mpr (ha₀ r hr)) (hlog r hr)
  obtain ⟨τa, hta, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨τm, htm⟩ ha.norm
  let peak := A τa
  have hgreat : IsGreatest (A '' Icc 0 T) peak := by
    refine ⟨mem_image_of_mem A hta, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact isMaxOn_iff.mp hmax r hr
  have hpeaklo : Real.exp (-ε) * referenceV Y τm ≤ peak :=
    (hcompare τm htm).1.trans (hgreat.2 (mem_image_of_mem A htm))
  have hpeakhi : peak ≤ Real.exp ε * referenceV Y τm :=
    (hcompare τa hta).2.trans (mul_le_mul_of_nonneg_left (hpeak τa hta.1) (by positivity))
  obtain ⟨hcross, hcrossBounds⟩ :=
    exists_crossing_of_couplingRatio hε hε₁ hn hnsmall hm hT
      (hρ.mono (Icc_subset_Icc_left htm.1)) hcomp
  refine ⟨τm, hm, hzero, peak, hgreat, ⟨hpeaklo, hpeakhi⟩, hcross, ?_, ?_⟩
  · intro τ hτ hρτ
    have hτT : τ ≤ T := hτ.2.trans hT
    have hlate : τ ∈ Icc (2 / ε) T := ⟨hm.1.trans hτ.1, hτT⟩
    obtain ⟨hlo, hhi⟩ := hcrossBounds τ ⟨hτ.1, hτT⟩ hρτ
    obtain ⟨hclocklo, hclockhi⟩ := sqrt_clock_bounds_at_crossing hε hn hlo hhi
    obtain ⟨hklo, hkhi⟩ := wave_norm_comparable_to_late_clock hε hε₁ hlate.1
      (he τ hlate) hscale hS (hX τ hlate) (hQ τ hlate) (hZ τ hlate)
    rw [show x ε τ / 2 = (1 / 2) * x ε τ by ring] at hklo
    obtain ⟨hslo, hshi⟩ := amplitude_late_strength_bounds_of_reference_comparison
      hε hε₁ hm hτ.1 hτT hform hYc hdev (Real.exp_pos _) (Real.exp_pos _)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (3 : ℝ))
      (fun r hr => hpeak r hr.1) hcompare hgreat hklo hkhi
    have hloexp : Real.exp (-1) ≤ Real.exp (-ε) / Real.exp ε := by
      rw [← Real.exp_sub]
      exact Real.exp_le_exp.mpr (by linarith)
    have hhiexp : Real.exp ε / Real.exp (-ε) ≤ Real.exp 1 := by
      rw [← Real.exp_sub]
      exact Real.exp_le_exp.mpr (by linarith)
    have hstrength :
        (‖k τ‖ / scale) * (A τ / peak) = ‖a τ‖ * ‖k τ‖ / (scale * peak) := by
      rw [div_mul_div_comm, mul_comm ‖k τ‖]
    rw [hstrength] at hslo hshi
    constructor
    · calc
        _ = (1 / 2) * Real.exp (-1) * ((Real.sqrt (ε * next))⁻¹ / 2) := by ring
        _ ≤ (1 / 2) * (Real.exp (-ε) / Real.exp ε) * Real.sqrt (x ε τ / ε) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hloexp (by norm_num)) hclocklo
            (by positivity) (by positivity)
        _ ≤ _ := hslo
    · calc
        _ ≤ 3 * (Real.exp ε / Real.exp (-ε)) * (3 * Real.exp 2) *
            Real.sqrt (x ε τ / ε) := hshi
        _ ≤ 3 * Real.exp 1 * (3 * Real.exp 2) * (2 * (Real.sqrt (ε * next))⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hhiexp (by norm_num)) (by positivity)) hclockhi
            (by positivity) (by positivity)
        _ = _ := by
          rw [show Real.exp (3 : ℝ) = Real.exp 1 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
          ring
  · intro τ hτ
    have hT₁ : 1 ≤ T :=
      ((le_div_iff₀ hε).mpr (by linarith : 1 * ε ≤ 8)).trans <|
        (eight_div_le_crossingHorizon hε hn hnsmall).trans hT
    exact (amplitude_initial_window_of_reference_comparison hεsmall hYc hcap hgain hτ
      (hτ.2.trans hT₁) htm hcompare).trans
      (mul_le_mul_of_nonneg_left (hgreat.2 (mem_image_of_mem A htm)) (by positivity))

end TorusEuler.ReferenceAmplitude

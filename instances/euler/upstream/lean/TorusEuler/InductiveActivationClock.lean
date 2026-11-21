import TorusEuler.InductionScales
import TorusEuler.PhysicalAmplificationCrossing
import TorusEuler.TerminalVorticityTransfer

/-! The physical activation clock of Theorem 7.1 and the interval weight
in the direct curl-integral argument of Corollary 8.3. -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TorusEuler

open AmplificationCrossing (crossingHorizon)
open MovingWaveVector (amplificationGrowthRate amplificationGrowthRate_sq)

/-- The strength bounds at the preceding crossing and the cumulative first
coupling bound give both normalized rates in item 2 of Theorem 7.1. -/
theorem activationGrowthRate_bounds {μ L σ ν c C : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hc : 0 < c) (hC : 0 < C)
    (hσlo : c * μ ^ (1 / 4 : ℝ) ≤ σ) (hσhi : σ ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2)
    (hνlo : Real.pi ≤ ν) (hνhi : ν ≤ 4 * Real.pi) :
    Real.sqrt (2 * c * Real.pi) * μ ^ (1 / 8 : ℝ) ≤ amplificationGrowthRate σ ν ∧
      amplificationGrowthRate σ ν ≤ Real.sqrt (8 * C * Real.pi) * μ ^ (1 / 8 : ℝ) * L := by
  have hσ := (mul_pos hc (Real.rpow_pos_of_pos hμ _)).trans_le hσlo
  have hν := Real.pi_pos.trans_le hνlo
  have hp : (μ ^ (1 / 8 : ℝ)) ^ 2 = μ ^ (1 / 4 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hμ]
    norm_num
  have hlo : 2 * c * Real.pi * μ ^ (1 / 4 : ℝ) ≤ 2 * σ * ν := by
    calc
      _ = 2 * ((c * μ ^ (1 / 4 : ℝ)) * Real.pi) := by ring
      _ ≤ 2 * (σ * ν) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hσlo hνlo Real.pi_pos.le hσ.le) (by norm_num)
      _ = _ := by ring
  have hhi : 2 * σ * ν ≤ (8 * C * Real.pi) * μ ^ (1 / 4 : ℝ) * L ^ 2 := by
    calc
      _ = 2 * (σ * ν) := by ring
      _ ≤ 2 * ((C * μ ^ (1 / 4 : ℝ) * L ^ 2) * (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hσhi hνhi hν.le
          (by positivity [Real.rpow_pos_of_pos hμ (1 / 4 : ℝ)])) (by norm_num)
      _ = _ := by ring
  have hrnonneg : 0 ≤ amplificationGrowthRate σ ν := Real.sqrt_nonneg _
  constructor
  · apply le_of_sq_le_sq _ hrnonneg
    rw [mul_pow, Real.sq_sqrt (by positivity), hp, amplificationGrowthRate_sq hσ hν]
    exact hlo
  · apply le_of_sq_le_sq _ (by positivity [Real.rpow_pos_of_pos hμ (1 / 8 : ℝ)])
    rw [amplificationGrowthRate_sq hσ hν, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hp]
    exact hhi

/-- The normalized right crossing bracket is the product of the two
successive logarithmic gains, multiplied by two. -/
theorem crossingHorizon_eq_of_gains {L LNext : ℝ} (hL : 0 < L) (hstep : 640 * L ≤ LNext) :
    crossingHorizon (couplingRatioOfGain L) (couplingRatioOfGain LNext) = 2 * (L * LNext) := by
  have hprod : 0 ≤ couplingRatioOfGain L * couplingRatioOfGain LNext := by
    unfold couplingRatioOfGain
    positivity
  rw [crossingHorizon, div_eq_mul_inv, ← (couplingRatioOfGain_step hL hstep).2.2.1,
    show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hprod, ← Real.sqrt_eq_rpow]

/-- The normalized crossing lower bound and the growth-rate upper bound
give the weight of one activation interval in the curl integral. -/
theorem activation_interval_weight_lower {μ L C r start stop : ℝ}
    (hL : 0 < L) (hC : 0 < C) (hr : 0 < r)
    (hclock : 2 * L ^ 2 ≤ r * (stop - start))
    (hrupper : r ≤ C * μ ^ (1 / 8 : ℝ) * L) :
    start < stop ∧ (2 / C) * L ≤ μ ^ (1 / 8 : ℝ) * (stop - start) := by
  have hpositive : 0 < r * (stop - start) :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos hL 2)).trans_le hclock
  have hd : 0 < stop - start := pos_of_mul_pos_right hpositive hr.le
  refine ⟨sub_pos.mp hd, ?_⟩
  have h := hclock.trans (mul_le_mul_of_nonneg_right hrupper hd.le)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).2
  apply (mul_le_mul_iff_left₀ hL).mp
  calc
    (2 * L) * L = 2 * L ^ 2 := by ring
    _ ≤ _ := h.trans_eq (by ring)

namespace MovingWaveVector.PhysicalAmplification

variable {I : Set ℝ} {t₀ T scale Ustar : ℝ} (w : PhysicalAmplification I t₀)

/-- Any crossing in the physical bracket occurs after the lower
normalized clock bound. -/
theorem GrowingCrossing.normalized_delay_lower_of_gains {L next : ℝ}
    (d : w.GrowingCrossing T scale Ustar next) (hratio : w.ratio = couplingRatioOfGain L) :
    2 * L ^ 2 ≤ w.rate * (d.crossing - t₀) := by
  have hl : d.referenceTurn / w.rate ≤ d.crossing - t₀ := by
    have h := d.crossing_in_bracket.1
    unfold clock at h
    linarith only [h]
  have hlow : 2 / w.ratio ≤ (d.crossing - t₀) * w.rate :=
    d.turning_bounds.1.trans ((div_le_iff₀ w.rate_pos).mp hl)
  rwa [hratio, couplingRatioOfGain, div_inv_eq_mul, mul_comm (d.crossing - t₀)] at hlow

/-- The physical crossing inherits the exact lower clock from the reference
turning time and the exact upper clock from the crossing bracket. -/
theorem GrowingCrossing.normalized_delay_bounds_of_gains {L LNext : ℝ}
    (d : w.GrowingCrossing T scale Ustar (couplingRatioOfGain LNext))
    (hL : 0 < L) (hstep : 640 * L ≤ LNext)
    (hratio : w.ratio = couplingRatioOfGain L) :
    2 * L ^ 2 ≤ w.rate * (d.crossing - t₀) ∧
      w.rate * (d.crossing - t₀) ≤ 2 * (L * LNext) := by
  have hup : (d.crossing - t₀) * w.rate ≤
      crossingHorizon w.ratio (couplingRatioOfGain LNext) :=
    (le_div_iff₀ w.rate_pos).mp (d.delay_bounds).2
  rw [hratio, crossingHorizon_eq_of_gains hL hstep] at hup
  exact ⟨GrowingCrossing.normalized_delay_lower_of_gains w d hratio, by rwa [mul_comm w.rate]⟩

/-- With the preceding (7.3) strength and cumulative coupling bounds,
the selected physical crossing lies in the first half of the endpoint
interval and has the weight required for the terminal curl integral. -/
theorem GrowingCrossing.inductive_activation_clock {μ L LNext c C : ℝ}
    (d : w.GrowingCrossing T scale Ustar (couplingRatioOfGain LNext))
    (hμ : 0 < μ) (hL : 0 < L) (hstep : 640 * L ≤ LNext)
    (hc : 0 < c) (hC : 0 < C) (hratio : w.ratio = couplingRatioOfGain L)
    (hσlo : c * μ ^ (1 / 4 : ℝ) ≤ w.initialStrength)
    (hσhi : w.initialStrength ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2)
    (hνlo : Real.pi ≤ w.firstCoupling) (hνhi : w.firstCoupling ≤ 4 * Real.pi)
    (hlarge : 2 / Real.sqrt (2 * c * Real.pi) ≤ LNext) :
    let cRate := Real.sqrt (2 * c * Real.pi)
    let CRate := Real.sqrt (8 * C * Real.pi)
    cRate * μ ^ (1 / 8 : ℝ) ≤ w.rate ∧ w.rate ≤ CRate * μ ^ (1 / 8 : ℝ) * L ∧
      t₀ < d.crossing ∧ d.crossing - t₀ ≤ μ ^ (-1 / 8 : ℝ) * LNext ^ 3 ∧
      2 * L ^ 2 ≤ w.rate * (d.crossing - t₀) ∧
      (2 / CRate) * L ≤ μ ^ (1 / 8 : ℝ) * (d.crossing - t₀) := by
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμ hL.le hc hC hσlo hσhi hνlo hνhi
  have hclock := GrowingCrossing.normalized_delay_lower_of_gains w d hratio
  obtain ⟨hadvance, hweight⟩ := activation_interval_weight_lower hL
    (show 0 < Real.sqrt (8 * C * Real.pi) by positivity [Real.pi_pos]) w.rate_pos hclock hrHi
  have hhalf := crossingClock_le_endpointHalfLength hμ
    (show 0 < Real.sqrt (2 * c * Real.pi) by positivity [Real.pi_pos]) hL hstep hrLo hlarge
  have hdelay := d.delay_bounds.2
  rw [hratio, crossingHorizon_eq_of_gains hL hstep] at hdelay
  rw [(couplingRatioOfGain_step hL hstep).2.2.1] at hhalf
  exact ⟨hrLo, hrHi, hadvance, hdelay.trans hhalf, hclock, hweight⟩

end MovingWaveVector.PhysicalAmplification

open MovingWaveVector (PhysicalAmplification)

/-- The actual physical crossings give the time weights needed to integrate
the central curl lower bound. At index `j` the current wave is `j + 2`,
and this integral uses gain `L_{j+2}`. -/
theorem curlIntegral_eq_top_of_inductive_physical_crossings
    {T c B cStrength CStrength : ℝ} {u : Velocity} {activation freq σ ν : ℕ → ℝ}
    (hc : 0 < c) (hcStrength : 0 < cStrength) (hCStrength : 0 < CStrength)
    (hfreq : Tendsto freq atTop atTop) (hmono : Monotone activation)
    (hbefore : ∀ j, activation j < T)
    (hsmooth : ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (u t))
    (hσ : ∀ᶠ j : ℕ in atTop,
      cStrength * freq (j + 1) ^ (1 / 4 : ℝ) ≤ σ j ∧
        σ j ≤ CStrength * freq (j + 1) ^ (1 / 4 : ℝ) *
          (4 * Real.log (freq (j + 3))) ^ 2)
    (hν : ∀ᶠ j : ℕ in atTop, Real.pi ≤ ν j ∧ ν j ≤ 4 * Real.pi)
    (hcrossings : ∀ᶠ j : ℕ in atTop,
      ∃ (I : Set ℝ) (window : ℝ) (w : PhysicalAmplification I (activation (j + 2)))
        (d : w.GrowingCrossing window (freq (j + 2)) (freq (j + 2) ^ (-3 / 4 : ℝ))
          (couplingRatioOfGain (4 * Real.log (freq (j + 4))))),
        d.crossing = activation (j + 3) ∧
        w.initialStrength = σ j ∧ w.firstCoupling = ν j ∧
        w.ratio = couplingRatioOfGain (4 * Real.log (freq (j + 3))))
    (hcurl : ∀ᶠ j : ℕ in atTop, 0 ≤ activation (j + 2) ∧
      ∀ t ∈ Ico (activation (j + 2)) (activation (j + 3)),
        c * freq (j + 1) ^ (1 / 8 : ℝ) - B * freq (j + 1) ^ (1 / 32 : ℝ) - B ≤
          ‖curl (u t) 0‖) :
    (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ := by
  let μ (j : ℕ) := freq (j + 1)
  let L (j : ℕ) := 4 * Real.log (freq (j + 3))
  let t (j : ℕ) := activation (j + 2)
  let r (j : ℕ) := amplificationGrowthRate (σ j) (ν j)
  let CRate := Real.sqrt (8 * CStrength * Real.pi)
  have hshift (s : ℕ) : Tendsto (fun j : ℕ => j + s) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right j s) tendsto_id
  have hμ : Tendsto μ atTop atTop := hfreq.comp (hshift 1)
  have hL : Tendsto L atTop atTop :=
    (Real.tendsto_log_atTop.comp (hfreq.comp (hshift 3))).const_mul_atTop (by norm_num)
  have ht : Monotone t := hmono.comp (fun _ _ h => Nat.add_le_add_right h 2)
  have hCRate : 0 < CRate := by dsimp [CRate]; positivity [Real.pi_pos]
  apply curlIntegral_eq_top_of_activation_bounds_with_errors (r := r) (B := B)
    hc hCRate ht hμ hL hsmooth
  filter_upwards [hσ, hν, hcrossings, hcurl, hμ.eventually_gt_atTop 0, hL.eventually_ge_atTop 0]
    with j hσj hνj hcross hjcurl hjμ hjL
  obtain ⟨I, window, w, d, hcross, hstrength, hfirst, hratio⟩ := hcross
  have hclock :=
    MovingWaveVector.PhysicalAmplification.GrowingCrossing.normalized_delay_lower_of_gains w d hratio
  have hrate : w.rate = r j := by
    unfold MovingWaveVector.PhysicalAmplification.rate r
    rw [hstrength, hfirst]
  rw [hrate, hcross] at hclock
  have hrUpper := (activationGrowthRate_bounds hjμ hjL hcStrength hCStrength
    hσj.1 hσj.2 hνj.1 hνj.2).2
  exact ⟨hjcurl.1, (hbefore (j + 3)).le, hclock, hrUpper, hjcurl.2⟩

end TorusEuler

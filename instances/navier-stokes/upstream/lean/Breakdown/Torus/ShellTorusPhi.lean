import Breakdown.Torus.ShellTorusBase

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ShellTorus.Internal

open TorusSeries.Internal

def shellCoef (s : ℝ) (ψ : V) (k : Lattice) : Coef := (weight k * heatFactor s k : ℝ) • coeff ψ k

theorem exp_mul_bound {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    (1 + y) * Real.exp (-(y * s)) ≤ 1 + 1 / s := by
  have h1 : Real.exp (-(y * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h2 : y * s * Real.exp (-(y * s)) ≤ 1 := by
    have h3 : y * s + 1 ≤ Real.exp (y * s) := Real.add_one_le_exp _
    have h4 : Real.exp (y * s) * Real.exp (-(y * s)) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(y * s))]
  have h5 : y * Real.exp (-(y * s)) ≤ 1 / s := by
    rw [le_div_iff₀ hs]
    nlinarith
  nlinarith

theorem weight_heat_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (k : Lattice) :
    0 ≤ weight k * heatFactor s k ∧ weight k * heatFactor s k ≤ 2 / s := by
  refine ⟨mul_nonneg (Internal.weight_pos k).le (Internal.heatFactor_nonneg s k), ?_⟩
  have h := exp_mul_bound hs (sq_nonneg (2 * π * ‖freq k‖))
  have e : weight k * heatFactor s k = (1 + (2 * π * ‖freq k‖) ^ 2) * Real.exp (-((2 * π * ‖freq k‖) ^ 2 * s)) := by
    rw [weight, heatFactor, max_eq_left hs.le]
    congr 2
    · ring
    · ring
  have h1 : 1 ≤ 1 / s := by rw [le_div_iff₀ hs]; linarith
  rw [e]
  calc _ ≤ 1 + 1 / s := h
    _ ≤ 2 / s := by rw [show (2 : ℝ) / s = 1 / s + 1 / s by ring]; linarith

theorem norm_shellCoef (s : ℝ) (ψ : V) (k : Lattice) :
    ‖shellCoef s ψ k‖ = weight k * heatFactor s k * ‖coeff ψ k‖ := by
  rw [shellCoef, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Internal.weight_pos k).le (Internal.heatFactor_nonneg s k))]

theorem summable_norm_shellCoef {s : ℝ} (hs : 0 < s) (ψ : V) : Summable fun k => ‖shellCoef s ψ k‖ := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (((Internal.summable_weight_heat hs).add hw.summable).mul_left (1 / 2))
  rw [norm_shellCoef]
  have hw0 := (Internal.weight_pos k).le
  have := mul_nonneg hw0 (sq_nonneg (heatFactor s k - ‖coeff ψ k‖))
  nlinarith

theorem sq_norm_shellCoef_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ψ : V) (k : Lattice) :
    ‖shellCoef s ψ k‖ ^ 2 ≤ 2 / s * (weight k * ‖coeff ψ k‖ ^ 2) := by
  rw [norm_shellCoef]
  obtain ⟨h0, h1⟩ := weight_heat_bound hs hs1 k
  have hh := Internal.heatFactor_nonneg s k
  have hh1 : heatFactor s k ≤ 1 := by
    have := abs_heatFactor_le s k
    rw [abs_of_nonneg hh] at this
    exact this
  have hw0 := (Internal.weight_pos k).le
  have e : (weight k * heatFactor s k * ‖coeff ψ k‖) ^ 2 =
      (weight k * heatFactor s k) * heatFactor s k * (weight k * ‖coeff ψ k‖ ^ 2) := by ring
  rw [e]
  have ha := mul_nonneg hw0 (sq_nonneg ‖coeff ψ k‖)
  have h2 : weight k * heatFactor s k * heatFactor s k ≤ 2 / s :=
    (mul_le_of_le_one_right h0 hh1).trans h1
  exact mul_le_mul_of_nonneg_right h2 ha

theorem weight_sq_norm_shellCoef_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ψ : V) (k : Lattice) :
    weight k * ‖shellCoef s ψ k‖ ^ 2 ≤ (2 / s) ^ 2 * (weight k * ‖coeff ψ k‖ ^ 2) := by
  rw [norm_shellCoef]
  obtain ⟨h0, h1⟩ := weight_heat_bound hs hs1 k
  have hw0 := (Internal.weight_pos k).le
  have e : weight k * (weight k * heatFactor s k * ‖coeff ψ k‖) ^ 2 =
      (weight k * heatFactor s k) ^ 2 * (weight k * ‖coeff ψ k‖ ^ 2) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (mul_nonneg hw0 (sq_nonneg _))

def termBounded (c : Lattice → Coef) (k : Lattice) : BoundedContinuousFunction Space Coef :=
  BoundedContinuousFunction.ofNormedAddCommGroup (term c k) (continuous_term c k) ‖c k‖ fun x => by
    rw [term, norm_smul, FreqTrSeries.Internal.norm_character, one_mul]

theorem norm_termBounded_le (c : Lattice → Coef) (k : Lattice) : ‖termBounded c k‖ ≤ ‖c k‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => by
    show ‖term c k x‖ ≤ ‖c k‖
    rw [term, norm_smul, FreqTrSeries.Internal.norm_character, one_mul]

theorem torusSeries_ae_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef) (hc : Summable fun k => ‖c k‖) :
    (torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell] fun x => ∑' k, character (-k) x • c k := by
  have := finite_cell
  have hs : Summable (termBounded c) := Summable.of_norm_bounded hc (norm_termBounded_le c)
  have e : torusSeries p c = BoundedContinuousFunction.toLp p (volume.restrict cell) ℝ (∑' k, termBounded c k) := by
    rw [ContinuousLinearMap.map_tsum _ hs]
    unfold torusSeries
    congr 1
    funext k
    rw [lpOrZero_term]
    refine Lp.ext ((MemLp.coeFn_toLp _).trans ?_)
    exact (BoundedContinuousFunction.coeFn_toLp p (volume.restrict cell) ℝ (termBounded c k)).symm
  rw [e]
  refine (BoundedContinuousFunction.coeFn_toLp p _ ℝ _).trans (ae_of_all _ fun x => ?_)
  show (BoundedContinuousFunction.evalCLM ℝ x) (∑' k, termBounded c k) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  rfl

theorem four_mul_half : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

theorem twelve_mul_half : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6 := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    show (12 : ℝ≥0∞) = 6 * 2 by norm_num, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

instance lpProdFourTwelve : ENNReal.HolderTriple 4 12 3 := by
  constructor
  rw [← ENNReal.toReal_eq_toReal_iff']
  · rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
    norm_num
  · simp
  · simp

theorem eLpNorm_three_le (f : Space → Space) (μ : Measure Space) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 3 μ ≤ eLpNorm f 2 μ ^ (1 / 2 : ℝ) * eLpNorm f 6 μ ^ (1 / 2 : ℝ) := by
  have hg : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 / 2 : ℝ)) μ :=
    (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable hf.norm
  have e1 : eLpNorm f 3 μ = eLpNorm (fun x => ‖f x‖ ^ (1 / 2 : ℝ) * ‖f x‖ ^ (1 / 2 : ℝ)) 3 μ := by
    refine eLpNorm_congr_norm_ae (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 4) (q := 12) (r := 3) hg hg
    (fun a b : ℝ => a * b) 1 (ae_of_all _ fun x => by simp [norm_mul])
  rw [eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 1 / 2), four_mul_half] at h
  rw [eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 1 / 2), twelve_mul_half] at h
  rw [e1]
  simpa using h

theorem eLpNorm_phi_le (p : ℝ≥0∞) [Fact (1 ≤ p)] {s : ℝ} (hs : 0 < s) (ψ : V) :
    eLpNorm (phiField s ψ) p (volume.restrict cell) ≤ ENNReal.ofReal ‖torusSeries p (shellCoef s ψ)‖ := by
  have hae : phiField s ψ =ᵐ[volume.restrict cell]
      fun x => Freq.realVec (torusSeries p (shellCoef s ψ) x) :=
    (torusSeries_ae_eq p _ (summable_norm_shellCoef hs ψ)).mono fun x hx => by
      exact congrArg Freq.realVec hx.symm
  rw [eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  exact eLpNorm_mono fun x => ShellDefs.Internal.norm_realVec_le _

theorem torusSeries_two_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ψ : V) :
    ‖torusSeries 2 (shellCoef s ψ)‖ ^ 2 ≤ 2 / s * ‖ψ‖ ^ 2 := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  have hsum : Summable fun k => ‖shellCoef s ψ k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (sq_norm_shellCoef_le hs hs1 ψ) (hw.summable.mul_left _)
  rw [torusSeries_norm_sq _ hsum, ← hw.tsum_eq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (sq_norm_shellCoef_le hs hs1 ψ) hsum (hw.summable.mul_left _)

theorem torusSeries_six_le (C : ℝ) (hC0 : 0 < C) (hC : ∀ (t : Finset Lattice) (c : Lattice → Coef),
    (∫ x in cell, ‖∑ k ∈ t, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      C * (∑ k ∈ t, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ψ : V) :
    ‖torusSeries 6 (shellCoef s ψ)‖ ≤ C * (2 / s * ‖ψ‖) := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  have hsum : Summable fun k => weight k * ‖shellCoef s ψ k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Internal.weight_pos k).le (sq_nonneg _))
      (weight_sq_norm_shellCoef_le hs hs1 ψ) (hw.summable.mul_left _)
  have h := norm_tsum_le_of_bound _ (summable_six _ hsum) _
    (fun k => mul_nonneg (Internal.weight_pos k).le (sq_nonneg _)) hsum C hC0.le (norm_sum_six_le hC _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
  have h2 : ∑' k, weight k * ‖shellCoef s ψ k‖ ^ 2 ≤ (2 / s * ‖ψ‖) ^ 2 := by
    rw [mul_pow, ← hw.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (weight_sq_norm_shellCoef_le hs hs1 ψ) hsum (hw.summable.mul_left _)
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (by positivity)] at h3

theorem phiField_bound (hTS : TrigHs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ ψ : V,
      MemLp (phiField s ψ) 3 (volume.restrict cell) ∧
        (eLpNorm (phiField s ψ) 3 (volume.restrict cell)).toReal ≤ C * s ^ (-(3 / 4 : ℝ)) * ‖ψ‖ := by
  obtain ⟨C6, hC60, hC6⟩ := hTS
  refine ⟨2 * Real.sqrt C6, by positivity, fun s hs hs1 ψ => ?_⟩
  set a := ‖torusSeries 2 (shellCoef s ψ)‖ with ha_def
  set b := ‖torusSeries 6 (shellCoef s ψ)‖ with hb_def
  have hmeas : AEStronglyMeasurable (phiField s ψ) (volume.restrict cell) := by
    have hae : phiField s ψ =ᵐ[volume.restrict cell]
        fun x => Freq.realVec (torusSeries 2 (shellCoef s ψ) x) :=
      (torusSeries_ae_eq 2 _ (summable_norm_shellCoef hs ψ)).mono fun x hx => by
        exact congrArg Freq.realVec hx.symm
    exact (Freq.realVec.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).congr hae.symm
  have key : eLpNorm (phiField s ψ) 3 (volume.restrict cell) ≤ ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
    calc _ ≤ _ := eLpNorm_three_le _ _ hmeas
      _ ≤ ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal b ^ (1 / 2 : ℝ) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (eLpNorm_phi_le 2 hs ψ) (by norm_num))
            (ENNReal.rpow_le_rpow (eLpNorm_phi_le 6 hs ψ) (by norm_num))
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  refine ⟨⟨hmeas, key.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) key).trans ?_
  set u := s ^ (-(1 / 4 : ℝ)) with hu_def
  have hu : 0 < u := Real.rpow_pos_of_pos hs _
  have hu4 : u ^ 4 = s⁻¹ := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num [Real.rpow_neg_one]
  have hu3 : u ^ 3 = s ^ (-(3 / 4 : ℝ)) := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have h2s : 2 / s = 2 * u ^ 4 := by rw [hu4, div_eq_mul_inv]
  have hψ := norm_nonneg ψ
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha : a ≤ 2 * u ^ 2 * ‖ψ‖ := by
    have h1 : a ^ 2 ≤ (2 * u ^ 2 * ‖ψ‖) ^ 2 := by
      refine (torusSeries_two_le hs hs1 ψ).trans ?_
      rw [h2s]
      nlinarith [sq_nonneg (u ^ 2 * ‖ψ‖)]
    have h3 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq ha0, Real.sqrt_sq (by positivity)] at h3
  have hb : b ≤ C6 * (2 * u ^ 4 * ‖ψ‖) := by
    have := torusSeries_six_le C6 hC60 hC6 hs hs1 ψ
    rwa [h2s] at this
  have hab : a * b ≤ (2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2 := by
    have e : (2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2 = 2 * u ^ 2 * ‖ψ‖ * (C6 * (2 * u ^ 4 * ‖ψ‖)) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC60.le]
      ring
    rw [e]
    exact mul_le_mul ha hb hb0 (by positivity)
  rw [← Real.sqrt_mul ha0]
  calc Real.sqrt (a * b) ≤ Real.sqrt ((2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2) := Real.sqrt_le_sqrt hab
    _ = 2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖ := Real.sqrt_sq (by positivity)
    _ = _ := by rw [hu3]

end ShellTorus.Internal

end Breakdown.Periodic

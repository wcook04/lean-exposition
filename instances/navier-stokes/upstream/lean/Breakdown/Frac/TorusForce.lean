import Breakdown.Frac.StTorusForce
import Breakdown.Torus.StatementsForce

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace FracForce.Internal

theorem one_le_norm_freq {k : Lattice} (hk : k ≠ 0) : 1 ≤ ‖freq k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    exact hk (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hz : (1 : ℤ) ≤ k i ^ 2 := by
    rcases lt_trichotomy (k i) 0 with h | h | h
    · nlinarith
    · exact absurd h hi
    · nlinarith
  have h1 : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by exact_mod_cast hz
  have h2 : ((k i : ℤ) : ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [Internal.norm_freq_sq]
    exact Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (freq k)]

theorem sq_le_rpow {α : ℝ} (hα : 1 ≤ α) (k : Lattice) :
    4 * π ^ 2 * ‖freq k‖ ^ 2 ≤ (2 * π * ‖freq k‖) ^ (2 * α) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : freq (0 : Lattice) = 0 := by simp [freq]
    rw [h0, norm_zero, mul_zero, Real.zero_rpow (by linarith)]
    simp
  · have hx : 1 ≤ 2 * π * ‖freq k‖ := by
      have := one_le_norm_freq hk
      nlinarith [Real.pi_gt_three]
    have h := Real.rpow_le_rpow_of_exponent_le hx (show (2 : ℝ) ≤ 2 * α by linarith)
    rw [Real.rpow_two] at h
    calc 4 * π ^ 2 * ‖freq k‖ ^ 2 = (2 * π * ‖freq k‖) ^ 2 := by ring
      _ ≤ _ := h

theorem factor_nonneg (α t : ℝ) (k : Lattice) : 0 ≤ fracLatticeFactor α t k := (Real.exp_pos _).le

theorem factor_le_heat {α : ℝ} (hα : 1 ≤ α) (t : ℝ) (k : Lattice) :
    fracLatticeFactor α t k ≤ heatFactor t k := by
  unfold fracLatticeFactor heatFactor
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_right (sq_le_rpow hα k) (le_max_right _ _)

theorem factor_anti (α : ℝ) {s t : ℝ} (h : s ≤ t) (k : Lattice) :
    fracLatticeFactor α t k ≤ fracLatticeFactor α s k := by
  unfold fracLatticeFactor
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_left (max_le_max h le_rfl) (Real.rpow_nonneg (by positivity) _)

theorem factor_neg (α t : ℝ) (k : Lattice) :
    fracLatticeFactor α t (-k) = fracLatticeFactor α t k := by
  simp [fracLatticeFactor, FreqTrSeries.Internal.freq_neg, norm_neg]

theorem factor_add (α : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (k : Lattice) :
    fracLatticeFactor α (s + t) k = fracLatticeFactor α s k * fracLatticeFactor α t k := by
  unfold fracLatticeFactor
  rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, ← Real.exp_add]
  ring_nf

theorem continuous_factor (α : ℝ) (k : Lattice) : Continuous fun t => fracLatticeFactor α t k := by
  unfold fracLatticeFactor
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)

def seq (α τ : ℝ) (F : Space → Space) (k : Lattice) : Coef :=
  if 0 < τ then (Real.sqrt (weight k) * fracLatticeFactor α τ k) • divFree k (freqTrCoef F k) else 0

theorem norm_seq_le_of_le {α : ℝ} (hα : 1 ≤ α) (F : Space → Space) {s₁ s : ℝ} (h₁ : 0 < s₁)
    (h : s₁ ≤ s) (k : Lattice) :
    ‖seq α s F k‖ ≤ 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor s₁ k) := by
  have hs : 0 < s := h₁.trans_le h
  have hA : ‖freqTrCoef F k‖ ≤ ∫ x in cell, ‖complexify (F x)‖ := FreqTrSeries.Internal.norm_freqTrCoef_le k
  have hw : 0 ≤ Real.sqrt (weight k) := Real.sqrt_nonneg _
  have hh : fracLatticeFactor α s k ≤ heatFactor s₁ k :=
    (factor_anti α h k).trans (factor_le_heat hα s₁ k)
  have hh0 : 0 ≤ fracLatticeFactor α s k := factor_nonneg _ _ _
  have hb : 0 ≤ Real.sqrt (weight k) * heatFactor s₁ k := mul_nonneg hw (Internal.heatFactor_nonneg _ _)
  unfold seq
  rw [if_pos hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hh0)]
  calc Real.sqrt (weight k) * fracLatticeFactor α s k * ‖divFree k (freqTrCoef F k)‖
      ≤ Real.sqrt (weight k) * fracLatticeFactor α s k * (2 * ‖freqTrCoef F k‖) :=
        mul_le_mul_of_nonneg_left (Internal.norm_divFree_le _ _) (mul_nonneg hw hh0)
    _ ≤ Real.sqrt (weight k) * heatFactor s₁ k * (2 * ∫ x in cell, ‖complexify (F x)‖) := by
        gcongr
    _ = 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor s₁ k) := by ring

theorem summable_bound (A : ℝ) {s : ℝ} (hs : 0 < s) :
    Summable fun k => (2 * A * (Real.sqrt (weight k) * heatFactor s k)) ^ 2 := by
  refine ((Internal.summable_weight_heat hs).mul_left ((2 * A) ^ 2)).congr fun k => ?_
  simp only [mul_pow, Real.sq_sqrt (Internal.weight_pos k).le]

theorem memℓp_seq {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) : Memℓp (seq α τ F) 2 := by
  by_cases hτ : 0 < τ
  · rw [memℓp_gen_iff (by norm_num)]
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_bound (∫ x in cell, ‖complexify (F x)‖) hτ)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_seq_le_of_le hα F hτ le_rfl k) 2
  · have h : seq α τ F = 0 := funext fun k => if_neg hτ
    rw [h]
    exact zero_memℓp

theorem seq_mem {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) :
    (⟨seq α τ F, memℓp_seq hα τ F⟩ : Seq) ∈ fieldSpace := by
  change (∀ k i, (seq α τ F (-k)).ofLp i = starRingEnd ℂ ((seq α τ F k).ofLp i)) ∧
    ∀ k, divPairing k (seq α τ F k) = 0
  refine ⟨fun k i => ?_, fun k => ?_⟩
  · unfold seq
    split_ifs with hτ
    · rw [FreqTrSeries.Internal.weight_neg, factor_neg, PiLp.smul_apply, PiLp.smul_apply,
        Force.Internal.divFree_neg_apply k (Force.Internal.freqTrCoef_neg_apply F k)]
      simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
    · simp
  · unfold seq
    split_ifs with hτ
    · rw [Force.Internal.divPairing_real_smul, Force.Internal.divPairing_divFree, mul_zero]
    · simp [divPairing]

def vec {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) : V :=
  ⟨⟨seq α τ F, memℓp_seq hα τ F⟩, seq_mem hα τ F⟩

theorem vec_apply {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) (k : Lattice) :
    ((vec hα τ F : V) : Seq) k = seq α τ F k := rfl

theorem vec_spec {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) :
    FracTorusForceSpec α τ F (vec hα τ F) := by
  intro k
  show (Real.sqrt (weight k))⁻¹ • seq α τ F k = _
  unfold seq fracTorusForceCoef
  split_ifs with hτ
  · rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ (Internal.sqrt_weight_pos k).ne', one_mul]
  · simp

theorem force_eq {α : ℝ} (hα : 1 ≤ α) (τ : ℝ) (F : Space → Space) :
    fracTorusForce α τ F = vec hα τ F := by
  have h : ∃ w, FracTorusForceSpec α τ F w := ⟨vec hα τ F, vec_spec hα τ F⟩
  unfold fracTorusForce
  rw [dif_pos h]
  exact coeff_injective fun k => by rw [h.choose_spec k, vec_spec hα τ F k]

theorem vec_continuousOn {α : ℝ} (hα : 1 ≤ α) (F : Space → Space) :
    ContinuousOn (fun s => vec hα s F) (Ioi 0) := by
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) < s₀ := hs₀
  rw [ContinuousWithinAt, tendsto_subtype_rng]
  have hev : ∀ᶠ s in 𝓝[Ioi 0] s₀, s₀ / 2 ≤ s :=
    nhdsWithin_le_nhds (Ici_mem_nhds (half_lt_self hs₀'))
  apply Internal.tendsto_seq
    (b := fun k => 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor (s₀ / 2) k))
    (summable_bound _ (half_pos hs₀'))
  · intro k
    simp only [vec_apply]
    have e : seq α s₀ F k = (Real.sqrt (weight k) * fracLatticeFactor α s₀ k) • divFree k (freqTrCoef F k) := by
      simp only [seq, if_pos hs₀']
    rw [e]
    have hc : Tendsto (fun s => (Real.sqrt (weight k) * fracLatticeFactor α s k) • divFree k (freqTrCoef F k))
        (𝓝[Ioi 0] s₀) (𝓝 ((Real.sqrt (weight k) * fracLatticeFactor α s₀ k) • divFree k (freqTrCoef F k))) :=
      (((continuous_const.mul (continuous_factor α k)).smul continuous_const).tendsto
        s₀).mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [seq, if_pos hs']
  · filter_upwards [hev] with s hs k
    rw [vec_apply]
    exact norm_seq_le_of_le hα F (half_pos hs₀') hs k

end FracForce.Internal

open FracForce.Internal

theorem fracTorusForceExists (α : ℝ) (hα : 1 ≤ α) : FracTorusForceExists α :=
  fun τ F => ⟨vec hα τ F, vec_spec hα τ F⟩

theorem fracTorusForceAlgebra (α : ℝ) (hα : 1 ≤ α) (hH : FracTorusHeatAlgebra α) :
    FracTorusForceAlgebra α := by
  refine ⟨fun τ F k => ?_, fun σ τ hσ hστ F => ?_, fun F => ?_⟩
  · rw [force_eq hα]
    exact vec_spec hα τ F k
  · apply coeff_injective
    intro k
    rw [hH.1, force_eq hα, force_eq hα, vec_spec hα, vec_spec hα]
    unfold fracTorusForceCoef
    rw [if_pos (hσ.trans_le hστ), if_pos hσ, smul_smul]
    congr 1
    have e := factor_add α (sub_nonneg.2 hστ) hσ.le k
    rw [sub_add_cancel] at e
    rw [e]
  · have e : (fun τ => fracTorusForce α τ F) = fun τ => vec hα τ F := funext fun τ => force_eq hα τ F
    rw [e]
    exact vec_continuousOn hα F

end Breakdown.Periodic

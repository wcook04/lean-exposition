import Breakdown.Uniqueness.PressureAverageAuxStress
import Breakdown.Uniqueness.PressureAverageAuxTime
import Breakdown.Uniqueness.PressureAverageAuxIdentity
import Breakdown.Uniqueness.PressureAverageAuxBound
import Breakdown.Uniqueness.PressureContinuity

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem abs_add_sub_le_three (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b,
    le_abs_self c, neg_abs_le c]

private theorem abs_integral_pressureDefect_le {T : ℝ} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSolutionOn T v q) (hE : EnergyBoundedOn T v)
    {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) {t₁ t₂ : ℝ}
    (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ T) {β δ : ℝ}
    (hF : ∀ t ∈ Icc 0 T, |∫ x, inner ℝ (v t x) (Φ x)| ≤ β)
    (hG : ∀ t ∈ Ioo 0 T, |(∫ x, inner ℝ (v t x) (sumSecondPartialsAt Φ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ Φ x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt Φ))| ≤ δ) :
    |∫ t in t₁..t₂, pressureDefect v q t Φ| ≤ 2 * β + δ * (t₂ - t₁) := by
  have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h₁ h₂
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hF t₁ (hsub ⟨le_rfl, h₁₂⟩))
  rcases eq_or_lt_of_le h₁₂ with h | h
  · subst h
    simp only [intervalIntegral.integral_same, abs_zero, sub_self, mul_zero, add_zero]
    positivity
  set F : ℝ → ℝ := fun τ => ∫ x, inner ℝ (v τ x) (Φ x) with hFdef
  set P : ℝ → ℝ := fun τ => pressureDefect v q τ Φ with hPdef
  have hPc : ContinuousOn P (Icc 0 T) := continuousOn_pressureDefect hv hE hΦ hc
  have hFc : ContinuousOn F (Icc 0 T) :=
    Internal.continuousOn_integral_inner_field hv.smooth_velocity hΦ.continuous hc
  have hPi : IntegrableOn P (uIcc t₁ t₂) := by
    rw [uIcc_of_le h₁₂]; exact (hPc.mono hsub).integrableOn_Icc
  set g : ℝ → ℝ := fun τ => F τ + ∫ s in t₁..τ, P s with hgdef
  have hgc : ContinuousOn g (Icc t₁ t₂) := by
    have h2 := intervalIntegral.continuousOn_primitive_interval hPi
    rw [uIcc_of_le h₁₂] at h2
    exact (hFc.mono hsub).add h2
  have hgd : ∀ τ ∈ Ioo t₁ t₂, HasDerivAt g
      ((∫ x, inner ℝ (deriv (fun s => v s x) τ) (Φ x)) + P τ) τ := by
    intro τ hτ
    have hτ' : τ ∈ Ioo 0 T := ⟨lt_of_le_of_lt h₁ hτ.1, lt_of_lt_of_le hτ.2 h₂⟩
    have hF' := Internal.hasDerivAt_integral_inner_field hv.smooth_velocity hΦ.continuous hc hτ'
    have hii : IntervalIntegrable P volume t₁ τ :=
      ContinuousOn.intervalIntegrable_of_Icc hτ.1.le (hPc.mono (Icc_subset_Icc h₁ (hτ.2.le.trans h₂)))
    have hmeas : StronglyMeasurableAtFilter P (nhds τ) volume :=
      (hPc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ'
    have hca : ContinuousAt P τ := hPc.continuousAt (Icc_mem_nhds hτ'.1 hτ'.2)
    exact hF'.add (intervalIntegral.integral_hasDerivAt_right hii hmeas hca)
  obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope g _ h hgc hgd
  have hc0 : c ∈ Ioo 0 T := ⟨lt_of_le_of_lt h₁ hc'.1, lt_of_lt_of_le hc'.2 h₂⟩
  have hid := Internal.integral_time_derivative_add_pressureDefect hv hc0 hΦ hc
  have hEc : |(∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c| ≤ δ := by
    simp only [hPdef]; rw [hid]; exact hG c hc0
  have hlen : 0 < t₂ - t₁ := sub_pos.2 h
  have hgeq : g t₂ - g t₁ =
      ((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) := by
    rw [hcd]; field_simp
  have hg1 : g t₁ = F t₁ := by simp [hgdef]
  have hint : (∫ t in t₁..t₂, pressureDefect v q t Φ) = g t₂ - F t₂ := by
    simp [hgdef, hPdef]
  have hF1 := hF t₁ (hsub ⟨le_rfl, h₁₂⟩)
  have hF2 := hF t₂ (hsub ⟨h₁₂, le_rfl⟩)
  rw [hint]
  have e : g t₂ - F t₂ =
      ((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) + F t₁ - F t₂ := by
    rw [← hgeq, hg1]; ring
  rw [e]
  calc |((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) + F t₁ - F t₂|
      ≤ |((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁)| + |F t₁| + |F t₂| :=
        abs_add_sub_le_three _ _ _
    _ ≤ δ * (t₂ - t₁) + β + β := by
        rw [abs_mul, abs_of_pos hlen]
        gcongr
    _ = 2 * β + δ * (t₂ - t₁) := by ring

theorem tendsto_integral_pressureDefect_mollify {T : ℝ} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSolutionOn T v q) (hE : EnergyBoundedOn T v)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) {t₁ t₂ : ℝ}
    (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ T) :
    Filter.Tendsto (fun ρ => ∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ))
      Filter.atTop (nhds 0) := by
  obtain ⟨A, hA0, hA⟩ := Internal.exists_energy_bound hv hE
  obtain ⟨R, C, hR, hC, hB⟩ := Internal.mollify_field_bounds hϕ hc
  obtain ⟨C', hC', hS⟩ := Internal.abs_secondPartial_potential_div_mollify_le hϕ hc
  obtain ⟨V, hVpos, hV⟩ := Internal.exists_volume_closedBall_eq
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * (A + 8 * C ^ 2 * V) +
      (A + 72 * C ^ 2 * V + 9 * C * A + 9 * C' * A) * (t₂ - t₁) := ⟨_, rfl⟩
  have hlen : 0 ≤ t₂ - t₁ := sub_nonneg.2 h₁₂
  have key : ∀ ρ : ℝ, max 1 R ≤ ρ →
      |∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ)| ≤ K * ρ⁻¹ := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := (le_max_left _ _).trans hρ
    have hρR : R ≤ ρ := (le_max_right _ _).trans hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ρ⁻¹ := ⟨_, rfl⟩
    rw [← hs]
    have hs0 : 0 < s := hs ▸ inv_pos.2 hρ0
    have hs1 : s ≤ 1 := hs ▸ inv_le_one_of_one_le₀ hρ1
    have hρs : ρ * s = 1 := hs ▸ mul_inv_cancel₀ hρ0.ne'
    have hsinv : s⁻¹ = ρ := hs ▸ inv_inv ρ
    have hB' : ∀ x, ‖FundSol.mollify ρ ϕ x‖ ≤ C * s ^ 3 ∧
        ‖fderiv ℝ (FundSol.mollify ρ ϕ) x‖ ≤ C * s ^ 4 ∧
        ‖iteratedFDeriv ℝ 2 (FundSol.mollify ρ ϕ) x‖ ≤ C * s ^ 5 := fun x => by
      rw [hs]; exact (hB ρ hρ1 x).2
    have hS' : ∀ i j x, |FundSol.secondPartial (FundSol.potential
        (divergenceAt (FundSol.mollify ρ ϕ))) i j x| ≤ C' * s ^ 3 := fun i j x => by
      rw [hs]; exact hS ρ hρ1 i j x
    have hΦ := Internal.contDiff_mollify_field hϕ hc hρ0
    have hΦc := Internal.hasCompactSupport_mollify_field hϕ hc hρ0
    have hsupp : ∀ x, 2 * ρ < ‖x‖ → FundSol.mollify ρ ϕ x = 0 := fun x hx =>
      ((hB ρ hρ1 x).1 (by linarith))
    have hvol : volume.real (Metric.closedBall (0 : Space) (2 * ρ)) = V * (2 * ρ) ^ 3 :=
      hV _ (by linarith)
    have hθ : ContDiff ℝ ∞ (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ))) :=
      FundSol.contDiff_potential (Internal.PressureMollify.contDiff_divergenceAt hΦ)
        (Internal.PressureMollify.hasCompactSupport_divergenceAt hΦc)
    have hβ : ∀ t ∈ Icc 0 T, |∫ x, inner ℝ (v t x) (FundSol.mollify ρ ϕ x)| ≤
        s * A + s⁻¹ * ((C * s ^ 3) ^ 2 * (V * (2 * ρ) ^ 3)) := by
      intro t ht
      obtain ⟨hwc, hwi, hwA⟩ := hA t ht
      have h := Internal.abs_integral_inner_le_of_support hwc hwi hΦ.continuous
        (fun x => (hB' x).1) hsupp hs0
      rw [hvol] at h
      exact h.trans (by gcongr)
    have hδ : ∀ t ∈ Ioo 0 T, |(∫ x, inner ℝ (v t x) (sumSecondPartialsAt (FundSol.mollify ρ ϕ) x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ (FundSol.mollify ρ ϕ) x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ)))| ≤
        (s * A + s⁻¹ * ((3 * (C * s ^ 5)) ^ 2 * (V * (2 * ρ) ^ 3))) + 9 * (C * s ^ 4) * A +
          9 * (C' * s ^ 3) * A := by
      intro t ht
      obtain ⟨hwc, hwi, hwA⟩ := hA t (Ioo_subset_Icc_self ht)
      have h1 := Internal.abs_integral_inner_sumSecondPartialsAt_le hwc hwi hΦ
        (fun x => (hB' x).2.2) hsupp hs0
      rw [hvol] at h1
      have h2 := Internal.abs_integral_fderiv_stress_le hwc hwi hΦ (fun x => (hB' x).2.1)
      have h3 := Internal.abs_stressPairing_self_le hwc hwi hθ hS'
      have hI0 : 0 ≤ ∫ x, ‖v t x‖ ^ 2 := integral_nonneg fun x => by positivity
      calc _ ≤ |∫ x, inner ℝ (v t x) (sumSecondPartialsAt (FundSol.mollify ρ ϕ) x)| +
            |∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ (FundSol.mollify ρ ϕ) x (unitVector i) j| +
            |stressPairing (v t) (v t) (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ)))| :=
            abs_add_sub_le_three _ _ _
        _ ≤ _ := by
            gcongr
            · exact h1.trans (by gcongr)
            · exact h2.trans (by gcongr)
            · exact h3.trans (by gcongr)
    have hmain := abs_integral_pressureDefect_le hv hE hΦ hΦc h₁ h₁₂ h₂ hβ hδ
    refine hmain.trans ?_
    have e1 : s⁻¹ * ((C * s ^ 3) ^ 2 * (V * (2 * ρ) ^ 3)) = 8 * C ^ 2 * V * s ^ 2 * (ρ * s) ^ 4 := by
      rw [hsinv]; ring
    have e2 : s⁻¹ * ((3 * (C * s ^ 5)) ^ 2 * (V * (2 * ρ) ^ 3)) =
        72 * C ^ 2 * V * s ^ 6 * (ρ * s) ^ 4 := by
      rw [hsinv]; ring
    rw [e1, e2, hρs, one_pow, mul_one, mul_one]
    have p2 : s ^ 2 ≤ s := by
      calc s ^ 2 = s * s := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0.le
        _ = s := mul_one s
    have hpow : ∀ n : ℕ, s ^ (n + 1) ≤ s := fun n => by
      calc s ^ (n + 1) = s * s ^ n := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs0.le hs1) hs0.le
        _ = s := mul_one s
    have hCV : 0 ≤ C ^ 2 * V := by positivity
    have q1 : 8 * C ^ 2 * V * s ^ 2 ≤ 8 * C ^ 2 * V * s :=
      mul_le_mul_of_nonneg_left p2 (by positivity)
    have q2 : 72 * C ^ 2 * V * s ^ 6 ≤ 72 * C ^ 2 * V * s :=
      mul_le_mul_of_nonneg_left (hpow 5) (by positivity)
    have q3 : 9 * (C * s ^ 4) * A ≤ 9 * C * s * A := by
      have h := mul_le_mul_of_nonneg_left (hpow 3) (mul_nonneg hC hA0)
      linear_combination 9 * h
    have q4 : 9 * (C' * s ^ 3) * A ≤ 9 * C' * s * A := by
      have h := mul_le_mul_of_nonneg_left (hpow 2) (mul_nonneg hC' hA0)
      linear_combination 9 * h
    have hsum : (s * A + 72 * C ^ 2 * V * s ^ 6 + 9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A) ≤
        (A + 72 * C ^ 2 * V + 9 * C * A + 9 * C' * A) * s := by linarith
    have hsum2 : s * A + 8 * C ^ 2 * V * s ^ 2 ≤ (A + 8 * C ^ 2 * V) * s := by linarith
    calc 2 * (s * A + 8 * C ^ 2 * V * s ^ 2) +
          (s * A + 72 * C ^ 2 * V * s ^ 6 + 9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A) * (t₂ - t₁)
        ≤ 2 * ((A + 8 * C ^ 2 * V) * s) +
          ((A + 72 * C ^ 2 * V + 9 * C * A + 9 * C' * A) * s) * (t₂ - t₁) := by
          have := mul_le_mul_of_nonneg_right hsum hlen
          linarith
      _ = K * s := by rw [hK]; ring
  have hlim : Filter.Tendsto (fun ρ : ℝ => K * ρ⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (max 1 R)] with ρ hρ
  rw [Real.norm_eq_abs]
  exact key ρ hρ

end Breakdown

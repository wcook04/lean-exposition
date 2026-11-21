import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.PressureAverageAuxStress
import Breakdown.Uniqueness.PressureAverageAuxTime
import Breakdown.Uniqueness.PressureAverageAuxBound

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal

namespace SpacePressureAverage

private theorem abs_add_sub_le_three (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b,
    le_abs_self c, neg_abs_le c]

private theorem energy_bound {T : ℝ} {v : ℝ → Space → Space}
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Icc 0 T ×ˢ univ))
    (hE : EnergyBoundedOn T v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc 0 T, Continuous (v t) ∧
      Integrable (fun x => ‖v t x‖ ^ 2) ∧ ∫ x, ‖v t x‖ ^ 2 ≤ A := by
  obtain ⟨A, hA⟩ := hE
  refine ⟨max A 0, le_max_right _ _, fun t ht => ?_⟩
  have hc : Continuous (v t) := (Internal.CutoffEnergy.contDiff_slice hv ht).continuous
  have hi : Integrable (fun x => ‖v t x‖ ^ 2) :=
    Internal.PressureMollify.integrable_norm_sq hc (hA t ht)
  refine ⟨hc, hi, ?_⟩
  have h1 : ENNReal.ofReal (∫ x, ‖v t x‖ ^ 2) ≤ ENNReal.ofReal A := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)]
    exact hA t ht
  rcases le_total A 0 with h | h
  · rw [ENNReal.ofReal_eq_zero.2 h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    exact h1.trans (le_max_right _ _)
  · exact ((ENNReal.ofReal_le_ofReal_iff h).1 h1).trans (le_max_left _ _)

private theorem abs_integral_le {T : ℝ} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {F : ℝ → Space → Space} (h1 : ForcedTimeIdentityStatement)
    (hv : IsForcedSolutionOn T v q F)
    {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    (hPc : ContinuousOn (fun τ => pressureDefect v q τ Φ) (Icc 0 T)) {t₁ t₂ : ℝ}
    (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ T) {β δ : ℝ}
    (hF : ∀ t ∈ Icc 0 T, |∫ x, inner ℝ (v t x) (Φ x)| ≤ β)
    (hG : ∀ t ∈ Ioo 0 T, |-(∫ x, inner ℝ (F t x) (Φ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ Φ x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt Φ))| ≤ δ) :
    |∫ t in t₁..t₂, pressureDefect v q t Φ| ≤ 2 * β + δ * (t₂ - t₁) := by
  have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h₁ h₂
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hF t₁ (hsub ⟨le_rfl, h₁₂⟩))
  rcases eq_or_lt_of_le h₁₂ with h | h
  · subst h
    simp only [intervalIntegral.integral_same, abs_zero, sub_self, mul_zero, add_zero]
    positivity
  set G : ℝ → ℝ := fun τ => ∫ x, inner ℝ (v τ x) (Φ x) with hGdef
  set P : ℝ → ℝ := fun τ => pressureDefect v q τ Φ with hPdef
  have hGc : ContinuousOn G (Icc 0 T) :=
    Internal.continuousOn_integral_inner_field hv.smooth_velocity hΦ.continuous hc
  have hPi : IntegrableOn P (uIcc t₁ t₂) := by
    rw [uIcc_of_le h₁₂]; exact (hPc.mono hsub).integrableOn_Icc
  set g : ℝ → ℝ := fun τ => G τ + ∫ s in t₁..τ, P s with hgdef
  have hgc : ContinuousOn g (Icc t₁ t₂) := by
    have h2 := intervalIntegral.continuousOn_primitive_interval hPi
    rw [uIcc_of_le h₁₂] at h2
    exact (hGc.mono hsub).add h2
  have hgd : ∀ τ ∈ Ioo t₁ t₂, HasDerivAt g
      ((∫ x, inner ℝ (deriv (fun s => v s x) τ) (Φ x)) + P τ) τ := by
    intro τ hτ
    have hτ' : τ ∈ Ioo 0 T := ⟨lt_of_le_of_lt h₁ hτ.1, lt_of_lt_of_le hτ.2 h₂⟩
    have hG' := Internal.hasDerivAt_integral_inner_field hv.smooth_velocity hΦ.continuous hc hτ'
    have hii : IntervalIntegrable P volume t₁ τ :=
      ContinuousOn.intervalIntegrable_of_Icc hτ.1.le
        (hPc.mono (Icc_subset_Icc h₁ (hτ.2.le.trans h₂)))
    have hmeas : StronglyMeasurableAtFilter P (nhds τ) volume :=
      (hPc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ'
    have hca : ContinuousAt P τ := hPc.continuousAt (Icc_mem_nhds hτ'.1 hτ'.2)
    exact hG'.add (intervalIntegral.integral_hasDerivAt_right hii hmeas hca)
  obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope g _ h hgc hgd
  have hc0 : c ∈ Ioo 0 T := ⟨lt_of_le_of_lt h₁ hc'.1, lt_of_lt_of_le hc'.2 h₂⟩
  have hid := h1 T v q F hv c hc0 Φ hΦ hc
  have hEc : |(∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c| ≤ δ := by
    simp only [hPdef]; rw [hid]; exact hG c hc0
  have hlen : 0 < t₂ - t₁ := sub_pos.2 h
  have hgeq : g t₂ - g t₁ =
      ((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) := by
    rw [hcd]; field_simp
  have hg1 : g t₁ = G t₁ := by simp [hgdef]
  have hint : (∫ t in t₁..t₂, pressureDefect v q t Φ) = g t₂ - G t₂ := by
    simp [hgdef, hPdef]
  have hF1 := hF t₁ (hsub ⟨le_rfl, h₁₂⟩)
  have hF2 := hF t₂ (hsub ⟨h₁₂, le_rfl⟩)
  rw [hint]
  have e : g t₂ - G t₂ =
      ((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) + G t₁ - G t₂ := by
    rw [← hgeq, hg1]; ring
  rw [e]
  calc |((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁) + G t₁ - G t₂|
      ≤ |((∫ x, inner ℝ (deriv (fun s => v s x) c) (Φ x)) + P c) * (t₂ - t₁)| + |G t₁| + |G t₂| :=
        abs_add_sub_le_three _ _ _
    _ ≤ δ * (t₂ - t₁) + β + β := by
        rw [abs_mul, abs_of_pos hlen]
        gcongr
    _ = 2 * β + δ * (t₂ - t₁) := by ring

end SpacePressureAverage

end FracInternal

open FracInternal.SpacePressureAverage in
theorem forcedPressureAverage_of (h1 : ForcedTimeIdentityStatement)
    (h2 : ForcedPressureContinuityStatement) : ForcedPressureAverageStatement := by
  intro T v q F hv hE ϕ hϕ hc t₁ t₂ h₁ h₁₂ h₂
  obtain ⟨A, hA0, hA⟩ := energy_bound hv.smooth_velocity hE
  obtain ⟨R, C, hR, hC, hB⟩ := Internal.mollify_field_bounds hϕ hc
  obtain ⟨C', hC', hS⟩ := Internal.abs_secondPartial_potential_div_mollify_le hϕ hc
  obtain ⟨V, hVpos, hV⟩ := Internal.exists_volume_closedBall_eq
  set L : ℝ := t₂ - t₁ with hL
  have hlen : 0 ≤ L := sub_nonneg.2 h₁₂
  set K : ℝ := 2 * (A + 8 * C ^ 2 * V) + (9 * C * A + 9 * C' * A) * L with hK
  have key : ∀ η : ℝ, 0 ≤ η → ∀ ρ : ℝ, max 1 R ≤ ρ →
      (∀ t ∈ Ioo 0 T, |∫ x, inner ℝ (F t x) (FundSol.mollify ρ ϕ x)| ≤ η) →
      |∫ t in t₁..t₂, pressureDefect v q t (FundSol.mollify ρ ϕ)| ≤ K * ρ⁻¹ + η * L := by
    intro η hη ρ hρ hforce
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
        ‖fderiv ℝ (FundSol.mollify ρ ϕ) x‖ ≤ C * s ^ 4 := fun x => by
      rw [hs]; exact ⟨(hB ρ hρ1 x).2.1, (hB ρ hρ1 x).2.2.1⟩
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
    have hδ : ∀ t ∈ Ioo 0 T, |-(∫ x, inner ℝ (F t x) (FundSol.mollify ρ ϕ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ (FundSol.mollify ρ ϕ) x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ)))| ≤
        η + 9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A := by
      intro t ht
      obtain ⟨hwc, hwi, hwA⟩ := hA t (Ioo_subset_Icc_self ht)
      have h0 := hforce t ht
      have h2' := Internal.abs_integral_fderiv_stress_le hwc hwi hΦ (fun x => (hB' x).2)
      have h3 := Internal.abs_stressPairing_self_le hwc hwi hθ hS'
      have hI0 : 0 ≤ ∫ x, ‖v t x‖ ^ 2 := integral_nonneg fun x => by positivity
      calc _ ≤ |-(∫ x, inner ℝ (F t x) (FundSol.mollify ρ ϕ x))| +
            |∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ (FundSol.mollify ρ ϕ) x (unitVector i) j| +
            |stressPairing (v t) (v t) (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ)))| :=
            abs_add_sub_le_three _ _ _
        _ ≤ _ := by
            rw [abs_neg]
            gcongr
            · exact h2'.trans (by gcongr)
            · exact h3.trans (by gcongr)
    have hmain := abs_integral_le h1 hv hΦ hΦc (h2 T v q F hv hE _ hΦ hΦc) h₁ h₁₂ h₂ hβ hδ
    refine hmain.trans ?_
    have e1 : s⁻¹ * ((C * s ^ 3) ^ 2 * (V * (2 * ρ) ^ 3)) =
        8 * C ^ 2 * V * s ^ 2 * (ρ * s) ^ 4 := by
      rw [hsinv]; ring
    rw [e1, hρs, one_pow, mul_one]
    have p2 : s ^ 2 ≤ s := by
      calc s ^ 2 = s * s := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0.le
        _ = s := mul_one s
    have hpow : ∀ n : ℕ, s ^ (n + 1) ≤ s := fun n => by
      calc s ^ (n + 1) = s * s ^ n := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs0.le hs1) hs0.le
        _ = s := mul_one s
    have q1 : 8 * C ^ 2 * V * s ^ 2 ≤ 8 * C ^ 2 * V * s :=
      mul_le_mul_of_nonneg_left p2 (by positivity)
    have q3 : 9 * (C * s ^ 4) * A ≤ 9 * C * s * A := by
      have h := mul_le_mul_of_nonneg_left (hpow 3) (mul_nonneg hC hA0)
      linear_combination 9 * h
    have q4 : 9 * (C' * s ^ 3) * A ≤ 9 * C' * s * A := by
      have h := mul_le_mul_of_nonneg_left (hpow 2) (mul_nonneg hC' hA0)
      linear_combination 9 * h
    have hsum : 9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A ≤ (9 * C * A + 9 * C' * A) * s := by
      linarith
    have hsum2 : s * A + 8 * C ^ 2 * V * s ^ 2 ≤ (A + 8 * C ^ 2 * V) * s := by linarith
    have hm := mul_le_mul_of_nonneg_right hsum hlen
    calc 2 * (s * A + 8 * C ^ 2 * V * s ^ 2) +
          (η + 9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A) * (t₂ - t₁)
        = 2 * (s * A + 8 * C ^ 2 * V * s ^ 2) +
          (9 * (C * s ^ 4) * A + 9 * (C' * s ^ 3) * A) * L + η * L := by rw [hL]; ring
      _ ≤ 2 * ((A + 8 * C ^ 2 * V) * s) + ((9 * C * A + 9 * C' * A) * s) * L + η * L := by
          linarith
      _ = K * s + η * L := by rw [hK]; ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  set η : ℝ := ε / (2 * (L + 1)) with hη
  have hL1 : 0 < L + 1 := by linarith
  have hη0 : 0 < η := by positivity
  have hηL : η * L ≤ ε / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  obtain ⟨ρ₀, hρ₀⟩ := hv.force_mollify ϕ hϕ hc η hη0
  have hlim : Filter.Tendsto (fun ρ : ℝ => K * ρ⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul K
  filter_upwards [hlim.eventually (gt_mem_nhds hε2),
    Filter.eventually_ge_atTop (max (max 1 R) ρ₀)] with ρ hK' hρ
  rw [Real.dist_eq, sub_zero]
  have hb := key η hη0.le ρ ((le_max_left _ _).trans hρ)
    (hρ₀ ρ ((le_max_right _ _).trans hρ))
  linarith

end Breakdown

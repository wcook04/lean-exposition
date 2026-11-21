import Breakdown.FracCert.SmoothMomentStepAux
import Breakdown.Transfer.Restrict

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem lintegral_rpow_sub_le {s m t β : ℝ} (hm : m ≤ s) (hs : s ≤ t) (hm0 : 0 ≤ m)
    (hβ : β < 1) :
    ∫⁻ r in Ioo m s, ENNReal.ofReal ((s - r) ^ (-β)) ≤ ENNReal.ofReal (t ^ (1 - β) / (1 - β)) := by
  have hint : IntervalIntegrable (fun r => (s - r) ^ (-β)) volume m s := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := s - m) (b := 0)
      (by linarith : -1 < -β)).comp_sub_left s
    simpa using h
  have hint' : IntegrableOn (fun r => (s - r) ^ (-β)) (Ioo m s) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hm).1 hint).mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo m s)] fun r => (s - r) ^ (-β) :=
    (ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun r hr => Real.rpow_nonneg (by linarith [hr.2]) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint' hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hm, intervalIntegral.integral_comp_sub_left
      (fun r => r ^ (-β)) s, sub_self, integral_rpow (Or.inl (by linarith))]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (0 : ℝ) ^ (-β + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h1, sub_zero, show -β + 1 = 1 - β by ring]
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)

private theorem sq_rpow_half (z : ℝ≥0∞) : z = (z ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
  rw [← ENNReal.rpow_mul]; norm_num

set_option maxHeartbeats 1000000 in
private theorem restart_concrete {α : ℝ} {F : ScaledMildFramework X (dilExponent α)}
    (hG : F.G = fracHeatX α) (hK : F.K = fracBilinX α) {u : ℝ → X} {t : ℝ}
    (hmild : F.IsMildOnIcc u 0 t) {m s : ℝ} (hm0 : 0 ≤ m) (hms : m ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => fracBilinX α (s - r) (u r) (u r)) volume m s ∧
      u s = fracHeatX α (s - m) (u m) + ∫ r in m..s, fracBilinX α (s - r) (u r) (u r) := by
  have hD : F.toHeatBilinear.VarConst u m s :=
    Breakdown.restrict X F.toHeatBilinear u 0 m s hm0 hms
      (hmild.1.mono (Icc_subset_Icc le_rfl hst))
      (hmild.2 m ⟨hm0, hms.trans hst⟩) (hmild.2 s ⟨hm0.trans hms, hst⟩)
  have hKK : F.toHeatBilinear.K = fracBilinX α := hK
  have hGG : F.toHeatBilinear.G = fracHeatX α := hG
  obtain ⟨hInt, hEq⟩ := hD
  rw [hKK] at hInt
  rw [hKK, hGG] at hEq
  exact ⟨hInt, hEq⟩

private theorem heat_part {α : ℝ} (hα : 1 < α) {k : ℕ} {CH : ℝ}
    (hCH : ∀ τ : ℝ, 0 < τ → ∀ x : X, homNormSq (k + 1) (symbolX (fracHeatX α τ x)) ≤
      ENNReal.ofReal (CH * τ ^ (-(1 / α))) * homNormSq k (symbolX x))
    {m τ B' : ℝ} (hm0 : 0 < m) (hmτ : m ≤ τ) (hB'0 : 0 ≤ B') (x : X)
    (hx : homNormSq k (symbolX x) ≤ ENNReal.ofReal B') :
    homNormSq (k + 1) (symbolX (fracHeatX α τ x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (|CH| * m ^ (-(1 / α)) * B')) := by
  have h1 := hCH τ (by linarith) x
  have hmono : τ ^ (-(1 / α)) ≤ m ^ (-(1 / α)) :=
    Real.rpow_le_rpow_of_nonpos hm0 hmτ (by have := one_div_pos.2 (by linarith : (0:ℝ) < α); linarith)
  have h2 : homNormSq (k + 1) (symbolX (fracHeatX α τ x)) ≤
      ENNReal.ofReal (|CH| * m ^ (-(1 / α)) * B') := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hm0.le _))]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hx
    calc CH * τ ^ (-(1 / α)) ≤ |CH| * τ ^ (-(1 / α)) :=
          mul_le_mul_of_nonneg_right (le_abs_self CH) (Real.rpow_nonneg (by linarith) _)
      _ ≤ |CH| * m ^ (-(1 / α)) := mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
  calc _ ≤ ENNReal.ofReal (|CH| * m ^ (-(1 / α)) * B') ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hm0.le _)) hB'0) (by norm_num),
          Real.sqrt_eq_rpow]

private theorem bilin_pointwise {α : ℝ} {k : ℕ} {CB : ℝ}
    (hCB : ∀ τ : ℝ, 0 < τ → ∀ x : X, homNormSq (k + 1) (symbolX (fracBilinX α τ x x)) ≤
      ENNReal.ofReal (CB * τ ^ (-(2 / α))) * (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x)))
    {τ B' : ℝ} (hτ : 0 < τ) (hB'0 : 0 ≤ B') (x : X)
    (hW : freqL1Norm (symbolX x) ≤ ENNReal.ofReal B') (hH : homNormSq k (symbolX x) ≤ ENNReal.ofReal B') :
    homNormSq (k + 1) (symbolX (fracBilinX α τ x x)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (|CB| * B' ^ 3)) * ENNReal.ofReal (τ ^ (-(1 / α))) := by
  have h1 := hCB τ hτ x
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.sqrt (|CB| * B' ^ 3) * τ ^ (-(1 / α)) := ⟨_, rfl⟩
  have hYn : 0 ≤ Y := hY ▸ mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hτ.le _)
  have hY2 : Y ^ 2 = |CB| * τ ^ (-(2 / α)) * B' ^ 3 := by
    rw [hY, mul_pow, Real.sq_sqrt (mul_nonneg (abs_nonneg _) (pow_nonneg hB'0 _)),
      ← Real.rpow_natCast (τ ^ (-(1 / α))), ← Real.rpow_mul hτ.le]
    push_cast
    ring_nf
  have h2 : homNormSq (k + 1) (symbolX (fracBilinX α τ x x)) ≤ ENNReal.ofReal (Y ^ 2) := by
    refine h1.trans ?_
    rw [hY2, ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hτ.le _))]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self CB) (Real.rpow_nonneg hτ.le _))) ?_
    calc freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x)
        ≤ ENNReal.ofReal B' ^ 2 * ENNReal.ofReal B' := by gcongr
      _ = ENNReal.ofReal (B' ^ 3) := by
          rw [← ENNReal.ofReal_pow hB'0, ← ENNReal.ofReal_mul (pow_nonneg hB'0 _)]
          ring_nf
  calc _ ≤ ENNReal.ofReal (Y ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal Y := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hYn]
    _ = _ := by rw [hY, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

private theorem bilin_part {α : ℝ} (hα : 1 < α) {k : ℕ} {CB : ℝ}
    (hCB : ∀ τ : ℝ, 0 < τ → ∀ x : X, homNormSq (k + 1) (symbolX (fracBilinX α τ x x)) ≤
      ENNReal.ofReal (CB * τ ^ (-(2 / α))) * (freqL1Norm (symbolX x) ^ 2 * homNormSq k (symbolX x)))
    {u : ℝ → X} {m s t B' : ℝ} (hm0 : 0 ≤ m) (hms : m ≤ s) (hst : s ≤ t) (hB'0 : 0 ≤ B')
    (hInt : IntervalIntegrable (fun r => fracBilinX α (s - r) (u r) (u r)) volume m s)
    (hW : ∀ r ∈ Icc m t, freqL1Norm (symbolX (u r)) ≤ ENNReal.ofReal B')
    (hH : ∀ r ∈ Icc m t, homNormSq k (symbolX (u r)) ≤ ENNReal.ofReal B') :
    homNormSq (k + 1) (symbolX (∫ r in m..s, fracBilinX α (s - r) (u r) (u r))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (|CB| * B' ^ 3) * (t ^ (1 - 1 / α) / (1 - 1 / α))) := by
  have hβ1 : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact hα
  refine (smoothMomentNorm_integral (k + 1) _ m s hms hInt).trans ?_
  calc ∫⁻ r in Ioo m s, homNormSq (k + 1) (symbolX (fracBilinX α (s - r) (u r) (u r))) ^
        (1 / 2 : ℝ)
      ≤ ∫⁻ r in Ioo m s, ENNReal.ofReal (Real.sqrt (|CB| * B' ^ 3)) *
          ENNReal.ofReal ((s - r) ^ (-(1 / α))) := by
        refine setLIntegral_mono' measurableSet_Ioo (fun r hr => ?_)
        have hr' : r ∈ Icc m t := ⟨hr.1.le, hr.2.le.trans hst⟩
        exact bilin_pointwise hCB (by linarith [hr.2]) hB'0 (u r) (hW r hr') (hH r hr')
    _ = ENNReal.ofReal (Real.sqrt (|CB| * B' ^ 3)) *
          ∫⁻ r in Ioo m s, ENNReal.ofReal ((s - r) ^ (-(1 / α))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.sqrt (|CB| * B' ^ 3)) *
          ENNReal.ofReal (t ^ (1 - 1 / α) / (1 - 1 / α)) := by
        gcongr
        exact lintegral_rpow_sub_le hms hst hm0 hβ1
    _ = _ := by rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

set_option maxHeartbeats 1000000 in
theorem mildMomentStep : MildMomentStepStatement := by
  unfold MildMomentStepStatement
  intro α hα hα2 F hF u t ht hmild k hk hbd σ hσ
  obtain ⟨hG, hK⟩ := hF
  have hm0 : 0 < σ / 2 := by linarith [hσ.1]
  have hmt : σ / 2 ≤ t := by linarith [hσ.1, hσ.2]
  obtain ⟨B, hB⟩ := hbd (σ / 2) ⟨hm0, hmt⟩
  obtain ⟨CH, hCH⟩ := smoothHeatMomentGain α hα k
  obtain ⟨CB, hCB⟩ := smoothBilinMomentGain α hα k
  have hB'0 : 0 ≤ max B 0 := le_max_right _ _
  have hW : ∀ s ∈ Icc (σ / 2) t, freqL1Norm (symbolX (u s)) ≤ ENNReal.ofReal (max B 0) :=
    fun s hs => le_trans (le_trans le_self_add (hB s hs)) (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hH : ∀ s ∈ Icc (σ / 2) t, homNormSq k (symbolX (u s)) ≤ ENNReal.ofReal (max B 0) :=
    fun s hs => le_trans (le_trans le_add_self (hB s hs)) (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hβ1 : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact hα
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = Real.sqrt (|CH| * (σ / 2) ^ (-(1 / α)) * max B 0) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ,
      c2 = Real.sqrt (|CB| * max B 0 ^ 3) * (t ^ (1 - 1 / α) / (1 - 1 / α)) := ⟨_, rfl⟩
  have hc1n : 0 ≤ c1 := hc1 ▸ Real.sqrt_nonneg _
  have hc2n : 0 ≤ c2 := hc2 ▸ mul_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (Real.rpow_nonneg ht.le _) (by linarith))
  refine ⟨(c1 + c2) ^ 2, fun s hs => ?_⟩
  have hms : σ / 2 ≤ s := by linarith [hs.1, hσ.1]
  obtain ⟨hInt, hEq⟩ := restart_concrete hG hK hmild hm0.le hms hs.2
  have hA := heat_part hα hCH hm0 (by linarith [hs.1] : σ / 2 ≤ s - σ / 2) hB'0 (u (σ / 2))
    (hH _ ⟨le_rfl, hmt⟩)
  have hI := bilin_part hα hCB hm0.le hms hs.2 hB'0 hInt hW hH
  rw [← hc1] at hA
  rw [← hc2] at hI
  have htri := smoothMomentNorm_add (k + 1) (fracHeatX α (s - σ / 2) (u (σ / 2)))
    (∫ r in (σ / 2)..s, fracBilinX α (s - r) (u r) (u r))
  rw [← hEq] at htri
  rw [sq_rpow_half (homNormSq (k + 1) (symbolX (u s)))]
  calc (homNormSq (k + 1) (symbolX (u s)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
      ≤ (ENNReal.ofReal c1 + ENNReal.ofReal c2) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (htri.trans (add_le_add hA hI)) (by norm_num)
    _ = ENNReal.ofReal ((c1 + c2) ^ 2) := by
        rw [← ENNReal.ofReal_add hc1n hc2n,
          ENNReal.ofReal_rpow_of_nonneg (add_nonneg hc1n hc2n) (by norm_num), Real.rpow_two]

end Breakdown.FracCert

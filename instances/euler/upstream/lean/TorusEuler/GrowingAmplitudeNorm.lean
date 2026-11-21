import TorusEuler.MovingAmplitudeCoefficients

/-! The amplitude norm comparison in Lemma 2.5, given the normalized state error. -/

open scoped InnerProductSpace

namespace TorusEuler.ReferenceAmplitude

open ReferenceComparison ReferencePropagator
open ReferenceRiccati (s s_pos s_le_one)

private theorem growing_component_bounds {ε t δ : ℝ} {Y U V : ℝ → ℝ}
    (hδ : δ ≤ 1 / 2) (hclose : ‖normalizedState ε Y U V t - (1, 0)‖ ≤ δ) :
    |normalizedH Y V t - 1| ≤ δ ∧ |normalizedL ε Y U V t| ≤ δ ∧
      1 / 2 ≤ normalizedH Y V t := by
  let p := normalizedState ε Y U V t - (1, 0)
  have hh : |normalizedH Y V t - 1| ≤ δ := by
    simpa only [Real.norm_eq_abs, p, Prod.fst_sub, normalizedState] using
      (norm_fst_le p).trans hclose
  have hl : |normalizedL ε Y U V t| ≤ δ := by
    simpa only [Real.norm_eq_abs, p, Prod.snd_sub, normalizedState, sub_zero] using
      (norm_snd_le p).trans hclose
  exact ⟨hh, hl, by linarith [(abs_le.mp hh).1]⟩

/-- Closeness to the growing state gives positivity of the transverse component
and the ratio estimate following (2.9). -/
theorem raw_ratio_close_of_growing_state_close {ε t δ : ℝ} {Y U V : ℝ → ℝ}
    (hδ : δ ≤ 1 / 2) (hclose : ‖normalizedState ε Y U V t - (1, 0)‖ ≤ δ) :
    0 < V t ∧ |U t / V t - Y t| ≤ 2 * δ := by
  obtain ⟨_, hl, hh⟩ := growing_component_bounds hδ hclose
  have hH : 0 < normalizedH Y V t := lt_of_lt_of_le (by norm_num) hh
  have hV : 0 < V t := (div_pos_iff_of_pos_right (growingFactor_pos Y t)).mp hH
  refine ⟨hV, ?_⟩
  rw [raw_ratio_eq (ε := ε) (Y := Y) (U := U) hV.ne', add_sub_cancel_left, abs_mul,
    abs_of_pos (s_pos ε t), abs_div, abs_of_pos hH]
  calc
    _ ≤ |normalizedL ε Y U V t| / normalizedH Y V t :=
      mul_le_of_le_one_left (div_nonneg (abs_nonneg _) hH.le) (s_le_one ε t)
    _ ≤ δ / (1 / 2) :=
      (div_le_div_of_nonneg_right hl hH.le).trans
        (div_le_div_of_nonneg_left ((abs_nonneg _).trans hl) (by norm_num) hh)
    _ = 2 * δ := by ring

/-- The wave-vector window and the ratio bound control the geometric correction
to the amplitude norm. -/
theorem normCorrection_le_of_growing_geometry {T X Q Z U V : ℝ}
    (hT : 1 ≤ T) (hX : |X| ≤ T ^ 2) (hQ : |Q| ≤ T) (hZ : 1 / 2 ≤ Z)
    (hw : |U / V| ≤ 2) :
    normCorrection X Q Z U V ≤ 40 * T ^ 4 := by
  let w := U / V
  have hT2 : T ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hZ₀ : 0 < Z := by linarith
  have hnum : |X * w - Q| ≤ 3 * T ^ 2 := calc
    _ ≤ |X * w| + |Q| := abs_sub _ _
    _ ≤ T ^ 2 * 2 + T := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hX hw (abs_nonneg _) (sq_nonneg _)) hQ
    _ ≤ _ := by linarith
  have hz : |(X * w - Q) / Z| ≤ 6 * T ^ 2 := by
    rw [abs_div, abs_of_pos hZ₀, div_le_iff₀ hZ₀]
    exact hnum.trans (by nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hZ)])
  have hw2 : w ^ 2 ≤ 2 ^ 2 := sq_le_sq.mpr (by
    simpa only [abs_of_pos (by norm_num : 0 < (2 : ℝ))] using hw)
  have hz2 : ((X * w - Q) / Z) ^ 2 ≤ (6 * T ^ 2) ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg (by positivity : 0 ≤ 6 * T ^ 2)])
  have hT4 : 1 ≤ T ^ 4 := one_le_pow₀ hT
  unfold normCorrection
  change w ^ 2 + ((X * w - Q) / Z) ^ 2 ≤ _
  nlinarith

open MovingWaveVector MovingAmplitude

/-- The physical amplitude in the preceding orthonormal frame satisfies the
logarithmic estimate (2.9) with an explicit error budget. -/
theorem log_growing_physical_norm_le {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {Y : ℝ → ℝ} {ε t scale S T δ : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : 0 < S)
    (hperp : ⟪k t, a t⟫_ℝ = 0)
    (hT : 1 ≤ T) (hX : |X e k scale t| ≤ T ^ 2)
    (hQ : |Q e k scale S t| ≤ T) (hZ : 1 / 2 ≤ Z e k scale t)
    (hY : |Y t| ≤ 1) (hδ : δ ≤ 1 / 2)
    (hclose : ‖normalizedState ε Y (U e a S) (V e a) t - (1, 0)‖ ≤ δ) :
    |Real.log (‖a t‖ / growingFactor Y t)| ≤ 2 * δ + 20 * T ^ 4 * (S ^ 2)⁻¹ := by
  obtain ⟨hh, _, hhhalf⟩ := growing_component_bounds hδ hclose
  obtain ⟨hV, hratio⟩ := raw_ratio_close_of_growing_state_close hδ hclose
  have hw : |U e a S t / V e a t| ≤ 2 := by
    calc
      _ = |U e a S t / V e a t - Y t + Y t| := by rw [sub_add_cancel]
      _ ≤ |U e a S t / V e a t - Y t| + |Y t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hZ₀ : Z e k scale t ≠ 0 := by linarith
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Space := by simp
  let B := OrthonormalBasis.mk he (he.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  have hB (i : Fin 3) : B.repr (a t) i = ⟪e t i, a t⟫_ℝ := by
    simp only [B, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk]
  obtain ⟨h₀, h₁, h₂⟩ := amplitude_pairings he hscale hS.ne' hZ₀ hperp
  let F := normCorrection (X e k scale t) (Q e k scale S t) (Z e k scale t) (U e a S t) (V e a t)
  have hF : F ≤ 40 * T ^ 4 := normCorrection_le_of_growing_geometry hT hX hQ hZ hw
  have hnorm : ‖a t‖ = V e a t * Real.sqrt (1 + (S ^ 2)⁻¹ * F) :=
    orthonormal_physical_norm_eq B (a t) hV hZ₀ hS
      ((hB 0).trans h₀) ((hB 1).trans h₁) ((hB 2).trans h₂)
  have hg := growingFactor_pos Y t
  have hφ : 0 ≤ (S ^ 2)⁻¹ := by positivity
  have hlog := log_amplitude_ratio_le hg (by norm_num : (0 : ℝ) < 1 / 2)
    hhhalf (by norm_num : (1 / 2 : ℝ) ≤ 1) hh hφ (normCorrection_nonneg
      (X e k scale t) (Q e k scale S t) (Z e k scale t) (U e a S t) (V e a t))
  dsimp only [normalizedH] at hlog
  rw [mul_div_cancel₀ _ hg.ne', mul_one, ← hnorm] at hlog
  refine hlog.trans ?_
  calc
    _ ≤ δ / (1 / 2) + (S ^ 2)⁻¹ * (40 * T ^ 4) / 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF hφ) (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

end TorusEuler.ReferenceAmplitude

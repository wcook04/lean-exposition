import TorusEuler.Paper.Proofs.S678b.Library.CurlLower

/-! # Proposition 8.2: the curl lower bound (8.2) for the limit `u`

Copy (package S678b) of the private library lemma
`InductiveEulerCentralWaves.eventually_curl_lower_bound` (Theorem11FromInductiveStages.lean:520)
and of its private helpers (`frequency_mono`, `frequency_lower`, `frequency_gap`,
`correction_jet_bound`, `clock_maps`, `physical_activeSlab`, `initial_strength_eq`,
`first_coupling_eq`, `order_at_least_one`), with:
(1.15) from an argument `hlog` (Lemma 1.3), the bound (7.6) of the older gradient from an
argument `hOld` (Lemma B.1), the retained strength from `preceding_strength_retained h2_2`
(Lemma 2.2), the geometry of the new wave from `wave_geometry_of_lemma24 h2_4` (Lemma 2.4), and
the lower bound `S ≥ 1` of the shear from the values (7.3) (the library took it from
`PhysicalAmplification.toNormalized`, which reaches the content of Lemma 2.2). With the bounds
of Lemma 2.4 (`|ζ| ≤ 3T^2`, `|ζ_2 + ετ| ≤ 1/2`) the normalized window enters as `2T` and the
window constant as `2K`, `K` from `h71.window_upper`. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S678b

open MovingWaveVector (PhysicalAmplification frame entry X Q Z)

namespace Stages

variable (s : InductiveEulerStages)

/-- Copy of the library's private `InductiveEulerStages.frequency_mono`. -/
theorem frequency_mono (hinit : 2 ≤ s.frequency 0) : Monotone s.frequency :=
  frequencySchedule_frequency_mono s.exponentParameter s.order s.frequency s.exponentParameter_ge
    (one_le_two.trans hinit) s.frequency_step

/-- Copy of the library's private `InductiveEulerStages.frequency_lower`. -/
theorem frequency_lower (hinit : 2 ≤ s.frequency 0) (n : ℕ) : 2 ≤ s.frequency n :=
  hinit.trans (frequency_mono s hinit (Nat.zero_le n))

/-- Copy of the library's private `InductiveEulerStages.frequency_gap`: `λ_n^288 ≤ λ_{n+1}`. -/
theorem frequency_gap (hinit : 2 ≤ s.frequency 0) (n : ℕ) :
    s.frequency n ^ 288 ≤ s.frequency (n + 1) := by
  rw [s.frequency_step]
  exact pow_le_pow_right₀ (one_le_two.trans (frequency_lower s hinit n))
    ((by decide : 288 ≤ 320).trans (by
      have hb := s.exponentParameter_ge
      unfold frequencyExponent
      exact (Nat.mul_le_mul_left 320 hb).trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos (s.order (n + 1))))))

/-- Copy of the library's private `InductiveEulerStages.correction_jet_bound` ((7.4) as a jet
bound). -/
theorem correction_jet_bound (n m : ℕ) (hm : m ≤ s.order (n + 1)) (t : ℝ)
    (ht : t ∈ Icc 0 (s.slab (n + 1))) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (s.velocity (n + 1) t - s.velocity n t - s.oscillation (n + 1) t) x‖ ≤
      (s.frequency (n + 1))⁻¹ := by
  have h := s.correction_bound n m hm t ht
  exact (norm_iteratedFDeriv_le_spatialHolderHalfNorm h.1 le_rfl x).trans h.2

/-- Copy of the library's private `order_at_least_one`. -/
theorem order_at_least_one (n : ℕ) : 1 ≤ s.order (n + 1) := by
  cases n with
  | zero => rw [s.initial_order]
  | succ n => exact (s.order_maximum n).1.1

/-- Copy of the library's private `InductiveEulerCentralWaves.activation_mono`. -/
theorem activation_mono : Monotone s.activation := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => rw [s.activation_zero, s.first_activation]
  | succ n => exact sub_nonneg.mp (s.activation_step n).1

end Stages

namespace CentralWaves

variable {s : InductiveEulerStages} (w : InductiveEulerCentralWaves s)

/-- Copy of the library's private `clock_maps`. -/
theorem clock_maps (j : ℕ) :
    MapsTo (w.physical j).clock (Icc 0 (w.window j))
      (Icc (s.activation (j + 2)) (s.slab (j + 2))) := by
  intro τ hτ
  have hr := (w.physical j).rate_pos
  refine ⟨le_add_of_nonneg_right (div_nonneg hτ.1 hr.le), ?_⟩
  have h : (w.physical j).clock τ ≤ (w.physical j).clock (w.window j) :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hr.le)
  exact h.trans_eq (w.physical_window j)

/-- Copy of the library's private `physical_activeSlab`. -/
theorem physical_activeSlab (j : ℕ) :
    (w.physical j).activeSlab (w.window j) = Icc (s.activation (j + 2)) (s.slab (j + 2)) := by
  rw [PhysicalAmplification.activeSlab, w.physical_window]

/-- Copy of the library's private `initial_strength_eq`. -/
theorem initial_strength_eq (j : ℕ) :
    (w.physical j).initialStrength =
      ‖w.waveVector (j + 1) (s.activation (j + 2))‖ *
        ‖w.amplitude (j + 1) (s.activation (j + 2))‖ := by
  rw [PhysicalAmplification.initialStrength, w.preceding_vector, w.preceding_amplitude]

/-- Copy of the library's private `first_coupling_eq`. -/
theorem first_coupling_eq (j : ℕ) :
    (w.physical j).firstCoupling =
      entry (frame (w.waveVector (j + 1)) (w.amplitude (j + 1)) (s.activation (j + 2)))
        (fderiv ℝ (s.velocity j (s.activation (j + 2))) 0) 0 1 := by
  unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis
  rw [w.preceding_vector, w.preceding_amplitude,
    w.older_gradient j _ (w.physical j).activation]

/-- The coefficient of the principal term of (8.2) for the doubled window, where `K` bounds the
normalized window by `K L^4` (item 2 of the proof of Theorem 7.1). -/
noncomputable def curlCoefficient (K : ℝ) : ℝ :=
  Real.exp (-1) * w.strengthConstant⁻¹ / (6 * (2 * K) ^ 2)

/-- The coefficient of the principal term is positive. -/
theorem curlCoefficient_pos {K : ℝ} (hK : 0 < K) : 0 < curlCoefficient w K := by
  have h : 0 < w.strengthConstant := zero_lt_two.trans_le w.strengthConstant_ge
  unfold curlCoefficient
  exact div_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr h))
    (mul_pos (by norm_num) (pow_pos (mul_pos two_pos hK) 2))

/-- `S ≥ 1` when the strength is at least twice the first coupling: `S = σ/r`,
`r = (2σν)^{1/2} ≤ σ`. -/
theorem one_le_shear {I : Set ℝ} {t₀ : ℝ} (P : PhysicalAmplification I t₀)
    (h : 2 * P.firstCoupling ≤ P.initialStrength) : 1 ≤ P.shear := by
  have hσ := P.initialStrength_pos
  have hν := P.first_coupling_positive
  have hr := P.rate_pos
  have hle : P.rate ≤ P.initialStrength := by
    change Real.sqrt (2 * P.initialStrength * P.firstCoupling) ≤ P.initialStrength
    calc Real.sqrt (2 * P.initialStrength * P.firstCoupling)
        ≤ Real.sqrt (P.initialStrength ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = P.initialStrength := Real.sqrt_sq hσ.le
  unfold PhysicalAmplification.shear
  rw [le_div_iff₀ hr, one_mul]
  exact hle

/-- **The curl lower bound (8.2) passed to the limit** (09b:12-63): for large `j` and
`t ∈ [t_{j+2}, t_{j+3})` (Lean index `j + 2` = TeX index `j`),
`|curl u(t,0)| ≥ c λ_{j+1}^{1/8} - C λ_{j+1}^{1/32} - C`. Copy of the library's private
`eventually_curl_lower_bound` with the cited results as arguments (module docstring). -/
theorem eventually_curl_lower_bound (h2_2 : Statement.lemma_2_2) (h2_4 : Statement.lemma_2_4)
    {K : ℝ} (hK : 0 < K)
    (hwindow : ∀ j, w.window j ≤ K * (4 * Real.log (s.frequency (j + 4))) ^ 4) {T : ℝ} (hinit : 2 ≤ s.frequency 0) (hslab : ∀ n, T ≤ s.slab n)
    (hbefore : ∀ n, s.activation n < T)
    (hHalf : ∀ j, inductionHalfLength s.frequency j ≤ s.frequency j ^ (-1 / 16 : ℝ))
    (hlog : ∀ i, 4 * Real.log (s.frequency (i + 3)) ≤ Real.log (s.frequency i) ^ 2)
    (hOld : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (s.slab n),
      ‖fderiv ℝ (s.velocity n t) 0‖ ≤ s.frequency n ^ 9)
    (hcomp : ∀ C₀ : ℕ, ∀ᶠ j in atTop, FiniteSmallness (w.physical j) (w.window j) C₀)
    {u : Velocity}
    (hprefix : ∀ S < T, TendstoUniformlyOn
      (fun n (z : ℝ × Vec3) => fderiv ℝ (s.velocity n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3))) :
    ∀ᶠ j : ℕ in atTop, 0 ≤ s.activation (j + 2) ∧
      ∀ t ∈ Ico (s.activation (j + 2)) (s.activation (j + 3)),
        curlCoefficient w K * s.frequency (j + 1) ^ (1 / 8 : ℝ) -
          (3 * ‖curlOfDerivativeCLM‖) * s.frequency (j + 1) ^ (1 / 32 : ℝ) -
            3 * ‖curlOfDerivativeCLM‖ ≤ ‖curl (u t) 0‖ := by
  obtain ⟨N, hGeo24⟩ := wave_geometry_of_lemma24 h2_4
  have hmono := Stages.activation_mono s
  have ha (n : ℕ) : 0 ≤ s.activation n := by
    rw [← s.activation_zero]; exact hmono (Nat.zero_le n)
  have hWaves (n : ℕ) := stage_spatial_jets_of_joint_smoothness (u := s.velocity n)
    ((ha 0).trans_lt ((hbefore 0).trans_le (hslab n))) (s.smooth n)
  have hfreqT : Tendsto s.frequency atTop atTop :=
    frequencySchedule_frequency_tendsto_atTop s.exponentParameter s.order s.frequency
      s.exponentParameter_ge (one_lt_two.trans_le hinit) s.frequency_step
  have hC := zero_lt_two.trans_le w.strengthConstant_ge
  have hroot : Tendsto (fun j => s.frequency (j + 1) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (hfreqT.comp (tendsto_add_atTop_nat 1))
  filter_upwards [hOld, eventually_inductive_projection_log_bound hfreqT hlog,
    hcomp (max N 1), hroot.eventually_ge_atTop (8 * Real.pi * w.strengthConstant)]
    with j hOld hlog hsmall hlarge
  refine ⟨ha (j + 2), fun t ht => ?_⟩
  let I := Icc (s.activation (j + 2)) (s.activation (j + 3))
  let P := w.physical j
  let d := w.crossing j
  have htI : t ∈ I := Ico_subset_Icc_self ht
  have hWithin (n : ℕ) : s.activation (j + 3) ≤ s.slab n := (hbefore (j + 3)).le.trans (hslab n)
  have hI : I ⊆ Icc (s.activation (j + 2)) (s.slab (j + 2)) :=
    Icc_subset_Icc_right (hWithin (j + 2))
  have hmOld (r : ℝ) (hr : r ∈ I) : r ∈ Icc 0 (s.slab j) :=
    ⟨(ha (j + 2)).trans hr.1, hr.2.trans (hWithin j)⟩
  have hμ : 1 ≤ s.frequency (j + 1) := one_le_two.trans (Stages.frequency_lower s hinit (j + 1))
  have hshort : s.activation (j + 3) - s.activation (j + 2) ≤
      s.frequency (j + 1) ^ (-1 / 16 : ℝ) :=
    (s.activation_step (j + 1)).2.trans (hHalf (j + 1))
  have hB (r : ℝ) (hr : r ∈ I) : ‖P.B r‖ ≤ s.frequency (j + 1) ^ (1 / 32 : ℝ) := by
    rw [show P.B r = fderiv ℝ (s.velocity j r) 0 from w.older_gradient j r (hI hr)]
    exact (hOld r (hmOld r hr)).trans <|
      older_gradient_scale_le_of_frequency_gap
        (zero_le_two.trans (Stages.frequency_lower s hinit j)) (Stages.frequency_gap s hinit j)
  have hStrength := preceding_strength_retained h2_2
    (k := P.kp) (a := P.ap) (B := P.B) hμ hshort
    (fun r hr => P.preceding_data r (hI hr))
    (fun r hr => P.trace_zero r (hI hr))
    (fun r hr => (P.preceding_vector r (hI hr)).mono hI)
    (fun r hr => by simpa only [affineWaveAmplitudeOperator_apply] using
      (P.preceding_amplitude r (hI hr)).mono hI)
    hB htI
  have hPhysical : t ∈ P.activeSlab (w.window j) :=
    (physical_activeSlab w j).symm ▸ hI htI
  have hVec := P.preceding_data t (hI htI)
  have hNew := d.transverse t hPhysical
  have hscale : 0 < s.frequency (j + 2) :=
    zero_lt_two.trans_le (Stages.frequency_lower s hinit (j + 2))
  have hGeo := hGeo24 d (le_max_left N 1) (le_max_right N 1) (w.window_ge j) hscale
    (physical_activeSlab w j).symm hsmall hPhysical
  have hShear : 1 ≤ P.shear := by
    apply one_le_shear
    have hS := (w.strength_at_crossing j).1
    have hN' := (w.coupling_at_crossing j).2
    rw [← first_coupling_eq] at hN'
    rw [← initial_strength_eq] at hS
    have h8 : 8 * Real.pi ≤ w.strengthConstant⁻¹ * s.frequency (j + 1) ^ (1 / 4 : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hC]
      linarith
    change 2 * (w.physical j).firstCoupling ≤ (w.physical j).initialStrength
    linarith
  have hCarry : (Real.exp (-1) * w.strengthConstant⁻¹) * s.frequency (j + 1) ^ (1 / 4 : ℝ) ≤
      ‖w.waveVector (j + 1) t‖ * ‖w.amplitude (j + 1) t‖ := by
    change Real.exp (-1) * (‖(w.physical j).kp (s.activation (j + 2))‖ *
      ‖(w.physical j).ap (s.activation (j + 2))‖) ≤
        ‖(w.physical j).kp t‖ * ‖(w.physical j).ap t‖ at hStrength
    rw [w.preceding_vector, w.preceding_amplitude] at hStrength
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (w.strength_at_crossing j).1 (Real.exp_pos _).le).trans
      hStrength
  have hPrev : t ∈ Icc (s.activation (j + 1)) (s.slab (j + 1)) :=
    ⟨(hmono (by omega : j + 1 ≤ j + 2)).trans ht.1, htI.2.trans (hWithin (j + 1))⟩
  have hPrevDone : t ∈ Icc (s.activation (j + 2)) (s.slab (j + 1)) :=
    ⟨ht.1, htI.2.trans (hWithin (j + 1))⟩
  have hSplit := w.gradient_split j t hPrev
  rw [w.cutoff_complete j t hPrevDone, one_smul] at hSplit
  have hTail := norm_center_fderiv_sub_le_of_inductive_tail
    (j := j + 2) (by omega) htI hmono (ha (j + 2)) (hbefore (j + 3)) hslab hinit
    (s.frequency_square_gap hinit)
    (fun n r hr => ((hWaves n).1 r hr).differentiable (by simp) 0) s.oscillation_vanishes
    (fun n _ r hr => Stages.correction_jet_bound s n 1 (Stages.order_at_least_one s n) r hr 0)
    hprefix
  have hwin : 2 * w.window j ≤ 2 * K * (4 * Real.log (s.frequency (j + 4))) ^ 4 := by
    have := hwindow j
    nlinarith
  have hV := norm_limit_center_curl_ge_of_inductive_stage
    (j := j) (freq := s.frequency) (U := s.velocity) (w := u) (C := 2 * K)
    (a := d.amplitude) (Eprev := w.error (j + 1) t) (Enew := w.error (j + 2) t)
    (cutoff := w.cutoff (j + 2) t) (c := w.strengthConstant⁻¹) hμ
    (zero_le_two.trans (Stages.frequency_lower s hinit j))
    (Stages.frequency_mono s hinit (by omega)) (Stages.frequency_lower s hinit (j + 3))
    (Stages.frequency_gap s hinit j) hVec.1 hVec.2.1 hVec.2.2 hNew.1 hShear
    (by linarith [w.window_ge j]) (mul_pos two_pos hK)
    hwin hGeo.1 hGeo.2.1 hGeo.2.2 hlog.2
  have hkp : P.kp = w.waveVector (j + 1) := w.preceding_vector j
  have hap : P.ap = w.amplitude (j + 1) := w.preceding_amplitude j
  have hk : d.waveVector = w.waveVector (j + 2) := w.current_vector j
  have ha' : d.amplitude = w.amplitude (j + 2) := w.current_amplitude j
  have hres := hV
    (by simpa only [hkp, hap] using hCarry)
    (by simpa only [hkp, hap] using hSplit)
    (by simpa only [hk, ha'] using w.gradient_split (j + 1) t (hI htI))
    (hOld t (hmOld t htI)) (w.error_bound j t hPrev) (w.error_bound (j + 1) t (hI htI)) hTail
  simpa only [curlCoefficient] using hres

end CentralWaves

end TorusEuler.Paper.Lib.S678b

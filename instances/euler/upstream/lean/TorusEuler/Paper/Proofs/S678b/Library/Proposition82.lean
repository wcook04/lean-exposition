import TorusEuler.Paper.Proofs.S678b.Library.CurlBound

/-! # Proposition 8.2 from the conclusions of Theorem 7.1 and Proposition 8.1

`proposition82_of_conclusions` proves `Proposition82Conclusions` from the statements of
Lemmas 1.3, 2.2, 2.4, B.1 (used where the TeX proof uses them, see `Library/CurlLower.lean`)
and the setting predicates of Theorem 7.1 and Proposition 8.1. The comparison hypotheses (2.7)
(`h71.comparison`, item 2 of the proof of Theorem 7.1, sections/08b_induction.tex:312-326) and the
bound on the normalized window (`h71.window_upper`, 08b:306-310) are read from `h71`, as the
TeX proof of 8.2 does (09b:28); the bound `λ_{j-2}^9 ≤ μ^{1/32}` of 09b:41 comes from the frequency gap of the parameter record. -/

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler.Paper.Lib.S678b

/-- Proposition 8.2 (sections/09b_terminal_properties.tex:7-66) for the limit `u` of
Proposition 8.1.

* Bounded velocity (09b:8-10): the continuous closed-slab limit `w` of the opening of Section 8
  (09_limit.tex:2-5), built from (7.4) at order zero alone (`closedSlab_velocity_limit`; Lemma 1.3
  does not enter this step), is bounded, and `h81` identifies it with `u` before `T_∞`
  (`limit_agreement`, `terminalVelocityBound_of_extension`).
* The curl lower bound (8.2) for `u` (09b:12-63): `CentralWaves.eventually_curl_lower_bound`
  with `h2_2`, `h2_4`, (1.15) from `h1_3`, (7.6) from `hB_1`, the half lengths (7.7)
  (`c.lifetime`), `t_j < T_∞` (`h71`), and the convergence of the order-one jets before `T_∞`
  from Proposition 8.1 (`h81.convergence` at `m = 1`). Exported as `curl_lower` (index shift
  `j ↦ j + 2`).
* `|curl u(t,0)| → ∞` (09b:64-66): the successive intervals `[t_j,t_{j+1})` cover
  `[t_j,T_∞)` (`tendsto_atTop_of_activationBounds`). -/
theorem proposition82_of_conclusions (h1_3 : Statement.lemma_1_3) (h2_2 : Statement.lemma_2_2)
    (h2_4 : Statement.lemma_2_4) (hB_1 : Statement.lemma_B_1)
    {P : InductiveEulerParameters} {c : InductiveEulerConstruction P} {C T : ℝ} {u : Velocity}
    {p : Pressure} (h71 : Theorem71Conclusions c C T) (h81 : Proposition81Conclusions c T u p)
    :
    Proposition82Conclusions c T u := by
  obtain ⟨hT, hAct, hSlab⟩ := h71.lifetime
  obtain ⟨K₀, hK₀⟩ := h71.window_upper
  have hinit := two_le_frequency_zero P
  obtain ⟨-, hlog⟩ := lemma13_schedule h1_3 P
  have hFreq : Tendsto P.frequency atTop atTop :=
    frequencySchedule_frequency_tendsto_atTop P.exponentParameter P.order P.frequency
      P.exponentParameter_ge (one_lt_two.trans_le hinit) P.frequency_step
  -- the order-one jets of `U_j` converge to those of `u` before `T_∞` (Proposition 8.1)
  have hprefix : ∀ S < T, TendstoUniformlyOn
      (fun n (z : ℝ × Vec3) => fderiv ℝ (c.stages.velocity n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
    intro S hST
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hconv := Metric.tendstoUniformlyOn_iff.mp (h81.convergence S hST 1) ε hε
    filter_upwards [hconv] with n hn z hz
    have ht : z.1 ∈ Ico 0 T := ⟨hz.1.1, hz.1.2.trans_lt hST⟩
    have hslice : ContDiff ℝ ∞ (c.stages.velocity n z.1) := by
      rw [← contDiffOn_univ]
      exact (h71.T1 n).1.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun y _ => ⟨⟨ht.1, ht.2.le.trans (hSlab n).le⟩, mem_univ y⟩)
    have hu := h81.euler.contDiff_velocity_slice ht
    have hH := spatialHolderHalf_of_contDiff_periodic (hslice.sub hu)
      (fun m y => by
        show c.stages.velocity n z.1 (y + _) - u z.1 (y + _) = _
        rw [c.stages.periodic_velocity n z.1 m y, h81.euler.periodic_velocity z.1 ht m y]) 1
    have h1 := norm_iteratedFDeriv_le_spatialHolderHalfNorm hH (le_rfl : 1 ≤ 1) z.2
    rw [norm_iteratedFDeriv_one] at h1
    have hsub : fderiv ℝ (fun x => c.stages.velocity n z.1 x - u z.1 x) z.2 =
        fderiv ℝ (c.stages.velocity n z.1) z.2 - fderiv ℝ (u z.1) z.2 :=
      ((hslice.differentiable (by simp) z.2).hasFDerivAt.sub
        (hu.differentiable (by simp) z.2).hasFDerivAt).fderiv
    rw [hsub] at h1
    have hn' := hn z.1 hz.1
    rw [Real.dist_eq, zero_sub, abs_neg] at hn'
    rw [dist_comm, dist_eq_norm]
    exact h1.trans_lt ((le_abs_self _).trans_lt hn')
  have hK : 0 < max K₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hwin : ∀ j, c.centralWaves.window j ≤
      max K₀ 1 * (4 * Real.log (c.stages.frequency (j + 4))) ^ 4 := fun j =>
    (hK₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by
      have : 0 ≤ Schedule.L P.frequency (j + 3) := mul_nonneg (by norm_num)
        (Real.log_nonneg (one_le_two.trans (Stages.frequency_lower c.stages hinit (j + 4))))
      exact pow_nonneg this 4))
  have hCurl := CentralWaves.eventually_curl_lower_bound c.centralWaves h2_2 h2_4 hK hwin hinit
    (fun n => (hSlab n).le) (activation_lt h71) (fun j => (c.lifetime.step j).2.1) hlog
    (eventually_central_gradient_bound hB_1 h71) h71.comparison hprefix
  have hcoef := CentralWaves.curlCoefficient_pos c.centralWaves hK
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, -, hagree⟩ := closedSlab_velocity_limit h71 h81
    exact terminalVelocityBound_of_extension (hw.mono (prod_mono_right (subset_univ centeredCell)))
      (fun t ht x _ => by rw [hagree t ht])
  · have hμ : Tendsto (fun j => P.frequency (j + 1)) atTop atTop :=
      hFreq.comp (tendsto_add_atTop_nat 1)
    have hActivation' : Tendsto (fun j => c.stages.activation (j + 2)) atTop (𝓝 T) :=
      hAct.comp (tendsto_add_atTop_nat 2)
    have hPrincipal : Tendsto
        (fun j => (CentralWaves.curlCoefficient c.centralWaves (max K₀ 1) / 2) *
          P.frequency (j + 1) ^ (1 / 8 : ℝ)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hμ).const_mul_atTop
        (half_pos hcoef)
    refine (tendsto_atTop_of_activationBounds hActivation' (fun j => activation_lt h71 (j + 2))
      hPrincipal ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
    filter_upwards [eventually_half_curl_power_lower_bound hcoef
      (B := 3 * ‖curlOfDerivativeCLM‖) hμ, hCurl] with j hj hjet t ht
    exact hj.trans (hjet.2 t ht)
  · refine ⟨CentralWaves.curlCoefficient c.centralWaves (max K₀ 1), 3 * ‖curlOfDerivativeCLM‖, hcoef, ?_⟩
    filter_upwards [(tendsto_sub_atTop_nat 2).eventually hCurl, eventually_ge_atTop 2]
      with j hj hj2 t ht
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at hj
    exact hj.2 t ht

end TorusEuler.Paper.Lib.S678b

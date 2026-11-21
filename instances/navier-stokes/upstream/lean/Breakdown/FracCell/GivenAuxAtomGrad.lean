import Breakdown.FracCell.GivenAuxAtomGradOff

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AtomGradInternal

open Filter Set

theorem weight_shift {y z : Space} (h : ‖z - y‖ ≤ (1 + ‖y‖) / 2) :
    (1 + ‖z‖) ^ (-(2 : ℝ)) ≤ 4 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have h1 : (1 + ‖y‖) / 2 ≤ 1 + ‖z‖ := by
    have := norm_sub_norm_le y z
    rw [norm_sub_rev] at this
    linarith [norm_nonneg y]
  have hp : 0 < (1 + ‖y‖) / 2 := by positivity
  have hq : 0 < 1 + ‖z‖ := by positivity
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hq.le, Real.rpow_neg hy.le, Real.rpow_two, Real.rpow_two]
  have h2 : ((1 + ‖y‖) / 2) ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ hp.le h1 2
  calc ((1 + ‖z‖) ^ 2)⁻¹ ≤ (((1 + ‖y‖) / 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
    _ = 4 * ((1 + ‖y‖) ^ 2)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]; norm_num

theorem ray_step {u : Space → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hoff : ∀ z : Space, (z 0 ≠ 0 ∨ z 1 ≠ 0) → DifferentiableAt ℝ u z ∧
      ‖fderiv ℝ u z‖ ≤ C * (1 + ‖z‖) ^ (-(2 : ℝ)))
    {y : Space} (hy0 : y 0 = 0) (hy1 : y 1 = 0) (hcont : ContinuousAt u y)
    {v : Space} (hv : v 0 ≠ 0 ∨ v 1 ≠ 0) {h : ℝ} (hh : 0 < h) (hhv : h * ‖v‖ ≤ (1 + ‖y‖) / 2) :
    ‖u (y + h • v) - u y‖ ≤ 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v‖ * h := by
  set K := 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v‖ with hK
  set g : ℝ → ℂ := fun s => u (y + s • v) with hg
  have hoffs : ∀ s : ℝ, s ≠ 0 → ((y + s • v) 0 ≠ 0 ∨ (y + s • v) 1 ≠ 0) := by
    intro s hs
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hy0, hy1, zero_add]
    rcases hv with h0 | h1
    · exact Or.inl (mul_ne_zero hs h0)
    · exact Or.inr (mul_ne_zero hs h1)
  have hderiv : ∀ s : ℝ, s ≠ 0 → HasDerivAt g (fderiv ℝ u (y + s • v) v) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => y + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add y
    exact (hoff _ (hoffs s hs)).1.hasFDerivAt.comp_hasDerivAt s h1
  have hbd : ∀ s : ℝ, 0 < s → s ≤ h → ‖fderiv ℝ u (y + s • v) v‖ ≤ K := by
    intro s hs hsh
    have hw : ‖(y + s • v) - y‖ ≤ (1 + ‖y‖) / 2 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
      calc s * ‖v‖ ≤ h * ‖v‖ := by gcongr
        _ ≤ _ := hhv
    calc ‖fderiv ℝ u (y + s • v) v‖ ≤ ‖fderiv ℝ u (y + s • v)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * (1 + ‖y + s • v‖) ^ (-(2 : ℝ))) * ‖v‖ := by
          gcongr; exact (hoff _ (hoffs s hs.ne')).2
      _ ≤ (C * (4 * (1 + ‖y‖) ^ (-(2 : ℝ)))) * ‖v‖ := by
          gcongr; exact weight_shift hw
      _ = K := by rw [hK]; ring
  have hseg : ∀ ε ∈ Ioo (0 : ℝ) h, ‖g h - g ε‖ ≤ K * (h - ε) := by
    intro ε hε
    exact norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := ε) (b := h)
      (f' := fun s => fderiv ℝ u (y + s • v) v) (C := K)
      (fun s hs => (hderiv s (lt_of_lt_of_le hε.1 hs.1).ne').hasDerivWithinAt)
      (fun s hs => hbd s (lt_of_lt_of_le hε.1 hs.1) hs.2.le) h (right_mem_Icc.2 hε.2.le)
  have hgc : ContinuousAt g 0 := by
    have hc : ContinuousAt (fun s : ℝ => y + s • v) 0 := by fun_prop
    exact ContinuousAt.comp_of_eq hcont hc (by simp)
  have hlim : Tendsto (fun ε => ‖g h - g ε‖) (𝓝[>] 0) (𝓝 ‖g h - g 0‖) :=
    (tendsto_const_nhds.sub (hgc.tendsto.mono_left nhdsWithin_le_nhds)).norm
  have hlim2 : Tendsto (fun ε : ℝ => K * (h - ε)) (𝓝[>] 0) (𝓝 (K * (h - 0))) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖g h - g ε‖ ≤ K * (h - ε) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hh)] with ε h1 h2
    exact hseg ε ⟨h1, h2⟩
  have := le_of_tendsto_of_tendsto hlim hlim2 hev
  simpa [hg] using this

theorem axis_bound {u : Space → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hoff : ∀ z : Space, (z 0 ≠ 0 ∨ z 1 ≠ 0) → DifferentiableAt ℝ u z ∧
      ‖fderiv ℝ u z‖ ≤ C * (1 + ‖z‖) ^ (-(2 : ℝ)))
    {y : Space} (hy0 : y 0 = 0) (hy1 : y 1 = 0) (hd : DifferentiableAt ℝ u y) :
    ‖fderiv ℝ u y‖ ≤ 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  set B := 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) with hB
  have hB0 : 0 ≤ B := by positivity
  set L := fderiv ℝ u y with hL
  have hA : ∀ v : Space, (v 0 ≠ 0 ∨ v 1 ≠ 0) → ‖L v‖ ≤ B * ‖v‖ := by
    intro v hv
    have hvpos : 0 < ‖v‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      rcases hv with h | h <;> simp [h0] at h
    set g : ℝ → ℂ := fun s => u (y + s • v) with hg
    have hgd : HasDerivAt g (L v) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
      exact hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (by simp)
    have hδ : 0 < (1 + ‖y‖) / (2 * ‖v‖) := by positivity
    have hδv : (1 + ‖y‖) / (2 * ‖v‖) * ‖v‖ = (1 + ‖y‖) / 2 := by field_simp
    refine hgd.le_of_lip' (by positivity) ?_
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hδ) hδ] with s hs
    simp only [hg, zero_smul, add_zero, sub_zero]
    rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
    · have hv' : (-v) 0 ≠ 0 ∨ (-v) 1 ≠ 0 := by
        simp only [PiLp.neg_apply, ne_eq, neg_eq_zero]; exact hv
      have hb : (-s) * ‖-v‖ ≤ (1 + ‖y‖) / 2 := by
        rw [norm_neg, ← hδv]
        exact mul_le_mul_of_nonneg_right (by linarith [hs.1]) (norm_nonneg _)
      have := ray_step hC hoff hy0 hy1 hd.continuousAt hv' (by linarith) hb
      rw [neg_smul_neg, norm_neg] at this
      rw [Real.norm_eq_abs, abs_of_neg hs0]
      calc _ ≤ 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v‖ * -s := this
        _ = B * ‖v‖ * -s := by rw [hB]
    · simp [hs0]
    · have hb : s * ‖v‖ ≤ (1 + ‖y‖) / 2 := by
        rw [← hδv]
        exact mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
      have := ray_step hC hoff hy0 hy1 hd.continuousAt hv hs0 hb
      rw [Real.norm_eq_abs, abs_of_pos hs0]
      calc _ ≤ 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v‖ * s := this
        _ = B * ‖v‖ * s := by rw [hB]
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 (fun v => ?_)
  by_cases hv : v 0 ≠ 0 ∨ v 1 ≠ 0
  · exact hA v hv
  · push Not at hv
    set e : Space := EuclideanSpace.single 0 1 with he
    have he1 : ‖e‖ = 1 := by simp [he]
    have key : ∀ ε : ℝ, 0 < ε → ‖L v‖ ≤ B * ‖v‖ + 2 * B * ε := by
      intro ε hε
      have h1 : (v + ε • e) 0 ≠ 0 ∨ (v + ε • e) 1 ≠ 0 := by
        left; simp [he, hv.1, hε.ne']
      have h2 : (ε • e) 0 ≠ 0 ∨ (ε • e) 1 ≠ 0 := by
        left; simp [he, hε.ne']
      have a1 := hA _ h1
      have a2 := hA _ h2
      have n1 : ‖v + ε • e‖ ≤ ‖v‖ + ε := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, he1, Real.norm_of_nonneg hε.le, mul_one]
      have n2 : ‖ε • e‖ = ε := by rw [norm_smul, he1, Real.norm_of_nonneg hε.le, mul_one]
      have hv' : L v = L (v + ε • e) - L (ε • e) := by rw [map_add]; abel
      rw [hv']
      calc ‖L (v + ε • e) - L (ε • e)‖ ≤ ‖L (v + ε • e)‖ + ‖L (ε • e)‖ := norm_sub_le _ _
        _ ≤ B * (‖v‖ + ε) + B * ε := by
            gcongr
            · exact a1.trans (mul_le_mul_of_nonneg_left n1 hB0)
            · exact a2.trans_eq (by rw [n2])
        _ = B * ‖v‖ + 2 * B * ε := by ring
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := key (δ / (2 * B + 1)) (by positivity)
    have h3 : 2 * B * (δ / (2 * B + 1)) ≤ δ := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end AtomGradInternal

theorem atomScalar_gradBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ C : ℝ, ∀ y : Space, ‖fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, hoff⟩ := atomScalar_offAxisGrad P hP j a M β S ha hS hM
  refine ⟨4 * C, fun y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
  by_cases hax : y 0 ≠ 0 ∨ y 1 ≠ 0
  · refine (hoff y hax).2.trans ?_
    nlinarith
  · push Not at hax
    by_cases hd : DifferentiableAt ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y
    · exact AtomGradInternal.axis_bound hC hoff hax.1 hax.2 hd
    · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
      positivity

end GivenFields

end CellCert

end Breakdown

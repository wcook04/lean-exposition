import Breakdown.FracCell.AxisLiftWeak

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert Internal.SpectralBlocksMode Internal.OnAxisNorm Internal.AxisLiftParts

namespace Internal.AxisLift

theorem entry_frame (A : Fin 3 → Fin 3 → ℝ) (θ : ℝ) :
    entrySq (∑ c : Fin 3, ∑ d : Fin 3, A c d • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ))
      = ∑ c : Fin 3, ∑ d : Fin 3, A c d ^ 2 := by
  have hv : ∀ i : Fin 3,
      (∑ c : Fin 3, ∑ d : Fin 3, A c d • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ)) (unitVector i)
        = ∑ c : Fin 3, (∑ d : Fin 3, A c d * inner ℝ (frameAt d θ) (unitVector i)) • frameAt c θ := by
    intro i
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, Finset.sum_smul, smul_smul]
  unfold entrySq
  simp only [hv, ← real_inner_self_eq_norm_sq, inner_frame_sum]
  simp [Fin.sum_univ_three, frameAt, unitVector, inner_add_left, EuclideanSpace.inner_single_left]
  linear_combination (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 + A 2 0 ^ 2 + A 2 1 ^ 2) * cos_sq_add_sin_sq θ

theorem coef_one (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (s : Fin 2) (c d : Fin 3) (r z : ℝ) :
    liftCoef g χ u s c d 1 r z = 0 := by
  simp [liftCoef]

theorem grad_cyl (g : CellBlock) (hmode : g.mode = 0) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    liftGrad g χ u (cylPoint r θ z) = ∑ c : Fin 3, ∑ d : Fin 3,
      (∑ s : Fin 2, cellInd g s r z * liftCoef g χ u s c d 0 r z) • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ) := by
  classical
  have e : ∀ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, ∑ d : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * liftCoef g χ u s c d t (radialCoord w) (w 2)) • (innerSL ℝ (frameVector d w)).smulRight (frameVector c w))
        (cylPoint r θ z)
      = ∑ c : Fin 3, ∑ d : Fin 3, (cellInd g s r z * liftCoef g χ u s c d 0 r z)
          • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ) := by
    intro s
    rw [Set.indicator_apply]
    simp only [solid_iff g s hr θ z, frame_eq, angle_cyl hr hθ, radial_cyl hr, cyl2, cellInd, hmode]
    split_ifs <;> simp [trigMode]
  calc liftGrad g χ u (cylPoint r θ z)
      = ∑ s : Fin 2, ∑ c : Fin 3, ∑ d : Fin 3, (cellInd g s r z * liftCoef g χ u s c d 0 r z)
          • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ) := Finset.sum_congr rfl fun s _ => e s
    _ = _ := by
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]

theorem sq_ind (g : CellBlock) (hin : g.innerRadius = 0) (hlow : 0 ≤ g.lowerHeight) {r : ℝ} (hr : 0 < r)
    {z : ℝ} (hz : z ≠ 0) (b : Fin 2 → ℝ) :
    (∑ s : Fin 2, cellInd g s r z * b s) ^ 2 = ∑ s : Fin 2, cellInd g s r z * b s ^ 2 := by
  have hx := ind_cross g hin hlow hr hz
  simp only [Fin.sum_univ_two]
  rcases ind_cases g 0 r z with h0 | h0 <;> rcases ind_cases g 1 r z with h1 | h1 <;>
    rw [h0, h1] at hx ⊢
  all_goals first | (exfalso; norm_num at hx; done) | ring

def integrand (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (lam : ℝ)
    (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) (s : Fin 2) (c : Fin 3) (r z : ℝ) : ℝ :=
  ((f s c r z - liftVal g χ (u s c) r z) ^ 2
    + lam⁻¹ * (liftRad g χ (u s c) r z ^ 2 + liftHgt g χ (u s c) r z ^ 2
      + ((if c = 2 then 0 else 1 : ℕ) : ℝ) ^ 2 * liftVal g χ (u s c) r z ^ 2 / r ^ 2)) * r

theorem coef_sq (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (s : Fin 2) (r z : ℝ) :
    ∑ c : Fin 3, ∑ d : Fin 3, liftCoef g χ u s c d 0 r z ^ 2
      = ∑ c : Fin 3, (liftRad g χ (u s c) r z ^ 2 + liftHgt g χ (u s c) r z ^ 2
        + ((if c = 2 then 0 else 1 : ℕ) : ℝ) ^ 2 * liftVal g χ (u s c) r z ^ 2 / r ^ 2) := by
  simp [liftCoef, Fin.sum_univ_three]
  ring

theorem point (g : CellBlock) (hin : g.innerRadius = 0) (hlow : 0 ≤ g.lowerHeight) (χ : ℝ → ℝ)
    (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (lam : ℝ) (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    {z : ℝ} (hz : z ≠ 0) :
    r * (∑ c : Fin 3, (∑ s : Fin 2, cellInd g s r z * (f s c r z - liftVal g χ (u s c) r z)) ^ 2
      + lam⁻¹ * ∑ c : Fin 3, ∑ d : Fin 3, (∑ s : Fin 2, cellInd g s r z * liftCoef g χ u s c d 0 r z) ^ 2)
      = ∑ s : Fin 2, ∑ c : Fin 3, cellInd g s r z * integrand g χ u lam f s c r z := by
  simp only [sq_ind g hin hlow hr hz]
  have k0 := coef_sq g χ u 0 r z
  have k1 := coef_sq g χ u 1 r z
  simp only [Fin.sum_univ_two, Fin.sum_univ_three] at k0 k1 ⊢
  unfold integrand
  simp only [Fin.isValue, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] at k0 k1 ⊢
  norm_num at k0 k1 ⊢
  linear_combination (r * lam⁻¹ * cellInd g 0 r z) * k0 + (r * lam⁻¹ * cellInd g 1 r z) * k1


open Internal.CylIntegral in
theorem cyl_int {F : Space → ℝ} (hF : Integrable F) :
    IntegrableOn (fun q : ℝ × ℝ => q.1 * ∫ θ in (-π)..π, F (cylPoint q.1 θ q.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
  set G : (ℝ × ℝ) × ℝ → ℝ := fun w => F (toSpace w) with hG_def
  have hG : Integrable G := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hF
  have hH := change_integrable hG
  set H : (ℝ × ℝ) × ℝ → ℝ := fun x => x.1.1 * G (cylMap.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapEquiv) ((Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) ×ˢ Set.Ioo (-π) π) := by
    rw [← swapEquiv_preimage]
    exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hHσ
  have h2 := hHσ.integral_prod_left
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only []
  rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  obtain ⟨r, z⟩ := q
  simp only [Function.comp_apply, swapEquiv_apply, hH_def, hG_def]
  rw [← toSpace_apply]
  rfl

theorem box_eq (g : CellBlock) (hin : g.innerRadius = 0) (h : ℝ → ℝ → ℝ) (s : Fin 2) :
    ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), cellInd g s q.1 q.2 * h q.1 q.2
      = (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)).indicator
          (fun q : ℝ × ℝ => h q.1 q.2) q := by
  intro q hq
  have hr : 0 < q.1 := hq.1
  unfold cellInd
  by_cases hm : cylPoint q.1 0 q.2 ∈ cellSolid g s
  · have h3 := (mem_cell g hin s hr q.2).1 hm
    rw [if_pos hm, one_mul, Set.indicator_of_mem]
    exact ⟨⟨hr, h3.1⟩, h3.2.1, h3.2.2⟩
  · rw [if_neg hm, zero_mul, Set.indicator_of_notMem]
    intro hq'
    exact hm ((mem_cell g hin s hr q.2).2 ⟨hq'.1.2, hq'.2.1, hq'.2.2⟩)

theorem gpiece (g : CellBlock) (hin : g.innerRadius = 0) (hR : 0 < g.outerRadius) (hz : g.lowerHeight < g.upperHeight)
    (h : ℝ → ℝ → ℝ) (s : Fin 2)
    (hI : IntegrableOn (fun q : ℝ × ℝ => cellInd g s q.1 q.2 * h q.1 q.2) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :
    ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), cellInd g s q.1 q.2 * h q.1 q.2
      = ∫ r in (0 : ℝ)..g.outerRadius, ∫ z in zLow g s..zHigh g s, h r z := by
  have hSm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hab : zLow g s ≤ zHigh g s := by
    unfold zLow zHigh
    split_ifs <;> linarith
  have hB : MeasurableSet (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hBS : Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) :=
    fun q hq => ⟨hq.1.1, Set.mem_univ _⟩
  have heq := box_eq g hin h s
  have hI2 := (integrableOn_congr_fun heq hSm).1 hI
  have hInt : IntegrableOn (fun q : ℝ × ℝ => h q.1 q.2)
      (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)) := by
    have h3 := (integrable_indicator_iff hB).1 hI2
    rw [IntegrableOn, Measure.restrict_restrict hB, Set.inter_eq_left.mpr hBS] at h3
    exact h3
  rw [setIntegral_congr_fun hSm heq, setIntegral_indicator hB, Set.inter_eq_right.mpr hBS,
    Measure.volume_eq_prod, setIntegral_prod _ hInt, intervalIntegral.integral_of_le hR.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only []
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

theorem integrand_meas (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ}
    (hu : ∀ s c j, ContDiff ℝ 1 (u s c j)) (lam : ℝ) {f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ}
    (hf : ∀ s c, Continuous (Function.uncurry (f s c))) (s : Fin 2) (c : Fin 3) :
    Measurable (fun q : ℝ × ℝ => integrand g χ u lam f s c q.1 q.2) := by
  have hv : ∀ j, Continuous (u s c j) := fun j => (hu s c j).continuous
  have hV : Measurable (fun q : ℝ × ℝ => liftVal g χ (u s c) q.1 q.2) := (val_cont g hχ hv).measurable
  have hf' : Measurable (fun q : ℝ × ℝ => f s c q.1 q.2) := (hf s c).measurable
  have hRd := rad_meas g hχ hv
  have hHt := (hgt_cont g hχ (hu s c)).measurable
  unfold integrand
  exact (((hf'.sub hV).pow_const 2).add (measurable_const.mul (((hRd.pow_const 2).add (hHt.pow_const 2)).add
    ((measurable_const.mul (hV.pow_const 2)).div (measurable_fst.pow_const 2))))).mul measurable_fst

theorem integrand_nonneg (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) (s : Fin 2) (c : Fin 3) {r : ℝ} (hr : 0 ≤ r) (z : ℝ) :
    0 ≤ integrand g χ u lam f s c r z := by
  unfold integrand
  have : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  positivity

theorem ind_nonneg (g : CellBlock) (s : Fin 2) (r z : ℝ) : 0 ≤ cellInd g s r z := by
  rcases ind_cases g s r z with h | h <;> rw [h] <;> norm_num

end Internal.AxisLift

open Internal.AxisLift in
theorem axisLift_of_grad (hG : LiftGradStatement) : AxisLiftStatement := by
  intro g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  obtain ⟨hψ2, hDm, hDi, hW⟩ := hG g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  have hχ : Continuous χ := by
    obtain ⟨K, hK⟩ := hχL
    exact hK.continuous
  refine ⟨liftGrad g χ u, hψ2, hDm, hDi, hW, liftGrad_mode g hχ hu, ?_⟩
  intro lam f hlam hf hF2
  set F : Space → Space := fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y with hFdef
  set f' : Fin 2 → Fin 3 → ℝ → ℝ → ℝ := fun s c r z => f s c r z - liftVal g χ (u s c) r z with hf'def
  have hsub : ∀ y, F y - ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, f' s c (radialCoord w) (w 2) • frameVector c w) y := by
    classical
    intro y
    rw [hψ y, hFdef, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    split_ifs
    · rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← sub_smul]
      rfl
    · simp
  have hFψ := hF2.sub hψ2
  have h1 : Integrable (fun y => ‖F y - ψ y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hFψ.1).1 hFψ
  set G : Space → ℝ := fun y => ‖F y - ψ y‖ ^ 2 + lam⁻¹ * entrySq (liftGrad g χ u y) with hGdef
  have hGi : Integrable G := h1.add (hDi.const_mul _)
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have hSm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hnull : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ≠ 0 := by
    have h0 : volume ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) h0
    simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hq
    exact ⟨Set.mem_univ _, hq⟩
  set T : ℝ × ℝ → ℝ := fun q => ∑ s : Fin 2, ∑ c : Fin 3, cellInd g s q.1 q.2 * integrand g χ u lam f s c q.1 q.2
    with hTdef
  have hpt : ∀ᵐ q ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))),
      q.1 * ∫ θ in (-π)..π, G (cylPoint q.1 θ q.2) = 2 * π * T q := by
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem hSm] with q hq hqS
    have hr : 0 < q.1 := hqS.1
    have e : ∫ θ in (-π)..π, G (cylPoint q.1 θ q.2)
        = ∫ θ in (-π)..π, (∑ c : Fin 3, (∑ s : Fin 2, cellInd g s q.1 q.2 * f' s c q.1 q.2) ^ 2
          + lam⁻¹ * ∑ c : Fin 3, ∑ d : Fin 3,
            (∑ s : Fin 2, cellInd g s q.1 q.2 * liftCoef g χ u s c d 0 q.1 q.2) ^ 2) := by
      rw [intervalIntegral.integral_of_le hpi, intervalIntegral.integral_of_le hpi]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
      simp only [hGdef]
      rw [hsub, norm_cyl g f' hr hθ q.2, grad_cyl g hmode χ u hr hθ q.2, entry_frame]
    rw [e, intervalIntegral.integral_const, smul_eq_mul, hTdef]
    simp only []
    rw [← point g hin hlow χ u lam f hr hq]
    ring
  have hΦ := cyl_int hGi
  have hTi : IntegrableOn T (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    have h3 := hΦ.const_mul (2 * π)⁻¹
    refine h3.congr ?_
    filter_upwards [hpt] with q hq
    rw [hq]
    field_simp
  have hpiece : ∀ s c, IntegrableOn (fun q : ℝ × ℝ => cellInd g s q.1 q.2 * integrand g χ u lam f s c q.1 q.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro s c
    have hB : MeasurableSet (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)) :=
      measurableSet_Ioc.prod measurableSet_Icc
    have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => cellInd g s q.1 q.2 * integrand g χ u lam f s c q.1 q.2)
        (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) := by
      refine ((integrand_meas g hχ hu lam hf s c).indicator hB).aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem hSm] with q hq
      exact (box_eq g hin (integrand g χ u lam f s c) s q hq).symm
    refine Integrable.mono' hTi hm ?_
    filter_upwards [ae_restrict_mem hSm] with q hq
    have hr : 0 ≤ q.1 := le_of_lt hq.1
    have hnn : ∀ s' c', 0 ≤ cellInd g s' q.1 q.2 * integrand g χ u lam f s' c' q.1 q.2 := fun s' c' =>
      mul_nonneg (ind_nonneg g s' q.1 q.2) (integrand_nonneg g χ u hlam f s' c' hr q.2)
    rw [Real.norm_of_nonneg (hnn s c), hTdef]
    simp only []
    calc cellInd g s q.1 q.2 * integrand g χ u lam f s c q.1 q.2
        ≤ ∑ c' : Fin 3, cellInd g s q.1 q.2 * integrand g χ u lam f s c' q.1 q.2 :=
          Finset.single_le_sum (f := fun c' => cellInd g s q.1 q.2 * integrand g χ u lam f s c' q.1 q.2)
            (fun c' _ => hnn s c') (Finset.mem_univ c)
      _ ≤ ∑ s' : Fin 2, ∑ c' : Fin 3, cellInd g s' q.1 q.2 * integrand g χ u lam f s' c' q.1 q.2 :=
          Finset.single_le_sum (f := fun s' => ∑ c' : Fin 3, cellInd g s' q.1 q.2 * integrand g χ u lam f s' c' q.1 q.2)
            (fun s' _ => Finset.sum_nonneg fun c' _ => hnn s' c') (Finset.mem_univ s)
  have hLHS : (∫ y, ‖F y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (liftGrad g χ u y) = ∫ y, G y := by
    rw [hGdef, integral_add h1 (hDi.const_mul _), integral_const_mul, one_div]
  refine le_of_eq ?_
  rw [hLHS, cylIntegral G hGi, integral_congr_ae hpt,
    integral_const_mul]
  congr 1
  rw [hTdef, integral_finsetSum _ fun s _ => integrable_finsetSum _ fun c _ => hpiece s c]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun c _ => hpiece s c]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gpiece g hin hR hz (integrand g χ u lam f s c) s (hpiece s c)]
  rfl

theorem axisLift_of_parts (hL : LiftSlopeStatement) (hD : LiftDerivStatement) : AxisLiftStatement :=
  axisLift_of_grad (liftGrad_of_parts hL hD)

end Spectral

end CellCert

end Breakdown

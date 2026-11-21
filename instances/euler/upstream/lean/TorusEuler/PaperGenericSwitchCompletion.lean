import TorusEuler.HierarchyTwistedCompletion
import TorusEuler.LocalizedSeedRegularity

/-! Curl completion of a time-dependent multiple on the closed centered label cell. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff Topology

namespace TorusEuler.HierarchyTwistedProfile

private theorem wavePotential_smul_profile (K : Vec3) (c : ℝ) (V : ℝ → Vec3) (s : ℝ) :
    wavePotential K (fun q => c • V q) s = c • wavePotential K V s := by
  have he : (fun q => (-(‖K‖ ^ 2)⁻¹) • cross3 K (c • V q)) =
      fun q => c • ((-(‖K‖ ^ 2)⁻¹) • cross3 K (V q)) := by
    funext q
    change (-(‖K‖ ^ 2)⁻¹) • cross3Left K (c • V q) =
      c • ((-(‖K‖ ^ 2)⁻¹) • cross3Left K (V q))
    rw [map_smul]
    exact smul_comm _ _ _
  unfold wavePotential
  rw [he]
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

private theorem uniqueDiffOn_centeredCell : UniqueDiffOn ℝ centeredCell := by
  apply uniqueDiffOn_convex
  · have heq : centeredCell = ⋂ i : Fin 3, (fun x : Vec3 => x i) ⁻¹' Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext x
      simp [centeredCell]
    rw [heq]
    exact convex_iInter fun i => (convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap
  · refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    refine mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num)) ?_
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)

set_option maxHeartbeats 900000 in
/-- The curl completion on the closed cell commutes with a time-only scalar
factor. The smoothness assumption concerns the multiplied raw profile. -/
theorem complete_smul_raw_closedCell_eval {T : ℝ} {k : Vec3} (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ V : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    {κ : ℝ → Vec3 → Vec3} {c : ℝ → ℝ} {raw : ℝ → Vec3 → ℝ → Vec3}
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    (hMean : profilePhaseAverage hT V = 0)
    (hRaw : ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => c x.1 • raw x.1 x.2.1 x.2.2)
      (hierarchyProfileSlab T))
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hCell : ∀ b ∈ centeredCell, ∀ q, V.val.val.val (t, b, q) = c t • raw t b q)
    {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    (complete hT G κ₀ hPhase hκ₀ V).val.val.val (t, a, s) =
      c t • curlOfDerivative ((fderiv ℝ (fun b => wavePotential (κ t b) (raw t b) s) a).comp
        (G.val.val.val (t, a, s))) := by
  let Vraw := HierarchySmoothProfile.ofSmooth _ hRaw
  let Q := HierarchySmoothProfile.profileWavePotential hT κ₀.val.val hκ₀ V.val.val
  let Qraw := HierarchySmoothProfile.profileWavePotential hT κ₀.val.val hκ₀ Vraw
  have hRawEval (b : Vec3) : (fun q => Vraw.val (t, b, q)) = fun q => c t • raw t b q :=
    funext fun q => HierarchySmoothProfile.ofSmooth_apply hRaw ⟨ht, mem_univ _⟩
  have hCellPotential : EqOn (fun b => Q.val (t, b, s)) (fun b => Qraw.val (t, b, s)) centeredCell := by
    intro b hb
    change Q.val (t, b, s) = Qraw.val (t, b, s)
    rw [HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ V.val.val ht,
      HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ Vraw ht, hRawEval b]
    exact congrArg (fun f => wavePotential (κ₀.val.val.val (t, b, 0)) f s)
      (funext (hCell b hb))
  have hSlice (F : HierarchySmoothProfile T Vec3) : Differentiable ℝ (fun b => F.val (t, b, s)) := by
    have hIncl : ContDiff ℝ ∞ (fun b : Vec3 => (t, b, s)) :=
      contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
    exact (contDiffOn_univ.mp ((HierarchySmoothProfile.smooth F).comp hIncl.contDiffOn
      (fun _ _ => ⟨ht, mem_univ _⟩))).differentiable (by simp)
  have hUnique := uniqueDiffOn_centeredCell a ha
  have hDiff : fderiv ℝ (fun b => Q.val (t, b, s)) a = fderiv ℝ (fun b => Qraw.val (t, b, s)) a := by
    rw [← fderivWithin_eq_fderiv hUnique (hSlice Q a), ← fderivWithin_eq_fderiv hUnique (hSlice Qraw a)]
    exact fderivWithin_congr' hCellPotential ha
  have hQraw : (fun b => Qraw.val (t, b, s)) = c t • (fun b => wavePotential (κ t b) (raw t b) s) := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ Vraw ht,
      hκ _ (show (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩), hRawEval b]
    exact wavePotential_smul_profile _ _ _ _
  rw [complete_val_val_of_phaseMean_zero hT G κ₀ hPhase hκ₀ V hMean]
  change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, a, s) = _
  rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht, hDiff, hQraw,
    fderiv_const_smul_field, Pi.smul_apply, smul_comp, curlOfDerivative_smul]

set_option maxHeartbeats 900000 in
/-- The wrapped curl completion preserves a time-only scalar factor on
the whole label space. It uses only the profile identity at the given time. -/
theorem complete_smul_wrapped_eval {T : ℝ} {k : Vec3} (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (κ₀ V : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    {κ : ℝ → Vec3 → Vec3} {c : ℝ → ℝ} {raw : ℝ → Vec3 → ℝ → Vec3}
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ₀.val.val.val x = κ x.1 x.2.1)
    (hMean : profilePhaseAverage hT V = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hWrapped : ∀ b q, V.val.val.val (t, b, q) = c t • phaseTwistedPeriodizeCentered k raw t b q)
    (a : Vec3) (s : ℝ) :
    (complete hT G κ₀ hPhase hκ₀ V).val.val.val (t, a, s) =
      c t • curlOfDerivative ((fderiv ℝ (fun b =>
        wavePotential (κ t b) (phaseTwistedPeriodizeCentered k raw t b) s) a).comp
          (G.val.val.val (t, a, s))) := by
  let Q := HierarchySmoothProfile.profileWavePotential hT κ₀.val.val hκ₀ V.val.val
  let P (b : Vec3) := wavePotential (κ t b) (phaseTwistedPeriodizeCentered k raw t b) s
  have hQ : (fun b => Q.val (t, b, s)) = c t • P := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ V.val.val ht,
      hκ _ (show (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩),
      funext (hWrapped b)]
    exact wavePotential_smul_profile _ _ _ _
  rw [complete_val_val_of_phaseMean_zero hT G κ₀ hPhase hκ₀ V hMean]
  change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, a, s) = _
  rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht, hQ,
    fderiv_const_smul_field, Pi.smul_apply, smul_comp, curlOfDerivative_smul]

end TorusEuler.HierarchyTwistedProfile

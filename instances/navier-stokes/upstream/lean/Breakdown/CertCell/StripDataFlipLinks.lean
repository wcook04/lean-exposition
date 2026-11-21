import Breakdown.CertCell.ModeHeightDerivative

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.StripFlipLinks

open HeightModes HeightOrbit

theorem plane_rect_integrable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) (a : Fin 3)
    {a₁ b₁ c₁ d₁ : ℝ} (h0 : 0 < a₁) :
    IntegrableOn (fun p : ℝ × ℝ => planeVel ξ v a p.1 p.2) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∧
      IntegrableOn (fun p : ℝ × ℝ => planeVelHeight ξ G a p.1 p.2) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∧
      IntegrableOn (fun p : ℝ × ℝ => planeVelHeight2 ξ H a p.1 p.2) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) := by
  obtain ⟨lv, lG, lH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hp
  have L1s := frameCoord_smooth a
  have L2s : ContDiff ℝ ∞ (axialL (frameCoord a)) := L1s.clm_comp contDiff_const
  have L3s : ContDiff ℝ ∞ (axialL (axialL (frameCoord a))) := L2s.clm_comp contDiff_const
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun p : ℝ × ℝ => planeVel ξ v a p.1 p.2) =
        fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg v (frameCoord a) ξ.1 ξ.2 p :=
      funext fun p => vel_rep ξ v a p
    rw [e]
    exact (waveAvg_integrableOn v lv _ L1s.continuous _ _ h0).const_mul _
  · have e : (fun p : ℝ × ℝ => planeVelHeight ξ G a p.1 p.2) =
        fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg G (axialL (frameCoord a)) ξ.1 ξ.2 p :=
      funext fun p => gradz_rep ξ G a p
    rw [e]
    exact (waveAvg_integrableOn G lG _ L2s.continuous _ _ h0).const_mul _
  · have e : (fun p : ℝ × ℝ => planeVelHeight2 ξ H a p.1 p.2) =
        fun p => (1 / (2 * Real.pi) : ℂ) * waveAvg H (axialL (axialL (frameCoord a))) ξ.1 ξ.2 p :=
      funext fun p => secondDerivzz_rep ξ H a p
    rw [e]
    exact (waveAvg_integrableOn H lH _ L3s.continuous _ _ h0).const_mul _

theorem trace_eq_at_heights (hT : TraceHeightHolds) {f fz : ℝ → ℂ}
    (hw : ∀ h : ℝ, 0 < h → HasWeakDerivOn f fz (-h) h) {h h' : ℝ} (h0 : 0 < h) (h0' : 0 < h') :
    upperTrace f fz h = upperTrace f fz h' := by
  rcases le_total h h' with hle | hle
  · exact hT f fz h h' h0 hle (hw _ (by positivity))
  · exact (hT f fz h' h h0' hle (hw _ (by positivity))).symm

end Internal.StripFlipLinks

open Internal.StripFlipLinks in
theorem stripDataFlip (hP : PlaneDataFlipHolds) (hS : StripMomentTraceHolds) (hT : TraceHeightHolds)
    (hD : ModeHeightDerivHolds) (_hE : HessianEnergyIdentityHolds) (_hV : VelocitySixthIntegralHolds) :
    StripDataFlipHolds := by
  intro Γ P v G H g hp hflip ξ a lo hi h h' wt t hlo hlohi hh hh' hwt ht
  obtain ⟨iF, iFz, iFzz⟩ := plane_rect_integrable hp (flipLabel ξ) a (b₁ := hi) (c₁ := 0) (d₁ := h) hlo
  obtain ⟨jF, jFz, jFzz⟩ := plane_rect_integrable hp ξ a (b₁ := hi) (c₁ := 0) (d₁ := h') hlo
  have hPD := (hP Γ P v G H g hp hflip ξ a).and (hD Γ P v G H g hp ξ a)
  rw [ae_restrict_iff' measurableSet_Ioi] at hPD
  have key : ∀ᵐ r, r ∈ uIoc lo hi →
      upperTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) h
          = (frameSign a : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h' ∧
        upperTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) h
          = -((frameSign a : ℂ) * upperTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) h') := by
    filter_upwards [hPD] with r hr hmem
    rw [uIoc_of_le hlohi.le] at hmem
    obtain ⟨h1, h2⟩ := hr (hlo.trans hmem.1)
    obtain ⟨e1, e2⟩ := h1 h hh
    rw [trace_eq_at_heights hT (fun k hk => (h2 k hk).1) hh hh'] at e1
    rw [trace_eq_at_heights hT (fun k hk => (h2 k hk).2.1) hh hh'] at e2
    exact ⟨e1, e2⟩
  refine ⟨?_, ?_⟩
  · rw [hS h lo hi wt t _ _ hh hlohi iF iFz hwt ht, hS h' lo hi wt t _ _ hh' hlohi jF jFz hwt ht,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [key] with r hr hmem
    have e := (hr hmem).1
    show ((wt r * t r : ℝ) : ℂ) * upperTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) h =
      (frameSign a : ℂ) * (((wt r * t r : ℝ) : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h')
    rw [e]
    ring
  · rw [hS h lo hi wt t _ _ hh hlohi iFz iFzz hwt ht, hS h' lo hi wt t _ _ hh' hlohi jFz jFzz hwt ht,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [key] with r hr hmem
    have e := (hr hmem).2
    show ((wt r * t r : ℝ) : ℂ) *
        upperTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) h =
      -((frameSign a : ℂ) * (((wt r * t r : ℝ) : ℂ) *
        upperTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) h'))
    rw [e]
    ring

end Breakdown.CertCell.Bridge

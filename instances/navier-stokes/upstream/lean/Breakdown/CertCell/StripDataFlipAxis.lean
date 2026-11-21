import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SideTrace

open CellCert.CellFormula Bridge

namespace Internal.StripFlipAxis

theorem sideTrace_zero_eq_upperTrace (f fd : ℝ → ℂ) {h : ℝ} (hh : 0 < h) :
    sideTrace f fd 0 h = upperTrace f fd h := by
  have hne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have he : edgeSign 0 h = -1 := by simp [edgeSign, not_lt.mpr hh.le]
  unfold sideTrace upperTrace
  rw [he, min_eq_left hh.le, max_eq_right hh.le, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hh.le, neg_one_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  push_cast
  field_simp
  ring

theorem weight_continuousOn {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t) (s : Set (ℝ × ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) s :=
  (Complex.continuous_ofReal.comp ((hwt.comp continuous_fst).mul (ht.comp continuous_fst))).continuousOn

theorem weighted_integrable {g : ℝ × ℝ → ℂ} {wt t : ℝ → ℝ} {lo hi h : ℝ}
    (hwt : Continuous wt) (ht : Continuous t) (hh : 0 < h) (hg : IntegrableOn g (Icc lo hi ×ˢ Icc 0 h)) :
    IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * g p) (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := by
  rw [min_eq_left hh.le, max_eq_right hh.le]
  exact hg.continuousOn_mul (weight_continuousOn hwt ht _) (isCompact_Icc.prod isCompact_Icc)

theorem axis_weighted_integrable {g : ℝ × ℝ → ℂ} {wt t t₀ : ℝ → ℝ} {hi h : ℝ} (hh : 0 < h)
    (ht₀ : Continuous t₀) (he : ∀ r, wt r * t r = r * t₀ r)
    (hg : IntegrableOn (fun p => (p.1 : ℂ) * g p) (Icc 0 hi ×ˢ Icc 0 h)) :
    IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * g p) (Icc 0 hi ×ˢ Icc (min 0 h) (max 0 h)) := by
  rw [min_eq_left hh.le, max_eq_right hh.le]
  have e : (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * g p)
      = fun p => ((t₀ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) * g p) := by
    funext p
    rw [he p.1]
    push_cast
    ring
  rw [e]
  exact hg.continuousOn_mul (Complex.continuous_ofReal.comp (ht₀.comp continuous_fst)).continuousOn
    (isCompact_Icc.prod isCompact_Icc)

theorem side_eq_at_heights (hM : SideTraceMatchHolds) {f fd : ℝ → ℂ}
    (hw : ∀ k : ℝ, 0 < k → HasWeakDerivOn f fd (-k) k) {h h' : ℝ} (hh : 0 < h) (hh' : 0 < h') :
    sideTrace f fd 0 h = sideTrace f fd 0 h' := by
  have hk : 0 < h + h' + 1 := by linarith
  refine hM f fd 0 h h' (-(h + h' + 1)) (h + h' + 1) hh.ne hh'.ne ?_ ?_ (hw _ hk)
  · simp only [lt_min_iff]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [max_lt_iff]
    refine ⟨?_, ?_, ?_⟩ <;> linarith

end Internal.StripFlipAxis

open Internal.StripFlipAxis in
theorem stripDataFlipAxis (hP : PlaneDataFlipHolds) (hS : HeightStripTraceHolds)
    (hM : SideTraceMatchHolds) (hD : ModeHeightDerivHolds) (hA : ModeAxisIntegrableHolds)
    (hU : ModeAxisPlainIntegrableHolds) (hL : ModePlaneDerivsHolds) : StripDataFlipAxisHolds := by
  intro Γ P v G H g hp hflip ξ a lo hi h h' wt t hlo hlohi hh hh' hwt ht
  have hi0 : 0 < hi := hlo.trans_lt hlohi
  have hPD := (hP Γ P v G H g hp hflip ξ a).and (hD Γ P v G H g hp ξ a)
  rw [ae_restrict_iff' measurableSet_Ioi] at hPD
  have key : ∀ᵐ r : ℝ, r ∈ Icc lo hi →
      sideTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) 0 h
          = (frameSign a : ℂ) * sideTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) 0 h' ∧
        sideTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) 0 h
          = -((frameSign a : ℂ) * sideTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) 0 h') := by
    filter_upwards [hPD, compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr hr0 hmem
    have hrpos : 0 < r := lt_of_le_of_ne (hlo.trans hmem.1) (Ne.symm hr0)
    obtain ⟨h1, h2⟩ := hr hrpos
    obtain ⟨e1, e2⟩ := h1 h hh
    rw [← side_eq_at_heights hM (fun k hk => (h2 k hk).1) hh hh',
      ← side_eq_at_heights hM (fun k hk => (h2 k hk).2.1) hh hh',
      sideTrace_zero_eq_upperTrace (planeVel (flipLabel ξ) v a r) _ hh,
      sideTrace_zero_eq_upperTrace (planeVel ξ v a r) _ hh,
      sideTrace_zero_eq_upperTrace (planeVelHeight (flipLabel ξ) G a r) _ hh,
      sideTrace_zero_eq_upperTrace (planeVelHeight ξ G a r) _ hh]
    exact ⟨e1, e2⟩
  have sub : ∀ k : ℝ, Icc lo hi ×ˢ Icc (0 : ℝ) k ⊆ Icc 0 hi ×ˢ Icc 0 k := fun k =>
    prod_mono (Icc_subset_Icc_left hlo) subset_rfl
  refine ⟨?_, fun hadm => ?_⟩
  · obtain ⟨uF, uFz⟩ := hU Γ P v G H g hp (flipLabel ξ) a 2 hi 0 h hi0 hh
    obtain ⟨wF, wFz⟩ := hU Γ P v G H g hp ξ a 2 hi 0 h' hi0 hh'
    rw [hS 0 h lo hi wt _ _ t hh.ne hlohi hwt ht (weighted_integrable hwt ht hh (uF.mono_set (sub h)))
        (weighted_integrable hwt ht hh (uFz.mono_set (sub h))),
      hS 0 h' lo hi wt _ _ t hh'.ne hlohi hwt ht (weighted_integrable hwt ht hh' (wF.mono_set (sub h')))
        (weighted_integrable hwt ht hh' (wFz.mono_set (sub h'))), ← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [key] with r hr hmem
    have e := (hr hmem).1
    show ((wt r * t r : ℝ) : ℂ) * sideTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) 0 h
      = (frameSign a : ℂ) * (((wt r * t r : ℝ) : ℂ) * sideTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) 0 h')
    rw [e]
    ring
  · have hint : ∀ (η : ℤ × ℤ) (k : ℝ), 0 < k →
        IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * planeGrad η G a 2 p)
            (Icc lo hi ×ˢ Icc (min 0 k) (max 0 k)) ∧
          IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * planeSlope η H a 2 2 p)
            (Icc lo hi ×ˢ Icc (min 0 k) (max 0 k)) := by
      intro η k hk
      unfold IsAxisAdmissibleTest at hadm
      rcases hadm with hlo0 | ⟨rfl, t₀, ht₀c, ht₀⟩
      · obtain ⟨-, hL2⟩ := hL Γ P v G H g hp η a lo hi 0 k hlo0 hlohi hk
        exact ⟨weighted_integrable hwt ht hk (hL2 2 2).1, weighted_integrable hwt ht hk (hL2 2 2).2⟩
      · obtain ⟨-, i1, i2⟩ := hA Γ P v G H g hp η a 2 2 hi 0 k hi0 hk
        exact ⟨axis_weighted_integrable hk ht₀c (fun r => ht₀ r) i1,
          axis_weighted_integrable hk ht₀c (fun r => ht₀ r) i2⟩
    obtain ⟨iF, iFz⟩ := hint (flipLabel ξ) h hh
    obtain ⟨jF, jFz⟩ := hint ξ h' hh'
    rw [hS 0 h lo hi wt _ _ t hh.ne hlohi hwt ht iF iFz, hS 0 h' lo hi wt _ _ t hh'.ne hlohi hwt ht jF jFz,
      ← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [key] with r hr hmem
    have e := (hr hmem).2
    show ((wt r * t r : ℝ) : ℂ)
        * sideTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) 0 h
      = -((frameSign a : ℂ) * (((wt r * t r : ℝ) : ℂ)
        * sideTrace (planeVelHeight ξ G a r) (planeVelHeight2 ξ H a r) 0 h'))
    rw [e]
    ring

end Breakdown.CertCell.SideTrace

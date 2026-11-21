import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge

namespace Internal

theorem norm_real_mul_add_le (a b : ℝ) (x y : ℂ) :
    ‖(a : ℂ) * x + (b : ℂ) * y‖ ≤ |a| * ‖x‖ + |b| * ‖y‖ := by
  calc _ ≤ ‖(a : ℂ) * x‖ + ‖(b : ℂ) * y‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

theorem sideTrace_eq_below (f fd : ℝ → ℂ) {c s : ℝ} (hs : s < c) :
    sideTrace f fd c s = ∫ r in Icc s c,
      ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r) := by
  simp only [sideTrace, edgeSign, if_pos hs, one_mul, min_eq_right hs.le, max_eq_left hs.le]

theorem sideTrace_eq_restrict (f fd : ℝ → ℂ) {c s b : ℝ} (hs0 : 0 ≤ s) (hs : s < c) (hcb : c ≤ b) :
    sideTrace f fd c s = ∫ r in Icc 0 b, (Icc s c).indicator (fun r =>
      ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r)) r := by
  rw [sideTrace_eq_below f fd hs, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr (Icc_subset_Icc hs0 hcb)]

theorem sideTrace_tendsto_axis (f fd : ℝ → ℂ) {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hW : ∀ lo, 0 < lo → HasWeakDerivOn f fd lo b) (hf : IntegrableOn f (Ioo 0 b))
    (hfd : IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ) * fd r) (Ioo 0 b)) :
    Tendsto (fun s => sideTrace f fd c s) (𝓝[>] 0) (𝓝 (sideTrace f fd c 0)) := by
  have hf' : IntegrableOn f (Icc 0 b) := (integrableOn_Icc_iff_integrableOn_Ioo).mpr hf
  have hfd' : IntegrableOn (fun r : ℝ => ((r : ℝ) : ℂ) * fd r) (Icc 0 b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).mpr hfd
  set F : ℝ → ℝ → ℂ := fun s => (Icc s c).indicator (fun r =>
      ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r)) with hF
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (c / 2) := Ioo_mem_nhdsGT (half_pos hc)
  have hlim : Tendsto (fun s => ∫ r in Icc 0 b, F s r) (𝓝[>] 0) (𝓝 (∫ r in Icc 0 b, F 0 r)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => 2 / c * (‖f r‖ + ‖((r : ℝ) : ℂ) * fd r‖)) ?_ ?_ ?_ ?_
    · filter_upwards [hev] with s hs
      have hsub : Icc s c ⊆ Ioo (s / 2) b := fun r hr =>
        ⟨by linarith [hr.1, hs.1], lt_of_le_of_lt hr.2 hcb⟩
      have hsub' : Icc s c ⊆ Ioo 0 b := fun r hr =>
        ⟨by linarith [hr.1, hs.1], lt_of_le_of_lt hr.2 hcb⟩
      have hfdI : IntegrableOn fd (Icc s c) := ((hW (s / 2) (by linarith [hs.1])).2.1).mono_set hsub
      have hfI : IntegrableOn f (Icc s c) := hf.mono_set hsub'
      have hg : IntegrableOn (fun r =>
          ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r)) (Icc s c) := by
        refine Integrable.add (hfI.const_mul _) ?_
        exact IntegrableOn.continuousOn_mul (by fun_prop) hfdI isCompact_Icc
      exact ((integrable_indicator_iff measurableSet_Icc).mpr hg).aestronglyMeasurable.restrict
    · filter_upwards [hev] with s hs
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_)
      have hB : 0 ≤ 2 / c * (‖f r‖ + ‖((r : ℝ) : ℂ) * fd r‖) := by positivity
      by_cases hrs : r ∈ Icc s c
      · have hcs : 0 < c - s := by linarith [hs.2]
        have h1 : 1 / (c - s) ≤ 2 / c := by
          rw [div_le_div_iff₀ hcs hc]; linarith [hs.2]
        have h2 : (r - s) / (c - s) ≤ 2 / c * r := by
          rw [div_le_iff₀ hcs]
          have : 2 / c * r * (c - s) = r * (2 * (c - s) / c) := by field_simp
          rw [this]
          have h3 : 1 ≤ 2 * (c - s) / c := by rw [le_div_iff₀ hc]; linarith [hs.2]
          nlinarith [hr.1, hs.1]
        have h4 : 0 ≤ (r - s) / (c - s) := div_nonneg (by linarith [hrs.1]) hcs.le
        simp only [hF, indicator_of_mem hrs]
        refine (norm_real_mul_add_le _ _ _ _).trans ?_
        rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / (c - s) by positivity), abs_of_nonneg h4]
        calc 1 / (c - s) * ‖f r‖ + (r - s) / (c - s) * ‖fd r‖
            ≤ 2 / c * ‖f r‖ + 2 / c * r * ‖fd r‖ := by
              gcongr
          _ = 2 / c * (‖f r‖ + ‖((r : ℝ) : ℂ) * fd r‖) := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]; ring
      · simp only [hF, indicator_of_notMem hrs, norm_zero]
        exact hB
    · exact ((hf'.norm.add hfd'.norm).const_mul _)
    · have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
        have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
        exact measure_eq_zero_iff_ae_notMem.mp this
      refine ae_restrict_of_ae (hne.mono fun r hr0 => ?_)
      by_cases hrc : r ≤ c
      · rcases lt_or_gt_of_ne hr0 with hneg | hpos
        · have hnot : ∀ s, 0 ≤ s → r ∉ Icc s c := fun s hs hmem => by linarith [hmem.1]
          have hfun : ∀ᶠ s in 𝓝[>] (0 : ℝ), F s r = 0 := by
            filter_upwards [self_mem_nhdsWithin] with s hs
            simp only [hF, indicator_of_notMem (hnot s (le_of_lt hs))]
          simp only [hF, indicator_of_notMem (hnot 0 le_rfl)]
          exact tendsto_const_nhds.congr' (hfun.mono fun s hs => hs.symm)
        · have hfun : ∀ᶠ s in 𝓝[>] (0 : ℝ), F s r =
              ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r) := by
            filter_upwards [Ioo_mem_nhdsGT hpos] with s hs
            simp only [hF, indicator_of_mem (show r ∈ Icc s c from ⟨hs.2.le, hrc⟩)]
          have hat : F 0 r = ((((1 / (c - 0)) : ℝ) : ℂ) * f r + (((r - 0) / (c - 0) : ℝ) : ℂ) * fd r) := by
            simp only [hF, indicator_of_mem (show r ∈ Icc 0 c from ⟨hpos.le, hrc⟩)]
          rw [hat]
          refine Tendsto.congr' (EventuallyEq.symm hfun) (tendsto_nhdsWithin_of_tendsto_nhds ?_)
          have hcont : ContinuousAt (fun s : ℝ =>
              ((((1 / (c - s)) : ℝ) : ℂ) * f r + (((r - s) / (c - s) : ℝ) : ℂ) * fd r)) 0 := by
            have hc0 : c - 0 ≠ 0 := by simpa using hc.ne'
            fun_prop (disch := exact hc0)
          exact hcont.tendsto
      · have hnot : ∀ s, r ∉ Icc s c := fun s hmem => hrc hmem.2
        simp only [hF, indicator_of_notMem (hnot _)]
        exact tendsto_const_nhds
  have heq : (fun s => ∫ r in Icc 0 b, F s r) =ᶠ[𝓝[>] 0] fun s => sideTrace f fd c s := by
    filter_upwards [hev] with s hs
    rw [sideTrace_eq_restrict f fd hs.1.le (by linarith [hs.2]) hcb.le]
  rw [sideTrace_eq_restrict f fd le_rfl hc hcb.le]
  exact hlim.congr' heq

theorem sideTrace_eq_of_pos (hM : SideTraceMatchHolds) (f fd : ℝ → ℂ) {c o o' b : ℝ}
    (ho : 0 < o) (ho' : 0 < o') (hco : c ≠ o) (hco' : c ≠ o') (hc : 0 < c)
    (hb : max c (max o o') < b) (hW : ∀ lo, 0 < lo → HasWeakDerivOn f fd lo b) :
    sideTrace f fd c o = sideTrace f fd c o' := by
  have hm : 0 < min c (min o o') := lt_min hc (lt_min ho ho')
  exact hM f fd c o o' (min c (min o o') / 2) b hco hco' (by linarith) hb
    (hW _ (by linarith))

end Internal

theorem axisSideTrace (hM : SideTraceMatchHolds) : AxisSideTraceHolds := by
  intro f fd c o' b hc ho' hco' hb hW hf hfd
  have hcb : c < b := lt_of_le_of_lt (le_max_left _ _) hb
  have hc2 : c ≠ c / 2 := by intro h; linarith
  have hmid : ∀ s, 0 < s → s < c → sideTrace f fd c s = sideTrace f fd c (c / 2) := by
    intro s hs hsc
    refine Internal.sideTrace_eq_of_pos hM f fd hs (half_pos hc) (ne_of_gt hsc) hc2 hc ?_ hW
    refine max_lt hcb (max_lt (by linarith) (by linarith))
  have hlim := Internal.sideTrace_tendsto_axis f fd hc hcb hW hf hfd
  have h0 : sideTrace f fd c 0 = sideTrace f fd c (c / 2) := by
    have hev : (fun _ : ℝ => sideTrace f fd c (c / 2)) =ᶠ[𝓝[>] 0] fun s => sideTrace f fd c s := by
      filter_upwards [Ioo_mem_nhdsGT hc] with s hs using (hmid s hs.1 hs.2).symm
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev)
  rcases ho'.eq_or_lt with h | h
  · rw [← h]
  · rw [h0]
    refine Internal.sideTrace_eq_of_pos hM f fd (half_pos hc) h hc2 hco' hc ?_ hW
    exact max_lt hcb (max_lt (by linarith) (lt_of_le_of_lt (le_max_right _ _) hb))

end SideTrace

end CertCell

end Breakdown

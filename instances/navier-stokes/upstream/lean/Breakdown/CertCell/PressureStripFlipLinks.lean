import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula CellCert.CellAnalysis Bridge

namespace Internal

theorem weak_integrableOn_Icc {f fd : ℝ → ℂ}
    (hw : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f fd zlo zhi) (a b : ℝ) :
    IntegrableOn f (Icc a b) ∧ IntegrableOn fd (Icc a b) := by
  have h := hw (min a b - 1) (max a b + 1) (by linarith [min_le_max (a := a) (b := b)])
  have hsub : Icc a b ⊆ Ioo (min a b - 1) (max a b + 1) := fun x hx =>
    ⟨by linarith [hx.1, min_le_left a b], by linarith [hx.2, le_max_right a b]⟩
  exact ⟨h.1.mono_set hsub, h.2.1.mono_set hsub⟩

theorem weak_intervalIntegrable {f fd : ℝ → ℂ}
    (hw : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f fd zlo zhi) (a b : ℝ) :
    IntervalIntegrable fd volume a b :=
  ⟨(weak_integrableOn_Icc hw a b).2.mono_set Ioc_subset_Icc_self,
    (weak_integrableOn_Icc hw b a).2.mono_set Ioc_subset_Icc_self⟩

theorem sideTrace_split (f fd : ℝ → ℂ) (c o : ℝ) (hf : IntegrableOn f (Icc (min c o) (max c o)))
    (hfd : IntegrableOn fd (Icc (min c o) (max c o))) :
    sideTrace f fd c o = edgeSign c o * ((((1 / (c - o)) : ℝ) : ℂ) * ∫ r in Icc (min c o) (max c o), f r)
      + edgeSign c o * ∫ r in Icc (min c o) (max c o), (((r - o) / (c - o) : ℝ) : ℂ) * fd r := by
  unfold sideTrace
  rw [integral_add (hf.const_mul _), integral_const_mul, mul_add]
  exact hfd.continuousOn_mul (by fun_prop) isCompact_Icc

theorem weighted_norm_le (fd : ℝ → ℂ) (a b c o : ℝ) (hab : a ≤ b) (hfd : IntegrableOn fd (Icc a b))
    (hw : ∀ r ∈ Icc a b, |(r - o) / (c - o)| ≤ 1) :
    ‖∫ r in Icc a b, (((r - o) / (c - o) : ℝ) : ℂ) * fd r‖ ≤ ∫ r in a..b, ‖fd r‖ := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine norm_integral_le_of_norm_le hfd.norm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw r hr)

theorem line_flip (f1 fd1 f2 fd2 : ℝ → ℂ) (h h' : ℝ) (hh : 0 < h) (hh' : 0 < h')
    (hM : SideTraceMatchHolds)
    (hw1 : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f1 fd1 zlo zhi)
    (hw2 : ∀ zlo zhi : ℝ, zlo < zhi → HasWeakDerivOn f2 fd2 zlo zhi)
    (hfl : ∀ᵐ z ∂(volume.restrict (Ioi (0 : ℝ))), f1 z = f2 (-z)) :
    sideTrace f1 fd1 0 h = sideTrace f2 fd2 0 h' := by
  set k : ℝ → ℝ := fun x => (∫ r in (0 : ℝ)..x, ‖fd1 r‖) - ∫ r in (0 : ℝ)..(-x), ‖fd2 r‖ with hk
  have hkc : Continuous k := by
    have c1 := intervalIntegral.continuous_primitive (fun a b => (weak_intervalIntegrable hw1 a b).norm) 0
    have c2 := intervalIntegral.continuous_primitive (fun a b => (weak_intervalIntegrable hw2 a b).norm) 0
    exact c1.sub (c2.comp continuous_neg)
  have hk0 : k 0 = 0 := by simp [hk]
  have hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖sideTrace f1 fd1 0 h - sideTrace f2 fd2 0 h'‖ ≤ k ε := by
    intro ε hε hε1
    have e1 : sideTrace f1 fd1 0 h = sideTrace f1 fd1 0 ε :=
      hM f1 fd1 0 h ε (-1) (h + 2) hh.ne hε.ne
        (lt_min (by norm_num) (lt_min (by linarith) (by linarith)))
        (max_lt (by linarith) (max_lt (by linarith) (by linarith))) (hw1 _ _ (by linarith))
    have e2 : sideTrace f2 fd2 0 h' = sideTrace f2 fd2 0 (-ε) :=
      hM f2 fd2 0 h' (-ε) (-2) (h' + 1) hh'.ne (ne_of_gt (by linarith))
        (lt_min (by norm_num) (lt_min (by linarith) (by linarith)))
        (max_lt (by linarith) (max_lt (by linarith) (by linarith))) (hw2 _ _ (by linarith))
    have m1 : min (0 : ℝ) ε = 0 := min_eq_left hε.le
    have M1 : max (0 : ℝ) ε = ε := max_eq_right hε.le
    have m2 : min (0 : ℝ) (-ε) = -ε := min_eq_right (by linarith)
    have M2 : max (0 : ℝ) (-ε) = 0 := max_eq_left (by linarith)
    have s1 := sideTrace_split f1 fd1 0 ε (by rw [m1, M1]; exact (weak_integrableOn_Icc hw1 0 ε).1)
      (by rw [m1, M1]; exact (weak_integrableOn_Icc hw1 0 ε).2)
    have s2 := sideTrace_split f2 fd2 0 (-ε) (by rw [m2, M2]; exact (weak_integrableOn_Icc hw2 (-ε) 0).1)
      (by rw [m2, M2]; exact (weak_integrableOn_Icc hw2 (-ε) 0).2)
    rw [m1, M1] at s1
    rw [m2, M2] at s2
    have es1 : edgeSign 0 ε = -1 := by simp [edgeSign, not_lt.mpr hε.le]
    have es2 : edgeSign 0 (-ε) = 1 := by simp [edgeSign, hε]
    have hS : ∫ r in Icc (-ε) 0, f2 r = ∫ r in Icc 0 ε, f1 r := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hε.le]
      have hc := intervalIntegral.integral_comp_neg (a := 0) (b := ε) f2
      rw [neg_zero] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hfl] with x hx hmem
      rw [Set.uIoc_of_le hε.le] at hmem
      exact (hx hmem.1).symm
    have b1 := weighted_norm_le fd1 0 ε 0 ε hε.le (weak_integrableOn_Icc hw1 0 ε).2 (fun r hr => by
      rw [abs_div, div_le_one (abs_pos.mpr (sub_ne_zero.mpr hε.ne)), abs_of_nonpos (by linarith [hr.2]),
        abs_of_neg (by linarith)]
      linarith [hr.1])
    have b2 := weighted_norm_le fd2 (-ε) 0 0 (-ε) (by linarith) (weak_integrableOn_Icc hw2 (-ε) 0).2
      (fun r hr => by
        rw [abs_div, div_le_one (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (by linarith)))),
          abs_of_nonneg (by linarith [hr.1]), abs_of_pos (by linarith)]
        linarith [hr.2])
    have hsym : ∫ r in (-ε)..0, ‖fd2 r‖ = -∫ r in (0 : ℝ)..(-ε), ‖fd2 r‖ := intervalIntegral.integral_symm _ _
    rw [e1, e2, s1, s2, es1, es2, hS]
    have hc : ((1 / (0 - ε) : ℝ) : ℂ) = -((1 / (0 - -ε) : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    set T1 := ∫ r in Icc 0 ε, (((r - ε) / (0 - ε) : ℝ) : ℂ) * fd1 r
    set T2 := ∫ r in Icc (-ε) 0, (((r - -ε) / (0 - -ε) : ℝ) : ℂ) * fd2 r
    have halg : -1 * (-((1 / (0 - -ε) : ℝ) : ℂ) * ∫ r in Icc 0 ε, f1 r) + -1 * T1
        - (1 * (((1 / (0 - -ε) : ℝ) : ℂ) * ∫ r in Icc 0 ε, f1 r) + 1 * T2) = -(T1 + T2) := by ring
    rw [halg, norm_neg]
    refine (norm_add_le _ _).trans ?_
    simp only [hk]
    linarith
  have htk : Tendsto k (𝓝[>] 0) (𝓝 0) := by
    have := (hkc.continuousAt (x := 0)).tendsto
    rw [hk0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖sideTrace f1 fd1 0 h - sideTrace f2 fd2 0 h'‖ ≤ k ε := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε using hbound ε hε.1 hε.2
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto htk hev))

theorem weighted_strip_integrable (G : ℝ × ℝ → ℂ) (lo hi zlo zhi : ℝ) (wt t : ℝ → ℝ)
    (hadm : IsAxisAdmissibleTest lo (fun r => wt r * t r)) (hwt : Continuous wt) (ht : Continuous t)
    (hplain : 0 < lo → IntegrableOn G (Icc lo hi ×ˢ Icc zlo zhi))
    (hweighted : IntegrableOn (fun p => (p.1 : ℂ) * G p) (Icc 0 hi ×ˢ Icc zlo zhi)) :
    IntegrableOn (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * G p) (Icc lo hi ×ˢ Icc zlo zhi) := by
  rcases hadm with hlo | ⟨rfl, t₀, ht₀, hrt⟩
  · exact (hplain hlo).continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  · have he : (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * G p)
        = fun p => ((t₀ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) * G p) := by
      funext p
      have hp := hrt p.1
      simp only at hp
      rw [hp]
      push_cast
      ring
    rw [he]
    exact hweighted.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)

end Internal

theorem pressureStripFlip (hD : PressureModeDerivHolds) (hI : PressureModeIntegrableHolds)
    (hF : PressurePlaneFlipHolds) (hS : HeightStripTraceHolds) (hM : SideTraceMatchHolds) :
    PressureStripFlipHolds := by
  intro m Q q hm hQ hsq hflipQ n lo hi h h' wt t hadm hlohi hh hh' hwt ht
  have hlo : 0 ≤ lo := by
    rcases hadm with h0 | ⟨h0, _⟩
    · exact h0.le
    · exact h0.ge
  have hhi : 0 < hi := lt_of_le_of_lt hlo hlohi
  have intF : ∀ (k : ℤ) (c : ℝ), 0 < c →
      IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * presMode m k q p.1 p.2)
        (Icc lo hi ×ˢ Icc (min 0 c) (max 0 c)) := by
    intro k c hc
    rw [min_eq_left hc.le, max_eq_right hc.le]
    have hk := ((hI m Q q hm hQ hsq k 2 hi 0 c hhi hc).1).mono_set
      (prod_mono (Icc_subset_Icc_left hlo) le_rfl)
    exact hk.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  have intD : ∀ (k : ℤ) (c : ℝ), 0 < c →
      IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) * modeVec m k Q p.1 p.2 2)
        (Icc lo hi ×ˢ Icc (min 0 c) (max 0 c)) := by
    intro k c hc
    rw [min_eq_left hc.le, max_eq_right hc.le]
    have hk := hI m Q q hm hQ hsq k 2 hi 0 c hhi hc
    exact Internal.weighted_strip_integrable (fun p => modeVec m k Q p.1 p.2 2) lo hi 0 c wt t hadm hwt ht
      (fun hl => hk.2.2 lo hl hlohi) hk.2.1
  rw [hS 0 h lo hi wt (fun p => presMode m (-n) q p.1 p.2) (fun p => modeVec m (-n) Q p.1 p.2 2) t
      hh.ne hlohi hwt ht (intF (-n) h hh) (intD (-n) h hh),
    hS 0 h' lo hi wt (fun p => presMode m n q p.1 p.2) (fun p => modeVec m n Q p.1 p.2 2) t
      hh'.ne hlohi hwt ht (intF n h' hh') (intD n h' hh')]
  have hDm := (hD m Q q hm hQ hsq (-n)).2
  have hDp := (hD m Q q hm hQ hsq n).2
  have hFl := hF m Q q hm hQ hsq hflipQ (-n)
  simp only [neg_neg] at hFl
  have hFl2 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ z ∂(volume.restrict (Ioi (0 : ℝ))),
      presMode m n q r (-z) = presMode m (-n) q r z := by
    have e : volume.restrict Breakdown.CertCell.halfPlane
        = (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      rfl
    rw [e] at hFl
    exact Measure.ae_ae_of_ae_prod hFl
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hDm, (ae_restrict_iff' measurableSet_Ioi).1 hDp,
    (ae_restrict_iff' measurableSet_Ioi).1 hFl2] with r h1 h2 h3 hmem
  have hr : (0 : ℝ) < r := lt_of_le_of_lt hlo hmem.1
  congr 1
  exact Internal.line_flip _ _ _ _ h h' hh hh' hM (h1 hr) (h2 hr)
    (by filter_upwards [h3 hr] with z hz using hz.symm)

end SideTrace

end CertCell

end Breakdown

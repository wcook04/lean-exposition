import Breakdown.FracCell.CylinderFlux
import Breakdown.FracCell.ModeRadialPartsF
import Breakdown.FracCell.ModeStripIntegrable

open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CellCert.CellFormula.Internal.StripTrace

open Breakdown.CellCert.CellAnalysis.ModeRadialLineInternal

theorem st_iterated {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ r in Icc a b, ∫ z in Icc c d, f (r, z) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod f hf

theorem st_sliceInt {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    IntegrableOn (fun r => ∫ z in Icc c d, f (r, z)) (Icc a b) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left

theorem st_sliceAe {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ r ∂(volume.restrict (Icc a b)), IntegrableOn (fun z => f (r, z)) (Icc c d) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.prod_right_ae

theorem st_primSwap {D : ℝ → ℂ} {a b : ℝ} (hD : IntegrableOn D (Icc a b)) :
    ∫ r in Icc a b, (∫ t in a..r, D t) = ∫ t in Icc a b, ((b - t : ℝ) : ℂ) * D t := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  set k : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => D p.2) with hk
  have hDi : Integrable (fun p : ℝ × ℝ => D p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    Integrable.comp_snd hD _
  have hki : Integrable k ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    hDi.indicator (measurableSet_le measurable_snd measurable_fst)
  have hswap := integral_integral_swap (μ := volume.restrict (Icc a b)) (ν := volume.restrict (Icc a b))
    (f := fun r t => k (r, t)) hki
  have h1 : ∀ r ∈ Icc a b, ∫ t, k (r, t) ∂(volume.restrict (Icc a b)) = ∫ t in a..r, D t := by
    intro r hr
    have e : (fun t => k (r, t)) = Set.indicator (Iic r) D := by
      funext t
      by_cases ht : t ≤ r <;> simp [hk, Set.indicator, ht]
    have hs : Iic r ∩ Icc a b = Icc a r := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hr.2⟩
    rw [e, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, hs,
      intervalIntegral.integral_of_le hr.1, integral_Icc_eq_integral_Ioc]
  have h2 : ∀ t ∈ Icc a b, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) = ((b - t : ℝ) : ℂ) * D t := by
    intro t ht
    have e : (fun r => k (r, t)) = Set.indicator (Ici t) (fun _ => D t) := by
      funext r
      by_cases hr : t ≤ r <;> simp [hk, Set.indicator, hr]
    have hs : Ici t ∩ Icc a b = Icc t b := by
      ext r; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ht.1.trans h1, h2⟩
    rw [e, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hs,
      setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 ht.2),
      Complex.real_smul]
  calc ∫ r in Icc a b, (∫ t in a..r, D t)
      = ∫ r, ∫ t, k (r, t) ∂(volume.restrict (Icc a b)) ∂(volume.restrict (Icc a b)) :=
        setIntegral_congr_fun measurableSet_Icc (fun r hr => (h1 r hr).symm)
    _ = ∫ t, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) ∂(volume.restrict (Icc a b)) := hswap
    _ = ∫ t in Icc a b, ((b - t : ℝ) : ℂ) * D t := setIntegral_congr_fun measurableSet_Icc h2

theorem st_affine {D : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hD : IntegrableOn D (Icc a b)) (T0 : ℂ)
    (α β : ℝ) :
    ∫ r in Icc a b, ((α : ℂ) * (T0 + ∫ t in a..r, D t) + ((α * r + β : ℝ) : ℂ) * D r)
      = ((α * b + β : ℝ) : ℂ) * (T0 + ∫ t in a..b, D t) - ((α * a + β : ℝ) : ℂ) * T0 := by
  have hK : IsCompact (Icc a b) := isCompact_Icc
  have hP : ContinuousOn (fun r => ∫ t in a..r, D t) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b)
      (f := D) (by rw [uIcc_of_le hab]; exact hD)
    rwa [uIcc_of_le hab] at h
  have i0 : IntegrableOn (fun _ : ℝ => T0) (Icc a b) := continuousOn_const.integrableOn_Icc
  have iP : IntegrableOn (fun r => ∫ t in a..r, D t) (Icc a b) := hP.integrableOn_Icc
  have i1 : IntegrableOn (fun r => (α : ℂ) * (T0 + ∫ t in a..r, D t)) (Icc a b) :=
    (i0.add iP).const_mul _
  have i2 : IntegrableOn (fun r => ((α * r + β : ℝ) : ℂ) * D r) (Icc a b) :=
    hD.continuousOn_mul (g := fun r : ℝ => ((α * r + β : ℝ) : ℂ)) (Continuous.continuousOn (by fun_prop)) hK
  have i3 : IntegrableOn (fun t => ((b - t : ℝ) : ℂ) * D t) (Icc a b) :=
    hD.continuousOn_mul (g := fun t : ℝ => ((b - t : ℝ) : ℂ)) (Continuous.continuousOn (by fun_prop)) hK
  have hIab : ∫ t in a..b, D t = ∫ t in Icc a b, D t := by
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have e0 : ∫ _ in Icc a b, T0 = ((b - a : ℝ) : ℂ) * T0 := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
      Complex.real_smul]
  have e1 : ∫ r in Icc a b, (α : ℂ) * (T0 + ∫ t in a..r, D t)
      = (α : ℂ) * (((b - a : ℝ) : ℂ) * T0) + ∫ t in Icc a b, (α : ℂ) * (((b - t : ℝ) : ℂ) * D t) := by
    rw [integral_const_mul, integral_add i0 iP, e0, st_primSwap hD, integral_const_mul, mul_add]
  have e2 : (∫ t in Icc a b, (α : ℂ) * (((b - t : ℝ) : ℂ) * D t))
      + ∫ t in Icc a b, ((α * t + β : ℝ) : ℂ) * D t = ((α * b + β : ℝ) : ℂ) * ∫ t in Icc a b, D t := by
    calc _ = ∫ t in Icc a b, ((α : ℂ) * (((b - t : ℝ) : ℂ) * D t) + ((α * t + β : ℝ) : ℂ) * D t) :=
          (integral_add (i3.const_mul (α : ℂ)) i2).symm
      _ = ∫ t in Icc a b, ((α * b + β : ℝ) : ℂ) * D t := by
          refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
          push_cast
          ring
      _ = _ := integral_const_mul _ _
  rw [integral_add i1 i2, e1, hIab]
  have e3 : ((α * b + β : ℝ) : ℂ) * (T0 + ∫ t in Icc a b, D t) - ((α * a + β : ℝ) : ℂ) * T0
      = (α : ℂ) * (((b - a : ℝ) : ℂ) * T0) + ((α * b + β : ℝ) : ℂ) * ∫ t in Icc a b, D t := by
    push_cast; ring
  rw [e3]
  linear_combination e2

theorem st_core {F dF : ℝ × ℝ → ℂ} {z₁ z₂ : ℝ}
    (hFi : ∀ R, IntegrableOn F (Icc 0 R ×ˢ Icc z₁ z₂))
    (hdFi : ∀ R, IntegrableOn dF (Icc 0 R ×ˢ Icc z₁ z₂))
    (hw : ∀ N : ℝ, 0 < N → ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ 0 = 0 → ψ N = 0 →
      ∫ p in Icc 0 N ×ˢ Icc z₁ z₂, ((ψ p.1 * 1 : ℝ) : ℂ) * dF p =
        -∫ p in Icc 0 N ×ˢ Icc z₁ z₂, ((deriv ψ p.1 * 1 : ℝ) : ℂ) * F p) :
    ∃ T : ℝ → ℂ, ∀ a b : ℝ, 0 ≤ a → a < b → ∀ α β : ℝ,
      ∫ p in Icc a b ×ˢ Icc z₁ z₂, ((α : ℂ) * F p + ((α * p.1 + β : ℝ) : ℂ) * dF p)
        = ((α * b + β : ℝ) : ℂ) * T b - ((α * a + β : ℝ) : ℂ) * T a := by
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun r => ∫ z in Icc z₁ z₂, F (r, z) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℂ, D = fun r => ∫ z in Icc z₁ z₂, dF (r, z) := ⟨_, rfl⟩
  have hSi : ∀ R, IntegrableOn S (Icc 0 R) := fun R => by rw [hS]; exact st_sliceInt (hFi R)
  have hDi : ∀ R, IntegrableOn D (Icc 0 R) := fun R => by rw [hD]; exact st_sliceInt (hdFi R)
  have hDii : ∀ R s t : ℝ, 0 ≤ s → s ≤ t → t ≤ R → IntervalIntegrable D volume s t := by
    intro R s t hs hst htR
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).2
      ((hDi R).mono_set (Icc_subset_Icc hs htR))
  have key : ∀ N : ℝ, 0 < N → ∃ L : ℂ, ∀ᵐ r ∂(volume.restrict (Icc 0 N)),
      S r = L - ∫ t in r..N, D t := by
    intro N hN
    refine line_core 0 N hN S D (hSi N) (fun x' hx' => (hDi N).mono_set (Icc_subset_Icc_left hx'.le)) ?_
    intro k x y hx1 hx2 hy1 hy2
    have hψ0 : test k x y 0 = 0 := test_left k hx1.le hy1.le
    have hψN : test k x y N = 0 := test_right k hx2.le hy2.le
    have h := hw N hN (test k x y) (test_contDiff k x y) hψ0 hψN
    have hK : IsCompact (Icc (0 : ℝ) N ×ˢ Icc z₁ z₂) := isCompact_Icc.prod isCompact_Icc
    have iA : IntegrableOn (fun p : ℝ × ℝ => ((test k x y p.1 * 1 : ℝ) : ℂ) * dF p)
        (Icc 0 N ×ˢ Icc z₁ z₂) :=
      (hdFi N).continuousOn_mul (g := fun p : ℝ × ℝ => ((test k x y p.1 * 1 : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (((test_cont k x y).comp continuous_fst).mul
          continuous_const)).continuousOn hK
    have iB : IntegrableOn (fun p : ℝ × ℝ => ((deriv (test k x y) p.1 * 1 : ℝ) : ℂ) * F p)
        (Icc 0 N ×ˢ Icc z₁ z₂) :=
      (hFi N).continuousOn_mul (g := fun p : ℝ × ℝ => ((deriv (test k x y) p.1 * 1 : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (((test_deriv_cont k x y).comp continuous_fst).mul
          continuous_const)).continuousOn hK
    rw [st_iterated iA, st_iterated iB] at h
    simp only [mul_one, integral_const_mul] at h
    have iC : IntegrableOn (fun r => ((deriv (test k x y) r : ℝ) : ℂ) * S r) (Icc 0 N) :=
      (hSi N).continuousOn_mul (g := fun r : ℝ => ((deriv (test k x y) r : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (test_deriv_cont k x y)).continuousOn isCompact_Icc
    have iD : IntegrableOn (fun r => ((test k x y r : ℝ) : ℂ) * D r) (Icc 0 N) :=
      (hDi N).continuousOn_mul (g := fun r : ℝ => ((test k x y r : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (test_cont k x y)).continuousOn isCompact_Icc
    rw [integral_add iC iD]
    have h' : ∫ r in Icc 0 N, ((test k x y r : ℝ) : ℂ) * D r
        = -∫ r in Icc 0 N, ((deriv (test k x y) r : ℝ) : ℂ) * S r := by
      rw [hS, hD]; exact h
    rw [h', add_neg_cancel]
  obtain ⟨L1, hL1⟩ := key 1 one_pos
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℂ, ∀ r, T r = (L1 - ∫ t in (0 : ℝ)..1, D t) + ∫ t in (0 : ℝ)..r, D t :=
    ⟨_, fun r => rfl⟩
  have hsplit : ∀ R r : ℝ, 0 ≤ r → r ≤ R → ∫ t in r..R, D t = (∫ t in (0 : ℝ)..R, D t) - ∫ t in (0 : ℝ)..r, D t :=
    fun R r h0 hr => (intervalIntegral.integral_interval_sub_left (hDii R 0 R le_rfl (h0.trans hr) le_rfl)
      (hDii R 0 r le_rfl h0 hr)).symm
  have hcN : ∀ N : ℝ, 1 ≤ N → ∀ᵐ r ∂(volume.restrict (Icc 0 N)), S r = T r := by
    intro N hN1
    obtain ⟨LN, hLN⟩ := key N (by linarith)
    have hc : LN - ∫ t in (0 : ℝ)..N, D t = L1 - ∫ t in (0 : ℝ)..1, D t := by
      have h1 : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) 1)), S r = LN - ∫ t in r..N, D t :=
        ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hN1) hLN
      have : (ae (volume.restrict (Icc (0 : ℝ) 1))).NeBot := ae_neBot.2 (by
        rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; norm_num)
      obtain ⟨r, hr1, hrN, hrm⟩ := (hL1.and (h1.and (ae_restrict_mem measurableSet_Icc))).exists
      rw [hsplit N r hrm.1 (hrm.2.trans hN1)] at hrN
      rw [hsplit 1 r hrm.1 hrm.2] at hr1
      linear_combination hr1 - hrN
    filter_upwards [hLN, ae_restrict_mem measurableSet_Icc] with r hr hmem
    rw [hr, hsplit N r hmem.1 hmem.2, hT, ← hc]
    ring
  refine ⟨T, ?_⟩
  intro a b ha hab α β
  have hb1 : 1 ≤ max b 1 := le_max_right _ _
  have hbM : b ≤ max b 1 := le_max_left _ _
  have hK : IsCompact (Icc a b ×ˢ Icc z₁ z₂) := isCompact_Icc.prod isCompact_Icc
  have hsub : Icc a b ×ˢ Icc z₁ z₂ ⊆ Icc 0 (max b 1) ×ˢ Icc z₁ z₂ :=
    prod_mono (Icc_subset_Icc ha hbM) subset_rfl
  have hFab := (hFi (max b 1)).mono_set hsub
  have hdFab := (hdFi (max b 1)).mono_set hsub
  have iI : IntegrableOn (fun p : ℝ × ℝ => (α : ℂ) * F p + ((α * p.1 + β : ℝ) : ℂ) * dF p)
      (Icc a b ×ˢ Icc z₁ z₂) :=
    (hFab.const_mul _).add (hdFab.continuousOn_mul (g := fun p : ℝ × ℝ => ((α * p.1 + β : ℝ) : ℂ))
      (Continuous.continuousOn (by fun_prop)) hK)
  have hST : ∀ᵐ r ∂(volume.restrict (Icc a b)), S r = T r :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc ha hbM) (hcN (max b 1) hb1)
  have hTa : ∀ r, a ≤ r → r ≤ b → T r = T a + ∫ t in a..r, D t := by
    intro r har hrb
    rw [hT, hT, add_assoc, intervalIntegral.integral_add_adjacent_intervals
      (hDii (max b 1) 0 a le_rfl ha (hab.le.trans hbM)) (hDii (max b 1) a r ha har (hrb.trans hbM))]
  have e : ∫ r in Icc a b, ∫ z in Icc z₁ z₂, ((α : ℂ) * F (r, z) + ((α * (r, z).1 + β : ℝ) : ℂ) * dF (r, z))
      = ∫ r in Icc a b, ((α : ℂ) * (T a + ∫ t in a..r, D t) + ((α * r + β : ℝ) : ℂ) * D r) := by
    refine integral_congr_ae ?_
    filter_upwards [st_sliceAe hFab, st_sliceAe hdFab, hST, ae_restrict_mem measurableSet_Icc]
      with r h1 h2 h3 hr
    rw [integral_add (h1.const_mul _) (h2.const_mul _)]
    simp only [integral_const_mul]
    rw [← hTa r hr.1 hr.2, ← h3, hS, hD]
  rw [st_iterated iI]
  refine e.trans ?_
  rw [st_affine hab.le ((hDi (max b 1)).mono_set (Icc_subset_Icc ha hbM)), ← hTa b hab.le le_rfl]

end Breakdown.CellCert.CellFormula.Internal.StripTrace

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem stripTrace_holds : StripTraceStatement := by
  intro m v G H hs z₁ z₂ hz
  exact Internal.StripTrace.st_core (F := fun p => modeVec m 0 v p.1 p.2 0) (dF := gradMode m 0 G 0 0)
    (fun R => (modeStripIntegrable m v G H hs 0 R z₁ z₂).1 0)
    (fun R => (modeStripIntegrable m v G H hs 0 R z₁ z₂).2 0 0)
    (fun N hN ψ hψ h0 hN' => (Breakdown.CellCert.CellFormula.modeRadialParts m v G hs.measurable_velocity hs.velocity_six
      hs.measurable_gradient hs.gradient_two hs.weak_gradient 0 0 0 N z₁ z₂ le_rfl hN hz).2 ψ
        (fun _ => 1) hψ continuous_const h0 hN')

end Breakdown.CellCert.CellFormula

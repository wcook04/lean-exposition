import Mathlib

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow


private lemma integralIneq_cont {a T : ℝ} {φ b : ℝ → ℝ} (hT : 0 ≤ T)
    (hφ : ContinuousOn φ (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (h : ∀ t ∈ Icc 0 T, φ t ≤ a + ∫ s in (0 : ℝ)..t, b s * φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ a * Real.exp (∫ s in (0 : ℝ)..t, b s) := by
  have hbφ : ContinuousOn (fun s => b s * φ s) (Icc 0 T) := hb.mul hφ
  have hu : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT
  have hψc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, b s * φ s) (Icc 0 T) := by
    rw [← hu]
    exact intervalIntegral.continuousOn_primitive_interval (by rw [hu]; exact hbφ.integrableOn_Icc)
  have hEc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, b s) (Icc 0 T) := by
    rw [← hu]
    exact intervalIntegral.continuousOn_primitive_interval (by rw [hu]; exact hb.integrableOn_Icc)
  set G : ℝ → ℝ := fun t => (a + ∫ s in (0 : ℝ)..t, b s * φ s) *
    Real.exp (-(∫ s in (0 : ℝ)..t, b s)) with hG
  have hGc : ContinuousOn G (Icc 0 T) := (continuousOn_const.add hψc).mul hEc.neg.rexp
  have hint : interior (Icc (0 : ℝ) T) = Ioo 0 T := interior_Icc
  have hderiv : ∀ x ∈ Ioo 0 T, HasDerivAt G ((b x * φ x) * Real.exp (-(∫ s in (0 : ℝ)..x, b s)) +
      (a + ∫ s in (0 : ℝ)..x, b s * φ s) * (Real.exp (-(∫ s in (0 : ℝ)..x, b s)) * -(b x))) x := by
    intro x hx
    have hxI : Icc 0 T ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hsub : Icc 0 x ⊆ Icc 0 T := Icc_subset_Icc le_rfl hx.2.le
    have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, b s * φ s) (b x * φ x) x :=
      intervalIntegral.integral_hasDerivAt_right
        ((hbφ.mono hsub).intervalIntegrable_of_Icc hx.1.le)
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hbφ.mono Ioo_subset_Icc_self) x hx)
        (hbφ.continuousAt hxI)
    have h2 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, b s) (b x) x :=
      intervalIntegral.integral_hasDerivAt_right
        ((hb.mono hsub).intervalIntegrable_of_Icc hx.1.le)
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hb.mono Ioo_subset_Icc_self) x hx)
        (hb.continuousAt hxI)
    exact (h1.const_add a).mul h2.neg.exp
  have hanti : AntitoneOn G (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hGc
      (f' := fun x => (b x * φ x) * Real.exp (-(∫ s in (0 : ℝ)..x, b s)) +
        (a + ∫ s in (0 : ℝ)..x, b s * φ s) * (Real.exp (-(∫ s in (0 : ℝ)..x, b s)) * -(b x)))
      (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [hint] at hx
      exact (hderiv x hx).hasDerivWithinAt
    · rw [hint] at hx
      have hxI : x ∈ Icc 0 T := Ioo_subset_Icc_self hx
      have hle := h x hxI
      have hb' := hb0 x hxI
      have he := Real.exp_pos (-(∫ s in (0 : ℝ)..x, b s))
      nlinarith [mul_nonneg (mul_nonneg hb' he.le) (sub_nonneg.2 hle)]
  intro t ht
  have hGt : G t ≤ G 0 := hanti ⟨le_rfl, hT⟩ ht ht.1
  have hG0 : G 0 = a := by simp [hG]
  have hψ := h t ht
  have hsplit : a + ∫ s in (0 : ℝ)..t, b s * φ s = G t * Real.exp (∫ s in (0 : ℝ)..t, b s) := by
    simp only [hG]
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hepos := Real.exp_pos (∫ s in (0 : ℝ)..t, b s)
  calc φ t ≤ G t * Real.exp (∫ s in (0 : ℝ)..t, b s) := hsplit ▸ hψ
    _ ≤ a * Real.exp (∫ s in (0 : ℝ)..t, b s) := by
        rw [← hG0]
        exact mul_le_mul_of_nonneg_right hGt hepos.le

private lemma lintegral_kernel_eq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(2 / 3 : ℝ))) =
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) := by
  have hii : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(2 / 3 : ℝ))) volume 0 t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (r := -(2 / 3 : ℝ)) (a := t) (b := 0)
      (by norm_num)).comp_sub_left t
    simpa using h
  have hion : IntegrableOn (fun s : ℝ => (t - s) ^ (-(2 / 3 : ℝ))) (Ioo 0 t) :=
    (hii.1).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hion]
  · congr 1
    rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(2 / 3 : ℝ))) t]
    simp only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num)]
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact Real.rpow_nonneg (by linarith [hs.2]) _


private lemma rpow_pow_four (x : ℝ≥0∞) (r : ℝ) : (x ^ r) ^ 4 = x ^ (4 * r) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  ring_nf

private lemma lpProd_step {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Ioo 0 t)))
    (hg : AEMeasurable g (volume.restrict (Ioo 0 t))) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * f s * g s ≤
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∫⁻ s in Ioo 0 t, (f s * g s) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := (Real.holderConjugate_iff).2 ⟨by norm_num, by norm_num⟩
  have hk : AEMeasurable (fun s : ℝ => ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))))
      (volume.restrict (Ioo 0 t)) :=
    ((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal.aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo 0 t)) hpq hk (hf.mul hg)
  have hker : ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ^ (4 / 3 : ℝ) =
      ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) := by
    rw [← lintegral_kernel_eq ht]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
    have hts : 0 ≤ t - s := by linarith [hs.2]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hts _) (by norm_num),
      ← Real.rpow_mul hts]
    norm_num
  calc ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * f s * g s
      = ∫⁻ s in Ioo 0 t, ((fun s : ℝ => ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ)))) *
          (fun s => f s * g s)) s := by
        refine lintegral_congr (fun s => ?_)
        simp only [Pi.mul_apply, mul_assoc]
    _ ≤ _ := h
    _ = _ := by
        rw [hker]
        norm_num

theorem iterIntegral_bound (A C K T : ℝ) : ∃ B : ℝ, ∀ T' ∈ Icc 0 T, ∀ n w : ℝ → ℝ,
    ContinuousOn n (Icc 0 T') → ContinuousOn w (Icc 0 T') →
    (∀ t ∈ Icc 0 T', 0 ≤ n t) → (∀ t ∈ Icc 0 T', 0 ≤ w t) →
    ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4) ≤ ENNReal.ofReal K →
    (∀ t ∈ Icc 0 T', ENNReal.ofReal (n t) ≤ ENNReal.ofReal A + ENNReal.ofReal C *
      ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (w s) *
        ENNReal.ofReal (n s)) →
    ∀ t ∈ Icc 0 T', n t ≤ B := by
  set A' := max A 0 with hA'
  set C' := max C 0 with hC'
  set K' := max K 0 with hK'
  set c : ℝ := 3 * max T 0 ^ (1 / 3 : ℝ) with hc
  set D : ℝ := 8 * C' ^ 4 * c ^ (3 : ℝ) with hD
  set a : ℝ := 8 * A' ^ 4 with ha
  have hA0 : 0 ≤ A' := le_max_right _ _
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hK0 : 0 ≤ K' := le_max_right _ _
  have hc0 : 0 ≤ c := mul_nonneg (by norm_num) (Real.rpow_nonneg (le_max_right _ _) _)
  have hD0 : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 _))
    (Real.rpow_nonneg hc0 _)
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) (pow_nonneg hA0 _)
  refine ⟨max 1 (a * Real.exp (D * K')), ?_⟩
  intro T' hT' n w hn hw hn0 hw0 hW hmild
  have hT'0 : 0 ≤ T' := hT'.1
  have hφc : ContinuousOn (fun s => n s ^ 4) (Icc 0 T') := hn.pow 4
  have hbc : ContinuousOn (fun s => D * w s ^ 4) (Icc 0 T') := continuousOn_const.mul (hw.pow 4)
  have hbφc : ContinuousOn (fun s => w s ^ 4 * n s ^ 4) (Icc 0 T') := (hw.pow 4).mul (hn.pow 4)
  have hJ : ∀ t ∈ Icc 0 T', ∫⁻ s in Ioo 0 t, ENNReal.ofReal (w s ^ 4 * n s ^ 4) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, w s ^ 4 * n s ^ 4) := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 T' := Icc_subset_Icc le_rfl ht.2
    have hint : IntegrableOn (fun s => w s ^ 4 * n s ^ 4) (Ioo 0 t) :=
      ((hbφc.mono hsub).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs' : s ∈ Icc 0 T' := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _)
  have hstep : ∀ t ∈ Icc 0 T', n t ^ 4 ≤ a + ∫ s in (0 : ℝ)..t, D * w s ^ 4 * n s ^ 4 := by
    intro t ht
    have hsub : Ioo 0 t ⊆ Icc 0 T' := fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hfm : AEMeasurable (fun s => ENNReal.ofReal (w s)) (volume.restrict (Ioo 0 t)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hw.mono hsub)).aemeasurable measurableSet_Ioo
    have hgm : AEMeasurable (fun s => ENNReal.ofReal (n s)) (volume.restrict (Ioo 0 t)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn (hn.mono hsub)).aemeasurable measurableSet_Ioo
    have hH := lpProd_step ht.1 hfm hgm
    have hJeq : ∫⁻ s in Ioo 0 t, (ENNReal.ofReal (w s) * ENNReal.ofReal (n s)) ^ (4 : ℝ) =
        ∫⁻ s in Ioo 0 t, ENNReal.ofReal (w s ^ 4 * n s ^ 4) := by
      refine setLIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
      have hs' := hsub hs
      rw [← ENNReal.ofReal_mul (hw0 s hs'), ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (hw0 s hs') (hn0 s hs')) (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow]
    rw [hJeq, hJ t ht] at hH
    set J := ∫ s in (0 : ℝ)..t, w s ^ 4 * n s ^ 4 with hJdef
    have hkc : ENNReal.ofReal (3 * t ^ (1 / 3 : ℝ)) ≤ ENNReal.ofReal c := by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact Real.rpow_le_rpow ht.1 (ht.2.trans (hT'.2.trans (le_max_left _ _))) (by norm_num)
    have h1 : ENNReal.ofReal (n t) ≤ ENNReal.ofReal A' + ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ)) := by
      refine (hmild t ht).trans (add_le_add (ENNReal.ofReal_le_ofReal (le_max_left _ _)) ?_)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (hH.trans ?_)
      gcongr
    have h2 : ENNReal.ofReal (n t) ^ 4 ≤ 8 * (ENNReal.ofReal A' ^ 4 + (ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ))) ^ 4) := by
      have e4 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ 4 := fun x => by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      have := ENNReal.rpow_add_le_mul_rpow_add_rpow (ENNReal.ofReal A') (ENNReal.ofReal C' *
        (ENNReal.ofReal c ^ (3 / 4 : ℝ) * ENNReal.ofReal J ^ (1 / 4 : ℝ))) (p := 4) (by norm_num)
      rw [e4, e4, e4] at this
      have h8 : (2 : ℝ≥0∞) ^ ((4 : ℝ) - 1) = 8 := by
        rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        norm_num
      rw [h8] at this
      exact (pow_le_pow_left' h1 4).trans this
    have h3 : ENNReal.ofReal (n t ^ 4) ≤ ENNReal.ofReal (a + D * J) := by
      rw [ENNReal.ofReal_pow (hn0 t ht)]
      refine h2.trans (le_of_eq ?_)
      have hJ0 : 0 ≤ J := by
        rw [hJdef]
        refine intervalIntegral.integral_nonneg ht.1 (fun s hs => ?_)
        have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans ht.2⟩
        exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _)
      have eA : ENNReal.ofReal a = 8 * ENNReal.ofReal A' ^ 4 := by
        rw [ha, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hA0]
        norm_num
      have eD : ENNReal.ofReal D = 8 * ENNReal.ofReal C' ^ 4 * ENNReal.ofReal c ^ (3 : ℝ) := by
        rw [hD, ENNReal.ofReal_mul (mul_nonneg (by norm_num) (pow_nonneg hC0 _)),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hC0,
          ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num)]
        norm_num
      rw [ENNReal.ofReal_add ha0 (mul_nonneg hD0 hJ0), ENNReal.ofReal_mul hD0, eA, eD, mul_pow,
        mul_pow, rpow_pow_four, rpow_pow_four]
      norm_num
      ring
    have h4 := (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha0 (mul_nonneg hD0 (by
      rw [hJdef]
      refine intervalIntegral.integral_nonneg ht.1 (fun s hs => ?_)
      have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans ht.2⟩
      exact mul_nonneg (pow_nonneg (hw0 s hs') _) (pow_nonneg (hn0 s hs') _))))).1 h3
    refine h4.trans (le_of_eq ?_)
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  have hgr := integralIneq_cont (a := a) (φ := fun s => n s ^ 4) (b := fun s => D * w s ^ 4) hT'0
    hφc hbc (fun t ht => mul_nonneg hD0 (pow_nonneg (hw0 t ht) _)) hstep
  intro t ht
  have hwint : ∫ s in (0 : ℝ)..t, D * w s ^ 4 ≤ D * K' := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have hsub : Icc 0 t ⊆ Icc 0 T' := Icc_subset_Icc le_rfl ht.2
    have hint : IntegrableOn (fun s => w s ^ 4) (Ioc 0 t) :=
      (((hw.pow 4).mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, w s ^ 4 := intervalIntegral.integral_nonneg ht.1
      (fun s hs => pow_nonneg (hw0 s ⟨hs.1, hs.2.trans ht.2⟩) _)
    have hle : ENNReal.ofReal (∫ s in (0 : ℝ)..t, w s ^ 4) ≤ ENNReal.ofReal K' := by
      rw [intervalIntegral.integral_of_le ht.1, ofReal_integral_eq_lintegral_ofReal hint]
      · calc ∫⁻ s in Ioc 0 t, ENNReal.ofReal (w s ^ 4)
            ≤ ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4) :=
              lintegral_mono_set (Ioc_subset_Icc_self.trans hsub)
          _ ≤ ENNReal.ofReal K := hW
          _ ≤ ENNReal.ofReal K' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact pow_nonneg (hw0 s ⟨hs.1.le, hs.2.trans ht.2⟩) _
    exact (ENNReal.ofReal_le_ofReal_iff hK0).1 hle
  have h4 : n t ^ 4 ≤ a * Real.exp (D * K') :=
    (hgr t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hwint) ha0)
  by_cases h1 : n t ≤ 1
  · exact h1.trans (le_max_left _ _)
  · replace h1 := not_le.1 h1
    have : n t ≤ n t ^ 4 := by
      calc n t = n t ^ 1 := (pow_one _).symm
        _ ≤ n t ^ 4 := pow_le_pow_right₀ h1.le (by norm_num)
    exact this.trans (h4.trans (le_max_right _ _))

end Breakdown.SmoothFlow

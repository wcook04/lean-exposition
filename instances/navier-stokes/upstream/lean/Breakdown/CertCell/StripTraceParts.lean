import Breakdown.FracCell.SegmentIndependenceParts
import Breakdown.Weak.ConstOfWeakDeriv

open MeasureTheory Set Filter
open scoped ContDiff Topology Interval

noncomputable section

namespace Breakdown.CertCell.StripTrace

namespace Internal

theorem supported_integrable {f : ℝ → ℂ} {θ : ℝ → ℝ} {l u : ℝ} (hf : IntegrableOn f (Ioo l u))
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hts : ∀ x, x ∉ Ioo l u → θ x = 0) :
    Integrable (fun t => (θ t : ℂ) * f t) := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have h1 : Integrable (fun t => (θ t : ℂ) * (Ioo l u).indicator f t) :=
    ((integrable_indicator_iff measurableSet_Ioo).2 hf).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp hθ).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Complex.norm_real]; exact hC t)
  refine h1.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioo l u
  · simp [indicator_of_mem ht]
  · simp [hts t ht]

theorem weak_rep {f df : ℝ → ℂ} {l u : ℝ} (hlu : l < u) (hf : IntegrableOn f (Ioo l u))
    (hdf : IntegrableOn df (Ioo l u))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo l u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t) :
    ∃ c : ℂ, ∀ᵐ t ∂(volume.restrict (Ioo l u)), f t = c + ∫ τ in l..t, df τ := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo l u →
      ∫ t, deriv η t * L (f t) = ∫ t, η t * -(L (df t)) := by
    intro L η hη hc hts
    have z1 : ∀ x, x ∉ Ioo l u → η x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
    have z2 : ∀ x, x ∉ Ioo l u → deriv η x = 0 := fun x hx =>
      Function.notMem_support.1 (fun h => hx (hts (support_deriv_subset h)))
    have i1 := supported_integrable hf (hη.continuous_deriv (by simp)) hc.deriv z2
    have i2 := supported_integrable hdf hη.continuous hc z1
    have e := congrArg L (hw η hη hc hts)
    rw [← L.integral_comp_comm i1, L.map_neg, ← L.integral_comp_comm i2, ← integral_neg] at e
    have s : ∀ (s : ℝ) (w : ℂ), L ((s : ℂ) * w) = s * L w := fun s w => by
      rw [← Complex.real_smul, L.map_smul, smul_eq_mul]
    simp only [s] at e
    rw [e]
    congr 1
    funext t
    ring
  obtain ⟨c1, h1⟩ := WeakProfile.constOfWeakDeriv_holds (fun t => Complex.reCLM (f t))
    (fun t => -(Complex.reCLM (df t))) l u hlu (Complex.reCLM.integrable_comp hf)
    (Complex.reCLM.integrable_comp hdf).neg (key Complex.reCLM)
  obtain ⟨c2, h2⟩ := WeakProfile.constOfWeakDeriv_holds (fun t => Complex.imCLM (f t))
    (fun t => -(Complex.imCLM (df t))) l u hlu (Complex.imCLM.integrable_comp hf)
    (Complex.imCLM.integrable_comp hdf).neg (key Complex.imCLM)
  refine ⟨⟨c1, c2⟩, ?_⟩
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with t hr hi ht
  have hii : IntervalIntegrable df volume l t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).2 (hdf.mono_set (Ioc_subset_Ioo_right ht.2))
  have er := Complex.reCLM.intervalIntegral_comp_comm hii
  have ei := Complex.imCLM.intervalIntegral_comp_comm hii
  rw [intervalIntegral.integral_neg] at hr hi
  apply Complex.ext
  · simp only [Complex.reCLM_apply] at hr er
    rw [Complex.add_re, ← er, hr, sub_neg_eq_add]
  · simp only [Complex.imCLM_apply] at hi ei
    rw [Complex.add_im, ← ei, hi, sub_neg_eq_add]

theorem primitive_parts {D k k' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hD : IntegrableOn D (Ioc a b))
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') (c : ℂ) :
    ∫ x in a..b, (D x * k x + (c + ∫ s in a..x, D s) * k' x) = (c + ∫ s in a..b, D s) * k b - c * k a := by
  set μ := volume.restrict (Ioc a b) with hμ
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have hDμ : Integrable D μ := hD
  have hk'μ : Integrable k' μ := (hk'.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  set Kf : ℝ × ℝ → ℂ := indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => k' p.1 * D p.2) with hKf
  have hKi : Integrable Kf (μ.prod μ) :=
    (hk'μ.mul_prod hDμ).indicator (measurableSet_le measurable_snd measurable_fst)
  have inner : ∀ x ∈ Ioc a b, (∫ s in a..x, D s) * k' x = ∫ s, Kf (x, s) ∂μ := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.1.le]
    have : (fun s => Kf (x, s)) = indicator (Iic x) (fun s => k' x * D s) := by
      funext s
      simp [hKf, indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hx.2,
      integral_const_mul, mul_comm]
  have outer : ∀ s ∈ Ioc a b, ∫ x, Kf (x, s) ∂μ = D s * (k b - k s) := by
    intro s hs
    have : (fun x => Kf (x, s)) = indicator (Ici s) (fun x => k' x * D s) := by
      funext x
      simp [hKf, indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Ici, integral_mul_const]
    have hset : Ioc a b ∩ Ici s = Icc s b := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨by linarith [hs.1], h2⟩, h3⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hk x) (hk'.intervalIntegrable s b)]
    ring
  have hP : ∫ x in a..b, (∫ s in a..x, D s) * k' x = ∫ s in a..b, D s * (k b - k s) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      setIntegral_congr_fun measurableSet_Ioc inner,
      setIntegral_congr_fun measurableSet_Ioc fun s hs => (outer s hs).symm]
    exact integral_integral_swap (f := fun x s => Kf (x, s)) hKi
  have iD : IntervalIntegrable D volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hD
  have hPc : ContinuousOn (fun x => ∫ s in a..x, D s) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hab]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hD)
  have i1 : IntervalIntegrable (fun x => D x * k x) volume a b := iD.mul_continuousOn hkc.continuousOn
  have i3 : IntervalIntegrable (fun x => (∫ s in a..x, D s) * k' x) volume a b :=
    (hPc.mul hk'.continuousOn).intervalIntegrable
  have i4 : IntervalIntegrable (fun x => c * k' x) volume a b := (hk'.intervalIntegrable a b).const_mul c
  have i2 : IntervalIntegrable (fun x => (c + ∫ s in a..x, D s) * k' x) volume a b := by
    refine (i4.add i3).congr ?_
    intro x _
    simp only
    ring
  have i5 : IntervalIntegrable (fun x => D x * k b) volume a b := iD.mul_const _
  rw [intervalIntegral.integral_add i1 i2]
  have e2 : ∫ x in a..b, (c + ∫ s in a..x, D s) * k' x = c * (k b - k a) + ∫ x in a..b, (∫ s in a..x, D s) * k' x := by
    have : (fun x => (c + ∫ s in a..x, D s) * k' x) = fun x => c * k' x + (∫ s in a..x, D s) * k' x := by
      funext x
      ring
    rw [this, intervalIntegral.integral_add i4 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hk x) (hk'.intervalIntegrable a b)]
  have e3 : ∫ s in a..b, D s * (k b - k s) = (∫ s in a..b, D s) * k b - ∫ s in a..b, D s * k s := by
    have : (fun s => D s * (k b - k s)) = fun s => D s * k b - D s * k s := by
      funext s
      ring
    rw [this, intervalIntegral.integral_sub i5 i1, intervalIntegral.integral_mul_const]
  rw [e2, hP, e3]
  ring

end Internal

end Breakdown.CertCell.StripTrace

namespace Breakdown.CertCell.StripTrace

namespace Internal

theorem ramp_deriv (o d : ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (((x - o) / d : ℝ) : ℂ)) (((1 / d : ℝ)) : ℂ) x := by
  have h : HasDerivAt (fun x : ℝ => (x - o) / d) (1 / d) x := ((hasDerivAt_id x).sub_const o).div_const d
  exact h.ofReal_comp

theorem line_parts {f df g g' : ℝ → ℂ} {l a b u : ℝ} (hla : l < a) (hab : a < b) (hbu : b < u)
    (hf : IntegrableOn f (Ioo l u)) (hdf : IntegrableOn df (Ioo l u))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo l u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    ∫ x in a..b, (df x * g x + f x * g' x) =
      g b * (∫ x in a..b, ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x))
      + g a * (∫ x in a..b, ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) := by
  obtain ⟨c, hc⟩ := weak_rep (hla.trans (hab.trans hbu)) hf hdf hw
  set P : ℝ → ℂ := fun x => c + ∫ τ in l..x, df τ with hPd
  have hsub : ∀ {s t : ℝ}, l ≤ s → t < u → Ioc s t ⊆ Ioo l u := fun hs ht x hx =>
    ⟨lt_of_le_of_lt hs hx.1, lt_of_le_of_lt hx.2 ht⟩
  have hii : ∀ {s t : ℝ}, l ≤ s → s ≤ t → t < u → IntervalIntegrable df volume s t := fun hs hst ht =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 (hdf.mono_set (hsub hs ht))
  have hPa : ∀ x, a ≤ x → x < u → P x = P a + ∫ s in a..x, df s := by
    intro x hax hxu
    simp only [hPd]
    rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals (hii le_rfl hla.le (hab.trans hbu))
      (hii hla.le hax hxu)]
  have hae : ∀ᵐ x ∂volume, x ∈ Ι a b → f x = P a + ∫ s in a..x, df s := by
    have := (ae_restrict_iff' measurableSet_Ioo).1 hc
    filter_upwards [this] with x hx hxab
    rw [uIoc_of_le hab.le] at hxab
    rw [hx (hsub hla.le hbu hxab), ← hPa x hxab.1.le (lt_of_le_of_lt hxab.2 hbu)]
  have hDab : IntegrableOn df (Ioc a b) := hdf.mono_set (hsub hla.le hbu)
  have gen : ∀ k k' : ℝ → ℂ, (∀ x, HasDerivAt k (k' x) x) → Continuous k' →
      ∫ x in a..b, (df x * k x + f x * k' x) = P b * k b - P a * k a := by
    intro k k' hk hk'
    have e : ∫ x in a..b, (df x * k x + f x * k' x) =
        ∫ x in a..b, (df x * k x + (P a + ∫ s in a..x, df s) * k' x) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hxab
      rw [hx hxab]
    rw [e, primitive_parts hab.le hDab hk hk' (P a), ← hPa b hab.le hbu]
  have hb := gen _ _ (ramp_deriv a (b - a)) continuous_const
  have ha := gen _ _ (ramp_deriv b (a - b)) continuous_const
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne
  have e1 : (∫ x in a..b, ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x)) = P b := by
    rw [← mul_one (P b), ← sub_zero (P b * 1)]
    convert hb using 2
    · funext x
      ring
    · simp [div_self hba]
    · simp
  have e2 : (∫ x in a..b, ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) = -P a := by
    have : -P a = P b * 0 - P a * 1 := by ring
    rw [this]
    convert ha using 2
    · funext x
      ring
    · simp
    · simp [div_self hab']
  rw [gen g g' hg hg', e1, e2]
  ring

theorem not_integrable_inv {δ : ℝ} (hδ : 0 < δ) : ¬ IntegrableOn (fun t : ℝ => t⁻¹) (Ioo 0 δ) := by
  intro h
  have : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le]
    exact h
  rw [intervalIntegrable_inv_iff] at this
  rcases this with h1 | h1
  · exact hδ.ne h1
  · exact h1 (by simp [hδ.le])

theorem axis_line_parts {f df k k' : ℝ → ℂ} {b u : ℝ} (hb : 0 < b) (hbu : b < u)
    (hf : IntegrableOn f (Ioo 0 u)) (hrdf : IntegrableOn (fun r : ℝ => (r : ℂ) * df r) (Ioo 0 u))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t)
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') :
    ∫ x in (0 : ℝ)..b, (df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x)) =
      ((b : ℂ) * k b) * ∫ x in (0 : ℝ)..b, ((((1 / b : ℝ)) : ℂ) * f x + (((x / b) : ℝ) : ℂ) * df x) := by
  have hu : 0 < u := hb.trans hbu
  set h : ℝ → ℂ := fun x => (x : ℂ) * f x with hhd
  set dh : ℝ → ℂ := fun x => f x + (x : ℂ) * df x with hdhd
  have hhi : IntegrableOn h (Ioo 0 u) := by
    refine (hf.bdd_mul (c := u) (Complex.continuous_ofReal.aestronglyMeasurable) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
    exact hx.2.le
  have hdhi : IntegrableOn dh (Ioo 0 u) := hf.add hrdf
  have hwh : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * h t = -∫ t, (η t : ℂ) * dh t := by
    intro η hη hc hts
    set ρ : ℝ → ℝ := fun t => t * η t with hρd
    have hρ : ContDiff ℝ ∞ ρ := contDiff_id.mul hη
    have hρc : HasCompactSupport ρ := hc.mul_left
    have hρs : tsupport ρ ⊆ Ioo 0 u := (tsupport_mul_subset_right).trans hts
    have hdρ : ∀ t, deriv ρ t = η t + t * deriv η t := by
      intro t
      have := ((hasDerivAt_id t).mul ((hη.differentiable (by simp)) t).hasDerivAt).deriv
      simp only [id, one_mul] at this
      exact this
    have z1 : ∀ x, x ∉ Ioo 0 u → η x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
    have z2 : ∀ x, x ∉ Ioo 0 u → deriv η x = 0 := fun x hx =>
      Function.notMem_support.1 (fun h => hx (hts (support_deriv_subset h)))
    have z3 : ∀ x, x ∉ Ioo 0 u → x * deriv η x = 0 := fun x hx => by rw [z2 x hx, mul_zero]
    have hdc : Continuous (deriv η) := hη.continuous_deriv (by simp)
    have i1 := supported_integrable hf hη.continuous hc z1
    have i2 : Integrable (fun t => (((t * deriv η t : ℝ)) : ℂ) * f t) :=
      supported_integrable (θ := fun t => t * deriv η t) hf (continuous_id.mul hdc) (hc.deriv.mul_left) z3
    have i3 := supported_integrable hrdf hη.continuous hc z1
    have key := hw ρ hρ hρc hρs
    simp only [hdρ] at key
    have e1 : (fun t => (((η t + t * deriv η t : ℝ)) : ℂ) * f t) =
        fun t => (η t : ℂ) * f t + (((t * deriv η t : ℝ)) : ℂ) * f t := by
      funext t
      push_cast
      ring
    have e2 : (fun t => ((ρ t : ℝ) : ℂ) * df t) = fun t => (η t : ℂ) * ((t : ℂ) * df t) := by
      funext t
      simp only [hρd]
      push_cast
      ring
    rw [e1, e2, integral_add i1 i2] at key
    have e3 : (fun t => ((deriv η t : ℝ) : ℂ) * h t) = fun t => (((t * deriv η t : ℝ)) : ℂ) * f t := by
      funext t
      simp only [hhd]
      push_cast
      ring
    have e4 : (fun t => (η t : ℂ) * dh t) = fun t => (η t : ℂ) * f t + (η t : ℂ) * ((t : ℂ) * df t) := by
      funext t
      simp only [hdhd]
      ring
    rw [e3, e4, integral_add i1 i3]
    linear_combination key
  obtain ⟨c, hc⟩ := weak_rep hu hhi hdhi hwh
  have hc0 : c = 0 := by
    by_contra hne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hne
    have hPc : ContinuousOn (fun x => ∫ τ in (0 : ℝ)..x, dh τ) (Icc 0 u) := by
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := u) (μ := volume) (f := dh) (by
        rw [uIcc_of_le hu.le]
        exact (integrableOn_Icc_iff_integrableOn_Ioo).2 hdhi)
      rwa [uIcc_of_le hu.le] at this
    have hcw := hPc (0 : ℝ) ⟨le_rfl, hu.le⟩
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ0, hδ0, hδ⟩ := hcw (‖c‖ / 2) (by linarith)
    set δ := min δ0 u with hδd
    have hδp : 0 < δ := lt_min hδ0 hu
    have hbound : ∀ x ∈ Ioo 0 δ, ‖∫ τ in (0 : ℝ)..x, dh τ‖ < ‖c‖ / 2 := by
      intro x hx
      have hxu : x ∈ Icc 0 u := ⟨hx.1.le, hx.2.le.trans (min_le_right _ _)⟩
      have hd : dist x 0 < δ0 := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_left _ _)
      have := hδ hxu hd
      simpa using this
    apply not_integrable_inv hδp
    have hfδ : IntegrableOn f (Ioo 0 δ) := hf.mono_set (Ioo_subset_Ioo_right (min_le_right _ _))
    have hmeas : AEStronglyMeasurable (fun t : ℝ => t⁻¹) (volume.restrict (Ioo 0 δ)) :=
      measurable_inv.aestronglyMeasurable
    refine Integrable.mono' (hfδ.norm.const_mul (2 / ‖c‖)) hmeas ?_
    have hc' := (ae_restrict_iff' measurableSet_Ioo).1 hc
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hc'] with x hx hxe
    have hxu : x ∈ Ioo 0 u := ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
    have e := hxe hxu
    have hlow : ‖c‖ / 2 ≤ ‖h x‖ := by
      rw [e]
      have h1 := norm_sub_norm_le c (-(∫ τ in (0 : ℝ)..x, dh τ))
      rw [sub_neg_eq_add, norm_neg] at h1
      linarith [hbound x hx]
    have hhx : ‖h x‖ = x * ‖f x‖ := by
      simp only [hhd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx.1]
    rw [hhx] at hlow
    rw [inv_le_iff_one_le_mul₀' hx.1]
    have : 1 ≤ 2 / ‖c‖ * (x * ‖f x‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      linarith
    nlinarith [norm_nonneg (f x)]
  have hae : ∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) b → h x = 0 + ∫ s in (0 : ℝ)..x, dh s := by
    have := (ae_restrict_iff' measurableSet_Ioo).1 hc
    filter_upwards [this] with x hx hxb
    rw [uIoc_of_le hb.le] at hxb
    rw [hx ⟨hxb.1, lt_of_le_of_lt hxb.2 hbu⟩, hc0]
  have hDb : IntegrableOn dh (Ioc 0 b) := hdhi.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hbu⟩)
  have lhs : ∫ x in (0 : ℝ)..b, (df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x)) =
      (∫ s in (0 : ℝ)..b, dh s) * k b := by
    have e : ∫ x in (0 : ℝ)..b, (df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x)) =
        ∫ x in (0 : ℝ)..b, (dh x * k x + (0 + ∫ s in (0 : ℝ)..x, dh s) * k' x) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hxb
      rw [← hx hxb]
      simp only [hhd, hdhd]
      ring
    rw [e, primitive_parts hb.le hDb hk hk' 0]
    ring
  have rhs : ∫ x in (0 : ℝ)..b, ((((1 / b : ℝ)) : ℂ) * f x + (((x / b) : ℝ) : ℂ) * df x) =
      (((1 / b : ℝ)) : ℂ) * ∫ s in (0 : ℝ)..b, dh s := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp only [hdhd]
    push_cast
    ring
  rw [lhs, rhs]
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  field_simp

end Internal

end Breakdown.CertCell.StripTrace

namespace Breakdown.CertCell.StripTrace

namespace Internal

open Breakdown.CellCert.CellFormula

theorem sym_box (lo hi : ℝ) : Icc lo hi ⊆ Icc (-(|lo| + |hi|)) (|lo| + |hi|) := fun s hs =>
  ⟨by linarith [neg_abs_le lo, abs_nonneg hi, hs.1], by linarith [le_abs_self hi, abs_nonneg lo, hs.2]⟩

theorem prod_iter {G : ℝ × ℝ → ℂ} {s1 s2 : Set ℝ} (hG : IntegrableOn G (s1 ×ˢ s2)) :
    ∫ p in s1 ×ˢ s2, G p = ∫ x in s1, ∫ y in s2, G (x, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod G (Breakdown.FracInternal.SegmentParts.prod_int hG)

theorem slice_int {H : ℝ × ℝ → ℂ} {χ : ℝ → ℝ} {c d Z : ℝ} (hH : IntegrableOn H (Icc c d ×ˢ Icc (-Z) Z))
    (hχ : Continuous χ) :
    IntegrableOn (fun r => ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r, z)) (Icc c d) := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (χ p.2 : ℂ) * H p) (Icc c d ×ˢ Icc (-Z) Z) :=
    hH.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  exact (Breakdown.FracInternal.SegmentParts.prod_int h1).integral_prod_left

theorem slice_pair {H : ℝ × ℝ → ℂ} {θ χ : ℝ → ℝ} {c d Z : ℝ} (hH : IntegrableOn H (Icc c d ×ˢ Icc (-Z) Z))
    (hθ : Continuous θ) (hχ : Continuous χ) (hθs : ∀ x, x ∉ Icc c d → θ x = 0)
    (hχs : ∀ z, z ∉ Icc (-Z) Z → χ z = 0) :
    ∫ p, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = ∫ r, (θ r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r, z) := by
  have hz1 : ∀ p ∉ Icc c d ×ˢ Icc (-Z) Z, ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p = 0 := by
    intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc c d ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hθs _ h]
    · simp [hχs _ h]
  have hz2 : ∀ r ∉ Icc c d, (θ r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * H (r, z) = 0 := by
    intro r hr
    simp [hθs _ hr]
  have hint : IntegrableOn (fun p : ℝ × ℝ => ((θ p.1 * χ p.2 : ℝ) : ℂ) * H p) (Icc c d ×ˢ Icc (-Z) Z) :=
    hH.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2,
    prod_iter hint]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext z
  push_cast
  ring

theorem radial_slices {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {χ : ℝ → ℝ} {Z u : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : ∀ z, z ∉ Icc (-Z) Z → χ z = 0) :
    IntegrableOn (fun r => ∫ z in Icc (-Z) Z, (χ z : ℂ) * F (r, z)) (Ioo 0 u) ∧
    IntegrableOn (fun r : ℝ => (r : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * dF (r, z)) (Ioo 0 u) ∧
    (∀ δ, 0 < δ → IntegrableOn (fun r => ∫ z in Icc (-Z) Z, (χ z : ℂ) * dF (r, z)) (Ioo δ u)) ∧
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * (∫ z in Icc (-Z) Z, (χ z : ℂ) * F (t, z)) =
        -∫ t, (η t : ℂ) * ∫ z in Icc (-Z) Z, (χ z : ℂ) * dF (t, z) := by
  have hχc : Continuous χ := hχ.continuous
  refine ⟨(slice_int (h.1 u Z).1 hχc).mono_set Ioo_subset_Icc_self, ?_, fun δ hδ =>
    (slice_int (h.2.1 δ u Z hδ) hχc).mono_set Ioo_subset_Icc_self, ?_⟩
  · have := (slice_int (h.1 u Z).2 hχc).mono_set (Ioo_subset_Icc_self (a := (0 : ℝ)) (b := u))
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioo
    simp only
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  · intro η hη hc hts
    obtain ⟨δ, hδ, R, hR⟩ := Breakdown.FracInternal.CornerParts.pos_bound hc (fun r hr => (hts hr).1)
    have hηs : ∀ x, x ∉ Icc δ u → η x = 0 := by
      intro x hx
      by_cases hx1 : x ∈ Ioo 0 u
      · exact hR x (fun hm => hx ⟨hm.1, hx1.2.le⟩)
      · exact image_eq_zero_of_notMem_tsupport (fun hm => hx1 (hts hm))
    have hdηs : ∀ x, x ∉ Icc 0 u → deriv η x = 0 := fun x hx =>
      Function.notMem_support.1 (fun hm => hx (Ioo_subset_Icc_self (hts (support_deriv_subset hm))))
    have hχcs : HasCompactSupport χ := HasCompactSupport.intro isCompact_Icc hχs
    set ψ : ℝ × ℝ → ℝ := fun q => η q.1 * χ q.2 with hψd
    have hψ : ContDiff ℝ ∞ ψ := (hη.comp contDiff_fst).mul (hχ.comp contDiff_snd)
    have hψc : HasCompactSupport ψ := by
      refine HasCompactSupport.intro (hc.isCompact.prod hχcs.isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport η ∧ q.2 ∈ tsupport χ) from hq) with h' | h'
      · simp [hψd, image_eq_zero_of_notMem_tsupport h']
      · simp [hψd, image_eq_zero_of_notMem_tsupport h']
    have hψp : ∀ q ∈ tsupport ψ, 0 < q.1 := by
      intro q hq
      have hsub : tsupport ψ ⊆ Icc δ u ×ˢ univ := by
        refine closure_minimal ?_ (isClosed_Icc.prod isClosed_univ)
        intro q' hq'
        refine ⟨?_, trivial⟩
        by_contra hm
        exact hq' (by simp [hψd, hηs _ hm])
      exact lt_of_lt_of_le hδ (hsub hq).1.1
    have key := h.2.2 ψ hψ hψc hψp
    have hfd := fun q => Breakdown.FracInternal.CornerParts.fderiv_prod_apply
      (hη.differentiable (by simp)) (hχ.differentiable (by simp)) q
    simp only [hψd, (hfd _).1] at key
    rw [slice_pair (h.1 u Z).1 (hη.continuous_deriv (by simp)) hχc hdηs hχs,
      slice_pair (h.2.1 δ u Z hδ) hη.continuous hχc hηs hχs] at key
    exact key

theorem radial_line {f df k k' : ℝ → ℂ} {a b u : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbu : b < u)
    (hf : IntegrableOn f (Ioo 0 u)) (hrdf : IntegrableOn (fun r : ℝ => (r : ℂ) * df r) (Ioo 0 u))
    (hdf : ∀ δ, 0 < δ → IntegrableOn df (Ioo δ u))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 u →
      ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t)
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') :
    ∫ x in Icc a b, ((df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x))
      - ((b : ℂ) * k b) * ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x)
      - ((a : ℂ) * k a) * ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have hsub : Ioc a b ⊆ Ioo 0 u := fun x hx => ⟨lt_of_le_of_lt ha hx.1, lt_of_le_of_lt hx.2 hbu⟩
  have hfab : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hf.mono_set hsub)
  have hrab : IntervalIntegrable (fun x : ℝ => (x : ℂ) * df x) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hrdf.mono_set hsub)
  have i1 : IntervalIntegrable (fun x => df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x)) volume a b := by
    refine ((hrab.mul_continuousOn hkc.continuousOn).add
      (hfab.mul_continuousOn (hkc.add (Complex.continuous_ofReal.mul hk')).continuousOn)).congr ?_
    intro x _
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have i2 : IntervalIntegrable (fun x => ((b : ℂ) * k b) *
        ((((1 / (b - 0) : ℝ)) : ℂ) * f x + (((x - 0) / (b - 0) : ℝ) : ℂ) * df x)) volume 0 b := by
      refine ((hfab.const_mul ((((1 / b : ℝ)) : ℂ))).add (hrab.const_mul ((((1 / b : ℝ)) : ℂ)))).const_mul
        ((b : ℂ) * k b) |>.congr ?_
      intro x _
      simp only [sub_zero]
      push_cast
      ring
    have e : ∀ x : ℝ, ((df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x))
        - ((b : ℂ) * k b) * ((((1 / (b - 0) : ℝ)) : ℂ) * f x + (((x - 0) / (b - 0) : ℝ) : ℂ) * df x)
        - ((((0 : ℝ)) : ℂ) * k 0) * ((((1 / (0 - b) : ℝ)) : ℂ) * f x + (((x - b) / (0 - b) : ℝ) : ℂ) * df x)) =
        (df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x))
          - ((b : ℂ) * k b) * ((((1 / (b - 0) : ℝ)) : ℂ) * f x + (((x - 0) / (b - 0) : ℝ) : ℂ) * df x) := by
      intro x
      simp
    simp_rw [e]
    rw [intervalIntegral.integral_sub i1 i2, axis_line_parts hab hbu hf hrdf hw hk hk',
      intervalIntegral.integral_const_mul]
    simp only [sub_zero]
    ring
  · have hf' : IntegrableOn f (Ioo (a / 2) u) := hf.mono_set (Ioo_subset_Ioo_left (by linarith))
    have hdf' : IntegrableOn df (Ioo (a / 2) u) := hdf (a / 2) (by linarith)
    have hw' : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo (a / 2) u →
        ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t := fun η h1 h2 h3 =>
      hw η h1 h2 (h3.trans (Ioo_subset_Ioo_left (by linarith)))
    have hg : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * k x) (k x + (x : ℂ) * k' x) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
      exact (h1.mul (hk x)).congr_deriv (by ring)
    have L : ∫ x in a..b, (df x * ((x : ℂ) * k x) + f x * (k x + (x : ℂ) * k' x)) =
        ((b : ℂ) * k b) * (∫ x in a..b, ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x))
        + ((a : ℂ) * k a) * (∫ x in a..b, ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) :=
      line_parts (by linarith : a / 2 < a) hab hbu hf' hdf' hw' hg (hkc.add (Complex.continuous_ofReal.mul hk'))
    have hdfab : IntervalIntegrable df volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
        ((hdf a hpos).mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hbu⟩))
    have i2 : IntervalIntegrable (fun x => ((b : ℂ) * k b) *
        ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x)) volume a b :=
      ((hfab.const_mul _).add (hdfab.continuousOn_mul (Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn)).const_mul _
    have i3 : IntervalIntegrable (fun x => ((a : ℂ) * k a) *
        ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) volume a b :=
      ((hfab.const_mul _).add (hdfab.continuousOn_mul (Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)).continuousOn)).const_mul _
    rw [intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2, L,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring

end Internal

end Breakdown.CertCell.StripTrace

namespace Breakdown.CertCell.StripTrace

namespace Internal

open Breakdown.CellCert.CellFormula

theorem bounded_box {K : Set ℝ} (hK : IsCompact K) : ∃ Z : ℝ, K ⊆ Icc (-Z) Z := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => ?_⟩
  have := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩

theorem slice_core {F dF : ℝ × ℝ → ℂ} {α β t : ℝ → ℂ} {a b lo hi : ℝ}
    (hα : Continuous α)
    (hF : ∀ Z, IntegrableOn F (Icc a b ×ˢ Icc (-Z) Z))
    (hdF : ∀ Z, IntegrableOn (fun p => β p.1 * dF p) (Icc a b ×ˢ Icc (-Z) Z))
    (h1 : ∀ (χ : ℝ → ℝ) (Z : ℝ), ContDiff ℝ ∞ χ → (∀ z, z ∉ Icc (-Z) Z → χ z = 0) →
      ∫ r in Icc a b, (α r * (∫ z in Icc (-Z) Z, (χ z : ℂ) * F (r, z))
        + β r * ∫ z in Icc (-Z) Z, (χ z : ℂ) * dF (r, z)) = 0) :
    ∫ p in Icc a b ×ˢ Icc lo hi, t p.2 * (α p.1 * F p + β p.1 * dF p) = 0 := by
  set E : ℝ × ℝ → ℂ := fun p => α p.1 * F p + β p.1 * dF p with hEd
  have hE : ∀ Z, IntegrableOn E (Icc a b ×ˢ Icc (-Z) Z) := fun Z =>
    ((hF Z).continuousOn_mul (hα.comp continuous_fst).continuousOn (isCompact_Icc.prod isCompact_Icc)).add (hdF Z)
  set Φ : ℝ × ℝ → ℂ := (Icc a b ×ˢ (univ : Set ℝ)).indicator E with hΦd
  have hΦs : ∀ p : ℝ × ℝ, p.1 ∉ Icc a b → Φ p = 0 := fun p hp =>
    indicator_of_notMem (fun hm => hp hm.1) _
  have hΦE : ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → Φ p = E p := fun p hp =>
    indicator_of_mem (show p ∈ Icc a b ×ˢ (univ : Set ℝ) from ⟨hp, trivial⟩) _
  have hint : ∀ K, IsCompact K → IntegrableOn Φ (Icc a b ×ˢ K) := by
    intro K hK
    obtain ⟨Z, hZ⟩ := bounded_box hK
    refine ((hE Z).mono_set (prod_mono le_rfl hZ)).congr_fun (fun p hp => (hΦE p hp.1).symm)
      (measurableSet_Icc.prod hK.measurableSet)
  have hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∫ p, (χ p.2 : ℂ) * Φ p = 0 := by
    intro χ hχs hχc
    obtain ⟨Z, hZ⟩ := Breakdown.FracInternal.CornerParts.sym_bound hχc
    have hz : ∀ p ∉ Icc a b ×ˢ Icc (-Z) Z, (χ p.2 : ℂ) * Φ p = 0 := by
      intro p hp
      rcases not_and_or.1 (show ¬ (p.1 ∈ Icc a b ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
      · rw [hΦs p h, mul_zero]
      · rw [hZ _ h]; simp
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hcongr : ∫ p in Icc a b ×ˢ Icc (-Z) Z, (χ p.2 : ℂ) * Φ p = ∫ p in Icc a b ×ˢ Icc (-Z) Z, (χ p.2 : ℂ) * E p :=
      setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => by simp only [hΦE p hp.1])
    have hχE : IntegrableOn (fun p : ℝ × ℝ => (χ p.2 : ℂ) * E p) (Icc a b ×ˢ Icc (-Z) Z) :=
      (hE Z).continuousOn_mul (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_snd)).continuousOn
        (isCompact_Icc.prod isCompact_Icc)
    rw [hcongr, prod_iter hχE]
    have i1 : Integrable (fun p : ℝ × ℝ => (χ p.2 : ℂ) * (α p.1 * F p))
        ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-Z) Z))) := by
      refine Breakdown.FracInternal.SegmentParts.prod_int ?_
      exact ((hF Z).continuousOn_mul (hα.comp continuous_fst).continuousOn (isCompact_Icc.prod isCompact_Icc)).continuousOn_mul
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_snd)).continuousOn (isCompact_Icc.prod isCompact_Icc)
    have i2 : Integrable (fun p : ℝ × ℝ => (χ p.2 : ℂ) * (β p.1 * dF p))
        ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-Z) Z))) := by
      refine Breakdown.FracInternal.SegmentParts.prod_int ?_
      exact (hdF Z).continuousOn_mul
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_snd)).continuousOn (isCompact_Icc.prod isCompact_Icc)
    rw [← h1 χ Z hχs hZ]
    refine integral_congr_ae ?_
    filter_upwards [i1.prod_right_ae, i2.prod_right_ae] with r hr1 hr2
    simp only [hEd]
    have e : (fun z => (χ z : ℂ) * (α r * F (r, z) + β r * dF (r, z))) =
        fun z => (χ z : ℂ) * (α r * F (r, z)) + (χ z : ℂ) * (β r * dF (r, z)) := by
      funext z
      ring
    rw [e, integral_add hr1 hr2]
    have e1 : (fun z => (χ z : ℂ) * (α r * F (r, z))) = fun z => α r * ((χ z : ℂ) * F (r, z)) := by
      funext z
      ring
    have e2 : (fun z => (χ z : ℂ) * (β r * dF (r, z))) = fun z => β r * ((χ z : ℂ) * dF (r, z)) := by
      funext z
      ring
    rw [e1, e2, integral_const_mul, integral_const_mul]
  have hmain := Breakdown.FracInternal.SegmentParts.snd_slice measurableSet_Icc hΦs hint hχ t (A := Icc lo hi)
  rw [← hmain]
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
  simp only [hΦE p hp.1, hEd]

end Internal

open Internal Breakdown.CellCert.CellFormula

theorem radial_parts {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {a b lo hi : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {k k' t : ℝ → ℂ} (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => (dF p * ((p.1 : ℂ) * k p.1) + F p * (k p.1 + (p.1 : ℂ) * k' p.1)) * t p.2)
      (Icc a b ×ˢ Icc lo hi) ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p) * t p.2)
      (Icc a b ×ˢ Icc lo hi) ∧
    ∫ p in Icc a b ×ˢ Icc lo hi, (dF p * ((p.1 : ℂ) * k p.1) + F p * (k p.1 + (p.1 : ℂ) * k' p.1)) * t p.2 =
      ((b : ℂ) * k b) * (∫ p in Icc a b ×ˢ Icc lo hi,
          ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p) * t p.2)
      + ((a : ℂ) * k a) * (∫ p in Icc a b ×ˢ Icc lo hi,
          ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p) * t p.2) := by
  set u : ℝ := b + 1 with hud
  have hbu : b < u := by linarith
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have hsub : ∀ Z : ℝ, Icc a b ×ˢ Icc (-Z) Z ⊆ Icc 0 u ×ˢ Icc (-Z) Z := fun Z =>
    prod_mono (Icc_subset_Icc ha hbu.le) le_rfl
  have hcpt : ∀ Z : ℝ, IsCompact (Icc a b ×ˢ Icc (-Z) Z) := fun Z => isCompact_Icc.prod isCompact_Icc
  have hFZ : ∀ Z, IntegrableOn F (Icc a b ×ˢ Icc (-Z) Z) := fun Z => ((h.1 u Z).1).mono_set (hsub Z)
  have hrZ : ∀ Z (v : ℝ → ℂ), Continuous v →
      IntegrableOn (fun p : ℝ × ℝ => ((p.1 : ℂ) * v p.1) * dF p) (Icc a b ×ˢ Icc (-Z) Z) := by
    intro Z v hv
    refine IntegrableOn.congr_fun ((((h.1 u Z).2).mono_set (hsub Z)).continuousOn_mul (hv.comp continuous_fst).continuousOn (hcpt Z))
      (fun p _ => by simp only [Function.comp_apply]; ring) (measurableSet_Icc.prod measurableSet_Icc)
  set cb : ℂ := (b : ℂ) * k b with hcb
  set ca : ℂ := (a : ℂ) * k a with hca
  set Sb : ℝ × ℝ → ℂ := fun p => (((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.1 - a) / (b - a) : ℝ) : ℂ) * dF p with hSb
  set Sa : ℝ × ℝ → ℂ := fun p => (((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.1 - b) / (a - b) : ℝ) : ℂ) * dF p with hSa
  set Lf : ℝ × ℝ → ℂ := fun p => dF p * ((p.1 : ℂ) * k p.1) + F p * (k p.1 + (p.1 : ℂ) * k' p.1) with hLf
  set α : ℝ → ℂ := fun r => (k r + (r : ℂ) * k' r) - cb * (((1 / (b - a) : ℝ)) : ℂ) - ca * (((1 / (a - b) : ℝ)) : ℂ)
    with hαd
  set β : ℝ → ℂ := fun r => (r : ℂ) * k r - cb * (((r - a) / (b - a) : ℝ) : ℂ) - ca * (((r - b) / (a - b) : ℝ) : ℂ)
    with hβd
  have hα : Continuous α := by
    simp only [hαd]
    exact ((hkc.add (Complex.continuous_ofReal.mul hk')).sub continuous_const).sub continuous_const
  have hpt : ∀ p : ℝ × ℝ, Lf p - cb * Sb p - ca * Sa p = α p.1 * F p + β p.1 * dF p := by
    intro p
    simp only [hLf, hSb, hSa, hαd, hβd]
    ring
  have hLi : ∀ Z, IntegrableOn Lf (Icc a b ×ˢ Icc (-Z) Z) := by
    intro Z
    refine IntegrableOn.congr_fun ((hrZ Z k hkc).add ((hFZ Z).continuousOn_mul
      ((hkc.add (Complex.continuous_ofReal.mul hk')).comp continuous_fst).continuousOn (hcpt Z)))
      (fun p _ => by simp only [hLf, Function.comp_apply, Pi.add_apply, Pi.mul_apply]; ring)
      (measurableSet_Icc.prod measurableSet_Icc)
  have hcases : (∀ Z, IntegrableOn (fun p => β p.1 * dF p) (Icc a b ×ˢ Icc (-Z) Z)) ∧
      (∀ Z, IntegrableOn Sb (Icc a b ×ˢ Icc (-Z) Z)) ∧
      (∀ Z, IntegrableOn (fun p => ca * Sa p) (Icc a b ×ˢ Icc (-Z) Z)) := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0
      have hca0 : ca = 0 := by simp [hca]
      refine ⟨fun Z => ?_, fun Z => ?_, fun Z => ?_⟩
      · refine IntegrableOn.congr_fun (hrZ Z (fun r => k r - cb * (((1 / b : ℝ)) : ℂ))
          (hkc.sub continuous_const)) (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [hβd, hca0, sub_zero, zero_mul]
        push_cast
        ring
      · refine IntegrableOn.congr_fun (((hFZ Z).const_mul ((((1 / b : ℝ)) : ℂ))).add (hrZ Z (fun _ => (((1 / b : ℝ)) : ℂ))
          continuous_const)) (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [hSb, sub_zero, Pi.add_apply]
        push_cast
        ring
      · refine IntegrableOn.congr_fun integrableOn_zero (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp [hca0]
    · have hdFZ : ∀ Z (v : ℝ → ℂ), Continuous v →
          IntegrableOn (fun p : ℝ × ℝ => v p.1 * dF p) (Icc a b ×ˢ Icc (-Z) Z) := by
        intro Z v hv
        exact (((h.2.1 a u Z hpos).mono_set (prod_mono (Icc_subset_Icc le_rfl hbu.le) le_rfl)).continuousOn_mul
          (hv.comp continuous_fst).continuousOn (hcpt Z))
      have hramp : ∀ o d : ℝ, Continuous (fun r : ℝ => (((r - o) / d : ℝ) : ℂ)) := fun o d =>
        Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const d)
      refine ⟨fun Z => ?_, fun Z => ?_, fun Z => ?_⟩
      · exact hdFZ Z β (((Complex.continuous_ofReal.mul hkc).sub (continuous_const.mul (hramp a (b - a)))).sub
          (continuous_const.mul (hramp b (a - b))))
      · exact ((hFZ Z).const_mul _).add (hdFZ Z _ (hramp a (b - a)))
      · exact (((hFZ Z).const_mul _).add (hdFZ Z _ (hramp b (a - b)))).const_mul ca
  obtain ⟨hβi, hSbi, hSai⟩ := hcases
  set Z0 : ℝ := |lo| + |hi| with hZ0
  have hsub0 : Icc a b ×ˢ Icc lo hi ⊆ Icc a b ×ˢ Icc (-Z0) Z0 := prod_mono le_rfl (sym_box lo hi)
  have hcpt0 : IsCompact (Icc a b ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  have htc : ContinuousOn (fun p : ℝ × ℝ => t p.2) (Icc a b ×ˢ Icc lo hi) := (ht.comp continuous_snd).continuousOn
  have iL : IntegrableOn (fun p => Lf p * t p.2) (Icc a b ×ˢ Icc lo hi) :=
    ((hLi Z0).mono_set hsub0).mul_continuousOn htc hcpt0
  have iSb : IntegrableOn (fun p => Sb p * t p.2) (Icc a b ×ˢ Icc lo hi) :=
    ((hSbi Z0).mono_set hsub0).mul_continuousOn htc hcpt0
  have iSa : IntegrableOn (fun p => (ca * Sa p) * t p.2) (Icc a b ×ˢ Icc lo hi) :=
    ((hSai Z0).mono_set hsub0).mul_continuousOn htc hcpt0
  refine ⟨iL, iSb, ?_⟩
  have hzero : ∫ p in Icc a b ×ˢ Icc lo hi, t p.2 * (α p.1 * F p + β p.1 * dF p) = 0 := by
    refine slice_core hα hFZ hβi ?_
    intro χ Z hχ hχs
    obtain ⟨s1, s2, s3, s4⟩ := radial_slices h (u := u) hχ hχs
    have hline := radial_line ha hab hbu s1 s2 s3 s4 hk hk'
    rw [← hline]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hαd, hβd, hca, hcb]
    ring
  have e : (fun p : ℝ × ℝ => t p.2 * (α p.1 * F p + β p.1 * dF p)) =
      fun p => Lf p * t p.2 - cb * (Sb p * t p.2) - (ca * Sa p) * t p.2 := by
    funext p
    rw [← hpt p]
    ring
  have j0 : IntegrableOn (fun p : ℝ × ℝ => cb * (Sb p * t p.2)) (Icc a b ×ˢ Icc lo hi) := iSb.const_mul cb
  have j1 : IntegrableOn (fun p : ℝ × ℝ => Lf p * t p.2 - cb * (Sb p * t p.2)) (Icc a b ×ˢ Icc lo hi) := iL.sub j0
  rw [e, integral_sub j1 iSa, integral_sub iL j0, integral_const_mul] at hzero
  have e2 : ∫ p in Icc a b ×ˢ Icc lo hi, (ca * Sa p) * t p.2 = ca * ∫ p in Icc a b ×ˢ Icc lo hi, Sa p * t p.2 := by
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [e2] at hzero
  have goal_eq : ∫ p in Icc a b ×ˢ Icc lo hi, Lf p * t p.2 =
      cb * (∫ p in Icc a b ×ˢ Icc lo hi, Sb p * t p.2) + ca * ∫ p in Icc a b ×ˢ Icc lo hi, Sa p * t p.2 := by
    linear_combination hzero
  exact goal_eq

end Breakdown.CertCell.StripTrace

namespace Breakdown.CertCell.StripTrace

namespace Internal

open Breakdown.CellCert.CellFormula

theorem wslice {G : ℝ × ℝ → ℂ} {χ : ℝ → ℝ} {R δ C : ℝ} {S : Set ℝ} (hδ : 0 < δ)
    (hG : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * G p) (Icc (-R) R ×ˢ S))
    (hχ : Continuous χ) (hC : ∀ r, |χ r| ≤ C) (hχ0 : ∀ r, |r| < δ → χ r = 0) :
    IntegrableOn (fun p : ℝ × ℝ => (χ p.1 : ℂ) * G p) (Icc (-R) R ×ˢ S) := by
  have hm : Measurable (fun r : ℝ => χ r / r) := hχ.measurable.div measurable_id
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := hG.bdd_mul (c := C / δ) ((Complex.measurable_ofReal.comp (hm.comp measurable_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  · refine h1.congr (Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 = 0
    · simp [hp, hχ0 0 (by simp [hδ])]
    · simp only [Function.comp_apply]
      have : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp
      push_cast
      field_simp
  · simp only [Function.comp_apply]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    by_cases hp : |p.1| < δ
    · rw [hχ0 _ hp, abs_zero, zero_div]
      positivity
    · replace hp := not_lt.1 hp
      have hpos : 0 < |p.1| := hδ.trans_le hp
      rw [div_le_div_iff₀ hpos hδ]
      calc |χ p.1| * δ ≤ C * δ := mul_le_mul_of_nonneg_right (hC _) hδ.le
        _ ≤ C * |p.1| := mul_le_mul_of_nonneg_left hp hC0

theorem prod_iter_fst {G : ℝ × ℝ → ℂ} {s1 s2 : Set ℝ} (hG : IntegrableOn G (s1 ×ˢ s2)) :
    ∫ p in s1 ×ˢ s2, G p = ∫ y in s2, ∫ x in s1, G (x, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm G (Breakdown.FracInternal.SegmentParts.prod_int hG)

theorem slice_pair_fst {H : ℝ × ℝ → ℂ} {θ χ : ℝ → ℝ} {c d R : ℝ}
    (hH : IntegrableOn (fun p : ℝ × ℝ => (χ p.1 : ℂ) * H p) (Icc (-R) R ×ˢ Icc c d))
    (hθ : Continuous θ) (hθs : ∀ x, x ∉ Icc c d → θ x = 0) (hχs : ∀ r, r ∉ Icc (-R) R → χ r = 0) :
    ∫ p, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = ∫ z, (θ z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * H (r, z) := by
  have hz1 : ∀ p ∉ Icc (-R) R ×ˢ Icc c d, ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p = 0 := by
    intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (-R) R ∧ p.2 ∈ Icc c d) from hp) with h | h
    · simp [hχs _ h]
    · simp [hθs _ h]
  have hz2 : ∀ z ∉ Icc c d, (θ z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * H (r, z) = 0 := by
    intro z hz
    simp [hθs _ hz]
  have hint : IntegrableOn (fun p : ℝ × ℝ => ((χ p.1 * θ p.2 : ℝ) : ℂ) * H p) (Icc (-R) R ×ˢ Icc c d) := by
    refine IntegrableOn.congr_fun (hH.continuousOn_mul (Complex.continuous_ofReal.comp (hθ.comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)) (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2,
    prod_iter_fst hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_const_mul]
  congr 1
  funext r
  push_cast
  ring

theorem height_slices {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {χ : ℝ → ℝ} {R δ l u : ℝ}
    (hδ : 0 < δ) (hχ : ContDiff ℝ ∞ χ) (hχs : ∀ r, r ∉ Icc (-R) R → χ r = 0) (hχ0 : ∀ r, |r| < δ → χ r = 0) :
    IntegrableOn (fun z => ∫ r in Icc (-R) R, (χ r : ℂ) * F (r, z)) (Ioo l u) ∧
    IntegrableOn (fun z => ∫ r in Icc (-R) R, (χ r : ℂ) * dF (r, z)) (Ioo l u) ∧
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo l u →
      ∫ z, ((deriv η z : ℝ) : ℂ) * (∫ r in Icc (-R) R, (χ r : ℂ) * F (r, z)) =
        -∫ z, (η z : ℂ) * ∫ r in Icc (-R) R, (χ r : ℂ) * dF (r, z) := by
  have hχc : Continuous χ := hχ.continuous
  have hχcs : HasCompactSupport χ := HasCompactSupport.intro isCompact_Icc hχs
  obtain ⟨C, hC⟩ := hχcs.exists_bound_of_continuous hχc
  have hC' : ∀ r, |χ r| ≤ C := fun r => by simpa [Real.norm_eq_abs] using hC r
  set Z : ℝ := |l| + |u| with hZ
  have hsub : Icc (-R) R ×ˢ Icc l u ⊆ Icc (-R) R ×ˢ Icc (-Z) Z := prod_mono le_rfl (sym_box l u)
  have hwF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc (-R) R ×ˢ Icc l u) :=
    ((h.1 R Z).1).mono_set hsub
  have hwdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc (-R) R ×ˢ Icc l u) :=
    ((h.1 R Z).2).mono_set hsub
  have iF := wslice hδ hwF hχc hC' hχ0
  have idF := wslice hδ hwdF hχc hC' hχ0
  refine ⟨IntegrableOn.mono_set ((Breakdown.FracInternal.SegmentParts.prod_int iF).integral_prod_right) Ioo_subset_Icc_self,
    IntegrableOn.mono_set ((Breakdown.FracInternal.SegmentParts.prod_int idF).integral_prod_right) Ioo_subset_Icc_self, ?_⟩
  intro η hη hc hts
  have hηs : ∀ x, x ∉ Icc l u → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (Ioo_subset_Icc_self (hts hm)))
  have hdηs : ∀ x, x ∉ Icc l u → deriv η x = 0 := fun x hx =>
    Function.notMem_support.1 (fun hm => hx (Ioo_subset_Icc_self (hts (support_deriv_subset hm))))
  set ψ : ℝ × ℝ → ℝ := fun q => χ q.1 * η q.2 with hψd
  have hψ : ContDiff ℝ ∞ ψ := (hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (hχcs.isCompact.prod hc.isCompact) ?_
    intro q hq
    rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport χ ∧ q.2 ∈ tsupport η) from hq) with h' | h'
    · simp [hψd, image_eq_zero_of_notMem_tsupport h']
    · simp [hψd, image_eq_zero_of_notMem_tsupport h']
  have hψp : ∀ q ∈ tsupport ψ, q.1 ≠ 0 := by
    intro q hq
    have hsub' : tsupport ψ ⊆ {q : ℝ × ℝ | δ ≤ |q.1|} := by
      refine closure_minimal ?_ (isClosed_le continuous_const (continuous_abs.comp continuous_fst))
      intro q' hq'
      by_contra hm
      exact hq' (by simp [hψd, hχ0 _ (lt_of_not_ge hm)])
    have hle : δ ≤ |q.1| := hsub' hq
    intro h0
    rw [h0, abs_zero] at hle
    linarith
  have key := h.2.2 ψ hψ hψc hψp
  have hfd := fun q => Breakdown.FracInternal.CornerParts.fderiv_prod_apply
    (hχ.differentiable (by simp)) (hη.differentiable (by simp)) q
  simp only [hψd, (hfd _).2] at key
  rw [slice_pair_fst iF (hη.continuous_deriv (by simp)) hdηs hχs,
    slice_pair_fst idF hη.continuous hηs hχs] at key
  exact key

theorem height_line {f df k k' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioo (a - 1) (b + 1))) (hdf : IntegrableOn df (Ioo (a - 1) (b + 1)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo (a - 1) (b + 1) →
      ∫ t, ((deriv η t : ℝ) : ℂ) * f t = -∫ t, (η t : ℂ) * df t)
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') :
    ∫ x in Icc a b, ((df x * k x + f x * k' x)
      - k b * ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x)
      - k a * ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have hsub : Ioc a b ⊆ Ioo (a - 1) (b + 1) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hfab : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hf.mono_set hsub)
  have hdfab : IntervalIntegrable df volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hdf.mono_set hsub)
  have hramp : ∀ o d : ℝ, Continuous (fun r : ℝ => (((r - o) / d : ℝ) : ℂ)) := fun o d =>
    Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const d)
  have i1 : IntervalIntegrable (fun x => df x * k x + f x * k' x) volume a b :=
    (hdfab.mul_continuousOn hkc.continuousOn).add (hfab.mul_continuousOn hk'.continuousOn)
  have i2 : IntervalIntegrable (fun x => k b *
      ((((1 / (b - a) : ℝ)) : ℂ) * f x + (((x - a) / (b - a) : ℝ) : ℂ) * df x)) volume a b :=
    ((hfab.const_mul _).add (hdfab.continuousOn_mul (hramp a (b - a)).continuousOn)).const_mul _
  have i3 : IntervalIntegrable (fun x => k a *
      ((((1 / (a - b) : ℝ)) : ℂ) * f x + (((x - b) / (a - b) : ℝ) : ℂ) * df x)) volume a b :=
    ((hfab.const_mul _).add (hdfab.continuousOn_mul (hramp b (a - b)).continuousOn)).const_mul _
  have L := line_parts (by linarith : a - 1 < a) hab (by linarith : b < b + 1) hf hdf hw hk hk'
  rw [intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2, L,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem height_core {F dF : ℝ × ℝ → ℂ} {α β w : ℝ → ℂ} {a b lo hi : ℝ}
    (hα : Continuous α) (hβ : Continuous β)
    (hF : ∀ R, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc (-R) R ×ˢ Icc a b))
    (hdF : ∀ R, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc (-R) R ×ˢ Icc a b))
    (hFo : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn F {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn dF {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z})
    (h1 : ∀ (χ : ℝ → ℝ) (R δ : ℝ), 0 < δ → ContDiff ℝ ∞ χ → (∀ r, r ∉ Icc (-R) R → χ r = 0) →
      (∀ r, |r| < δ → χ r = 0) →
      ∫ z in Icc a b, (α z * (∫ r in Icc (-R) R, (χ r : ℂ) * F (r, z))
        + β z * ∫ r in Icc (-R) R, (χ r : ℂ) * dF (r, z)) = 0) :
    ∫ p in Icc lo hi ×ˢ Icc a b, w p.1 * (α p.2 * F p + β p.2 * dF p) = 0 := by
  set E : ℝ × ℝ → ℂ := fun p => α p.2 * F p + β p.2 * dF p with hEd
  set Φ : ℝ × ℝ → ℂ := ((univ : Set ℝ) ×ˢ Icc a b).indicator E with hΦd
  have hΦs : ∀ p : ℝ × ℝ, p.2 ∉ Icc a b → Φ p = 0 := fun p hp =>
    indicator_of_notMem (fun hm => hp hm.2) _
  have hΦE : ∀ p : ℝ × ℝ, p.2 ∈ Icc a b → Φ p = E p := fun p hp =>
    indicator_of_mem (show p ∈ (univ : Set ℝ) ×ˢ Icc a b from ⟨trivial, hp⟩) _
  have hint : ∀ K, K ⊆ ({0} : Set ℝ)ᶜ → IsCompact K → IntegrableOn Φ (K ×ˢ Icc a b) := by
    intro K hKU hK
    obtain ⟨δ, hδ, R, hR⟩ := Breakdown.FracInternal.SegmentParts.nz_set hK (fun r hr => by simpa using hKU hr)
    set Z : ℝ := |a| + |b|
    have hsub : K ×ˢ Icc a b ⊆ {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} := by
      intro p hp
      have h2 := sym_box a b hp.2
      exact ⟨(hR _ hp.1).1, (hR _ hp.1).2, abs_le.2 h2⟩
    have hE : IntegrableOn E (K ×ˢ Icc a b) := by
      have hc : IsCompact (K ×ˢ Icc a b) := hK.prod isCompact_Icc
      exact ((((hFo δ R Z hδ).1).mono_set hsub).continuousOn_mul (hα.comp continuous_snd).continuousOn hc).add
        ((((hFo δ R Z hδ).2).mono_set hsub).continuousOn_mul (hβ.comp continuous_snd).continuousOn hc)
    exact IntegrableOn.congr_fun hE (fun p hp => (hΦE p hp.2).symm) (hK.measurableSet.prod measurableSet_Icc)
  have hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ({0} : Set ℝ)ᶜ →
      ∫ p, (χ p.1 : ℂ) * Φ p = 0 := by
    intro χ hχs hχc hχU
    obtain ⟨δ, hδ, R, hR⟩ := Breakdown.FracInternal.SegmentParts.nz_set hχc.isCompact
      (fun r hr => by simpa using hχU hr)
    have hout : ∀ r, r ∉ Icc (-R) R → χ r = 0 := by
      intro r hr
      refine image_eq_zero_of_notMem_tsupport (fun hm => hr ?_)
      exact abs_le.1 (hR r hm).2
    have hnear : ∀ r, |r| < δ → χ r = 0 := by
      intro r hr
      refine image_eq_zero_of_notMem_tsupport (fun hm => ?_)
      linarith [(hR r hm).1]
    obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχs.continuous
    have hC' : ∀ r, |χ r| ≤ C := fun r => by simpa [Real.norm_eq_abs] using hC r
    have hz : ∀ p ∉ Icc (-R) R ×ˢ Icc a b, (χ p.1 : ℂ) * Φ p = 0 := by
      intro p hp
      rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (-R) R ∧ p.2 ∈ Icc a b) from hp) with h | h
      · rw [hout _ h]; simp
      · rw [hΦs p h, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hcongr : ∫ p in Icc (-R) R ×ˢ Icc a b, (χ p.1 : ℂ) * Φ p =
        ∫ p in Icc (-R) R ×ˢ Icc a b, (χ p.1 : ℂ) * E p :=
      setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => by simp only [hΦE p hp.2])
    have hcpt : IsCompact (Icc (-R) R ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
    have jF : IntegrableOn (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (α p.2 * F p)) (Icc (-R) R ×ˢ Icc a b) := by
      refine wslice hδ (IntegrableOn.congr_fun ((hF R).continuousOn_mul (hα.comp continuous_snd).continuousOn hcpt)
        (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)) hχs.continuous hC' hnear
      simp only [Function.comp_apply]
      ring
    have jdF : IntegrableOn (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (β p.2 * dF p)) (Icc (-R) R ×ˢ Icc a b) := by
      refine wslice hδ (IntegrableOn.congr_fun ((hdF R).continuousOn_mul (hβ.comp continuous_snd).continuousOn hcpt)
        (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)) hχs.continuous hC' hnear
      simp only [Function.comp_apply]
      ring
    have hχE : IntegrableOn (fun p : ℝ × ℝ => (χ p.1 : ℂ) * E p) (Icc (-R) R ×ˢ Icc a b) :=
      IntegrableOn.congr_fun (jF.add jdF) (fun p _ => by simp only [hEd, Pi.add_apply]; ring)
        (measurableSet_Icc.prod measurableSet_Icc)
    rw [hcongr, prod_iter_fst hχE]
    rw [← h1 χ R δ hδ hχs hout hnear]
    refine integral_congr_ae ?_
    filter_upwards [(Breakdown.FracInternal.SegmentParts.prod_int jF).prod_left_ae,
      (Breakdown.FracInternal.SegmentParts.prod_int jdF).prod_left_ae] with z hz1 hz2
    simp only [hEd]
    have e : (fun r => (χ r : ℂ) * (α z * F (r, z) + β z * dF (r, z))) =
        fun r => (χ r : ℂ) * (α z * F (r, z)) + (χ r : ℂ) * (β z * dF (r, z)) := by
      funext r
      ring
    rw [e, integral_add hz1 hz2]
    have e1 : (fun r => (χ r : ℂ) * (α z * F (r, z))) = fun r => α z * ((χ r : ℂ) * F (r, z)) := by
      funext r
      ring
    have e2 : (fun r => (χ r : ℂ) * (β z * dF (r, z))) = fun r => β z * ((χ r : ℂ) * dF (r, z)) := by
      funext r
      ring
    rw [e1, e2, integral_const_mul, integral_const_mul]
  have hmain := Breakdown.FracInternal.SegmentParts.fst_slice measurableSet_Icc isOpen_compl_singleton
    (by simp) hΦs hint hχ w (A := Icc lo hi)
  rw [← hmain]
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
  simp only [hΦE p hp.2, hEd]

end Internal

open Internal Breakdown.CellCert.CellFormula

theorem height_parts {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair (fun r => r) F dF) {lo hi a b : ℝ} (hab : a < b)
    {k k' t : ℝ → ℂ} (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * (dF p * k p.2 + F p * k' p.2) * t p.1) (Icc lo hi ×ˢ Icc a b) ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1)) (Icc lo hi ×ˢ Icc a b) ∧
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1)) (Icc lo hi ×ˢ Icc a b) ∧
    ∫ p in Icc lo hi ×ˢ Icc a b, (p.1 : ℂ) * (dF p * k p.2 + F p * k' p.2) * t p.1 =
      k b * (∫ p in Icc lo hi ×ˢ Icc a b,
          ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t p.1))
      + k a * (∫ p in Icc lo hi ×ˢ Icc a b,
          ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t p.1)) := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have hramp : ∀ o d : ℝ, Continuous (fun r : ℝ => (((r - o) / d : ℝ) : ℂ)) := fun o d =>
    Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const d)
  set Zab : ℝ := |a| + |b| with hZab
  have hwF : ∀ R, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc (-R) R ×ˢ Icc a b) := fun R =>
    ((h.1 R Zab).1).mono_set (prod_mono le_rfl (sym_box a b))
  have hwdF : ∀ R, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc (-R) R ×ˢ Icc a b) := fun R =>
    ((h.1 R Zab).2).mono_set (prod_mono le_rfl (sym_box a b))
  set R0 : ℝ := |lo| + |hi| with hR0
  have hsub0 : Icc lo hi ×ˢ Icc a b ⊆ Icc (-R0) R0 ×ˢ Icc a b := prod_mono (sym_box lo hi) le_rfl
  have hcpt : IsCompact (Icc lo hi ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hF0 := (hwF R0).mono_set hsub0
  have hdF0 := (hwdF R0).mono_set hsub0
  have hms : MeasurableSet (Icc lo hi ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  have mk : ∀ (v w : ℝ × ℝ → ℂ), Continuous v → Continuous w →
      IntegrableOn (fun p : ℝ × ℝ => v p * ((p.1 : ℂ) * F p) + w p * ((p.1 : ℂ) * dF p)) (Icc lo hi ×ˢ Icc a b) :=
    fun v w hv hw => (hF0.continuousOn_mul hv.continuousOn hcpt).add (hdF0.continuousOn_mul hw.continuousOn hcpt)
  have iL : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * (dF p * k p.2 + F p * k' p.2) * t p.1) (Icc lo hi ×ˢ Icc a b) :=
    IntegrableOn.congr_fun (mk (fun p => k' p.2 * t p.1) (fun p => k p.2 * t p.1)
      ((hk'.comp continuous_snd).mul (ht.comp continuous_fst)) ((hkc.comp continuous_snd).mul (ht.comp continuous_fst)))
      (fun p _ => by ring) hms
  have iSb : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1)) (Icc lo hi ×ˢ Icc a b) :=
    IntegrableOn.congr_fun (mk (fun p => (((1 / (b - a) : ℝ)) : ℂ) * t p.1) (fun p => (((p.2 - a) / (b - a) : ℝ) : ℂ) * t p.1)
      (continuous_const.mul (ht.comp continuous_fst)) (((hramp a (b - a)).comp continuous_snd).mul (ht.comp continuous_fst)))
      (fun p _ => by ring) hms
  have iSa : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1)) (Icc lo hi ×ˢ Icc a b) :=
    IntegrableOn.congr_fun (mk (fun p => (((1 / (a - b) : ℝ)) : ℂ) * t p.1) (fun p => (((p.2 - b) / (a - b) : ℝ) : ℂ) * t p.1)
      (continuous_const.mul (ht.comp continuous_fst)) (((hramp b (a - b)).comp continuous_snd).mul (ht.comp continuous_fst)))
      (fun p _ => by ring) hms
  refine ⟨iL, iSb, iSa, ?_⟩
  set α : ℝ → ℂ := fun z => k' z - k b * (((1 / (b - a) : ℝ)) : ℂ) - k a * (((1 / (a - b) : ℝ)) : ℂ) with hαd
  set β : ℝ → ℂ := fun z => k z - k b * (((z - a) / (b - a) : ℝ) : ℂ) - k a * (((z - b) / (a - b) : ℝ) : ℂ) with hβd
  have hα : Continuous α := (hk'.sub continuous_const).sub continuous_const
  have hβ : Continuous β := (hkc.sub (continuous_const.mul (hramp a (b - a)))).sub (continuous_const.mul (hramp b (a - b)))
  have hzero : ∫ p in Icc lo hi ×ˢ Icc a b, ((p.1 : ℂ) * t p.1) * (α p.2 * F p + β p.2 * dF p) = 0 := by
    refine height_core (w := fun r => (r : ℂ) * t r) hα hβ hwF hwdF h.2.1 ?_
    intro χ R δ hδ hχ hχs hχ0
    obtain ⟨s1, s2, s3⟩ := height_slices h (l := a - 1) (u := b + 1) hδ hχ hχs hχ0
    rw [← height_line hab s1 s2 s3 hk hk']
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hαd, hβd]
    ring
  have j0 : IntegrableOn (fun p : ℝ × ℝ => k b * (((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1))) (Icc lo hi ×ˢ Icc a b) := iSb.const_mul _
  have j1 : IntegrableOn (fun p : ℝ × ℝ => k a * (((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p)
      * ((p.1 : ℂ) * t p.1))) (Icc lo hi ×ˢ Icc a b) := iSa.const_mul _
  have j2 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * (dF p * k p.2 + F p * k' p.2) * t p.1
      - k b * (((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t p.1)))
      (Icc lo hi ×ˢ Icc a b) := iL.sub j0
  have e : (fun p : ℝ × ℝ => ((p.1 : ℂ) * t p.1) * (α p.2 * F p + β p.2 * dF p)) =
      fun p => ((p.1 : ℂ) * (dF p * k p.2 + F p * k' p.2) * t p.1
        - k b * (((((1 / (b - a) : ℝ)) : ℂ) * F p + (((p.2 - a) / (b - a) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t p.1)))
        - k a * (((((1 / (a - b) : ℝ)) : ℂ) * F p + (((p.2 - b) / (a - b) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * t p.1)) := by
    funext p
    simp only [hαd, hβd]
    ring
  rw [e, integral_sub j2 j1, integral_sub iL j0, integral_const_mul, integral_const_mul] at hzero
  linear_combination hzero

end Breakdown.CertCell.StripTrace

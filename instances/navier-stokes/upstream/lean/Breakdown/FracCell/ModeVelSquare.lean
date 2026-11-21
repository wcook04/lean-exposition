import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.CylIntegral

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Spectral.Internal.CylIntegral

namespace ModeVelSquareInternal

theorem symm_apply (r θ z : ℝ) :
    cylMap.symm ((r, θ), z) = ((r * Real.cos θ, r * Real.sin θ), z) := by
  simp [cylMap]

theorem symm_meas : Measurable (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) := by
  have h : (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) = fun x => (polarCoord.symm x.1, x.2) := rfl
  rw [h]
  exact ((continuous_polarCoord_symm.comp continuous_fst).prodMk continuous_snd).measurable

theorem symm_qmp :
    Measure.QuasiMeasurePreserving (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ)
      (volume.restrict cylMap.target) volume := by
  refine ⟨symm_meas, Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_⟩
  rw [Measure.map_apply symm_meas hN]
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    cylMap.open_target.measurableSet (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn
    (N.indicator 1)
  rw [lintegral_indicator_one hN] at key
  have hL : volume.restrict (cylMap.symm '' cylMap.target) N = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans h0.le)
  rw [hL] at key
  simp_rw [det_cylDeriv] at key
  have hAE : AEMeasurable (fun x : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal |x.1.1| * N.indicator 1 (cylMap.symm x)) (volume.restrict cylMap.target) :=
    ((ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (measurable_fst.comp measurable_fst))).mul
      ((measurable_one.indicator hN).comp symm_meas)).aemeasurable
  have hae := (lintegral_eq_zero_iff' hAE).mp key.symm
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae, ae_restrict_mem cylMap.open_target.measurableSet] with x hx hxt hxN
  have hpos : 0 < x.1.1 := hxt.1.1
  have hxN' : cylMap.symm x ∈ N := hxN
  simp only [Pi.zero_apply, Set.indicator_of_mem hxN', Pi.one_apply, mul_one,
    ENNReal.ofReal_eq_zero] at hx
  linarith [abs_of_pos hpos]

theorem single_cont (i : Fin 3) :
    Continuous fun t : ℝ => (EuclideanSpace.single i t : Space) := by
  have h : (fun t : ℝ => (EuclideanSpace.single i t : Space)) =
      fun t => t • (EuclideanSpace.single i 1 : Space) := by
    funext t
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  exact continuous_id.smul continuous_const

theorem frameUnit_cont (c : Fin 3) : Continuous fun θ : ℝ => frameUnit θ c := by
  fin_cases c
  · show Continuous fun θ : ℝ => radialUnit θ
    exact ((single_cont 0).comp Real.continuous_cos).add ((single_cont 1).comp Real.continuous_sin)
  · show Continuous fun θ : ℝ => angularUnit θ
    exact ((single_cont 0).comp Real.continuous_sin.neg).add
      ((single_cont 1).comp Real.continuous_cos)
  · exact continuous_const

theorem frameUnit_norm (θ : ℝ) (c : Fin 3) : ‖frameUnit θ c‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  fin_cases c <;> simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit]

theorem frameVec_eq (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = inner ℝ u (frameUnit θ a) := by
  fin_cases a <;> rfl

theorem frameVec_cont (a : Fin 3) :
    Continuous fun q : ℝ × Space => frameVec q.1 q.2 a := by
  simp_rw [frameVec_eq]
  exact continuous_snd.inner ((frameUnit_cont a).comp continuous_fst)

theorem frameVec_abs (θ : ℝ) (u : Space) (a : Fin 3) : |frameVec θ u a| ≤ ‖u‖ := by
  rw [frameVec_eq]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [frameUnit_norm, mul_one]

def kern (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (x : (ℝ × ℝ) × ℝ) : ℂ :=
  Complex.exp (-(azimuth m n * x.2 : ℝ) * Complex.I) *
    (frameVec x.2 (v (cylPoint x.1.1 x.2 x.1.2)) a : ℂ)

theorem kern_periodic (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    Function.Periodic (fun θ => kern m n v a (p, θ)) (2 * Real.pi) := by
  intro θ
  have h1 : radialUnit (θ + 2 * Real.pi) = radialUnit θ := by simp [radialUnit]
  have h2 : angularUnit (θ + 2 * Real.pi) = angularUnit θ := by simp [angularUnit]
  have h3 : cylPoint p.1 (θ + 2 * Real.pi) p.2 = cylPoint p.1 θ p.2 := by simp [cylPoint]
  have h5 : Complex.exp (-(azimuth m n * (θ + 2 * Real.pi) : ℝ) * Complex.I) =
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) := by
    have e : -((azimuth m n * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I =
        -((azimuth m n * θ : ℝ) : ℂ) * Complex.I +
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [azimuth]
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [kern, frameVec, h1, h2, h3, h5]

theorem mode_eq (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVec m n v p.1 p.2 a =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (p, θ) := by
  have hper := (kern_periodic m n v a p).intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hper
  rw [← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), ← hper]
  rfl

theorem vel_comp_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    AEStronglyMeasurable (fun x => v (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
  hs.measurable_velocity.comp_quasiMeasurePreserving
    (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)

theorem kern_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (kern m n v a)
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
        (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hset : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi =ᵐ[volume]
      swapEquiv ⁻¹' cylMap.target := by
    rw [swapEquiv_preimage]
    exact Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm
  rw [Measure.restrict_congr_set hset]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hΨ : Continuous fun q : ℝ × Space =>
      Complex.exp (-(azimuth m n * q.1 : ℝ) * Complex.I) * (frameVec q.1 q.2 a : ℂ) := by
    have := frameVec_cont a
    fun_prop
  have hk := hΨ.comp_aestronglyMeasurable
      ((continuous_snd.comp continuous_fst).aestronglyMeasurable.prodMk (vel_comp_meas hs))
  refine (hk.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply, swapEquiv_apply, kern]
  rw [symm_apply, toSpace_apply]
  rfl

theorem mode_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have h := (kern_meas hs n a).integral_prod_right'
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p =>
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (p, θ) :=
    funext (mode_eq m n v a)
  rw [e]
  exact h.const_mul _

theorem sq_integral_le {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hg : IntegrableOn g (Ioc (-Real.pi) Real.pi)) (hfg : ∀ θ, ‖f θ‖ ^ 2 ≤ g θ) :
    ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ^ 2 ≤ 2 * Real.pi * ∫ θ in Ioc (-Real.pi) Real.pi, g θ := by
  have hp := Real.pi_pos
  have hsq : IntegrableOn (fun θ => ‖f θ‖ ^ 2) (Ioc (-Real.pi) Real.pi) :=
    hg.mono' (hf.norm.pow 2) (ae_of_all _ fun θ => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hfg θ)
  have h1 : ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ :=
    norm_integral_le_integral_norm _
  have hs0 : 0 ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ := integral_nonneg fun _ => norm_nonneg _
  have hc : IntegrableOn (fun θ : ℝ => (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi))
      (Ioc (-Real.pi) Real.pi) := integrableOn_const (by simp)
  have h2 : (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) * (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ≤
      ∫ θ in Ioc (-Real.pi) Real.pi,
        ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi) + Real.pi * ‖f θ‖ ^ 2) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun θ => by positivity)
      (hc.add (hsq.const_mul Real.pi)) (ae_of_all _ fun θ => ?_)
    have e : (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi) + Real.pi * ‖f θ‖ ^ 2
        - (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) * ‖f θ‖ =
        ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) - 2 * Real.pi * ‖f θ‖) ^ 2 / (4 * Real.pi) := by
      field_simp
      ring
    have : 0 ≤ ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) - 2 * Real.pi * ‖f θ‖) ^ 2 / (4 * Real.pi) := by
      positivity
    linarith
  rw [integral_add hc (hsq.const_mul Real.pi), setIntegral_const, integral_const_mul,
    measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h2
  have h3 : ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ ^ 2 ≤ ∫ θ in Ioc (-Real.pi) Real.pi, g θ :=
    integral_mono hsq hg hfg
  have e2 : (Real.pi - -Real.pi) * ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi)) =
      (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / 2 := by
    field_simp
    ring
  rw [e2] at h2
  have h4 : ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ^ 2 ≤ (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

def bump (R : ℝ) (v : Space → Space) (y : Space) : ℝ :=
  (Metric.closedBall (0 : Space) R).indicator (fun y => 1 + ‖v y‖ ^ 6) y

theorem bump_integrable {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (R : ℝ) :
    Integrable (bump R v) := by
  have h6 : Integrable (fun y => ‖v y‖ ^ 6) :=
    (show MemLp v ((6 : ℕ) : ENNReal) volume by exact_mod_cast hs.velocity_six).integrable_norm_pow
      (by norm_num)
  have hc : IntegrableOn (fun _ : Space => (1 : ℝ)) (Metric.closedBall (0 : Space) R) :=
    integrableOn_const (measure_closedBall_lt_top).ne
  exact (hc.add h6.integrableOn).integrable_indicator Metric.isClosed_closedBall.measurableSet

theorem cylPoint_norm (r θ z : ℝ) : ‖cylPoint r θ z‖ = Real.sqrt (r ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, cylPoint, PiLp.single_apply, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem kern_sq {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3)
    (x : (ℝ × ℝ) × ℝ) (hx : x.1 ∈ K.rect) :
    ‖kern m n v a x‖ ^ 2 ≤ bump (K.r₂ + K.z₂) v (cylPoint x.1.1 x.2 x.1.2) := by
  have hr0 : 0 ≤ x.1.1 := le_trans hK.r_order.1 hx.1.1
  have hz0 : 0 ≤ x.1.2 := le_trans hK.z_order.1 hx.2.1
  have hball : cylPoint x.1.1 x.2 x.1.2 ∈ Metric.closedBall (0 : Space) (K.r₂ + K.z₂) := by
    rw [mem_closedBall_zero_iff, cylPoint_norm, Real.sqrt_le_iff]
    constructor
    · linarith [hx.1.2, hx.2.2]
    · nlinarith [hx.1.2, hx.2.2]
  rw [bump, Set.indicator_of_mem hball]
  unfold kern
  rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  set t := ‖v (cylPoint x.1.1 x.2 x.1.2)‖
  have ht : 0 ≤ t := norm_nonneg _
  have h1 : |frameVec x.2 (v (cylPoint x.1.1 x.2 x.1.2)) a| ^ 2 ≤ t ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (frameVec_abs _ _ _) 2
  nlinarith [sq_nonneg (t ^ 3 - t), sq_nonneg (t ^ 2 - 1), sq_nonneg t]

theorem mode_integrable_p {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) K.rect := by
  have hp := Real.pi_pos
  set R := K.r₂ + K.z₂
  have hF : Integrable (bump R v) := bump_integrable hs R
  have hG : Integrable (fun w => bump R v (toSpace w)) :=
    (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hF
  have hH := change_integrable hG
  have h1 : IntegrableOn
      ((fun x : (ℝ × ℝ) × ℝ => x.1.1 * bump R v (toSpace (cylMap.symm x))) ∘ swapEquiv)
      (swapEquiv ⁻¹' cylMap.target) :=
    (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  rw [swapEquiv_preimage] at h1
  have h2 : IntegrableOn
      ((fun x : (ℝ × ℝ) × ℝ => x.1.1 * bump R v (toSpace (cylMap.symm x))) ∘ swapEquiv)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi) :=
    h1.congr_set_ae (Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm)
  have h3 : IntegrableOn (fun x : (ℝ × ℝ) × ℝ => x.1.1 * bump R v (cylPoint x.1.1 x.2 x.1.2))
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi) := by
    refine h2.congr_fun (fun x _ => ?_)
      ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioc)
    obtain ⟨⟨r, z⟩, θ⟩ := x
    simp only [Function.comp_apply, swapEquiv_apply]
    rw [symm_apply, toSpace_apply]
    rfl
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h3
  have hB := h3.integral_prod_left
  have hsl := h3.prod_right_ae
  have hks := (kern_meas hs n a).prodMk_left
  have hT : MeasurableSet ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
    (measurableSet_Ioi.prod MeasurableSet.univ).inter (measurableSet_Icc.prod measurableSet_Icc)
  have hsub : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    inter_subset_left
  have hhalf : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) := by
    have hB' : IntegrableOn
        (fun q : ℝ × ℝ => ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * bump R v (cylPoint q.1 θ q.2))
        ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
      IntegrableOn.mono_set hB hsub
    refine (hB'.const_mul (1 / (2 * Real.pi))).mono'
      (continuous_fst.aestronglyMeasurable.mul
        (((mode_meas hs n a).mono_measure (Measure.restrict_mono hsub le_rfl)).norm.pow 2)) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsl,
      ae_restrict_of_ae_restrict_of_subset hsub hks, ae_restrict_mem hT] with q hq hk hqS
    have hpos : 0 < q.1 := hqS.1.1
    have hgi : IntegrableOn (fun θ => bump R v (cylPoint q.1 θ q.2)) (Ioc (-Real.pi) Real.pi) := by
      refine (hq.const_mul (q.1⁻¹)).congr (ae_of_all _ fun θ => ?_)
      simp only []
      field_simp
    have hcs := sq_integral_le hk hgi (fun θ => kern_sq hK m n v a (q, θ) hqS.2)
    have e1 : ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * bump R v (cylPoint q.1 θ q.2) =
        q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, bump R v (cylPoint q.1 θ q.2) :=
      integral_const_mul _ _
    have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    show ‖q.1 * ‖modeVec m n v q.1 q.2 a‖ ^ 2‖ ≤
      1 / (2 * Real.pi) * ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * bump R v (cylPoint q.1 θ q.2)
    rw [e1, Real.norm_of_nonneg (by positivity), mode_eq, norm_mul, mul_pow, hn]
    calc q.1 * ((1 / (2 * Real.pi)) ^ 2 * ‖∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (q, θ)‖ ^ 2)
        ≤ q.1 * ((1 / (2 * Real.pi)) ^ 2 *
            (2 * Real.pi * ∫ θ in Ioc (-Real.pi) Real.pi, bump R v (cylPoint q.1 θ q.2))) := by
          gcongr
      _ = 1 / (2 * Real.pi) * (q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, bump R v (cylPoint q.1 θ q.2)) := by
          field_simp
  refine hhalf.of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  have h1 : K.r₁ ≤ p.1 := hp.1.1.1
  have h2 : ¬ (0 < p.1) := fun h => hp.2 ⟨⟨h, trivial⟩, hp.1⟩
  have h3 : p.1 = 0 := le_antisymm (not_lt.mp h2) (le_trans hK.r_order.1 h1)
  simp [h3]

theorem rect_ae_le (K : CellBox) (hK : IsCellBox K) :
    volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp =>
    ⟨le_trans hK.r_order.1 hp.1.1, trivial⟩
  refine hsub.eventuallyLE.trans ?_
  exact (Measure.set_prod_ae_eq (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm .rfl).le

end ModeVelSquareInternal

open ModeVelSquareInternal in
theorem modeVelSquare : ModeVelSquareStatement := by
  intro K hK m v G H hs n a
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a)
      (volume.restrict K.rect) := (mode_meas hs n a).mono_measure (rect_ae_le K hK)
  refine ⟨hmeas, ?_⟩
  have hI := mode_integrable_p hK hs n a
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  by_cases h0 : K.r₁ = 0
  · refine hI.congr_fun (fun p _ => ?_) hrect
    simp [CellBox.lineWeight, h0]
  · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    refine (hI.const_mul (K.r₁⁻¹)).mono' ?_ ?_
    · have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) =
          fun p => ‖modeVec m n v p.1 p.2 a‖ ^ 2 := by
        funext p
        simp [CellBox.lineWeight, h0]
      rw [e]
      exact hmeas.norm.pow 2
    · filter_upwards [ae_restrict_mem hrect] with p hp
      have hp1 : K.r₁ ≤ p.1 := hp.1.1
      simp only [CellBox.lineWeight, h0, if_false, one_mul]
      rw [Real.norm_of_nonneg (by positivity)]
      have hq : 1 ≤ K.r₁⁻¹ * p.1 := by
        rw [← div_eq_inv_mul, one_le_div hr]
        exact hp1
      have hx : 0 ≤ ‖modeVec m n v p.1 p.2 a‖ ^ 2 := by positivity
      nlinarith

end Breakdown.CellCert.CellAnalysis

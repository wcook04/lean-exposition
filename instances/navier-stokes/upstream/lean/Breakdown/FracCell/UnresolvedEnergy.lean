import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.CylIntegral

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Spectral.Internal.CylIntegral

private theorem symm_apply (r θ z : ℝ) :
    cylMap.symm ((r, θ), z) = ((r * Real.cos θ, r * Real.sin θ), z) := by
  simp [cylMap]

private theorem symm_meas : Measurable (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) := by
  have h : (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) = fun x => (polarCoord.symm x.1, x.2) := rfl
  rw [h]
  exact ((continuous_polarCoord_symm.comp continuous_fst).prodMk continuous_snd).measurable

private theorem symm_qmp :
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

private theorem second_comp_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    AEStronglyMeasurable (fun x => H (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
  hs.measurable_second.comp_quasiMeasurePreserving
    (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)

private theorem single_cont (i : Fin 3) :
    Continuous fun t : ℝ => (EuclideanSpace.single i t : Space) := by
  have h : (fun t : ℝ => (EuclideanSpace.single i t : Space)) =
      fun t => t • (EuclideanSpace.single i 1 : Space) := by
    funext t
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  exact continuous_id.smul continuous_const

private theorem frameUnit_cont (c : Fin 3) : Continuous fun θ : ℝ => frameUnit θ c := by
  fin_cases c
  · show Continuous fun θ : ℝ => radialUnit θ
    exact ((single_cont 0).comp Real.continuous_cos).add ((single_cont 1).comp Real.continuous_sin)
  · show Continuous fun θ : ℝ => angularUnit θ
    exact ((single_cont 0).comp Real.continuous_sin.neg).add
      ((single_cont 1).comp Real.continuous_cos)
  · exact continuous_const

private theorem frameThird_cont (a b c : Fin 3) :
    Continuous fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => frameThird q.1 q.2 a b c := by
  unfold frameThird
  exact ((continuous_snd.clm_apply ((frameUnit_cont c).comp continuous_fst)).clm_apply
    ((frameUnit_cont b).comp continuous_fst)).inner ((frameUnit_cont a).comp continuous_fst)

private def kern (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (x : (ℝ × ℝ) × ℝ) : ℂ :=
  Complex.exp (-(azimuth m n * x.2 : ℝ) * Complex.I) *
    (frameThird x.2 (H (cylPoint x.1.1 x.2 x.1.2)) a b c : ℂ)

private theorem kern_periodic (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (p : ℝ × ℝ) :
    Function.Periodic (fun θ => kern m n H a b c (p, θ)) (2 * Real.pi) := by
  intro θ
  have h1 : radialUnit (θ + 2 * Real.pi) = radialUnit θ := by simp [radialUnit]
  have h2 : angularUnit (θ + 2 * Real.pi) = angularUnit θ := by simp [angularUnit]
  have h3 : cylPoint p.1 (θ + 2 * Real.pi) p.2 = cylPoint p.1 θ p.2 := by simp [cylPoint]
  have h4 : frameUnit (θ + 2 * Real.pi) = frameUnit θ := by simp [frameUnit, h1, h2]
  have h5 : Complex.exp (-(azimuth m n * (θ + 2 * Real.pi) : ℝ) * Complex.I) =
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) := by
    have e : -((azimuth m n * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I =
        -((azimuth m n * θ : ℝ) : ℂ) * Complex.I +
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [azimuth]
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [kern, frameThird, h3, h4, h5]

private theorem mode_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a b c p =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n H a b c (p, θ) := by
  have hper := (kern_periodic m n H a b c p).intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hper
  rw [← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), ← hper]
  rfl

private theorem kern_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a b c : Fin 3) :
    AEStronglyMeasurable (kern m n H a b c)
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
        (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hset : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi =ᵐ[volume]
      swapEquiv ⁻¹' cylMap.target := by
    rw [swapEquiv_preimage]
    exact Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm
  rw [Measure.restrict_congr_set hset]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hΨ : Continuous fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      Complex.exp (-(azimuth m n * q.1 : ℝ) * Complex.I) * (frameThird q.1 q.2 a b c : ℂ) := by
    have := frameThird_cont a b c
    fun_prop
  have hk := hΨ.comp_aestronglyMeasurable
      ((continuous_snd.comp continuous_fst).aestronglyMeasurable.prodMk (second_comp_meas hs))
  refine (hk.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply, swapEquiv_apply, kern]
  rw [symm_apply, toSpace_apply]
  rfl


private theorem mode_meas {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a b c : Fin 3) :
    AEStronglyMeasurable (modeThird m n H a b c) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have h := (kern_meas hs n a b c).integral_prod_right'
  have e : modeThird m n H a b c = fun p =>
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n H a b c (p, θ) :=
    funext (mode_eq m n H a b c)
  rw [e]
  exact h.const_mul _

private theorem coord_expand (u : Space) : ∑ i, u i • unitVector i = u := by
  ext j
  simp [unitVector, Pi.single_apply]

private theorem apply_bound (L : Space →L[ℝ] Space →L[ℝ] Space) (u w : Space)
    (hu : ∀ i, |u i| ≤ 1) (hw : ∀ j, |w j| ≤ 1) :
    ‖L u w‖ ≤ ∑ i, ∑ j, ‖L (unitVector i) (unitVector j)‖ := by
  rw [← coord_expand u, ← coord_expand w]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
  refine le_trans ?_ (le_of_eq Finset.sum_comm)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hw i)).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using hu j)

private theorem frameUnit_coord (θ : ℝ) (c k : Fin 3) : |frameUnit θ c k| ≤ 1 := by
  fin_cases c <;> fin_cases k <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Real.abs_cos_le_one, Real.abs_sin_le_one]

private theorem frameUnit_norm (θ : ℝ) (c : Fin 3) : ‖frameUnit θ c‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  fin_cases c <;> simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit]

private theorem frameThird_sq (θ : ℝ) (L : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird θ L a b c ^ 2 ≤ 9 * ∑ i, ∑ j, ‖L (unitVector i) (unitVector j)‖ ^ 2 := by
  have h1 : |frameThird θ L a b c| ≤ ∑ i, ∑ j, ‖L (unitVector i) (unitVector j)‖ := by
    unfold frameThird
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [frameUnit_norm, mul_one]
    exact apply_bound L _ _ (frameUnit_coord θ c) (frameUnit_coord θ b)
  have h2 : (∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖) ^ 2 ≤
      9 * ∑ i, ∑ j, ‖L (unitVector i) (unitVector j)‖ ^ 2 := by
    have hi : ∀ i : Fin 3, (∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖) ^ 2 ≤
        3 * ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖ ^ 2 := fun i => by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j : Fin 3 => ‖L (unitVector i) (unitVector j)‖)
    have ho : (∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖) ^ 2 ≤
        3 * ∑ i : Fin 3, (∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖) ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin 3 => ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖)
    refine ho.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i)
      (by norm_num : (0 : ℝ) ≤ 3)) ?_)
    rw [← Finset.mul_sum]
    ring
  have h0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc frameThird θ L a b c ^ 2 = |frameThird θ L a b c| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ _ := h2

private theorem kern_sq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (x : (ℝ × ℝ) × ℝ) :
    ‖kern m n H a b c x‖ ^ 2 ≤
      9 * ∑ i, ∑ j, ‖H (cylPoint x.1.1 x.2 x.1.2) (unitVector i) (unitVector j)‖ ^ 2 := by
  unfold kern
  rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  exact frameThird_sq _ _ a b c

private theorem sq_integral_le {f : ℝ → ℂ} {g : ℝ → ℝ}
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

private def entrySqSum (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) : ℝ :=
  ∑ i, ∑ j, ‖H y (unitVector i) (unitVector j)‖ ^ 2

private theorem mode_integrable_half {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    (a b c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n H a b c p‖ ^ 2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have hp := Real.pi_pos
  have hF : Integrable (entrySqSum H) := hs.second_two
  have hG : Integrable (fun w => entrySqSum H (toSpace w)) :=
    (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hF
  have hH := change_integrable hG
  have h1 : IntegrableOn
      ((fun x : (ℝ × ℝ) × ℝ => x.1.1 * entrySqSum H (toSpace (cylMap.symm x))) ∘ swapEquiv)
      (swapEquiv ⁻¹' cylMap.target) :=
    (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  rw [swapEquiv_preimage] at h1
  have h2 : IntegrableOn
      ((fun x : (ℝ × ℝ) × ℝ => x.1.1 * entrySqSum H (toSpace (cylMap.symm x))) ∘ swapEquiv)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi) :=
    h1.congr_set_ae (Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm)
  have h3 : IntegrableOn (fun x : (ℝ × ℝ) × ℝ => x.1.1 * entrySqSum H (cylPoint x.1.1 x.2 x.1.2))
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
  have hks := (kern_meas hs n a b c).prodMk_left
  refine (hB.const_mul (9 / (2 * Real.pi))).mono'
    (continuous_fst.aestronglyMeasurable.mul ((mode_meas hs n a b c).norm.pow 2)) ?_
  filter_upwards [hsl, hks, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)]
    with q hq hk hqS
  have hpos : 0 < q.1 := hqS.1
  have hgi : IntegrableOn (fun θ => 9 * entrySqSum H (cylPoint q.1 θ q.2)) (Ioc (-Real.pi) Real.pi) := by
    refine (hq.const_mul (9 * q.1⁻¹)).congr (ae_of_all _ fun θ => ?_)
    simp only []
    field_simp
  have hcs := sq_integral_le hk hgi (fun θ => kern_sq m n H a b c (q, θ))
  rw [integral_const_mul] at hcs
  have e1 : ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * entrySqSum H (cylPoint q.1 θ q.2) =
      q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, entrySqSum H (cylPoint q.1 θ q.2) :=
    integral_const_mul _ _
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  show ‖q.1 * ‖modeThird m n H a b c q‖ ^ 2‖ ≤
    9 / (2 * Real.pi) * ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * entrySqSum H (cylPoint q.1 θ q.2)
  rw [e1, Real.norm_of_nonneg (by positivity), mode_eq, norm_mul, mul_pow, hn]
  calc q.1 * ((1 / (2 * Real.pi)) ^ 2 * ‖∫ θ in Ioc (-Real.pi) Real.pi, kern m n H a b c (q, θ)‖ ^ 2)
      ≤ q.1 * ((1 / (2 * Real.pi)) ^ 2 *
          (2 * Real.pi * (9 * ∫ θ in Ioc (-Real.pi) Real.pi, entrySqSum H (cylPoint q.1 θ q.2)))) := by
        gcongr
    _ = 9 / (2 * Real.pi) * (q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, entrySqSum H (cylPoint q.1 θ q.2)) := by
        field_simp

private theorem mode_integrable {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (a b c : Fin 3) :
    IntegrableOn (fun p => p.1 * ‖modeThird m n H a b c p‖ ^ 2) K.rect := by
  refine (mode_integrable_half hs n a b c).of_forall_sdiff_eq_zero
    (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  have h1 : K.r₁ ≤ p.1 := hp.1.1.1
  have h2 : ¬ (0 < p.1) := fun h => hp.2 ⟨h, trivial⟩
  have h3 : p.1 = 0 := le_antisymm (not_lt.mp h2) (le_trans hK.r_order.1 h1)
  simp [h3]


private theorem rect_meas (K : CellBox) : MeasurableSet K.rect :=
  measurableSet_Icc.prod measurableSet_Icc

private theorem refR_sq_le {K : CellBox} (hK : IsCellBox K) {r : ℝ} (h1 : K.r₁ ≤ r) (h2 : r ≤ K.r₂) :
    K.refR r ^ 2 ≤ 1 := by
  have hd : 0 < K.r₂ - K.r₁ := sub_pos.mpr hK.r_order.2
  rw [CellBox.refR, div_pow, div_le_one (by positivity)]
  nlinarith

private theorem refZ_sq_le {K : CellBox} (hK : IsCellBox K) {z : ℝ} (h1 : K.z₁ ≤ z) (h2 : z ≤ K.z₂) :
    K.refZ z ^ 2 ≤ 1 := by
  have hd : 0 < K.z₂ - K.z₁ := sub_pos.mpr hK.z_order.2
  rw [CellBox.refZ, div_pow, div_le_one (by positivity)]
  nlinarith

private theorem frame_weight {K : CellBox} (hK : IsCellBox K) {r x : ℝ} (h1 : K.r₁ ≤ r)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ K.innerRadius * (K.lineWeight r * x) ∧ K.innerRadius * (K.lineWeight r * x) ≤ r := by
  have h0 := hK.r_order.1
  unfold CellBox.innerRadius CellBox.lineWeight
  split_ifs with h
  · rw [h] at h1
    constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem angular_weight {K : CellBox} (hK : IsCellBox K) (n : ℤ) {r : ℝ} (h1 : K.r₁ ≤ r)
    (h2 : r ≤ K.r₂) :
    0 ≤ K.angularWeight n * K.lineWeight r * r ^ 2 ∧ K.angularWeight n * K.lineWeight r * r ^ 2 ≤ r := by
  have h0 := hK.r_order.1
  have hr0 : 0 ≤ r := le_trans h0 h1
  have hr2 : 0 < K.r₂ := lt_of_le_of_lt h0 hK.r_order.2
  have ht1 : r * K.r₂⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hr2]
    exact h2
  have ht0 : 0 ≤ r * K.r₂⁻¹ := mul_nonneg hr0 (inv_nonneg.mpr hr2.le)
  unfold CellBox.angularWeight CellBox.lineWeight
  split_ifs with h hn
  · simp [hr0]
  · have e : K.r₂⁻¹ ^ 2 * r * r ^ 2 = r * (r * K.r₂⁻¹) ^ 2 := by ring
    rw [e]
    have hq : (r * K.r₂⁻¹) ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hq hr0]
  · have e : K.r₂⁻¹ * 1 * r ^ 2 = r * (r * K.r₂⁻¹) := by ring
    rw [e]
    constructor
    · positivity
    · nlinarith

private theorem weighted_le {K : CellBox} {w : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hw : ∀ p ∈ K.rect, 0 ≤ w p ∧ w p ≤ p.1)
    (hg : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) :
    ∫ p in K.rect, w p * ‖g p‖ ^ 2 ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    exact mul_nonneg (hw p hp).1 (sq_nonneg _)
  · filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
    exact mul_le_mul_of_nonneg_right (hw p hp).2 (sq_nonneg _)

private theorem radial_term {K : CellBox} (hK : IsCellBox K) {g : ℝ × ℝ → ℂ}
    (hg : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) :
    K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) g
      ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  have hw : ∀ p ∈ K.rect, 0 ≤ K.innerRadius * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) ∧
      K.innerRadius * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) ≤ p.1 := fun p hp =>
    frame_weight hK hp.1.1 (sub_nonneg.mpr (refR_sq_le hK hp.1.1 hp.1.2))
      (sub_le_self _ (sq_nonneg _))
  refine le_trans (le_of_eq ?_) (weighted_le hw hg)
  unfold CellBox.normSqOn
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

private theorem height_term {K : CellBox} (hK : IsCellBox K) {g : ℝ × ℝ → ℂ}
    (hg : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) :
    K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) g
      ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  have hw : ∀ p ∈ K.rect, 0 ≤ K.innerRadius * (K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) ∧
      K.innerRadius * (K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) ≤ p.1 := fun p hp =>
    frame_weight hK hp.1.1 (sub_nonneg.mpr (refZ_sq_le hK hp.2.1 hp.2.2))
      (sub_le_self _ (sq_nonneg _))
  refine le_trans (le_of_eq ?_) (weighted_le hw hg)
  unfold CellBox.normSqOn
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

private theorem angular_term {K : CellBox} (hK : IsCellBox K) (n : ℤ) {g : ℝ × ℝ → ℂ}
    (hg : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect) :
    K.angularWeight n * K.normSqOn K.lineWeightFn (fun p => (p.1 : ℂ) * g p)
      ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  have hw : ∀ p ∈ K.rect, 0 ≤ K.angularWeight n * K.lineWeight p.1 * p.1 ^ 2 ∧
      K.angularWeight n * K.lineWeight p.1 * p.1 ^ 2 ≤ p.1 := fun p hp =>
    angular_weight hK n hp.1.1 hp.1.2
  refine le_trans (le_of_eq ?_) (weighted_le hw hg)
  unfold CellBox.normSqOn
  rw [← integral_const_mul]
  congr 1
  funext p
  simp only [CellBox.lineWeightFn, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring


theorem unresolvedEnergy : UnresolvedEnergyStatement := by
  intro K hK m v G H hs n
  have hint : ∀ a b c : Fin 3,
      IntegrableOn (fun p => p.1 * ‖modeThird m n H a b c p‖ ^ 2) K.rect :=
    fun a b c => mode_integrable hK hs n a b c
  have hrhs : ∫ p in K.rect, p.1 * secondModeSq m n H p =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∫ p in K.rect, p.1 * ‖modeThird m n H a b c p‖ ^ 2 := by
    unfold secondModeSq
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun b _ => integrable_finsetSum _ (fun c _ => hint a b c)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hint a b c))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ (fun c _ => hint a b c)]
  rw [hrhs]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [Fin.sum_univ_three]
  unfold CellBox.fullGradWeight
  rw [mul_add]
  have h0 : K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
      (radialGradMode m n H a b) ≤ ∫ p in K.rect, p.1 * ‖modeThird m n H a b 0 p‖ ^ 2 :=
    radial_term hK (hint a b 0)
  have h2 : K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
      (heightGradMode m n H a b) ≤ ∫ p in K.rect, p.1 * ‖modeThird m n H a b 2 p‖ ^ 2 :=
    height_term hK (hint a b 2)
  have h1 : K.angularWeight n * K.normSqOn K.lineWeightFn (angularGradMode m n H a b)
      ≤ ∫ p in K.rect, p.1 * ‖modeThird m n H a b 1 p‖ ^ 2 :=
    angular_term hK n (hint a b 1)
  linarith


end Breakdown.CellCert.CellAnalysis

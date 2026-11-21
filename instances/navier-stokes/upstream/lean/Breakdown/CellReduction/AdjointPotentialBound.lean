import Breakdown.CellReduction.AdjointPotentialBoundSlice

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

namespace PotentialBound

theorem ae_slice_finite {f : ℝ → Space → ℝ} (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (h : periodLIntegral f < ⊤) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (f σ y) < ⊤ := by
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) periodMeasure :=
    (aesm_period hf).aemeasurable.ennreal_ofReal
  exact ae_lt_top' hm.lintegral_prod_right' h.ne

theorem abs_matrixInner_le (A B : Space →L[ℝ] Space) :
    |matInner A B| ≤ Real.sqrt (matSq A) * Real.sqrt (matSq B) := by
  unfold matInner matSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm (A (unitVector i)) (B (unitVector i))).trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem period_lintegral_le_sq {f : ℝ → Space → ℝ} (hf : periodLIntegral f < ⊤) :
    periodLIntegral f ≤ ENNReal.ofReal (Real.sqrt (periodLIntegral f).toReal ^ 2) := by
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf.ne]

theorem period_matrix_bound {G M : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hM : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hi : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (M z.1 z.2)) periodMeasure)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : periodLIntegral (fun σ y => matSq (G σ y)) ≤ ENNReal.ofReal (A ^ 2))
    (hB : periodLIntegral (fun σ y => matSq (M σ y)) ≤ ENNReal.ofReal (B ^ 2)) :
    |periodMatrixIntegral G M| ≤ A * B := by
  have hGp := aesm_period hG
  have hMp := aesm_period hM
  have hsG : AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) periodMeasure :=
    continuous_entrySq.comp_aestronglyMeasurable hGp
  have hsM : AEStronglyMeasurable (fun z : ℝ × Space => matSq (M z.1 z.2)) periodMeasure :=
    continuous_entrySq.comp_aestronglyMeasurable hMp
  have e : ∀ A : Space →L[ℝ] Space, Real.sqrt (matSq A) ^ 2 = matSq A := fun A =>
    Real.sq_sqrt (entrySq_nonneg A)
  unfold periodMatrixIntegral
  rw [iterated_eq (f := fun σ y => matInner (G σ y) (M σ y)) hi]
  refine abs_integral_le_of_le_mul (h := fun z : ℝ × Space => matInner (G z.1 z.2) (M z.1 z.2))
    (a := fun z => Real.sqrt (matSq (G z.1 z.2)))
    (b := fun z => Real.sqrt (matSq (M z.1 z.2))) hsG.aemeasurable.sqrt hsM.aemeasurable.sqrt
    (fun z => Real.sqrt_nonneg _) (fun z => Real.sqrt_nonneg _)
    (ae_of_all _ fun z => abs_matrixInner_le _ _) hA0 hB0 ?_ ?_
  · simp only [e]
    rw [← periodL_eq (f := fun σ y => matSq (G σ y)) hsG.aemeasurable.ennreal_ofReal]
    exact hA
  · simp only [e]
    rw [← periodL_eq (f := fun σ y => matSq (M σ y)) hsM.aemeasurable.ennreal_ofReal]
    exact hB

theorem period_inner_bound {f g : ℝ → Space → Space}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hi : Integrable (fun z : ℝ × Space => inner ℝ (f z.1 z.2) (g z.1 z.2)) periodMeasure)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : periodLIntegral (fun σ y => ‖f σ y‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (hB : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) ≤ ENNReal.ofReal (B ^ 2)) :
    |∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (f σ y) (g σ y)| ≤ A * B := by
  have hfp := aesm_period hf
  have hgp := aesm_period hg
  rw [iterated_eq (f := fun σ y => inner ℝ (f σ y) (g σ y)) hi]
  refine abs_integral_le_of_le_mul (h := fun z : ℝ × Space => inner ℝ (f z.1 z.2) (g z.1 z.2))
    (a := fun z => ‖f z.1 z.2‖) (b := fun z => ‖g z.1 z.2‖)
    hfp.norm.aemeasurable hgp.norm.aemeasurable (fun z => norm_nonneg _) (fun z => norm_nonneg _)
    (ae_of_all _ fun z => abs_real_inner_le_norm _ _) hA0 hB0 ?_ ?_
  · have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖f z.1 z.2‖ ^ 2)) periodMeasure :=
      (hfp.norm.pow 2).aemeasurable.ennreal_ofReal
    rw [← periodL_eq (f := fun σ y => ‖f σ y‖ ^ 2) hm]
    exact hA
  · have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) periodMeasure :=
      (hgp.norm.pow 2).aemeasurable.ennreal_ofReal
    rw [← periodL_eq (f := fun σ y => ‖g σ y‖ ^ 2) hm]
    exact hB

theorem pairing_two_term_le {a b x y w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 < w) :
    a * x + b * y ≤ Real.sqrt (a ^ 2 + b ^ 2 / w) * Real.sqrt (x ^ 2 + w * y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have key : w * ((a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2) = (a * w * y - b * x) ^ 2 := by
    field_simp
    ring
  have h : 0 ≤ (a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2 := by
    by_contra hneg
    push_neg at hneg
    have : w * ((a ^ 2 + b ^ 2 / w) * (x ^ 2 + w * y ^ 2) - (a * x + b * y) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hw hneg
    rw [key] at this
    exact absurd this (not_lt.2 (sq_nonneg _))
  linarith

theorem continuous_traceSecond : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  exact continuous_finset_sum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem integrable_period_of_lintegral {f : ℝ → Space → ℝ}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (h0 : ∀ σ y, 0 ≤ f σ y)
    (h : periodLIntegral f < ⊤) : Integrable (fun z : ℝ × Space => f z.1 z.2) periodMeasure := by
  have hm := aesm_period hf
  refine ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z : ℝ × Space => h0 z.1 z.2)).2 ?_⟩
  rw [← periodL_eq (f := f) hm.aemeasurable.ennreal_ofReal]
  exact h

theorem period_add_smul {f g : ℝ → Space → ℝ}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hf0 : ∀ σ y, 0 ≤ f σ y) (hg0 : ∀ σ y, 0 ≤ g σ y) {w : ℝ} (hw : 0 ≤ w) :
    periodLIntegral (fun σ y => f σ y + w * g σ y) = periodLIntegral f + ENNReal.ofReal w * periodLIntegral g := by
  have hfm := (aesm_period hf).aemeasurable.ennreal_ofReal
  have hgm := (aesm_period hg).aemeasurable.ennreal_ofReal
  have hsm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2 + w * g z.1 z.2)) periodMeasure :=
    ((aesm_period hf).add ((aesm_period hg).const_mul w)).aemeasurable.ennreal_ofReal
  rw [periodL_eq (f := fun σ y => f σ y + w * g σ y) hsm, periodL_eq (f := f) hfm, periodL_eq (f := g) hgm,
    ← lintegral_const_mul'' _ hgm, ← lintegral_add_left' hfm]
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_add (hf0 _ _) (mul_nonneg hw (hg0 _ _)), ENNReal.ofReal_mul hw]

end PotentialBound

end Internal

open Internal Internal.PotentialBound in
theorem potentialBoundHolds_proof : PotentialBoundHolds := by
  intro Γ P w₀ C γ v g T G H K p n hw₀ hv hR hp hn hrem
  obtain ⟨-, hRint, hRb⟩ := hrem v G hv.measurable_velocity hv.measurable_gradient hv.weak_gradient
    hv.sixth_power hv.gradient_finite
  have hγ := hR.rate_gt
  have hSumSecondPartials : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    continuous_traceSecond.comp_aestronglyMeasurable hv.measurable_secondDeriv
  have hGsq : AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    continuous_entrySq.comp_aestronglyMeasurable hv.measurable_gradient
  have hφD : AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (p.phi z.1) z.2) volume :=
    (slice_fderiv_continuous hp.phi_smooth).aestronglyMeasurable
  have hθm : AEStronglyMeasurable (fun z : ℝ × Space => p.theta z.1 z.2) volume :=
    hp.theta_smooth.continuous.aestronglyMeasurable
  have hvs : ∀ᵐ σ, AEStronglyMeasurable (v σ) volume := hv.measurable_velocity.prodMk_left
  have hGs : ∀ᵐ σ, AEStronglyMeasurable (G σ) volume := hv.measurable_gradient.prodMk_left
  have hHs : ∀ᵐ σ, AEStronglyMeasurable (H σ) volume := hv.measurable_secondDeriv.prodMk_left
  have hTs : ∀ᵐ σ, AEStronglyMeasurable (T σ) volume := hR.residual_measurable.prodMk_left
  have hgood : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫ y, inner ℝ (v σ y) (T σ y)) + (∫ y, matInner (G σ y) (K σ y)) =
        (∫ y, inner ℝ (v σ y) (remainderField w₀ T K p σ y)) - (∫ y, inner ℝ (secondDerivTrace (H σ y)) (p.theta σ y))
          + w₀ * (∫ y, matInner (G σ y) (fderiv ℝ (p.phi σ) y)) - ∫ y, matInner (G σ y) (p.flux σ y) := by
    filter_upwards [ae_restrict_of_ae hvs, ae_restrict_of_ae hGs, ae_restrict_of_ae hHs, ae_restrict_of_ae hTs,
      ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.weak_secondDeriv, ae_restrict_of_ae hv.divergence_free,
      ae_restrict_of_ae hv.sixth_power, ae_slice_finite hGsq hv.gradient_finite,
      ae_slice_finite (hSumSecondPartials.norm.pow 2) hv.sumSecondPartials_finite] with σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    have hH2 : Integrable (fun y => ‖secondDerivTrace (H σ y)‖ ^ 2) :=
      integrable_of_lintegral_lt ((continuous_traceSecond.comp_aestronglyMeasurable h3).norm.pow 2)
        (fun y => by positivity) h10
    exact (slice_identity w₀ ⟨h1, h2, h5, h8, h9⟩ h7 h6 hH2 hR hp σ h4).2.2
  have iT : IntegrableOn (fun σ => ∫ y, inner ℝ (v σ y) (T σ y)) (Set.Icc (0 : ℝ) 1) :=
    (pairing_integrable weightedPairingIntegrable_proof hv hγ hR.residual_measurable
      (fun σ y => (hR.decay σ y).1)).integral_prod_left
  have iKp := matrix_integrable hv (B := C) (β := γ + 1) (by linarith) hR.flux_measurable
    (fun σ y => (hR.decay σ y).2)
  have iK : IntegrableOn (fun σ => ∫ y, matInner (G σ y) (K σ y)) (Set.Icc (0 : ℝ) 1) := iKp.integral_prod_left
  have iφp := matrix_integrable hv (M := fun σ y => fderiv ℝ (p.phi σ) y) (B := C) (β := 2) (by norm_num) hφD
    (fun σ y => by rw [Real.rpow_two]; exact (hp.value_decay σ y).2.2.2.1)
  have iφ : IntegrableOn (fun σ => ∫ y, matInner (G σ y) (fderiv ℝ (p.phi σ) y)) (Set.Icc (0 : ℝ) 1) :=
    iφp.integral_prod_left
  have iYp := matrix_integrable hv (M := p.flux) (B := C) (β := 2) (by norm_num) hp.flux_measurable
    (fun σ y => by rw [Real.rpow_two]; exact (hp.value_decay σ y).2.2.2.2.1)
  have iY : IntegrableOn (fun σ => ∫ y, matInner (G σ y) (p.flux σ y)) (Set.Icc (0 : ℝ) 1) := iYp.integral_prod_left
  have iθp : Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2)) (p.theta z.1 z.2)) periodMeasure := by
    have hL2 := integrable_period_of_lintegral (hSumSecondPartials.norm.pow 2) (fun σ y => by positivity) hv.sumSecondPartials_finite
    have hw : Integrable (fun z : ℝ × Space => (1 : ℝ) * (C ^ 2 * (1 + ‖z.2‖) ^ (-(4 : ℝ)))) periodMeasure :=
      (integrable_const (1 : ℝ)).mul_prod ((space_weight_integrable (by norm_num)).const_mul _)
    refine ((hL2.add hw).div_const 2).mono' ((aesm_period hSumSecondPartials).inner (aesm_period hθm)) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hb := (hp.value_decay z.1 z.2).1
    rw [div_pow_eq_rpow _ _ (norm_nonneg _)] at hb
    have hb2 := sq_le_of_decay (norm_nonneg z.2) (norm_nonneg _) hb
    have e : -(2 * ((2 : ℕ) : ℝ)) = -(4 : ℝ) := by norm_num
    rw [e] at hb2
    simp only [Pi.add_apply, one_mul]
    nlinarith [sq_nonneg (‖secondDerivTrace (H z.1 z.2)‖ - ‖p.theta z.1 z.2‖)]
  have iθ : IntegrableOn (fun σ => ∫ y, inner ℝ (secondDerivTrace (H σ y)) (p.theta σ y)) (Set.Icc (0 : ℝ) 1) :=
    iθp.integral_prod_left
  have hsum : periodInnerIntegral v T + periodMatrixIntegral G K =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (v σ y) (remainderField w₀ T K p σ y))
        - (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (secondDerivTrace (H σ y)) (p.theta σ y))
        + w₀ * (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (fderiv ℝ (p.phi σ) y))
        - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (p.flux σ y) := by
    unfold periodInnerIntegral periodMatrixIntegral
    rw [← integral_add iT iK, integral_congr_ae hgood, integral_sub, integral_add, integral_sub,
      integral_const_mul]
    all_goals first
      | exact hRint | exact iθ | exact iφ.const_mul _ | exact iY | exact hRint.sub iθ
      | exact (hRint.sub iθ).add (iφ.const_mul _)
  obtain ⟨gn, hgn⟩ : ∃ x : ℝ, x = gradientNorm G := ⟨_, rfl⟩
  obtain ⟨hnn, hhnn⟩ : ∃ x : ℝ, x = Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal :=
    ⟨_, rfl⟩
  have hgn0 : 0 ≤ gn := hgn ▸ Real.sqrt_nonneg _
  have hhn0 : 0 ≤ hnn := hhnn ▸ Real.sqrt_nonneg _
  have hbθ : |∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (secondDerivTrace (H σ y)) (p.theta σ y)| ≤ hnn * n.theta :=
    period_inner_bound (f := fun σ y => secondDerivTrace (H σ y)) (g := p.theta) hSumSecondPartials hθm iθp hhn0 hn.theta_nonneg
      (hhnn ▸ period_lintegral_le_sq hv.sumSecondPartials_finite) hn.theta_le
  have hbφ : |periodMatrixIntegral G (fun σ y => fderiv ℝ (p.phi σ) y)| ≤ gn * n.phiGrad :=
    period_matrix_bound (G := G) (M := fun σ y => fderiv ℝ (p.phi σ) y) hv.measurable_gradient hφD iφp hgn0 hn.phiGrad_nonneg
      (hgn ▸ period_lintegral_le_sq hv.gradient_finite) hn.phiGrad_le
  have hbY : |periodMatrixIntegral G p.flux| ≤ gn * n.flux :=
    period_matrix_bound (G := G) (M := p.flux) hv.measurable_gradient hp.flux_measurable iYp hgn0 hn.flux_nonneg
      (hgn ▸ period_lintegral_le_sq hv.gradient_finite) hn.flux_le
  have hbR : |periodInnerIntegral v (remainderField w₀ T K p)| ≤ n.remainder * gn := hgn ▸ hRb
  unfold periodMatrixIntegral at hbφ hbY
  unfold periodInnerIntegral at hbR
  have htot : |periodInnerIntegral v T + periodMatrixIntegral G K| ≤
      n.theta * hnn + (w₀ * n.phiGrad + n.flux + n.remainder) * gn := by
    rw [hsum]
    have a1 := abs_le.1 hbR
    have a2 := abs_le.1 hbθ
    have a3 := abs_le.1 hbφ
    have a4 := abs_le.1 hbY
    have b1 := mul_le_mul_of_nonneg_left a3.2 hw₀.le
    have b2 := mul_le_mul_of_nonneg_left a3.1 hw₀.le
    rw [abs_le]
    constructor <;> nlinarith
  have hE : weightedEnergy (fun _ => w₀) G H = hnn ^ 2 + w₀ * gn ^ 2 := by
    unfold weightedEnergy
    rw [period_add_smul (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) (g := fun σ y => matSq (G σ y))
      (hSumSecondPartials.norm.pow 2) hGsq (fun σ y => by positivity) (fun σ y => entrySq_nonneg _) hw₀.le,
      ENNReal.toReal_add hv.sumSecondPartials_finite.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.gradient_finite.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hw₀.le, hhnn, hgn, gradientNorm,
      Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [hE, potentialDefect]
  refine htot.trans (pairing_two_term_le hn.theta_nonneg (by
    have := hn.phiGrad_nonneg; have := hn.flux_nonneg; have := hn.remainder_nonneg; positivity) hhn0 hgn0 hw₀)

end AdjointDefect

end Breakdown

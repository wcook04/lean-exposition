import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePowerJumpsCover

open CellCert.GivenFields SteadyCert

private theorem dim_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

private theorem weight_inv_norm_integrable :
    Integrable (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖⁻¹) := by
  have key := (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => (1 + r) ^ (-(3 : ℝ)) * r⁻¹)).2
  refine key ?_
  rw [dim_space]
  have hI : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) := by
    apply integrable_one_add_norm
    simp
  refine (hI.integrableOn (s := Set.Ioi 0)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun y : ℝ => y ^ 2).aestronglyMeasurable.smul
      (((by fun_prop : Continuous fun y : ℝ => 1 + y).measurable.pow_const _).mul
        measurable_inv).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := hy
    have h1 : 0 < 1 + y := by linarith
    simp only [Nat.add_one_sub_one, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hy0]
    rw [Real.rpow_neg h1.le, Real.rpow_neg h1.le, abs_of_nonneg (by positivity)]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    calc _ = y / (1 + y) * ((1 + y) ^ 2)⁻¹ := by field_simp
      _ ≤ 1 * ((1 + y) ^ 2)⁻¹ := by
          gcongr
          rw [div_le_one h1]
          linarith
      _ = _ := one_mul _

private theorem sq_mul_weight_le_one {y : ℝ} (hy : 0 ≤ y) : y ^ 2 * (1 + y) ^ (-(3 : ℝ)) ≤ 1 := by
  have h1 : 0 < 1 + y := by linarith
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith [sq_nonneg y, mul_nonneg hy (sq_nonneg y)]

private theorem weight_shell :
    ∃ C : ℝ, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) {y : Space | a ≤ ‖y‖ ∧ ‖y‖ ≤ b} ∧
      (∫ y in {y : Space | a ≤ ‖y‖ ∧ ‖y‖ ≤ b}, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ C * (b - a) := by
  set V : ℝ := (volume : Measure Space).real (Metric.ball 0 1) with hV
  refine ⟨3 * V, fun a b ha hab => ?_⟩
  set S : Set Space := {y : Space | a ≤ ‖y‖ ∧ ‖y‖ ≤ b} with hS
  have hSm : MeasurableSet S :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet
  set f : ℝ → ℝ := (Set.Icc a b).indicator (fun r => (1 + r) ^ (-(3 : ℝ))) with hf
  have hind : S.indicator (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) = fun y => f ‖y‖ := by
    ext y
    by_cases hy : a ≤ ‖y‖ ∧ ‖y‖ ≤ b
    · rw [Set.indicator_of_mem (show y ∈ S from hy), hf, Set.indicator_of_mem (show ‖y‖ ∈ Set.Icc a b from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ S from hy), hf,
        Set.indicator_of_notMem (show ‖y‖ ∉ Set.Icc a b from hy)]
  have hbound : Integrable ((Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • f y ≤
      (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [dim_space, smul_eq_mul, hf]
    by_cases hyI : y ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hyI, Set.indicator_of_mem hyI]
      exact sq_mul_weight_le_one hy0.le
    · rw [Set.indicator_of_notMem hyI, Set.indicator_of_notMem hyI, mul_zero]
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • f y)
      (volume.restrict (Set.Ioi 0)) := by
    refine ((by fun_prop : Continuous fun y : ℝ => y ^ (Module.finrank ℝ Space - 1)).measurable.smul
      ?_).aestronglyMeasurable
    exact (((by fun_prop : Continuous fun y : ℝ => 1 + y).measurable.pow_const _)).indicator
      measurableSet_Icc
  have hnn : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ y ^ (Module.finrank ℝ Space - 1) • f y := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [smul_eq_mul, hf]
    exact mul_nonneg (pow_nonneg hy0.le _)
      (Set.indicator_nonneg (fun r hr => Real.rpow_nonneg (by linarith [hr.1]) _) y)
  have hIon : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • f y) (Set.Ioi 0) := by
    refine (hbound.integrableOn).mono' hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn y hy)]
    exact hpt y hy
  have hint : Integrable (fun y : Space => f ‖y‖) :=
    (integrable_fun_norm_addHaar (volume : Measure Space) (f := f)).2 hIon
  have hion : IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) S := by
    rw [← integrable_indicator_iff hSm, hind]
    exact hint
  refine ⟨hion, ?_⟩
  have hVpos : 0 ≤ V := measureReal_nonneg
  have hX : (∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • f y) ≤ b - a := by
    calc (∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • f y)
        ≤ ∫ y in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) y :=
          setIntegral_mono_on hIon hbound.integrableOn measurableSet_Ioi hpt
      _ ≤ ∫ y, (Set.Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) y :=
          setIntegral_le_integral hbound (Filter.Eventually.of_forall fun y =>
            Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      _ = b - a := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
            Real.volume_real_Icc_of_le hab]
  calc (∫ y in S, (1 + ‖y‖) ^ (-(3 : ℝ)))
      = ∫ y, f ‖y‖ := by rw [← integral_indicator hSm, hind]
    _ = Module.finrank ℝ Space • V • ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • f y :=
        integral_fun_norm_addHaar (volume : Measure Space) f
    _ ≤ 3 * V * (b - a) := by
        rw [dim_space] at hX
        rw [dim_space, smul_eq_mul, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hX (by positivity)


private def planeLift (t : ℝ) (p : Fin 2 → ℝ) : Space :=
  WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm (t, p))

private theorem planeLift_two (t : ℝ) (p : Fin 2 → ℝ) : planeLift t p 2 = t := by
  show Fin.insertNth (α := fun _ : Fin 3 => ℝ) (2 : Fin 3) t p 2 = t
  exact Fin.insertNth_apply_same _ _ _

private theorem planeLift_succAbove (t : ℝ) (p : Fin 2 → ℝ) (j : Fin 2) :
    planeLift t p ((2 : Fin 3).succAbove j) = p j := by
  show Fin.insertNth (α := fun _ : Fin 3 => ℝ) (2 : Fin 3) t p ((2 : Fin 3).succAbove j) = p j
  exact Fin.insertNth_apply_succAbove _ _ _ _

private theorem norm_le_lift (t : ℝ) (p : Fin 2 → ℝ) : ‖p‖ ≤ ‖planeLift t p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  rw [← planeLift_succAbove t p j]
  exact PiLp.norm_apply_le (planeLift t p) _

private theorem planeLift_sub (t s : ℝ) (p : Fin 2 → ℝ) :
    planeLift t p - planeLift s p = EuclideanSpace.single 2 (t - s) := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove (2 : Fin 3) i with h | ⟨j, rfl⟩
  · subst h
    simp [planeLift_two]
  · rw [PiLp.sub_apply, planeLift_succAbove, planeLift_succAbove, PiLp.single_apply,
      if_neg (Fin.succAbove_ne _ _)]
    simp

private theorem planeLift_norm_slope (t s : ℝ) (p : Fin 2 → ℝ) : |‖planeLift t p‖ - ‖planeLift s p‖| ≤ |t - s| := by
  have := abs_norm_sub_norm_le (planeLift t p) (planeLift s p)
  rwa [planeLift_sub, PiLp.norm_single, Real.norm_eq_abs] at this

private theorem band_slice {c δ : ℝ} (hc : |c| < 1) (p : Fin 2 → ℝ) {t s : ℝ}
    (ht : |planeLift t p 2 - c * ‖planeLift t p‖| ≤ δ) (hs : |planeLift s p 2 - c * ‖planeLift s p‖| ≤ δ) :
    |t - s| ≤ 2 * δ / (1 - |c|) := by
  rw [planeLift_two] at ht hs
  have hl := planeLift_norm_slope t s p
  have hκ : 0 < 1 - |c| := by linarith
  rw [le_div_iff₀ hκ]
  have hA : |(t - c * ‖planeLift t p‖) - (s - c * ‖planeLift s p‖)| ≤ 2 * δ :=
    (abs_sub _ _).trans (by linarith)
  have hB : |c * (‖planeLift t p‖ - ‖planeLift s p‖)| ≤ |c| * |t - s| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hl (abs_nonneg c)
  have hsum : |t - s| ≤ 2 * δ + |c| * |t - s| := by
    have heq : t - s = ((t - c * ‖planeLift t p‖) - (s - c * ‖planeLift s p‖)) + c * (‖planeLift t p‖ - ‖planeLift s p‖) := by
      ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [← heq]
    linarith
  have : |t - s| * (1 - |c|) = |t - s| - |c| * |t - s| := by ring
  linarith

private theorem weight_band (c : ℝ) :
    ∃ C : ℝ, |c| < 1 → ∀ δ : ℝ, 0 ≤ δ →
      IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) {y : Space | |y 2 - c * ‖y‖| ≤ δ} ∧
      (∫ y in {y : Space | |y 2 - c * ‖y‖| ≤ δ}, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ C * δ := by
  set J : ℝ := ∫ p : Fin 2 → ℝ, (1 + ‖p‖) ^ (-(3 : ℝ)) with hJ
  refine ⟨4 * J / (1 - |c|), fun hc δ hδ => ?_⟩
  have hκ : 0 < 1 - |c| := by linarith
  have hJi : Integrable (fun p : Fin 2 → ℝ => (1 + ‖p‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hJ0 : 0 ≤ J := integral_nonneg fun p => Real.rpow_nonneg (by positivity) _
  set T : Set Space := {y : Space | |y 2 - c * ‖y‖| ≤ δ} with hT
  have hcont2 : Continuous (fun y : Space => y 2) := by fun_prop
  have hTm : MeasurableSet T :=
    (isClosed_le ((hcont2.sub (continuous_const.mul continuous_norm)).abs)
      continuous_const).measurableSet
  set f : Space → ℝ := T.indicator (fun y => (1 + ‖y‖) ^ (-(3 : ℝ))) with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y =>
    Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (by positivity) _) y
  have hfm : Measurable f :=
    ((by fun_prop : Continuous fun y : Space => 1 + ‖y‖).measurable.pow_const _).indicator hTm
  set F : Space → ENNReal := fun y => ENNReal.ofReal (f y) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hfm
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have hG : Measurable (fun x : Fin 3 → ℝ => F (WithLp.toLp 2 x)) :=
    hFm.comp (PiLp.volume_preserving_toLp (ι := Fin 3)).measurable
  have hH : Measurable (fun z : ℝ × (Fin 2 → ℝ) => F (planeLift z.1 z.2)) :=
    hG.comp hmp.symm.measurable
  have hstep : ∫⁻ y, F y = ∫⁻ p : Fin 2 → ℝ, ∫⁻ t : ℝ, F (planeLift t p) := by
    rw [← (PiLp.volume_preserving_toLp (ι := Fin 3)).lintegral_comp hFm,
      ← hmp.symm.lintegral_comp hG]
    exact lintegral_prod_symm' (fun z : ℝ × (Fin 2 → ℝ) => F (planeLift z.1 z.2)) hH
  have hslice : ∀ p : Fin 2 → ℝ, ∫⁻ t, F (planeLift t p) ≤
      ENNReal.ofReal (4 * δ / (1 - |c|)) * ENNReal.ofReal ((1 + ‖p‖) ^ (-(3 : ℝ))) := by
    intro p
    by_cases hne : ∃ t₀, planeLift t₀ p ∈ T
    · obtain ⟨t₀, ht₀⟩ := hne
      set r : ℝ := 2 * δ / (1 - |c|) with hr
      have hr0 : 0 ≤ r := by positivity
      calc ∫⁻ t, F (planeLift t p)
          ≤ ∫⁻ t, (Set.Icc (t₀ - r) (t₀ + r)).indicator
              (fun _ => ENNReal.ofReal ((1 + ‖p‖) ^ (-(3 : ℝ)))) t := by
            refine lintegral_mono fun t => ?_
            by_cases ht : planeLift t p ∈ T
            · have hd := band_slice hc p ht ht₀
              rw [abs_le] at hd
              rw [Set.indicator_of_mem (show t ∈ Set.Icc (t₀ - r) (t₀ + r) from
                ⟨by linarith [hd.1], by linarith [hd.2]⟩)]
              simp only [hF, hf, Set.indicator_of_mem ht]
              apply ENNReal.ofReal_le_ofReal
              exact Real.rpow_le_rpow_of_nonpos (by positivity)
                (by linarith [norm_le_lift t p]) (by norm_num)
            · simp only [hF, hf, Set.indicator_of_notMem ht, ENNReal.ofReal_zero]
              exact zero_le
        _ = ENNReal.ofReal ((1 + ‖p‖) ^ (-(3 : ℝ))) * volume (Set.Icc (t₀ - r) (t₀ + r)) :=
            lintegral_indicator_const measurableSet_Icc _
        _ = ENNReal.ofReal (4 * δ / (1 - |c|)) * ENNReal.ofReal ((1 + ‖p‖) ^ (-(3 : ℝ))) := by
            rw [Real.volume_Icc, mul_comm]
            congr 2
            rw [hr]
            ring
    · push Not at hne
      have h0 : ∀ t, F (planeLift t p) = 0 := fun t => by
        simp only [hF, hf, Set.indicator_of_notMem (hne t), ENNReal.ofReal_zero]
      simp only [h0, lintegral_zero]
      exact zero_le
  have hbound : ∫⁻ y, F y ≤ ENNReal.ofReal (4 * δ / (1 - |c|) * J) := by
    rw [hstep, ENNReal.ofReal_mul (by positivity), hJ,
      ofReal_integral_eq_lintegral_ofReal hJi
        (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (by positivity) _),
      ← lintegral_const_mul _ ((by fun_prop : Continuous fun p : Fin 2 → ℝ =>
        1 + ‖p‖).measurable.pow_const _).ennreal_ofReal]
    exact lintegral_mono hslice
  have hfint : Integrable f :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hf0)).2 (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  refine ⟨(integrable_indicator_iff hTm).1 hfint, ?_⟩
  rw [← integral_indicator hTm]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  calc (∫⁻ y, ENNReal.ofReal (f y)).toReal ≤ (ENNReal.ofReal (4 * δ / (1 - |c|) * J)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = 4 * J / (1 - |c|) * δ := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        ring


private theorem second_segment_of_third {u : Space → Space} {K : ℝ} {Rs cs : Finset ℝ}
    (hK : 0 ≤ K)
    (h3 : ∀ z : Space, z ≠ 0 → (∀ R ∈ Rs, ‖z‖ ≠ R) → (∀ c ∈ cs, z 2 ≠ c * ‖z‖) →
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) z ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z‖ ≤ K * ‖z‖⁻¹)
    (y h : Space) (hyh : 2 * ‖h‖ ≤ ‖y‖)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, (∀ R ∈ Rs, ‖y + s • h‖ ≠ R) ∧
        ∀ c ∈ cs, (y + s • h) 2 ≠ c * ‖y + s • h‖) :
    ‖fderiv ℝ (fderiv ℝ u) (y + h) - fderiv ℝ (fderiv ℝ u) y‖ ≤ ‖h‖ * (2 * K * ‖y‖⁻¹) := by
  by_cases hh0 : h = 0
  · subst hh0
    simp
  have hhpos : 0 < ‖h‖ := norm_pos_iff.2 hh0
  have hypos : 0 < ‖y‖ := by linarith
  have hmem : ∀ z ∈ segment ℝ y (y + h), ∃ θ ∈ Set.Icc (0 : ℝ) 1, z = y + θ • h := by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact ⟨θ, hθ, by rw [add_sub_cancel_left]⟩
  have hlow : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖y‖ / 2 ≤ ‖y + θ • h‖ := by
    intro θ hθ
    have h1 : ‖θ • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
    have h2 := norm_sub_norm_le y (-(θ • h))
    rw [sub_neg_eq_add, norm_neg] at h2
    linarith
  have hpt : ∀ z ∈ segment ℝ y (y + h), DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) z ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z‖ ≤ 2 * K * ‖y‖⁻¹ := by
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := hmem z hz
    have hl := hlow θ hθ
    have hz0 : y + θ • h ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hl
      linarith
    obtain ⟨hd, hb⟩ := h3 _ hz0 (hseg θ hθ).1 (hseg θ hθ).2
    refine ⟨hd, hb.trans ?_⟩
    have hinv : ‖y + θ • h‖⁻¹ ≤ (‖y‖ / 2)⁻¹ := inv_anti₀ (by positivity) hl
    rw [inv_div] at hinv
    calc K * ‖y + θ • h‖⁻¹ ≤ K * (2 / ‖y‖) := mul_le_mul_of_nonneg_left hinv hK
      _ = 2 * K * ‖y‖⁻¹ := by ring
  have hmv := (convex_segment y (y + h)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hpt z hz).1) (fun z hz => (hpt z hz).2)
    (left_mem_segment ℝ y (y + h)) (right_mem_segment ℝ y (y + h))
  rw [add_sub_cancel_left] at hmv
  linarith [hmv]

private theorem weight_nonneg' (y : Space) : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) :=
  Real.rpow_nonneg (by positivity) _

private theorem union_two {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hiA : IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) A)
    (hiB : IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) B) :
    IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) (A ∪ B) ∧
      (∫ y in A ∪ B, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤
        (∫ y in A, (1 + ‖y‖) ^ (-(3 : ℝ))) + ∫ y in B, (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  refine ⟨hiA.union hiB, ?_⟩
  have hdisj : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  rw [← Set.union_sdiff_self, setIntegral_union hdisj hBA hiA (hiB.mono_set Set.sdiff_subset)]
  have hmono := setIntegral_mono_set hiB (Filter.Eventually.of_forall fun y => weight_nonneg' y)
    (Set.sdiff_subset : B \ A ⊆ B).eventuallyLE
  linarith

private theorem union_finset {ι : Type*} (s : Finset ι) (t : ι → Set Space)
    (hm : ∀ i ∈ s, MeasurableSet (t i))
    (hi : ∀ i ∈ s, IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) (t i)) :
    MeasurableSet (⋃ i ∈ s, t i) ∧
    IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) (⋃ i ∈ s, t i) ∧
      (∫ y in ⋃ i ∈ s, t i, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤
        ∑ i ∈ s, ∫ y in t i, (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨hm', hi', hle⟩ := ih (fun i hi2 => hm i (Finset.mem_insert_of_mem hi2))
      (fun i hi2 => hi i (Finset.mem_insert_of_mem hi2))
    have hma := hm a (Finset.mem_insert_self a s)
    have hia := hi a (Finset.mem_insert_self a s)
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    obtain ⟨h1, h2⟩ := union_two hma hm' hia hi'
    exact ⟨hma.union hm', h1, h2.trans (by linarith)⟩

theorem fieldOf_second_jump_cover {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∃ (B : Set Space) (g : Space → ℝ),
      MeasurableSet B ∧ IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) B ∧
      (∫ y in B, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ C * ‖h‖ ∧
      (∀ y, 0 ≤ g y) ∧ Integrable (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ)) * g y) ∧
      (∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * g y) ≤ C ∧
      ∀ y ∉ B, ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) (y + h) -
        fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ ‖h‖ * g y := by
  obtain ⟨K0, Rs, cs, hK0, hcs, h3⟩ := ProfilePowerJumpsPieces.fieldOf_third_bound hP hD β
  obtain ⟨K, hseg⟩ : ∃ K : ℝ, ∀ y h : Space, 2 * ‖h‖ ≤ ‖y‖ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, (∀ R ∈ Rs, ‖y + s • h‖ ≠ R) ∧
        ∀ c ∈ cs, (y + s • h) 2 ≠ c * ‖y + s • h‖) →
      ‖fderiv ℝ (fderiv ℝ (fieldOf P D β)) (y + h) -
        fderiv ℝ (fderiv ℝ (fieldOf P D β)) y‖ ≤ ‖h‖ * (K * ‖y‖⁻¹) :=
    ⟨2 * K0, fun y h hyh hs => second_segment_of_third hK0 h3 y h hyh hs⟩
  obtain ⟨C1, hC1⟩ := weight_shell
  choose Cb hCb using weight_band
  have hG := weight_inv_norm_integrable
  set G : ℝ := |K| * ∫ y : Space, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖⁻¹ with hGdef
  set CB : ℝ := 2 * C1 + ∑ R ∈ Rs, 2 * C1 + ∑ c ∈ cs, 2 * Cb c with hCBdef
  refine ⟨max CB G, fun h hh => ?_⟩
  set δ : ℝ := ‖h‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg h
  set A1 : Set Space := {y : Space | 0 ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * δ} with hA1
  set tube : ℝ → Set Space := fun R => {y : Space | |‖y‖ - R| ≤ δ} with htube
  set band : ℝ → Set Space := fun c => {y : Space | |y 2 - c * ‖y‖| ≤ 2 * δ} with hband
  have hcont2 : Continuous (fun y : Space => y 2) := by fun_prop
  have hmA1 : MeasurableSet A1 :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet
  have hmtube : ∀ R, MeasurableSet (tube R) := fun R =>
    (isClosed_le ((continuous_norm.sub continuous_const).abs) continuous_const).measurableSet
  have hmband : ∀ c, MeasurableSet (band c) := fun c =>
    (isClosed_le ((hcont2.sub (continuous_const.mul continuous_norm)).abs)
      continuous_const).measurableSet
  obtain ⟨hiA1, hA1le⟩ := hC1 0 (2 * δ) le_rfl (by positivity)
  have htubeb : ∀ R, IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) (tube R) ∧
      (∫ y in tube R, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ 2 * C1 * δ := by
    intro R
    set a : ℝ := max (R - δ) 0
    set b : ℝ := max (R + δ) a
    have ha0 : 0 ≤ a := le_max_right _ _
    have hab : a ≤ b := le_max_right _ _
    have hba : b - a ≤ 2 * δ := by
      rcases le_total (R + δ) a with h1 | h1
      · rw [show b = a from max_eq_right h1]; linarith
      · rw [show b = R + δ from max_eq_left h1]
        have : R - δ ≤ a := le_max_left _ _
        linarith
    have hsub : tube R ⊆ {y : Space | a ≤ ‖y‖ ∧ ‖y‖ ≤ b} := by
      intro y hy
      simp only [htube, Set.mem_ofPred_eq, abs_le] at hy
      refine ⟨max_le (by linarith) (norm_nonneg y), le_max_of_le_left (by linarith)⟩
    obtain ⟨hi, hle⟩ := hC1 a b ha0 hab
    have hC1nn : 0 ≤ C1 := by
      by_contra hneg
      have h0 := (hC1 0 1 le_rfl zero_le_one).2
      simp only [sub_zero, mul_one] at h0
      have hpos : 0 ≤ ∫ y in {y : Space | 0 ≤ ‖y‖ ∧ ‖y‖ ≤ 1}, (1 + ‖y‖) ^ (-(3 : ℝ)) :=
        setIntegral_nonneg ((isClosed_le continuous_const continuous_norm).measurableSet.inter
          (isClosed_le continuous_norm continuous_const).measurableSet) (fun y _ => weight_nonneg' y)
      linarith
    refine ⟨hi.mono_set hsub, ?_⟩
    calc (∫ y in tube R, (1 + ‖y‖) ^ (-(3 : ℝ)))
        ≤ ∫ y in {y : Space | a ≤ ‖y‖ ∧ ‖y‖ ≤ b}, (1 + ‖y‖) ^ (-(3 : ℝ)) :=
          setIntegral_mono_set hi (Filter.Eventually.of_forall fun y => weight_nonneg' y)
            (Filter.Eventually.of_forall hsub)
      _ ≤ C1 * (b - a) := hle
      _ ≤ C1 * (2 * δ) := mul_le_mul_of_nonneg_left hba hC1nn
      _ = 2 * C1 * δ := by ring
  have hbandb : ∀ c ∈ cs, IntegrableOn (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) (band c) ∧
      (∫ y in band c, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ 2 * Cb c * δ := by
    intro c hc
    obtain ⟨hi, hle⟩ := hCb c (hcs c hc) (2 * δ) (by positivity)
    exact ⟨hi, hle.trans_eq (by ring)⟩
  obtain ⟨hmT, hiT, hleT⟩ := union_finset Rs tube (fun R _ => hmtube R) (fun R _ => (htubeb R).1)
  obtain ⟨hmC, hiC, hleC⟩ := union_finset cs band (fun c _ => hmband c) (fun c hc => (hbandb c hc).1)
  obtain ⟨hi12, hle12⟩ := union_two hmA1 hmT hiA1 hiT
  obtain ⟨hi123, hle123⟩ := union_two (hmA1.union hmT) hmC hi12 hiC
  refine ⟨A1 ∪ (⋃ R ∈ Rs, tube R) ∪ ⋃ c ∈ cs, band c, fun y : Space => |K| * ‖y‖⁻¹,
    (hmA1.union hmT).union hmC, hi123, ?_, fun y : Space => by positivity, ?_, ?_, ?_⟩
  · have hsT : (∑ R ∈ Rs, ∫ y in tube R, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ ∑ R ∈ Rs, 2 * C1 * δ :=
      Finset.sum_le_sum fun R _ => (htubeb R).2
    have hsC : (∑ c ∈ cs, ∫ y in band c, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ ∑ c ∈ cs, 2 * Cb c * δ :=
      Finset.sum_le_sum fun c hc => (hbandb c hc).2
    have heq : 2 * C1 * δ + ∑ R ∈ Rs, 2 * C1 * δ + ∑ c ∈ cs, 2 * Cb c * δ = CB * δ := by
      rw [hCBdef, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    have hA1le' : (∫ y in A1, (1 + ‖y‖) ^ (-(3 : ℝ))) ≤ 2 * C1 * δ := hA1le.trans_eq (by ring)
    calc (∫ y in A1 ∪ (⋃ R ∈ Rs, tube R) ∪ ⋃ c ∈ cs, band c, (1 + ‖y‖) ^ (-(3 : ℝ)))
        ≤ CB * δ := by linarith
      _ ≤ max CB G * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  · have := hG.const_mul |K|
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  · have heq : (∫ y : Space, (1 + ‖y‖) ^ (-(3 : ℝ)) * (|K| * ‖y‖⁻¹)) = G := by
      rw [hGdef, ← integral_const_mul]
      congr 1
      ext y
      ring
    rw [heq]
    exact le_max_right _ _
  · intro y hy
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hy
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
    have hy1' : 2 * δ < ‖y‖ := by
      by_contra hc
      exact hy1 ⟨norm_nonneg y, not_lt.1 hc⟩
    have hsegc : ∀ s ∈ Set.Icc (0 : ℝ) 1, (∀ R ∈ Rs, ‖y + s • h‖ ≠ R) ∧
        ∀ c ∈ cs, (y + s • h) 2 ≠ c * ‖y + s • h‖ := by
      intro s hs
      have hsh : ‖s • h‖ ≤ δ := by
        rw [norm_smul, Real.norm_of_nonneg hs.1]
        exact mul_le_of_le_one_left hδ0 hs.2
      have hnorm : |‖y + s • h‖ - ‖y‖| ≤ δ := by
        have := abs_norm_sub_norm_le (y + s • h) y
        rw [add_sub_cancel_left] at this
        exact this.trans hsh
      refine ⟨fun R hR hEq => hy2 R hR ?_, fun c hc hEq => hy3 c hc ?_⟩
      · show |‖y‖ - R| ≤ δ
        rw [← hEq, abs_sub_comm]
        exact hnorm
      · show |y 2 - c * ‖y‖| ≤ 2 * δ
        have hcomp : (y + s • h) 2 = y 2 + s * h 2 := by simp
        have hh2 : |s * h 2| ≤ δ := by
          have h2le : |h 2| ≤ ‖h‖ := by
            have := PiLp.norm_apply_le h 2
            rwa [Real.norm_eq_abs] at this
          rw [abs_mul, abs_of_nonneg hs.1]
          exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans h2le
        have hc1 : |c| ≤ 1 := (hcs c hc).le
        have hcn : |c * (‖y + s • h‖ - ‖y‖)| ≤ δ := by
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans hnorm
        have hrw : y 2 - c * ‖y‖ = c * (‖y + s • h‖ - ‖y‖) - s * h 2 := by
          rw [hcomp] at hEq
          linarith
        rw [hrw]
        calc |c * (‖y + s • h‖ - ‖y‖) - s * h 2| ≤ |c * (‖y + s • h‖ - ‖y‖)| + |s * h 2| :=
              abs_sub _ _
          _ ≤ 2 * δ := by linarith
    have hb := hseg y h (by linarith) hsegc
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self K) (inv_nonneg.2 (norm_nonneg y))) hδ0

end ProfilePowerJumpsCover

end FracInternal

end Breakdown

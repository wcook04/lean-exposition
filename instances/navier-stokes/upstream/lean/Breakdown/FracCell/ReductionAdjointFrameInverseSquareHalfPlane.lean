import Breakdown.FracCell.ReductionAdjointFrameInverseSquareParts

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FrameInverseSquareHalfPlane

open SteadyCert CellCert.Reduction

private def ringLin (θ : ℝ) : ℝ × ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      ((EuclideanSpace.single 0 (Real.cos θ) + EuclideanSpace.single 1 (Real.sin θ) : Space)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single 2 1 : Space)

private theorem ringLin_apply (θ : ℝ) (p : ℝ × ℝ) : ringLin θ p = ringPoint p.1 θ p.2 := by
  ext i
  fin_cases i <;> simp [ringLin, ringPoint]

private theorem ringLin_cont : Continuous ringLin := by
  refine continuous_clm_apply.2 fun p => ?_
  simp_rw [ringLin_apply]
  have hs : ∀ i : Fin 3, Continuous fun t : ℝ => (EuclideanSpace.single i t : Space) := by
    intro i
    have h : (fun t : ℝ => (EuclideanSpace.single i t : Space)) = fun t => t • (EuclideanSpace.single i 1 : Space) := by
      funext t
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [h]
    exact continuous_id.smul continuous_const
  unfold ringPoint
  exact (((hs 0).comp (by fun_prop)).add ((hs 1).comp (by fun_prop))).add continuous_const

private theorem ringRadius_pt (ρ θ z : ℝ) (hρ : 0 ≤ ρ) : ringRadius (ringPoint ρ θ z) = ρ := by
  have e0 : ringPoint ρ θ z 0 = ρ * Real.cos θ := by simp [ringPoint]
  have e1 : ringPoint ρ θ z 1 = ρ * Real.sin θ := by simp [ringPoint]
  rw [ringRadius, e0, e1, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hρ]

private theorem norm_pt_sq (ρ θ z : ℝ) : ‖ringPoint ρ θ z‖ ^ 2 = ρ ^ 2 + z ^ 2 := by
  have e0 : ringPoint ρ θ z 0 = ρ * Real.cos θ := by simp [ringPoint]
  have e1 : ringPoint ρ θ z 1 = ρ * Real.sin θ := by simp [ringPoint]
  have e2 : ringPoint ρ θ z 2 = z := by simp [ringPoint]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three, e0, e1, e2]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem frame0_pt (ρ θ z : ℝ) (hρ : 0 < ρ) : ringLin θ (1, 0) = ringFrame 0 (ringPoint ρ θ z) := by
  rw [ringLin_apply]
  have hr := ringRadius_pt ρ θ z hρ.le
  simp only [ringFrame, hr]
  ext i
  fin_cases i <;> simp [ringPoint] <;> field_simp

private theorem frame1_pt (ρ θ z : ℝ) (hρ : 0 < ρ) : ringFrame 1 (ringPoint ρ θ z) =
    (EuclideanSpace.single 0 (-Real.sin θ) + EuclideanSpace.single 1 (Real.cos θ) : Space) := by
  have hr := ringRadius_pt ρ θ z hρ.le
  simp only [ringFrame, hr]
  ext i
  fin_cases i <;> simp [ringPoint] <;> field_simp

private theorem frame2_pt (ρ θ z : ℝ) : ringLin θ (0, 1) = ringFrame 2 (ringPoint ρ θ z) := by
  rw [ringLin_apply]
  ext i
  fin_cases i <;> simp [ringFrame, ringPoint]

private theorem pt_hasDeriv (ρ θ z : ℝ) (hρ : 0 < ρ) :
    HasDerivAt (fun t => ringPoint ρ t z) (ρ • ringFrame 1 (ringPoint ρ θ z)) θ := by
  have hform : (fun t => ringPoint ρ t z) = fun t =>
      (ρ * Real.cos t) • (EuclideanSpace.single 0 1 : Space) + (ρ * Real.sin t) • (EuclideanSpace.single 1 1 : Space) +
        (EuclideanSpace.single 2 z : Space) := by
    funext t
    ext i
    fin_cases i <;> simp [ringPoint]
  rw [hform]
  have h := ((((Real.hasDerivAt_cos θ).const_mul ρ).smul_const (EuclideanSpace.single 0 1 : Space)).add
    (((Real.hasDerivAt_sin θ).const_mul ρ).smul_const (EuclideanSpace.single 1 1 : Space))).add_const
    (EuclideanSpace.single 2 z : Space)
  have e : ρ • ringFrame 1 (ringPoint ρ θ z) =
      (ρ * -Real.sin θ) • (EuclideanSpace.single 0 1 : Space) + (ρ * Real.cos θ) • (EuclideanSpace.single 1 1 : Space) := by
    rw [frame1_pt ρ θ z hρ]
    ext i
    fin_cases i <;> simp
  rw [e]
  exact h

private theorem exp_pi_eq (k : ℤ) :
    Complex.exp (-((k : ℂ) * ((Real.pi : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-((k : ℂ) * ((-Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

private theorem modeData (w : Space → ℂ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (k : ℤ) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => angularMode w k p.1 p.2) ∧
      HasCompactSupport (fun p : ℝ × ℝ => angularMode w k p.1 p.2) ∧
      ∀ ρ z : ℝ, 0 < ρ →
        fderiv ℝ (fun p : ℝ × ℝ => angularMode w k p.1 p.2) (ρ, z) (1, 0) =
            angularMode (fun y => fderiv ℝ w y (ringFrame 0 y)) k ρ z ∧
          fderiv ℝ (fun p : ℝ × ℝ => angularMode w k p.1 p.2) (ρ, z) (0, 1) =
            angularMode (fun y => fderiv ℝ w y (ringFrame 2 y)) k ρ z ∧
          angularMode (fun y => fderiv ℝ w y (ringFrame 1 y)) k ρ z =
            ((k : ℂ) * Complex.I / (ρ : ℂ)) * angularMode w k ρ z := by
  set E : ℝ → ℂ := fun θ => Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) with hE
  have hEc : Continuous E := by
    simp only [hE]
    fun_prop
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hwc : Continuous w := hw.continuous
  have hDc : Continuous (fun y => fderiv ℝ w y) := hw.continuous_fderiv one_ne_zero
  set c : ℂ := (1 / (2 * Real.pi) : ℂ) with hc
  set g : ℝ × ℝ → ℝ → ℂ := fun p θ => E θ * w (ringLin θ p) with hg
  set F' : ℝ × ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℂ) := fun p θ => E θ • ((fderiv ℝ w (ringLin θ p)).comp (ringLin θ)) with hF'
  have hA : (fun p : ℝ × ℝ => angularMode w k p.1 p.2) = fun p => c * ∫ θ in (-Real.pi)..Real.pi, g p θ := by
    funext p
    simp only [angularMode, hc, hg, hE, ringLin_apply]
  have hgc : Continuous (Function.uncurry g) := by
    simp only [hg, Function.uncurry]
    exact (hEc.comp continuous_snd).mul (hwc.comp ((ringLin_cont.comp continuous_snd).clm_apply continuous_fst))
  have hF'c : Continuous (Function.uncurry F') := by
    simp only [hF', Function.uncurry]
    exact (hEc.comp continuous_snd).smul ((hDc.comp ((ringLin_cont.comp continuous_snd).clm_apply continuous_fst)).clm_comp
      (ringLin_cont.comp continuous_snd))
  have hder : ∀ p θ, HasFDerivAt (fun x => g x θ) (F' p θ) p := by
    intro p θ
    have h1 : HasFDerivAt (fun x => w (ringLin θ x)) ((fderiv ℝ w (ringLin θ p)).comp (ringLin θ)) p :=
      (hwd _).hasFDerivAt.comp p (ringLin θ).hasFDerivAt
    exact h1.const_mul (E θ)
  have hint : ∀ p, HasFDerivAt (fun x => ∫ θ in (-Real.pi)..Real.pi, g x θ) (∫ θ in (-Real.pi)..Real.pi, F' p θ) p := by
    intro p
    have hK : IsCompact (Metric.closedBall p 1 ×ˢ Set.Icc (-Real.pi) Real.pi) :=
      (isCompact_closedBall p 1).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'c.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (Metric.ball_mem_nhds p one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x => (hgc.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    · exact (hgc.comp (Continuous.prodMk_right p)).intervalIntegrable _ _
    · exact (hF'c.comp (Continuous.prodMk_right p)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx => ?_
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at ht
      exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, ht.1.le, ht.2⟩
    · exact Eventually.of_forall fun t _ x _ => hder x t
  set Df : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ) := fun p => c • ∫ θ in (-Real.pi)..Real.pi, F' p θ with hDf
  have hAd : ∀ p, HasFDerivAt (fun p : ℝ × ℝ => angularMode w k p.1 p.2) (Df p) p := by
    intro p
    rw [hA]
    exact (hint p).const_mul c
  have hDfc : Continuous Df :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF'c _ _).const_smul c
  refine ⟨contDiff_one_iff_hasFDerivAt.2 ⟨Df, hDfc, hAd⟩, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).1 hs.isCompact.isBounded
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) R) fun p hp => ?_
    have hpR : R < ‖p‖ := by simpa using hp
    have hvan : ∀ θ : ℝ, w (ringPoint p.1 θ p.2) = 0 := by
      intro θ
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have hle : ‖ringPoint p.1 θ p.2‖ ≤ R := by simpa using hR hmem
      have hR0 : 0 ≤ R := (norm_nonneg _).trans hle
      have h1 : R ^ 2 < ‖p‖ ^ 2 := pow_lt_pow_left₀ hpR hR0 two_ne_zero
      have h2 : ‖p‖ ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 := by
        rw [Prod.norm_def]
        rcases max_cases ‖p.1‖ ‖p.2‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          simp only [Real.norm_eq_abs, sq_abs] <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      have h3 : ‖ringPoint p.1 θ p.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      rw [norm_pt_sq] at h3
      linarith
    simp [angularMode, hvan]
  · intro ρ z hρ
    have hfd : fderiv ℝ (fun p : ℝ × ℝ => angularMode w k p.1 p.2) (ρ, z) = Df (ρ, z) := (hAd _).fderiv
    have hIi : IntervalIntegrable (fun θ => F' (ρ, z) θ) volume (-Real.pi) Real.pi :=
      (hF'c.comp (Continuous.prodMk_right (ρ, z))).intervalIntegrable _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hfd]
      simp only [hDf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply hIi]
      simp only [angularMode, hc, hF', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [frame0_pt ρ θ z hρ, ringLin_apply]
    · rw [hfd]
      simp only [hDf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply hIi]
      simp only [angularMode, hc, hF', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [frame2_pt ρ θ z, ringLin_apply]
    · set f : ℝ → ℂ := fun θ => w (ringPoint ρ θ z) with hf
      set f' : ℝ → ℂ := fun θ => (ρ : ℂ) * fderiv ℝ w (ringPoint ρ θ z) (ringFrame 1 (ringPoint ρ θ z)) with hf'
      have hfd' : ∀ θ, HasDerivAt f (f' θ) θ := by
        intro θ
        have h := (hwd (ringPoint ρ θ z)).hasFDerivAt.comp_hasDerivAt θ (pt_hasDeriv ρ θ z hρ)
        have e : fderiv ℝ w (ringPoint ρ θ z) (ρ • ringFrame 1 (ringPoint ρ θ z)) = f' θ := by
          rw [map_smul, Complex.real_smul]
        exact h.congr_deriv e
      have hEd : ∀ θ, HasDerivAt E (-((k : ℂ) * Complex.I) * E θ) θ := by
        intro θ
        have h := (((hasDerivAt_id θ).ofReal_comp.const_mul (k : ℂ)).mul_const Complex.I).neg.cexp
        convert h using 1
        · funext x
          simp only [hE, id, Pi.neg_apply]
        · simp only [hE, id, Complex.ofReal_one, Pi.neg_apply]
          ring
      have hf'c : Continuous f' := by
        simp only [hf']
        refine continuous_const.mul ?_
        have hp : Continuous fun θ => ringPoint ρ θ z := by
          have := ringLin_cont.clm_apply (continuous_const (y := ((ρ, z) : ℝ × ℝ)))
          simpa [ringLin_apply] using this
        have hfr : Continuous fun θ => ringFrame 1 (ringPoint ρ θ z) := by
          have e : (fun θ => ringFrame 1 (ringPoint ρ θ z)) = fun θ =>
              (EuclideanSpace.single 0 (-Real.sin θ) + EuclideanSpace.single 1 (Real.cos θ) : Space) := by
            funext θ
            exact frame1_pt ρ θ z hρ
          have e2 : (fun θ : ℝ => (EuclideanSpace.single 0 (-Real.sin θ) + EuclideanSpace.single 1 (Real.cos θ) : Space)) =
              fun θ => ringLin (θ + Real.pi / 2) (1, 0) := by
            funext θ
            rw [ringLin_apply]
            ext i
            fin_cases i <;> simp [ringPoint, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
          rw [e, e2]
          exact (ringLin_cont.comp (continuous_add_const _)).clm_apply continuous_const
        exact (hDc.comp hp).clm_apply hfr
      have hEd'c : Continuous fun θ => -((k : ℂ) * Complex.I) * E θ := continuous_const.mul hEc
      have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -Real.pi) (b := Real.pi)
        (fun θ _ => hEd θ) (fun θ _ => hfd' θ) (hEd'c.intervalIntegrable _ _) (hf'c.intervalIntegrable _ _)
      have hper : E Real.pi * f Real.pi = E (-Real.pi) * f (-Real.pi) := by
        have e1 : E Real.pi = E (-Real.pi) := exp_pi_eq k
        have e2 : ringPoint ρ Real.pi z = ringPoint ρ (-Real.pi) z := by
          simp [ringPoint, Real.cos_neg, Real.sin_neg]
        simp only [hf, e1, e2]
      have hR : ∫ θ in (-Real.pi)..Real.pi, -((k : ℂ) * Complex.I) * E θ * f θ =
          -((k : ℂ) * Complex.I) * ∫ θ in (-Real.pi)..Real.pi, E θ * w (ringPoint ρ θ z) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [hf]
        ring
      rw [hper, sub_self, zero_sub, hR] at hparts
      have hL : ∫ θ in (-Real.pi)..Real.pi, E θ * f' θ =
          (ρ : ℂ) * ∫ θ in (-Real.pi)..Real.pi, E θ * fderiv ℝ w (ringPoint ρ θ z) (ringFrame 1 (ringPoint ρ θ z)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [hf']
        ring
      rw [hL, neg_mul, neg_neg] at hparts
      have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
      simp only [hE] at hparts
      have hI1 : ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) *
            fderiv ℝ w (ringPoint ρ θ z) (ringFrame 1 (ringPoint ρ θ z)) =
          ((k : ℂ) * Complex.I / (ρ : ℂ)) *
            ∫ θ in (-Real.pi)..Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * w (ringPoint ρ θ z) := by
        rw [div_mul_eq_mul_div, eq_div_iff hρc]
        linear_combination hparts
      simp only [angularMode]
      rw [hI1]
      ring

private def coord (i : Fin 3) : Space →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w i
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }

private theorem coord_apply (i : Fin 3) (w : Space) : coord i w = w i := rfl

private theorem hpart_fderiv (u : Space → Space) (hu : Differentiable ℝ u) (y v : Space) :
    fderiv ℝ (horizontalPart u) y v = ((fderiv ℝ u y v 0 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ u y v 1 : ℝ) : ℂ) := by
  have h0 : HasFDerivAt (fun x => ((u x 0 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((coord 0).comp (fderiv ℝ u y))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y ((coord 0).hasFDerivAt.comp y (hu y).hasFDerivAt)
  have h1 : HasFDerivAt (fun x => ((u x 1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((coord 1).comp (fderiv ℝ u y))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y ((coord 1).hasFDerivAt.comp y (hu y).hasFDerivAt)
  have h := h0.add (h1.const_mul Complex.I)
  rw [HasFDerivAt.fderiv (f := horizontalPart u) h]
  simp [coord_apply]

private theorem vpart_fderiv (u : Space → Space) (hu : Differentiable ℝ u) (y v : Space) :
    fderiv ℝ (verticalPart u) y v = ((fderiv ℝ u y v 2 : ℝ) : ℂ) := by
  have h2 : HasFDerivAt (fun x => ((u x 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((coord 2).comp (fderiv ℝ u y))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y ((coord 2).hasFDerivAt.comp y (hu y).hasFDerivAt)
  rw [HasFDerivAt.fderiv (f := verticalPart u) h2]
  simp [coord_apply]

private theorem norm_mode_sq (k : ℤ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    ‖((k : ℂ) * Complex.I / (ρ : ℂ)) * x‖ ^ 2 = (k : ℝ) ^ 2 * ‖x‖ ^ 2 / ρ ^ 2 := by
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    Complex.norm_intCast, mul_pow, div_pow, sq_abs]
  ring

private theorem inv_lintegral_top (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∫⁻ x in Set.Ioo (0 : ℝ) δ, ENNReal.ofReal (C / x) = ⊤ := by
  by_contra hne
  have hint : IntegrableOn (fun x : ℝ => C / x) (Set.Ioo 0 δ) := by
    refine ⟨(measurable_const.div measurable_id).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact lt_top_iff_ne_top.2 hne
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (div_pos hC hx.1).le
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioo 0 δ) := by
    have h1 : IntegrableOn (fun x : ℝ => C⁻¹ * (C / x)) (Set.Ioo 0 δ) := hint.const_mul C⁻¹
    refine IntegrableOn.congr_fun h1 (fun x _ => ?_) measurableSet_Ioo
    field_simp
  have hII : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 δ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).2 hinv
  rcases intervalIntegrable_inv_iff.1 hII with h | h
  · exact hδ.ne h
  · exact h (Set.left_mem_uIcc)

private theorem axis_top (a : ℝ × ℝ → ℂ) (k : ℤ) (hac : Continuous a) (hk : k ≠ 0) (z0 : ℝ) (hz0 : a (0, z0) ≠ 0) :
    ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
        (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2)) = ⊤ := by
  set c : ℝ := ‖a (0, z0)‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 hz0
  have hev : ∀ᶠ q in 𝓝 ((0 : ℝ), z0), c / 2 < ‖a q‖ :=
    (hac.norm.continuousAt).eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set S : Set (ℝ × ℝ) := Set.Ioo 0 δ ×ˢ Set.Ioo (z0 - δ) (z0 + δ) with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hSsub : S ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := fun q hq => ⟨hq.1.1, Set.mem_univ _⟩
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    positivity
  set C : ℝ := 2 * Real.pi * (k : ℝ) ^ 2 * (c / 2) ^ 2 with hCdef
  have hC : 0 < C := by positivity
  have hlow : ∫⁻ q in S, ENNReal.ofReal (C / q.1) ≤
      ∫⁻ q in S, ENNReal.ofReal (2 * Real.pi * q.1 *
        (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2)) := by
    refine setLIntegral_mono' hSm fun q hq => ENNReal.ofReal_le_ofReal ?_
    have hq1 : 0 < q.1 := hq.1.1
    have hd : dist q (0, z0) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      constructor
      · rw [sub_zero, abs_of_pos hq1]
        exact hq.1.2
      · rw [abs_lt]
        constructor <;> linarith [hq.2.1, hq.2.2]
    have ha := hball hd
    have hsq : (c / 2) ^ 2 ≤ ‖a q‖ ^ 2 := pow_le_pow_left₀ (by positivity) ha.le 2
    have e : 2 * Real.pi * q.1 * ((k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2) = 2 * Real.pi * (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 := by
      field_simp
    have h1 : C / q.1 ≤ 2 * Real.pi * (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 := by
      rw [hCdef]
      gcongr
    have h2 : 0 ≤ 2 * Real.pi * q.1 * (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2) := by positivity
    calc C / q.1 ≤ 2 * Real.pi * q.1 * ((k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2) := by rw [e]; exact h1
      _ ≤ _ := by nlinarith [h2]
  have htop : ∫⁻ q in S, ENNReal.ofReal (C / q.1) = ⊤ := by
    rw [hS, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have hprod := lintegral_prod_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) δ))
      (ν := volume.restrict (Set.Ioo (z0 - δ) (z0 + δ))) (f := fun x : ℝ => ENNReal.ofReal (C / x))
      (g := fun _ : ℝ => (1 : ENNReal)) ((measurable_const.div measurable_id).ennreal_ofReal.aemeasurable)
      aemeasurable_const
    rw [inv_lintegral_top C δ hC hδ] at hprod
    simp only [mul_one] at hprod
    rw [hprod]
    simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo]
    refine ENNReal.top_mul ?_
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  refine top_le_iff.1 ?_
  rw [← htop]
  exact hlow.trans (lintegral_mono_set hSsub)

def AxisHalfPlaneBoundStatement : Prop :=
  ∀ (a : ℝ × ℝ → ℂ) (k : ℤ) (s : ℝ), ContDiff ℝ 1 a → HasCompactSupport a → (k ≠ 0 → ∀ z : ℝ, a (0, z) = 0) →
    (s = ((|k| : ℤ) : ℝ) + 1 / 2 ∨ (s = ((|k| : ℤ) : ℝ) + 3 / 2 ∧ ∀ p : ℝ × ℝ, a (p.1, -p.2) = -a p)) →
    ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 * (s ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) ≤
      ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
        (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2))

theorem halfPlaneBound_of_axis (h : AxisHalfPlaneBoundStatement) : FrameInverseSquareParts.HalfPlaneBoundStatement := by
  intro a k s hac has hs
  by_cases hax : k ≠ 0 → ∀ z : ℝ, a (0, z) = 0
  · exact h a k s hac has hax hs
  · push Not at hax
    obtain ⟨hk, z0, hz0⟩ := hax
    rw [axis_top a k hac.continuous hk z0 hz0]
    exact le_top

def RadialInverseSquareStatement : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f r‖ ^ 2) ≤
      4 * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2)


private theorem ray_support (a : ℝ × ℝ → ℂ) (has : HasCompactSupport a) (θ : ℝ) :
    HasCompactSupport (fun r : ℝ => a (r * Real.cos θ, r * Real.sin θ)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 has.isCompact.isBounded
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * |R|)) fun r hr => ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have hle : ‖((r * Real.cos θ, r * Real.sin θ) : ℝ × ℝ)‖ ≤ R := by simpa using hR hmem
  have hr' : 2 * |R| < |r| := by simpa using hr
  rw [Prod.norm_def] at hle
  have h1 : |r * Real.cos θ| ≤ R := (le_max_left _ _).trans hle
  have h2 : |r * Real.sin θ| ≤ R := (le_max_right _ _).trans hle
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h1
  have e1 : (r * Real.cos θ) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : (r * Real.sin θ) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e3 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have e4 : (2 * |R|) ^ 2 < |r| ^ 2 := pow_lt_pow_left₀ hr' (by positivity) two_ne_zero
  rw [sq_abs, mul_pow, sq_abs] at e4
  nlinarith

def AngularCosBoundStatement : Prop :=
  ∀ (g : ℝ → ℂ) (m : ℕ) (t : ℝ), ContDiff ℝ 1 g → (0 < m → g (-(Real.pi / 2)) = 0 ∧ g (Real.pi / 2) = 0) →
    (t = (m : ℝ) * ((m : ℝ) + 1) ∨ (t = ((m : ℝ) + 1) * ((m : ℝ) + 2) ∧ g 0 = 0)) →
    ENNReal.ofReal t * ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2) ≤
      ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
        (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2))

private theorem rot_norm (A B : ℂ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ‖(c : ℂ) * A + (s : ℂ) * B‖ ^ 2 + ‖(-(s : ℂ)) * A + (c : ℂ) * B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  have e : ∀ x : ℝ, x = x * (c ^ 2 + s ^ 2) := fun x => by rw [h, mul_one]
  rw [e (A.re * A.re + A.im * A.im + (B.re * B.re + B.im * B.im))]
  ring

private theorem clm_pair (L : ℝ × ℝ →L[ℝ] ℂ) (x y : ℝ) : L (x, y) = (x : ℂ) * L (1, 0) + (y : ℂ) * L (0, 1) := by
  have e : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

private theorem cos_pos_iff_mem (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos θ ↔ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    by_contra hn
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hn
    rcases hn with h | h
    · have : Real.cos θ ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hθ.1])
      linarith
    · have : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [hθ.2])
      linarith
  · exact fun h => Real.cos_pos_of_mem_Ioo h

theorem axisHalfPlaneBound_of (hR : RadialInverseSquareStatement) (hA : AngularCosBoundStatement) :
    AxisHalfPlaneBoundStatement := by
  intro a k s hac has hax hs
  set m : ℕ := k.natAbs with hm
  have hkm : (((|k| : ℤ) : ℝ)) = (m : ℝ) := by simp [hm, Int.cast_abs]
  have hk2 : (k : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
    rw [← hkm, Int.cast_abs, sq_abs]
  set t : ℝ := s ^ 2 - 1 / 4 with ht
  have hda : Differentiable ℝ a := hac.differentiable one_ne_zero
  have hDc : Continuous (fun q => fderiv ℝ a q) := hac.continuous_fderiv one_ne_zero
  set P : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 * Real.cos p.2, p.1 * Real.sin p.2) with hP
  have hPc : Continuous P := by simp only [hP]; fun_prop
  set b : ℝ × ℝ → ℂ := fun p => a (P p) with hb
  set br : ℝ × ℝ → ℂ := fun p => fderiv ℝ a (P p) (Real.cos p.2, Real.sin p.2) with hbr
  set bt : ℝ × ℝ → ℂ := fun p => fderiv ℝ a (P p) (-(p.1 * Real.sin p.2), p.1 * Real.cos p.2) with hbt
  have hbc : Continuous b := hac.continuous.comp hPc
  have hbrc : Continuous br := (hDc.comp hPc).clm_apply (by fun_prop)
  have hbtc : Continuous bt := (hDc.comp hPc).clm_apply (by fun_prop)
  set T : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) with hT
  have hTm : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hTsub : T ⊆ polarCoord.target := by
    intro p hp
    refine ⟨hp.1, ?_, ?_⟩ <;> linarith [hp.2.1, hp.2.2, Real.pi_pos]
  set H : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) with hH
  have hHm : MeasurableSet H := measurableSet_Ioi.prod MeasurableSet.univ
  have hpolar : ∀ F : ℝ × ℝ → ENNReal,
      ∫⁻ q in H, F q = ∫⁻ p in T, ENNReal.ofReal p.1 * F (P p) := by
    intro F
    rw [← lintegral_indicator hHm, ← lintegral_comp_polarCoord_symm]
    have htm : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
    have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • H.indicator F (polarCoord.symm p) =
        T.indicator (fun p => ENNReal.ofReal p.1 * F (P p)) p := by
      intro p hp
      have hp1 : 0 < p.1 := hp.1
      have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      by_cases hpT : p ∈ T
      · have hc : 0 < Real.cos p.2 := (cos_pos_iff_mem p.2 hp2).2 hpT.2
        have hmem : polarCoord.symm p ∈ H := by
          simp only [hH, polarCoord_symm_apply, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
          positivity
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpT, smul_eq_mul, polarCoord_symm_apply]
      · have hnc : ¬ 0 < Real.cos p.2 := fun hc => hpT ⟨hp1, (cos_pos_iff_mem p.2 hp2).1 hc⟩
        have hnmem : polarCoord.symm p ∉ H := by
          simp only [hH, polarCoord_symm_apply, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true, not_lt]
          exact mul_nonpos_of_nonneg_of_nonpos hp1.le (not_lt.1 hnc)
        rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hpT, smul_zero]
    rw [setLIntegral_congr_fun htm hcongr, lintegral_indicator hTm, Measure.restrict_restrict hTm,
      Set.inter_eq_left.2 hTsub]
  have hTprod : (volume : Measure (ℝ × ℝ)).restrict T =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
    rw [hT, Measure.volume_eq_prod, Measure.prod_restrict]
  have hdr : ∀ r θ : ℝ, HasDerivAt (fun r' => a (r' * Real.cos θ, r' * Real.sin θ)) (br (r, θ)) r := by
    intro r θ
    have hl : HasDerivAt (fun r' : ℝ => (r' * Real.cos θ, r' * Real.sin θ)) (Real.cos θ, Real.sin θ) r := by
      have := ((hasDerivAt_id r).mul_const (Real.cos θ)).prodMk ((hasDerivAt_id r).mul_const (Real.sin θ))
      simpa using this
    exact (hda _).hasFDerivAt.comp_hasDerivAt r hl
  have hdt : ∀ r θ : ℝ, HasDerivAt (fun θ' => a (r * Real.cos θ', r * Real.sin θ')) (bt (r, θ)) θ := by
    intro r θ
    have hl : HasDerivAt (fun θ' : ℝ => (r * Real.cos θ', r * Real.sin θ')) (-(r * Real.sin θ), r * Real.cos θ) θ := by
      have := ((Real.hasDerivAt_cos θ).const_mul r).prodMk ((Real.hasDerivAt_sin θ).const_mul r)
      simpa using this
    exact (hda _).hasFDerivAt.comp_hasDerivAt θ hl
  have htnn : 0 ≤ t := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases hs with h | ⟨h, _⟩ <;> rw [ht, h, hkm] <;> nlinarith
  set F_L : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (2 * Real.pi / 4 * (Real.cos p.2 * ‖b p‖ ^ 2)) with hFL
  set F_T : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (2 * Real.pi * t * (Real.cos p.2 * ‖b p‖ ^ 2)) with hFT
  set G_R : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (2 * Real.pi * (Real.cos p.2 * (p.1 ^ 2 * ‖br p‖ ^ 2))) with hGR
  set G_T : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (2 * Real.pi *
    (Real.cos p.2 * (‖bt p‖ ^ 2 + (m : ℝ) ^ 2 * ‖b p‖ ^ 2 / Real.cos p.2 ^ 2))) with hGT
  have mFL : Measurable F_L := by
    simp only [hFL]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => 2 * Real.pi / 4 * (Real.cos p.2 * ‖b p‖ ^ 2)).measurable.ennreal_ofReal
  have mFT : Measurable F_T := by
    simp only [hFT]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => 2 * Real.pi * t * (Real.cos p.2 * ‖b p‖ ^ 2)).measurable.ennreal_ofReal
  have mGR : Measurable G_R := by
    simp only [hGR]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => 2 * Real.pi * (Real.cos p.2 * (p.1 ^ 2 * ‖br p‖ ^ 2))).measurable.ennreal_ofReal
  have mGT : Measurable G_T := by
    simp only [hGT]
    refine Measurable.ennreal_ofReal ?_
    have h1 : Measurable fun p : ℝ × ℝ => ‖bt p‖ ^ 2 := (by fun_prop : Continuous fun p : ℝ × ℝ => ‖bt p‖ ^ 2).measurable
    have h2 : Measurable fun p : ℝ × ℝ => (m : ℝ) ^ 2 * ‖b p‖ ^ 2 :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => (m : ℝ) ^ 2 * ‖b p‖ ^ 2).measurable
    have h3 : Measurable fun p : ℝ × ℝ => Real.cos p.2 ^ 2 :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos p.2 ^ 2).measurable
    have h4 : Measurable fun p : ℝ × ℝ => Real.cos p.2 := (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos p.2).measurable
    exact measurable_const.mul (h4.mul (h1.add (h2.div h3)))
  have hLeq : ∫⁻ q in H, ENNReal.ofReal (2 * Real.pi * q.1 * (s ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) =
      ∫⁻ p in T, (F_L p + F_T p) := by
    rw [hpolar]
    refine setLIntegral_congr_fun hTm fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo hp.2
    simp only [hFL, hFT, hP, hb]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hp1.le]
    congr 1
    have e : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq p.2]
    rw [e, ht]
    field_simp
    ring
  have hReq : ∫⁻ q in H, ENNReal.ofReal (2 * Real.pi * q.1 *
        (‖fderiv ℝ a q (1, 0)‖ ^ 2 + ‖fderiv ℝ a q (0, 1)‖ ^ 2 + (k : ℝ) ^ 2 * ‖a q‖ ^ 2 / q.1 ^ 2)) =
      ∫⁻ p in T, (G_R p + G_T p) := by
    rw [hpolar]
    refine setLIntegral_congr_fun hTm fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo hp.2
    set A : ℂ := fderiv ℝ a (P p) (1, 0) with hA'
    set B : ℂ := fderiv ℝ a (P p) (0, 1) with hB'
    have hbr' : br p = (Real.cos p.2 : ℂ) * A + (Real.sin p.2 : ℂ) * B := by
      simp only [hbr]
      rw [clm_pair]
    have hbt' : ‖bt p‖ ^ 2 = p.1 ^ 2 * ‖(-(Real.sin p.2 : ℂ)) * A + (Real.cos p.2 : ℂ) * B‖ ^ 2 := by
      simp only [hbt]
      rw [clm_pair]
      have e : ((-(p.1 * Real.sin p.2) : ℝ) : ℂ) * A + ((p.1 * Real.cos p.2 : ℝ) : ℂ) * B =
          (p.1 : ℂ) * ((-(Real.sin p.2 : ℂ)) * A + (Real.cos p.2 : ℂ) * B) := by
        push_cast
        ring
      rw [← hA', ← hB', e, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hrot := rot_norm A B (Real.cos p.2) (Real.sin p.2) (Real.cos_sq_add_sin_sq p.2)
    simp only [hGR, hGT, hb]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hp1.le]
    congr 1
    rw [hbt', hbr', hk2]
    show p.1 * (2 * Real.pi * (p.1 * Real.cos p.2) * (‖A‖ ^ 2 + ‖B‖ ^ 2 +
      (m : ℝ) ^ 2 * ‖a (P p)‖ ^ 2 / (p.1 * Real.cos p.2) ^ 2)) = _
    rw [← hrot]
    field_simp
    ring
  have h1 : ∫⁻ p in T, F_L p ≤ ∫⁻ p in T, G_R p := by
    rw [hTprod, lintegral_prod_symm _ mFL.aemeasurable, lintegral_prod_symm _ mGR.aemeasurable]
    refine lintegral_mono fun θ => ?_
    by_cases hc : 0 < Real.cos θ
    · set f : ℝ → ℂ := fun r => a (r * Real.cos θ, r * Real.sin θ) with hf
      have hfc : ContDiff ℝ 1 f := hac.comp (by fun_prop)
      have hfs : HasCompactSupport f := ray_support a has θ
      have hfd : ∀ r, deriv f r = br (r, θ) := fun r => (hdr r θ).deriv
      have hH := hR f hfc hfs
      have eL : ∫⁻ r in Set.Ioi (0 : ℝ), F_L (r, θ) =
          ENNReal.ofReal (2 * Real.pi / 4 * Real.cos θ) * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f r‖ ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun r => ?_
        simp only [hFL, hf, hb, hP]
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf
      have eR : ∫⁻ r in Set.Ioi (0 : ℝ), G_R (r, θ) =
          ENNReal.ofReal (2 * Real.pi * Real.cos θ) * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun r => ?_
        simp only [hGR, hfd]
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf
      rw [eL, eR]
      calc ENNReal.ofReal (2 * Real.pi / 4 * Real.cos θ) * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f r‖ ^ 2)
          ≤ ENNReal.ofReal (2 * Real.pi / 4 * Real.cos θ) *
              (4 * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2)) := by gcongr
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
    · have hz : ∀ r, F_L (r, θ) = 0 := by
        intro r
        simp only [hFL]
        refine ENNReal.ofReal_of_nonpos ?_
        have : Real.cos θ ≤ 0 := not_lt.1 hc
        have : Real.cos θ * ‖b (r, θ)‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this (by positivity)
        nlinarith [Real.pi_pos]
      simp only [hz, lintegral_zero]
      exact zero_le
  have h2 : ∫⁻ p in T, F_T p ≤ ∫⁻ p in T, G_T p := by
    rw [hTprod, lintegral_prod _ mFT.aemeasurable, lintegral_prod _ mGT.aemeasurable]
    refine lintegral_mono fun r => ?_
    set g : ℝ → ℂ := fun θ => a (r * Real.cos θ, r * Real.sin θ) with hg
    have hgc : ContDiff ℝ 1 g := hac.comp (by fun_prop)
    have hgd : ∀ θ, deriv g θ = bt (r, θ) := fun θ => (hdt r θ).deriv
    have hgax : 0 < m → g (-(Real.pi / 2)) = 0 ∧ g (Real.pi / 2) = 0 := by
      intro hm0
      have hk : k ≠ 0 := by
        intro h0
        rw [hm, h0] at hm0
        simp at hm0
      have := hax hk
      simp only [hg, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero]
      exact ⟨this _, this _⟩
    have hcase : t = (m : ℝ) * ((m : ℝ) + 1) ∨ (t = ((m : ℝ) + 1) * ((m : ℝ) + 2) ∧ g 0 = 0) := by
      rcases hs with h | ⟨h, hodd⟩
      · left
        rw [ht, h, hkm]
        ring
      · right
        refine ⟨by rw [ht, h, hkm]; ring, ?_⟩
        have := hodd (r, 0)
        simp only [neg_zero] at this
        simp only [hg, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
        exact self_eq_neg.1 this
    have hB := hA g m t hgc hgax hcase
    have eL : ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), F_T (r, θ) =
        ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal t *
          ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun θ => ?_
      simp only [hFT, hg, hb, hP]
      rw [← ENNReal.ofReal_mul htnn, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have eR : ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), G_T (r, θ) =
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
          (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun θ => ?_
      simp only [hGT, hgd]
      simp only [hg, hb, hP]
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [eL, eR]
    gcongr
  rw [hLeq, hReq, lintegral_add_left mFL, lintegral_add_left mGR]
  exact add_le_add h1 h2

theorem radialInverseSquare : RadialInverseSquareStatement := by
  intro f hf hs
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hs.isCompact.isBounded
  set R : ℝ := |R'| + 1 with hRdef
  have hR0 : 0 < R := by positivity
  have hzero : ∀ r, R ≤ r → f r = 0 := by
    intro r hr
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR' hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have h1 : R' ≤ |R'| := le_abs_self R'
    have h2 : r ≤ |r| := le_abs_self r
    linarith
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfc : Continuous f := hf.continuous
  set v : ℝ → ℝ := fun r => ‖f r‖ ^ 2 with hv
  set v' : ℝ → ℝ := fun r => 2 * inner ℝ (f r) (deriv f r) with hv'
  have hvd : ∀ r, HasDerivAt v (v' r) r := fun r => (hfd r).hasDerivAt.norm_sq
  have hvc : Continuous v := by simp only [hv]; fun_prop
  have hv'c : Continuous v' := by simp only [hv']; fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R) (u := fun r : ℝ => r)
    (u' := fun _ => (1 : ℝ)) (v := v) (v' := v') (fun r _ => hasDerivAt_id r) (fun r _ => hvd r)
    intervalIntegrable_const (hv'c.intervalIntegrable _ _)
  have hvR : v R = 0 := by simp [hv, hzero R le_rfl]
  simp only [hvR, mul_zero, zero_mul, sub_zero, one_mul, zero_sub] at hparts
  set I : ℝ := ∫ r in (0 : ℝ)..R, v r with hI
  set J : ℝ := ∫ r in (0 : ℝ)..R, r ^ 2 * ‖deriv f r‖ ^ 2 with hJ
  have hpt : ∀ r, -(r * v' r) ≤ 1 / 2 * v r + 2 * (r ^ 2 * ‖deriv f r‖ ^ 2) := by
    intro r
    simp only [hv, hv']
    have hcs : |inner ℝ (f r) (deriv f r)| ≤ ‖f r‖ * ‖deriv f r‖ := abs_real_inner_le_norm _ _
    have h1 : -(r * (2 * inner ℝ (f r) (deriv f r))) ≤ 2 * (|r| * (‖f r‖ * ‖deriv f r‖)) := by
      have := neg_abs_le (r * inner ℝ (f r) (deriv f r))
      rw [abs_mul] at this
      nlinarith [abs_nonneg r, mul_le_mul_of_nonneg_left hcs (abs_nonneg r)]
    nlinarith [sq_nonneg (‖f r‖ / 2 - |r| * ‖deriv f r‖), sq_abs r, norm_nonneg (f r), norm_nonneg (deriv f r)]
  have hineq : I ≤ 1 / 2 * I + 2 * J := by
    have e : I = ∫ r in (0 : ℝ)..R, -(r * v' r) := by
      rw [intervalIntegral.integral_neg, hparts, neg_neg]
    have hi1 : IntervalIntegrable (fun r => -(r * v' r)) volume 0 R := by
      exact (by fun_prop : Continuous fun r => -(r * v' r)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun r => 1 / 2 * v r + 2 * (r ^ 2 * ‖deriv f r‖ ^ 2)) volume 0 R :=
      (by fun_prop : Continuous fun r => 1 / 2 * v r + 2 * (r ^ 2 * ‖deriv f r‖ ^ 2)).intervalIntegrable _ _
    have ia : IntervalIntegrable (fun r => 1 / 2 * v r) volume 0 R :=
      (by fun_prop : Continuous fun r => 1 / 2 * v r).intervalIntegrable _ _
    have ib : IntervalIntegrable (fun r => 2 * (r ^ 2 * ‖deriv f r‖ ^ 2)) volume 0 R :=
      (by fun_prop : Continuous fun r => 2 * (r ^ 2 * ‖deriv f r‖ ^ 2)).intervalIntegrable _ _
    calc I = ∫ r in (0 : ℝ)..R, -(r * v' r) := e
      _ ≤ ∫ r in (0 : ℝ)..R, (1 / 2 * v r + 2 * (r ^ 2 * ‖deriv f r‖ ^ 2)) :=
          intervalIntegral.integral_mono_on hR0.le hi1 hi2 fun r _ => hpt r
      _ = 1 / 2 * I + 2 * J := by
          rw [intervalIntegral.integral_add ia ib, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hIJ : I ≤ 4 * J := by linarith
  have hIeq : ∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (‖f r‖ ^ 2) = ENNReal.ofReal I := by
    rw [hI, intervalIntegral.integral_of_le hR0.le, ofReal_integral_eq_lintegral_ofReal]
    · exact (hvc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Eventually.of_forall fun r => by positivity
  have hJeq : ∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2) = ENNReal.ofReal J := by
    rw [hJ, intervalIntegral.integral_of_le hR0.le, ofReal_integral_eq_lintegral_ofReal]
    · exact ((by fun_prop : Continuous fun r : ℝ => r ^ 2 * ‖deriv f r‖ ^ 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Eventually.of_forall fun r => by positivity
  have hsplit : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 R ∪ Set.Ioi R := by
    intro r hr
    by_cases h : r ≤ R
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr (not_le.1 h)
  have htail : ∫⁻ r in Set.Ioi R, ENNReal.ofReal (‖f r‖ ^ 2) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun r hr => by
      simp [hzero r (le_of_lt hr)]]
    simp
  calc ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f r‖ ^ 2)
      ≤ ∫⁻ r in Set.Ioc (0 : ℝ) R ∪ Set.Ioi R, ENNReal.ofReal (‖f r‖ ^ 2) := lintegral_mono_set hsplit
    _ ≤ (∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (‖f r‖ ^ 2)) + ∫⁻ r in Set.Ioi R, ENNReal.ofReal (‖f r‖ ^ 2) :=
        lintegral_union_le _ _ _
    _ = ENNReal.ofReal I := by rw [htail, add_zero, hIeq]
    _ ≤ ENNReal.ofReal (4 * J) := ENNReal.ofReal_le_ofReal hIJ
    _ = 4 * ENNReal.ofReal J := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ = 4 * ∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2) := by rw [hJeq]
    _ ≤ 4 * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2) := by
        have hmono : (∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2)) ≤
            ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖deriv f r‖ ^ 2) := lintegral_mono_set Set.Ioc_subset_Ioi_self
        gcongr

def AngularOddBoundStatement : Prop :=
  ∀ (g : ℝ → ℂ) (m : ℕ), ContDiff ℝ 1 g → (0 < m → g (-(Real.pi / 2)) = 0 ∧ g (Real.pi / 2) = 0) → g 0 = 0 →
    ENNReal.ofReal (((m : ℝ) + 1) * ((m : ℝ) + 2)) *
        ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2) ≤
      ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
        (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2))

private theorem angular_pt (X Y : ℂ) (c s m : ℝ) (hc : 0 < c) (hcs : c ^ 2 + s ^ 2 = 1) :
    m ^ 2 * c * ‖Y‖ ^ 2 - m * s * (2 * inner ℝ Y X) ≤ c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^ 2) := by
  have hN : 0 ≤ (c * X.re + m * s * Y.re) ^ 2 + (c * X.im + m * s * Y.im) ^ 2 := by positivity
  have hin : inner ℝ Y X = Y.re * X.re + Y.im * X.im := by
    simp [Complex.inner, mul_comm]
  have hX : ‖X‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hY : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hin, hX, hY]
  rw [← sub_nonneg]
  have e : c * (X.re ^ 2 + X.im ^ 2 + m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) / c ^ 2) -
      (m ^ 2 * c * (Y.re ^ 2 + Y.im ^ 2) - m * s * (2 * (Y.re * X.re + Y.im * X.im))) =
      ((c * X.re + m * s * Y.re) ^ 2 + (c * X.im + m * s * Y.im) ^ 2) / c := by
    field_simp
    linear_combination (-(m ^ 2 * (Y.re ^ 2 + Y.im ^ 2))) * hcs
  rw [e]
  positivity

theorem angularEven (g : ℝ → ℂ) (m : ℕ) (hg : ContDiff ℝ 1 g)
    (hax : 0 < m → g (-(Real.pi / 2)) = 0 ∧ g (Real.pi / 2) = 0) :
    ENNReal.ofReal ((m : ℝ) * ((m : ℝ) + 1)) *
        ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2) ≤
      ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
        (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgc : Continuous g := hg.continuous
  set v : ℝ → ℝ := fun θ => ‖g θ‖ ^ 2 with hv
  set v' : ℝ → ℝ := fun θ => 2 * inner ℝ (g θ) (deriv g θ) with hv'
  have hvd : ∀ θ, HasDerivAt v (v' θ) θ := fun θ => (hgd θ).hasDerivAt.norm_sq
  have hvc : Continuous v := by simp only [hv]; fun_prop
  have hv'c : Continuous v' := by simp only [hv']; fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (u := fun θ : ℝ => (m : ℝ) * Real.sin θ) (u' := fun θ => (m : ℝ) * Real.cos θ) (v := v) (v' := v')
    (fun θ _ => (Real.hasDerivAt_sin θ).const_mul _) (fun θ _ => hvd θ)
    ((by fun_prop : Continuous fun θ : ℝ => (m : ℝ) * Real.cos θ).intervalIntegrable _ _)
    (hv'c.intervalIntegrable _ _)
  have hbd : (m : ℝ) * Real.sin (Real.pi / 2) * v (Real.pi / 2) -
      (m : ℝ) * Real.sin (-(Real.pi / 2)) * v (-(Real.pi / 2)) = 0 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hax hpos
      simp [hv, h1, h2]
  rw [hbd, zero_sub] at hparts
  set h : ℝ → ℝ := fun θ => (m : ℝ) ^ 2 * (Real.cos θ * v θ) - (m : ℝ) * Real.sin θ * v' θ with hh
  have hhc : Continuous h := by simp only [hh]; fun_prop
  set C : ℝ := ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Real.cos θ * v θ with hC
  have hint : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), h θ = (m : ℝ) * ((m : ℝ) + 1) * C := by
    have i1 : IntervalIntegrable (fun θ => (m : ℝ) ^ 2 * (Real.cos θ * v θ)) volume (-(Real.pi / 2)) (Real.pi / 2) :=
      (by fun_prop : Continuous fun θ => (m : ℝ) ^ 2 * (Real.cos θ * v θ)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => (m : ℝ) * Real.sin θ * v' θ) volume (-(Real.pi / 2)) (Real.pi / 2) :=
      (by fun_prop : Continuous fun θ => (m : ℝ) * Real.sin θ * v' θ).intervalIntegrable _ _
    simp only [hh]
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul, hparts]
    have e : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), (m : ℝ) * Real.cos θ * v θ = (m : ℝ) * C := by
      rw [hC, ← intervalIntegral.integral_const_mul]
      congr 1
      funext θ
      ring
    rw [e]
    ring
  have hcos : ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ => Real.cos_pos_of_mem_Ioo hθ
  have hCnn : 0 ≤ C := by
    rw [hC]
    refine intervalIntegral.integral_nonneg hab fun θ hθ => ?_
    exact mul_nonneg (Real.cos_nonneg_of_mem_Icc hθ) (by positivity)
  have hL : ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2) = ENNReal.ofReal C := by
    rw [hC, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
    · exact ((by fun_prop : Continuous fun θ => Real.cos θ * v θ).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact mul_nonneg (hcos θ hθ).le (by positivity)
  rw [hL, ← ENNReal.ofReal_mul (by positivity), ← hint]
  calc ENNReal.ofReal (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), h θ)
      = ENNReal.ofReal (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), h θ) := by
        rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ ≤ ENNReal.ofReal (∫ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), max (h θ) 0) := by
        refine ENNReal.ofReal_le_ofReal (integral_mono ?_ ?_ fun θ => le_max_left _ _)
        · exact (hhc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
        · exact ((hhc.max continuous_const).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    _ = ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (max (h θ) 0) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact ((hhc.max continuous_const).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
        · exact Eventually.of_forall fun θ => le_max_right _ _
    _ = ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (h θ) := by
        refine lintegral_congr fun θ => ?_
        rcases le_total (h θ) 0 with hx | hx
        · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hx]
        · rw [max_eq_left hx]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioo fun θ hθ => ENNReal.ofReal_le_ofReal ?_
        have := angular_pt (deriv g θ) (g θ) (Real.cos θ) (Real.sin θ) (m : ℝ) (hcos θ hθ) (Real.cos_sq_add_sin_sq θ)
        simp only [hh, hv, hv']
        linarith

theorem angularCosBound_of (h : AngularOddBoundStatement) : AngularCosBoundStatement := by
  intro g m t hg hax ht
  rcases ht with ht | ⟨ht, h0⟩
  · rw [ht]
    exact angularEven g m hg hax
  · rw [ht]
    exact h g m hg hax h0

private theorem odd_pt (X Y : ℂ) (c s m : ℝ) (hc : 0 < c) (hs : s ≠ 0) (hcs : c ^ 2 + s ^ 2 = 1) :
    (m + 1) * (m + 2) * (c * ‖Y‖ ^ 2) -
        ((m * c + 2 * c + c ^ 3 / s ^ 2) * ‖Y‖ ^ 2 + (m * s - c ^ 2 / s) * (2 * inner ℝ Y X)) ≤
      c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^ 2) := by
  set W : ℝ := m * s - c ^ 2 / s with hW
  have hin : inner ℝ Y X = Y.re * X.re + Y.im * X.im := by
    simp [Complex.inner, mul_comm]
  have hX : ‖X‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hY : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hin, hX, hY, ← sub_nonneg]
  have e : c * (X.re ^ 2 + X.im ^ 2 + m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) / c ^ 2) -
      ((m + 1) * (m + 2) * (c * (Y.re ^ 2 + Y.im ^ 2)) -
        ((m * c + 2 * c + c ^ 3 / s ^ 2) * (Y.re ^ 2 + Y.im ^ 2) + W * (2 * (Y.re * X.re + Y.im * X.im)))) =
      ((c * X.re + W * Y.re) ^ 2 + (c * X.im + W * Y.im) ^ 2) / c := by
    rw [hW]
    field_simp
    linear_combination (-(m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) * s ^ 2)) * hcs
  rw [e]
  positivity

private theorem ofReal_int_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ENNReal.ofReal (∫ θ in a..b, f θ) ≤ ∫⁻ θ in Set.Ioo a b, ENNReal.ofReal (f θ) := by
  have hi : IntegrableOn f (Set.Ioo a b) := (hf.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hm : ContinuousOn (fun θ => max (f θ) 0) (Set.Icc a b) :=
    continuous_max.comp_continuousOn (hf.prodMk continuousOn_const)
  have hmi : IntegrableOn (fun θ => max (f θ) 0) (Set.Ioo a b) := (hm.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  calc ENNReal.ofReal (∫ θ in a..b, f θ) = ENNReal.ofReal (∫ θ in Set.Ioo a b, f θ) := by
        rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ ≤ ENNReal.ofReal (∫ θ in Set.Ioo a b, max (f θ) 0) :=
        ENNReal.ofReal_le_ofReal (integral_mono hi hmi fun θ => le_max_left _ _)
    _ = ∫⁻ θ in Set.Ioo a b, ENNReal.ofReal (max (f θ) 0) :=
        ofReal_integral_eq_lintegral_ofReal hmi (Eventually.of_forall fun θ => le_max_right _ _)
    _ = ∫⁻ θ in Set.Ioo a b, ENNReal.ofReal (f θ) := by
        refine lintegral_congr fun θ => ?_
        rcases le_total (f θ) 0 with hx | hx
        · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hx]
        · rw [max_eq_left hx]

theorem angularOdd : AngularOddBoundStatement := by
  intro g m hg hax h0
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgc : Continuous g := hg.continuous
  set v : ℝ → ℝ := fun θ => ‖g θ‖ ^ 2 with hv
  set v' : ℝ → ℝ := fun θ => 2 * inner ℝ (g θ) (deriv g θ) with hv'
  have hvd : ∀ θ, HasDerivAt v (v' θ) θ := fun θ => (hgd θ).hasDerivAt.norm_sq
  have hvc : Continuous v := by simp only [hv]; fun_prop
  have hv'c : Continuous v' := by simp only [hv']; fun_prop
  have hv0 : v 0 = 0 := by simp [hv, h0]
  have hv'0 : v' 0 = 0 := by simp [hv', h0]
  set K : ℝ := ((m : ℝ) + 1) * ((m : ℝ) + 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set W : ℝ → ℝ := fun θ => (m : ℝ) * Real.sin θ - Real.cos θ ^ 2 / Real.sin θ with hW
  set W' : ℝ → ℝ := fun θ => (m : ℝ) * Real.cos θ + 2 * Real.cos θ + Real.cos θ ^ 3 / Real.sin θ ^ 2 with hW'
  have hWd : ∀ θ, Real.sin θ ≠ 0 → HasDerivAt W (W' θ) θ := by
    intro θ hs
    have h1 := ((Real.hasDerivAt_sin θ).const_mul (m : ℝ)).sub (((Real.hasDerivAt_cos θ).pow 2).div (Real.hasDerivAt_sin θ) hs)
    refine h1.congr_deriv ?_
    simp only [hW', Pi.pow_apply]
    field_simp
    ring
  set h : ℝ → ℝ := fun θ => K * (Real.cos θ * v θ) - (W' θ * v θ + W θ * v' θ) with hh
  have hpt : ∀ θ, 0 < Real.cos θ → Real.sin θ ≠ 0 →
      h θ ≤ Real.cos θ * (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2) := by
    intro θ hc hs
    have := odd_pt (deriv g θ) (g θ) (Real.cos θ) (Real.sin θ) (m : ℝ) hc hs (Real.cos_sq_add_sin_sq θ)
    simp only [hh, hv, hv', hW, hW', hK]
    linarith
  have hDcont : ∀ a b : ℝ, (∀ x ∈ Set.Icc a b, Real.sin x ≠ 0) →
      ContinuousOn (fun θ => W' θ * v θ + W θ * v' θ) (Set.Icc a b) := by
    intro a b hne
    simp only [hW, hW']
    refine ContinuousOn.add (ContinuousOn.mul ?_ hvc.continuousOn) (ContinuousOn.mul ?_ hv'c.continuousOn)
    · exact (by fun_prop : Continuous fun θ => (m : ℝ) * Real.cos θ + 2 * Real.cos θ).continuousOn.add
        ((Real.continuous_cos.pow 3).continuousOn.div (Real.continuous_sin.pow 2).continuousOn
          fun x hx => pow_ne_zero 2 (hne x hx))
    · exact (by fun_prop : Continuous fun θ => (m : ℝ) * Real.sin θ).continuousOn.sub
        ((Real.continuous_cos.pow 2).continuousOn.div Real.continuous_sin.continuousOn hne)
  have hhcont : ∀ a b : ℝ, (∀ x ∈ Set.Icc a b, Real.sin x ≠ 0) → ContinuousOn h (Set.Icc a b) := by
    intro a b hne
    exact (by fun_prop : Continuous fun θ => K * (Real.cos θ * v θ)).continuousOn.sub (hDcont a b hne)
  have hFTC : ∀ a b : ℝ, a ≤ b → (∀ x ∈ Set.Icc a b, Real.sin x ≠ 0) →
      ∫ θ in a..b, h θ = K * (∫ θ in a..b, Real.cos θ * v θ) - (W b * v b - W a * v a) := by
    intro a b hab hne
    have i1 : IntervalIntegrable (fun θ => K * (Real.cos θ * v θ)) volume a b :=
      (by fun_prop : Continuous fun θ => K * (Real.cos θ * v θ)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => W' θ * v θ + W θ * v' θ) volume a b :=
      (hDcont a b hne).intervalIntegrable_of_Icc hab
    have hftc : ∫ θ in a..b, (W' θ * v θ + W θ * v' θ) = W b * v b - W a * v a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => W x * v x) (fun x hx => by
        rw [Set.uIcc_of_le hab] at hx
        exact (hWd x (hne x hx)).mul (hvd x)) i2
    simp only [hh]
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul, hftc]
  have hpi : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hbR : W (Real.pi / 2) * v (Real.pi / 2) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · simp [hW, hm0, Real.cos_pi_div_two]
    · simp [hv, (hax hpos).2]
  have hbL : W (-(Real.pi / 2)) * v (-(Real.pi / 2)) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · simp [hW, hm0, Real.cos_pi_div_two]
    · simp [hv, (hax hpos).1]
  set C : ℝ := ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Real.cos θ * v θ with hC
  set Q : ℝ → ℝ := fun e => (∫ θ in (-(Real.pi / 2))..(-e), Real.cos θ * v θ) - ∫ θ in (Real.pi / 2)..e, Real.cos θ * v θ with hQ
  set Bd : ℝ → ℝ := fun e => Real.cos e ^ 2 * (v e + v (-e)) / Real.sin e with hBd
  have hbound : ∀ e ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (K * Q e - Bd e) ≤
      ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
        (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := by
    intro e he
    have he0 : 0 < e := he.1
    have hes : 0 < Real.sin e := Real.sin_pos_of_pos_of_lt_pi he0 (by linarith [he.2, Real.pi_pos])
    have hneR : ∀ x ∈ Set.Icc e (Real.pi / 2), Real.sin x ≠ 0 := fun x hx =>
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])).ne'
    have hneL : ∀ x ∈ Set.Icc (-(Real.pi / 2)) (-e), Real.sin x ≠ 0 := by
      intro x hx
      have : 0 < Real.sin (-x) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.2]) (by linarith [hx.1, Real.pi_pos])
      rw [Real.sin_neg] at this
      exact (neg_pos.1 this).ne
    have hR := hFTC e (Real.pi / 2) he.2.le hneR
    have hL := hFTC (-(Real.pi / 2)) (-e) (by linarith [he.2]) hneL
    rw [hbR] at hR
    rw [hbL] at hL
    have e1 := ofReal_int_le he.2.le (hhcont e (Real.pi / 2) hneR)
    have e2 := ofReal_int_le (by linarith [he.2] : -(Real.pi / 2) ≤ -e) (hhcont (-(Real.pi / 2)) (-e) hneL)
    have hWe : W e * v e ≥ -(Real.cos e ^ 2 * v e / Real.sin e) := by
      simp only [hW]
      have : 0 ≤ (m : ℝ) * Real.sin e * v e := by positivity
      rw [sub_mul, div_mul_eq_mul_div]
      linarith
    have hWme : -(W (-e) * v (-e)) ≥ -(Real.cos e ^ 2 * v (-e) / Real.sin e) := by
      simp only [hW, Real.sin_neg, Real.cos_neg]
      have : 0 ≤ (m : ℝ) * Real.sin e * v (-e) := by positivity
      rw [div_neg, sub_neg_eq_add, add_mul, div_mul_eq_mul_div]
      nlinarith
    have hsum : K * Q e - Bd e ≤ (∫ θ in (-(Real.pi / 2))..(-e), h θ) + ∫ θ in e..(Real.pi / 2), h θ := by
      rw [hL, hR]
      simp only [hQ, hBd]
      rw [intervalIntegral.integral_symm e]
      have hsplit : Real.cos e ^ 2 * (v e + v (-e)) / Real.sin e =
          Real.cos e ^ 2 * v e / Real.sin e + Real.cos e ^ 2 * v (-e) / Real.sin e := by ring
      rw [hsplit, sub_neg_eq_add, mul_add]
      linarith [hWe, hWme]
    have hunion : Set.Ioo (-(Real.pi / 2)) (-e) ∪ Set.Ioo e (Real.pi / 2) ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro x hx
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2, he0, Real.pi_pos]⟩
      · exact ⟨by linarith [hx.1, he0, Real.pi_pos], hx.2⟩
    have hdisj : Disjoint (Set.Ioo (-(Real.pi / 2)) (-e)) (Set.Ioo e (Real.pi / 2)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      linarith [h1.2, h2.1]
    have mono1 : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) → (∀ x ∈ Set.Ioo a b, Real.sin x ≠ 0) →
        ∫⁻ θ in Set.Ioo a b, ENNReal.ofReal (h θ) ≤ ∫⁻ θ in Set.Ioo a b, ENNReal.ofReal (Real.cos θ *
          (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := by
      intro a b hsub hne
      refine setLIntegral_mono' measurableSet_Ioo fun θ hθ => ENNReal.ofReal_le_ofReal ?_
      exact hpt θ (Real.cos_pos_of_mem_Ioo (hsub hθ)) (hne θ hθ)
    calc ENNReal.ofReal (K * Q e - Bd e)
        ≤ ENNReal.ofReal ((∫ θ in (-(Real.pi / 2))..(-e), h θ) + ∫ θ in e..(Real.pi / 2), h θ) :=
          ENNReal.ofReal_le_ofReal hsum
      _ ≤ ENNReal.ofReal (∫ θ in (-(Real.pi / 2))..(-e), h θ) + ENNReal.ofReal (∫ θ in e..(Real.pi / 2), h θ) :=
          ENNReal.ofReal_add_le
      _ ≤ (∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (-e), ENNReal.ofReal (h θ)) +
            ∫⁻ θ in Set.Ioo e (Real.pi / 2), ENNReal.ofReal (h θ) := add_le_add e2 e1
      _ ≤ (∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (-e), ENNReal.ofReal (Real.cos θ *
              (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2))) +
            ∫⁻ θ in Set.Ioo e (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
              (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := by
          exact add_le_add (mono1 _ _ (fun x hx => hunion (Or.inl hx)) fun x hx => hneL x ⟨hx.1.le, hx.2.le⟩)
            (mono1 _ _ (fun x hx => hunion (Or.inr hx)) fun x hx => hneR x ⟨hx.1.le, hx.2.le⟩)
      _ = ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (-e) ∪ Set.Ioo e (Real.pi / 2), ENNReal.ofReal (Real.cos θ *
              (‖deriv g θ‖ ^ 2 + (m : ℝ) ^ 2 * ‖g θ‖ ^ 2 / Real.cos θ ^ 2)) := (lintegral_union measurableSet_Ioo hdisj).symm
      _ ≤ _ := lintegral_mono_set hunion
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcos : ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ => Real.cos_pos_of_mem_Ioo hθ
  have hLint : ∫⁻ θ in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), ENNReal.ofReal (Real.cos θ * ‖g θ‖ ^ 2) = ENNReal.ofReal C := by
    rw [hC, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
    · exact ((by fun_prop : Continuous fun θ => Real.cos θ * v θ).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact mul_nonneg (hcos θ hθ).le (by positivity)
  rw [hLint, ← ENNReal.ofReal_mul hK0]
  have hcv : Continuous fun t : ℝ => Real.cos t * v t := by fun_prop
  have hQc : Continuous Q := by
    simp only [hQ]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
        (f := fun (_ : ℝ) (t : ℝ) => Real.cos t * v t) (a₀ := -(Real.pi / 2)) (hcv.comp continuous_snd) continuous_neg).sub
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
        (f := fun (_ : ℝ) (t : ℝ) => Real.cos t * v t) (a₀ := Real.pi / 2) (hcv.comp continuous_snd) continuous_id)
  have hQ0 : Q 0 = C := by
    simp only [hQ, hC, neg_zero]
    rw [intervalIntegral.integral_symm 0 (Real.pi / 2), sub_neg_eq_add,
      intervalIntegral.integral_add_adjacent_intervals (hcv.intervalIntegrable _ _) (hcv.intervalIntegrable _ _)]
  have hsR : Tendsto (fun t : ℝ => t⁻¹ * v t) (𝓝[>] 0) (𝓝 0) := by
    have := (hvd 0).tendsto_slope_zero_right
    simpa [hv0, hv'0] using this
  have hsL : Tendsto (fun t : ℝ => t⁻¹ * v (-t)) (𝓝[>] 0) (𝓝 0) := by
    have hd : HasDerivAt (fun t => v (-t)) (v' (-0) * -1) 0 := (hvd (-0)).comp 0 (hasDerivAt_neg 0)
    have := hd.tendsto_slope_zero_right
    simpa [hv0, hv'0] using this
  have hev : ∀ᶠ e in 𝓝[>] (0 : ℝ), e ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := Ioo_mem_nhdsGT (by positivity)
  have hBd : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have hup : Tendsto (fun e : ℝ => Real.pi / 2 * (e⁻¹ * v e + e⁻¹ * v (-e))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hsR.add hsL).const_mul (Real.pi / 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with e he
      have hes : 0 < Real.sin e := Real.sin_pos_of_pos_of_lt_pi he.1 (by linarith [he.2, Real.pi_pos])
      simp only [hBd]
      positivity
    · filter_upwards [hev] with e he
      have hes : 0 < Real.sin e := Real.sin_pos_of_pos_of_lt_pi he.1 (by linarith [he.2, Real.pi_pos])
      have hj : 2 / Real.pi * e ≤ Real.sin e := Real.mul_le_sin he.1.le he.2.le
      have hv1 : 0 ≤ v e + v (-e) := by positivity
      have hc2 : Real.cos e ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_add_sin_sq e, sq_nonneg (Real.sin e)]
      simp only [hBd]
      rw [div_le_iff₀ hes]
      have hpe : 0 < e := he.1
      have e1 : Real.pi / 2 * (e⁻¹ * v e + e⁻¹ * v (-e)) * (2 / Real.pi * e) = v e + v (-e) := by
        field_simp
      have h3 : Real.pi / 2 * (e⁻¹ * v e + e⁻¹ * v (-e)) * (2 / Real.pi * e) ≤
          Real.pi / 2 * (e⁻¹ * v e + e⁻¹ * v (-e)) * Real.sin e := by
        apply mul_le_mul_of_nonneg_left hj
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hc2 hv1]
  have hlim : Tendsto (fun e => ENNReal.ofReal (K * Q e - Bd e)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (K * C))) := by
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Tendsto Q (𝓝[>] 0) (𝓝 C) := by
      rw [← hQ0]
      exact (hQc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using (h1.const_mul K).sub hBd
  exact le_of_tendsto hlim (by filter_upwards [hev] with e he using hbound e he)

end FrameInverseSquareHalfPlane

namespace FrameInverseSquareParts

open SteadyCert CellCert.Reduction FrameInverseSquareHalfPlane

theorem frameModeCalculus' : FrameModeCalculusStatement := by
  intro u hu hs k
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
  have hHc : ContDiff ℝ 1 (horizontalPart u) :=
    (Complex.ofRealCLM.contDiff.comp ((coord 0).contDiff.comp hu1)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((coord 1).contDiff.comp hu1)))
  have hVc : ContDiff ℝ 1 (verticalPart u) :=
    Complex.ofRealCLM.contDiff.comp ((coord 2).contDiff.comp hu1)
  have hHs : HasCompactSupport (horizontalPart u) :=
    hs.comp_left (g := fun w : Space => ((w 0 : ℝ) : ℂ) + Complex.I * ((w 1 : ℝ) : ℂ)) (by simp)
  have hVs : HasCompactSupport (verticalPart u) :=
    hs.comp_left (g := fun w : Space => ((w 2 : ℝ) : ℂ)) (by simp)
  obtain ⟨hac, has, had⟩ := modeData (horizontalPart u) hHc hHs k
  obtain ⟨hbc, hbs, hbd⟩ := modeData (verticalPart u) hVc hVs k
  refine ⟨⟨hac, has⟩, ⟨hbc, hbs⟩, fun ρ z hρ => ?_⟩
  obtain ⟨a0, a2, a1⟩ := had ρ z hρ
  obtain ⟨b0, b2, b1⟩ := hbd ρ z hρ
  have eH : ∀ c : Fin 3, horizontalPart (fun y => fderiv ℝ u y (ringFrame c y)) =
      fun y => fderiv ℝ (horizontalPart u) y (ringFrame c y) :=
    fun c => funext fun y => (hpart_fderiv u hud y _).symm
  have eV : ∀ c : Fin 3, verticalPart (fun y => fderiv ℝ u y (ringFrame c y)) =
      fun y => fderiv ℝ (verticalPart u) y (ringFrame c y) :=
    fun c => funext fun y => (vpart_fderiv u hud y _).symm
  simp only [frameModeSq, Fin.sum_univ_three, eH, eV]
  rw [← a0, ← a2, a1, ← b0, ← b2, b1, norm_mode_sq k ρ hρ, norm_mode_sq k ρ hρ]
  ring

theorem halfPlaneBound' : HalfPlaneBoundStatement :=
  halfPlaneBound_of_axis (axisHalfPlaneBound_of radialInverseSquare (angularCosBound_of angularOdd))

end FrameInverseSquareParts

end FracInternal

end Breakdown

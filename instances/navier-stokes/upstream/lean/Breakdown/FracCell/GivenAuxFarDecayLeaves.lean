import Breakdown.FracCell.GivenAuxFarDecay
import Breakdown.FracCell.GivenAuxPinSmoothLocal

noncomputable section

namespace Breakdown

namespace FarDecayInternal

open CellCert.GivenFields

theorem coord_far (i : Fin 3) : FarDecay (fun y : Space => y i) (-1) := by
  have h := FarDecay.ident.clm (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
  have e : (fun y : Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) y) = fun y => y i := funext fun y => by simp
  rw [e] at h
  exact h

theorem normSq_far : FarDecay (fun y : Space => ‖y‖ ^ 2) (-2) := by
  have h := (((coord_far 0).rmul (coord_far 0)).add ((coord_far 1).rmul (coord_far 1))).add
    ((coord_far 2).rmul (coord_far 2))
  have e : (fun y : Space => y 0 * y 0 + y 1 * y 1 + y 2 * y 2) = fun y => ‖y‖ ^ 2 := by
    funext y
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  rw [e] at h
  exact h.mono (b := -2) (le_of_eq (by norm_num))

theorem normSq_low : ∀ y : Space, 2 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1, 1 / 4 * ‖y‖ ^ (-(-2 : ℝ)) ≤ ‖z‖ ^ 2 := by
  intro y hy z hz
  rw [neg_neg, Real.rpow_two]
  have := ball_norm_ge hz
  nlinarith

theorem sq_rpow (y : Space) (q : ℝ) : (‖y‖ ^ 2) ^ q = ‖y‖ ^ (2 * q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
  norm_num

theorem norm_far : FarDecay (fun y : Space => ‖y‖) (-1) := by
  have h := normSq_far.rpow (R0 := 2) (c := 1 / 4) (by norm_num) normSq_low (1 / 2)
  have e : (fun z : Space => (‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) = fun z => ‖z‖ := by
    funext z
    rw [sq_rpow]
    norm_num
  rw [e] at h
  exact h.mono (b := -1) (le_of_eq (by norm_num))

theorem invNorm_far : FarDecay (fun y : Space => ‖y‖⁻¹) 1 := by
  have h := normSq_far.rpow (R0 := 2) (c := 1 / 4) (by norm_num) normSq_low (-1 / 2)
  have e : (fun z : Space => (‖z‖ ^ 2) ^ ((-1 : ℝ) / 2)) = fun z => ‖z‖⁻¹ := by
    funext z
    rw [sq_rpow]
    norm_num [Real.rpow_neg_one]
  rw [e] at h
  exact h.mono (b := 1) (le_of_eq (by norm_num))

theorem ratio_far (i : Fin 3) : FarDecay (fun y : Space => y i / ‖y‖) 0 := by
  have h := (coord_far i).rmul invNorm_far
  have e : (fun y : Space => y i * ‖y‖⁻¹) = fun y => y i / ‖y‖ := funext fun y => (div_eq_mul_inv _ _).symm
  rw [e] at h
  exact h.mono (b := 0) (le_of_eq (by norm_num))

theorem radial_far (i : Fin 3) : FarDecay (fun y => radialVec y i) 0 := ratio_far i

theorem polar_far (i : Fin 3) : FarDecay (fun y => polarVecQ y i) 0 := by
  fin_cases i
  · have h := (ratio_far 2).rmul (ratio_far 0)
    have e : (fun y : Space => y 2 / ‖y‖ * (y 0 / ‖y‖)) = fun y => polarVecQ y 0 := by
      funext y
      show _ = heightRatio y * y 0 / ‖y‖
      unfold heightRatio
      ring
    rw [e] at h
    exact h.mono (b := 0) (le_of_eq (by norm_num))
  · have h := (ratio_far 2).rmul (ratio_far 1)
    have e : (fun y : Space => y 2 / ‖y‖ * (y 1 / ‖y‖)) = fun y => polarVecQ y 1 := by
      funext y
      show _ = heightRatio y * y 1 / ‖y‖
      unfold heightRatio
      ring
    rw [e] at h
    exact h.mono (b := 0) (le_of_eq (by norm_num))
  · have h := ((FarDecay.const (1 : ℝ)).add (((ratio_far 2).rmul (ratio_far 2)).mono (b := 0)
      (le_of_eq (by norm_num))).neg).neg
    have e : (fun y : Space => -((1 : ℝ) + -(y 2 / ‖y‖ * (y 2 / ‖y‖)))) = fun y => polarVecQ y 2 := by
      funext y
      show _ = -(qOf y)
      unfold qOf heightRatio
      ring
    rw [e] at h
    exact h

theorem azim_far (i : Fin 3) : FarDecay (fun y => azimVecQ y i) 0 := by
  fin_cases i
  · have h := (ratio_far 1).neg
    have e : (fun y : Space => -(y 1 / ‖y‖)) = fun y => azimVecQ y 0 := by
      funext y
      show _ = -(y 1) / ‖y‖
      ring
    rw [e] at h
    exact h
  · exact ratio_far 0
  · exact FarDecay.const (0 : ℝ)

theorem chartS_eq (P : ChartParams) (hP : IsChartParams P) :
    chartS P = fun y => P.L0 * (‖y‖ + P.L0) ^ (-1 : ℝ) := by
  funext y
  have h : ‖y‖ + P.L0 ≠ 0 := by linarith [norm_nonneg y, hP.L0_pos]
  unfold chartS chartT
  rw [Real.rpow_neg_one]
  field_simp
  ring

theorem chartS_far (P : ChartParams) (hP : IsChartParams P) : FarDecay (chartS P) 1 := by
  have n1 := norm_far.add ((FarDecay.const P.L0).mono (b := -1) (by norm_num))
  have low : ∀ y : Space, 2 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1, 1 / 2 * ‖y‖ ^ (-(-1 : ℝ)) ≤ ‖z‖ + P.L0 := by
    intro y hy z hz
    rw [neg_neg, Real.rpow_one]
    linarith [ball_norm_ge hz, hP.L0_pos]
  have inv := n1.rpow (R0 := 2) (c := 1 / 2) (by norm_num) low (-1)
  have sF := (FarDecay.const P.L0).rmul inv
  rw [chartS_eq P hP]
  exact sF.mono (b := 1) (le_of_eq (by norm_num))

theorem decay_far (P : ChartParams) (hP : IsChartParams P) : FarDecay (decayFactor P) 0 := by
  have hL := hP.L0_pos
  have low : ∀ y : Space, 2 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1,
      P.L0 / (2 + P.L0) * ‖y‖ ^ (-(1 : ℝ)) ≤ chartS P z := by
    intro y hy z hz
    rw [chartS_eq P hP]
    show P.L0 / (2 + P.L0) * ‖y‖ ^ (-(1 : ℝ)) ≤ P.L0 * (‖z‖ + P.L0) ^ (-1 : ℝ)
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    have hz1 := ball_norm_le hz
    have hz0 := norm_nonneg z
    have hpos : 0 < ‖z‖ + P.L0 := by linarith
    have hle : ‖z‖ + P.L0 ≤ (2 + P.L0) * ‖y‖ := by nlinarith
    have e : P.L0 / (2 + P.L0) * ‖y‖⁻¹ = P.L0 / ((2 + P.L0) * ‖y‖) := by
      have : ‖y‖ ≠ 0 := by linarith
      field_simp
    rw [e, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hL.le hpos hle
  have h := (chartS_far P hP).rpow (R0 := 2) (c := P.L0 / (2 + P.L0)) (by positivity) low (2 * P.eps)
  exact h.mono (b := 0) (by linarith [hP.eps_pos])

theorem chartT_far (P : ChartParams) (hP : IsChartParams P) : FarDecay (chartT P) 0 := by
  have h := (FarDecay.const (1 : ℝ)).add ((chartS_far P hP).neg.mono (b := 0) (by norm_num))
  have e : (fun y : Space => (1 : ℝ) + -chartS P y) = chartT P := by
    funext y
    unfold chartS
    ring
  rw [e] at h
  exact h

theorem chart_far (P : ChartParams) (hP : IsChartParams P) :
    FarDecay (fun y : Space => (chartT P y, heightRatio y)) 0 :=
  (chartT_far P hP).prodMk (ratio_far 2)

theorem chart_mem (P : ChartParams) (hP : IsChartParams P) (z : Space) (hz : 1 ≤ ‖z‖) :
    (chartT P z, heightRatio z) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
  have hpos : 0 < ‖z‖ + P.L0 := by linarith [hP.L0_pos]
  have hc : |z 2| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z 2
    rwa [Real.norm_eq_abs] at this
  have hr : |heightRatio z| ≤ 1 := by
    unfold heightRatio
    rw [abs_div, abs_norm]
    exact div_le_one_of_le₀ hc (norm_nonneg _)
  refine Set.mk_mem_prod ⟨?_, ?_⟩ ⟨(abs_le.1 hr).1, (abs_le.1 hr).2⟩
  · unfold chartT
    exact div_nonneg (norm_nonneg _) hpos.le
  · unfold chartT
    rw [div_le_one hpos]
    linarith [hP.L0_pos]

theorem locSlope_add {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] {f g : X → E}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (fun x => f x + g x) := by
  intro x
  obtain ⟨K1, t1, ht1, h1⟩ := hf x
  obtain ⟨K2, t2, ht2, h2⟩ := hg x
  exact ⟨K1 + K2, t1 ∩ t2, Filter.inter_mem ht1 ht2,
    (h1.mono Set.inter_subset_left).add (h2.mono Set.inter_subset_right)⟩

theorem locSlope_smul {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → ℂ}
    {g : X → E} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (fun x => f x • g x) := by
  intro x
  obtain ⟨K1, t1, ht1, h1⟩ := hf x
  obtain ⟨K2, t2, ht2, h2⟩ := hg x
  have hb : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x one_pos
  set s := t1 ∩ t2 ∩ Metric.ball x 1
  have hs : s ∈ nhds x := Filter.inter_mem (Filter.inter_mem ht1 ht2) hb
  have hx : x ∈ s := mem_of_mem_nhds hs
  have bf : ∀ z ∈ s, ‖f z‖ ≤ ‖f x‖ + K1 := by
    intro z hz
    have d := h1.dist_le_mul z hz.1.1 x hx.1.1
    have dz : dist z x < 1 := hz.2
    rw [dist_eq_norm] at d
    have := norm_le_insert' (f z) (f x)
    nlinarith [K1.2, norm_nonneg (f z - f x)]
  have bg : ∀ z ∈ s, ‖g z‖ ≤ ‖g x‖ + K2 := by
    intro z hz
    have d := h2.dist_le_mul z hz.1.2 x hx.1.2
    have dz : dist z x < 1 := hz.2
    rw [dist_eq_norm] at d
    have := norm_le_insert' (g z) (g x)
    nlinarith [K2.2, norm_nonneg (g z - g x)]
  refine ⟨Real.toNNReal (K1 * (‖g x‖ + K2) + (‖f x‖ + K1) * K2), s, hs,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  have hK1 := K1.2
  have hK2 := K2.2
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have e : f z • g z - f w • g w = (f z - f w) • g z + f w • (g z - g w) := by
    simp only [sub_smul, smul_sub]
    abel
  have d1 := h1.dist_le_mul z hz.1.1 w hw.1.1
  have d2 := h2.dist_le_mul z hz.1.2 w hw.1.2
  rw [dist_eq_norm] at d1 d2
  rw [e]
  have hd := dist_nonneg (x := z) (y := w)
  calc _ ≤ ‖(f z - f w) • g z‖ + ‖f w • (g z - g w)‖ := norm_add_le _ _
    _ = ‖f z - f w‖ * ‖g z‖ + ‖f w‖ * ‖g z - g w‖ := by rw [norm_smul, norm_smul]
    _ ≤ (K1 * dist z w) * (‖g x‖ + K2) + (‖f x‖ + K1) * (K2 * dist z w) :=
        add_le_add (mul_le_mul d1 (bg z hz) (norm_nonneg _) (by positivity))
          (mul_le_mul (bf w hw) d2 (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem tame_mul2 {c f : ℝ × ℝ → ℂ} (hc : ContDiff ℝ 1 c) (hcl : LocallyLipschitz (fderiv ℝ c))
    (hf : ContDiff ℝ 1 f) (hfl : LocallyLipschitz (fderiv ℝ f)) :
    Differentiable ℝ (fun p => c p * f p) ∧ LocallyLipschitz (fderiv ℝ (fun p => c p * f p)) := by
  have dc := hc.differentiable (by norm_num)
  have df := hf.differentiable (by norm_num)
  refine ⟨dc.mul df, ?_⟩
  have e : fderiv ℝ (fun p => c p * f p) = fun p => c p • fderiv ℝ f p + f p • fderiv ℝ c p :=
    funext fun p => ((dc p).hasFDerivAt.mul (df p).hasFDerivAt).fderiv
  rw [e]
  exact locSlope_add (locSlope_smul hc.locallyLipschitz hfl) (locSlope_smul hf.locallyLipschitz hcl)

theorem tame_add2 {c f : ℝ × ℝ → ℂ} (hc : Differentiable ℝ c) (hcl : LocallyLipschitz (fderiv ℝ c))
    (hf : Differentiable ℝ f) (hfl : LocallyLipschitz (fderiv ℝ f)) :
    Differentiable ℝ (fun p => c p + f p) ∧ LocallyLipschitz (fderiv ℝ (fun p => c p + f p)) := by
  refine ⟨hc.add hf, ?_⟩
  have e : fderiv ℝ (fun p => c p + f p) = fun p => fderiv ℝ c p + fderiv ℝ f p :=
    funext fun p => fderiv_add (hc p) (hf p)
  rw [e]
  exact locSlope_add hcl hfl

theorem mean_factor_one (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    ∃ H : ℝ × ℝ → ℂ, Differentiable ℝ H ∧ LocallyLipschitz (fderiv ℝ H) ∧
      ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → reducedField P D 0 β t x 1 = (((1 - t) ^ 3 : ℝ) : ℂ) * H (t, x) := by
  have hD' : IsFieldData P 0 { D with highOrder := 0 } := { hD with highOrder_eq := rfl }
  have h3 : D.highOrder = 3 := hD.highOrder_eq
  have hS := (hD.meanStream hn).1
  have cS := spline_eval_contDiff _ hS (by norm_num) (by norm_num)
  have lS := spline_eval_localSlope _ hS (by norm_num) (by norm_num)
  have cq : ContDiff ℝ 2 (fun p : ℝ × ℝ => (((3 * p.1 ^ 2 : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul (contDiff_fst.pow 2)))
  have hm := tame_mul2 (cq.of_le (by norm_num)) ((cq.fderiv_right (m := 1) (by norm_num)).locallyLipschitz) cS lS
  have ha := tame_add2 ((reducedField_mean_contDiff P hP hD' β hn 1).differentiable (by norm_num))
    (reducedField_fderiv_localSlope_mean P hP hD' β hn 1) hm.1 hm.2
  refine ⟨_, ha.1, ha.2, fun t x _ _ => ?_⟩
  have dS : HasDerivAt (fun t' => (D.amp 0).streamAmp.eval true t' x)
      (deriv (fun t' => (D.amp 0).streamAmp.eval true t' x) t) t := by
    have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact (((cS.differentiable (by norm_num)) (t, x)).hasFDerivAt.comp_hasDerivAt t hl).differentiableAt.hasDerivAt
  have w3 : HasDerivAt (fun t' : ℝ => weightPoly 1 3 t') (((1 - t) ^ 3 - 3 * t * (1 - t) ^ 2 : ℝ) : ℂ) t := by
    have h := ((hasDerivAt_pow 1 t).mul (((hasDerivAt_id t).const_sub 1).pow 3)).ofReal_comp
    unfold weightPoly
    convert h using 2 <;> simp [Pi.pow_apply, Pi.mul_apply] <;> ring
  have w0 : HasDerivAt (fun t' : ℝ => weightPoly 1 0 t') ((1 : ℝ) : ℂ) t := by
    have h := (hasDerivAt_id t).ofReal_comp
    unfold weightPoly
    convert h using 2
    simp
  have d3 : deriv (fun t' => weightPoly 1 3 t' * (D.amp 0).streamAmp.eval true t' x) t =
      (((1 - t) ^ 3 - 3 * t * (1 - t) ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t x +
        weightPoly 1 3 t * deriv (fun t' => (D.amp 0).streamAmp.eval true t' x) t := (w3.mul dS).deriv
  have d0 : deriv (fun t' => weightPoly 1 0 t' * (D.amp 0).streamAmp.eval true t' x) t =
      ((1 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t x +
        weightPoly 1 0 t * deriv (fun t' => (D.amp 0).streamAmp.eval true t' x) t := (w0.mul dS).deriv
  simp only [reducedField, ↓reduceIte, h3, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.tail_cons, twistedScale, radialScale]
  rw [d3, d0]
  unfold weightPoly
  push_cast
  ring

theorem mean_factor (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) (k : Fin 3) :
    ∃ H : ℝ × ℝ → ℂ, Differentiable ℝ H ∧ LocallyLipschitz (fderiv ℝ H) ∧
      ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → reducedField P D 0 β t x k = (((1 - t) ^ 3 : ℝ) : ℂ) * H (t, x) := by
  have hD' : IsFieldData P 0 { D with highOrder := 0 } := { hD with highOrder_eq := rfl }
  have h3 : D.highOrder = 3 := hD.highOrder_eq
  fin_cases k
  · refine ⟨fun p => reducedField P { D with highOrder := 0 } 0 β p.1 p.2 0,
      (reducedField_mean_contDiff P hP hD' β hn 0).differentiable (by norm_num),
      reducedField_fderiv_localSlope_mean P hP hD' β hn 0, fun t x _ _ => ?_⟩
    simp only [reducedField, if_pos rfl, weightPoly, h3, Matrix.cons_val_zero]
    push_cast
    ring
  · exact mean_factor_one P hP D hD β hn
  · refine ⟨fun p => reducedField P { D with highOrder := 0 } 0 β p.1 p.2 2,
      (reducedField_mean_contDiff P hP hD' β hn 2).differentiable (by norm_num),
      reducedField_fderiv_localSlope_mean P hP hD' β hn 2, fun t x _ _ => ?_⟩
    simp only [reducedField, if_pos rfl, weightPoly, h3, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    push_cast
    ring

theorem exp_unit (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

theorem logPhase_exp_far (P : ChartParams) (hP : IsChartParams P) (κ : ℝ) :
    FarDecay (fun y => Complex.exp (Complex.I * ((κ * logPhase P y : ℝ) : ℂ))) 0 := by
  have hrc : 0 < P.rc ^ 2 := by have := hP.rc_pos; positivity
  have hg0 := ((FarDecay.const (1 : ℝ)).mono (b := -2) (by norm_num)).add
    ((normSq_far.rmul (FarDecay.const (P.rc ^ 2)⁻¹)).mono (b := -2) (le_of_eq (by norm_num)))
  have eg : (fun y : Space => (1 : ℝ) + ‖y‖ ^ 2 * (P.rc ^ 2)⁻¹) = fun y => 1 + ‖y‖ ^ 2 / P.rc ^ 2 :=
    funext fun y => by rw [div_eq_mul_inv]
  rw [eg] at hg0
  have low : ∀ y : Space, 2 ≤ ‖y‖ → ∀ z ∈ Metric.ball y 1,
      1 / (4 * P.rc ^ 2) * ‖y‖ ^ (-(-2 : ℝ)) ≤ 1 + ‖z‖ ^ 2 / P.rc ^ 2 := by
    intro y hy z hz
    have h := normSq_low y hy z hz
    have e : 1 / (4 * P.rc ^ 2) * ‖y‖ ^ (-(-2 : ℝ)) = (1 / 4 * ‖y‖ ^ (-(-2 : ℝ))) / P.rc ^ 2 := by
      field_simp
    rw [e]
    have := div_le_div_of_nonneg_right h hrc.le
    have h2 : 0 ≤ ‖z‖ ^ 2 / P.rc ^ 2 := div_nonneg (sq_nonneg _) hrc.le
    linarith
  obtain ⟨R, C, hR, hC, hs⟩ := hg0.log_slope (by positivity) low
  set k : ℝ := κ / 2
  have hG : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) * (Complex.I * ((k * 1 : ℝ) : ℂ))) u := fun u =>
    ((((hasDerivAt_id' u).const_mul k).ofReal_comp).const_mul Complex.I).cexp
  have hGn : ∀ u : ℝ, ‖Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) * (Complex.I * ((k * 1 : ℝ) : ℂ))‖ = |k| := by
    intro u
    rw [norm_mul, exp_unit, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    simp
  have hfd : ∀ u : ℝ, fderiv ℝ (fun u : ℝ => Complex.exp (Complex.I * ((k * u : ℝ) : ℂ))) u =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) * (Complex.I * ((k * 1 : ℝ) : ℂ))) :=
    fun u => (hG u).hasFDerivAt.fderiv
  have hslope : ∀ u v : ℝ, ‖Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) - Complex.exp (Complex.I * ((k * v : ℝ) : ℂ))‖ ≤
      |k| * ‖u - v‖ :=
    fun u v => (convex_univ).norm_image_sub_le_of_norm_deriv_le (fun x _ => (hG x).differentiableAt)
      (fun x _ => by rw [(hG x).deriv]; exact le_of_eq (hGn x)) (Set.mem_univ v) (Set.mem_univ u)
  have h := FarDecay.comp_slope hR hC hs (G := fun u : ℝ => Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)))
    (B := 1) (M := |k|) (L := |k| * |k|) (fun u => (hG u).differentiableAt) (fun u => le_of_eq (exp_unit _))
    (fun u => by
      rw [hfd u, ContinuousLinearMap.norm_smulRight_apply, hGn u]
      exact mul_le_of_le_one_left (abs_nonneg _) (ContinuousLinearMap.norm_id_le))
    (fun u v => by
      have es : ∀ A B : ℂ, ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A - ContinuousLinearMap.smulRight 1 B =
          ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (A - B) := fun A B => by
        ext
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply, smul_sub]
        rfl
      rw [hfd u, hfd v, es, ContinuousLinearMap.norm_smulRight_apply]
      have e : Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) * (Complex.I * ((k * 1 : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((k * v : ℝ) : ℂ)) * (Complex.I * ((k * 1 : ℝ) : ℂ)) =
          (Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) - Complex.exp (Complex.I * ((k * v : ℝ) : ℂ))) *
            (Complex.I * ((k * 1 : ℝ) : ℂ)) := by ring
      rw [e, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_one]
      have h1 := hslope u v
      have h2 : ‖(1 : ℝ →L[ℝ] ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      have h3 := norm_nonneg (Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) - Complex.exp (Complex.I * ((k * v : ℝ) : ℂ)))
      have h4 := abs_nonneg k
      have h5 := norm_nonneg (1 : ℝ →L[ℝ] ℝ)
      calc ‖(1 : ℝ →L[ℝ] ℝ)‖ * (‖Complex.exp (Complex.I * ((k * u : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((k * v : ℝ) : ℂ))‖ * |k|)
          ≤ 1 * ((|k| * ‖u - v‖) * |k|) := by gcongr
        _ = |k| * |k| * ‖u - v‖ := by ring)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have e : (fun y => Complex.exp (Complex.I * ((k * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2) : ℝ) : ℂ))) =
      fun y => Complex.exp (Complex.I * ((κ * logPhase P y : ℝ) : ℂ)) := by
    funext y
    unfold logPhase
    congr 3
    ring
  rw [e] at h
  exact h

theorem FarDecay.congr_far {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Space → F} {a : ℝ}
    (h : ∀ y : Space, y ≠ 0 → f y = g y) (hf : FarDecay f a) : FarDecay g a := by
  obtain ⟨R, C, hR, hC, hf⟩ := hf
  refine ⟨R, C, hR, hC, fun y hy => ?_⟩
  obtain ⟨f1, f2⟩ := hf y hy
  have nz : ∀ z ∈ Metric.ball y 1, z ≠ 0 := by
    intro z hz h0
    have := ball_norm_ge hz
    rw [h0, norm_zero] at this
    linarith
  have ev : ∀ z ∈ Metric.ball y 1, f =ᶠ[nhds z] g := by
    intro z hz
    have hz0 : z ∈ ({0}ᶜ : Set Space) := nz z hz
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with u hu using h u hu
  have hd : ∀ z ∈ Metric.ball y 1, fderiv ℝ g z = fderiv ℝ f z := fun z hz => (ev z hz).fderiv_eq.symm
  refine ⟨fun z hz => ⟨(f1 z hz).1.congr_of_eventuallyEq (ev z hz).symm, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [← h z (nz z hz)]
    exact (f1 z hz).2.1
  · rw [hd z hz]
    exact (f1 z hz).2.2
  · rw [hd z hz, hd w hw]
    exact f2 z hz w hw

theorem angle_order0 (P : ChartParams) (hP : IsChartParams P) {e : ℕ} (D : FieldData) (hD : IsFieldData P e D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (k : Fin 3) :
    FarDecay (fun y => Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y : ℝ) : ℂ)) *
      reducedField P D n β (chartT P y) (heightRatio y) k) 0 := by
  obtain ⟨H, hH, hRH⟩ := reducedField_wave_axisFactor_slope P hP hD β n hn h0
  have hΨ : FarDecay (fun y : Space => ((y 0 / ‖y‖ : ℝ) : ℂ) + Complex.I * ((y 1 / ‖y‖ : ℝ) : ℂ)) 0 :=
    (ratio_far 0).ofReal.add (((FarDecay.const Complex.I).mul (ratio_far 1).ofReal).mono (b := 0)
      (le_of_eq (by norm_num)))
  have sq3 : ∀ z : Space, ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have hsq : ∀ z : Space, z ≠ 0 →
      ‖((z 0 / ‖z‖ : ℝ) : ℂ) + Complex.I * ((z 1 / ‖z‖ : ℝ) : ℂ)‖ ^ 2 = 1 - heightRatio z ^ 2 := by
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    rw [mul_comm Complex.I, Complex.sq_norm, Complex.normSq_add_mul_I]
    unfold heightRatio
    field_simp
    linarith [sq3 z]
  have hΨK : ∀ z : Space, 1 ≤ ‖z‖ →
      ((z 0 / ‖z‖ : ℝ) : ℂ) + Complex.I * ((z 1 / ‖z‖ : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hsq z hz0
    have h2 := sq_nonneg (heightRatio z)
    nlinarith [norm_nonneg (((z 0 / ‖z‖ : ℝ) : ℂ) + Complex.I * ((z 1 / ‖z‖ : ℝ) : ℂ))]
  have hP1 := hΨ.comp_compact (isCompact_closedBall 0 1) hΨK
    ((planePhase_contDiff (n * P.m)).differentiable (by norm_num)) (planePhase_fderiv_localSlope (n * P.m))
  have hHk := (chart_far P hP).comp_compact (isCompact_Icc.prod isCompact_Icc) (chart_mem P hP)
    ((hH k).1.differentiable (by norm_num)) (hH k).2
  have h := (hP1.mul hHk).mono (b := 0) (le_of_eq (by norm_num))
  refine h.congr_far fun y hy => ?_
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have heq : ((y 0 / ‖y‖ : ℝ) : ℂ) + Complex.I * ((y 1 / ‖y‖ : ℝ) : ℂ) =
      ((‖y‖⁻¹ : ℝ) : ℂ) * (⟨y 0, y 1⟩ : ℂ) := by
    apply Complex.ext <;> simp [div_eq_mul_inv, mul_comm]
  have harg : Complex.arg (((y 0 / ‖y‖ : ℝ) : ℂ) + Complex.I * ((y 1 / ‖y‖ : ℝ) : ℂ)) = angleOf y := by
    rw [heq, Complex.arg_real_mul _ (inv_pos.2 hr)]
    rfl
  show ((‖((y 0 / ‖y‖ : ℝ) : ℂ) + Complex.I * ((y 1 / ‖y‖ : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) *
        Complex.arg (((y 0 / ‖y‖ : ℝ) : ℂ) + Complex.I * ((y 1 / ‖y‖ : ℝ) : ℂ)) : ℝ) : ℂ)) *
      H (chartT P y) (heightRatio y) k = _
  rw [hsq y hy, harg, hRH]
  ring

theorem phased_order0 (P : ChartParams) (hP : IsChartParams P) {e : ℕ} (D : FieldData) (hD : IsFieldData P e D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (k : Fin 3) :
    FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) k) 0 := by
  have h := (logPhase_exp_far P hP ((n : ℝ) * β)).mul (angle_order0 P hP D hD β n hn h0 k)
  have e : (fun y => Complex.exp (Complex.I * ((((n : ℝ) * β) * logPhase P y : ℝ) : ℂ)) *
      (Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y : ℝ) : ℂ)) *
        reducedField P D n β (chartT P y) (heightRatio y) k)) =
      fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) k := by
    funext y
    unfold modePhase
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e] at h
  exact h.mono (b := 0) (le_of_eq (by norm_num))

theorem wave_factor01 (D : FieldData) (P : ChartParams) (h3 : D.highOrder = 3) (β : ℝ) (n : ℤ) (h0 : n ≠ 0)
    (t x : ℝ) :
    reducedField P D n β t x 0 = (((1 - t) ^ 3 : ℝ) : ℂ) * reducedField P { D with highOrder := 0 } n β t x 0 ∧
      reducedField P D n β t x 1 = (((1 - t) ^ 3 : ℝ) : ℂ) * reducedField P { D with highOrder := 0 } n β t x 1 := by
  constructor
  · simp only [reducedField, h0, ↓reduceIte, h3, Matrix.cons_val_zero, weightPoly]
    push_cast
    ring
  · simp only [reducedField, h0, ↓reduceIte, h3, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      weightPoly]
    push_cast
    ring

theorem wave_factor2 (P : ChartParams) (D : FieldData) (hD : IsFieldData P 3 D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes)
    (h0 : n ≠ 0) (t x : ℝ) :
    reducedField P D n β t x 2 = (((1 - t) ^ 3 : ℝ) : ℂ) * (reducedField P { D with highOrder := 0 } n β t x 2 +
      (-3 * (Complex.I / ((n * P.m : ℤ) : ℂ)) * (t : ℂ)) * reducedField P { D with highOrder := 0 } n β t x 0) := by
  have h3 : D.highOrder = 3 := hD.highOrder_eq
  have hR := hD.waveRadial n hn h0
  have cR := spline_eval_contDiff _ hR (by norm_num) (by norm_num)
  have dR : HasDerivAt (fun t' => (D.amp n).radialAmp.eval false t' x)
      (deriv (fun t' => (D.amp n).radialAmp.eval false t' x) t) t := by
    have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact (((cR.differentiable (by norm_num)) (t, x)).hasFDerivAt.comp_hasDerivAt t hl).differentiableAt.hasDerivAt
  have wa3 : HasDerivAt (fun t' : ℝ => weightPoly (D.lowOrder n) 3 t')
      (((D.lowOrder n * t ^ (D.lowOrder n - 1) * (1 - t) ^ 3 - 3 * t ^ (D.lowOrder n) * (1 - t) ^ 2 : ℝ)) : ℂ) t := by
    have h := ((hasDerivAt_pow (D.lowOrder n) t).mul (((hasDerivAt_id t).const_sub 1).pow 3)).ofReal_comp
    unfold weightPoly
    convert h using 2 <;> simp [Pi.pow_apply, Pi.mul_apply] <;> ring
  have wa0 : HasDerivAt (fun t' : ℝ => weightPoly (D.lowOrder n) 0 t')
      (((D.lowOrder n * t ^ (D.lowOrder n - 1) : ℝ)) : ℂ) t := by
    have h := (hasDerivAt_pow (D.lowOrder n) t).ofReal_comp
    unfold weightPoly
    convert h using 2 <;> simp
  have d3 : deriv (fun t' => weightPoly (D.lowOrder n) 3 t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x) t =
      (((D.lowOrder n * t ^ (D.lowOrder n - 1) * (1 - t) ^ 3 - 3 * t ^ (D.lowOrder n) * (1 - t) ^ 2 : ℝ)) : ℂ) * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t x +
      weightPoly (D.lowOrder n) 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * deriv (fun t' => (D.amp n).radialAmp.eval false t' x) t :=
    ((wa3.mul_const (((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n)).mul dR).deriv
  have d0 : deriv (fun t' => weightPoly (D.lowOrder n) 0 t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x) t =
      (((D.lowOrder n * t ^ (D.lowOrder n - 1) : ℝ)) : ℂ) * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t x +
      weightPoly (D.lowOrder n) 0 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * deriv (fun t' => (D.amp n).radialAmp.eval false t' x) t :=
    ((wa0.mul_const (((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n)).mul dR).deriv
  have hx : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) 3 t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x =
      (((1 - t) ^ 3 : ℝ) : ℂ) * heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) 0 t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x := by
    unfold heightDeriv
    rw [← deriv_const_mul_field]
    congr 1
    funext x'
    unfold weightPoly
    push_cast
    ring
  simp only [reducedField, h0, ↓reduceIte, h3, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.tail_cons,
    Matrix.head_cons, twistedScale, radialScale]
  rw [d3, d0, hx]
  unfold weightPoly
  push_cast
  ring

theorem phased_far_wave (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (k : Fin 3) :
    FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) k) 3 := by
  have hD' : IsFieldData P 0 { D with highOrder := 0 } := { hD with highOrder_eq := rfl }
  have h3 : D.highOrder = 3 := hD.highOrder_eq
  have L := fun j => phased_order0 P hP { D with highOrder := 0 } hD' β n hn h0 j
  have hs3 := (((chartS_far P hP).rmul (chartS_far P hP)).rmul (chartS_far P hP)).ofReal
  have cs : ∀ y : Space, (((1 - chartT P y) ^ 3 : ℝ) : ℂ) = ((chartS P y * chartS P y * chartS P y : ℝ) : ℂ) := by
    intro y
    unfold chartS
    push_cast
    ring
  fin_cases k
  · have h := hs3.mul (L 0)
    have e : (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 0) =
        fun y => ((chartS P y * chartS P y * chartS P y : ℝ) : ℂ) *
          (modePhase P n β y * reducedField P { D with highOrder := 0 } n β (chartT P y) (heightRatio y) 0) := by
      funext y
      rw [(wave_factor01 D P h3 β n h0 _ _).1, cs]
      ring
    show FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 0) 3
    rw [e]
    exact h.mono (b := 3) (le_of_eq (by norm_num))
  · have h := hs3.mul (L 1)
    have e : (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 1) =
        fun y => ((chartS P y * chartS P y * chartS P y : ℝ) : ℂ) *
          (modePhase P n β y * reducedField P { D with highOrder := 0 } n β (chartT P y) (heightRatio y) 1) := by
      funext y
      rw [(wave_factor01 D P h3 β n h0 _ _).2, cs]
      ring
    show FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 1) 3
    rw [e]
    exact h.mono (b := 3) (le_of_eq (by norm_num))
  · have hb := (L 2).add (((FarDecay.const (-3 * (Complex.I / ((n * P.m : ℤ) : ℂ)))).mul
      ((chartT_far P hP).ofReal.mul (L 0))).mono (b := 0) (le_of_eq (by norm_num)))
    have h := hs3.mul hb
    have e : (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 2) =
        fun y => ((chartS P y * chartS P y * chartS P y : ℝ) : ℂ) *
          (modePhase P n β y * reducedField P { D with highOrder := 0 } n β (chartT P y) (heightRatio y) 2 +
            (-3 * (Complex.I / ((n * P.m : ℤ) : ℂ))) * ((chartT P y : ℂ) *
              (modePhase P n β y * reducedField P { D with highOrder := 0 } n β (chartT P y) (heightRatio y) 0))) := by
      funext y
      rw [wave_factor2 P D hD β n hn h0, cs]
      ring
    show FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 2) 3
    rw [e]
    exact h.mono (b := 3) (le_of_eq (by norm_num))

theorem phased_far (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (k : Fin 3) :
    FarDecay (fun y => modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) k) 3 := by
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨H, hHd, hHl, hHe⟩ := mean_factor P hP D hD β hn k
    have hc := (chart_far P hP).comp_compact (isCompact_Icc.prod isCompact_Icc) (chart_mem P hP) hHd hHl
    have hs3 := (((chartS_far P hP).rmul (chartS_far P hP)).rmul (chartS_far P hP)).ofReal
    have h := hs3.mul hc
    have e : (fun y => modePhase P 0 β y * reducedField P D 0 β (chartT P y) (heightRatio y) k) =
        fun y => ((chartS P y * chartS P y * chartS P y : ℝ) : ℂ) * H (chartT P y, heightRatio y) := by
      funext y
      have ht := chart_mem P hP y
      have hph : modePhase P 0 β y = 1 := by simp [modePhase]
      by_cases hy : 1 ≤ ‖y‖
      · have ht := (chart_mem P hP y hy).1
        rw [hHe _ _ ht.1 ht.2, hph, one_mul]
        congr 1
        unfold chartS
        push_cast
        ring
      · have ht0 : 0 ≤ chartT P y := div_nonneg (norm_nonneg _) (by linarith [norm_nonneg y, hP.L0_pos])
        have ht1 : chartT P y ≤ 1 := by
          unfold chartT
          rw [div_le_one (by linarith [norm_nonneg y, hP.L0_pos])]
          linarith [hP.L0_pos]
        rw [hHe _ _ ht0 ht1, hph, one_mul]
        congr 1
        unfold chartS
        push_cast
        ring
    rw [e]
    exact h.mono (b := 3) (le_of_eq (by norm_num))
  · exact phased_far_wave P hP D hD β n hn h0 k

end FarDecayInternal

end Breakdown

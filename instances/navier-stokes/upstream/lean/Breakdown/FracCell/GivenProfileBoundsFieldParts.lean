import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenProfileFarModeBounds

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracCellInternal

open CellCert.GivenFields

def splineScale (c : ℂ) (S : Spline) : Spline := ⟨S.mesh, fun i j => MvPolynomial.C c * S.piece i j⟩

def ampScale (c : ℂ) (A : ModeAmp) : ModeAmp :=
  ⟨splineScale c A.radialAmp, splineScale c A.polarAmp, splineScale c A.streamAmp, splineScale c A.swirlAmp⟩

def quarterTurnData (D : FieldData) (n : ℤ) : FieldData :=
  { D with amp := fun k => if k = n then ampScale (-Complex.I) (D.amp k)
      else if k = -n then ampScale Complex.I (D.amp k) else D.amp k }

theorem splineScale_eval (c : ℂ) (S : Spline) (odd : Bool) (t x : ℝ) :
    (splineScale c S).eval odd t x = c * S.eval odd t x := by
  simp only [Spline.eval, Spline.evalHalf, splineScale, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  ring

private theorem twisted_const_mul (P : ChartParams) (n : ℤ) (β : ℝ) (c : ℂ) (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    twistedScale P n β (fun t' x' => c * f t' x') t x = c * twistedScale P n β f t x := by
  unfold twistedScale radialScale
  rw [deriv_const_mul_field']
  ring

private theorem height_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    heightDeriv (fun t' x' => c * f t' x') t x = c * heightDeriv f t x := by
  unfold heightDeriv
  rw [deriv_const_mul_field']

private theorem reduced_quarter (P : ChartParams) (D : FieldData) (n : ℤ) (hn : n ≠ 0) (β t x : ℝ)
    (k : Fin 3) : reducedField P (quarterTurnData D n) n β t x k = -Complex.I * reducedField P D n β t x k := by
  have hamp : (quarterTurnData D n).amp n = ampScale (-Complex.I) (D.amp n) := by
    simp [quarterTurnData]
  have hr : ∀ t' x', weightPoly ((quarterTurnData D n).lowOrder n) (quarterTurnData D n).highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ (quarterTurnData D n).axisOrder n *
        ((quarterTurnData D n).amp n).radialAmp.eval false t' x' =
      -Complex.I * (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x') := by
    intro t' x'
    rw [hamp]
    simp only [ampScale, splineScale_eval, quarterTurnData]
    ring
  have hp : ∀ t' x', ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly ((quarterTurnData D n).lowOrder n) (quarterTurnData D n).highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ (quarterTurnData D n).axisOrder n *
        ((quarterTurnData D n).amp n).polarAmp.eval true t' x') =
      -Complex.I * (((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t' x')) := by
    intro t' x'
    rw [hamp]
    simp only [ampScale, splineScale_eval, quarterTurnData]
    ring
  unfold reducedField
  simp only [hn, if_false]
  fin_cases k
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    exact hr t x
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hamp]
    simp only [ampScale, splineScale_eval, quarterTurnData]
    ring
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [show (fun t' x' => weightPoly ((quarterTurnData D n).lowOrder n) (quarterTurnData D n).highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ (quarterTurnData D n).axisOrder n *
        ((quarterTurnData D n).amp n).radialAmp.eval false t' x') = fun t' x' => -Complex.I * (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x') from funext fun t' => funext fun x' => hr t' x']
    rw [show (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly ((quarterTurnData D n).lowOrder n) (quarterTurnData D n).highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ (quarterTurnData D n).axisOrder n *
        ((quarterTurnData D n).amp n).polarAmp.eval true t' x')) = fun t' x' => -Complex.I * (((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t' x')) from funext fun t' => funext fun x' => hp t' x']
    rw [twisted_const_mul, height_const_mul, hr t x]
    ring

private theorem reduced_affine (P : ChartParams) (D : FieldData) (n : ℤ) (β t x : ℝ) (k : Fin 3) :
    reducedField P D n β t x k =
      ((1 - β : ℝ) : ℂ) * reducedField P D n 0 t x k + (β : ℂ) * reducedField P D n 1 t x k := by
  unfold reducedField twistedScale
  by_cases hn : n = 0
  · subst hn
    fin_cases k <;> simp <;> ring
  · simp only [hn, if_false]
    fin_cases k <;> simp <;> ring

private theorem phase_split (P : ChartParams) (n : ℤ) (β c : ℝ) (y : Space) :
    modePhase P n β y = modePhase P n c y * Complex.exp (Complex.I * (((n : ℝ) * (β - c) * logPhase P y : ℝ) : ℂ)) := by
  unfold modePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem re_rot (a : ℝ) (z : ℂ) :
    (Complex.exp (Complex.I * (a : ℂ)) * z).re = Real.cos a * z.re - Real.sin a * z.im := by
  rw [show Complex.I * (a : ℂ) = (a : ℂ) * Complex.I by ring, Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]


private theorem combo_re (d ph ph0 ph1 ea eb s s0 s1 : ℂ) (β : ℝ) (h0 : ph = ph0 * ea) (h1 : ph = ph1 * eb)
    (hs : s = ((1 - β : ℝ) : ℂ) * s0 + (β : ℂ) * s1) :
    (d * (ph * s)).re = (1 - β) * (ea * (d * (ph0 * s0))).re + β * (eb * (d * (ph1 * s1))).re := by
  have h : d * (ph * s) = ((1 - β : ℝ) : ℂ) * (ea * (d * (ph0 * s0))) + (β : ℂ) * (eb * (d * (ph1 * s1))) := by
    rw [hs]
    linear_combination (((1 - β : ℝ) : ℂ) * d * s0) * h0 + ((β : ℂ) * d * s1) * h1
  rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem mode_phase_identity (P : ChartParams) (D : FieldData) (n : ℤ) (hn : n ≠ 0) (β : ℝ) (y : Space) :
    modeFieldOf P D β n y =
      (1 - β) • (Real.cos ((n : ℝ) * β * logPhase P y) • modeFieldOf P D 0 n y -
          Real.sin ((n : ℝ) * β * logPhase P y) • modeFieldOf P (quarterTurnData D n) 0 n y) +
        β • (Real.cos ((n : ℝ) * (β - 1) * logPhase P y) • modeFieldOf P D 1 n y -
          Real.sin ((n : ℝ) * (β - 1) * logPhase P y) • modeFieldOf P (quarterTurnData D n) 1 n y) := by
  ext i
  have hU : ∀ c : ℝ, (modeFieldOf P D c n y) i = ((decayFactor P y : ℂ) * (modePhase P n c y *
      (reducedField P D n c (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n c (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n c (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re := by
    intro c
    simp only [modeFieldOf, FracInternal.ofComponents_apply]
  have hq : ∀ c : ℝ, (modeFieldOf P (quarterTurnData D n) c n y) i = ((decayFactor P y : ℂ) * (modePhase P n c y *
      (reducedField P D n c (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n c (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n c (chartT P y) (heightRatio y) 2 * azimVecQ y i))).im := by
    intro c
    simp only [modeFieldOf, FracInternal.ofComponents_apply, reduced_quarter P D n hn]
    rw [show ∀ a b e u v w d ph : ℂ, d * (ph * (-Complex.I * a * u + -Complex.I * b * v + -Complex.I * e * w)) =
      -Complex.I * (d * (ph * (a * u + b * v + e * w))) from fun _ _ _ _ _ _ _ _ => by ring]
    simp [Complex.mul_re]
  have hs : reducedField P D n β (chartT P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ) =
      ((1 - β : ℝ) : ℂ) * (reducedField P D n 0 (chartT P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
        reducedField P D n 0 (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
        reducedField P D n 0 (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ)) +
      (β : ℂ) * (reducedField P D n 1 (chartT P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
        reducedField P D n 1 (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
        reducedField P D n 1 (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ)) := by
    rw [reduced_affine P D n β _ _ 0, reduced_affine P D n β _ _ 1, reduced_affine P D n β _ _ 2]
    ring
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hU, hq]
  rw [combo_re _ _ _ _ _ _ _ _ _ β (phase_split P n β 0 y) (phase_split P n β 1 y) hs, re_rot, re_rot, sub_zero]

private theorem locSlope_bilin {X E F G : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : X → E} {h : X → F} (hf : LocallyLipschitz f) (hh : LocallyLipschitz h) :
    LocallyLipschitz (fun x => B (f x) (h x)) := by
  intro x
  obtain ⟨K1, t1, ht1, hf1⟩ := hf x
  obtain ⟨K2, t2, ht2, hh2⟩ := hh x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht1 ht2)
  have hf' : LipschitzOnWith K1 f (Metric.ball x r) := hf1.mono fun z hz => (hrt hz).1
  have hh' : LipschitzOnWith K2 h (Metric.ball x r) := hh2.mono fun z hz => (hrt hz).2
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  set M1 : ℝ := ‖f x‖ + K1 * r
  set M2 : ℝ := ‖h x‖ + K2 * r
  have hb1 : ∀ z ∈ Metric.ball x r, ‖f z‖ ≤ M1 := by
    intro z hz
    have h1 := hf'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖f z‖ ≤ ‖f x‖ + dist (f z) (f x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (f z) (f x)
      linarith [norm_sub_rev (f z) (f x)]
    nlinarith [K1.2]
  have hb2 : ∀ z ∈ Metric.ball x r, ‖h z‖ ≤ M2 := by
    intro z hz
    have h1 := hh'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖h z‖ ≤ ‖h x‖ + dist (h z) (h x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (h z) (h x)
      linarith [norm_sub_rev (h z) (h x)]
    nlinarith [K2.2]
  have hM1 : 0 ≤ M1 := le_trans (norm_nonneg _) (hb1 x hx)
  have hM2 : 0 ≤ M2 := le_trans (norm_nonneg _) (hb2 x hx)
  refine ⟨Real.toNNReal (‖B‖ * (K1 * M2 + M1 * K2)), Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hsplit : B (f a) (h a) - B (f b) (h b) = B (f a - f b) (h a) + B (f b) (h a - h b) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  have e1 : ‖B (f a - f b) (h a)‖ ≤ ‖B‖ * ‖f a - f b‖ * ‖h a‖ := B.le_opNorm₂ _ _
  have e2 : ‖B (f b) (h a - h b)‖ ≤ ‖B‖ * ‖f b‖ * ‖h a - h b‖ := B.le_opNorm₂ _ _
  have d1 : ‖f a - f b‖ ≤ K1 * dist a b := by rw [← dist_eq_norm]; exact hf'.dist_le_mul a ha b hb
  have d2 : ‖h a - h b‖ ≤ K2 * dist a b := by rw [← dist_eq_norm]; exact hh'.dist_le_mul a ha b hb
  have n1 := hb2 a ha
  have n2 := hb1 b hb
  have hB := norm_nonneg B
  calc ‖B (f a - f b) (h a) + B (f b) (h a - h b)‖ ≤ ‖B (f a - f b) (h a)‖ + ‖B (f b) (h a - h b)‖ :=
        norm_add_le _ _
    _ ≤ ‖B‖ * (K1 * dist a b) * M2 + ‖B‖ * M1 * (K2 * dist a b) := by
        gcongr
        · exact e1.trans (by gcongr)
        · exact e2.trans (by gcongr)
    _ = ‖B‖ * (K1 * M2 + M1 * K2) * dist a b := by ring

private theorem term_fderiv (g : ℝ × Space → ℝ) (W : Space → Space) (hg : ContDiff ℝ 2 g)
    (hW : ContDiff ℝ 1 W) (β : ℝ) (y : Space) :
    HasFDerivAt (fun z => g (β, z) • W z)
      (g (β, y) • fderiv ℝ W y + ((fderiv ℝ g (β, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)).smulRight (W y)) y := by
  have hg1 : HasFDerivAt (fun z : Space => g (β, z))
      ((fderiv ℝ g (β, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    ((hg.differentiable (by norm_num)) (β, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right β y)
  have hW1 : HasFDerivAt W (fderiv ℝ W y) y := ((hW.differentiable (by norm_num)) y).hasFDerivAt
  exact hg1.smul hW1

private theorem term_locSlope (g : ℝ × Space → ℝ) (W : Space → Space) (hg : ContDiff ℝ 2 g)
    (hW : ContDiff ℝ 1 W) (hDW : LocallyLipschitz (fderiv ℝ W)) :
    LocallyLipschitz (fun q : ℝ × Space => g q • fderiv ℝ W q.2 +
      ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ ℝ Space)).smulRight (W q.2)) := by
  have hsnd : LocallyLipschitz (fun q : ℝ × Space => q.2) := LipschitzWith.prod_snd.locallyLipschitz
  have h1 : LocallyLipschitz g := (hg.of_le (by norm_num)).locallyLipschitz
  have h2 : LocallyLipschitz (fun q : ℝ × Space => fderiv ℝ W q.2) := hDW.comp hsnd
  have h3 : LocallyLipschitz (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by norm_num)).locallyLipschitz
  have h4 : LocallyLipschitz (fun q : ℝ × Space => W q.2) := hW.locallyLipschitz.comp hsnd
  have hinr : LocallyLipschitz (fun _ : ℝ × Space => ContinuousLinearMap.inr ℝ ℝ Space) :=
    (LipschitzWith.const _).locallyLipschitz
  have h5 := locSlope_bilin (ContinuousLinearMap.compL ℝ Space (ℝ × Space) ℝ) h3 hinr
  have h6 := locSlope_bilin (ContinuousLinearMap.lsmul ℝ ℝ) h1 h2
  have h7 := locSlope_bilin (ContinuousLinearMap.smulRightL ℝ Space Space) h5 h4
  simpa [ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.compL_apply] using h6.add h7

private theorem four_locSlope (g : Fin 4 → ℝ × Space → ℝ) (W : Fin 4 → Space → Space)
    (hg : ∀ j, ContDiff ℝ 2 (g j)) (hW : ∀ j, ContDiff ℝ 1 (W j)) (hDW : ∀ j, LocallyLipschitz (fderiv ℝ (W j))) :
    LocallyLipschitz (fun q : ℝ × Space => fderiv ℝ (fun z => ∑ j, g j (q.1, z) • W j z) q.2) := by
  have heq : (fun q : ℝ × Space => fderiv ℝ (fun z => ∑ j, g j (q.1, z) • W j z) q.2) = fun q =>
      ∑ j, (g j q • fderiv ℝ (W j) q.2 +
        ((fderiv ℝ (g j) q).comp (ContinuousLinearMap.inr ℝ ℝ Space)).smulRight (W j q.2)) := by
    funext q
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => term_fderiv (g j) (W j) (hg j) (hW j) q.1 q.2).fderiv
  rw [heq]
  simp only [Fin.sum_univ_four]
  exact (((term_locSlope _ _ (hg 0) (hW 0) (hDW 0)).add (term_locSlope _ _ (hg 1) (hW 1) (hDW 1))).add
    (term_locSlope _ _ (hg 2) (hW 2) (hDW 2))).add (term_locSlope _ _ (hg 3) (hW 3) (hDW 3))

private theorem logPhase_smooth (P : ChartParams) : ContDiff ℝ 2 (logPhase P) := by
  show ContDiff ℝ 2 (fun y : Space => (1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2))
  refine contDiff_const.mul ((contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)).log fun y => ?_)
  positivity

def waveCoef (P : ChartParams) (n : ℤ) : Fin 4 → ℝ × Space → ℝ :=
  ![fun q => (1 - q.1) * Real.cos ((n : ℝ) * q.1 * logPhase P q.2),
    fun q => -((1 - q.1) * Real.sin ((n : ℝ) * q.1 * logPhase P q.2)),
    fun q => q.1 * Real.cos ((n : ℝ) * (q.1 - 1) * logPhase P q.2),
    fun q => -(q.1 * Real.sin ((n : ℝ) * (q.1 - 1) * logPhase P q.2))]

def waveParts (P : ChartParams) (F : FieldData) (n : ℤ) : Fin 4 → Space → Space :=
  ![modeFieldOf P F 0 n, modeFieldOf P (quarterTurnData F n) 0 n,
    modeFieldOf P F 1 n, modeFieldOf P (quarterTurnData F n) 1 n]

private theorem mode_eq_parts (P : ChartParams) (F : FieldData) (n : ℤ) (h0 : n ≠ 0) (β : ℝ) :
    modeFieldOf P F β n = fun z => ∑ j, waveCoef P n j (β, z) • waveParts P F n j z := by
  funext z
  rw [mode_phase_identity P F n h0 β z]
  simp only [Fin.sum_univ_four, waveCoef, waveParts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  module

private theorem waveCoef_smooth (P : ChartParams) (n : ℤ) (j : Fin 4) : ContDiff ℝ 2 (waveCoef P n j) := by
  have hL := logPhase_smooth P
  fin_cases j <;> simp only [waveCoef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

private theorem waveParts_of (P : ChartParams) (F : FieldData) (n : ℤ) {Q : (Space → Space) → Prop}
    (h : ∀ c : ℝ, Q (modeFieldOf P F c n) ∧ Q (modeFieldOf P (quarterTurnData F n) c n)) (j : Fin 4) :
    Q (waveParts P F n j) := by
  fin_cases j
  · exact (h 0).1
  · exact (h 0).2
  · exact (h 1).1
  · exact (h 1).2

private theorem wave_joint_of (P : ChartParams) (F : FieldData) (n : ℤ) (h0 : n ≠ 0)
    (hW : ∀ c : ℝ, ContDiff ℝ 1 (modeFieldOf P F c n) ∧ ContDiff ℝ 1 (modeFieldOf P (quarterTurnData F n) c n))
    (hDW : ∀ c : ℝ, LocallyLipschitz (fderiv ℝ (modeFieldOf P F c n)) ∧
      LocallyLipschitz (fderiv ℝ (modeFieldOf P (quarterTurnData F n) c n))) :
    LocallyLipschitz (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 n) q.2) := by
  have heq : (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 n) q.2) =
      fun q => fderiv ℝ (fun z => ∑ j, waveCoef P n j (q.1, z) • waveParts P F n j z) q.2 := by
    funext q
    rw [mode_eq_parts P F n h0 q.1]
  rw [heq]
  exact four_locSlope _ _ (waveCoef_smooth P n) (waveParts_of P F n hW)
    (waveParts_of (Q := fun f => LocallyLipschitz (fderiv ℝ f)) P F n hDW)

private theorem mode_phase_hasDerivAt (P : ChartParams) (F : FieldData) (n : ℤ) (h0 : n ≠ 0) (β₀ : ℝ)
    (y : Space) : HasDerivAt (fun β => modeFieldOf P F β n y)
      (∑ j, (fderiv ℝ (waveCoef P n j) (β₀, y) ((1 : ℝ), (0 : Space))) • waveParts P F n j y) β₀ := by
  have he : (fun β => modeFieldOf P F β n y) = fun β => ∑ j, waveCoef P n j (β, y) • waveParts P F n j y := by
    funext β
    rw [mode_eq_parts P F n h0 β]
  rw [he]
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.smul_const ?_ _
  have hc : HasDerivAt (fun β : ℝ => ((β, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) β₀ :=
    (hasDerivAt_id β₀).prodMk (hasDerivAt_const β₀ y)
  exact (((waveCoef_smooth P n j).differentiable (by norm_num)) (β₀, y)).hasFDerivAt.comp_hasDerivAt β₀ hc

private theorem ofComponents_finsum (s : Finset ℤ) (w : ℤ → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ n ∈ s, w n i) = ∑ n ∈ s, ofComponents (w n) := by
  ext j
  fin_cases j <;> simp [ofComponents]

private theorem fieldOf_eq_modeSum (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, modeFieldOf P D β n y := by
  funext y
  unfold fieldOf modeFieldOf
  rw [← ofComponents_finsum]
  congr 1
  funext i
  rw [Finset.mul_sum, Complex.re_sum]

private theorem mode_zero_indep (P : ChartParams) (D : FieldData) (β : ℝ) :
    modeFieldOf P D β 0 = modeFieldOf P D 0 0 := by
  funext y
  simp [modeFieldOf, modePhase, reducedField, twistedScale]

def phaseTerm (P : ChartParams) (F : FieldData) (β₀ : ℝ) (n : ℤ) (y : Space) : Space :=
  if n = 0 then 0 else ∑ j, (fderiv ℝ (waveCoef P n j) (β₀, y) ((1 : ℝ), (0 : Space))) • waveParts P F n j y

private theorem phaseDeriv_eq (P : ChartParams) (F : FieldData) (β₀ : ℝ) (y : Space) :
    deriv (fun β => fieldOf P F β y) β₀ = ∑ n ∈ F.modes, phaseTerm P F β₀ n y := by
  have hm : ∀ n ∈ F.modes, HasDerivAt (fun β => modeFieldOf P F β n y) (phaseTerm P F β₀ n y) β₀ := by
    intro n _
    by_cases h0 : n = 0
    · subst h0
      simp only [phaseTerm, if_true]
      have : (fun β => modeFieldOf P F β 0 y) = fun _ => modeFieldOf P F 0 0 y := by
        funext β
        rw [mode_zero_indep P F β]
      rw [this]
      exact hasDerivAt_const _ _
    · simp only [phaseTerm, h0, if_false]
      exact mode_phase_hasDerivAt P F n h0 β₀ y
  have he : (fun β => fieldOf P F β y) = fun β => ∑ n ∈ F.modes, modeFieldOf P F β n y := by
    funext β
    rw [fieldOf_eq_modeSum P F β]
  rw [he]
  exact (HasDerivAt.fun_sum hm).deriv

private theorem phaseDeriv_contDiff_of (P : ChartParams) (F : FieldData) (β₀ : ℝ)
    (hW : ∀ n ∈ F.modes, n ≠ 0 → ∀ c : ℝ, ContDiff ℝ 1 (modeFieldOf P F c n) ∧
      ContDiff ℝ 1 (modeFieldOf P (quarterTurnData F n) c n)) :
    ContDiff ℝ 1 (fun y => deriv (fun β => fieldOf P F β y) β₀) := by
  have he : (fun y => deriv (fun β => fieldOf P F β y) β₀) = fun y => ∑ n ∈ F.modes, phaseTerm P F β₀ n y := by
    funext y
    exact phaseDeriv_eq P F β₀ y
  rw [he]
  refine ContDiff.sum fun n hn => ?_
  by_cases h0 : n = 0
  · simp only [phaseTerm, h0, if_true]
    exact contDiff_const
  · simp only [phaseTerm, h0, if_false]
    refine ContDiff.sum fun j _ => ?_
    have h1 : ContDiff ℝ 1 (fderiv ℝ (waveCoef P n j)) :=
      (waveCoef_smooth P n j).fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun y : Space => ((β₀, y) : ℝ × Space)) := contDiff_const.prodMk contDiff_id
    have h3 : ContDiff ℝ 1 (fun y : Space => (fderiv ℝ (waveCoef P n j) (β₀, y)) ((1 : ℝ), (0 : Space))) :=
      (h1.comp h2).clm_apply contDiff_const
    exact h3.smul (waveParts_of (Q := fun f => ContDiff ℝ 1 f) P F n (hW n hn h0) j)

private theorem tDeriv_C_mul (c : ℂ) (o : ℕ) (p : MvPolynomial (Fin 2) ℂ) :
    tDeriv o (MvPolynomial.C c * p) = MvPolynomial.C c * tDeriv o p := by
  unfold tDeriv
  induction o with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, MvPolynomial.pderiv_C_mul]

private theorem xDeriv_C_mul (c : ℂ) (o : ℕ) (p : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.C c * p) = MvPolynomial.C c * xDeriv o p := by
  unfold xDeriv
  induction o with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, MvPolynomial.pderiv_C_mul]

private theorem atFirst_C_mul (v c : ℂ) (p : MvPolynomial (Fin 2) ℂ) :
    atFirst v (MvPolynomial.C c * p) = MvPolynomial.C c * atFirst v p := by
  simp [atFirst, map_mul]

private theorem atSecond_C_mul (v c : ℂ) (p : MvPolynomial (Fin 2) ℂ) :
    atSecond v (MvPolynomial.C c * p) = MvPolynomial.C c * atSecond v p := by
  simp [atSecond, map_mul]

private theorem splineScale_class {a b : ℕ} {odd : Bool} {S : Spline} (c : ℂ) (hS : IsSplineClass a b odd S) :
    IsSplineClass a b odd (splineScale c S) where
  mesh := hS.mesh
  t_joins := by
    intro i hi1 hi2 j hj o ho
    simp only [splineScale, tDeriv_C_mul, atFirst_C_mul]
    rw [hS.t_joins i hi1 hi2 j hj o ho]
  x_joins := by
    intro j hj1 hj2 i hi o ho
    simp only [splineScale, xDeriv_C_mul, atSecond_C_mul]
    rw [hS.x_joins j hj1 hj2 i hi o ho]
  parity := by
    intro i hi o ho hpar
    simp only [splineScale, xDeriv_C_mul, atSecond_C_mul]
    rw [hS.parity i hi o ho hpar, mul_zero]

private theorem splineScale_conj (c : ℂ) (S : Spline) :
    (splineScale c S).conj = splineScale ((starRingEnd ℂ) c) S.conj := by
  simp [Spline.conj, splineScale, map_mul, MvPolynomial.map_C]

private theorem ampScale_conj (c : ℂ) (A : ModeAmp) :
    (ampScale c A).conj = ampScale ((starRingEnd ℂ) c) A.conj := by
  simp only [ModeAmp.conj, ampScale, splineScale_conj]

private theorem quarter_amp_cases (F : FieldData) (n k : ℤ) :
    (quarterTurnData F n).amp k = F.amp k ∨ ∃ c, (quarterTurnData F n).amp k = ampScale c (F.amp k) := by
  simp only [quarterTurnData]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

private theorem quarter_amp_zero (F : FieldData) (n : ℤ) (h0 : n ≠ 0) :
    (quarterTurnData F n).amp 0 = F.amp 0 := by
  have h1 : (0 : ℤ) ≠ n := Ne.symm h0
  have h2 : (0 : ℤ) ≠ -n := by omega
  simp [quarterTurnData, h1, h2]

private theorem spline_conj_conj (S : Spline) : S.conj.conj = S := by
  cases S
  simp [Spline.conj, MvPolynomial.map_map, MvPolynomial.map_id]

private theorem amp_conj_conj (A : ModeAmp) : A.conj.conj = A := by
  cases A
  simp [ModeAmp.conj, spline_conj_conj]

theorem quarterTurnData_isFieldData (P : ChartParams) (F : FieldData) (hF : IsFieldData P 1 F) (n : ℤ)
    (h0 : n ≠ 0) : IsFieldData P 1 (quarterTurnData F n) where
  modes_symm := hF.modes_symm
  amp_conj := by
    intro k hk
    have hnn : n ≠ -n := by omega
    by_cases hkn : k = n
    · subst hkn
      have e1 : (quarterTurnData F k).amp (-k) = ampScale Complex.I (F.amp (-k)) := by
        simp [quarterTurnData, Ne.symm hnn]
      have e2 : (quarterTurnData F k).amp k = ampScale (-Complex.I) (F.amp k) := by
        simp [quarterTurnData]
      rw [e1, e2, ampScale_conj, hF.amp_conj k hk]
      simp
    · by_cases hkm : k = -n
      · subst hkm
        have hm : n ∈ F.modes := by simpa using (hF.modes_symm (-n)).1 hk
        have e1 : (quarterTurnData F n).amp (-(-n)) = ampScale (-Complex.I) (F.amp n) := by
          simp [quarterTurnData]
        have e2 : (quarterTurnData F n).amp (-n) = ampScale Complex.I (F.amp (-n)) := by
          simp [quarterTurnData, Ne.symm hnn]
        rw [e1, e2, ampScale_conj, hF.amp_conj n hm]
        rw [amp_conj_conj]
        simp
      · have e1 : (quarterTurnData F n).amp (-k) = F.amp (-k) := by
          have a1 : -k ≠ n := fun h => hkm (by omega)
          have a2 : -k ≠ -n := fun h => hkn (by omega)
          simp [quarterTurnData, a1, a2]
        have e2 : (quarterTurnData F n).amp k = F.amp k := by
          simp [quarterTurnData, hkn, hkm]
        rw [e1, e2, hF.amp_conj k hk]
  waveRadial := by
    intro k hk hk0
    rcases quarter_amp_cases F n k with h | ⟨c, h⟩ <;> rw [h]
    · exact hF.waveRadial k hk hk0
    · exact splineScale_class c (hF.waveRadial k hk hk0)
  wavePolar := by
    intro k hk hk0
    rcases quarter_amp_cases F n k with h | ⟨c, h⟩ <;> rw [h]
    · exact hF.wavePolar k hk hk0
    · exact splineScale_class c (hF.wavePolar k hk hk0)
  meanStream := by
    intro h
    rw [quarter_amp_zero F n h0]
    exact hF.meanStream h
  meanSwirl := by
    intro h
    rw [quarter_amp_zero F n h0]
    exact hF.meanSwirl h
  guard_stream := by
    intro h
    rw [quarter_amp_zero F n h0]
    exact hF.guard_stream h
  guard_swirl := by
    intro h
    rw [quarter_amp_zero F n h0]
    exact hF.guard_swirl h
  lowOrder_ge := hF.lowOrder_ge
  axisOrder_ge := hF.axisOrder_ge
  orders_conj := hF.orders_conj
  highOrder_eq := hF.highOrder_eq

theorem fieldOf_differentiable (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) : Differentiable ℝ (fieldOf P F β) :=
  (FracInternal.fieldOf_contDiff hP hF β).differentiable (by norm_num)

theorem fieldOf_div_ae (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), divergenceAt (fieldOf P F β) y = 0 :=
  FracInternal.fieldOf_divergence_ae hP hF β

private theorem ofComponents_sum_form (w : Fin 3 → ℝ) :
    ofComponents w = ∑ i : Fin 3, w i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [ofComponents, Fin.sum_univ_three]

private theorem reducedField_phase_continuous (P : ChartParams) (F : FieldData) (n : ℤ) (t x : ℝ)
    (c : Fin 3) : Continuous (fun β : ℝ => reducedField P F n β t x c) := by
  unfold reducedField twistedScale
  by_cases hn : n = 0
  · simp only [hn, if_true]
    fin_cases c <;> simp <;> fun_prop
  · simp only [hn, if_false]
    fin_cases c <;> simp <;> fun_prop

private theorem fieldOf_phase_continuous (P : ChartParams) (F : FieldData) (y : Space) :
    Continuous (fun β : ℝ => fieldOf P F β y) := by
  unfold fieldOf modePhase
  simp only [ofComponents_sum_form]
  have h : ∀ n c, Continuous (fun β : ℝ => reducedField P F n β (chartT P y) (heightRatio y) c) :=
    fun n c => reducedField_phase_continuous P F n _ _ c
  fun_prop

private theorem mode_contDiff (P : ChartParams) (hP : IsChartParams P) (D : FieldData)
    (hD : IsFieldData P 1 D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ContDiff ℝ 1 (modeFieldOf P D β n) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases h0 : n = 0
  · subst h0
    by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_mean P hP hD β hn
    · have hph : modePhase P 0 β = fun _ => 1 := by
        funext z
        simp [modePhase]
      refine modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hD β hn) y hy ?_
      rw [hph]
      exact contDiffAt_const
  · by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_wave P hP hD β n hn h0
    exact modeFieldOf_contDiffAt_axis_of P hP hD β n hn h0 y hy

private theorem fieldOf_fderiv_modes (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β : ℝ) (y : Space) :
    fderiv ℝ (fieldOf P F β) y = ∑ n ∈ F.modes, fderiv ℝ (modeFieldOf P F β n) y := by
  rw [fieldOf_eq_modeSum]
  have hd : ∀ n ∈ F.modes, DifferentiableAt ℝ (fun z => modeFieldOf P F β n z) y :=
    fun n hn => ((mode_contDiff P hP F hF β n hn).differentiable (by norm_num)) y
  exact fderiv_fun_sum hd

theorem modeField_fderiv_joint_locallySlope_wave (P : ChartParams) (hP : IsChartParams P)
    (F : FieldData) (hF : IsFieldData P 1 F) (n : ℤ) (hn : n ∈ F.modes) (h0 : n ≠ 0) :
    LocallyLipschitz (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 n) q.2) := by
  have hQ := quarterTurnData_isFieldData P F hF n h0
  exact wave_joint_of P F n h0
    (fun c => ⟨mode_contDiff P hP F hF c n hn, mode_contDiff P hP (quarterTurnData F n) hQ c n hn⟩)
    (fun c => ⟨FracInternal.modeFieldOf_fderiv_locallySlope_wave hP hF c n hn h0,
      FracInternal.modeFieldOf_fderiv_locallySlope_wave hP hQ c n hn h0⟩)

private theorem mode_joint_locallySlope (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (n : ℤ) (hn : n ∈ F.modes) :
    LocallyLipschitz (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 n) q.2) := by
  by_cases h0 : n = 0
  · subst h0
    have h := FracInternal.modeFieldOf_fderiv_locallySlope_mean hP hF 0 hn
    have hs : LocallyLipschitz (fun q : ℝ × Space => q.2) := LipschitzWith.prod_snd.locallyLipschitz
    have heq : (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 0) q.2) =
        (fderiv ℝ (modeFieldOf P F 0 0)) ∘ (fun q : ℝ × Space => q.2) := by
      funext q
      rw [Function.comp_apply, mode_zero_indep P F q.1]
    rw [heq]
    exact h.comp hs
  · exact modeField_fderiv_joint_locallySlope_wave P hP F hF n hn h0

theorem fieldOf_fderiv_joint_slopeOn (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun q : ℝ × Space => fderiv ℝ (fieldOf P F q.1) q.2)
      (Metric.closedBall 0 R) := by
  classical
  have hmode : ∀ n ∈ F.modes, ∃ K : NNReal, LipschitzOnWith K
      (fun q : ℝ × Space => fderiv ℝ (modeFieldOf P F q.1 n) q.2) (Metric.closedBall 0 R) :=
    fun n hn => (mode_joint_locallySlope P hP F hF n hn).locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall 0 R)
  have hsum : ∀ s : Finset ℤ, s ⊆ F.modes → ∃ K : NNReal, LipschitzOnWith K
      (fun q : ℝ × Space => ∑ n ∈ s, fderiv ℝ (modeFieldOf P F q.1 n) q.2) (Metric.closedBall 0 R) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, by simpa using (LipschitzWith.const (0 : Space →L[ℝ] Space)).lipschitzOnWith⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨K1, h1⟩ := ih fun x hx => hs (Finset.mem_insert_of_mem hx)
      obtain ⟨K2, h2⟩ := hmode a (hs (Finset.mem_insert_self a s))
      refine ⟨K2 + K1, ?_⟩
      simp only [Finset.sum_insert ha]
      exact h2.add h1
  obtain ⟨K, hK⟩ := hsum F.modes subset_rfl
  refine ⟨K, ?_⟩
  have heq : (fun q : ℝ × Space => fderiv ℝ (fieldOf P F q.1) q.2) =
      fun q => ∑ n ∈ F.modes, fderiv ℝ (modeFieldOf P F q.1 n) q.2 := by
    funext q
    exact fieldOf_fderiv_modes P hP F hF q.1 q.2
  rw [heq]
  exact hK

private theorem fderiv_joint_continuous_of (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) :
    Continuous (fun q : ℝ × Space => fderiv ℝ (fieldOf P F q.1) q.2) := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  obtain ⟨K, hK⟩ := fieldOf_fderiv_joint_slopeOn P hP F hF (‖q‖ + 1)
  have hq : q ∈ Metric.ball (0 : ℝ × Space) (‖q‖ + 1) := mem_ball_zero_iff.2 (by linarith)
  exact (hK.continuousOn.mono Metric.ball_subset_closedBall).continuousAt (Metric.isOpen_ball.mem_nhds hq)

theorem fieldOf_joint_continuous (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) : Continuous (fun q : ℝ × Space => fieldOf P F q.1 q.2) := by
  have hD := fderiv_joint_continuous_of P hP F hF
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  obtain ⟨β₀, y₀⟩ := q₀
  have hS : IsCompact (Set.Icc (β₀ - 1) (β₀ + 1) ×ˢ Metric.closedBall y₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall y₀ 1)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hD.continuousOn
  have hmv : ∀ β : ℝ, |β - β₀| ≤ 1 → ∀ y ∈ Metric.closedBall y₀ 1,
      ‖fieldOf P F β y - fieldOf P F β y₀‖ ≤ M * ‖y - y₀‖ := by
    intro β hβ y hy
    refine (convex_closedBall y₀ 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (fieldOf_differentiable P hP F hF β).differentiableAt)
      (fun z hz => hM (β, z) ⟨⟨?_, ?_⟩, hz⟩) (Metric.mem_closedBall_self zero_le_one) hy
    · linarith [(abs_le.1 hβ).1]
    · linarith [(abs_le.1 hβ).2]
  have h1 : Filter.Tendsto (fun q : ℝ × Space => fieldOf P F q.1 y₀) (nhds (β₀, y₀))
      (nhds (fieldOf P F β₀ y₀)) :=
    ((fieldOf_phase_continuous P F y₀).comp continuous_fst).tendsto (β₀, y₀)
  have h2 : Filter.Tendsto (fun q : ℝ × Space => fieldOf P F q.1 q.2 - fieldOf P F q.1 y₀)
      (nhds (β₀, y₀)) (nhds 0) := by
    refine squeeze_zero_norm' (a := fun q : ℝ × Space => M * ‖q.2 - y₀‖) ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds ((β₀, y₀) : ℝ × Space) one_pos] with q hq
      rw [Metric.mem_ball, Prod.dist_eq] at hq
      have hq1 : dist q.1 β₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hq
      have hq2 : dist q.2 y₀ < 1 := lt_of_le_of_lt (le_max_right _ _) hq
      rw [Real.dist_eq] at hq1
      exact hmv q.1 hq1.le q.2 (Metric.mem_closedBall.2 hq2.le)
    · have hc : Continuous (fun q : ℝ × Space => M * ‖q.2 - y₀‖) := by fun_prop
      simpa using hc.tendsto (β₀, y₀)
  have h3 := h1.add h2
  simp only [add_sub_cancel, add_zero] at h3
  exact h3

theorem fieldOf_fderiv_joint_continuous (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) :
    Continuous (fun q : ℝ × Space => fderiv ℝ (fieldOf P F q.1) q.2) :=
  fderiv_joint_continuous_of P hP F hF

theorem fieldOf_fderiv_slope_uniform (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B R : ℝ) :
    ∃ K : NNReal, ∀ β : ℝ, |β| ≤ B →
      LipschitzOnWith K (fderiv ℝ (fieldOf P F β)) (Metric.closedBall 0 R) := by
  obtain ⟨K, hK⟩ := fieldOf_fderiv_joint_slopeOn P hP F hF (max B R)
  refine ⟨K, fun β hβ => ?_⟩
  have hemb : LipschitzWith 1 (fun y : Space => ((β, y) : ℝ × Space)) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [Prod.dist_eq, dist_self, NNReal.coe_one, one_mul]
      exact max_le dist_nonneg le_rfl
  have hmaps : Set.MapsTo (fun y : Space => ((β, y) : ℝ × Space)) (Metric.closedBall 0 R)
      (Metric.closedBall 0 (max B R)) := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy ⊢
    rw [Prod.norm_def]
    exact max_le_max (by rw [Real.norm_eq_abs]; exact hβ) hy
  have h := hK.comp hemb.lipschitzOnWith hmaps
  rw [mul_one] at h
  exact h


private def FarBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E) (a C R : ℝ) : Prop :=
  0 ≤ C ∧ 1 ≤ R ∧ Differentiable ℝ f ∧ ∀ y : Space, R ≤ ‖y‖ →
    (∀ z ∈ Metric.ball y 1, ‖f z‖ ≤ C * ‖y‖ ^ (-a) ∧ ‖fderiv ℝ f z‖ ≤ C * ‖y‖ ^ (-(a + 1))) ∧
    LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(a + 2)))) (fderiv ℝ f) (Metric.ball y 1)

private theorem pw_mul {x : ℝ} (hx : 0 < x) (u v w : ℝ) (h : u + v = w) : x ^ (-u) * x ^ (-v) = x ^ (-w) := by
  rw [← Real.rpow_add hx]
  congr 1
  linarith

private theorem slopeOn_bilin {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) {s : Set Space} {f : Space → E} {h : Space → F}
    {K1 K2 M1 M2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hf : LipschitzOnWith (Real.toNNReal K1) f s) (hh : LipschitzOnWith (Real.toNNReal K2) h s)
    (hb1 : ∀ z ∈ s, ‖f z‖ ≤ M1) (hb2 : ∀ z ∈ s, ‖h z‖ ≤ M2) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    LipschitzOnWith (Real.toNNReal (K1 * M2 + M1 * K2)) (fun z => B (f z) (h z)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hsplit : B (f a) (h a) - B (f b) (h b) = B (f a - f b) (h a) + B (f b) (h a - h b) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hsplit]
  have d1 : ‖f a - f b‖ ≤ K1 * dist a b := by
    rw [← dist_eq_norm]
    have := hf.dist_le_mul a ha b hb
    rwa [Real.coe_toNNReal _ hK1] at this
  have d2 : ‖h a - h b‖ ≤ K2 * dist a b := by
    rw [← dist_eq_norm]
    have := hh.dist_le_mul a ha b hb
    rwa [Real.coe_toNNReal _ hK2] at this
  have e1 := hB (f a - f b) (h a)
  have e2 := hB (f b) (h a - h b)
  have n1 := hb2 a ha
  have n2 := hb1 b hb
  have hd := dist_nonneg (x := a) (y := b)
  calc ‖B (f a - f b) (h a) + B (f b) (h a - h b)‖ ≤ ‖B (f a - f b) (h a)‖ + ‖B (f b) (h a - h b)‖ :=
        norm_add_le _ _
    _ ≤ (K1 * dist a b) * M2 + M1 * (K2 * dist a b) := by
        gcongr
        · exact e1.trans (mul_le_mul d1 n1 (norm_nonneg _) (by positivity))
        · exact e2.trans (mul_le_mul n2 d2 (norm_nonneg _) hM1)
    _ = (K1 * M2 + M1 * K2) * dist a b := by ring

private theorem slopeOn_ball_of_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : Differentiable ℝ f) {y : Space} {M : ℝ} (hM : ∀ z ∈ Metric.ball y 1, ‖fderiv ℝ f z‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal M) f (Metric.ball y 1) := by
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => hf z) (fun z hz => ?_) (convex_ball y 1)
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hM z hz).trans (Real.le_coe_toNNReal M)

private theorem farBall_weaken {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    {a b C C' R R' : ℝ} (h : FarBall f a C R) (hab : b ≤ a) (hC : C ≤ C') (hR : R ≤ R') : FarBall f b C' R' := by
  obtain ⟨hC0, hR1, hd, hb⟩ := h
  refine ⟨hC0.trans hC, hR1.trans hR, hd, fun y hy => ?_⟩
  have hy1 : 1 ≤ ‖y‖ := hR1.trans (hR.trans hy)
  obtain ⟨h1, h2⟩ := hb y (hR.trans hy)
  have m : ∀ u v : ℝ, v ≤ u → C * ‖y‖ ^ (-u) ≤ C' * ‖y‖ ^ (-v) := fun u v huv =>
    mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)) (by positivity) (hC0.trans hC)
  refine ⟨fun z hz => ⟨(h1 z hz).1.trans (m _ _ hab), (h1 z hz).2.trans (m _ _ (by linarith))⟩, ?_⟩
  exact h2.weaken (Real.toNNReal_le_toNNReal (m _ _ (by linarith)))

private theorem farBall_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Space → E}
    {a C1 C2 R1 R2 : ℝ} (hf : FarBall f a C1 R1) (hg : FarBall g a C2 R2) :
    FarBall (fun z => f z + g z) a (C1 + C2) (max R1 R2) := by
  obtain ⟨hC1, hR1, hfd, hf⟩ := hf
  obtain ⟨hC2, hR2, hgd, hg⟩ := hg
  have hD : fderiv ℝ (fun z => f z + g z) = fun z => fderiv ℝ f z + fderiv ℝ g z := by
    funext z
    exact fderiv_add (hfd z) (hgd z)
  refine ⟨by positivity, le_max_of_le_left hR1, hfd.add hgd, fun y hy => ?_⟩
  obtain ⟨hf1, hf2⟩ := hf y (le_of_max_le_left hy)
  obtain ⟨hg1, hg2⟩ := hg y (le_of_max_le_right hy)
  rw [hD]
  refine ⟨fun z hz => ⟨?_, ?_⟩, ?_⟩
  · have := (hf1 z hz).1
    have := (hg1 z hz).1
    calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · have := (hf1 z hz).2
    have := (hg1 z hz).2
    calc ‖fderiv ℝ f z + fderiv ℝ g z‖ ≤ ‖fderiv ℝ f z‖ + ‖fderiv ℝ g z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · refine (hf2.add hg2).weaken ?_
    rw [← Real.toNNReal_add (by positivity) (by positivity), add_mul]

private theorem farBall_sum {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set ℝ)
    (s : Finset ι) (f : ℝ → ι → Space → E) (a : ℝ)
    (h : ∀ i ∈ s, ∃ C R : ℝ, ∀ β ∈ S, FarBall (f β i) a C R) :
    ∃ C R : ℝ, ∀ β ∈ S, FarBall (fun z => ∑ i ∈ s, f β i z) a C R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 1, fun β _ => ⟨le_rfl, le_rfl, ?_, fun y _ => ?_⟩⟩
    · simpa using (differentiable_const (0 : E) : Differentiable ℝ (fun _ : Space => (0 : E)))
    · have h0 : (fun z : Space => ∑ i ∈ (∅ : Finset ι), f β i z) = fun _ => (0 : E) := by simp
      have h1 : fderiv ℝ (fun _ : Space => (0 : E)) = fun _ => 0 := funext fun z => fderiv_const_apply _
      rw [h0, h1]
      refine ⟨fun z _ => by simp, ?_⟩
      simp only [zero_mul, Real.toNNReal_zero]
      exact (LipschitzWith.const (α := Space) (0 : Space →L[ℝ] E)).lipschitzOnWith
  | insert i s hi ih =>
    obtain ⟨C1, R1, h1⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨C2, R2, h2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨C1 + C2, max R1 R2, fun β hβ => ?_⟩
    simp only [Finset.sum_insert hi]
    exact farBall_add (h1 β hβ) (h2 β hβ)

private theorem srl_apply (u : Space →L[ℝ] ℝ) (v : Space) :
    ContinuousLinearMap.smulRightL ℝ Space Space u v = u.smulRight v := rfl

private theorem farBall_smul {g : Space → ℝ} {W : Space → Space} {a b C1 C2 R1 R2 : ℝ}
    (hg : FarBall g a C1 R1) (hW : FarBall W b C2 R2) :
    FarBall (fun z => g z • W z) (a + b) (4 * (C1 * C2)) (max R1 R2) := by
  obtain ⟨hC1, hR1, hgd, hg⟩ := hg
  obtain ⟨hC2, hR2, hWd, hW⟩ := hW
  have hD : fderiv ℝ (fun z => g z • W z) = fun z => g z • fderiv ℝ W z + (fderiv ℝ g z).smulRight (W z) := by
    funext z
    exact fderiv_smul (hgd z) (hWd z)
  refine ⟨by positivity, le_max_of_le_left hR1, hgd.smul hWd, fun y hy => ?_⟩
  have hρ : 0 < ‖y‖ := lt_of_lt_of_le one_pos (hR1.trans (le_of_max_le_left hy))
  obtain ⟨hg1, hg2⟩ := hg y (le_of_max_le_left hy)
  obtain ⟨hW1, hW2⟩ := hW y (le_of_max_le_right hy)
  set ρ := ‖y‖
  have p0 : 0 ≤ ρ ^ (-a) := by positivity
  have p1 : 0 ≤ ρ ^ (-(a + 1)) := by positivity
  have p2 : 0 ≤ ρ ^ (-(a + 2)) := by positivity
  have q0 : 0 ≤ ρ ^ (-b) := by positivity
  have q1 : 0 ≤ ρ ^ (-(b + 1)) := by positivity
  have q2 : 0 ≤ ρ ^ (-(b + 2)) := by positivity
  have e0 := pw_mul hρ a b (a + b) rfl
  have e1 := pw_mul hρ a (b + 1) (a + b + 1) (by ring)
  have e1' := pw_mul hρ (a + 1) b (a + b + 1) (by ring)
  have e2 := pw_mul hρ (a + 1) (b + 1) (a + b + 2) (by ring)
  have e2' := pw_mul hρ a (b + 2) (a + b + 2) (by ring)
  have e2'' := pw_mul hρ (a + 2) b (a + b + 2) (by ring)
  rw [hD]
  refine ⟨fun z hz => ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul]
    have u1 := (hg1 z hz).1
    have u2 := (hW1 z hz).1
    calc ‖g z‖ * ‖W z‖ ≤ (C1 * ρ ^ (-a)) * (C2 * ρ ^ (-b)) :=
          mul_le_mul u1 u2 (norm_nonneg _) (by positivity)
      _ = C1 * C2 * ρ ^ (-(a + b)) := by rw [← e0]; ring
      _ ≤ 4 * (C1 * C2) * ρ ^ (-(a + b)) := by
          have : 0 ≤ C1 * C2 * ρ ^ (-(a + b)) := by positivity
          linarith
  · have u1 := (hg1 z hz).1
    have u2 := (hW1 z hz).2
    have u3 := (hg1 z hz).2
    have u4 := (hW1 z hz).1
    calc ‖g z • fderiv ℝ W z + (fderiv ℝ g z).smulRight (W z)‖
        ≤ ‖g z‖ * ‖fderiv ℝ W z‖ + ‖fderiv ℝ g z‖ * ‖W z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ (C1 * ρ ^ (-a)) * (C2 * ρ ^ (-(b + 1))) + (C1 * ρ ^ (-(a + 1))) * (C2 * ρ ^ (-b)) := by
          gcongr
      _ = 2 * (C1 * C2) * ρ ^ (-(a + b + 1)) := by linear_combination (C1 * C2) * e1 + (C1 * C2) * e1'
      _ ≤ 4 * (C1 * C2) * ρ ^ (-(a + b + 1)) := by
          have : 0 ≤ C1 * C2 * ρ ^ (-(a + b + 1)) := by positivity
          linarith
  · have lg := slopeOn_ball_of_fderiv hgd fun z hz => (hg1 z hz).2
    have lW := slopeOn_ball_of_fderiv hWd fun z hz => (hW1 z hz).2
    have t1 := slopeOn_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (fun u v => by
        rw [ContinuousLinearMap.lsmul_apply, norm_smul]) (by positivity) (by positivity) lg hW2
        (fun z hz => (hg1 z hz).1) (fun z hz => (hW1 z hz).2) (by positivity) (by positivity)
    have t2 := slopeOn_bilin (ContinuousLinearMap.smulRightL ℝ Space Space) (fun u v => by
        rw [srl_apply, ContinuousLinearMap.norm_smulRight_apply])
        (by positivity) (by positivity) hg2 lW
        (fun z hz => (hg1 z hz).2) (fun z hz => (hW1 z hz).1) (by positivity) (by positivity)
    simp only [ContinuousLinearMap.lsmul_apply, srl_apply] at t1 t2
    refine (t1.add t2).weaken ?_
    rw [← Real.toNNReal_add (by positivity) (by positivity)]
    refine Real.toNNReal_le_toNNReal ?_
    have : C1 * ρ ^ (-(a + 1)) * (C2 * ρ ^ (-(b + 1))) + C1 * ρ ^ (-a) * (C2 * ρ ^ (-((b + 1) + 1))) +
        (C1 * ρ ^ (-(a + 2)) * (C2 * ρ ^ (-b)) + C1 * ρ ^ (-(a + 1)) * (C2 * ρ ^ (-(b + 1)))) =
        4 * (C1 * C2) * ρ ^ (-(a + b + 2)) := by
      rw [show -((b + 1) + 1) = -(b + 2) by ring]
      linear_combination (C1 * C2) * (2 * e2 + e2' + e2'')
    rw [← this]
    apply le_of_eq
    ring_nf


private def trigLin (p q r s k u : ℝ) : ℝ := (p + q * u) * Real.cos (k * u) + (r + s * u) * Real.sin (k * u)

private theorem trigLin_hasDerivAt (p q r s k u : ℝ) :
    HasDerivAt (trigLin p q r s k) (trigLin (q + k * r) (k * s) (s - k * p) (-(k * q)) k u) u := by
  have hk : HasDerivAt (fun u : ℝ => k * u) k u := by simpa using (hasDerivAt_id u).const_mul k
  have hl1 : HasDerivAt (fun u : ℝ => p + q * u) q u := by
    simpa using ((hasDerivAt_id u).const_mul q).const_add p
  have hl2 : HasDerivAt (fun u : ℝ => r + s * u) s u := by
    simpa using ((hasDerivAt_id u).const_mul s).const_add r
  have h := (hl1.mul hk.cos).add (hl2.mul hk.sin)
  show HasDerivAt (fun u => (p + q * u) * Real.cos (k * u) + (r + s * u) * Real.sin (k * u)) _ u
  refine h.congr_deriv ?_
  simp only [trigLin]
  ring

private theorem trigLin_bound (p q r s k u : ℝ) :
    |trigLin p q r s k u| ≤ (|p| + |q| + |r| + |s|) * (1 + |u|) := by
  unfold trigLin
  have c1 := Real.abs_cos_le_one (k * u)
  have s1 := Real.abs_sin_le_one (k * u)
  have a1 : |p + q * u| ≤ |p| + |q| * |u| := (abs_add_le _ _).trans (by rw [abs_mul])
  have a2 : |r + s * u| ≤ |r| + |s| * |u| := (abs_add_le _ _).trans (by rw [abs_mul])
  calc |(p + q * u) * Real.cos (k * u) + (r + s * u) * Real.sin (k * u)|
      ≤ |(p + q * u) * Real.cos (k * u)| + |(r + s * u) * Real.sin (k * u)| := abs_add_le _ _
    _ = |p + q * u| * |Real.cos (k * u)| + |r + s * u| * |Real.sin (k * u)| := by rw [abs_mul, abs_mul]
    _ ≤ (|p| + |q| * |u|) * 1 + (|r| + |s| * |u|) * 1 := by gcongr
    _ ≤ _ := by nlinarith [abs_nonneg p, abs_nonneg q, abs_nonneg r, abs_nonneg s, abs_nonneg u]

private theorem trigLin_coef (p q r s k : ℝ) :
    |q + k * r| + |k * s| + |s - k * p| + |-(k * q)| ≤ (1 + |k|) * (|p| + |q| + |r| + |s|) := by
  have h1 : |q + k * r| ≤ |q| + |k| * |r| := (abs_add_le _ _).trans (by rw [abs_mul])
  have h2 : |s - k * p| ≤ |s| + |k| * |p| := (abs_sub _ _).trans (by rw [abs_mul])
  rw [abs_neg, abs_mul, abs_mul]
  nlinarith [abs_nonneg p, abs_nonneg q, abs_nonneg r, abs_nonneg s, abs_nonneg k]

private theorem farBall_comp {L : Space → ℝ} {h h1 h2 : ℝ → ℝ} {e A1 A2 R K : ℝ}
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hR : 1 ≤ R) (hK : 0 ≤ K) (hL : Differentiable ℝ L)
    (hLb : ∀ y : Space, R ≤ ‖y‖ → (∀ z ∈ Metric.ball y 1, 0 ≤ L z ∧ 1 + L z ≤ A1 * ‖y‖ ^ e ∧
        ‖fderiv ℝ L z‖ ≤ 2 * ‖y‖ ^ (-(1 : ℝ))) ∧
      LipschitzOnWith (Real.toNNReal (A2 * ‖y‖ ^ (-(2 : ℝ)))) (fderiv ℝ L) (Metric.ball y 1))
    (d1 : ∀ u, HasDerivAt h (h1 u) u) (d2 : ∀ u, HasDerivAt h1 (h2 u) u)
    (b0 : ∀ u, |h u| ≤ K * (1 + |u|)) (b1 : ∀ u, |h1 u| ≤ K * (1 + |u|)) (b2 : ∀ u, |h2 u| ≤ K * (1 + |u|)) :
    FarBall (fun z => h (L z)) (-e) (K * A1 * (4 + A2)) R := by
  have hD : ∀ z, HasFDerivAt (fun z => h (L z)) (h1 (L z) • fderiv ℝ L z) z :=
    fun z => (d1 (L z)).comp_hasFDerivAt z (hL z).hasFDerivAt
  have hD1 : ∀ z, HasFDerivAt (fun z => h1 (L z)) (h2 (L z) • fderiv ℝ L z) z :=
    fun z => (d2 (L z)).comp_hasFDerivAt z (hL z).hasFDerivAt
  have hDe : fderiv ℝ (fun z => h (L z)) = fun z => h1 (L z) • fderiv ℝ L z := funext fun z => (hD z).fderiv
  refine ⟨by positivity, hR, fun z => (hD z).differentiableAt, fun y hy => ?_⟩
  obtain ⟨hb, hslope⟩ := hLb y hy
  have hρ : 0 < ‖y‖ := lt_of_lt_of_le one_pos (hR.trans hy)
  set ρ := ‖y‖
  have pe : 0 ≤ ρ ^ e := by positivity
  have p1 : 0 ≤ ρ ^ (-(1 : ℝ)) := by positivity
  have p2 : 0 ≤ ρ ^ (-(2 : ℝ)) := by positivity
  have E0 : ρ ^ e = ρ ^ (-(-e)) := by rw [neg_neg]
  have E1 : ρ ^ e * ρ ^ (-(1 : ℝ)) = ρ ^ (-(-e + 1)) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have E2 : ρ ^ e * ρ ^ (-(2 : ℝ)) = ρ ^ (-(-e + 2)) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have E3 : ρ ^ e * ρ ^ (-(1 : ℝ)) * ρ ^ (-(1 : ℝ)) = ρ ^ (-(-e + 2)) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 1
    ring
  have hv : ∀ z ∈ Metric.ball y 1, ∀ g : ℝ → ℝ, (∀ u, |g u| ≤ K * (1 + |u|)) → |g (L z)| ≤ K * A1 * ρ ^ e := by
    intro z hz g hg
    obtain ⟨l0, l1, -⟩ := hb z hz
    calc |g (L z)| ≤ K * (1 + |L z|) := hg _
      _ = K * (1 + L z) := by rw [abs_of_nonneg l0]
      _ ≤ K * (A1 * ρ ^ e) := by gcongr
      _ = K * A1 * ρ ^ e := by ring
  rw [hDe]
  refine ⟨fun z hz => ⟨?_, ?_⟩, ?_⟩
  · rw [Real.norm_eq_abs, ← E0]
    refine (hv z hz h b0).trans ?_
    have : 0 ≤ K * A1 * ρ ^ e * (3 + A2) := by positivity
    have e' : K * A1 * (4 + A2) * ρ ^ e = K * A1 * ρ ^ e + K * A1 * ρ ^ e * (3 + A2) := by ring
    linarith
  · rw [norm_smul, Real.norm_eq_abs, ← E1]
    have u1 := hv z hz h1 b1
    have l2 := (hb z hz).2.2
    have m := mul_le_mul u1 l2 (norm_nonneg _) (by positivity)
    have : 0 ≤ K * A1 * (ρ ^ e * ρ ^ (-(1 : ℝ))) * (2 + A2) := by positivity
    have e' : K * A1 * (4 + A2) * (ρ ^ e * ρ ^ (-(1 : ℝ))) =
        K * A1 * ρ ^ e * (2 * ρ ^ (-(1 : ℝ))) + K * A1 * (ρ ^ e * ρ ^ (-(1 : ℝ))) * (2 + A2) := by ring
    linarith
  · have lh := slopeOn_ball_of_fderiv (f := fun z => h1 (L z)) (fun z => (hD1 z).differentiableAt)
      (M := K * A1 * ρ ^ e * (2 * ρ ^ (-(1 : ℝ)))) (fun z hz => by
        rw [(hD1 z).fderiv, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hv z hz h2 b2) (hb z hz).2.2 (norm_nonneg _) (by positivity))
    have t := slopeOn_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (fun u v => by
        rw [ContinuousLinearMap.lsmul_apply, norm_smul]) (by positivity) (by positivity) lh hslope
      (fun z hz => by rw [Real.norm_eq_abs]; exact hv z hz h1 b1) (fun z hz => (hb z hz).2.2)
      (by positivity) (by positivity)
    simp only [ContinuousLinearMap.lsmul_apply] at t
    refine t.weaken (Real.toNNReal_le_toNNReal (le_of_eq ?_))
    linear_combination (4 * K * A1) * E3 + (K * A1 * A2) * E2

private theorem farBall_of_pointwise {f : Space → Space} (hf : Differentiable ℝ f) {e R C : ℝ} (he : 0 ≤ e)
    (h : ∀ y : Space, R ≤ ‖y‖ → ‖f y‖ ≤ C * ‖y‖ ^ (-e) ∧ ‖fderiv ℝ f y‖ ≤ C * ‖y‖ ^ (-(e + 1)) ∧
      LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(e + 2)))) (fderiv ℝ f) (Metric.ball y 1)) :
    FarBall f e (2 ^ (e + 1) * max C 0) (max (2 * R) 2) := by
  refine ⟨by positivity, le_max_of_le_right one_le_two, hf, fun y hy => ?_⟩
  have hρ2 : 2 ≤ ‖y‖ := le_of_max_le_right hy
  have hρR : 2 * R ≤ ‖y‖ := le_of_max_le_left hy
  have hρ : 0 < ‖y‖ := by linarith
  have cmp : ∀ z ∈ Metric.ball y 1, R ≤ ‖z‖ ∧ ∀ u : ℝ, 0 ≤ u → ‖z‖ ^ (-u) ≤ 2 ^ u * ‖y‖ ^ (-u) := by
    intro z hz
    have hd : ‖z - y‖ < 1 := by rw [← dist_eq_norm]; exact hz
    have h1 : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := norm_le_insert' y z
    rw [norm_sub_rev] at h1
    have hz2 : ‖y‖ / 2 ≤ ‖z‖ := by linarith
    refine ⟨by linarith, fun u hu => ?_⟩
    calc ‖z‖ ^ (-u) ≤ (‖y‖ / 2) ^ (-u) := Real.rpow_le_rpow_of_nonpos (by positivity) hz2 (by linarith)
      _ = 2 ^ u * ‖y‖ ^ (-u) := by
        rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ z ∈ Metric.ball y 1, ∀ u : ℝ, 0 ≤ u → u ≤ e + 1 → C * ‖z‖ ^ (-u) ≤ 2 ^ (e + 1) * max C 0 * ‖y‖ ^ (-u) := by
    intro z hz u hu hue
    obtain ⟨-, hc⟩ := cmp z hz
    have h2 : (2 : ℝ) ^ u ≤ 2 ^ (e + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hue
    have hp : 0 ≤ max C 0 * ‖y‖ ^ (-u) := by positivity
    calc C * ‖z‖ ^ (-u) ≤ max C 0 * ‖z‖ ^ (-u) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * (2 ^ u * ‖y‖ ^ (-u)) := mul_le_mul_of_nonneg_left (hc u hu) hM
      _ = 2 ^ u * (max C 0 * ‖y‖ ^ (-u)) := by ring
      _ ≤ 2 ^ (e + 1) * (max C 0 * ‖y‖ ^ (-u)) := mul_le_mul_of_nonneg_right h2 hp
      _ = 2 ^ (e + 1) * max C 0 * ‖y‖ ^ (-u) := by ring
  refine ⟨fun z hz => ⟨?_, ?_⟩, ?_⟩
  · exact (h z (cmp z hz).1).1.trans (key z hz e he (by linarith))
  · exact (h z (cmp z hz).1).2.1.trans (key z hz (e + 1) (by linarith) le_rfl)
  · refine (h y (by linarith)).2.2.weaken (Real.toNNReal_le_toNNReal ?_)
    have h1 : (1 : ℝ) ≤ 2 ^ (e + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    have hp : 0 ≤ max C 0 * ‖y‖ ^ (-(e + 2)) := by positivity
    calc C * ‖y‖ ^ (-(e + 2)) ≤ max C 0 * ‖y‖ ^ (-(e + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ 2 ^ (e + 1) * (max C 0 * ‖y‖ ^ (-(e + 2))) := le_mul_of_one_le_left hp h1
      _ = _ := by ring

private theorem logPhase_hasFDerivAt (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    HasFDerivAt (logPhase P) ((P.rc ^ 2 + ‖y‖ ^ 2)⁻¹ • innerSL ℝ y) y := by
  have hrc : 0 < P.rc := hP.rc_pos
  have h1 : HasFDerivAt (fun x : Space => ‖x‖ ^ 2) (2 • innerSL ℝ y) y := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hpos : 0 < 1 + ‖y‖ ^ 2 / P.rc ^ 2 := by positivity
  have hpos' : 1 + (P.rc ^ 2)⁻¹ * ‖y‖ ^ 2 ≠ 0 := by positivity
  have h3 := (((h1.const_mul (P.rc ^ 2)⁻¹).const_add 1).log hpos').const_mul (1 / 2 : ℝ)
  have hfun : logPhase P = fun y : Space => (1 / 2) * Real.log (1 + (P.rc ^ 2)⁻¹ * ‖y‖ ^ 2) := by
    funext z
    simp only [logPhase, div_eq_inv_mul]
  rw [hfun]
  refine h3.congr_fderiv ?_
  ext v
  simp
  field_simp

private theorem ball_norms {y z : Space} (hz : z ∈ Metric.ball y 1) : ‖y‖ ≤ ‖z‖ + 1 ∧ ‖z‖ ≤ ‖y‖ + 1 := by
  have hd : ‖z - y‖ < 1 := by rw [← dist_eq_norm]; exact hz
  have h1 : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := norm_le_insert' y z
  have h2 : ‖z‖ ≤ ‖y‖ + ‖z - y‖ := norm_le_insert' z y
  rw [norm_sub_rev] at h1
  constructor <;> linarith

private theorem logPhase_far (P : ChartParams) (hP : IsChartParams P) :
    ∃ A1 A2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ ∀ y : Space, 2 ≤ ‖y‖ →
      (∀ z ∈ Metric.ball y 1, 0 ≤ logPhase P z ∧ 1 + logPhase P z ≤ A1 * ‖y‖ ^ P.eps ∧
        ‖fderiv ℝ (logPhase P) z‖ ≤ 2 * ‖y‖ ^ (-(1 : ℝ))) ∧
      LipschitzOnWith (Real.toNNReal (A2 * ‖y‖ ^ (-(2 : ℝ)))) (fderiv ℝ (logPhase P)) (Metric.ball y 1) := by
  have hrc := hP.rc_pos
  have he := hP.eps_pos
  set K0 : ℝ := 1 + 4 / P.rc ^ 2 with hK0d
  have hK0 : 0 < K0 := by positivity
  refine ⟨1 + K0 ^ (P.eps / 2) / P.eps, 28, by positivity, by norm_num, fun y hy => ?_⟩
  have hρ : 0 < ‖y‖ := by linarith
  have hDL : ∀ z, fderiv ℝ (logPhase P) z = (P.rc ^ 2 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z :=
    fun z => (logPhase_hasFDerivAt P hP z).fderiv
  set ρ := ‖y‖ with hρdef
  have r1 : ρ ^ (-(1 : ℝ)) = ρ⁻¹ := Real.rpow_neg_one ρ
  have r2 : ρ ^ (-(2 : ℝ)) = (ρ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hρ.le]
    norm_cast
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨n1, n2⟩ := ball_norms hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hX : 1 ≤ 1 + ‖z‖ ^ 2 / P.rc ^ 2 := by
      have : 0 ≤ ‖z‖ ^ 2 / P.rc ^ 2 := by positivity
      linarith
    refine ⟨?_, ?_, ?_⟩
    · unfold logPhase
      have := Real.log_nonneg hX
      positivity
    · have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2 / P.rc ^ 2)
        (by positivity : 0 < P.eps / 2)
      have hXle : 1 + ‖z‖ ^ 2 / P.rc ^ 2 ≤ K0 * ρ ^ 2 := by
        have h0 : ‖z‖ ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
        have h4 : ‖z‖ ^ 2 / P.rc ^ 2 ≤ 4 * ρ ^ 2 / P.rc ^ 2 := div_le_div_of_nonneg_right h0 (by positivity)
        have h1 : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith
        have h5 : K0 * ρ ^ 2 = ρ ^ 2 + 4 * ρ ^ 2 / P.rc ^ 2 := by rw [hK0d]; ring
        linarith
      have hpow : (1 + ‖z‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 2) ≤ K0 ^ (P.eps / 2) * ρ ^ P.eps := by
        calc (1 + ‖z‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 2) ≤ (K0 * ρ ^ 2) ^ (P.eps / 2) :=
              Real.rpow_le_rpow (by linarith) hXle (by positivity)
          _ = K0 ^ (P.eps / 2) * ρ ^ P.eps := by
              rw [Real.mul_rpow hK0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
              congr 2
              push_cast
              ring
      have h1e : 1 ≤ ρ ^ P.eps := Real.one_le_rpow (by linarith) he.le
      have hL : logPhase P z ≤ K0 ^ (P.eps / 2) / P.eps * ρ ^ P.eps := by
        unfold logPhase
        calc (1 / 2) * Real.log (1 + ‖z‖ ^ 2 / P.rc ^ 2)
            ≤ (1 / 2) * ((1 + ‖z‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 2) / (P.eps / 2)) := by gcongr
          _ = (1 + ‖z‖ ^ 2 / P.rc ^ 2) ^ (P.eps / 2) / P.eps := by field_simp
          _ ≤ K0 ^ (P.eps / 2) * ρ ^ P.eps / P.eps := by gcongr
          _ = _ := by ring
      have e' : (1 + K0 ^ (P.eps / 2) / P.eps) * ρ ^ P.eps = ρ ^ P.eps + K0 ^ (P.eps / 2) / P.eps * ρ ^ P.eps := by
        ring
      linarith
    · rw [hDL, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos (by positivity), r1,
        inv_mul_le_iff₀ (by positivity)]
      have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
      have hz2 : ρ ≤ 2 * ‖z‖ := by linarith
      have h1 : ‖z‖ * ρ ≤ 2 * ‖z‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hz2 (norm_nonneg z)]
      have h2 : ‖z‖ = ‖z‖ * ρ * ρ⁻¹ := by field_simp
      calc ‖z‖ = ‖z‖ * ρ * ρ⁻¹ := h2
        _ ≤ 2 * ‖z‖ ^ 2 * ρ⁻¹ := mul_le_mul_of_nonneg_right h1 hρi.le
        _ ≤ (P.rc ^ 2 + ‖z‖ ^ 2) * (2 * ρ⁻¹) := by nlinarith [mul_nonneg (sq_nonneg P.rc) hρi.le]
  · refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.coe_toNNReal _ (by positivity), r2, dist_eq_norm, dist_eq_norm, hDL, hDL]
    obtain ⟨a1, a2⟩ := ball_norms ha
    obtain ⟨b1, b2⟩ := ball_norms hb
    have hna : 0 < ‖a‖ := by linarith
    have hnb : 0 < ‖b‖ := by linarith
    have hsub : (P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ • innerSL ℝ a - (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹ • innerSL ℝ b =
        innerSL ℝ ((P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ • (a - b) + ((P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ - (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹) • b) := by
      simp only [map_add, map_smul, map_sub, sub_smul, smul_sub]
      abel
    have hdiff : (P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ - (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹ =
        (P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ * (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹ * (‖b‖ ^ 2 - ‖a‖ ^ 2) := by
      field_simp
      ring
    rw [hsub, innerSL_apply_norm]
    have hca1 : (P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ * (P.rc ^ 2 + ‖a‖ ^ 2) = 1 := inv_mul_cancel₀ (by positivity)
    have hcb1 : (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹ * (P.rc ^ 2 + ‖b‖ ^ 2) = 1 := inv_mul_cancel₀ (by positivity)
    have hd : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
    rw [hdiff]
    generalize (P.rc ^ 2 + ‖a‖ ^ 2)⁻¹ = ca at hca1 ⊢
    generalize (P.rc ^ 2 + ‖b‖ ^ 2)⁻¹ = cb at hcb1 ⊢
    have hca0 : 0 ≤ ca := by
      by_contra hn
      have := lt_of_not_ge hn
      nlinarith [sq_nonneg P.rc, sq_nonneg ‖a‖]
    have hcb0 : 0 ≤ cb := by
      by_contra hn
      have := lt_of_not_ge hn
      nlinarith [sq_nonneg P.rc, sq_nonneg ‖b‖]
    have hca : ca * ‖a‖ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hca0 (sq_nonneg P.rc)]
    have hcb : cb * ‖b‖ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hcb0 (sq_nonneg P.rc)]
    have hsq : |‖b‖ ^ 2 - ‖a‖ ^ 2| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
      rw [show ‖b‖ ^ 2 - ‖a‖ ^ 2 = (‖b‖ - ‖a‖) * (‖b‖ + ‖a‖) by ring, abs_mul,
        abs_of_pos (by linarith : 0 < ‖b‖ + ‖a‖)]
      nlinarith [abs_nonneg (‖b‖ - ‖a‖)]
    calc ‖ca • (a - b) + (ca * cb * (‖b‖ ^ 2 - ‖a‖ ^ 2)) • b‖
        ≤ ca * ‖a - b‖ + ca * cb * |‖b‖ ^ 2 - ‖a‖ ^ 2| * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hca0, abs_mul,
            abs_of_nonneg (mul_nonneg hca0 hcb0)]
      _ ≤ 28 * (ρ ^ 2)⁻¹ * ‖a - b‖ := by
          have hρb : ρ ≤ 2 * ‖b‖ := by linarith
          have hρa : ρ ≤ 2 * ‖a‖ := by linarith
          have X : ρ ^ 2 * ca ≤ 4 := by
            have h1 : ρ ^ 2 ≤ (2 * ‖a‖) ^ 2 := pow_le_pow_left₀ hρ.le hρa 2
            have h2 := mul_le_mul_of_nonneg_right h1 hca0
            have h3 : (2 * ‖a‖) ^ 2 * ca = 4 * (ca * ‖a‖ ^ 2) := by ring
            linarith
          have Y : ρ * (cb * ‖b‖) ≤ 2 := by
            have h2 := mul_le_mul_of_nonneg_right hρb (mul_nonneg hcb0 hnb.le)
            have h3 : 2 * ‖b‖ * (cb * ‖b‖) = 2 * (cb * ‖b‖ ^ 2) := by ring
            linarith
          have Z : ‖a‖ + ‖b‖ ≤ 3 * ρ := by linarith
          have hY0 : 0 ≤ ρ * (cb * ‖b‖) := mul_nonneg hρ.le (mul_nonneg hcb0 hnb.le)
          have t2 : ca * cb * |‖b‖ ^ 2 - ‖a‖ ^ 2| * ‖b‖ ≤ ca * (cb * ‖b‖) * (‖a - b‖ * (‖a‖ + ‖b‖)) := by
            calc ca * cb * |‖b‖ ^ 2 - ‖a‖ ^ 2| * ‖b‖ = ca * (cb * ‖b‖) * |‖b‖ ^ 2 - ‖a‖ ^ 2| := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hsq (mul_nonneg hca0 (mul_nonneg hcb0 hnb.le))
          have t3 : ρ ^ 2 * (ca * (cb * ‖b‖) * (‖a - b‖ * (‖a‖ + ‖b‖))) ≤ 24 * ‖a - b‖ := by
            refine le_of_mul_le_mul_right ?_ hρ
            have m1 : (ρ ^ 2 * ca) * (ρ * (cb * ‖b‖)) ≤ 4 * 2 := mul_le_mul X Y hY0 (by norm_num)
            have m2 : (ρ ^ 2 * ca) * (ρ * (cb * ‖b‖)) * (‖a‖ + ‖b‖) ≤ 4 * 2 * (3 * ρ) :=
              mul_le_mul m1 Z (by positivity) (by norm_num)
            have m3 := mul_le_mul_of_nonneg_right m2 (norm_nonneg (a - b))
            calc ρ ^ 2 * (ca * (cb * ‖b‖) * (‖a - b‖ * (‖a‖ + ‖b‖))) * ρ
                = (ρ ^ 2 * ca) * (ρ * (cb * ‖b‖)) * (‖a‖ + ‖b‖) * ‖a - b‖ := by ring
              _ ≤ 4 * 2 * (3 * ρ) * ‖a - b‖ := m3
              _ = 24 * ‖a - b‖ * ρ := by ring
          have t1 : ρ ^ 2 * (ca * ‖a - b‖) ≤ 4 * ‖a - b‖ := by
            have h2 := mul_le_mul_of_nonneg_right X (norm_nonneg (a - b))
            have h3 : ρ ^ 2 * (ca * ‖a - b‖) = ρ ^ 2 * ca * ‖a - b‖ := by ring
            linarith
          rw [show 28 * (ρ ^ 2)⁻¹ * ‖a - b‖ = (28 * ‖a - b‖) / ρ ^ 2 by field_simp,
            le_div_iff₀ (by positivity)]
          have h4 := mul_le_mul_of_nonneg_left t2 (sq_nonneg ρ)
          have h5 : ρ ^ 2 * (ca * ‖a - b‖ + ca * cb * |‖b‖ ^ 2 - ‖a‖ ^ 2| * ‖b‖) =
              ρ ^ 2 * (ca * ‖a - b‖) + ρ ^ 2 * (ca * cb * |‖b‖ ^ 2 - ‖a‖ ^ 2| * ‖b‖) := by ring
          rw [mul_comm, h5]
          linarith

private theorem farBall_trig (P : ChartParams) (hP : IsChartParams P) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p q r s k : ℝ,
      FarBall (fun z => trigLin p q r s k (logPhase P z)) (-P.eps)
        ((|p| + |q| + |r| + |s|) * (1 + |k|) ^ 2 * A) 2 := by
  obtain ⟨A1, A2, hA1, hA2, hL⟩ := logPhase_far P hP
  refine ⟨A1 * (4 + A2), by positivity, fun p q r s k => ?_⟩
  have hk : 1 ≤ 1 + |k| := by linarith [abs_nonneg k]
  have hk2 : 1 + |k| ≤ (1 + |k|) ^ 2 := by nlinarith
  have hN : 0 ≤ |p| + |q| + |r| + |s| := by positivity
  have hN1 := trigLin_coef p q r s k
  have hN2 := trigLin_coef (q + k * r) (k * s) (s - k * p) (-(k * q)) k
  have hN10 : 0 ≤ |q + k * r| + |k * s| + |s - k * p| + |-(k * q)| := by positivity
  have h := farBall_comp (L := logPhase P) (h := trigLin p q r s k)
    (h1 := trigLin (q + k * r) (k * s) (s - k * p) (-(k * q)) k)
    (h2 := trigLin (k * s + k * (s - k * p)) (k * -(k * q)) (-(k * q) - k * (q + k * r)) (-(k * (k * s))) k)
    (K := (|p| + |q| + |r| + |s|) * (1 + |k|) ^ 2) hA1 hA2 one_le_two (by positivity)
    (fun z => (logPhase_hasFDerivAt P hP z).differentiableAt) hL (trigLin_hasDerivAt p q r s k)
    (trigLin_hasDerivAt _ _ _ _ k) (fun u => ?_) (fun u => ?_) (fun u => ?_)
  · exact farBall_weaken h le_rfl (le_of_eq (by ring)) le_rfl
  · refine (trigLin_bound p q r s k u).trans ?_
    gcongr
    nlinarith
  · refine (trigLin_bound _ _ _ _ k u).trans ?_
    gcongr
    nlinarith
  · refine (trigLin_bound _ _ _ _ k u).trans ?_
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left hN1 (by linarith : (0 : ℝ) ≤ 1 + |k|)]

private theorem mode_farBall (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 1 D)
    (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) : ∃ C R : ℝ, FarBall (modeFieldOf P D c n) (1 + P.eps) C R := by
  obtain ⟨R, C, h⟩ := modeFieldOf_far_bounds P hP D hD c n hn
  refine ⟨_, _, farBall_of_pointwise (R := R) (C := C) ((mode_contDiff P hP D hD c n hn).differentiable (by norm_num))
    (by linarith [hP.eps_pos]) (fun y hy => ?_)⟩
  obtain ⟨h1, h2, h3⟩ := h y hy
  refine ⟨h1, ?_, ?_⟩
  · rwa [show -(1 + P.eps + 1) = -(2 + P.eps) by ring]
  · rwa [show -(1 + P.eps + 2) = -(3 + P.eps) by ring]

private theorem waveCoef_trig (P : ChartParams) (n : ℤ) (j : Fin 4) (β : ℝ) :
    ∃ p r k : ℝ, |p| + |r| ≤ 1 + |β| ∧ |k| ≤ |(n : ℝ)| * (|β| + 1) ∧
      ∀ y, waveCoef P n j (β, y) = trigLin p 0 r 0 k (logPhase P y) := by
  have h1 : |1 - β| ≤ 1 + |β| := (abs_sub _ _).trans (by rw [abs_one])
  have h2 : |β - 1| ≤ |β| + 1 := (abs_sub _ _).trans (by rw [abs_one])
  have hn0 := abs_nonneg (n : ℝ)
  fin_cases j
  · refine ⟨1 - β, 0, n * β, by rw [abs_zero]; linarith, ?_, fun y => ?_⟩
    · rw [abs_mul]
      nlinarith [abs_nonneg β]
    · simp only [waveCoef, trigLin, Fin.zero_eta, Matrix.cons_val_zero]
      ring
  · refine ⟨0, -(1 - β), n * β, by rw [abs_zero, abs_neg]; linarith, ?_, fun y => ?_⟩
    · rw [abs_mul]
      nlinarith [abs_nonneg β]
    · simp only [waveCoef, trigLin, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
  · refine ⟨β, 0, n * (β - 1), by simp, ?_, fun y => ?_⟩
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 hn0
    · simp only [waveCoef, trigLin, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
  · refine ⟨0, -β, n * (β - 1), by simp, ?_, fun y => ?_⟩
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 hn0
    · simp only [waveCoef, trigLin, Fin.reduceFinMk, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
      ring

private theorem waveCoef_farBall (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (j : Fin 4) (B : ℝ) :
    ∃ C R : ℝ, ∀ β ∈ {β : ℝ | |β| ≤ B}, FarBall (fun y => waveCoef P n j (β, y)) (-P.eps) C R := by
  obtain ⟨A, hA, hT⟩ := farBall_trig P hP
  refine ⟨(1 + |B|) * (1 + |(n : ℝ)| * (|B| + 1)) ^ 2 * A, 2, fun β hβ => ?_⟩
  obtain ⟨p, r, k, hpr, hk, he⟩ := waveCoef_trig P n j β
  have hfun : (fun y => waveCoef P n j (β, y)) = fun y => trigLin p 0 r 0 k (logPhase P y) := funext he
  rw [hfun]
  refine farBall_weaken (hT p 0 r 0 k) le_rfl ?_ le_rfl
  have hβ' : |β| ≤ |B| := (show |β| ≤ B from hβ).trans (le_abs_self B)
  have hk' : |k| ≤ |(n : ℝ)| * (|B| + 1) :=
    hk.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have hN : |p| + |(0 : ℝ)| + |r| + |(0 : ℝ)| ≤ 1 + |B| := by
    simp only [abs_zero, add_zero]
    linarith
  have hK : (1 + |k|) ^ 2 ≤ (1 + |(n : ℝ)| * (|B| + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul hN hK (by positivity) (by positivity)) hA

private theorem waveCoef_dtrig (P : ChartParams) (n : ℤ) (j : Fin 4) (β₀ : ℝ) :
    ∃ p q r s k : ℝ, ∀ y, fderiv ℝ (waveCoef P n j) (β₀, y) ((1 : ℝ), (0 : Space)) =
      trigLin p q r s k (logPhase P y) := by
  have key : ∀ p q r s k : ℝ, (∀ y, HasDerivAt (fun β => waveCoef P n j (β, y))
      (trigLin p q r s k (logPhase P y)) β₀) → ∃ p q r s k : ℝ, ∀ y,
        fderiv ℝ (waveCoef P n j) (β₀, y) ((1 : ℝ), (0 : Space)) = trigLin p q r s k (logPhase P y) := by
    intro p q r s k h
    refine ⟨p, q, r, s, k, fun y => ?_⟩
    have hc : HasDerivAt (fun β : ℝ => ((β, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) β₀ :=
      (hasDerivAt_id β₀).prodMk (hasDerivAt_const β₀ y)
    have h2 := (((waveCoef_smooth P n j).differentiable (by norm_num)) (β₀, y)).hasFDerivAt.comp_hasDerivAt β₀ hc
    exact h2.unique (h y)
  have hk0 : ∀ u : ℝ, HasDerivAt (fun β : ℝ => (n : ℝ) * β * u) ((n : ℝ) * u) β₀ := by
    intro u
    simpa using ((hasDerivAt_id β₀).const_mul (n : ℝ)).mul_const u
  have hk1 : ∀ u : ℝ, HasDerivAt (fun β : ℝ => (n : ℝ) * (β - 1) * u) ((n : ℝ) * u) β₀ := by
    intro u
    simpa using (((hasDerivAt_id β₀).sub_const 1).const_mul (n : ℝ)).mul_const u
  have hl : HasDerivAt (fun β : ℝ => 1 - β) (-1) β₀ := by simpa using (hasDerivAt_id β₀).const_sub 1
  fin_cases j
  · refine key (-1) 0 0 (-((1 - β₀) * n)) (n * β₀) fun y => ?_
    simp only [waveCoef, Fin.zero_eta, Matrix.cons_val_zero]
    exact (hl.mul (hk0 (logPhase P y)).cos).congr_deriv (by simp only [trigLin]; ring)
  · refine key 0 (-((1 - β₀) * n)) 1 0 (n * β₀) fun y => ?_
    simp only [waveCoef, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact (hl.mul (hk0 (logPhase P y)).sin).neg.congr_deriv (by simp only [trigLin]; ring)
  · refine key 1 0 0 (-(β₀ * n)) (n * (β₀ - 1)) fun y => ?_
    simp only [waveCoef, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact ((hasDerivAt_id β₀).mul (hk1 (logPhase P y)).cos).congr_deriv (by simp only [trigLin, id]; ring)
  · refine key 0 (-(β₀ * n)) (-1) 0 (n * (β₀ - 1)) fun y => ?_
    simp only [waveCoef, Fin.reduceFinMk, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    exact ((hasDerivAt_id β₀).mul (hk1 (logPhase P y)).sin).neg.congr_deriv (by simp only [trigLin, id]; ring)

private theorem waveParts_farBall (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (n : ℤ) (hn : n ∈ F.modes) (h0 : n ≠ 0) (j : Fin 4) :
    ∃ C R : ℝ, FarBall (waveParts P F n j) (1 + P.eps) C R :=
  waveParts_of (Q := fun f => ∃ C R : ℝ, FarBall f (1 + P.eps) C R) P F n
    (fun c => ⟨mode_farBall P hP F hF c n hn,
      mode_farBall P hP (quarterTurnData F n) (quarterTurnData_isFieldData P F hF n h0) c n hn⟩) j

private theorem modeField_farBall_unif (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B : ℝ) (n : ℤ) (hn : n ∈ F.modes) :
    ∃ C R : ℝ, ∀ β ∈ {β : ℝ | |β| ≤ B}, FarBall (fun z => modeFieldOf P F β n z) 1 C R := by
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨C, R, h⟩ := mode_farBall P hP F hF 0 0 hn
    refine ⟨C, R, fun β _ => ?_⟩
    rw [mode_zero_indep P F β]
    exact farBall_weaken h (by linarith [hP.eps_pos]) le_rfl le_rfl
  · have hj : ∀ j ∈ (Finset.univ : Finset (Fin 4)), ∃ C R : ℝ, ∀ β ∈ {β : ℝ | |β| ≤ B},
        FarBall (fun z => waveCoef P n j (β, z) • waveParts P F n j z) 1 C R := by
      intro j _
      obtain ⟨C1, R1, h1⟩ := waveCoef_farBall P hP n j B
      obtain ⟨C2, R2, h2⟩ := waveParts_farBall P hP F hF n hn h0 j
      exact ⟨4 * (C1 * C2), max R1 R2, fun β hβ =>
        farBall_weaken (farBall_smul (h1 β hβ) h2) (by linarith) le_rfl le_rfl⟩
    obtain ⟨C, R, h⟩ := farBall_sum {β : ℝ | |β| ≤ B} Finset.univ
      (fun β j z => waveCoef P n j (β, z) • waveParts P F n j z) 1 hj
    refine ⟨C, R, fun β hβ => ?_⟩
    rw [mode_eq_parts P F n h0 β]
    exact h β hβ

private theorem phaseTerm_farBall (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) (n : ℤ) (hn : n ∈ F.modes) :
    ∃ C R : ℝ, ∀ β ∈ (Set.univ : Set ℝ), FarBall (fun z => phaseTerm P F β₀ n z) 1 C R := by
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨C, R, h⟩ := farBall_sum (Set.univ : Set ℝ) (∅ : Finset (Fin 4))
      (fun _ _ _ => (0 : Space)) 1 (by simp)
    refine ⟨C, R, fun β hβ => ?_⟩
    have he : (fun z => phaseTerm P F β₀ 0 z) = fun z => ∑ i ∈ (∅ : Finset (Fin 4)), (0 : Space) := by
      funext z
      simp [phaseTerm]
    rw [he]
    exact h β hβ
  · have hpt : (fun z => phaseTerm P F β₀ n z) = fun z => ∑ j : Fin 4,
        (fderiv ℝ (waveCoef P n j) (β₀, z) ((1 : ℝ), (0 : Space))) • waveParts P F n j z := by
      funext z
      simp only [phaseTerm, h0, if_false]
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin 4)), ∃ C R : ℝ, ∀ β ∈ (Set.univ : Set ℝ),
        FarBall (fun z => (fderiv ℝ (waveCoef P n j) (β₀, z) ((1 : ℝ), (0 : Space))) • waveParts P F n j z)
          1 C R := by
      intro j _
      obtain ⟨A, hA, hT⟩ := farBall_trig P hP
      obtain ⟨p, q, r, s, k, hd⟩ := waveCoef_dtrig P n j β₀
      obtain ⟨C2, R2, h2⟩ := waveParts_farBall P hP F hF n hn h0 j
      have hc : FarBall (fun z => fderiv ℝ (waveCoef P n j) (β₀, z) ((1 : ℝ), (0 : Space))) (-P.eps)
          ((|p| + |q| + |r| + |s|) * (1 + |k|) ^ 2 * A) 2 := by
        rw [show (fun z => fderiv ℝ (waveCoef P n j) (β₀, z) ((1 : ℝ), (0 : Space))) =
          fun z => trigLin p q r s k (logPhase P z) from funext hd]
        exact hT p q r s k
      exact ⟨_, _, fun _ _ => farBall_weaken (farBall_smul hc h2) (by linarith) le_rfl le_rfl⟩
    obtain ⟨C, R, h⟩ := farBall_sum (Set.univ : Set ℝ) Finset.univ
      (fun _ j z => (fderiv ℝ (waveCoef P n j) (β₀, z) ((1 : ℝ), (0 : Space))) • waveParts P F n j z) 1 hj
    refine ⟨C, R, fun β hβ => ?_⟩
    rw [hpt]
    exact h β hβ

theorem fieldOf_far_bounds (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (B : ℝ) :
    ∃ R C : ℝ, ∀ β : ℝ, |β| ≤ B → ∀ y : Space, R ≤ ‖y‖ →
      ‖fieldOf P F β y‖ ≤ C * ‖y‖ ^ (-(1 : ℝ)) ∧
        ‖fderiv ℝ (fieldOf P F β) y‖ ≤ C * ‖y‖ ^ (-(2 : ℝ)) ∧
          LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(3 : ℝ))))
            (fderiv ℝ (fieldOf P F β)) (Metric.ball y 1) := by
  obtain ⟨C, R, h⟩ := farBall_sum {β : ℝ | |β| ≤ B} F.modes (fun β n z => modeFieldOf P F β n z) 1
    (fun n hn => modeField_farBall_unif P hP F hF B n hn)
  refine ⟨R, C, fun β hβ y hy => ?_⟩
  obtain ⟨-, -, -, hb⟩ := h β hβ
  obtain ⟨h1, h2⟩ := hb y hy
  have hy1 := h1 y (Metric.mem_ball_self one_pos)
  rw [fieldOf_eq_modeSum P F β]
  refine ⟨hy1.1, ?_, ?_⟩
  · rw [show -((1 : ℝ) + 1) = -(2 : ℝ) by norm_num] at hy1
    exact hy1.2
  · rw [show -((1 : ℝ) + 2) = -(3 : ℝ) by norm_num] at h2
    exact h2

theorem phaseDeriv_contDiff (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) :
    ContDiff ℝ 1 (fun y => deriv (fun β => fieldOf P F β y) β₀) :=
  phaseDeriv_contDiff_of P F β₀ fun n hn h0 c =>
    ⟨mode_contDiff P hP F hF c n hn, mode_contDiff P hP (quarterTurnData F n) (quarterTurnData_isFieldData P F hF n h0) c n hn⟩

theorem phaseDeriv_far_bounds (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) :
    ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖deriv (fun β => fieldOf P F β y) β₀‖ ≤ C * ‖y‖ ^ (-(1 : ℝ)) ∧
        ‖fderiv ℝ (fun y => deriv (fun β => fieldOf P F β y) β₀) y‖ ≤ C * ‖y‖ ^ (-(2 : ℝ)) := by
  obtain ⟨C, R, h⟩ := farBall_sum (Set.univ : Set ℝ) F.modes (fun _ n z => phaseTerm P F β₀ n z) 1
    (fun n hn => phaseTerm_farBall P hP F hF β₀ n hn)
  obtain ⟨-, -, -, hb⟩ := h 0 (Set.mem_univ _)
  have heq : (fun y => deriv (fun β => fieldOf P F β y) β₀) = fun z => ∑ n ∈ F.modes, phaseTerm P F β₀ n z :=
    funext fun y => phaseDeriv_eq P F β₀ y
  refine ⟨R, C, fun y hy => ?_⟩
  obtain ⟨h1, -⟩ := hb y hy
  have hy1 := h1 y (Metric.mem_ball_self one_pos)
  rw [heq, phaseDeriv_eq P F β₀ y]
  refine ⟨hy1.1, ?_⟩
  rw [show -((1 : ℝ) + 1) = -(2 : ℝ) by norm_num] at hy1
  exact hy1.2

end FracCellInternal

end Breakdown

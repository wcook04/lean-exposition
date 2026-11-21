import Breakdown.FracCell.GivenProfilePowerFieldParts

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePower

open CellCert.GivenFields SteadyCert

private theorem memLp_decay {q : ENNReal} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) {a : ℝ}
    (ha : 3 < a * q.toReal) : MemLp (fun y : Space => (1 + ‖y‖) ^ (-a)) q volume := by
  have hm : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-a)) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  rw [← memLp_norm_rpow_iff (q := q) hm hq0 hqt, ENNReal.div_self hq0 hqt, memLp_one_iff_integrable]
  have h3 : ((Module.finrank ℝ Space : ℕ) : ℝ) < a * q.toReal := by simpa using ha
  refine (integrable_one_add_norm (μ := volume) h3).congr (Filter.Eventually.of_forall fun y => ?_)
  have h1 : 0 ≤ 1 + ‖y‖ := by positivity
  simp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg h1 _), ← Real.rpow_mul h1, neg_mul]

private theorem memLp_six_of_decay {f : Space → Space} (hf : Continuous f) (C : ℝ)
    (hC : ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ))) : MemLp f 6 volume := by
  have hg : MemLp (fun y : Space => (1 + ‖y‖) ^ (-(1 : ℝ))) 6 volume :=
    memLp_decay (by norm_num) (by norm_num) (by norm_num)
  exact (hg.const_mul C).of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (hC y).trans (Real.le_norm_self _))

private theorem weight_shift_le {y h : Space} (hh : ‖h‖ ≤ 1) :
    (1 + ‖y + h‖) ^ (-(3 : ℝ)) ≤ 8 * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  have h1 : 0 < 1 + ‖y + h‖ := by positivity
  have h2 : 0 < 1 + ‖y‖ := by positivity
  have hle : 1 + ‖y‖ ≤ 2 * (1 + ‖y + h‖) := by
    have := norm_sub_le (y + h) h
    rw [add_sub_cancel_right] at this
    linarith [norm_nonneg (y + h)]
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    inv_mul_eq_div, div_le_iff₀ (by positivity)]
  calc (1 + ‖y‖) ^ (3 : ℝ) ≤ (2 * (1 + ‖y + h‖)) ^ (3 : ℝ) :=
        Real.rpow_le_rpow h2.le hle (by norm_num)
    _ = 8 * (1 + ‖y + h‖) ^ (3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) h1.le]; norm_num

private theorem secondModulus_of_parts {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable H volume) (C : ℝ) (hC : ∀ y, ‖H y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)))
    (K : ℝ) (hK : ∀ h : Space, ‖h‖ ≤ 1 →
      ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖ ≤ K * ‖h‖) :
    MemLp H 2 volume ∧ ∃ C' : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C' * ‖h‖ := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hw : MemLp (fun y : Space => (1 + ‖y‖) ^ (-(3 : ℝ))) 2 volume :=
    memLp_decay (by norm_num) (by norm_num) (by norm_num)
  have hw2 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  refine ⟨(hw.const_mul C).of_le hm (Filter.Eventually.of_forall fun y => (hC y).trans (Real.le_norm_self _)),
    9 * C * K, fun h hh => ?_⟩
  have hmh : AEStronglyMeasurable (fun y => H (y + h)) volume :=
    hm.comp_measurePreserving (measurePreserving_add_right volume h)
  have hpt : ∀ y, ‖H (y + h) - H y‖ ≤ 9 * C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hwy : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc ‖H (y + h) - H y‖ ≤ ‖H (y + h)‖ + ‖H y‖ := norm_sub_le _ _
      _ ≤ C * (8 * (1 + ‖y‖) ^ (-(3 : ℝ))) + C * (1 + ‖y‖) ^ (-(3 : ℝ)) :=
          add_le_add ((hC _).trans (mul_le_mul_of_nonneg_left (weight_shift_le hh) hC0)) (hC y)
      _ = 9 * C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by ring
  have hsq : ∀ y : Space, (1 + ‖y‖) ^ (-(3 : ℝ)) * (1 + ‖y‖) ^ (-(3 : ℝ)) = (1 + ‖y‖) ^ (-(6 : ℝ)) := by
    intro y
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hint : Integrable (fun y => (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖) volume := by
    refine (hw2.const_mul (9 * C)).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (Measurable.aestronglyMeasurable (by fun_prop)).mul (hmh.sub hm).norm
    · have hwy : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by positivity) _
      rw [Real.norm_of_nonneg (mul_nonneg hwy (norm_nonneg _)), ← hsq y]
      calc (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖
          ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) * (9 * C * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hpt y) hwy
        _ = 9 * C * ((1 + ‖y‖) ^ (-(3 : ℝ)) * (1 + ‖y‖) ^ (-(3 : ℝ))) := by ring
  calc ∫ y, ‖H (y + h) - H y‖ ^ 2
      ≤ ∫ y, 9 * C * ((1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
          (hint.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [sq]
        calc ‖H (y + h) - H y‖ * ‖H (y + h) - H y‖ ≤ 9 * C * (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖ :=
              mul_le_mul_of_nonneg_right (hpt y) (norm_nonneg _)
          _ = 9 * C * ((1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖) := by ring
    _ = 9 * C * ∫ y, (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖H (y + h) - H y‖ := integral_const_mul _ _
    _ ≤ 9 * C * (K * ‖h‖) := mul_le_mul_of_nonneg_left (hK h hh) (by positivity)
    _ = 9 * C * K * ‖h‖ := by ring

private theorem coord_abs_le (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y i

private theorem div_norm_abs_le (y : Space) (i : Fin 3) : |y i / ‖y‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (coord_abs_le y i) (norm_nonneg y)

private theorem heightRatio_abs_le (y : Space) : |heightRatio y| ≤ 1 := div_norm_abs_le y 2

private theorem polarVecQ_abs_le (y : Space) (i : Fin 3) : |polarVecQ y i| ≤ 1 := by
  have h2 := heightRatio_abs_le y
  have hsq : heightRatio y ^ 2 ≤ 1 := by nlinarith [abs_nonneg (heightRatio y), sq_abs (heightRatio y)]
  fin_cases i
  · show |polarVecQ y 0| ≤ 1
    have e : polarVecQ y 0 = heightRatio y * (y 0 / ‖y‖) := by simp [polarVecQ, mul_div_assoc]
    rw [e, abs_mul]
    exact mul_le_one₀ h2 (abs_nonneg _) (div_norm_abs_le y 0)
  · show |polarVecQ y 1| ≤ 1
    have e : polarVecQ y 1 = heightRatio y * (y 1 / ‖y‖) := by simp [polarVecQ, mul_div_assoc]
    rw [e, abs_mul]
    exact mul_le_one₀ h2 (abs_nonneg _) (div_norm_abs_le y 1)
  · show |polarVecQ y 2| ≤ 1
    have e : polarVecQ y 2 = -(1 - heightRatio y ^ 2) := by simp [polarVecQ, qOf]
    rw [e, abs_neg, abs_le]
    constructor <;> nlinarith [sq_nonneg (heightRatio y)]

private theorem azimVecQ_abs_le (y : Space) (i : Fin 3) : |azimVecQ y i| ≤ 1 := by
  fin_cases i
  · show |azimVecQ y 0| ≤ 1
    have e : azimVecQ y 0 = -(y 1 / ‖y‖) := by simp [azimVecQ, neg_div]
    rw [e, abs_neg]
    exact div_norm_abs_le y 1
  · show |azimVecQ y 1| ≤ 1
    have e : azimVecQ y 1 = y 0 / ‖y‖ := by simp [azimVecQ]
    rw [e]
    exact div_norm_abs_le y 0
  · simp [azimVecQ]

private theorem ofComponents_norm_le (w : Fin 3 → ℝ) : ‖ofComponents w‖ ≤ |w 0| + |w 1| + |w 2| := by
  unfold ofComponents
  refine (norm_add₃_le).trans (le_of_eq ?_)
  simp [Real.norm_eq_abs]

private theorem modeTerm_norm_le {c a b d : ℂ} {r p q C s : ℝ} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ C * s)
    (hb : ‖b‖ ≤ C * s) (hd : ‖d‖ ≤ C * s) (hr : |r| ≤ 1) (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    ‖c * (a * (r : ℂ) + b * (p : ℂ) + d * (q : ℂ))‖ ≤ 3 * (C * s) := by
  rw [norm_mul, hc, one_mul]
  have hCst : 0 ≤ C * s := (norm_nonneg a).trans ha
  calc ‖a * (r : ℂ) + b * (p : ℂ) + d * (q : ℂ)‖ ≤ ‖a * (r : ℂ)‖ + ‖b * (p : ℂ)‖ + ‖d * (q : ℂ)‖ :=
        norm_add₃_le
    _ ≤ C * s * 1 + C * s * 1 + C * s * 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
    _ = 3 * (C * s) := by ring

private theorem chartT_nonneg (P : ChartParams) (hP : IsChartParams P) (y : Space) : 0 ≤ chartT P y :=
  div_nonneg (norm_nonneg y) (by linarith [norm_nonneg y, hP.L0_pos])

private theorem chartT_lt_one (P : ChartParams) (hP : IsChartParams P) (y : Space) : chartT P y < 1 :=
  (div_lt_one (by linarith [norm_nonneg y, hP.L0_pos])).2 (by linarith [hP.L0_pos])

private theorem one_sub_chartT_le (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    1 - chartT P y ≤ (P.L0 + 1) * (1 + ‖y‖) ^ (-(1 : ℝ)) := by
  have hL := hP.L0_pos
  have hy := norm_nonneg y
  have e : 1 - chartT P y = P.L0 / (‖y‖ + P.L0) := by
    unfold chartT
    field_simp
    ring
  rw [e, Real.rpow_neg_one, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem fieldOf_norm_le_of {P : ChartParams} {D : FieldData} {β : ℝ} (hP : IsChartParams P) (C : ℝ)
    (hC : ∀ n ∈ D.modes, ∀ t x : ℝ, 0 ≤ t → t < 1 → |x| ≤ 1 → ∀ k : Fin 3,
      ‖reducedField P D n β t x k‖ ≤ C * (1 - t)) :
    ∃ C' : ℝ, ∀ y : Space, ‖fieldOf P D β y‖ ≤ C' * (1 + ‖y‖) ^ (-(1 : ℝ)) := by
  refine ⟨3 * (D.modes.card * (3 * (max C 0))) * (P.L0 + 1), fun y => ?_⟩
  set t := chartT P y with ht
  have ht0 : 0 ≤ t := chartT_nonneg P hP y
  have ht1 : t < 1 := chartT_lt_one P hP y
  have hs : 0 ≤ 1 - t := by linarith
  have hC' : ∀ n ∈ D.modes, ∀ k : Fin 3,
      ‖reducedField P D n β t (heightRatio y) k‖ ≤ max C 0 * (1 - t) := fun n hn k =>
    (hC n hn t _ ht0 ht1 (heightRatio_abs_le y) k).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)
  have hdec : ‖((decayFactor P y : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold decayFactor chartS
    rw [abs_of_nonneg (Real.rpow_nonneg hs _)]
    exact Real.rpow_le_one hs (by linarith) (by linarith [hP.eps_pos])
  have hcomp : ∀ i : Fin 3, |((decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
      (reducedField P D n β t (heightRatio y) 0 * radialVec y i +
        reducedField P D n β t (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β t (heightRatio y) 2 * azimVecQ y i)).re| ≤
      D.modes.card * (3 * (max C 0 * (1 - t))) := by
    intro i
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hdec).trans ?_
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => ?_).trans (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
    exact modeTerm_norm_le (Complex.norm_exp_I_mul_ofReal _) (hC' n hn 0) (hC' n hn 1) (hC' n hn 2)
      (div_norm_abs_le y i) (polarVecQ_abs_le y i) (azimVecQ_abs_le y i)
  unfold fieldOf
  refine (ofComponents_norm_le _).trans ?_
  have h1 := one_sub_chartT_le P hP y
  have hK : 0 ≤ (D.modes.card : ℝ) * (3 * max C 0) := by positivity
  calc _ ≤ D.modes.card * (3 * (max C 0 * (1 - t))) + D.modes.card * (3 * (max C 0 * (1 - t))) +
        D.modes.card * (3 * (max C 0 * (1 - t))) := add_le_add (add_le_add (hcomp 0) (hcomp 1)) (hcomp 2)
    _ = 3 * (D.modes.card * (3 * max C 0)) * (1 - t) := by ring
    _ ≤ 3 * (D.modes.card * (3 * max C 0)) * ((P.L0 + 1) * (1 + ‖y‖) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

private theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  refine (List.length_filter_le _ _).trans ?_
  simp only [List.length_dropLast, List.length_drop]
  omega

private theorem polyEval_bound (Q : MvPolynomial (Fin 2) ℂ) : ∃ B : ℝ, ∀ t u : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ u → u ≤ 1 →
    ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] Q‖ ≤ B := by
  have hc : Continuous fun p : ℝ × ℝ => MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] Q :=
    (MvPolynomial.continuous_eval Q).comp ((Complex.continuous_ofReal.comp continuous_fst).matrixVecCons
      ((Complex.continuous_ofReal.comp continuous_snd).matrixVecCons continuous_const))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun t u h0 h1 h2 h3 => hB (t, u) ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩⟩

private theorem sign_norm_le (odd : Bool) (x : ℝ) : ‖(if odd && decide (x < 0) then (-1 : ℂ) else 1)‖ ≤ 1 := by
  split_ifs <;> simp

private theorem spline_eval_bound (S : Spline) (odd : Bool) :
    ∃ B : ℝ, ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖S.eval odd t x‖ ≤ B := by
  choose Bq hBq using polyEval_bound
  refine ⟨∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
    max (Bq (S.piece i j)) 0, ?_⟩
  intro t x h0 h1 hx
  unfold Spline.eval Spline.evalHalf
  rw [norm_mul]
  have hi := Nat.lt_succ_of_le (cellIndex_le S.mesh.tBreaks t)
  have hj := Nat.lt_succ_of_le (cellIndex_le S.mesh.xBreaks |x|)
  have hb := hBq (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|)) t |x| h0 h1 (abs_nonneg x) hx
  have hsum : max (Bq (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|))) 0 ≤
      ∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
        max (Bq (S.piece i j)) 0 :=
    (Finset.single_le_sum (f := fun j => max (Bq (S.piece (cellIndex S.mesh.tBreaks t) j)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_range.2 hj)).trans
    (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1), max (Bq (S.piece i j)) 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_range.2 hi))
  calc _ ≤ 1 * max (Bq (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|))) 0 :=
        mul_le_mul (sign_norm_le odd x) (hb.trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hsum

private theorem polyEval_contDiff (Q : MvPolynomial (Fin 2) ℂ) {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => MvPolynomial.eval ![(f p : ℂ), (g p : ℂ)] Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp hf
    · exact Complex.ofRealCLM.contDiff.comp hg

private theorem partial_bound {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (v : ℝ × ℝ) (a b c d : ℝ) :
    ∃ M : ℝ, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, ‖fderiv ℝ F p v‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF.continuous_fderiv (by norm_num)).continuousOn
  exact ⟨M * ‖v‖, fun p hp => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hM p hp) (norm_nonneg _))⟩

private theorem deriv_first_eq {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (t u : ℝ) :
    HasDerivAt (fun t' => F (t', u)) (fderiv ℝ F (t, u) (1, 0)) t := by
  have hd : HasDerivAt (fun t' : ℝ => (t', u)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
  exact ((hF.differentiable (by norm_num)) (t, u)).hasFDerivAt.comp_hasDerivAt t hd

private theorem tweight_bound {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ M : ℝ, ∀ t u : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ u → u ≤ 1 →
      ‖deriv (fun t' => (w t' : ℂ) * MvPolynomial.eval ![(t' : ℂ), (u : ℂ)] Q) t‖ ≤ M ∧
        DifferentiableAt ℝ (fun t' => (w t' : ℂ) * MvPolynomial.eval ![(t' : ℂ), (u : ℂ)] Q) t := by
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => (w p.1 : ℂ) * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] Q) :=
    (Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_fst)).mul (polyEval_contDiff Q contDiff_fst contDiff_snd)
  obtain ⟨M, hM⟩ := partial_bound hF (1, 0) 0 1 0 1
  refine ⟨M, fun t u h0 h1 h2 h3 => ⟨?_, (deriv_first_eq hF t u).differentiableAt⟩⟩
  rw [(deriv_first_eq hF t u).deriv]
  exact hM (t, u) ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩

private theorem filter_le_eventually (L : List ℝ) (u : ℝ) : ∃ δ > 0, ∀ v, u ≤ v → v < u + δ →
    L.filter (fun b => decide (b ≤ v)) = L.filter (fun b => decide (b ≤ u)) := by
  induction L with
  | nil => exact ⟨1, one_pos, fun _ _ _ => rfl⟩
  | cons b L ih =>
    obtain ⟨δ, hδ, hL⟩ := ih
    by_cases hb : b ≤ u
    · refine ⟨δ, hδ, fun v hv1 hv2 => ?_⟩
      rw [List.filter_cons, List.filter_cons, hL v hv1 hv2]
      simp [hb, le_trans hb hv1]
    · rw [not_le] at hb
      refine ⟨min δ (b - u), lt_min hδ (by linarith), fun v hv1 hv2 => ?_⟩
      have hv3 : v < b := by linarith [min_le_right δ (b - u)]
      rw [List.filter_cons, List.filter_cons, hL v hv1 (by linarith [min_le_left δ (b - u)])]
      simp [not_le.2 hb, not_le.2 hv3]

private theorem cellIndex_eventually (l : List ℝ) (u : ℝ) : ∃ δ > 0, ∀ v, u ≤ v → v < u + δ →
    cellIndex l v = cellIndex l u := by
  obtain ⟨δ, hδ, h⟩ := filter_le_eventually ((l.drop 1).dropLast) u
  exact ⟨δ, hδ, fun v h1 h2 => by unfold cellIndex; rw [h v h1 h2]⟩

private theorem norm_deriv_le_of_eqOn_Ici {g q : ℝ → ℂ} {t δ : ℝ} (hδ : 0 < δ)
    (hq : DifferentiableAt ℝ q t) (heq : ∀ s, t ≤ s → s < t + δ → g s = q s) :
    ‖deriv g t‖ ≤ ‖deriv q t‖ := by
  by_cases hg : DifferentiableAt ℝ g t
  · have h1 : HasDerivWithinAt q (deriv g t) (Set.Ici t) t := by
      refine hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq ?_ (heq t le_rfl (by linarith)).symm
      filter_upwards [Ico_mem_nhdsGE (by linarith : t < t + δ)] with s hs
      exact (heq s hs.1 hs.2).symm
    rw [(uniqueDiffWithinAt_Ici t).eq_deriv _ h1 hq.hasDerivAt.hasDerivWithinAt]
  · rw [deriv_zero_of_not_differentiableAt hg, norm_zero]
    exact norm_nonneg _

private theorem spline_tderiv_bound (S : Spline) (odd : Bool) {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) :
    ∃ B : ℝ, ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖deriv (fun t' => (w t' : ℂ) * S.eval odd t' x) t‖ ≤ B := by
  choose Bq hBq using tweight_bound hw
  refine ⟨∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
    max (Bq (S.piece i j)) 0, ?_⟩
  intro t x h0 h1 hx
  have hi := Nat.lt_succ_of_le (cellIndex_le S.mesh.tBreaks t)
  have hj := Nat.lt_succ_of_le (cellIndex_le S.mesh.xBreaks |x|)
  set c : ℂ := if odd && decide (x < 0) then (-1 : ℂ) else 1 with hc
  set Q := S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|) with hQ
  obtain ⟨hb, hdiff⟩ := hBq Q t |x| h0 h1 (abs_nonneg x) hx
  obtain ⟨δ, hδ, hloc⟩ := cellIndex_eventually S.mesh.tBreaks t
  have hle : ‖deriv (fun t' => (w t' : ℂ) * S.eval odd t' x) t‖ ≤
      ‖deriv (fun t' => c * ((w t' : ℂ) * MvPolynomial.eval ![(t' : ℂ), ((|x| : ℝ) : ℂ)] Q)) t‖ := by
    refine norm_deriv_le_of_eqOn_Ici hδ (hdiff.const_mul c) fun s hs1 hs2 => ?_
    simp only [Spline.eval, Spline.evalHalf, hloc s hs1 hs2, hQ, hc]
    ring
  rw [deriv_const_mul_field', norm_mul] at hle
  have hsum : max (Bq Q) 0 ≤
      ∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
        max (Bq (S.piece i j)) 0 :=
    (Finset.single_le_sum (f := fun j => max (Bq (S.piece (cellIndex S.mesh.tBreaks t) j)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_range.2 hj)).trans
    (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1), max (Bq (S.piece i j)) 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_range.2 hi))
  calc _ ≤ _ := hle
    _ ≤ 1 * max (Bq Q) 0 := mul_le_mul (sign_norm_le odd x) (hb.trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hsum

private theorem norm_deriv_le_of_eqOn_Iic {g q : ℝ → ℂ} {t δ : ℝ} (hδ : 0 < δ)
    (hq : DifferentiableAt ℝ q t) (heq : ∀ s, t - δ < s → s ≤ t → g s = q s) :
    ‖deriv g t‖ ≤ ‖deriv q t‖ := by
  by_cases hg : DifferentiableAt ℝ g t
  · have h1 : HasDerivWithinAt q (deriv g t) (Set.Iic t) t := by
      refine hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq ?_ (heq t (by linarith) le_rfl).symm
      filter_upwards [Ioc_mem_nhdsLE (by linarith : t - δ < t)] with s hs
      exact (heq s hs.1 hs.2).symm
    rw [(uniqueDiffWithinAt_Iic t).eq_deriv _ h1 hq.hasDerivAt.hasDerivWithinAt]
  · rw [deriv_zero_of_not_differentiableAt hg, norm_zero]
    exact norm_nonneg _

private theorem deriv_second_eq {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (t u : ℝ) :
    HasDerivAt (fun u' => F (t, u')) (fderiv ℝ F (t, u) (0, 1)) u := by
  have hd : HasDerivAt (fun u' : ℝ => (t, u')) ((0 : ℝ), (1 : ℝ)) u :=
    (hasDerivAt_const u t).prodMk (hasDerivAt_id u)
  exact ((hF.differentiable (by norm_num)) (t, u)).hasFDerivAt.comp_hasDerivAt u hd

private theorem xweight_bound {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (σ : ℝ) (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ M : ℝ, ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖deriv (fun x' => (w x' : ℂ) * MvPolynomial.eval ![(t : ℂ), ((σ * x' : ℝ) : ℂ)] Q) x‖ ≤ M ∧
        DifferentiableAt ℝ (fun x' => (w x' : ℂ) * MvPolynomial.eval ![(t : ℂ), ((σ * x' : ℝ) : ℂ)] Q) x := by
  have hσ : ContDiff ℝ 1 (fun p : ℝ × ℝ => σ * p.2) := (contDiff_const (c := σ)).mul contDiff_snd
  have hG : ContDiff ℝ 1 (fun p : ℝ × ℝ => MvPolynomial.eval ![(p.1 : ℂ), ((σ * p.2 : ℝ) : ℂ)] Q) :=
    polyEval_contDiff Q contDiff_fst hσ
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => (w p.2 : ℂ) * MvPolynomial.eval ![(p.1 : ℂ), ((σ * p.2 : ℝ) : ℂ)] Q) :=
    (Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)).mul hG
  obtain ⟨M, hM⟩ := partial_bound hF (0, 1) 0 1 (-1) 1
  refine ⟨M, fun t x h0 h1 hx => ⟨?_, (deriv_second_eq hF t x).differentiableAt⟩⟩
  rw [(deriv_second_eq hF t x).deriv]
  exact hM (t, x) ⟨⟨h0, h1⟩, abs_le.1 hx⟩

private theorem spline_xderiv_bound (S : Spline) (odd : Bool) {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) :
    ∃ B : ℝ, ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖deriv (fun x' => (w x' : ℂ) * S.eval odd t x') x‖ ≤ B := by
  choose Bp hBp using xweight_bound hw 1
  choose Bm hBm using xweight_bound hw (-1)
  refine ⟨∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
    (max (Bp (S.piece i j)) 0 + max (Bm (S.piece i j)) 0), ?_⟩
  intro t x h0 h1 hx
  have hi := Nat.lt_succ_of_le (cellIndex_le S.mesh.tBreaks t)
  have hj := Nat.lt_succ_of_le (cellIndex_le S.mesh.xBreaks |x|)
  set c : ℂ := if odd && decide (x < 0) then (-1 : ℂ) else 1 with hc
  set Q := S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|) with hQ
  have hsum : max (Bp Q) 0 + max (Bm Q) 0 ≤
      ∑ i ∈ Finset.range (S.mesh.tBreaks.length + 1), ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
        (max (Bp (S.piece i j)) 0 + max (Bm (S.piece i j)) 0) :=
    (Finset.single_le_sum (f := fun j => max (Bp (S.piece (cellIndex S.mesh.tBreaks t) j)) 0 +
        max (Bm (S.piece (cellIndex S.mesh.tBreaks t) j)) 0)
      (fun _ _ => add_nonneg (le_max_right _ _) (le_max_right _ _)) (Finset.mem_range.2 hj)).trans
    (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (S.mesh.xBreaks.length + 1),
        (max (Bp (S.piece i j)) 0 + max (Bm (S.piece i j)) 0))
      (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (le_max_right _ _) (le_max_right _ _))
      (Finset.mem_range.2 hi))
  have hc1 : ‖c‖ ≤ 1 := sign_norm_le odd x
  by_cases hx0 : 0 ≤ x
  · obtain ⟨hb, hdiff⟩ := hBp Q t x h0 h1 hx
    obtain ⟨δ, hδ, hloc⟩ := cellIndex_eventually S.mesh.xBreaks x
    have hle : ‖deriv (fun x' => (w x' : ℂ) * S.eval odd t x') x‖ ≤
        ‖deriv (fun x' => (w x' : ℂ) * MvPolynomial.eval ![(t : ℂ), ((1 * x' : ℝ) : ℂ)] Q) x‖ := by
      refine norm_deriv_le_of_eqOn_Ici hδ hdiff fun s hs1 hs2 => ?_
      have hs0 : 0 ≤ s := le_trans hx0 hs1
      have hcs : cellIndex S.mesh.xBreaks |s| = cellIndex S.mesh.xBreaks |x| := by
        rw [abs_of_nonneg hs0, abs_of_nonneg hx0]
        exact hloc s hs1 hs2
      simp only [Spline.eval, Spline.evalHalf, hcs, hQ]
      rw [abs_of_nonneg hs0]
      simp [not_lt.2 hs0]
    calc _ ≤ _ := hle
      _ ≤ max (Bp Q) 0 + max (Bm Q) 0 := hb.trans ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _)))
      _ ≤ _ := hsum
  · rw [not_le] at hx0
    obtain ⟨hb, hdiff⟩ := hBm Q t x h0 h1 hx
    obtain ⟨δ, hδ, hloc⟩ := cellIndex_eventually S.mesh.xBreaks |x|
    have hδ' : 0 < min δ (-x) := lt_min hδ (by linarith)
    have hle : ‖deriv (fun x' => (w x' : ℂ) * S.eval odd t x') x‖ ≤
        ‖deriv (fun x' => c * ((w x' : ℂ) * MvPolynomial.eval ![(t : ℂ), ((-1 * x' : ℝ) : ℂ)] Q)) x‖ := by
      refine norm_deriv_le_of_eqOn_Iic hδ' (hdiff.const_mul c) fun s hs1 hs2 => ?_
      have hsneg : s < 0 := lt_of_le_of_lt hs2 hx0
      have hcs : cellIndex S.mesh.xBreaks |s| = cellIndex S.mesh.xBreaks |x| := by
        rw [abs_of_neg hsneg]
        refine hloc (-s) (by rw [abs_of_neg hx0]; linarith) ?_
        rw [abs_of_neg hx0]
        linarith [min_le_left δ (-x)]
      simp only [Spline.eval, Spline.evalHalf, hcs, hQ, hc]
      rw [abs_of_neg hsneg]
      simp [hsneg, hx0]
    rw [deriv_const_mul_field', norm_mul] at hle
    calc _ ≤ _ := hle
      _ ≤ 1 * max (Bm Q) 0 := mul_le_mul hc1 (hb.trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
      _ ≤ max (Bp Q) 0 + max (Bm Q) 0 := by rw [one_mul]; exact le_add_of_nonneg_left (le_max_right _ _)
      _ ≤ _ := hsum

private theorem weightPoly_norm_le (lo : ℕ) {e : ℕ} (he : e ≠ 0) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖weightPoly lo e t‖ ≤ 1 - t := by
  unfold weightPoly
  have hs : 0 ≤ 1 - t := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg hs _))]
  calc t ^ lo * (1 - t) ^ e ≤ 1 * (1 - t) := mul_le_mul (pow_le_one₀ h0 h1)
        (pow_le_of_le_one hs (by linarith) he) (pow_nonneg hs _) zero_le_one
    _ = 1 - t := one_mul _

private theorem coreRatioT_abs_le (P : ChartParams) (t : ℝ) : |coreRatioT P t| ≤ 1 := by
  unfold coreRatioT
  have ha : 0 ≤ P.L0 ^ 2 * t ^ 2 := by positivity
  have hb : 0 ≤ P.rc ^ 2 * (1 - t) ^ 2 := by positivity
  rw [abs_of_nonneg (div_nonneg ha (by linarith))]
  exact div_le_one_of_le₀ (by linarith) (by linarith)

private theorem axisFactor_norm_le (a : ℕ) {x : ℝ} (hx : |x| ≤ 1) : ‖((1 - x ^ 2 : ℝ) : ℂ) ^ a‖ ≤ 1 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  exact pow_le_one₀ (abs_nonneg _) (by rw [abs_le]; constructor <;> nlinarith [sq_nonneg x])

private theorem twistedScale_norm_le {P : ChartParams} (hP : IsChartParams P) (n : ℤ) (β : ℝ)
    (f : ℝ → ℝ → ℂ) {t x Bd : ℝ} (h0 : 0 ≤ t) (h1 : t < 1)
    (hd : ‖deriv (fun t' => f t' x) t‖ ≤ Bd) :
    ‖twistedScale P n β f t x‖ ≤ (1 - t) * Bd + (|(n : ℝ)| * |β| + 1) * ‖f t x‖ := by
  unfold twistedScale radialScale
  have hr : ‖((t * (1 - t) : ℝ) : ℂ)‖ ≤ 1 - t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hc : ‖Complex.I * (((n : ℝ) * β * coreRatioT P t : ℝ) : ℂ) - ((2 * P.eps * t : ℝ) : ℂ)‖ ≤
      |(n : ℝ)| * |β| + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_mul]
    have hcr := coreRatioT_abs_le P t
    have h2 : |2 * P.eps * t| ≤ 1 := by
      rw [abs_of_nonneg (by nlinarith [hP.eps_pos])]
      nlinarith [hP.eps_lt, hP.eps_pos]
    have h3 : |(n : ℝ)| * |β| * |coreRatioT P t| ≤ |(n : ℝ)| * |β| :=
      mul_le_of_le_one_right (by positivity) hcr
    linarith
  calc _ ≤ ‖((t * (1 - t) : ℝ) : ℂ)‖ * ‖deriv (fun t' => f t' x) t‖ +
        ‖Complex.I * (((n : ℝ) * β * coreRatioT P t : ℝ) : ℂ) - ((2 * P.eps * t : ℝ) : ℂ)‖ * ‖f t x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ _ := add_le_add (mul_le_mul hr hd (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

private theorem norm_add_sub_le (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_sub_le (a + b) c
  have h2 := norm_add_le a b
  linarith

private theorem reducedField_mode_norm_le {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (β : ℝ)
    (he : D.highOrder ≠ 0) (n : ℤ) : ∃ C : ℝ, ∀ t x : ℝ, 0 ≤ t → t < 1 → |x| ≤ 1 → ∀ k : Fin 3,
      ‖reducedField P D n β t x k‖ ≤ C * (1 - t) := by
  by_cases hn : n = 0
  · subst hn
    obtain ⟨B₁, hB₁⟩ := spline_xderiv_bound (D.amp 0).streamAmp true
      (w := fun x' : ℝ => 1 - x' ^ 2) (by fun_prop)
    obtain ⟨B₂, hB₂⟩ := spline_tderiv_bound (D.amp 0).streamAmp true
      (w := fun t' : ℝ => t' ^ 1 * (1 - t') ^ D.highOrder) (by fun_prop)
    obtain ⟨B₃, hB₃⟩ := spline_eval_bound (D.amp 0).streamAmp true
    obtain ⟨B₄, hB₄⟩ := spline_eval_bound (D.amp 0).swirlAmp false
    have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 0 le_rfl zero_le_one (by simp))
    have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 0 le_rfl zero_le_one (by simp))
    have hB₃0 : 0 ≤ B₃ := (norm_nonneg _).trans (hB₃ 0 0 le_rfl zero_le_one (by simp))
    have hB₄0 : 0 ≤ B₄ := (norm_nonneg _).trans (hB₄ 0 0 le_rfl zero_le_one (by simp))
    refine ⟨B₁ + B₂ + (|β| + 3) * B₃ + B₄, ?_⟩
    intro t x ht0 ht1 hx k
    have hs : 0 ≤ 1 - t := by linarith
    have hp := weightPoly_norm_le 1 he ht0 ht1.le
    have hΨ := hB₃ t x ht0 ht1.le hx
    have hf : ‖weightPoly 1 D.highOrder t * (D.amp 0).streamAmp.eval true t x‖ ≤ (1 - t) * B₃ := by
      rw [norm_mul]; exact mul_le_mul hp hΨ (norm_nonneg _) hs
    have e0 : ‖-(weightPoly 1 D.highOrder t * heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) *
        (D.amp 0).streamAmp.eval true t' x') t x)‖ ≤ (1 - t) * B₁ := by
      rw [norm_neg, norm_mul]
      exact mul_le_mul hp (hB₁ t x ht0 ht1.le hx) (norm_nonneg _) hs
    have e1 : ‖-(twistedScale P 0 β (fun t' x' => weightPoly 1 D.highOrder t' *
        (D.amp 0).streamAmp.eval true t' x') t x +
          2 * (weightPoly 1 D.highOrder t * (D.amp 0).streamAmp.eval true t x))‖ ≤
        (1 - t) * B₂ + (|β| + 3) * ((1 - t) * B₃) := by
      rw [norm_neg]
      refine (norm_add_le _ _).trans ?_
      have h1 := twistedScale_norm_le hP 0 β (fun t' x' => weightPoly 1 D.highOrder t' *
        (D.amp 0).streamAmp.eval true t' x') ht0 ht1 (hB₂ t x ht0 ht1.le hx)
      have h2 : ‖(2 : ℂ) * (weightPoly 1 D.highOrder t * (D.amp 0).streamAmp.eval true t x)‖ ≤
          2 * ((1 - t) * B₃) := by
        have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [norm_mul, h22]; linarith
      simp only [Int.cast_zero, abs_zero, zero_mul, zero_add] at h1
      have h3 : 1 * ‖weightPoly 1 D.highOrder t * (D.amp 0).streamAmp.eval true t x‖ ≤ 1 * ((1 - t) * B₃) := by
        linarith
      nlinarith [abs_nonneg β, mul_nonneg (abs_nonneg β) (mul_nonneg hs hB₃0)]
    have e2 : ‖weightPoly 1 D.highOrder t * (D.amp 0).swirlAmp.eval false t x‖ ≤ (1 - t) * B₄ := by
      rw [norm_mul]; exact mul_le_mul hp (hB₄ t x ht0 ht1.le hx) (norm_nonneg _) hs
    have hfin : ∀ a : ℝ, 0 ≤ a → a ≤ (B₁ + B₂ + (|β| + 3) * B₃ + B₄) * (1 - t) →
        a ≤ (B₁ + B₂ + (|β| + 3) * B₃ + B₄) * (1 - t) := fun a _ h => h
    rw [reducedField, if_pos rfl]
    fin_cases k
    · refine e0.trans ?_
      nlinarith [mul_nonneg hs hB₂0, mul_nonneg hs hB₃0, mul_nonneg hs hB₄0, abs_nonneg β,
        mul_nonneg (abs_nonneg β) (mul_nonneg hs hB₃0)]
    · refine e1.trans ?_
      nlinarith [mul_nonneg hs hB₁0, mul_nonneg hs hB₄0]
    · refine e2.trans ?_
      nlinarith [mul_nonneg hs hB₁0, mul_nonneg hs hB₂0, mul_nonneg hs hB₃0, abs_nonneg β,
        mul_nonneg (abs_nonneg β) (mul_nonneg hs hB₃0)]

  · have hnm : ((n * (P.m : ℤ) : ℤ) : ℂ) ≠ 0 := by
      have : n * (P.m : ℤ) ≠ 0 := mul_ne_zero hn (by exact_mod_cast hP.m_pos.ne')
      exact_mod_cast this
    set K := ‖Complex.I / ((n * (P.m : ℤ) : ℤ) : ℂ)‖ with hK
    have hK0 : 0 ≤ K := norm_nonneg _
    obtain ⟨BR, hBR⟩ := spline_eval_bound (D.amp n).radialAmp false
    obtain ⟨Bθ, hBθ⟩ := spline_eval_bound (D.amp n).polarAmp true
    obtain ⟨Bt, hBt⟩ := spline_tderiv_bound (D.amp n).radialAmp false
      (w := fun t' : ℝ => t' ^ D.lowOrder n * (1 - t') ^ D.highOrder) (by fun_prop)
    obtain ⟨Bx, hBx⟩ := spline_xderiv_bound (D.amp n).polarAmp true
      (w := fun x' : ℝ => (1 - x' ^ 2) ^ (D.axisOrder n + 1)) (by fun_prop)
    have hBR0 : 0 ≤ BR := (norm_nonneg _).trans (hBR 0 0 le_rfl zero_le_one (by simp))
    have hBθ0 : 0 ≤ Bθ := (norm_nonneg _).trans (hBθ 0 0 le_rfl zero_le_one (by simp))
    have hBt0 : 0 ≤ Bt := (norm_nonneg _).trans (hBt 0 0 le_rfl zero_le_one (by simp))
    have hBx0 : 0 ≤ Bx := (norm_nonneg _).trans (hBx 0 0 le_rfl zero_le_one (by simp))
    refine ⟨BR + Bθ + K * (Bt + (|(n : ℝ)| * |β| + 3) * BR + Bx), ?_⟩
    intro t x ht0 ht1 hx k
    have hs : 0 ≤ 1 - t := by linarith
    have hp := weightPoly_norm_le (D.lowOrder n) he ht0 ht1.le
    have hc := axisFactor_norm_le (D.axisOrder n) hx
    have hur : ‖weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t x‖ ≤ (1 - t) * BR := by
      rw [norm_mul, norm_mul]
      calc _ ≤ (1 - t) * 1 * BR := mul_le_mul (mul_le_mul hp hc (norm_nonneg _) hs)
            (hBR t x ht0 ht1.le hx) (norm_nonneg _) (by positivity)
        _ = (1 - t) * BR := by ring
    have huθ : ‖weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t x‖ ≤ (1 - t) * Bθ := by
      rw [norm_mul, norm_mul]
      calc _ ≤ (1 - t) * 1 * Bθ := mul_le_mul (mul_le_mul hp hc (norm_nonneg _) hs)
            (hBθ t x ht0 ht1.le hx) (norm_nonneg _) (by positivity)
        _ = (1 - t) * Bθ := by ring
    have hdt : ‖deriv (fun t' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).radialAmp.eval false t' x) t‖ ≤ Bt := by
      have e : (fun t' => weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          (D.amp n).radialAmp.eval false t' x) = fun t' => ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          (((t' ^ D.lowOrder n * (1 - t') ^ D.highOrder : ℝ) : ℂ) * (D.amp n).radialAmp.eval false t' x) := by
        funext t'
        unfold weightPoly
        ring
      rw [e, deriv_const_mul_field', norm_mul]
      calc _ ≤ 1 * Bt := mul_le_mul hc (hBt t x ht0 ht1.le hx) (norm_nonneg _) zero_le_one
        _ = Bt := one_mul _
    have hdx : ‖heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x‖ ≤ (1 - t) * Bx := by
      unfold heightDeriv
      have e : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t *
          ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t x')) =
          fun x' => weightPoly (D.lowOrder n) D.highOrder t *
            ((((1 - x' ^ 2) ^ (D.axisOrder n + 1) : ℝ) : ℂ) * (D.amp n).polarAmp.eval true t x') := by
        funext x'
        push_cast
        ring
      rw [e, deriv_const_mul_field', norm_mul]
      exact mul_le_mul hp (hBx t x ht0 ht1.le hx) (norm_nonneg _) hs
    have htw := twistedScale_norm_le hP n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') ht0 ht1 hdt
    have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have e2 : ‖Complex.I / ((n * (P.m : ℤ) : ℤ) : ℂ) *
        (twistedScale P n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
          ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') t x +
          2 * (weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
            (D.amp n).radialAmp.eval false t x) -
          heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x)‖ ≤
        K * ((1 - t) * Bt + (|(n : ℝ)| * |β| + 3) * ((1 - t) * BR) + (1 - t) * Bx) := by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      refine (norm_add_sub_le _ _ _).trans ?_
      rw [norm_mul _ (weightPoly (D.lowOrder n) D.highOrder t * _ * _), h22]
      have hmn : 0 ≤ |(n : ℝ)| * |β| + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hur hmn]
    rw [reducedField, if_neg hn]
    fin_cases k
    · refine hur.trans ?_
      nlinarith [mul_nonneg hs hBθ0, mul_nonneg hK0 (mul_nonneg hs hBt0), mul_nonneg hK0 (mul_nonneg hs hBx0),
        mul_nonneg hK0 (mul_nonneg (mul_nonneg (abs_nonneg (n : ℝ)) (abs_nonneg β)) (mul_nonneg hs hBR0)),
        mul_nonneg hK0 (mul_nonneg hs hBR0)]
    · refine huθ.trans ?_
      nlinarith [mul_nonneg hs hBR0, mul_nonneg hK0 (mul_nonneg hs hBt0), mul_nonneg hK0 (mul_nonneg hs hBx0),
        mul_nonneg hK0 (mul_nonneg (mul_nonneg (abs_nonneg (n : ℝ)) (abs_nonneg β)) (mul_nonneg hs hBR0)),
        mul_nonneg hK0 (mul_nonneg hs hBR0)]
    · refine e2.trans ?_
      nlinarith [mul_nonneg hs hBR0, mul_nonneg hs hBθ0]

private theorem reducedField_norm_le_of {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (β : ℝ)
    (he : D.highOrder ≠ 0) : ∃ C : ℝ, ∀ n ∈ D.modes, ∀ t x : ℝ, 0 ≤ t → t < 1 → |x| ≤ 1 →
      ∀ k : Fin 3, ‖reducedField P D n β t x k‖ ≤ C * (1 - t) := by
  choose Cn hCn using fun n => reducedField_mode_norm_le hP D β he n
  refine ⟨∑ n ∈ D.modes, max (Cn n) 0, fun n hn t x ht0 ht1 hx k => ?_⟩
  refine (hCn n t x ht0 ht1 hx k).trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  exact (le_max_left _ _).trans
    (Finset.single_le_sum (f := fun n => max (Cn n) 0) (fun i _ => le_max_right _ _) hn)

theorem fieldOf_contDiff {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) : ContDiff ℝ 1 (fieldOf P D β) :=
  ProfilePowerParts.fieldOf_contDiff hP hD β

theorem fieldOf_memLp_six {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) : MemLp (fieldOf P D β) 6 volume := by
  obtain ⟨C₀, hC₀⟩ := reducedField_norm_le_of hP D β (by rw [hD.highOrder_eq]; norm_num)
  obtain ⟨C, hC⟩ := fieldOf_norm_le_of hP C₀ hC₀
  exact memLp_six_of_decay (fieldOf_contDiff hP hD β).continuous C hC

theorem fieldOf_second_modulus {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ H : Space → (Space →L[ℝ] Space →L[ℝ] Space),
      IsWeakSecondDerivOf (fun y => fderiv ℝ (fieldOf P D β) y) H ∧ MemLp H 2 volume ∧
        ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C * ‖h‖ := by
  obtain ⟨H, hH, hm, ⟨C, hC⟩, K, hK⟩ := ProfilePowerParts.fieldOf_second_parts hP hD β
  exact ⟨H, hH, secondModulus_of_parts hm C hC K hK⟩

end ProfilePower

end FracInternal

end Breakdown

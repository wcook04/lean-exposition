import Breakdown.FracCell.OffAxisCoreWeakSt
import Breakdown.FracCell.OffAxisCore
import Breakdown.FracCell.ModeOrthSame

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.OffAxisCoreGrad

open Internal.SpectralBlocksMode

theorem frame_expand (v : Space) (θ : ℝ) : v = ∑ d : Fin 3, inner ℝ (frameAt d θ) v • frameAt d θ := by
  have h := Real.cos_sq_add_sin_sq θ
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, frameAt, unitVector, PiLp.inner_apply]
  · linear_combination (-(v 0)) * h
  · linear_combination (-(v 1)) * h

theorem frame_energySum (v : Space) (θ : ℝ) : ‖v‖ ^ 2 = ∑ d : Fin 3, inner ℝ (frameAt d θ) v ^ 2 := by
  conv_lhs => rw [← real_inner_self_eq_norm_sq, frame_expand v θ]
  rw [inner_frame_sum]
  simp only [sq]

theorem std_energySum (v : Space) : ‖v‖ ^ 2 = ∑ i : Fin 3, inner ℝ (unitVector i) v ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← Internal.ModeOrthSame.coord_inner_sum v v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, sq]

theorem entrySq_frame (G : Space →L[ℝ] Space) (θ : ℝ) : entrySq G = ∑ d : Fin 3, ‖G (frameAt d θ)‖ ^ 2 := by
  unfold entrySq
  calc ∑ i : Fin 3, ‖G (unitVector i)‖ ^ 2
      = ∑ i : Fin 3, ∑ c : Fin 3, inner ℝ (frameAt c θ) (G (unitVector i)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => frame_energySum _ θ
    _ = ∑ c : Fin 3, ∑ i : Fin 3, inner ℝ (unitVector i) (ContinuousLinearMap.adjoint G (frameAt c θ)) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    _ = ∑ c : Fin 3, ∑ d : Fin 3, inner ℝ (frameAt d θ) (ContinuousLinearMap.adjoint G (frameAt c θ)) ^ 2 :=
        Finset.sum_congr rfl fun c _ => by rw [← std_energySum, frame_energySum _ θ]
    _ = ∑ d : Fin 3, ∑ c : Fin 3, inner ℝ (frameAt c θ) (G (frameAt d θ)) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    _ = ∑ d : Fin 3, ‖G (frameAt d θ)‖ ^ 2 :=
        Finset.sum_congr rfl fun d _ => (frame_energySum _ θ).symm

theorem clm_expand (G : Space →L[ℝ] Space) (θ : ℝ) :
    G = ∑ d : Fin 3, (innerSL ℝ (frameAt d θ)).smulRight (G (frameAt d θ)) := by
  ext1 v
  conv_lhs => rw [frame_expand v θ]
  simp [map_sum, map_smul, ContinuousLinearMap.smulRight_apply]

theorem column (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) (d : Fin 3) :
    shapeGradField g f y (frameVector d y) = shapeField g (fun s c t r z => f s c d t r z) y := by
  classical
  unfold shapeGradField shapeField
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ cellSolid g s
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [_root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, Internal.ModeOrthSame.frame_inner, smul_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    simp

theorem coef_cont (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hRin : 0 < g.innerRadius)
    (hQ : ∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) (s : Fin 2) (c d : Fin 3) (t : Fin 2) :
    Continuous fun p : ℝ × ℝ => shapeGradCoef g Q s c d t p.1 p.2 := by
  have hQc : ∀ s c t, Continuous fun p : ℝ × ℝ => Q s c t p.1 p.2 := fun s c t => (hQ s c t).continuous
  have hang : Continuous fun p : ℝ × ℝ => angularCoef g.mode Q s c t p.1 p.2 := by
    unfold angularCoef
    refine Continuous.add ?_ ?_
    · split_ifs
      · exact continuous_const.mul (hQc s c 1)
      · exact (continuous_const.mul (hQc s c 0)).neg
    · split_ifs
      · exact (hQc s 1 t).neg
      · exact hQc s 0 t
      · exact continuous_const
  unfold shapeGradCoef
  split_ifs
  · exact Internal.OffAxisCore.partial_r (hQ s c t)
  · exact ((continuous_fst.max continuous_const).inv₀ fun p =>
      (lt_of_lt_of_le hRin (le_max_right _ _)).ne').mul hang
  · exact Internal.OffAxisCore.partial_z (hQ s c t)

theorem weight_nonneg (m : ℕ) (t : Fin 2) : 0 ≤ trigWeight m t :=
  intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => sq_nonneg _

theorem weight_eq (m : ℕ) (hm : m ≠ 0) : trigWeight m 0 = trigWeight m 1 := by
  unfold trigWeight
  have h2 : ((2 * m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 2 * m ≠ 0)
  have hint := trig_int 0 ((2 * m : ℕ) : ℤ) h2
  have e : ∀ θ : ℝ, trigMode 0 ((((2 * m : ℕ) : ℤ) : ℝ) * θ)
      = trigMode 0 ((m : ℝ) * θ) ^ 2 - trigMode 1 ((m : ℝ) * θ) ^ 2 := by
    intro θ
    simp only [trigMode, if_true, one_ne_zero, if_false, Fin.isValue]
    push_cast
    rw [show 2 * (m : ℝ) * θ = 2 * ((m : ℝ) * θ) by ring, Real.cos_two_mul, Real.sin_sq]
    ring
  simp only [e] at hint
  have i0 : IntervalIntegrable (fun θ : ℝ => trigMode 0 ((m : ℝ) * θ) ^ 2) volume (-π) π :=
    ((trig_cont 0 _).pow 2).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun θ : ℝ => trigMode 1 ((m : ℝ) * θ) ^ 2) volume (-π) π :=
    ((trig_cont 1 _).pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i0 i1] at hint
  linarith

theorem ang_ineq (m : ℕ) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (s : Fin 2) (r z w0 w1 : ℝ)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : m = 0 ∨ w0 = w1) :
    ∑ c : Fin 3, (w0 * angularCoef m Q s c 0 r z ^ 2 + w1 * angularCoef m Q s c 1 r z ^ 2)
      ≤ ((m : ℝ) + 1) ^ 2 * ∑ c : Fin 3, (w0 * Q s c 0 r z ^ 2 + w1 * Q s c 1 r z ^ 2) := by
  simp only [Fin.sum_univ_three, angularCoef]
  simp
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases hw with h | h
  · subst h
    simp
    nlinarith [mul_nonneg hw0 (sq_nonneg (Q s 2 0 r z)), mul_nonneg hw1 (sq_nonneg (Q s 2 1 r z))]
  · subst h
    nlinarith [mul_nonneg hw0 (mul_nonneg hm (sq_nonneg (Q s 0 1 r z + Q s 1 0 r z))),
      mul_nonneg hw0 (mul_nonneg hm (sq_nonneg (Q s 1 1 r z - Q s 0 0 r z))),
      mul_nonneg hw0 (mul_nonneg hm (sq_nonneg (Q s 0 0 r z + Q s 1 1 r z))),
      mul_nonneg hw0 (mul_nonneg hm (sq_nonneg (Q s 0 1 r z - Q s 1 0 r z))),
      mul_nonneg hw0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * m + 1) (sq_nonneg (Q s 2 0 r z))),
      mul_nonneg hw0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * m + 1) (sq_nonneg (Q s 2 1 r z)))]

theorem rect_ct (w : Fin 2 → ℝ) (F : Fin 3 → Fin 2 → ℝ → ℝ → ℝ)
    (hF : ∀ c t, Continuous fun p : ℝ × ℝ => F c t p.1 p.2) (a b a' b' : ℝ) :
    ∑ c : Fin 3, ∑ t : Fin 2, w t * (∫ r in a..b, ∫ z in a'..b', F c t r z)
      = ∫ r in a..b, ∫ z in a'..b', ∑ c : Fin 3, ∑ t : Fin 2, w t * F c t r z := by
  rw [Internal.OffAxisCoreNorm.rect_sum _ _ (fun c => continuous_finsetSum _ fun t _ =>
    continuous_const.mul (hF c t))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Internal.OffAxisCoreNorm.rect_sum _ _ (fun t => continuous_const.mul (hF c t))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Internal.OffAxisCore.rect_mul]

def frameOuter (p : Space × Space) : Space →L[ℝ] Space := (innerSL ℝ p.1).smulRight p.2

theorem frameOuter_cont : Continuous frameOuter := by
  unfold frameOuter
  fun_prop

theorem inv_sq_mul {r : ℝ} (hr : r ≠ 0) (x : ℝ) : (r⁻¹ * x) ^ 2 * r = r⁻¹ * x ^ 2 := by
  field_simp

theorem shapeGrad_core (hW : ShapeWeakStatement) : ShapeGradStatement := by
  intro g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3
  have hfc := coef_cont g Q hRin hQc
  have hcolN := fun d : Fin 3 => shapeNorm_holds g (fun s c t r z => shapeGradCoef g Q s c d t r z)
    hRin hR hZ hZ0 fun s c t => hfc s c d t
  have hES : ∀ y, entrySq (shapeGradField g (shapeGradCoef g Q) y)
      = ∑ d : Fin 3, ‖shapeField g (fun s c t r z => shapeGradCoef g Q s c d t r z) y‖ ^ 2 := by
    intro y
    rw [entrySq_frame _ (angleCoord y)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← frame_eq, column]
  have hDexp : shapeGradField g (shapeGradCoef g Q) = fun y => ∑ d : Fin 3,
      frameOuter (frameVector d y, shapeField g (fun s c t r z => shapeGradCoef g Q s c d t r z) y) := by
    funext y
    rw [clm_expand (shapeGradField g (shapeGradCoef g Q) y) (angleCoord y)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← frame_eq, column]
    rfl
  have hDm : AEStronglyMeasurable (shapeGradField g (shapeGradCoef g Q)) volume := by
    have hterm : ∀ d : Fin 3, AEStronglyMeasurable (fun y => frameOuter (frameVector d y,
        shapeField g (fun s c t r z => shapeGradCoef g Q s c d t r z) y)) volume := by
      intro d
      have hpair : AEStronglyMeasurable (fun y => (frameVector d y,
          shapeField g (fun s c t r z => shapeGradCoef g Q s c d t r z) y)) volume :=
        (Internal.SpectralBlocks.frame_meas d).aestronglyMeasurable.prodMk (hcolN d).1.1
      exact frameOuter_cont.comp_aestronglyMeasurable hpair
    rw [hDexp]
    exact Finset.aestronglyMeasurable_fun_sum _ fun d _ => hterm d
  have hsq : ∀ d : Fin 3, Integrable fun y =>
      ‖shapeField g (fun s c t r z => shapeGradCoef g Q s c d t r z) y‖ ^ 2 := fun d =>
    (memLp_two_iff_integrable_sq_norm (hcolN d).1.1).1 (hcolN d).1
  have hDi : Integrable (fun y => entrySq (shapeGradField g (shapeGradCoef g Q) y)) := by
    simp only [hES]
    exact integrable_finsetSum _ fun d _ => hsq d
  refine ⟨shapeGradField g (shapeGradCoef g Q), hDm, hDi, hW g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3,
    ⟨shapeGradCoef g Q, fun s c d t => (hfc s c d t).measurable, fun y => rfl⟩, ?_⟩
  simp only [hES]
  rw [integral_finsetSum _ fun d _ => hsq d, Finset.sum_congr rfl fun d _ => (hcolN d).2, Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ => ?_
  have hpZ : solidLower g s ≤ solidUpper g s := by
    fin_cases s
    · simp [solidLower, solidUpper]
      linarith
    · simp only [solidLower, solidUpper]
      simp
      linarith
  have hQcont : ∀ c t, Continuous fun p : ℝ × ℝ => Q s c t p.1 p.2 := fun c t => (hQc s c t).continuous
  have hG : ∀ c t, Continuous fun p : ℝ × ℝ => (deriv (fun x => Q s c t x p.2) p.1 ^ 2
      + deriv (fun w => Q s c t p.1 w) p.2 ^ 2
      + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t p.1 p.2 ^ 2) * p.1 := fun c t =>
    ((((Internal.OffAxisCore.partial_r (hQc s c t)).pow 2).add
      ((Internal.OffAxisCore.partial_z (hQc s c t)).pow 2)).add
      (continuous_const.mul ((hQcont c t).pow 2))).mul continuous_fst
  have hF : ∀ d c t, Continuous fun p : ℝ × ℝ => shapeGradCoef g Q s c d t p.1 p.2 ^ 2 * p.1 :=
    fun d c t => ((hfc s c d t).pow 2).mul continuous_fst
  have hw : g.mode = 0 ∨ trigWeight g.mode 0 = trigWeight g.mode 1 := by
    by_cases hm : g.mode = 0
    · exact Or.inl hm
    · exact Or.inr (weight_eq g.mode hm)
  calc ∑ d : Fin 3, ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t *
          ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            shapeGradCoef g Q s c d t r z ^ 2 * r
        = ∑ d : Fin 3, ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * (shapeGradCoef g Q s c d t r z ^ 2 * r) :=
        Finset.sum_congr rfl fun d _ => rect_ct (trigWeight g.mode)
          (fun c t r z => shapeGradCoef g Q s c d t r z ^ 2 * r) (hF d) _ _ _ _
    _ = ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s, ∑ d : Fin 3,
            ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * (shapeGradCoef g Q s c d t r z ^ 2 * r) :=
        (Internal.OffAxisCoreNorm.rect_sum _ _ (fun d => continuous_finsetSum _ fun c _ =>
          continuous_finsetSum _ fun t _ => continuous_const.mul (hF d c t)) _ _ _ _).symm
    _ ≤ ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t * ((deriv (fun x => Q s c t x z) r ^ 2
              + deriv (fun w => Q s c t r w) z ^ 2
              + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r) := by
        refine Internal.OffAxisCore.rect_mono ?_ ?_ hR.le hpZ fun r hr z _ => ?_
        · exact continuous_finsetSum _ fun d _ => continuous_finsetSum _ fun c _ =>
            continuous_finsetSum _ fun t _ => continuous_const.mul (hF d c t)
        · exact continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun t _ =>
            continuous_const.mul (hG c t)
        have hr0 : 0 < r := lt_of_lt_of_le hRin hr.1
        have hmax : max r g.innerRadius = r := max_eq_left hr.1
        have hang := ang_ineq g.mode Q s r z (trigWeight g.mode 0) (trigWeight g.mode 1)
          (weight_nonneg _ _) (weight_nonneg _ _) hw
        have hY : 0 ≤ ∑ c : Fin 3, (trigWeight g.mode 0 * Q s c 0 r z ^ 2 + trigWeight g.mode 1 * Q s c 1 r z ^ 2) :=
          Finset.sum_nonneg fun c _ => add_nonneg (mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
            (mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
        have hrinv : r⁻¹ ≤ r / g.innerRadius ^ 2 := by
          rw [inv_eq_one_div, div_le_div_iff₀ hr0 (by positivity)]
          nlinarith [hr.1]
        have key : r⁻¹ * ∑ c : Fin 3, (trigWeight g.mode 0 * angularCoef g.mode Q s c 0 r z ^ 2
            + trigWeight g.mode 1 * angularCoef g.mode Q s c 1 r z ^ 2)
            ≤ (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * (r * ∑ c : Fin 3,
              (trigWeight g.mode 0 * Q s c 0 r z ^ 2 + trigWeight g.mode 1 * Q s c 1 r z ^ 2)) := by
          calc _ ≤ r⁻¹ * (((g.mode : ℝ) + 1) ^ 2 * ∑ c : Fin 3,
                (trigWeight g.mode 0 * Q s c 0 r z ^ 2 + trigWeight g.mode 1 * Q s c 1 r z ^ 2)) :=
                mul_le_mul_of_nonneg_left hang (inv_nonneg.2 hr0.le)
            _ ≤ r / g.innerRadius ^ 2 * (((g.mode : ℝ) + 1) ^ 2 * ∑ c : Fin 3,
                (trigWeight g.mode 0 * Q s c 0 r z ^ 2 + trigWeight g.mode 1 * Q s c 1 r z ^ 2)) :=
                mul_le_mul_of_nonneg_right hrinv (mul_nonneg (sq_nonneg _) hY)
            _ = _ := by ring
        simp only [Fin.sum_univ_three, Fin.sum_univ_two] at key ⊢
        simp (config := { decide := true }) only [shapeGradCoef, hmax, ↓reduceIte,
          inv_sq_mul hr0.ne']
        linarith [key]
    _ = ∑ c : Fin 3, ∑ t : Fin 2, trigWeight g.mode t *
          ∫ r in g.innerRadius..g.outerRadius, ∫ z in solidLower g s..solidUpper g s,
            (deriv (fun x => Q s c t x z) r ^ 2 + deriv (fun w => Q s c t r w) z ^ 2
              + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r :=
        (rect_ct (trigWeight g.mode) (fun c t r z => (deriv (fun x => Q s c t x z) r ^ 2
          + deriv (fun w => Q s c t r w) z ^ 2
          + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 * Q s c t r z ^ 2) * r) hG _ _ _ _).symm

end Internal.OffAxisCoreGrad

theorem shapeGrad_of_weak (hW : ShapeWeakStatement) : ShapeGradStatement :=
  Internal.OffAxisCoreGrad.shapeGrad_core hW

theorem offAxisCore_of_weak (h : RectOffStatement) (hW : ShapeWeakStatement) : OffAxisCoreStatement :=
  offAxisCore_of_grad h (shapeGrad_of_weak hW)

end Spectral

end CellCert

end Breakdown

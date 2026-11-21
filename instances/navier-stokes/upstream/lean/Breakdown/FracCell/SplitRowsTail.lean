import Breakdown.FracCell.Defs

open MeasureTheory Real Set intervalIntegral

noncomputable section

namespace Breakdown

namespace CellCert

namespace Internal.SplitRowsTail

theorem tail_real {s c x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 < c) (hcx : c ≤ x) :
    x ^ s - c ^ s ≤ ∫ l in c..x * x / c, s * l ^ (s - 1) * (x / (l + x)) := by
  have hx : 0 < x := hc.trans_le hcx
  set g : ℝ → ℝ := fun l => s * l ^ (s - 1) * (x / (l + x)) with hg
  set b := x * x / c with hb
  have hxb : x ≤ b := by
    rw [hb, le_div_iff₀ hc]
    nlinarith
  have hgc : ContinuousOn g (Ioi 0) := by
    intro μ hμ
    have hμ : (0 : ℝ) < μ := hμ
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hμ.ne')))
    exact continuousAt_const.div (continuousAt_id.add continuousAt_const) (by linarith)
  have hpos : ∀ l ∈ uIcc c x, 0 < l := by
    intro l hl
    rw [uIcc_of_le hcx] at hl
    exact hc.trans_le hl.1
  have hpos2 : ∀ l ∈ uIcc x b, 0 < l := by
    intro l hl
    rw [uIcc_of_le hxb] at hl
    exact hx.trans_le hl.1
  have Ig1 : IntervalIntegrable g volume c x :=
    (hgc.mono fun l hl => hpos l hl).intervalIntegrable
  have Ig2 : IntervalIntegrable g volume x b :=
    (hgc.mono fun l hl => hpos2 l hl).intervalIntegrable
  set f : ℝ → ℝ := fun l => x * x / l with hf
  set f' : ℝ → ℝ := fun l => -(x * x) / l ^ 2 with hf'
  have hfc : ContinuousOn f (uIcc c x) := by
    intro l hl
    exact (continuousAt_const.div continuousAt_id (hpos l hl).ne').continuousWithinAt
  have hf'c : ContinuousOn f' (uIcc c x) := by
    intro l hl
    exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 (hpos l hl).ne')).continuousWithinAt
  have hmaps : MapsTo f (uIcc c x) (Ioi 0) := by
    intro l hl
    have := hpos l hl
    show 0 < x * x / l
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv'' (f := f) (f' := f') (g := g) hfc
    (fun l hl => by
      have hl0 : 0 < l := by
        have := hl.1
        rw [min_eq_left hcx] at this
        exact hc.trans this
      have hd : HasDerivAt f (f' l) l := by
        have h2 := (hasDerivAt_inv hl0.ne').const_mul (x * x)
        have e1 : f = fun y => x * x * y⁻¹ := by
          rw [hf]
          funext y
          rw [div_eq_mul_inv]
        have e2 : f' l = x * x * -(l ^ 2)⁻¹ := by
          simp only [hf']
          ring
        rw [e1, e2]
        exact h2
      exact hd.hasDerivWithinAt) hf'c (hgc.mono (by
        rintro _ ⟨l, hl, rfl⟩
        exact hmaps hl))
  have efc : f c = b := rfl
  have efx : f x = x := by
    show x * x / x = x
    field_simp
  rw [efc, efx] at hsub
  have e2 : ∫ l in x..b, g l = ∫ l in c..x, g (f l) * (x * x / l ^ 2) := by
    rw [intervalIntegral.integral_symm b x, ← hsub, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun l _ => ?_
    show -(g (f l) * (-(x * x) / l ^ 2)) = g (f l) * (x * x / l ^ 2)
    ring
  have hpow : ∀ l ∈ Icc c x, s * l ^ s / (l + x) ≤ g (f l) * (x * x / l ^ 2) := by
    intro l hl
    have hl0 : 0 < l := hc.trans_le hl.1
    have hA : 0 < l ^ s := Real.rpow_pos_of_pos hl0 s
    have hAu : l ^ s ≤ x ^ s := Real.rpow_le_rpow hl0.le hl.2 hs0.le
    have hu : 0 < x ^ s := Real.rpow_pos_of_pos hx s
    have e3 : g (f l) * (x * x / l ^ 2) = s * (x ^ s * x ^ s) / (l ^ s * (l + x)) := by
      simp only [hg, hf]
      rw [Real.rpow_sub_one (by positivity), Real.div_rpow (by positivity) hl0.le,
        Real.mul_rpow hx.le hx.le]
      field_simp
      ring
    rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
    have : l ^ s * l ^ s ≤ x ^ s * x ^ s := mul_le_mul hAu hAu hA.le hu.le
    have hs' : 0 < s * (l + x) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hs'.le]
  have Ih : IntervalIntegrable (fun l => s * l ^ s / (l + x)) volume c x := by
    refine ContinuousOn.intervalIntegrable fun l hl => ?_
    have hl0 := hpos l hl
    exact ((continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hl0.ne'))).div
      (continuousAt_id.add continuousAt_const) (by show l + x ≠ 0; linarith)).continuousWithinAt
  have Ik : IntervalIntegrable (fun l => g (f l) * (x * x / l ^ 2)) volume c x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (hgc.comp hfc hmaps).mul ?_
    intro l hl
    exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 (hpos l hl).ne')).continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on hcx Ih Ik hpow
  have erp : ∫ l in c..x, s * l ^ (s - 1) = x ^ s - c ^ s := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have : s - 1 + 1 = s := by ring
    rw [this]
    field_simp
  have esplit : ∫ l in c..x, s * l ^ (s - 1) = (∫ l in c..x, g l) + ∫ l in c..x, s * l ^ s / (l + x) := by
    rw [← intervalIntegral.integral_add Ig1 Ih]
    refine intervalIntegral.integral_congr fun l hl => ?_
    have hl0 := hpos l hl
    simp only [hg]
    rw [Real.rpow_sub_one hl0.ne']
    field_simp
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals Ig1 Ig2, e2, ← erp, esplit]
  linarith

end Internal.SplitRowsTail

end CellCert

end Breakdown

import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Trilinear

theorem norm_sum_le_pointwise (a : Space) (b : Fin 3 → Space) (c : Space) :
    ‖∑ j : Fin 3, a j * inner ℝ (b j) c‖ ≤ ∑ j : Fin 3, ‖a‖ * ‖b j‖ * ‖c‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (PiLp.norm_apply_le a j) (norm_inner_le_norm _ _) (norm_nonneg _) (norm_nonneg _)

theorem enorm_sum_le_pointwise (a : Space) (b : Fin 3 → Space) (c : Space) :
    ‖∑ j : Fin 3, a j * inner ℝ (b j) c‖ₑ ≤ ∑ j : Fin 3, ‖a‖ₑ * ‖b j‖ₑ * ‖c‖ₑ := by
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (norm_sum_le_pointwise a b c)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
    ofReal_norm, ofReal_norm, ofReal_norm]

theorem lintegral_mul_three_le {f g h : Space → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hh : AEMeasurable h volume) :
    ∫⁻ x, f x * g x * h x ≤
      (∫⁻ x, f x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * (∫⁻ x, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        ((∫⁻ x, h x ^ (2 : ℝ)) ^ (1 / 4 : ℝ) * (∫⁻ x, h x ^ (6 : ℝ)) ^ (1 / 12 : ℝ)) := by
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := volume) (Finset.univ : Finset (Fin 4))
    (f := ![fun x => f x ^ (6 : ℝ), fun x => g x ^ (2 : ℝ), fun x => h x ^ (2 : ℝ),
      fun x => h x ^ (6 : ℝ)])
    (p := ![1 / 6, 1 / 2, 1 / 4, 1 / 12])
    (by
      intro i _
      fin_cases i
      · exact hf.pow_const _
      · exact hg.pow_const _
      · exact hh.pow_const _
      · exact hh.pow_const _)
    (by simp [Fin.sum_univ_four]; norm_num)
    (by intro i _; fin_cases i <;> norm_num)
  simp only [Fin.prod_univ_four, Matrix.cons_val] at key
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq (by rw [mul_assoc])))
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_assoc (f x ^ _ * g x ^ _), ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

theorem lintegral_enorm_mul_three_le {a b c : Space → Space} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) (hc : AEStronglyMeasurable c volume) :
    ∫⁻ x, ‖a x‖ₑ * ‖b x‖ₑ * ‖c x‖ₑ ≤
      eLpNorm a 6 volume * eLpNorm b 2 volume *
        (eLpNorm c 2 volume ^ (1 / 2 : ℝ) * eLpNorm c 6 volume ^ (1 / 2 : ℝ)) := by
  refine (lintegral_mul_three_le ha.enorm hb.enorm hc.enorm).trans (le_of_eq ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := a) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (f := b) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (f := c) (p := 2) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (f := c) (p := 6) (by norm_num) (by norm_num),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

end Internal.Trilinear

open Internal.Trilinear in
theorem trilinearBound (h1 : PartialNormLe) :
    TrilinearBound := by
  refine ⟨3 * ‖velocity‖, fun u v w hw2 hw6 => ?_⟩
  have ha : AEStronglyMeasurable (velocity u : Space → Space) volume := Lp.aestronglyMeasurable _
  have hb : ∀ j, AEStronglyMeasurable (partialX j v : Space → Space) volume :=
    fun j => Lp.aestronglyMeasurable _
  have hc : AEStronglyMeasurable w volume := hw2.1
  have hpj : ∀ j, ‖partialX j v‖ ≤ ‖v‖ := by
    intro j
    have hs := h1 v
    have hj : ‖partialX j v‖ ^ 2 ≤ ∑ i : Fin 3, ‖partialX i v‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖partialX i v‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (partialX j v), norm_nonneg v]
  have hpt : ∀ x, ‖∑ j : Fin 3, (velocity u : Space → Space) x j *
      inner ℝ ((partialX j v : Space → Space) x) (w x)‖ₑ ≤
      ∑ j : Fin 3, ‖(velocity u : Space → Space) x‖ₑ * ‖(partialX j v : Space → Space) x‖ₑ *
        ‖w x‖ₑ :=
    fun x => enorm_sum_le_pointwise _ (fun j => (partialX j v : Space → Space) x) _
  have hlin : ∫⁻ x, ‖∑ j : Fin 3, (velocity u : Space → Space) x j *
      inner ℝ ((partialX j v : Space → Space) x) (w x)‖ₑ ≤
      ∑ j : Fin 3, eLpNorm (velocity u : Space → Space) 6 volume *
        eLpNorm (partialX j v : Space → Space) 2 volume *
        (eLpNorm w 2 volume ^ (1 / 2 : ℝ) * eLpNorm w 6 volume ^ (1 / 2 : ℝ)) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_finsetSum' _ (fun j _ => ?_)]
    · exact Finset.sum_le_sum fun j _ => lintegral_enorm_mul_three_le ha (hb j) hc
    · exact (ha.enorm.mul (hb j).enorm).mul hc.enorm
  have hfin : ∑ j : Fin 3, eLpNorm (velocity u : Space → Space) 6 volume *
        eLpNorm (partialX j v : Space → Space) 2 volume *
        (eLpNorm w 2 volume ^ (1 / 2 : ℝ) * eLpNorm w 6 volume ^ (1 / 2 : ℝ)) ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun j _ => ?_
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hw2.eLpNorm_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hw6.eLpNorm_ne_top))
  have hF : AEStronglyMeasurable (fun x => ∑ j : Fin 3, (velocity u : Space → Space) x j *
      inner ℝ ((partialX j v : Space → Space) x) (w x)) volume := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact ((EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable ha).mul ((hb j).inner hc)
  refine ⟨⟨hF, lt_of_le_of_lt hlin hfin.lt_top⟩, ?_⟩
  have hS : 0 ≤ (eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ) :=
    by positivity
  have hsq : Real.sqrt ((eLpNorm w 2 volume).toReal * (eLpNorm w 6 volume).toReal) =
      (eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  have hmain : |trilinear u v w| ≤ ∑ j : Fin 3, ‖velocity u‖ * ‖partialX j v‖ *
      ((eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ)) := by
    rw [← Real.norm_eq_abs, trilinear]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    refine (ENNReal.toReal_mono hfin (by simpa only [ofReal_norm] using hlin)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.sum_ne_top.1 hfin j (Finset.mem_univ j))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def]
  rw [hsq]
  refine hmain.trans ?_
  calc ∑ j : Fin 3, ‖velocity u‖ * ‖partialX j v‖ *
        ((eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ))
      ≤ ∑ _j : Fin 3, ‖velocity‖ * ‖u‖ * ‖v‖ *
        ((eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
          (mul_le_mul (velocity.le_opNorm u) (hpj j) (norm_nonneg _) (by positivity)) hS
    _ = 3 * ‖velocity‖ * ‖u‖ * ‖v‖ *
        ((eLpNorm w 2 volume).toReal ^ (1 / 2 : ℝ) * (eLpNorm w 6 volume).toReal ^ (1 / 2 : ℝ)) := by
        rw [Fin.sum_univ_three]
        ring

end Breakdown.Freq

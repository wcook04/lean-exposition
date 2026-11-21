import Breakdown.CertCell.SixthPowerStatements

open MeasureTheory

noncomputable section

namespace Breakdown

private def pt (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

private lemma pt_preserving :
    MeasurePreserving (fun q : ℝ × ℝ × ℝ => pt q.1 q.2.1 q.2.2) volume volume := by
  have h := (PiLp.volume_preserving_toLp (Fin 3)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.comp
      ((MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ).symm))
  have e : (fun q : ℝ × ℝ × ℝ => pt q.1 q.2.1 q.2.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm ∘
        Prod.map id ⇑MeasurableEquiv.finTwoArrow.symm) := by
    funext q
    ext i
    fin_cases i <;> simp [pt, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  rw [e]
  exact h

private lemma measurable_pt {X : Type*} [MeasurableSpace X] {f g h : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable fun x => pt (f x) (g x) (h x) :=
  pt_preserving.measurable.comp (hf.prodMk (hg.prodMk hh))

private lemma pt_add_first (x y z t : ℝ) : pt x y z + t • unitVector 0 = pt (x + t) y z := by
  ext i
  fin_cases i <;> simp [pt, unitVector]

private lemma pt_add_second (x y z t : ℝ) : pt x y z + t • unitVector 1 = pt x (y + t) z := by
  ext i
  fin_cases i <;> simp [pt, unitVector]

private lemma pt_add_third (x y z t : ℝ) : pt x y z + t • unitVector 2 = pt x y (z + t) := by
  ext i
  fin_cases i <;> simp [pt, unitVector]

private lemma pt_eq (x y z : ℝ) :
    pt x y z = x • unitVector 0 + y • unitVector 1 + z • unitVector 2 := by
  ext i
  fin_cases i <;> simp [pt, unitVector]

private lemma lintegral_space_eq (F : Space → ENNReal) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ x, ∫⁻ y, ∫⁻ z, F (pt x y z) := by
  rw [← pt_preserving.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod (fun q : ℝ × ℝ × ℝ => F (pt q.1 q.2.1 q.2.2))
    (hF.comp pt_preserving.measurable).aemeasurable).trans ?_
  refine lintegral_congr fun x => ?_
  rw [Measure.volume_eq_prod]
  exact lintegral_prod (fun q : ℝ × ℝ => F (pt x q.1 q.2))
    (hF.comp (measurable_pt measurable_const measurable_fst measurable_snd)).aemeasurable

private lemma swap_inner (Φ : ℝ → ℝ → ℝ → ENNReal)
    (hΦ : Measurable fun q : ℝ × ℝ × ℝ => Φ q.1 q.2.1 q.2.2) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ a, ∫⁻ c, ∫⁻ b, Φ a b c := by
  refine lintegral_congr fun a => ?_
  apply lintegral_lintegral_swap
  exact (hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable

private lemma swap_outer (Φ : ℝ → ℝ → ℝ → ENNReal)
    (hΦ : Measurable fun q : ℝ × ℝ × ℝ => Φ q.1 q.2.1 q.2.2) :
    ∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a b c = ∫⁻ b, ∫⁻ a, ∫⁻ c, Φ a b c := by
  apply lintegral_lintegral_swap
  have h : Measurable fun p : (ℝ × ℝ) × ℝ => Φ p.1.1 p.1.2 p.2 :=
    hΦ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact h.lintegral_prod_right'.aemeasurable

private lemma ofReal_integral_le_lintegral {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t, f t) ≤ ∫⁻ t, ENNReal.ofReal (f t) := by
  by_cases hi : Integrable f
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi]
    simp

private lemma sum_abs_apply_le (L : Space →L[ℝ] ℝ) :
    |L (unitVector 0)| + |L (unitVector 1)| + |L (unitVector 2)| ≤ Real.sqrt 3 * ‖L‖ := by
  set c₀ := L (unitVector 0)
  set c₁ := L (unitVector 1)
  set c₂ := L (unitVector 2)
  have hw : L (pt c₀ c₁ c₂) = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := by
    rw [pt_eq]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hn : ‖pt c₀ c₁ c₂‖ ^ 2 = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [pt]
  have hb : c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 ≤ ‖L‖ * ‖pt c₀ c₁ c₂‖ := by
    rw [← hw]
    exact (le_abs_self _).trans (L.le_opNorm _)
  have hS : ‖pt c₀ c₁ c₂‖ ≤ ‖L‖ := by
    nlinarith [norm_nonneg (pt c₀ c₁ c₂), norm_nonneg L]
  have h3 : (Real.sqrt 3 * ‖L‖) ^ 2 = 3 * ‖L‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hsq : (|c₀| + |c₁| + |c₂|) ^ 2 ≤ (Real.sqrt 3 * ‖L‖) ^ 2 := by
    rw [h3]
    nlinarith [sq_nonneg (|c₀| - |c₁|), sq_nonneg (|c₁| - |c₂|), sq_nonneg (|c₀| - |c₂|),
      sq_abs c₀, sq_abs c₁, sq_abs c₂, norm_nonneg (pt c₀ c₁ c₂), norm_nonneg L]
  have hR : 0 ≤ Real.sqrt 3 * ‖L‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [abs_nonneg c₀, abs_nonneg c₁, abs_nonneg c₂]

theorem threeHalvesGradientBound_of (h₁ : TripleSliceBound) (h₂ : LineGradientBound) :
    ThreeHalvesGradientBound (1 / (2 * Real.sqrt 3)) := by
  intro u hu hc
  have hDc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  set a : Fin 3 → Space → ℝ := fun i y => |fderiv ℝ u y (unitVector i)| with ha_def
  have ha_nn : ∀ i y, 0 ≤ a i y := fun i y => abs_nonneg _
  have ha_cont : ∀ i, Continuous (a i) := fun i =>
    (hDc.clm_apply continuous_const).abs
  have ha_supp : ∀ i, HasCompactSupport (a i) := fun i =>
    (hc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℝ => |L (unitVector i)|) (by simp)
  have ha_int : ∀ i, Integrable (a i) := fun i =>
    (ha_cont i).integrable_of_hasCompactSupport (ha_supp i)
  have hD_int : Integrable fun y => ‖fderiv ℝ u y‖ :=
    hDc.norm.integrable_of_hasCompactSupport (hc.fderiv ℝ).norm
  set v : Space → ℝ := fun y => |u y| ^ ((3 : ℝ) / 2) with hv_def
  have hv_nn : ∀ y, 0 ≤ v y := fun y => Real.rpow_nonneg (abs_nonneg _) _
  have hv_cont : Continuous v := hu.continuous.abs.rpow_const fun _ => Or.inr (by norm_num)
  have hv_supp : HasCompactSupport v :=
    hc.comp_left (g := fun r : ℝ => |r| ^ ((3 : ℝ) / 2))
      (by rw [abs_zero, Real.zero_rpow (by norm_num)])
  have hv_int : Integrable v := hv_cont.integrable_of_hasCompactSupport hv_supp
  set b : Fin 3 → Space → ENNReal := fun i y => ENNReal.ofReal (a i y) with hb_def
  have hb : ∀ i, Measurable (b i) := fun i =>
    ENNReal.measurable_ofReal.comp (ha_cont i).measurable
  set A : Fin 3 → ℝ := fun i => ∫ y, a i y with hA_def
  have hA_nn : ∀ i, 0 ≤ A i := fun i => integral_nonneg (ha_nn i)
  have hbA : ∀ i, ∫⁻ y, b i y = ENNReal.ofReal (A i) := fun i =>
    (ofReal_integral_eq_lintegral_ofReal (ha_int i) (Filter.Eventually.of_forall (ha_nn i))).symm
  set c : ENNReal := ENNReal.ofReal (1 / 2) with hc_def
  have hline : ∀ i (p : Space), ENNReal.ofReal |u p| ≤ c * ∫⁻ t : ℝ, b i (p + t • unitVector i) := by
    intro i p
    calc ENNReal.ofReal |u p|
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) * ∫ t : ℝ, a i (p + t • unitVector i)) :=
          ENNReal.ofReal_le_ofReal (h₂ u hu hc i p)
      _ = c * ENNReal.ofReal (∫ t : ℝ, a i (p + t • unitVector i)) :=
          ENNReal.ofReal_mul (by norm_num)
      _ ≤ c * ∫⁻ t : ℝ, b i (p + t • unitVector i) :=
by
            gcongr
            exact ofReal_integral_le_lintegral fun t => ha_nn i _
  set g₀ : ℝ × ℝ → ENNReal := fun p => c * ∫⁻ t, b 0 (pt t p.1 p.2) with hg₀_def
  set g₁ : ℝ × ℝ → ENNReal := fun p => c * ∫⁻ t, b 1 (pt p.1 t p.2) with hg₁_def
  set g₂ : ℝ × ℝ → ENNReal := fun p => c * ∫⁻ t, b 2 (pt p.1 p.2 t) with hg₂_def
  have hm₀ : Measurable fun q : (ℝ × ℝ) × ℝ => b 0 (pt q.2 q.1.1 q.1.2) :=
    (hb 0).comp (measurable_pt measurable_snd measurable_fst.fst measurable_fst.snd)
  have hm₁ : Measurable fun q : (ℝ × ℝ) × ℝ => b 1 (pt q.1.1 q.2 q.1.2) :=
    (hb 1).comp (measurable_pt measurable_fst.fst measurable_snd measurable_fst.snd)
  have hm₂ : Measurable fun q : (ℝ × ℝ) × ℝ => b 2 (pt q.1.1 q.1.2 q.2) :=
    (hb 2).comp (measurable_pt measurable_fst.fst measurable_fst.snd measurable_snd)
  have hg₀ : Measurable g₀ := measurable_const.mul hm₀.lintegral_prod_right'
  have hg₁ : Measurable g₁ := measurable_const.mul hm₁.lintegral_prod_right'
  have hg₂ : Measurable g₂ := measurable_const.mul hm₂.lintegral_prod_right'
  have e₀ : ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 0 (pt t p.1 p.2) = ∫⁻ y, b 0 y := by
    calc ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 0 (pt t p.1 p.2)
        = ∫⁻ y, ∫⁻ z, ∫⁻ t, b 0 (pt t y z) :=
          lintegral_prod _ hm₀.lintegral_prod_right'.aemeasurable
      _ = ∫⁻ y, ∫⁻ t, ∫⁻ z, b 0 (pt t y z) :=
          swap_inner (fun y z t => b 0 (pt t y z))
            ((hb 0).comp (measurable_pt measurable_snd.snd measurable_fst measurable_snd.fst))
      _ = ∫⁻ t, ∫⁻ y, ∫⁻ z, b 0 (pt t y z) :=
          swap_outer (fun y t z => b 0 (pt t y z))
            ((hb 0).comp (measurable_pt measurable_snd.fst measurable_fst measurable_snd.snd))
      _ = ∫⁻ y, b 0 y := (lintegral_space_eq _ (hb 0)).symm
  have e₁ : ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 1 (pt p.1 t p.2) = ∫⁻ y, b 1 y := by
    calc ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 1 (pt p.1 t p.2)
        = ∫⁻ x, ∫⁻ z, ∫⁻ t, b 1 (pt x t z) :=
          lintegral_prod _ hm₁.lintegral_prod_right'.aemeasurable
      _ = ∫⁻ x, ∫⁻ t, ∫⁻ z, b 1 (pt x t z) :=
          swap_inner (fun x z t => b 1 (pt x t z))
            ((hb 1).comp (measurable_pt measurable_fst measurable_snd.snd measurable_snd.fst))
      _ = ∫⁻ y, b 1 y := (lintegral_space_eq _ (hb 1)).symm
  have e₂ : ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 2 (pt p.1 p.2 t) = ∫⁻ y, b 2 y := by
    calc ∫⁻ p : ℝ × ℝ, ∫⁻ t, b 2 (pt p.1 p.2 t)
        = ∫⁻ x, ∫⁻ y, ∫⁻ t, b 2 (pt x y t) :=
          lintegral_prod _ hm₂.lintegral_prod_right'.aemeasurable
      _ = ∫⁻ y, b 2 y := (lintegral_space_eq _ (hb 2)).symm
  have hG₀ : ∫⁻ p, g₀ p = c * ENNReal.ofReal (A 0) := by
    rw [lintegral_const_mul _ hm₀.lintegral_prod_right', e₀, hbA]
  have hG₁ : ∫⁻ p, g₁ p = c * ENNReal.ofReal (A 1) := by
    rw [lintegral_const_mul _ hm₁.lintegral_prod_right', e₁, hbA]
  have hG₂ : ∫⁻ p, g₂ p = c * ENNReal.ofReal (A 2) := by
    rw [lintegral_const_mul _ hm₂.lintegral_prod_right', e₂, hbA]
  have hpt : ∀ x y z : ℝ, ENNReal.ofReal (v (pt x y z)) ≤
      (g₀ (y, z) * g₁ (x, z) * g₂ (x, y)) ^ ((1 : ℝ) / 2) := by
    intro x y z
    have k₀ : ENNReal.ofReal |u (pt x y z)| ≤ g₀ (y, z) := by
      refine (hline 0 _).trans (le_of_eq ?_)
      simp only [hg₀_def, pt_add_first]
      rw [lintegral_add_left_eq_self (fun s => b 0 (pt s y z)) x]
    have k₁ : ENNReal.ofReal |u (pt x y z)| ≤ g₁ (x, z) := by
      refine (hline 1 _).trans (le_of_eq ?_)
      simp only [hg₁_def, pt_add_second]
      rw [lintegral_add_left_eq_self (fun s => b 1 (pt x s z)) y]
    have k₂ : ENNReal.ofReal |u (pt x y z)| ≤ g₂ (x, y) := by
      refine (hline 2 _).trans (le_of_eq ?_)
      simp only [hg₂_def, pt_add_third]
      rw [lintegral_add_left_eq_self (fun s => b 2 (pt x y s)) z]
    set m := ENNReal.ofReal |u (pt x y z)|
    have hmv : ENNReal.ofReal (v (pt x y z)) = (m * m * m) ^ ((1 : ℝ) / 2) := by
      have h3 : m * m * m = m ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
        ring
      rw [h3, ← ENNReal.rpow_mul, hv_def, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
        (by norm_num)]
      norm_num
      rfl
    rw [hmv]
    exact ENNReal.rpow_le_rpow (mul_le_mul' (mul_le_mul' k₀ k₁) k₂) (by norm_num)
  set Q : ℝ := A 0 / 2 * (A 1 / 2) * (A 2 / 2) with hQ_def
  have hQ : 0 ≤ Q := by
    have := hA_nn 0
    have := hA_nn 1
    have := hA_nn 2
    positivity
  have hcA : ∀ i, c * ENNReal.ofReal (A i) = ENNReal.ofReal (A i / 2) := by
    intro i
    rw [hc_def, ← ENNReal.ofReal_mul (by norm_num)]
    ring_nf
  have hE : ENNReal.ofReal (∫ y, v y) ≤ ENNReal.ofReal (Q ^ ((1 : ℝ) / 2)) := by
    calc ENNReal.ofReal (∫ y, v y)
        = ∫⁻ y, ENNReal.ofReal (v y) :=
          ofReal_integral_eq_lintegral_ofReal hv_int (Filter.Eventually.of_forall hv_nn)
      _ = ∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (v (pt x y z)) :=
          lintegral_space_eq _ (ENNReal.measurable_ofReal.comp hv_cont.measurable)
      _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ z, (g₀ (y, z) * g₁ (x, z) * g₂ (x, y)) ^ ((1 : ℝ) / 2) :=
          lintegral_mono fun x => lintegral_mono fun y => lintegral_mono fun z => hpt x y z
      _ ≤ ((∫⁻ p, g₀ p) * (∫⁻ p, g₁ p) * (∫⁻ p, g₂ p)) ^ ((1 : ℝ) / 2) :=
          h₁ g₀ g₁ g₂ hg₀ hg₁ hg₂
      _ = ENNReal.ofReal (Q ^ ((1 : ℝ) / 2)) := by
          rw [hG₀, hG₁, hG₂, hcA, hcA, hcA, ← ENNReal.ofReal_mul (by linarith [hA_nn 0]),
            ← ENNReal.ofReal_mul (by have := hA_nn 0; have := hA_nn 1; positivity),
            ENNReal.ofReal_rpow_of_nonneg hQ (by norm_num)]
  have hI : ∫ y, v y ≤ Q ^ ((1 : ℝ) / 2) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hQ _)).1 hE
  have hI0 : 0 ≤ ∫ y, v y := integral_nonneg hv_nn
  have hsum : ∀ y, a 0 y + a 1 y + a 2 y ≤ Real.sqrt 3 * ‖fderiv ℝ u y‖ := fun y =>
    sum_abs_apply_le (fderiv ℝ u y)
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  calc (∫ y, |u y| ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)
      = (∫ y, v y) ^ ((2 : ℝ) / 3) := rfl
    _ ≤ (Q ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow hI0 hI (by norm_num)
    _ = Q ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_mul hQ]
        norm_num
    _ = (A 0 / 2) ^ ((1 : ℝ) / 3) * (A 1 / 2) ^ ((1 : ℝ) / 3) * (A 2 / 2) ^ ((1 : ℝ) / 3) := by
        have := hA_nn 0
        have := hA_nn 1
        have := hA_nn 2
        rw [hQ_def, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ 1 / 3 * (A 0 / 2) + 1 / 3 * (A 1 / 2) + 1 / 3 * (A 2 / 2) := by
        have := hA_nn 0
        have := hA_nn 1
        have := hA_nn 2
        exact Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num)
          (by positivity) (by positivity) (by positivity) (by norm_num)
    _ = (∫ y, (a 0 y + a 1 y + a 2 y)) / 6 := by
        rw [integral_add (f := fun y => a 0 y + a 1 y) (g := a 2) ((ha_int 0).add (ha_int 1))
          (ha_int 2),
          integral_add (ha_int 0) (ha_int 1)]
        simp only [hA_def]
        ring
    _ ≤ (∫ y, Real.sqrt 3 * ‖fderiv ℝ u y‖) / 6 := by
        gcongr ?_ / 6
        exact integral_mono (((ha_int 0).add (ha_int 1)).add (ha_int 2))
          (hD_int.const_mul _) hsum
    _ = 1 / (2 * Real.sqrt 3) * ∫ y, ‖fderiv ℝ u y‖ := by
        rw [integral_const_mul]
        have hs3' : Real.sqrt 3 ^ 2 = 3 := by rw [sq, hs3]
        field_simp
        rw [hs3']
        ring

end Breakdown

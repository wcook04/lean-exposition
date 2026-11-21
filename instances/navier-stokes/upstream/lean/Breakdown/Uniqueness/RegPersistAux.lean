import Breakdown.Uniqueness.RegPersistAuxDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem measurable_ofReal_weight (r : ℝ) :
    Measurable fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) :=
  ((measurable_const.add (measurable_norm.pow_const 2)).pow_const r).ennreal_ofReal

private theorem enn_sq_add_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe x =>
    induction y using ENNReal.recTopCoe with
    | top => simp
    | coe y =>
      norm_cast
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith [sq_nonneg ((x : ℝ) - y)]

private theorem heat_enorm_le_one {a t : ℝ} (ht : a ≤ t) (ξ : Space) :
    ‖((heatSymbol (t - a) ξ : ℝ) : ℂ)‖ₑ ≤ 1 := by
  unfold heatSymbol
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
  exact neg_nonpos.2 (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.2 ht)) (by positivity))

theorem aestronglyMeasurable_heatPart {f : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (a t : ℝ) : AEStronglyMeasurable (heatPart a f t) volume := by
  have hc : Continuous fun ξ : Space => ((heatSymbol (t - a) ξ : ℝ) : ℂ) := by
    unfold heatSymbol
    fun_prop
  exact hc.aestronglyMeasurable.smul hf

theorem fracNormSq_natCast (m : ℕ) (f : Space → CSpace) : fracNormSq m f = hsNormSq m f := by
  unfold fracNormSq hsNormSq hsWeight
  simp_rw [Real.rpow_natCast]

theorem fracNormSq_mono {r s : ℝ} (h : r ≤ s) (f : Space → CSpace) :
    fracNormSq r f ≤ fracNormSq s f := by
  unfold fracNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr ?_ * _
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _)) h)

theorem fracNormSq_add_le (r : ℝ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    fracNormSq r (f + g) ≤ 2 * fracNormSq r f + 2 * fracNormSq r g := by
  unfold fracNormSq
  have hmf : AEMeasurable (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖f ξ‖ₑ ^ 2) volume :=
    (measurable_ofReal_weight r).aemeasurable.mul (hf.enorm.pow_const 2)
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖(f + g) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, (2 * (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖f ξ‖ₑ ^ 2) +
          2 * (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖g ξ‖ₑ ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖(f + g) ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (2 * ‖f ξ‖ₑ ^ 2 + 2 * ‖g ξ‖ₑ ^ 2) := by
              gcongr
              exact (pow_le_pow_left₀ zero_le (enorm_add_le (f ξ) (g ξ)) 2).trans
                (enn_sq_add_le _ _)
          _ = _ := by ring
    _ = 2 * (∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖f ξ‖ₑ ^ 2) +
          2 * ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖g ξ‖ₑ ^ 2 := by
        rw [lintegral_add_left' (hmf.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]

private theorem fracNormSq_neg (r : ℝ) (g : Space → CSpace) : fracNormSq r (-g) = fracNormSq r g := by
  unfold fracNormSq
  simp [enorm_neg]

theorem fracNormSq_sub_le (r : ℝ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    fracNormSq r (f - g) ≤ 2 * fracNormSq r f + 2 * fracNormSq r g := by
  rw [sub_eq_add_neg, ← fracNormSq_neg r g]
  exact fracNormSq_add_le r hf hg.neg

theorem fracNormSq_heatPart_le (r : ℝ) {a t : ℝ} (ht : a ≤ t) (f : Space → CSpace) :
    fracNormSq r (heatPart a f t) ≤ fracNormSq r f := by
  unfold fracNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  calc ‖heatPart a f t ξ‖ₑ = ‖((heatSymbol (t - a) ξ : ℝ) : ℂ)‖ₑ * ‖f ξ‖ₑ := enorm_smul _ _
    _ ≤ 1 * ‖f ξ‖ₑ := by gcongr; exact heat_enorm_le_one ht ξ
    _ = ‖f ξ‖ₑ := one_mul _

private theorem hsNormSq_add_le' (m : ℕ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  rw [← fracNormSq_natCast, ← fracNormSq_natCast, ← fracNormSq_natCast]
  exact fracNormSq_add_le _ hf hg

theorem hsNormSq_bdd_of_curve {k : ℕ} {F : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve k F a b) : ∃ B : ℝ, ∀ t ∈ Icc a b, hsNormSq k (F t) ≤ ENNReal.ofReal B := by
  have hU : ∀ x ∈ Icc a b, {t | t ∈ Icc a b → hsNormSq k (F t) ≤ 2 + 2 * hsNormSq k (F x)} ∈
      𝓝[Icc a b] x := by
    intro x hx
    have h1 : ∀ᶠ t in 𝓝[Icc a b] x, hsNormSq k (F t - F x) < 1 :=
      (hF.2 x hx).eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [h1] with t ht hti
    have e : F t = (F t - F x) + F x := (sub_add_cancel _ _).symm
    calc hsNormSq k (F t) = hsNormSq k ((F t - F x) + F x) := by rw [← e]
      _ ≤ 2 * hsNormSq k (F t - F x) + 2 * hsNormSq k (F x) :=
          hsNormSq_add_le' k ((hF.1 t hti).1.sub (hF.1 x hx).1) (hF.1 x hx).1
      _ ≤ 2 * 1 + 2 * hsNormSq k (F x) := by gcongr
      _ = 2 + 2 * hsNormSq k (F x) := by rw [mul_one]
  obtain ⟨s, hs, hcov⟩ := isCompact_Icc.elim_nhdsWithin_subcover _ hU
  refine ⟨∑ x ∈ s, (2 + 2 * hsNormSq k (F x)).toReal, fun t ht => ?_⟩
  obtain ⟨x, hx, htx⟩ := mem_iUnion₂.1 (hcov ht)
  have hfin : 2 + 2 * hsNormSq k (F x) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) (hF.1 x (hs x hx)).2.ne⟩
  calc hsNormSq k (F t) ≤ 2 + 2 * hsNormSq k (F x) := htx ht
    _ = ENNReal.ofReal (2 + 2 * hsNormSq k (F x)).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (∑ x ∈ s, (2 + 2 * hsNormSq k (F x)).toReal) :=
        ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := fun x => (2 + 2 * hsNormSq k (F x)).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) hx)

theorem tendsto_hsNormSq_heatPart {m : ℕ} {f : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (h : hsNormSq m f < ⊤) {a b : ℝ} (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    Tendsto (fun t => hsNormSq m (heatPart a f t - heatPart a f t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
  have hw : Measurable fun ξ : Space => ENNReal.ofReal (hsWeight m ξ) := by
    unfold hsWeight
    exact ((measurable_const.add (measurable_norm.pow_const 2)).pow_const m).ennreal_ofReal
  have hcont : ∀ ξ, Continuous fun t => ENNReal.ofReal (hsWeight m ξ) *
      ‖(heatPart a f t - heatPart a f t₀) ξ‖ₑ ^ 2 := by
    intro ξ
    have hh : Continuous fun t => heatPart a f t ξ := by
      unfold heatPart heatSymbol
      fun_prop
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hh.sub continuous_const)))
  have hlim := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume)
    (l := 𝓝[Icc a b] t₀)
    (F := fun t ξ => ENNReal.ofReal (hsWeight m ξ) * ‖(heatPart a f t - heatPart a f t₀) ξ‖ₑ ^ 2)
    (f := fun ξ => ENNReal.ofReal (hsWeight m ξ) * ‖(heatPart a f t₀ - heatPart a f t₀) ξ‖ₑ ^ 2)
    (fun ξ => 4 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2))
    (Eventually.of_forall fun t => hw.aemeasurable.mul
      (((aestronglyMeasurable_heatPart hf a t).sub (aestronglyMeasurable_heatPart hf a t₀)).enorm.pow_const 2))
    ?_ ?_ (Eventually.of_forall fun ξ => ((hcont ξ).tendsto t₀).mono_left nhdsWithin_le_nhds)
  · simpa [hsNormSq] using hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun ξ => ?_
    have h1 : ‖heatPart a f t ξ‖ₑ ≤ ‖f ξ‖ₑ := by
      calc ‖heatPart a f t ξ‖ₑ = ‖((heatSymbol (t - a) ξ : ℝ) : ℂ)‖ₑ * ‖f ξ‖ₑ := enorm_smul _ _
        _ ≤ 1 * ‖f ξ‖ₑ := by gcongr; exact heat_enorm_le_one ht.1 ξ
        _ = ‖f ξ‖ₑ := one_mul _
    have h2 : ‖heatPart a f t₀ ξ‖ₑ ≤ ‖f ξ‖ₑ := by
      calc ‖heatPart a f t₀ ξ‖ₑ = ‖((heatSymbol (t₀ - a) ξ : ℝ) : ℂ)‖ₑ * ‖f ξ‖ₑ := enorm_smul _ _
        _ ≤ 1 * ‖f ξ‖ₑ := by gcongr; exact heat_enorm_le_one ht₀.1 ξ
        _ = ‖f ξ‖ₑ := one_mul _
    have h3 : ‖(heatPart a f t - heatPart a f t₀) ξ‖ₑ ≤ 2 * ‖f ξ‖ₑ :=
      (enorm_sub_le).trans ((add_le_add h1 h2).trans_eq (two_mul _).symm)
    calc ENNReal.ofReal (hsWeight m ξ) * ‖(heatPart a f t - heatPart a f t₀) ξ‖ₑ ^ 2
        ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * ‖f ξ‖ₑ) ^ 2 := by gcongr
      _ = 4 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) := by ring
  · rw [lintegral_const_mul' _ _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num) h.ne

private theorem weight_split {x y m r : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hmr : m < r) (hm : 0 ≤ m) :
    x ^ m ≤ y ^ m * x ^ (3 : ℝ) + y ^ (m - r) * x ^ r := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rcases le_total x y with hxy | hxy
  · have h1 : x ^ m ≤ y ^ m := Real.rpow_le_rpow hx0.le hxy hm
    have h2 : 1 ≤ x ^ (3 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have h3 : 0 ≤ y ^ (m - r) * x ^ r := by positivity
    nlinarith [Real.rpow_nonneg hy0.le m]
  · have h1 : x ^ (m - r) ≤ y ^ (m - r) := Real.rpow_le_rpow_of_nonpos hy0 hxy (by linarith)
    have e : x ^ m = x ^ (m - r) * x ^ r := by
      rw [← Real.rpow_add hx0]; ring_nf
    have h4 : 0 ≤ y ^ m * x ^ (3 : ℝ) := by positivity
    rw [e]
    nlinarith [Real.rpow_nonneg hx0.le r]

theorem tendsto_hsNormSq_of_frac {G : ℝ → Space → CSpace} {m : ℕ} {r : ℝ} (hr : (m : ℝ) < r)
    {a b B : ℝ} (hG : ∀ t ∈ Icc a b, AEStronglyMeasurable (G t) volume) (hB : ∀ t ∈ Icc a b, fracNormSq r (G t) ≤ ENNReal.ofReal B)
    (h3 : ∀ t₀ ∈ Icc a b, Tendsto (fun t => hsNormSq 3 (G t - G t₀)) (𝓝[Icc a b] t₀) (𝓝 0))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    Tendsto (fun t => hsNormSq m (G t - G t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
  set B₀ := max B 0 with hB₀
  have hB₀n : 0 ≤ B₀ := le_max_right _ _
  have hBB : ∀ t ∈ Icc a b, fracNormSq r (G t) ≤ ENNReal.ofReal B₀ :=
    fun t ht => (hB t ht).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have key : ∀ y : ℝ, 1 ≤ y → ∀ t ∈ Icc a b, hsNormSq m (G t - G t₀) ≤
      ENNReal.ofReal (y ^ (m : ℝ)) * hsNormSq 3 (G t - G t₀) + ENNReal.ofReal (y ^ ((m : ℝ) - r) * (4 * B₀)) := by
    intro y hy t ht
    have hD : AEStronglyMeasurable (G t - G t₀) volume := (hG t ht).sub (hG t₀ ht₀)
    have hfr : fracNormSq r (G t - G t₀) ≤ ENNReal.ofReal (4 * B₀) := by
      calc fracNormSq r (G t - G t₀) ≤ 2 * fracNormSq r (G t) + 2 * fracNormSq r (G t₀) :=
            fracNormSq_sub_le r (hG t ht) (hG t₀ ht₀)
        _ ≤ 2 * ENNReal.ofReal B₀ + 2 * ENNReal.ofReal B₀ := by gcongr <;> [exact hBB t ht; exact hBB t₀ ht₀]
        _ = ENNReal.ofReal (4 * B₀) := by
            rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num)]
            norm_num
    have hm3 : Measurable fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (3 : ℝ)) := measurable_ofReal_weight 3
    rw [← fracNormSq_natCast, ← fracNormSq_natCast]
    calc fracNormSq m (G t - G t₀)
        ≤ ∫⁻ ξ, (ENNReal.ofReal (y ^ (m : ℝ)) * (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℕ) : ℝ)) *
            ‖(G t - G t₀) ξ‖ₑ ^ 2) + ENNReal.ofReal (y ^ ((m : ℝ) - r)) *
            (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * ‖(G t - G t₀) ξ‖ₑ ^ 2)) := by
          unfold fracNormSq
          refine lintegral_mono fun ξ => ?_
          have hw := weight_split (x := 1 + ‖ξ‖ ^ 2) (le_add_of_nonneg_right (sq_nonneg _)) hy hr
            (Nat.cast_nonneg m)
          calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (m : ℝ)) * ‖(G t - G t₀) ξ‖ₑ ^ 2
              ≤ ENNReal.ofReal (y ^ (m : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (3 : ℝ) +
                  y ^ ((m : ℝ) - r) * (1 + ‖ξ‖ ^ 2) ^ r) * ‖(G t - G t₀) ξ‖ₑ ^ 2 := by
                gcongr
            _ = _ := by
                have h1 : 0 ≤ y ^ (m : ℝ) := by positivity
                have h2 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (3 : ℝ) := by positivity
                have h3' : 0 ≤ y ^ ((m : ℝ) - r) := by positivity
                have h4 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ r := by positivity
                rw [ENNReal.ofReal_add (mul_nonneg h1 h2) (mul_nonneg h3' h4), ENNReal.ofReal_mul h1,
                  ENNReal.ofReal_mul h3']
                push_cast
                ring
      _ = ENNReal.ofReal (y ^ (m : ℝ)) * fracNormSq ((3 : ℕ) : ℝ) (G t - G t₀) +
            ENNReal.ofReal (y ^ ((m : ℝ) - r)) * fracNormSq r (G t - G t₀) := by
          unfold fracNormSq
          rw [lintegral_add_left', lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          push_cast
          exact ((hm3.aemeasurable.mul (hD.enorm.pow_const 2)).const_mul _)
      _ ≤ ENNReal.ofReal (y ^ (m : ℝ)) * fracNormSq ((3 : ℕ) : ℝ) (G t - G t₀) +
            ENNReal.ofReal (y ^ ((m : ℝ) - r)) * ENNReal.ofReal (4 * B₀) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have he : 0 < (ε / 2).toReal := ENNReal.toReal_pos (ENNReal.half_pos hε.ne').ne' (ENNReal.div_ne_top hεt (by norm_num))
  have hev : ∀ᶠ y in atTop, 1 ≤ y ∧ y ^ ((m : ℝ) - r) * (4 * B₀) < (ε / 2).toReal := by
    have ht : Tendsto (fun y : ℝ => y ^ (-(r - m)) * (4 * B₀)) atTop (𝓝 (0 * (4 * B₀))) :=
      (tendsto_rpow_neg_atTop (by linarith)).mul_const _
    rw [zero_mul] at ht
    filter_upwards [eventually_ge_atTop 1, ht.eventually (gt_mem_nhds he)] with y hy1 hy2
    refine ⟨hy1, ?_⟩
    simpa [neg_sub] using hy2
  obtain ⟨y, hy1, hy2⟩ := hev.exists
  have hA : Tendsto (fun t => ENNReal.ofReal (y ^ (m : ℝ)) * hsNormSq 3 (G t - G t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (h3 t₀ ht₀) (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (y ^ (m : ℝ)))
    simpa using this
  filter_upwards [self_mem_nhdsWithin, (ENNReal.tendsto_nhds_zero.1 hA) (ε / 2) (ENNReal.half_pos hε.ne')] with t ht hAt
  calc hsNormSq m (G t - G t₀) ≤ ENNReal.ofReal (y ^ (m : ℝ)) * hsNormSq 3 (G t - G t₀) +
        ENNReal.ofReal (y ^ ((m : ℝ) - r) * (4 * B₀)) := key y hy1 t ht
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        calc ENNReal.ofReal (y ^ ((m : ℝ) - r) * (4 * B₀)) ≤ ENNReal.ofReal (ε / 2).toReal :=
              ENNReal.ofReal_le_ofReal hy2.le
          _ = ε / 2 := ENNReal.ofReal_toReal (ENNReal.div_ne_top hεt (by norm_num))
    _ = ε := ENNReal.add_halves ε

end Breakdown.SmoothFlow

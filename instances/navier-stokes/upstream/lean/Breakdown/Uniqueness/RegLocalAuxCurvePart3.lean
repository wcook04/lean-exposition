import Breakdown.Uniqueness.RegLocalAuxCurvePart5

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem enorm_sub_sq_le_c (x y : ℂ) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have e : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  have h := norm_sub_le x y
  have key : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y)]
  calc ENNReal.ofReal (‖x - y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private theorem lintegral_sub_ne_top {p p' : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hp2 : ∫⁻ η, ‖p η‖ₑ ^ 2 ≠ ⊤) (hp2' : ∫⁻ η, ‖p' η‖ₑ ^ 2 ≠ ⊤) :
    ∫⁻ η, ‖p η - p' η‖ₑ ^ 2 ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun η => enorm_sub_sq_le_c (p η) (p' η))
  rw [lintegral_add_left' ((hp.enorm.pow_const 2).const_mul 2),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hp2, ENNReal.mul_ne_top (by norm_num) hp2'⟩

private theorem half_rpow_tendsto {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} (h : Tendsto f l (𝓝 0)) :
    Tendsto (fun x => f x ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this.comp h

private theorem half_rpow_ne_top {x : ℝ≥0∞} (h : x ≠ ⊤) : x ^ (1 / 2 : ℝ) ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) h

private theorem continuousOn_convC_param {P Q : ℝ → Space → ℂ} {a b : ℝ}
    (hPm : ∀ s ∈ Icc a b, AEStronglyMeasurable (P s) volume)
    (hQm : ∀ s ∈ Icc a b, AEStronglyMeasurable (Q s) volume)
    (hP2 : ∀ s ∈ Icc a b, ∫⁻ η, ‖P s η‖ₑ ^ 2 ≠ ⊤) (hQ2 : ∀ s ∈ Icc a b, ∫⁻ η, ‖Q s η‖ₑ ^ 2 ≠ ⊤)
    (hPc : ∀ s₀ ∈ Icc a b, Tendsto (fun s => ∫⁻ η, ‖P s η - P s₀ η‖ₑ ^ 2) (𝓝[Icc a b] s₀) (𝓝 0))
    (hQc : ∀ s₀ ∈ Icc a b, Tendsto (fun s => ∫⁻ η, ‖Q s η - Q s₀ η‖ₑ ^ 2) (𝓝[Icc a b] s₀) (𝓝 0)) :
    ContinuousOn (fun p : Space × ℝ => convC (P p.2) (Q p.2) p.1) (univ ×ˢ Icc a b) := by
  rintro ⟨ξ₀, s₀⟩ ⟨-, hs₀⟩
  have hsnd : Tendsto Prod.snd (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝[Icc a b] s₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto (ξ₀, s₀)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hy.2
  have hfst : Tendsto Prod.fst (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 ξ₀) :=
    (continuous_fst.tendsto (ξ₀, s₀)).mono_left nhdsWithin_le_nhds
  set dP : ℝ → Space → ℂ := fun s η => P s η - P s₀ η with hdP
  set dQ : ℝ → Space → ℂ := fun s η => Q s η - Q s₀ η with hdQ
  set EP : ℝ → ℝ≥0∞ := fun s => (∫⁻ η, ‖dP s η‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  set EQ : ℝ → ℝ≥0∞ := fun s => (∫⁻ η, ‖dQ s η‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  set CP : ℝ≥0∞ := (∫⁻ η, ‖P s₀ η‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  set CQ : ℝ≥0∞ := (∫⁻ η, ‖Q s₀ η‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  have hEP : Tendsto (fun y : Space × ℝ => EP y.2) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) :=
    (half_rpow_tendsto (hPc s₀ hs₀)).comp hsnd
  have hEQ : Tendsto (fun y : Space × ℝ => EQ y.2) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) :=
    (half_rpow_tendsto (hQc s₀ hs₀)).comp hsnd
  have hcont := continuous_convC (hPm s₀ hs₀) (hQm s₀ hs₀) (hP2 s₀ hs₀) (hQ2 s₀ hs₀)
  have h3 : Tendsto (fun y : Space × ℝ => ‖convC (P s₀) (Q s₀) y.1 - convC (P s₀) (Q s₀) ξ₀‖ₑ)
      (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) := by
    have := ((hcont.tendsto ξ₀).comp hfst)
    have h := (tendsto_iff_edist_tendsto_0.1 this)
    simpa [edist_eq_enorm_sub] using h
  have hsum : Tendsto (fun y : Space × ℝ => EP y.2 * EQ y.2 + EP y.2 * CQ + CP * EQ y.2 +
      ‖convC (P s₀) (Q s₀) y.1 - convC (P s₀) (Q s₀) ξ₀‖ₑ) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) := by
    have t1 : Tendsto (fun y : Space × ℝ => EP y.2 * EQ y.2) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) := by
      have := ENNReal.Tendsto.mul hEP (Or.inr ENNReal.zero_ne_top) hEQ (Or.inr ENNReal.zero_ne_top)
      rwa [mul_zero] at this
    have t2 : Tendsto (fun y : Space × ℝ => EP y.2 * CQ) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (b := CQ) hEP (Or.inr (half_rpow_ne_top (hQ2 s₀ hs₀)))
      rwa [zero_mul] at this
    have t3 : Tendsto (fun y : Space × ℝ => CP * EQ y.2) (𝓝[univ ×ˢ Icc a b] (ξ₀, s₀)) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := CP) hEQ (Or.inr (half_rpow_ne_top (hP2 s₀ hs₀)))
      rwa [mul_zero] at this
    have := ((t1.add t2).add t3).add h3
    simp only [add_zero] at this
    exact this
  refine tendsto_iff_edist_tendsto_0.2 ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨ξ, s⟩ := y
  have hs : s ∈ Icc a b := hy.2
  simp only [edist_eq_enorm_sub]
  have hdPm : AEStronglyMeasurable (dP s) volume := (hPm s hs).sub (hPm s₀ hs₀)
  have hdQm : AEStronglyMeasurable (dQ s) volume := (hQm s hs).sub (hQm s₀ hs₀)
  have hdP2 : ∫⁻ η, ‖dP s η‖ₑ ^ 2 ≠ ⊤ := lintegral_sub_ne_top (hPm s hs) (hP2 s hs) (hP2 s₀ hs₀)
  have hdQ2 : ∫⁻ η, ‖dQ s η‖ₑ ^ 2 ≠ ⊤ := lintegral_sub_ne_top (hQm s hs) (hQ2 s hs) (hQ2 s₀ hs₀)
  have e1 := convC_sub_left (hPm s hs) (hPm s₀ hs₀) (hQm s hs) (hP2 s hs) (hP2 s₀ hs₀) (hQ2 s hs) ξ
  have e2 := convC_sub_right hdPm (hQm s hs) (hQm s₀ hs₀) hdP2 (hQ2 s hs) (hQ2 s₀ hs₀) ξ
  have e3 := convC_sub_right (hPm s₀ hs₀) (hQm s hs) (hQm s₀ hs₀) (hP2 s₀ hs₀) (hQ2 s hs) (hQ2 s₀ hs₀) ξ
  have e4 := convC_sub_left hdPm (hPm s₀ hs₀) (hQm s₀ hs₀) hdP2 (hP2 s₀ hs₀) (hQ2 s₀ hs₀) ξ
  have key : convC (P s) (Q s) ξ - convC (P s₀) (Q s₀) ξ₀ =
      convC (dP s) (dQ s) ξ + convC (dP s) (Q s₀) ξ + convC (P s₀) (dQ s) ξ +
        (convC (P s₀) (Q s₀) ξ - convC (P s₀) (Q s₀) ξ₀) := by
    have e1' : convC (P s) (Q s) ξ = convC (P s₀) (Q s) ξ + convC (dP s) (Q s) ξ := by
      rw [← e1]; ring
    have e2' : convC (dP s) (Q s) ξ = convC (dP s) (dQ s) ξ + convC (dP s) (Q s₀) ξ := by
      rw [← e2]; ring
    have e3' : convC (P s₀) (Q s) ξ = convC (P s₀) (dQ s) ξ + convC (P s₀) (Q s₀) ξ := by
      rw [← e3]; ring
    rw [e1', e2', e3']
    ring
  rw [key]
  refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add
    ((enorm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) le_rfl)
  · exact enorm_convC_le hdPm hdQm ξ
  · exact enorm_convC_le hdPm (hQm s₀ hs₀) ξ
  · exact enorm_convC_le (hPm s₀ hs₀) hdQm ξ

private theorem lintegral_coef_le (m : ℕ) (c : Space → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ η, ‖c η‖ ^ 2 ≤ C * hsWeight m η) (f : Space → CSpace) (i : Fin 3) :
    ∫⁻ η, ‖c η * f η i‖ₑ ^ 2 ≤ ENNReal.ofReal C * hsNormSq m f := by
  unfold hsNormSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  have hw : 0 ≤ hsWeight m η := by unfold hsWeight; positivity
  have e1 : ‖c η * f η i‖ₑ ^ 2 = ENNReal.ofReal (‖c η‖ ^ 2 * ‖f η i‖ ^ 2) := by
    rw [← ofReal_norm, norm_mul, ← ENNReal.ofReal_pow (by positivity), mul_pow]
  have e2 : ENNReal.ofReal C * (ENNReal.ofReal (hsWeight m η) * ‖f η‖ₑ ^ 2) =
      ENNReal.ofReal (C * hsWeight m η * ‖f η‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hw,
      ← ENNReal.ofReal_mul hC, mul_assoc]
  rw [e1, e2]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul (hc η)
    (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ _) 2) (by positivity) (by positivity))

theorem continuousOn_advectionBilin_curve {m : ℕ} (hm : 1 ≤ m) {G : ℝ → Space → CSpace} {a b : ℝ}
    (hG : IsHsCurve m G a b) :
    ContinuousOn (fun p : Space × ℝ => advectionBilin (G p.2) (G p.2) p.1) (univ ×ˢ Icc a b) := by
  have hw1 : ∀ η : Space, 1 ≤ hsWeight m η := fun η => by
    unfold hsWeight
    exact one_le_pow₀ (by nlinarith [sq_nonneg ‖η‖])
  have hwη : ∀ η : Space, ‖η‖ ^ 2 ≤ hsWeight m η := fun η => by
    unfold hsWeight
    calc ‖η‖ ^ 2 ≤ 1 + ‖η‖ ^ 2 := by linarith
      _ = (1 + ‖η‖ ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ (1 + ‖η‖ ^ 2) ^ m := pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖η‖]) hm
  have hc1 : ∀ η : Space, ‖(1 : ℂ)‖ ^ 2 ≤ 1 * hsWeight m η := fun η => by
    simpa using hw1 η
  have hc2 : ∀ j : Fin 3, ∀ η : Space, ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)‖ ^ 2 ≤
      (4 * π ^ 2) * hsWeight m η := fun j η => by
    have hj : |η j| ≤ ‖η‖ := by
      have := PiLp.norm_apply_le η j
      simpa [Real.norm_eq_abs] using this
    have hn : ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)‖ = 2 * π * |η j| := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hn]
    have h1 : (2 * π * |η j|) ^ 2 ≤ 4 * π ^ 2 * ‖η‖ ^ 2 := by
      have : |η j| ^ 2 ≤ ‖η‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hj 2
      nlinarith [sq_nonneg π]
    nlinarith [hwη η, sq_nonneg π]
  have hcurve : ∀ (c : Space → ℂ) (C : ℝ), 0 ≤ C → Continuous c → (∀ η, ‖c η‖ ^ 2 ≤ C * hsWeight m η) →
      ∀ i : Fin 3,
      (∀ s ∈ Icc a b, AEStronglyMeasurable (fun η => c η * G s η i) volume) ∧
      (∀ s ∈ Icc a b, ∫⁻ η, ‖c η * G s η i‖ₑ ^ 2 ≠ ⊤) ∧
      (∀ s₀ ∈ Icc a b, Tendsto (fun s => ∫⁻ η, ‖c η * G s η i - c η * G s₀ η i‖ₑ ^ 2)
        (𝓝[Icc a b] s₀) (𝓝 0)) := by
    intro c C hC hcc hc i
    have hcomp : Continuous (fun z : CSpace => z i) := by fun_prop
    refine ⟨fun s hs => hcc.aestronglyMeasurable.mul (hcomp.comp_aestronglyMeasurable (hG.1 s hs).1),
      fun s hs => ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hG.1 s hs).2.ne)
        (lintegral_coef_le m c C hC hc (G s) i), fun s₀ hs₀ => ?_⟩
    have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) (hG.2 s₀ hs₀) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun s => ?_)
    have h := lintegral_coef_le m c C hC hc (G s - G s₀) i
    refine le_of_eq_of_le ?_ h
    congr 1
    funext η
    simp [mul_sub]
  have hpi : Continuous (fun p : Space × ℝ => fun i : Fin 3 => ∑ j, convC (fun η => G p.2 η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * G p.2 η i) p.1) → True := fun _ => trivial
  clear hpi
  have hij : ∀ i j : Fin 3, ContinuousOn (fun p : Space × ℝ => convC (fun η => G p.2 η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * G p.2 η i) p.1) (univ ×ˢ Icc a b) := by
    intro i j
    obtain ⟨m1, f1, c1⟩ := hcurve (fun _ => 1) 1 zero_le_one continuous_const hc1 j
    obtain ⟨m2, f2, c2⟩ := hcurve (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)) (4 * π ^ 2)
      (by positivity) (by fun_prop) (hc2 j) i
    simp only [one_mul] at m1 f1 c1
    exact continuousOn_convC_param (P := fun s η => G s η j)
      (Q := fun s η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * G s η i) m1 m2 f1 f2 c1 c2
  unfold advectionBilin
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn ?_
  exact continuousOn_pi.2 fun i => continuousOn_finsetSum _ fun j _ => hij i j

end Breakdown.SmoothFlow

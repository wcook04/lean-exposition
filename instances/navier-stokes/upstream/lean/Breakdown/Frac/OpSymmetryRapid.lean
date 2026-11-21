import Breakdown.Frac.StOperator

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace FracInternal

private theorem rapid_norm_remainder_le_far (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
    ‖secondOrderRemainder f x z‖ ≤
      ‖f (x + z)‖ + (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hD : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have hD2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖z‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two, sq] using this
  have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    nlinarith
  unfold secondOrderRemainder
  have n1 := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z) ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have n2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have n3 := norm_sub_le (f (x + z)) (f x)
  have p1 : ‖f x‖ ≤ ‖f x‖ * ‖z‖ ^ 2 := le_mul_of_one_le_right (norm_nonneg _) h2
  have p2 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  nlinarith

private theorem rapid_integrable_of_near_far {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    {a b C : ℝ} (ha : a < 3) (hb : 3 < b) (hnear : ∀ z : Space, ‖z‖ ≤ 1 → ‖f z‖ ≤ C * ‖z‖ ^ (-a))
    (hfar : ∀ z : Space, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-b)) : Integrable f := by
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hC : 0 ≤ C := by
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    have := hfar (EuclideanSpace.single 0 1) hn.ge
    rw [hn, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hball : IntegrableOn f (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := C) (by rw [hfin]; norm_num)
      (by rw [hfin]; exact_mod_cast ha) ?_ hf
    refine (ae_restrict_mem measurableSet_ball).mono fun z hz => hnear z ?_
    have : ‖z‖ < 1 := by simpa using hz
    exact this.le
  have hcomp : IntegrableOn f (Metric.ball (0 : Space) 1)ᶜ volume := by
    have hint : Integrable (fun z : Space => (1 + ‖z‖) ^ (-b)) :=
      integrable_one_add_norm (by rw [hfin]; exact_mod_cast hb)
    refine Integrable.mono' ((hint.const_mul (C * 2 ^ b)).integrableOn) hf.restrict ?_
    refine (ae_restrict_mem measurableSet_ball.compl).mono fun z hz => ?_
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hzpos : 0 < ‖z‖ := by linarith
    have key : ‖z‖ ^ (-b) ≤ 2 ^ b * (1 + ‖z‖) ^ (-b) := by
      rw [Real.rpow_neg hzpos.le, Real.rpow_neg (by positivity), ← div_eq_mul_inv]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      rw [div_mul_eq_mul_div, one_le_div (by positivity), ← Real.mul_rpow (by norm_num) hzpos.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc ‖f z‖ ≤ C * ‖z‖ ^ (-b) := hfar z hz1
      _ ≤ C * (2 ^ b * (1 + ‖z‖) ^ (-b)) := mul_le_mul_of_nonneg_left key hC
      _ = C * 2 ^ b * (1 + ‖z‖) ^ (-b) := by ring
  have := hball.union hcomp
  rwa [Set.union_compl_self, integrableOn_univ] at this

private theorem rapid_rpow_mul_pow (t r : ℝ) (ht : 0 ≤ t) (n : ℕ) (hr : r ≠ 0) (hrn : r + n ≠ 0) :
    t ^ r * t ^ n = t ^ (r + n) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hr, Real.zero_rpow hrn, zero_mul]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]

private theorem rapid_continuous_remainder (v : Space → Space) (hv : ContDiff ℝ ∞ v) :
    Continuous (fun p : Space × Space => secondOrderRemainder v p.1 p.2) := by
  unfold secondOrderRemainder
  have h0 : Continuous v := hv.continuous
  have h1 : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 v) :=
    hv.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have hvec : Continuous (fun p : Space × Space => ![p.2, p.2]) :=
    Continuous.matrixVecCons continuous_snd (Continuous.matrixVecCons continuous_snd continuous_const)
  have h3 : Continuous (fun p : Space × Space => iteratedFDeriv ℝ 2 v p.1 ![p.2, p.2]) :=
    (h2.comp continuous_fst).eval hvec
  have h4 : Continuous (fun p : Space × Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 v p.1 ![p.2, p.2]) :=
    h3.const_smul (1 / 2 : ℝ)
  refine Continuous.sub ?_ h4
  refine Continuous.sub ?_ ((h1.comp continuous_fst).clm_apply continuous_snd)
  exact (h0.comp (continuous_fst.add continuous_snd)).sub (h0.comp continuous_fst)

private theorem rapid_norm_second_le (f : Space → Space) (x z : Space) :
    ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖z‖ ^ 2 := by
  have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
  simpa [Fin.prod_univ_two, sq] using this

private theorem rapid_second_eq (f : Space → Space) (hf : ContDiff ℝ ∞ f) (x z : Space) :
    iteratedFDeriv ℝ 2 f x ![z, z] = fderiv ℝ (fun y => fderiv ℝ f y z) x z := by
  obtain ⟨_, hf1⟩ := contDiff_infty_iff_fderiv.1 hf
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (contDiff_infty_iff_fderiv.1 hf1).1 x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const z)]
  simp [fderiv_fun_const]

private theorem rapid_integrable_inner (g ψ : Space → Space) (hg : Continuous g) (B : ℝ)
    (hB : ∀ x, ‖g x‖ ≤ B) (hψ : Integrable ψ) : Integrable (fun x => inner ℝ (g x) (ψ x)) := by
  refine (hψ.norm.const_mul B).mono' (hg.aestronglyMeasurable.inner hψ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

private theorem rapid_integrable_fderiv_apply (ψ : Space → Space) (hψ : ContDiff ℝ ∞ ψ)
    (h : Integrable (fun x => ‖fderiv ℝ ψ x‖)) (z : Space) :
    Integrable (fun x => fderiv ℝ ψ x z) :=
  (h.mul_const ‖z‖).mono' ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (fderiv ℝ ψ x).le_opNorm z)

private theorem rapid_integrable_second (ψ : Space → Space) (hψ : ContDiff ℝ ∞ ψ)
    (h : Integrable (fun x => ‖iteratedFDeriv ℝ 2 ψ x‖)) (z : Space) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ ψ y z) x z) := by
  have e : (fun x => fderiv ℝ (fun y => fderiv ℝ ψ y z) x z) =
      fun x => iteratedFDeriv ℝ 2 ψ x ![z, z] := funext fun x => (rapid_second_eq ψ hψ x z).symm
  rw [e]
  refine (h.mul_const (‖z‖ ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun x => rapid_norm_second_le ψ x z)
  exact ((hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).eval
    continuous_const).aestronglyMeasurable

private theorem rapid_ibp (f g : Space → Space) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (z : Space) (B0 B1 : ℝ) (hB0 : ∀ x, ‖f x‖ ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ f x z‖ ≤ B1)
    (hgi : Integrable g) (hg'i : Integrable (fun x => fderiv ℝ g x z)) :
    ∫ x, inner ℝ (fderiv ℝ f x z) (g x) = -∫ x, inner ℝ (f x) (fderiv ℝ g x z) := by
  obtain ⟨hfd, hf1⟩ := contDiff_infty_iff_fderiv.1 hf
  obtain ⟨hgd, _⟩ := contDiff_infty_iff_fderiv.1 hg
  have hfc1 : Continuous (fun x => fderiv ℝ f x z) := hf1.continuous.clm_apply continuous_const
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := innerSL ℝ) (f := f) (g := g) (v := z)
    (rapid_integrable_inner _ _ hfc1 B1 hB1 hgi)
    (rapid_integrable_inner _ _ hf.continuous B0 hB0 hg'i)
    (rapid_integrable_inner _ _ hf.continuous B0 hB0 hgi)
    (fun x _ => hfd x) (fun x _ => hgd x)
  have h' : ∫ x, inner ℝ (f x) (fderiv ℝ g x z) = -∫ x, inner ℝ (fderiv ℝ f x z) (g x) := h
  rw [h', neg_neg]

private theorem rapid_shift_identity (v ψ : Space → Space) (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    (C : ℝ) (b0 : ∀ y, ‖v y‖ ≤ C) (b1 : ∀ y, ‖fderiv ℝ v y‖ ≤ C)
    (b2 : ∀ y, ‖iteratedFDeriv ℝ 2 v y‖ ≤ C) (i0 : Integrable ψ)
    (i1 : Integrable (fun x => ‖fderiv ℝ ψ x‖)) (i2 : Integrable (fun x => ‖iteratedFDeriv ℝ 2 ψ x‖))
    (z : Space) :
    ∫ x, inner ℝ (secondOrderRemainder v x z) (ψ x) =
      ∫ x, inner ℝ (v x) (secondOrderRemainder ψ x (-z)) := by
  obtain ⟨_, hv1⟩ := contDiff_infty_iff_fderiv.1 hv
  obtain ⟨_, hψ1⟩ := contDiff_infty_iff_fderiv.1 hψ
  have hw : ContDiff ℝ ∞ (fun y => fderiv ℝ v y z) := hv1.clm_apply contDiff_const
  have hq : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y z) := hψ1.clm_apply contDiff_const
  have hw2c : Continuous (fun y => fderiv ℝ (fun u => fderiv ℝ v u z) y z) :=
    ((contDiff_infty_iff_fderiv.1 hw).2.clm_apply contDiff_const).continuous
  have bw : ∀ x, ‖fderiv ℝ v x z‖ ≤ C * ‖z‖ := fun x =>
    ((fderiv ℝ v x).le_opNorm z).trans (mul_le_mul_of_nonneg_right (b1 x) (norm_nonneg _))
  have bw2 : ∀ x, ‖fderiv ℝ (fun u => fderiv ℝ v u z) x z‖ ≤ C * ‖z‖ ^ 2 := by
    intro x
    rw [← rapid_second_eq v hv x z]
    exact (rapid_norm_second_le v x z).trans (mul_le_mul_of_nonneg_right (b2 x) (by positivity))
  have iq : Integrable (fun x => fderiv ℝ ψ x z) := rapid_integrable_fderiv_apply ψ hψ i1 z
  have iq2 : Integrable (fun x => fderiv ℝ (fun u => fderiv ℝ ψ u z) x z) :=
    rapid_integrable_second ψ hψ i2 z
  have T0 : ∫ x, inner ℝ (v (x + z)) (ψ x) = ∫ x, inner ℝ (v x) (ψ (x - z)) := by
    have := integral_add_right_eq_self (μ := volume) (fun x => inner ℝ (v x) (ψ (x - z))) z
    simpa using this
  have T2 := rapid_ibp v ψ hv hψ z C (C * ‖z‖) b0 bw i0 iq
  have T3a := rapid_ibp (fun y => fderiv ℝ v y z) ψ hw hψ z (C * ‖z‖) (C * ‖z‖ ^ 2) bw bw2 i0 iq
  have T3b := rapid_ibp v (fun y => fderiv ℝ ψ y z) hv hq z C (C * ‖z‖) b0 bw iq iq2
  have hvc := hv.continuous
  have k0 : Integrable (fun x => inner ℝ (v (x + z)) (ψ x)) :=
    rapid_integrable_inner _ _ (hvc.comp (continuous_add_const z)) C (fun x => b0 _) i0
  have k1 : Integrable (fun x => inner ℝ (v x) (ψ x)) := rapid_integrable_inner v ψ hvc C b0 i0
  have k2 : Integrable (fun x => inner ℝ (fderiv ℝ v x z) (ψ x)) :=
    rapid_integrable_inner _ ψ hw.continuous _ bw i0
  have k3 : Integrable (fun x => inner ℝ (fderiv ℝ (fun u => fderiv ℝ v u z) x z) (ψ x)) :=
    rapid_integrable_inner _ ψ hw2c _ bw2 i0
  have l0 : Integrable (fun x => inner ℝ (v x) (ψ (x - z))) :=
    rapid_integrable_inner v _ hvc C b0 (i0.comp_sub_right z)
  have l2 : Integrable (fun x => inner ℝ (v x) (fderiv ℝ ψ x z)) :=
    rapid_integrable_inner v _ hvc C b0 iq
  have l3 : Integrable (fun x => inner ℝ (v x) (fderiv ℝ (fun u => fderiv ℝ ψ u z) x z)) :=
    rapid_integrable_inner v _ hvc C b0 iq2
  have hL : ∀ x, inner ℝ (secondOrderRemainder v x z) (ψ x) =
      inner ℝ (v (x + z)) (ψ x) - inner ℝ (v x) (ψ x) - inner ℝ (fderiv ℝ v x z) (ψ x)
        - (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (fun u => fderiv ℝ v u z) x z) (ψ x) := by
    intro x
    simp only [secondOrderRemainder, rapid_second_eq v hv x z, inner_sub_left, real_inner_smul_left]
  have hR : ∀ x, inner ℝ (v x) (secondOrderRemainder ψ x (-z)) =
      inner ℝ (v x) (ψ (x - z)) - inner ℝ (v x) (ψ x) + inner ℝ (v x) (fderiv ℝ ψ x z)
        - (1 / 2 : ℝ) * inner ℝ (v x) (fderiv ℝ (fun u => fderiv ℝ ψ u z) x z) := by
    intro x
    have e : iteratedFDeriv ℝ 2 ψ x ![-z, -z] = iteratedFDeriv ℝ 2 ψ x ![z, z] := by
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      simp
    simp only [secondOrderRemainder, e, rapid_second_eq ψ hψ x z, inner_sub_right,
      real_inner_smul_right, map_neg, inner_neg_right, ← sub_eq_add_neg]
    ring
  simp_rw [hL, hR]
  rw [integral_sub, integral_sub, integral_sub, integral_const_mul, integral_sub, integral_add,
    integral_sub, integral_const_mul]
  · rw [T0, T2, T3a, T3b]
    ring
  all_goals first
    | exact k0 | exact k1 | exact k2 | exact l0 | exact l2 | exact k0.sub k1 | exact l0.sub k1
    | exact (k0.sub k1).sub k2 | exact (l0.sub k1).add l2 | exact k3.const_mul _
    | exact l3.const_mul _

private theorem rapid_integrable_prod (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (F : Space → Space → ℝ) (hF : Continuous (fun p : Space × Space => F p.1 p.2))
    (G : Space → ℝ) (hG : Integrable G) (hG0 : ∀ x, 0 ≤ G x)
    (hnear : ∀ x z, ‖z‖ ≤ 1 → |F x z| ≤ G x * ‖z‖ ^ 3)
    (hfar : ∀ x z, 1 ≤ ‖z‖ → |F x z| ≤ G x * ‖z‖ ^ 2 + G (x + z)) :
    Integrable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * F p.1 p.2)
      (volume.prod volume) := by
  have hKm : Measurable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α))) :=
    (measurable_snd.norm).pow_const _
  have hFm : Measurable (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * F p.1 p.2) :=
    hKm.mul hF.measurable
  have hc0 : 0 ≤ ∫ x, G x := integral_nonneg hG0
  have hGt : ∀ z : Space, Integrable (fun x => G (x + z)) := fun z => hG.comp_add_right z
  have hGtI : ∀ z : Space, ∫ x, G (x + z) = ∫ x, G x := fun z =>
    integral_add_right_eq_self (fun x => G x) z
  have hbound : ∀ z : Space, ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * F x z‖ ≤
      ‖z‖ ^ (-(3 + 2 * α)) * (G x * (‖z‖ ^ 3 + ‖z‖ ^ 2) + G (x + z)) := by
    intro z x
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have h3 : 0 ≤ G x * ‖z‖ ^ 3 := mul_nonneg (hG0 x) (by positivity)
    have h2 : 0 ≤ G x * ‖z‖ ^ 2 := mul_nonneg (hG0 x) (by positivity)
    have hGz := hG0 (x + z)
    rcases le_total ‖z‖ 1 with h | h
    · have := hnear x z h
      nlinarith
    · have := hfar x z h
      nlinarith
  have hsec : ∀ z : Space, Integrable (fun x => ‖z‖ ^ (-(3 + 2 * α)) * F x z) := by
    intro z
    refine Integrable.mono' (((hG.mul_const (‖z‖ ^ 3 + ‖z‖ ^ 2)).add (hGt z)).const_mul _) ?_
      (Filter.Eventually.of_forall (hbound z))
    exact (continuous_const.mul (hF.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  apply rapid_integrable_of_near_far (a := 2 * α) (b := 1 + 2 * α) (C := 2 * ∫ x, G x)
  · exact (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume)).aestronglyMeasurable
  · linarith
  · linarith
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * F x z‖ ≤ (‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 3) * G x := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      exact (hnear x z hz).trans_eq (mul_comm _ _)
    have he := rapid_rpow_mul_pow ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 3 (by linarith)
      (by push_cast; linarith)
    have he' : -(3 + 2 * α) + ((3 : ℕ) : ℝ) = -(2 * α) := by push_cast; ring
    rw [he'] at he
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * F x z‖
        ≤ ∫ x, (‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 3) * G x :=
          integral_mono (hsec z).norm (hG.const_mul _) hpt
      _ = (∫ x, G x) * ‖z‖ ^ (-(2 * α)) := by
          rw [integral_const_mul, he]
          ring
      _ ≤ (2 * ∫ x, G x) * ‖z‖ ^ (-(2 * α)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * F x z‖ ≤
        ‖z‖ ^ (-(3 + 2 * α)) * (G x * ‖z‖ ^ 2 + G (x + z)) := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hfar x z hz) hK0
    have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
    have he := rapid_rpow_mul_pow ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 2 (by linarith)
      (by push_cast; linarith)
    have he' : -(3 + 2 * α) + ((2 : ℕ) : ℝ) = -(1 + 2 * α) := by push_cast; ring
    rw [he'] at he
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * F x z‖
        ≤ ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * (G x * ‖z‖ ^ 2 + G (x + z)) :=
          integral_mono (hsec z).norm (((hG.mul_const _).add (hGt z)).const_mul _) hpt
      _ = ‖z‖ ^ (-(3 + 2 * α)) * ((∫ x, G x) * ‖z‖ ^ 2 + ∫ x, G x) := by
          rw [integral_const_mul, integral_add (hG.mul_const _) (hGt z), integral_mul_const, hGtI]
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ((2 * ∫ x, G x) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          nlinarith
      _ = (2 * ∫ x, G x) * ‖z‖ ^ (-(1 + 2 * α)) := by
          rw [← he]
          ring

private theorem rapid_third_decay (φ : SchwartzMap Space Space) :
    ∃ H : Space → ℝ, Integrable H ∧ (∀ x, 0 ≤ H x) ∧
      ∀ x y, dist y x ≤ 1 → ‖iteratedFDeriv ℝ 3 φ y‖ ≤ H x := by
  obtain ⟨Ca, hCa0, hCa⟩ := φ.decay 0 3
  obtain ⟨Cb, hCb0, hCb⟩ := φ.decay 4 3
  refine ⟨fun x => 128 * (Ca + Cb) * (1 + ‖x‖) ^ (-(4 : ℝ)), ?_, fun x => by positivity, ?_⟩
  · exact (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul _
  · intro x y hxy
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
    have hd0 : 0 ≤ ‖iteratedFDeriv ℝ 3 φ y‖ := norm_nonneg _
    have ha := hCa y
    have hb := hCb y
    rw [pow_zero, one_mul] at ha
    have hxy' : ‖x‖ ≤ ‖y‖ + 1 := by
      have h1 := norm_sub_norm_le x y
      rw [dist_eq_norm, norm_sub_rev] at hxy
      linarith
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have key : (1 + ‖x‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖ ≤ 128 * (Ca + Cb) := by
      have e1 : (1 + ‖x‖) ^ 4 ≤ (2 * (1 + ‖y‖)) ^ 4 :=
        pow_le_pow_left₀ hpos.le (by linarith) 4
      have e2 : (1 + ‖y‖) ^ 4 ≤ 8 * (1 + ‖y‖ ^ 4) := by
        nlinarith [mul_nonneg (sq_nonneg (‖y‖ - 1))
          (by positivity : (0 : ℝ) ≤ 7 * ‖y‖ ^ 2 + 10 * ‖y‖ + 7)]
      calc (1 + ‖x‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖
          ≤ (2 * (1 + ‖y‖)) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖ := mul_le_mul_of_nonneg_right e1 hd0
        _ = 16 * ((1 + ‖y‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖) := by ring
        _ ≤ 16 * ((8 * (1 + ‖y‖ ^ 4)) * ‖iteratedFDeriv ℝ 3 φ y‖) := by gcongr
        _ = 128 * (‖iteratedFDeriv ℝ 3 φ y‖ + ‖y‖ ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖) := by ring
        _ ≤ 128 * (Ca + Cb) := by linarith
    have hrp : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hpos.le]
      norm_cast
    show ‖iteratedFDeriv ℝ 3 φ y‖ ≤ 128 * (Ca + Cb) * (1 + ‖x‖) ^ (-(4 : ℝ))
    rw [hrp, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith

private theorem rapid_uniform_bounds (v : Space → Space)
    (hvb : ∀ j ≤ 3, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j v y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y, ‖v y‖ ≤ C) ∧ (∀ y, ‖fderiv ℝ v y‖ ≤ C) ∧
      (∀ y, ‖iteratedFDeriv ℝ 2 v y‖ ≤ C) ∧ (∀ y, ‖iteratedFDeriv ℝ 3 v y‖ ≤ C) := by
  obtain ⟨C0, h0⟩ := hvb 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hvb 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hvb 2 (by norm_num)
  obtain ⟨C3, h3⟩ := hvb 3 (by norm_num)
  refine ⟨max (max C0 C1) (max (max C2 C3) 0), le_max_of_le_right (le_max_right _ _),
    fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have := h0 y
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_of_le_left (le_max_left _ _))
  · have := h1 y
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (le_max_of_le_left (le_max_right _ _))
  · exact (h2 y).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
  · exact (h3 y).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))

private theorem rapid_left_prod (h1 : RemainderBoundStatement) (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (v : Space → Space) (hv : ContDiff ℝ ∞ v) (C : ℝ) (hC0 : 0 ≤ C) (b0 : ∀ y, ‖v y‖ ≤ C)
    (b1 : ∀ y, ‖fderiv ℝ v y‖ ≤ C) (b2 : ∀ y, ‖iteratedFDeriv ℝ 2 v y‖ ≤ C)
    (b3 : ∀ y, ‖iteratedFDeriv ℝ 3 v y‖ ≤ C) (ψ : Space → Space) (hψ : Continuous ψ)
    (hψi : Integrable ψ) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v p.1 p.2) (ψ p.1))
      (volume.prod volume) := by
  have hv3 : ContDiff ℝ 3 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF : Continuous (fun p : Space × Space => inner ℝ (secondOrderRemainder v p.1 p.2) (ψ p.1)) :=
    (rapid_continuous_remainder v hv).inner (hψ.comp continuous_fst)
  refine rapid_integrable_prod α hα1 hα2 (fun x z => inner ℝ (secondOrderRemainder v x z) (ψ x)) hF
    (fun x => 4 * C * ‖ψ x‖) ((hψi.norm).const_mul _) (fun x => by positivity) ?_ ?_
  · intro x z hz
    have hR := h1 v hv3 x z C (fun y _ => b3 y)
    have hψ0 := norm_nonneg (ψ x)
    have hz3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    calc |inner ℝ (secondOrderRemainder v x z) (ψ x)|
        ≤ ‖secondOrderRemainder v x z‖ * ‖ψ x‖ := abs_real_inner_le_norm _ _
      _ ≤ (C * ‖z‖ ^ 3) * ‖ψ x‖ := mul_le_mul_of_nonneg_right hR hψ0
      _ ≤ 4 * C * ‖ψ x‖ * ‖z‖ ^ 3 := by nlinarith [mul_nonneg (mul_nonneg hC0 hψ0) hz3]
  · intro x z hz
    have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
    have hRf := rapid_norm_remainder_le_far v x z hz
    have hRb : ‖secondOrderRemainder v x z‖ ≤ 4 * C * ‖z‖ ^ 2 := by
      have e0 := b0 (x + z)
      have e1 : (‖v x‖ + ‖fderiv ℝ v x‖ + ‖iteratedFDeriv ℝ 2 v x‖) * ‖z‖ ^ 2 ≤ (3 * C) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [b0 x, b1 x, b2 x]) (by positivity)
      nlinarith
    have hψ0 := norm_nonneg (ψ x)
    have hψ1 := norm_nonneg (ψ (x + z))
    calc |inner ℝ (secondOrderRemainder v x z) (ψ x)|
        ≤ ‖secondOrderRemainder v x z‖ * ‖ψ x‖ := abs_real_inner_le_norm _ _
      _ ≤ (4 * C * ‖z‖ ^ 2) * ‖ψ x‖ := mul_le_mul_of_nonneg_right hRb hψ0
      _ ≤ 4 * C * ‖ψ x‖ * ‖z‖ ^ 2 + 4 * C * ‖ψ (x + z)‖ := by
          nlinarith [mul_nonneg hC0 hψ1]

private theorem rapid_right_prod (h1 : RemainderBoundStatement) (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (v : Space → Space) (hv : Continuous v) (C : ℝ) (hC0 : 0 ≤ C) (b0 : ∀ y, ‖v y‖ ≤ C)
    (φ : SchwartzMap Space Space) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2))
      (volume.prod volume) := by
  have hφs : ContDiff ℝ ∞ (φ : Space → Space) := φ.smooth ⊤
  have hφ3 : ContDiff ℝ 3 (φ : Space → Space) := hφs.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨H, hHi, hH0, hHb⟩ := rapid_third_decay φ
  have iφ : Integrable (fun x => ‖φ x‖) := φ.integrable.norm
  have iφ1 : Integrable (fun x => ‖fderiv ℝ φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 1
  have iφ2 : Integrable (fun x => ‖iteratedFDeriv ℝ 2 φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 2
  have hF : Continuous (fun p : Space × Space => inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) :=
    (hv.comp continuous_fst).inner (rapid_continuous_remainder φ hφs)
  refine rapid_integrable_prod α hα1 hα2 (fun x z => inner ℝ (v x) (secondOrderRemainder φ x z)) hF
    (fun x => C * (H x + ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖))
    ((((hHi.add iφ).add iφ1).add iφ2).const_mul C)
    (fun x => mul_nonneg hC0 (by have := hH0 x; positivity)) ?_ ?_
  · intro x z hz
    have hR := h1 φ hφ3 x z (H x) (fun y hy => hHb x y ((Metric.mem_closedBall.1 hy).trans hz))
    have hz3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have p1 : 0 ≤ C * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 3 :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) hz3
    calc |inner ℝ (v x) (secondOrderRemainder φ x z)|
        ≤ ‖v x‖ * ‖secondOrderRemainder φ x z‖ := abs_real_inner_le_norm _ _
      _ ≤ C * (H x * ‖z‖ ^ 3) := mul_le_mul (b0 x) hR (norm_nonneg _) hC0
      _ ≤ C * (H x + ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 3 := by nlinarith
  · intro x z hz
    have hRf := rapid_norm_remainder_le_far φ x z hz
    have p1 : 0 ≤ C * H x * ‖z‖ ^ 2 := mul_nonneg (mul_nonneg hC0 (hH0 x)) (by positivity)
    have p2 : 0 ≤ C * (H (x + z) + ‖fderiv ℝ φ (x + z)‖ + ‖iteratedFDeriv ℝ 2 φ (x + z)‖) :=
      mul_nonneg hC0 (by have := hH0 (x + z); positivity)
    calc |inner ℝ (v x) (secondOrderRemainder φ x z)|
        ≤ ‖v x‖ * ‖secondOrderRemainder φ x z‖ := abs_real_inner_le_norm _ _
      _ ≤ C * (‖φ (x + z)‖ + (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2) :=
          mul_le_mul (b0 x) hRf (norm_nonneg _) hC0
      _ ≤ C * (H x + ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2 +
          C * (H (x + z) + ‖φ (x + z)‖ + ‖fderiv ℝ φ (x + z)‖ + ‖iteratedFDeriv ℝ 2 φ (x + z)‖) := by
          nlinarith

end FracInternal

open FracInternal in
theorem symmetryRapid_of (h1 : RemainderBoundStatement) (h2 : RemainderIntegrableStatement) :
    SymmetryRapidStatement := by
  intro α hα1 hα2 v hv hvb φ
  obtain ⟨C, hC0, b0, b1, b2, b3⟩ := rapid_uniform_bounds v hvb
  have hφs : ContDiff ℝ ∞ (φ : Space → Space) := φ.smooth ⊤
  obtain ⟨Cφ, -, hCφ⟩ := φ.decay 0 0
  have hφb : ∀ y, ‖φ y‖ ≤ Cφ := fun y => by simpa using hCφ y
  have iφ1 : Integrable (fun x => ‖fderiv ℝ φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 1
  have iφ2 : Integrable (fun x => ‖iteratedFDeriv ℝ 2 φ x‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 2
  have hPL := rapid_left_prod h1 α hα1 hα2 v hv C hC0 b0 b1 b2 b3 φ φ.continuous φ.integrable
  have hPR := rapid_right_prod h1 α hα1 hα2 v hv.continuous C hC0 b0 φ
  have hLx : ∀ x, inner ℝ (fractionalPowerAt α v x) (φ x) = (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v x z) (φ x) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_left, real_inner_comm, ← integral_inner (h2 α hα1 hα2 v hv (Or.inr ⟨C, b0⟩) x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
    rw [real_inner_comm]
  have hRx : ∀ x, inner ℝ (v x) (fractionalPowerAt α φ x) = (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_right, ← integral_inner (h2 α hα1 hα2 φ hφs (Or.inr ⟨Cφ, hφb⟩) x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  have hLfun : (fun x => inner ℝ (fractionalPowerAt α v x) (φ x)) = fun x =>
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v x z) (φ x) := funext hLx
  have hRfun : (fun x => inner ℝ (v x) (fractionalPowerAt α φ x)) = fun x =>
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z) := funext hRx
  refine ⟨?_, ?_, ?_⟩
  · rw [hLfun]
    exact hPL.integral_prod_left.const_mul _
  · rw [hRfun]
    exact hPR.integral_prod_left.const_mul _
  · rw [hLfun, hRfun, integral_const_mul, integral_const_mul]
    congr 1
    have sL := integral_integral_swap (f := fun x z : Space =>
      ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v x z) (φ x)) hPL
    have sR := integral_integral_swap (f := fun x z : Space =>
      ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)) hPR
    rw [sL, sR]
    have e1 : ∀ z : Space, ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v x z) (φ x) =
        (fun w : Space => ‖w‖ ^ (-(3 + 2 * α)) *
          ∫ x, inner ℝ (v x) (secondOrderRemainder φ x w)) (-z) := by
      intro z
      rw [integral_const_mul, rapid_shift_identity v φ hv hφs C b0 b1 b2 φ.integrable iφ1 iφ2 z]
      simp only [norm_neg]
    refine (integral_congr_ae (Filter.Eventually.of_forall e1)).trans ?_
    refine (integral_neg_eq_self (fun w : Space => ‖w‖ ^ (-(3 + 2 * α)) *
      ∫ x, inner ℝ (v x) (secondOrderRemainder φ x w)) (volume : Measure Space)).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [integral_const_mul]

end Breakdown

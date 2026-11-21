import Breakdown.Frac.StSpace
import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpIntegrable
import Breakdown.Uniqueness.PressureMollifyAux

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace FracInternal

private theorem norm_remainder_le_far (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
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

private theorem integrable_of_near_far {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {a b C : ℝ}
    (ha : a < 3) (hb : 3 < b) (hnear : ∀ z : Space, ‖z‖ ≤ 1 → ‖f z‖ ≤ C * ‖z‖ ^ (-a))
    (hfar : ∀ z : Space, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-b)) : Integrable f := by
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hC : 0 ≤ C := by
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    have := hfar (EuclideanSpace.single 0 1) hn.ge
    rw [hn, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hball : IntegrableOn f (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := C) (by rw [hfin]; norm_num) (by rw [hfin]; exact_mod_cast ha) ?_ hf
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

private theorem exists_bound_translate (v φ : Space → Space) (hv : Continuous v)
    (hv2 : MemLp v 2 volume ∨ ∃ C : ℝ, ∀ y, ‖v y‖ ≤ C) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ A : ℝ, ∀ w : Space, Integrable (fun x => ‖v x‖ * ‖φ (x + w)‖) ∧ ∫ x, ‖v x‖ * ‖φ (x + w)‖ ≤ A := by
  have hint : ∀ w : Space, Integrable (fun x => ‖v x‖ * ‖φ (x + w)‖) := by
    intro w
    have hc : HasCompactSupport (fun x => φ (x + w)) := hφc.comp_homeomorph (Homeomorph.addRight w)
    refine (hv.norm.mul (hφ.comp (continuous_add_const w)).norm).integrable_of_hasCompactSupport ?_
    exact hc.norm.mul_left
  have hφi : Integrable (fun x => ‖φ x‖) := (hφ.integrable_of_hasCompactSupport hφc).norm
  rcases hv2 with hL | ⟨C, hC⟩
  · have hL2 : MemLp v ((2 : ℕ) : ENNReal) volume := by exact_mod_cast hL
    have hv2i : Integrable (fun x => ‖v x‖ ^ 2) := hL2.integrable_norm_pow two_ne_zero
    have hφL : MemLp φ ((2 : ℕ) : ENNReal) volume := hφ.memLp_of_hasCompactSupport hφc
    have hφ2i : Integrable (fun x => ‖φ x‖ ^ 2) := hφL.integrable_norm_pow two_ne_zero
    refine ⟨(∫ x, ‖v x‖ ^ 2) + ∫ x, ‖φ x‖ ^ 2, fun w => ⟨hint w, ?_⟩⟩
    have hs : Integrable (fun x => ‖φ (x + w)‖ ^ 2) := hφ2i.comp_add_right w
    calc ∫ x, ‖v x‖ * ‖φ (x + w)‖ ≤ ∫ x, (‖v x‖ ^ 2 + ‖φ (x + w)‖ ^ 2) := by
          refine integral_mono (hint w) (hv2i.add hs) fun x => ?_
          nlinarith [sq_nonneg (‖v x‖ - ‖φ (x + w)‖), norm_nonneg (v x), norm_nonneg (φ (x + w))]
      _ = (∫ x, ‖v x‖ ^ 2) + ∫ x, ‖φ x‖ ^ 2 := by
          rw [integral_add hv2i hs, integral_add_right_eq_self (fun x => ‖φ x‖ ^ 2) w]
  · refine ⟨C * ∫ x, ‖φ x‖, fun w => ⟨hint w, ?_⟩⟩
    calc ∫ x, ‖v x‖ * ‖φ (x + w)‖ ≤ ∫ x, C * ‖φ (x + w)‖ := by
          refine integral_mono (hint w) ((hφi.comp_add_right w).const_mul C) fun x => ?_
          exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
      _ = C * ∫ x, ‖φ x‖ := by
          rw [integral_const_mul, integral_add_right_eq_self (fun x => ‖φ x‖) w]


private lemma integrable_inner_compact_right (g ψ : Space → Space) (hg : Continuous g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => inner ℝ (g x) (ψ x)) := by
  refine (hg.inner hψ).integrable_of_hasCompactSupport ?_
  refine hψc.mono ?_
  intro x hx
  contrapose! hx
  rw [Function.notMem_support] at hx
  simp [hx]

private lemma iteratedFDeriv_two_eq_fderiv_apply (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (x z : Space) :
    iteratedFDeriv ℝ 2 f x ![z, z] = fderiv ℝ (fun y => fderiv ℝ f y z) x z := by
  obtain ⟨_, hf1⟩ := contDiff_infty_iff_fderiv.1 hf
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (contDiff_infty_iff_fderiv.1 hf1).1 x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const z)]
  simp [fderiv_fun_const]

private theorem rpow_mul_pow_eq_aux (t r : ℝ) (ht : 0 ≤ t) (n : ℕ) (hr : r ≠ 0) (hrn : r + n ≠ 0) :
    t ^ r * t ^ n = t ^ (r + n) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hr, Real.zero_rpow hrn, zero_mul]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]

private theorem continuous_remainder_pair (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun p : Space × Space => secondOrderRemainder φ p.1 p.2) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv (by norm_cast)
  have hm : Continuous (fun p : Space × Space => (![p.2, p.2] : Fin 2 → Space)) := by
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simpa using continuous_snd
  have hc := hφ.continuous
  have h3 : Continuous (fun p : Space × Space => iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) :=
    continuous_eval.comp ((h2.comp continuous_fst).prodMk hm)
  have h4 : Continuous (fun p : Space × Space => fderiv ℝ φ p.1 p.2) :=
    (h1.comp continuous_fst).clm_apply continuous_snd
  have h5 : Continuous (fun p : Space × Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) :=
    h3.const_smul (1 / 2 : ℝ)
  have h6 : Continuous (fun p : Space × Space => φ (p.1 + p.2)) := hc.comp (continuous_fst.add continuous_snd)
  have h7 : Continuous (fun p : Space × Space => φ p.1) := hc.comp continuous_fst
  exact ((h6.sub h7).sub h4).sub h5

private theorem continuous_remainder_section (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) (z : Space) :
    Continuous (fun x : Space => secondOrderRemainder φ x z) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv (by norm_cast)
  have hc := hφ.continuous
  have h3 : Continuous (fun x : Space => iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    continuous_eval.comp (h2.prodMk continuous_const)
  have h4 : Continuous (fun x : Space => fderiv ℝ φ x z) := h1.clm_apply continuous_const
  have h5 : Continuous (fun x : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    h3.const_smul (1 / 2 : ℝ)
  have h6 : Continuous (fun x : Space => φ (x + z)) := hc.comp (continuous_add_const z)
  exact ((h6.sub hc).sub h4).sub h5

private theorem remainder_eq_zero_of_far (φ : Space → Space) (x z : Space) {r : ℝ} (hz : ‖z‖ ≤ r)
    (hx : x ∉ Metric.cthickening r (tsupport φ)) : secondOrderRemainder φ x z = 0 := by
  have hx0 : x ∉ tsupport φ := fun h => hx (Metric.self_subset_cthickening _ h)
  have e1 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx0
  have e2 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx0
  have e3 : iteratedFDeriv ℝ 2 φ x = 0 := by
    by_contra h
    exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr h))
  have e4 : φ (x + z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    apply Metric.mem_cthickening_of_dist_le x (x + z) r _ h
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact hz
  simp [secondOrderRemainder, e1, e2, e3, e4]

private theorem integrable_prod_right_side (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (v φ : Space → Space) (hv : ContDiff ℝ ∞ v) (hv2 : MemLp v 2 volume ∨ ∃ C : ℝ, ∀ y, ‖v y‖ ≤ C)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) (volume.prod volume) := by
  have hα0 : 0 < α := by linarith
  have hvc : Continuous v := hv.continuous
  have hφ0 : Continuous φ := hφ.continuous
  have hRj := continuous_remainder_pair φ hφ
  have hRc : ∀ z, Continuous (fun x => secondOrderRemainder φ x z) := continuous_remainder_section φ hφ
  have hjoint : Continuous (fun p : Space × Space => inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) :=
    (hvc.comp continuous_fst).inner hRj
  have hFm : Measurable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) :=
    ((measurable_snd.norm).pow_const _).mul hjoint.measurable
  have hSc : IsCompact (tsupport φ) := hφc
  have hsec : ∀ z : Space, Integrable (fun x =>
      ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)) := by
    intro z
    refine (continuous_const.mul (hvc.inner (hRc z))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hSc.cthickening (r := ‖z‖)) (fun x hx => ?_)
    simp [remainder_eq_zero_of_far φ x z le_rfl hx]
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  have hT : IsCompact (Metric.cthickening 1 (tsupport φ)) := hSc.cthickening
  obtain ⟨C3, hC3⟩ := (hφ.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hφc.iteratedFDeriv 3)
  obtain ⟨A, hA⟩ := exists_bound_translate v φ hvc hv2 hφ0 hφc
  have hA0 : 0 ≤ A := le_trans (integral_nonneg (fun x => by positivity)) (hA 0).2
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_cast)
  have hvT : Integrable ((Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖)) :=
    (hvc.norm.continuousOn.integrableOn_compact hT).integrable_indicator hT.measurableSet
  have hzero : ∀ x, x ∉ tsupport φ →
      ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖ = 0 := by
    intro x hx0
    have e1 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx0
    have e2 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx0
    have e3 : iteratedFDeriv ℝ 2 φ x = 0 := by
      by_contra h
      exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr h))
    simp [e1, e2, e3]
  have hPc : Continuous (fun x => ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖)) :=
    hvc.norm.mul ((hφ0.norm.add (hφ.continuous_fderiv (by simp)).norm).add
      (hφ.continuous_iteratedFDeriv (m := 2) (by norm_cast)).norm)
  have hPi : Integrable (fun x => ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖)) := by
    refine hPc.integrable_of_hasCompactSupport (HasCompactSupport.intro hSc (fun x hx => ?_))
    rw [hzero x hx, mul_zero]
  set cP := ∫ x, ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) with hcP
  set I1 := ∫ x, (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x with hI1
  have hcP0 : 0 ≤ cP := integral_nonneg (fun x => by positivity)
  have hI10 : 0 ≤ I1 := integral_nonneg (fun x => Set.indicator_nonneg (fun y _ => norm_nonneg (v y)) x)
  set C3' := max C3 0 with hC3'
  have hC3'0 : 0 ≤ C3' := le_max_right _ _
  apply integrable_of_near_far (a := 2 * α) (b := 1 + 2 * α) (C := C3' * I1 + (A + cP))
  · exact (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume)).aestronglyMeasurable
  · linarith
  · linarith
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖ ≤
        (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport φ)
      · rw [Set.indicator_of_mem hx]
        calc |inner ℝ (v x) (secondOrderRemainder φ x z)| ≤ ‖v x‖ * ‖secondOrderRemainder φ x z‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ‖v x‖ * (C3' * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left
                (remainderBound φ hφ3 x z C3' (fun y _ => (hC3 y).trans (le_max_left _ _))) (norm_nonneg _)
          _ = C3' * (‖z‖ ^ 3 * ‖v x‖) := by ring
      · rw [Set.indicator_of_notMem hx, remainder_eq_zero_of_far φ x z hz hx]
        simp
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x :=
          integral_mono (hsec z).norm (hvT.const_mul _) hpt
      _ = (C3' * I1) * ‖z‖ ^ (-(2 * α)) := by
          rw [integral_const_mul]
          have := rpow_mul_pow_eq_aux ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 3 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((3 : ℕ) : ℝ) = -(2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(2 * α)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hg : Integrable (fun x => ‖v x‖ * ‖φ (x + z)‖) := (hA z).1
    have hgA : ∫ x, ‖v x‖ * ‖φ (x + z)‖ ≤ A := (hA z).2
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖ ≤
        ‖z‖ ^ (-(3 + 2 * α)) * (‖v x‖ * ‖φ (x + z)‖ +
          ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2) := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have := mul_le_mul_of_nonneg_left (norm_remainder_le_far φ x z hz) (norm_nonneg (v x))
      refine le_trans this (le_of_eq ?_)
      ring
    have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * (‖v x‖ * ‖φ (x + z)‖ +
          ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2) :=
          integral_mono (hsec z).norm ((hg.add (hPi.mul_const _)).const_mul _) hpt
      _ = ‖z‖ ^ (-(3 + 2 * α)) * ((∫ x, ‖v x‖ * ‖φ (x + z)‖) + cP * ‖z‖ ^ 2) := by
          rw [integral_const_mul, integral_add hg (hPi.mul_const _), integral_mul_const]
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ((A + cP) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          nlinarith
      _ = (A + cP) * ‖z‖ ^ (-(1 + 2 * α)) := by
          have := rpow_mul_pow_eq_aux ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 2 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((2 : ℕ) : ℝ) = -(1 + 2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(1 + 2 * α)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _)


private theorem gradField_contDiff {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (gradientAt h) := by
  show ContDiff ℝ ∞ (fun y => ∑ i : Fin 3, fderiv ℝ h y (unitVector i) • unitVector i)
  exact ContDiff.sum fun i _ =>
    (Internal.PressureMollify.contDiff_fderiv_apply hh _).smul contDiff_const

private theorem gradField_hasCompactSupport {h : Space → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (gradientAt h) := by
  have hK : IsCompact (tsupport h) := hc
  refine HasCompactSupport.intro hK (fun x hx => ?_)
  simp [gradientAt, fderiv_of_notMem_tsupport ℝ hx]

private theorem fderiv_apply_swap {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (x a b : Space) :
    fderiv ℝ (fun y => fderiv ℝ ξ y a) x b = fderiv ℝ (fun y => fderiv ℝ ξ y b) x a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ξ) x :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hξ).2).1 x
  have hs : IsSymmSndFDerivAt ℝ ξ x := hξ.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast Internal.PressureMollify.two_le_infty)
  rw [fderiv_clm_apply hd (differentiableAt_const a), fderiv_clm_apply hd (differentiableAt_const b)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hs b a

private theorem fderiv_gradField {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (x w : Space) :
    fderiv ℝ (gradientAt ξ) x w = gradientAt (fun y => fderiv ℝ ξ y w) x := by
  have hc : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => fderiv ℝ ξ y (unitVector i)) := fun i =>
    Internal.PressureMollify.contDiff_fderiv_apply hξ _
  have hH : HasFDerivAt (gradientAt ξ)
      (∑ i : Fin 3, (fderiv ℝ (fun y => fderiv ℝ ξ y (unitVector i)) x).smulRight (unitVector i)) x := by
    show HasFDerivAt (fun y => ∑ i : Fin 3, fderiv ℝ ξ y (unitVector i) • unitVector i) _ x
    exact HasFDerivAt.fun_sum fun i _ =>
      (((hc i).differentiable Internal.PressureMollify.infty_ne_zero) x).hasFDerivAt.smul_const _
  rw [hH.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  show _ = ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ ξ y w) x (unitVector i) • unitVector i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_swap hξ]

private theorem integral_inner_gradField_eq_zero {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ x, divergenceAt v x = 0) {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) :
    ∫ x, inner ℝ (v x) (gradientAt h x) = 0 := by
  have hI : ∀ i : Fin 3, Integrable (fun x => v x i * fderiv ℝ h x (unitVector i)) := fun i =>
    ((Internal.PressureMollify.contDiff_component hv i).continuous.mul
      (Internal.PressureMollify.contDiff_fderiv_apply hh _).continuous).integrable_of_hasCompactSupport
      ((Internal.PressureMollify.hasCompactSupport_fderiv_apply hc _).mul_left
        (f := fun x => v x i))
  have hJ : ∀ i : Fin 3, Integrable
      (fun x => fderiv ℝ (fun y => v y i) x (unitVector i) * h x) := fun i =>
    ((Internal.PressureMollify.contDiff_fderiv_apply
      (Internal.PressureMollify.contDiff_component hv i) _).continuous.mul
        hh.continuous).integrable_of_hasCompactSupport
      (hc.mul_left (f := fun x => fderiv ℝ (fun y => v y i) x (unitVector i)))
  have e1 : (fun x => inner ℝ (v x) (gradientAt h x)) =
      fun x => ∑ i : Fin 3, v x i * fderiv ℝ h x (unitVector i) := by
    funext x
    rw [real_inner_comm, Internal.PressureMollify.inner_gradientAt]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∀ i : Fin 3, ∫ x, v x i * fderiv ℝ h x (unitVector i) =
      -∫ x, fderiv ℝ (fun y => v y i) x (unitVector i) * h x := fun i =>
    Internal.PressureMollify.integral_mul_fderiv
      (Internal.PressureMollify.contDiff_component hv i) hh hc (unitVector i)
  have e3 : (fun x => ∑ i : Fin 3, fderiv ℝ (fun y => v y i) x (unitVector i) * h x) =
      fun _ => 0 := by
    funext x
    rw [← Finset.sum_mul]
    simp only [Internal.PressureMollify.fderiv_component hv]
    have hx := hdiv x
    unfold divergenceAt at hx
    rw [hx, zero_mul]
  rw [e1, integral_finsetSum _ (fun i _ => hI i), Finset.sum_congr rfl (fun i _ => e2 i),
    Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hJ i), e3]
  simp

private theorem integral_inner_remainder_gradField {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ x, divergenceAt v x = 0) {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ)
    (hc : HasCompactSupport ξ) (z : Space) :
    ∫ x, inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) = 0 := by
  set η : Space → ℝ := fun y => fderiv ℝ ξ y z with hηdef
  have hη : ContDiff ℝ ∞ η := Internal.PressureMollify.contDiff_fderiv_apply hξ z
  have hηc : HasCompactSupport η := Internal.PressureMollify.hasCompactSupport_fderiv_apply hc z
  have hθ : ContDiff ℝ ∞ (fun y => fderiv ℝ η y z) :=
    Internal.PressureMollify.contDiff_fderiv_apply hη z
  have hθc : HasCompactSupport (fun y => fderiv ℝ η y z) :=
    Internal.PressureMollify.hasCompactSupport_fderiv_apply hηc z
  have ht : ContDiff ℝ ∞ (fun y => ξ (y + z)) := hξ.comp (contDiff_id.add contDiff_const)
  have htc : HasCompactSupport (fun y => ξ (y + z)) := hc.comp_homeomorph (Homeomorph.addRight z)
  have hg : ContDiff ℝ ∞ (gradientAt ξ) := gradField_contDiff hξ
  have g0 : ∀ x, gradientAt ξ (x + z) = gradientAt (fun y => ξ (y + z)) x := by
    intro x
    simp only [gradientAt, fderiv_comp_add_right]
  have g1 : ∀ x, fderiv ℝ (gradientAt ξ) x z = gradientAt η x := fun x => fderiv_gradField hξ x z
  have g2 : ∀ x, iteratedFDeriv ℝ 2 (gradientAt ξ) x ![z, z] =
      gradientAt (fun y => fderiv ℝ η y z) x := by
    intro x
    rw [iteratedFDeriv_two_eq_fderiv_apply _ hg]
    have e : (fun y => fderiv ℝ (gradientAt ξ) y z) = gradientAt η := funext g1
    rw [e, fderiv_gradField hη]
  have hR : ∀ x, inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) =
      inner ℝ (v x) (gradientAt (fun y => ξ (y + z)) x) - inner ℝ (v x) (gradientAt ξ x)
        - inner ℝ (v x) (gradientAt η x)
        - (1 / 2 : ℝ) * inner ℝ (v x) (gradientAt (fun y => fderiv ℝ η y z) x) := by
    intro x
    rw [secondOrderRemainder, g0, g1, g2, inner_sub_right, inner_sub_right, inner_sub_right,
      real_inner_smul_right]
  have i0 : Integrable (fun x => inner ℝ (v x) (gradientAt (fun y => ξ (y + z)) x)) :=
    integrable_inner_compact_right _ _ hv.continuous (gradField_contDiff ht).continuous
      (gradField_hasCompactSupport htc)
  have i1 : Integrable (fun x => inner ℝ (v x) (gradientAt ξ x)) :=
    integrable_inner_compact_right _ _ hv.continuous hg.continuous (gradField_hasCompactSupport hc)
  have i2 : Integrable (fun x => inner ℝ (v x) (gradientAt η x)) :=
    integrable_inner_compact_right _ _ hv.continuous (gradField_contDiff hη).continuous
      (gradField_hasCompactSupport hηc)
  have i3 : Integrable (fun x => inner ℝ (v x) (gradientAt (fun y => fderiv ℝ η y z) x)) :=
    integrable_inner_compact_right _ _ hv.continuous (gradField_contDiff hθ).continuous
      (gradField_hasCompactSupport hθc)
  simp_rw [hR]
  rw [integral_sub, integral_sub, integral_sub, integral_const_mul,
    integral_inner_gradField_eq_zero hv hdiv ht htc, integral_inner_gradField_eq_zero hv hdiv hξ hc,
    integral_inner_gradField_eq_zero hv hdiv hη hηc, integral_inner_gradField_eq_zero hv hdiv hθ hθc]
  · ring
  all_goals first
    | exact i0 | exact i1 | exact i2 | exact i0.sub i1 | exact (i0.sub i1).sub i2
    | exact i3.const_mul _

end FracInternal

open FracInternal in
theorem fracWeakSolenoidal_of (h1 : SymmetryCompactStatement) (_h2 : FracCompactDecayStatement)
    (_h3 : CovarianceStatement) : FracWeakSolenoidalStatement := by
  intro α hα1 hα2 v hv hv2 hdiv ξ hξ hξc
  have hφ := gradField_contDiff hξ
  have hφc := gradField_hasCompactSupport hξc
  rw [(h1 α hα1 hα2 v (gradientAt ξ) hv (Or.inl hv2) hφ hφc).2.2]
  obtain ⟨Cφ, hCφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hRI := remainderIntegrable_of remainderBound α hα1 hα2 (gradientAt ξ) hφ (Or.inr ⟨Cφ, hCφ⟩)
  have hRx : ∀ x, inner ℝ (v x) (fractionalPowerAt α (gradientAt ξ) x) =
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_right, ← integral_inner (hRI x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  have hPR := integrable_prod_right_side α hα1 hα2 v (gradientAt ξ) hv (Or.inl hv2) hφ hφc
  have hfun : (fun x => inner ℝ (v x) (fractionalPowerAt α (gradientAt ξ) x)) = fun x =>
      (fractionalNormalizer α)⁻¹ *
        ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) :=
    funext hRx
  rw [hfun, integral_const_mul]
  have sR := integral_integral_swap (f := fun x z : Space =>
    ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z)) hPR
  rw [sR]
  have e : ∀ z : Space,
      ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder (gradientAt ξ) x z) = 0 := by
    intro z
    rw [integral_const_mul, integral_inner_remainder_gradField hv hdiv hξ hξc z, mul_zero]
  simp only [e, integral_zero, mul_zero]

end Breakdown

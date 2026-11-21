import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private def cutKernel (r : ℝ) (i : Fin 3) (x : Space) : ℝ :=
  FundSol.kernelGrad x i * (1 - Real.smoothTransition (2 - 8 * ‖x‖ ^ 2 / r ^ 2))

private theorem farWeight_eq_cutKernel (i : Fin 3) (y z : Space) :
    farWeight i y z = cutKernel (max 1 ‖y‖) i (y - z) := by
  unfold farWeight cutKernel nearCutoff
  rw [norm_sub_rev z y]

private theorem natCast_le_infty (k : ℕ) : ((k : ℕ∞ω) ≤ ∞) := by
  exact_mod_cast le_top

private theorem kernelGrad_coord_contDiffAt (i : Fin 3) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : Space => FundSol.kernelGrad z i) x := by
  have h1 : ContDiffAt ℝ ∞ (fun z : Space => ‖z‖⁻¹) x :=
    (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)
  have h2 : ContDiffAt ℝ ∞ (fun z : Space => ((4 * π)⁻¹ * ‖z‖⁻¹ ^ 3) • z) x :=
    (contDiffAt_const.mul (h1.pow 3)).smul contDiffAt_id
  exact ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt).comp x h2

private theorem cutoff_contDiff (r : ℝ) :
    ContDiff ℝ ∞ (fun x : Space => 1 - Real.smoothTransition (2 - 8 * ‖x‖ ^ 2 / r ^ 2)) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const _)))

private theorem cutKernel_eq_zero {r : ℝ} (hr : 0 < r) (i : Fin 3) {x : Space}
    (hx : ‖x‖ < r / 4) : cutKernel r i x = 0 := by
  unfold cutKernel
  have h : 8 * ‖x‖ ^ 2 / r ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [norm_nonneg x]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

private theorem cutKernel_contDiff {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    ContDiff ℝ ∞ (cutKernel r i) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h : cutKernel r i =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) (by positivity : (0 : ℝ) < r / 4)] with z hz
      exact cutKernel_eq_zero hr i (by simpa using hz)
    exact contDiffAt_const.congr_of_eventuallyEq h
  · exact (kernelGrad_coord_contDiffAt i hx).mul (cutoff_contDiff r).contDiffAt

private theorem cutKernel_far {r : ℝ} (hr : 0 < r) (i : Fin 3) {x : Space}
    (hx : r / 2 ≤ ‖x‖) : cutKernel r i x = FundSol.kernelGrad x i := by
  unfold cutKernel
  have h2 : 2 ≤ 8 * ‖x‖ ^ 2 / r ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero, mul_one]

private theorem kernelGrad_smul {t : ℝ} (ht : 0 < t) (x : Space) :
    FundSol.kernelGrad (t • x) = (t ^ 2)⁻¹ • FundSol.kernelGrad x := by
  unfold FundSol.kernelGrad
  rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul, smul_smul]
  congr 1
  rw [mul_inv t ‖x‖, mul_pow]
  have ht3 : t⁻¹ ^ 3 * t = (t ^ 2)⁻¹ := by
    have := ht.ne'
    field_simp
  linear_combination ((4 * π)⁻¹ * ‖x‖⁻¹ ^ 3) * ht3

private theorem cutKernel_scale {r : ℝ} (hr : 1 ≤ r) (i : Fin 3) {R : ℝ} (hR : r ≤ R)
    {x : Space} (hx : R / 2 < ‖x‖) : cutKernel r i x = (R ^ 2)⁻¹ * cutKernel 1 i (R⁻¹ • x) := by
  have hR0 : 0 < R := by linarith
  rw [cutKernel_far (by linarith) i (by linarith), cutKernel_far one_pos i ?_]
  · have h := congrArg (fun v : Space => v i) (kernelGrad_smul (inv_pos.mpr hR0) x)
    simp only [PiLp.smul_apply, smul_eq_mul] at h
    rw [h, inv_pow, inv_inv, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), inv_mul_eq_div,
      le_div_iff₀ hR0]
    linarith

private theorem cutKernel_decay {r : ℝ} (hr : 1 ≤ r) (i : Fin 3) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k (cutKernel r i) x‖ ≤ C / (1 + ‖x‖) ^ 2 := by
  have hs1 := cutKernel_contDiff one_pos i
  have hsr := cutKernel_contDiff (by linarith : (0 : ℝ) < r) i
  obtain ⟨S, hS⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv (natCast_le_infty k) hs1).continuousOn
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : Space) r).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv (natCast_le_infty k) hsr).continuousOn
  refine ⟨4 * max S 0 + max T 0 * (1 + r) ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ r
  · have h1 := hT x (mem_closedBall_zero_iff.mpr hx)
    calc ‖iteratedFDeriv ℝ k (cutKernel r i) x‖ ≤ max T 0 := h1.trans (le_max_left _ _)
      _ ≤ max T 0 * (1 + r) ^ 2 / (1 + ‖x‖) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) 2) (le_max_right _ _)
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  · rw [not_le] at hx
    set R := ‖x‖ with hRdef
    have hR0 : 0 < R := by linarith
    have heq : cutKernel r i =ᶠ[𝓝 x] fun z => (R ^ 2)⁻¹ * cutKernel 1 i (R⁻¹ • z) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show R / 2 < ‖x‖ by rw [← hRdef]; linarith)] with z hz
      exact cutKernel_scale hr i hx.le hz
    rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    set L : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space with hLdef
    have hfun : (fun z => (R ^ 2)⁻¹ * cutKernel 1 i (R⁻¹ • z)) =
        (R ^ 2)⁻¹ • (cutKernel 1 i ∘ L) := by
      funext z
      simp [L, smul_eq_mul]
    rw [hfun, iteratedFDeriv_const_smul_apply
        ((hs1.comp L.contDiff).of_le (natCast_le_infty k)).contDiffAt,
      L.iteratedFDeriv_comp_right hs1 x (natCast_le_infty k), norm_smul]
    have hLx : L x ∈ Metric.sphere (0 : Space) 1 := by
      rw [mem_sphere_zero_iff_norm]
      simp only [L, smul_apply, ContinuousLinearMap.id_apply]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), ← hRdef,
        inv_mul_cancel₀ hR0.ne']
    have hL : ‖L‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simp only [L, smul_apply, ContinuousLinearMap.id_apply]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), one_mul]
      have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      nlinarith [norm_nonneg v]
    have hc : ‖(iteratedFDeriv ℝ k (cutKernel 1 i) (L x)).compContinuousLinearMap
        fun _ => L‖ ≤ max S 0 := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      calc _ ≤ max S 0 * 1 :=
            mul_le_mul ((hS _ hLx).trans (le_max_left _ _))
              (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL))
              (Finset.prod_nonneg fun _ _ => norm_nonneg _) (le_max_right _ _)
        _ = max S 0 := mul_one _
    have hR2 : ‖(R ^ 2)⁻¹‖ ≤ 4 / (1 + R) ^ 2 := by
      rw [Real.norm_of_nonneg (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc ‖(R ^ 2)⁻¹‖ * ‖(iteratedFDeriv ℝ k (cutKernel 1 i) (L x)).compContinuousLinearMap
          fun _ => L‖ ≤ 4 / (1 + R) ^ 2 * max S 0 :=
          mul_le_mul hR2 hc (norm_nonneg _) (by positivity)
      _ = 4 * max S 0 / (1 + R) ^ 2 := by ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)

private theorem farWeight_bounds (i : Fin 3) (y : Space) :
    ContDiff ℝ 2 (farWeight i y) ∧
      ∃ B, ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (farWeight i y) z‖ ≤ B / (1 + ‖z‖) ^ 2 := by
  set M := max 1 ‖y‖ with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  set N : Space →L[ℝ] Space := -ContinuousLinearMap.id ℝ Space with hNdef
  have hfun : farWeight i y = fun z => (cutKernel M i ∘ N) (z - y) := by
    funext z
    rw [farWeight_eq_cutKernel]
    simp [N, M]
  have hs : ContDiff ℝ ∞ (cutKernel M i) := cutKernel_contDiff (by linarith) i
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ((hs.comp N.contDiff).comp (contDiff_id.sub contDiff_const)).of_le
      (natCast_le_infty 2)
  obtain ⟨C0, hC0, h0⟩ := cutKernel_decay hM i 0
  obtain ⟨C1, hC1, h1⟩ := cutKernel_decay hM i 1
  obtain ⟨C2, hC2, h2⟩ := cutKernel_decay hM i 2
  set Cm := max C0 (max C1 C2) with hCm
  have hCm0 : 0 ≤ Cm := hC0.trans (le_max_left _ _)
  have hall : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (cutKernel M i) x‖ ≤ Cm / (1 + ‖x‖) ^ 2 := by
    intro k hk x
    interval_cases k
    · exact (h0 x).trans (by gcongr; exact le_max_left _ _)
    · exact (h1 x).trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x).trans (by gcongr; exact (le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Cm * (1 + ‖y‖) ^ 2, fun k hk z => ?_⟩
  rw [hfun, iteratedFDeriv_comp_sub, N.iteratedFDeriv_comp_right hs _ (natCast_le_infty k)]
  have hN : ‖N‖ ≤ 1 := by
    rw [hNdef, norm_neg]
    exact ContinuousLinearMap.norm_id_le
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hNz : N (z - y) = y - z := by simp [N]
  rw [hNz]
  have hprod : ∏ _j : Fin k, ‖N‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hN)
  have hb := hall k hk (y - z)
  have htri : 1 + ‖z‖ ≤ (1 + ‖y‖) * (1 + ‖y - z‖) := by
    have hz : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := by
      calc ‖z‖ = ‖y - (y - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖ + ‖y - z‖ := norm_sub_le _ _
    nlinarith [norm_nonneg y, norm_nonneg (y - z)]
  calc ‖iteratedFDeriv ℝ k (cutKernel M i) (y - z)‖ * ∏ _j : Fin k, ‖N‖
      ≤ Cm / (1 + ‖y - z‖) ^ 2 * 1 :=
        mul_le_mul hb hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          ((norm_nonneg _).trans hb)
    _ ≤ Cm * (1 + ‖y‖) ^ 2 / (1 + ‖z‖) ^ 2 := by
        rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        have hsq : (1 + ‖z‖) ^ 2 ≤ ((1 + ‖y‖) * (1 + ‖y - z‖)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) htri 2
        calc Cm * (1 + ‖z‖) ^ 2 ≤ Cm * ((1 + ‖y‖) * (1 + ‖y - z‖)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq hCm0
          _ = _ := by ring

private theorem component_bounds {f : Space → Fin 3 → Fin 3 → ℝ} {A : ℝ} (hf : ContDiff ℝ 2 f)
    (hfb : ∀ m ≤ 2, ∀ z, ‖iteratedFDeriv ℝ m f z‖ ≤ A / (1 + ‖z‖) ^ (2 + m)) (a b : Fin 3) :
    ContDiff ℝ 2 (fun x => f x a b) ∧
      ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun x => f x a b) z‖ ≤ A / (1 + ‖z‖) ^ (2 + k) := by
  set L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) a) with hLdef
  have hfun : (fun x => f x a b) = L ∘ f := rfl
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => ?_
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, one_mul]
    exact (norm_le_pi_norm (F a) b).trans (norm_le_pi_norm F a)
  refine ⟨hfun ▸ L.contDiff.comp hf, fun k hk z => ?_⟩
  rw [hfun]
  refine (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hk)).trans ?_
  calc ‖L‖ * ‖iteratedFDeriv ℝ k f z‖ ≤ 1 * ‖iteratedFDeriv ℝ k f z‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hfb k hk z

private theorem decay_mul {φ ψ : Space → ℝ} {P Q : ℝ} {p q : ℕ}
    (hφ : ∀ z, |φ z| ≤ P / (1 + ‖z‖) ^ p) (hψ : ∀ z, |ψ z| ≤ Q / (1 + ‖z‖) ^ q) :
    ∀ z, |φ z * ψ z| ≤ P * Q / (1 + ‖z‖) ^ (p + q) := by
  intro z
  rw [abs_mul, pow_add, ← div_mul_div_comm]
  exact mul_le_mul (hφ z) (hψ z) (abs_nonneg _) ((abs_nonneg _).trans (hφ z))

private theorem integrable_of_decay {φ : Space → ℝ} (hc : Continuous φ) {C : ℝ} {n : ℕ}
    (hn : 3 < n) (hφ : ∀ z, |φ z| ≤ C / (1 + ‖z‖) ^ n) : Integrable φ := by
  have hi : Integrable (fun z : Space => (1 + ‖z‖) ^ (-(n : ℝ))) :=
    integrable_one_add_norm (by simp; exact_mod_cast hn)
  refine (hi.const_mul C).mono' hc.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  exact hφ z

private theorem fderiv_fderiv_apply_eq {h : Space → ℝ} (hh : ContDiff ℝ 2 h) (z u v : Space) :
    fderiv ℝ (fun x => fderiv ℝ h x v) z u = iteratedFDeriv ℝ 2 h z ![u, v] := by
  have hd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply (hd z) (differentiableAt_const v)]
  simp

private theorem ibp_twice {w g : Space → ℝ} (hw : ContDiff ℝ 2 w) (hg : ContDiff ℝ 2 g)
    {B A : ℝ} (hwb : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ B / (1 + ‖z‖) ^ 2)
    (hgb : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ A / (1 + ‖z‖) ^ (2 + k)) (u v : Space) :
    Integrable (fun z => w z * iteratedFDeriv ℝ 2 g z ![u, v]) ∧
      Integrable (fun z => iteratedFDeriv ℝ 2 w z ![u, v] * g z) ∧
        ∫ z, w z * iteratedFDeriv ℝ 2 g z ![u, v] =
          ∫ z, iteratedFDeriv ℝ 2 w z ![u, v] * g z := by
  have b0 : ∀ (h : Space → ℝ) (C : ℝ) (n : ℕ),
      (∀ z, ‖iteratedFDeriv ℝ 0 h z‖ ≤ C / (1 + ‖z‖) ^ n) →
        ∀ z, |h z| ≤ C / (1 + ‖z‖) ^ n := by
    intro h C n hb z
    have := hb z
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have b1 : ∀ (h : Space → ℝ) (C : ℝ) (n : ℕ) (e : Space),
      (∀ z, ‖iteratedFDeriv ℝ 1 h z‖ ≤ C / (1 + ‖z‖) ^ n) →
        ∀ z, |fderiv ℝ h z e| ≤ C * ‖e‖ / (1 + ‖z‖) ^ n := by
    intro h C n e hb z
    have := hb z
    rw [norm_iteratedFDeriv_one] at this
    rw [← Real.norm_eq_abs, mul_div_right_comm]
    exact ((fderiv ℝ h z).le_opNorm e).trans (mul_le_mul_of_nonneg_right this (norm_nonneg e))
  have b2 : ∀ (h : Space → ℝ) (C : ℝ) (n : ℕ) (a b : Space),
      (∀ z, ‖iteratedFDeriv ℝ 2 h z‖ ≤ C / (1 + ‖z‖) ^ n) →
        ∀ z, |iteratedFDeriv ℝ 2 h z ![a, b]| ≤ C * (‖a‖ * ‖b‖) / (1 + ‖z‖) ^ n := by
    intro h C n a b hb z
    rw [← Real.norm_eq_abs, mul_div_right_comm]
    refine ((iteratedFDeriv ℝ 2 h z).le_opNorm _).trans ?_
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_le_mul_of_nonneg_right (hb z) (by positivity)
  have w0 := b0 w B 2 (hwb 0 (by norm_num))
  have w1 := b1 w B 2 u (hwb 1 (by norm_num))
  have w2 := b2 w B 2 u v (hwb 2 le_rfl)
  have g0 := b0 g A (2 + 0) (hgb 0 (by norm_num))
  have g1 := b1 g A (2 + 1) v (hgb 1 (by norm_num))
  have g2 := b2 g A (2 + 2) u v (hgb 2 le_rfl)
  have cw : Continuous w := hw.continuous
  have cg : Continuous g := hg.continuous
  have cw1 : Continuous fun z => fderiv ℝ w z u :=
    (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have cg1 : Continuous fun z => fderiv ℝ g z v :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have cw2 : Continuous fun z => iteratedFDeriv ℝ 2 w z ![u, v] :=
    (continuous_eval_const _).comp (ContDiff.continuous_iteratedFDeriv le_rfl hw)
  have cg2 : Continuous fun z => iteratedFDeriv ℝ 2 g z ![u, v] :=
    (continuous_eval_const _).comp (ContDiff.continuous_iteratedFDeriv le_rfl hg)
  have dw : Differentiable ℝ (fderiv ℝ w) :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have dg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have sym : ∀ z, iteratedFDeriv ℝ 2 w z ![v, u] = iteratedFDeriv ℝ 2 w z ![u, v] := by
    intro z
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    exact (hw.contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  have eg : ∀ z, fderiv ℝ (fun x => fderiv ℝ g x v) z u = iteratedFDeriv ℝ 2 g z ![u, v] :=
    fun z => fderiv_fderiv_apply_eq hg z u v
  have ew : ∀ z, fderiv ℝ (fun x => fderiv ℝ w x u) z v = iteratedFDeriv ℝ 2 w z ![u, v] :=
    fun z => (fderiv_fderiv_apply_eq hw z v u).trans (sym z)
  have IA : Integrable (fun z => w z * iteratedFDeriv ℝ 2 g z ![u, v]) :=
    integrable_of_decay (cw.mul cg2) (by norm_num) (decay_mul w0 g2)
  have IB : Integrable (fun z => iteratedFDeriv ℝ 2 w z ![u, v] * g z) :=
    integrable_of_decay (cw2.mul cg) (by norm_num) (decay_mul w2 g0)
  have I1 : Integrable (fun z => fderiv ℝ w z u * fderiv ℝ g z v) :=
    integrable_of_decay (cw1.mul cg1) (by norm_num) (decay_mul w1 g1)
  have I2 : Integrable (fun z => w z * fderiv ℝ g z v) :=
    integrable_of_decay (cw.mul cg1) (by norm_num) (decay_mul w0 g1)
  have I3 : Integrable (fun z => fderiv ℝ w z u * g z) :=
    integrable_of_decay (cw1.mul cg) (by norm_num) (decay_mul w1 g0)
  have step1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := u)
    (f := w) (g := fun x => fderiv ℝ g x v) I1 (by simp_rw [eg]; exact IA) I2
    (fun x _ => hw.differentiable (by norm_num) x)
    (fun x _ => (dg x).clm_apply (differentiableAt_const v))
  have step2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := v)
    (f := fun x => fderiv ℝ w x u) (g := g) (by simp_rw [ew]; exact IB) I1 I3
    (fun x _ => (dw x).clm_apply (differentiableAt_const u))
    (fun x _ => hg.differentiable (by norm_num) x)
  simp_rw [eg] at step1
  simp_rw [ew] at step2
  refine ⟨IA, IB, ?_⟩
  rw [step1, step2, neg_neg]

theorem newtonFarIdentity_holds : NewtonFarIdentity := by
  intro f A hf hfb i y
  obtain ⟨hwc, B, hwb⟩ := farWeight_bounds i y
  have key : ∀ a b : Fin 3,
      Integrable (fun z => farWeight i y z *
        iteratedFDeriv ℝ 2 (fun x => f x a b) z ![unitVector a, unitVector b]) ∧
      Integrable (fun z => iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] *
        f z a b) ∧
      ∫ z, farWeight i y z *
          iteratedFDeriv ℝ 2 (fun x => f x a b) z ![unitVector a, unitVector b] =
        ∫ z, iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b :=
    fun a b => ibp_twice hwc (component_bounds hf hfb a b).1 hwb (component_bounds hf hfb a b).2
      (unitVector a) (unitVector b)
  have hL : (fun z => farWeight i y z * divDivSource f z) = fun z => ∑ a : Fin 3, ∑ b : Fin 3,
      farWeight i y z * iteratedFDeriv ℝ 2 (fun x => f x a b) z ![unitVector a, unitVector b] := by
    funext z
    simp only [divDivSource, Finset.mul_sum]
  have hIL : ∀ a ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z => ∑ b : Fin 3,
      farWeight i y z * iteratedFDeriv ℝ 2 (fun x => f x a b) z ![unitVector a, unitVector b]) :=
    fun a _ => integrable_finsetSum _ fun b _ => (key a b).1
  have hIR : ∀ a ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z => ∑ b : Fin 3,
      iteratedFDeriv ℝ 2 (farWeight i y) z ![unitVector a, unitVector b] * f z a b) :=
    fun a _ => integrable_finsetSum _ fun b _ => (key a b).2.1
  refine ⟨?_, ?_⟩
  · rw [hL]
    exact integrable_finsetSum _ hIL
  · rw [hL, integral_finsetSum _ hIL, integral_finsetSum _ hIR]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => (key a b).1),
      integral_finsetSum _ (fun b _ => (key a b).2.1)]
    exact Finset.sum_congr rfl fun b _ => (key a b).2.2

end Breakdown.FarField

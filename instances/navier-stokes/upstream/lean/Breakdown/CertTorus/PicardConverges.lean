import Breakdown.CertTorus.RegularStatements
import Breakdown.Weak.ContinuousVarConst
import Breakdown.Weak.BilinIntegrable

open MeasureTheory Set Real Filter
open scoped Topology

noncomputable section

namespace Breakdown.FarField

open Freq WeakProfile

namespace Internal.PicardConvergence

set_option maxHeartbeats 1000000

theorem picardIter_self (x : X) (a : ℝ) (n : ℕ) : fixedPointIter x a n a = x := by
  cases n <;> simp [fixedPointIter, heat_holds.1]

theorem norm_heatX_le {τ : ℝ} (hτ : 0 ≤ τ) (x : X) : ‖heatX τ x‖ ≤ ‖x‖ :=
  ((heatX τ).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (heat_holds.2.2.1 τ hτ))

theorem exists_bounded_extension {v : ℝ → X} {a R : ℝ} (hv : ContinuousOn v (Icc a R)) :
    ∃ (y : ℝ → X) (M : ℝ), (∀ t, ‖y t‖ ≤ M) ∧ AEStronglyMeasurable y volume ∧
      EqOn y v (Icc a R) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  refine ⟨(Icc a R).indicator v, max M 0, fun t => ?_, ?_, fun t ht => ?_⟩
  · by_cases ht : t ∈ Icc a R
    · simpa [ht] using (hM t ht).trans (le_max_left M 0)
    · simp [ht]
  · exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).2
      (hv.aestronglyMeasurable measurableSet_Icc)
  · simp [ht]

theorem bilin_intervalIntegrable {v : ℝ → X} {a R t : ℝ} (hv : ContinuousOn v (Icc a R))
    (ht : t ∈ Icc a R) :
    IntervalIntegrable (fun s => bilinX (t - s) (v s) (v s)) volume a t := by
  obtain ⟨y, M, hyM, hy, hyv⟩ := exists_bounded_extension hv
  have h : IntervalIntegrable (fun s => bilinX (t - s) (y s) (y s)) volume a t :=
    Internal.ContinuousVarConst.integ bilinIntegrable_holds (l := a - 1) (r := t + 1)
      (fun s _ => hyM s) hy.restrict (by linarith) ht.1 le_rfl (by linarith)
  refine (intervalIntegrable_congr fun s hs => ?_).mp h
  rw [uIoc_of_le ht.1] at hs
  have hs' : s ∈ Icc a R := ⟨hs.1.le, hs.2.trans ht.2⟩
  simp only [hyv hs']

theorem picardIter_continuousOn (x : X) (a R : ℝ) (n : ℕ) :
    ContinuousOn (fixedPointIter x a n) (Icc a R) := by
  rcases lt_or_ge R a with hRa | haR
  · simp [Icc_eq_empty_of_lt hRa]
  induction n with
  | zero =>
    exact (heat_holds.2.2.2.1 x).comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by simpa [sub_nonneg] using ht.1)
  | succ n ih =>
    obtain ⟨y, M, hyM, hy, hyv⟩ := exists_bounded_extension ih
    have hc := continuousVarConst_holds bilinIntegrable_holds y (a - 1) (R + 1) M
      (fun s _ => hyM s) hy.restrict a ⟨by linarith, by linarith⟩
    refine (hc.mono fun t ht => ⟨ht.1, by linarith [ht.2]⟩).congr fun t ht => ?_
    have hya : y a = x := by rw [hyv ⟨le_rfl, haR⟩, picardIter_self]
    simp only [fixedPointIter, varConst, hya]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hyv ⟨hs.1, hs.2.trans ht.2⟩]

theorem norm_integral_le_kernel {f : ℝ → X} {a t C L : ℝ} (hat : a ≤ t)
    (hf : ∀ s ∈ Ioc a t, ‖f s‖ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * L) :
    ‖∫ s in a..t, f s‖ ≤ 4 * C * L * (t - a) ^ (1 / 4 : ℝ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le hat (Eventually.of_forall hf)
    (((Internal.ContinuousVarConst.kernel_intervalIntegrable t a).const_mul C).mul_const L)
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    Internal.ContinuousVarConst.kernel_integral t a] at h
  linarith

end Internal.PicardConvergence

set_option maxHeartbeats 1000000 in
open Internal.PicardConvergence in
theorem picardConverges_holds : PicardConverges := by
  intro M
  obtain ⟨C, hC0, hC⟩ := bilin_holds.2
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right M 0
  set ε := (32 * C * M' + 2)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hεM : 32 * C * M' * ε ≤ 1 := by
    rw [hε, ← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  refine ⟨ε ^ (4 : ℝ), Real.rpow_pos_of_pos hε0 _, ?_⟩
  intro u a b hab hu huM
  have huM' : ∀ t ∈ Icc a b, ‖u t‖ ≤ M' := fun t ht => (huM t ht).trans (le_max_left M 0)
  set T := min b (a + ε ^ (4 : ℝ)) with hT
  set p := fixedPointIter (u a) a with hp
  have hTb : ∀ s ∈ Icc a T, s ∈ Icc a b := fun s hs => ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hpc : ∀ n, ContinuousOn (p n) (Icc a T) := fun n => picardIter_continuousOn (u a) a T n
  have hroot : ∀ s ∈ Icc a T, (s - a) ^ (1 / 4 : ℝ) ≤ ε := by
    intro s hs
    have h1 : (s - a) ^ (1 / 4 : ℝ) ≤ (ε ^ (4 : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith [hs.1]) (by linarith [hs.2.trans (min_le_right _ _)])
        (by norm_num)
    rwa [← Real.rpow_mul hε0.le, show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at h1
  have key : ∀ n : ℕ, ∀ s ∈ Icc a T, ‖p n s - u s‖ ≤ 2 * M' * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h1 : ‖p 0 s‖ ≤ M' := by
        simp only [hp, fixedPointIter]
        exact (norm_heatX_le (by linarith [hs.1]) _).trans (huM' a ⟨le_rfl, hab.le⟩)
      calc ‖p 0 s - u s‖ ≤ ‖p 0 s‖ + ‖u s‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add h1 (huM' s (hTb s hs))
        _ = 2 * M' * (1 / 2) ^ 0 := by ring
    | succ n ih =>
      intro s hs
      have hsb := hTb s hs
      obtain ⟨hui, hue⟩ := hu.2 s hsb
      have hpi : IntervalIntegrable (fun r => bilinX (s - r) (p n r) (p n r)) volume a s :=
        bilin_intervalIntegrable (hpc n) hs
      have hsub := intervalIntegral.integral_sub hpi hui
      have hps : p (n + 1) s = heatX (s - a) (u a) +
          ∫ r in a..s, bilinX (s - r) (p n r) (p n r) := rfl
      have hdiff : p (n + 1) s - u s =
          ∫ r in a..s, (bilinX (s - r) (p n r) (p n r) - bilinX (s - r) (u r) (u r)) := by
        rw [hsub]
        exact (congrArg₂ (fun x y : X => x - y) hps hue).trans (add_sub_add_left_eq_sub _ _ _)
      have hq : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      have hL : 0 ≤ 2 * M' * (1 / 2) ^ n * (4 * M') := by positivity
      have hbound : ∀ r ∈ Ioc a s,
          ‖bilinX (s - r) (p n r) (p n r) - bilinX (s - r) (u r) (u r)‖ ≤
            C * (s - r) ^ (-(3 / 4 : ℝ)) * (2 * M' * (1 / 2) ^ n * (4 * M')) := by
        intro r hr
        have hrT : r ∈ Icc a T := ⟨hr.1.le, hr.2.trans hs.2⟩
        rcases eq_or_lt_of_le hr.2 with hrs | hrs
        · rw [hrs, sub_self, Internal.ContinuousVarConst.bilinX_of_nonpos le_rfl]
          simp only [zero_apply, sub_zero, norm_zero]
          positivity
        · have hτ : 0 < s - r := by linarith
          have he := ih r hrT
          have hur := huM' r (hTb r hrT)
          have hpr : ‖p n r‖ ≤ 3 * M' := by
            have h2 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            calc ‖p n r‖ = ‖(p n r - u r) + u r‖ := by rw [sub_add_cancel]
              _ ≤ ‖p n r - u r‖ + ‖u r‖ := norm_add_le _ _
              _ ≤ 2 * M' * 1 + M' := add_le_add (he.trans (by gcongr)) hur
              _ = 3 * M' := by ring
          have hsplit : bilinX (s - r) (p n r) (p n r) - bilinX (s - r) (u r) (u r) =
              bilinX (s - r) (p n r - u r) (p n r) + bilinX (s - r) (u r) (p n r - u r) := by
            simp only [map_sub, sub_apply]
            abel
          have hk : 0 ≤ C * (s - r) ^ (-(3 / 4 : ℝ)) := by positivity
          rw [hsplit]
          calc _ ≤ ‖bilinX (s - r) (p n r - u r) (p n r)‖ + ‖bilinX (s - r) (u r) (p n r - u r)‖ :=
                norm_add_le _ _
            _ ≤ C * (s - r) ^ (-(3 / 4 : ℝ)) * ‖p n r - u r‖ * ‖p n r‖ +
                C * (s - r) ^ (-(3 / 4 : ℝ)) * ‖u r‖ * ‖p n r - u r‖ :=
                add_le_add (hC _ hτ _ _) (hC _ hτ _ _)
            _ = C * (s - r) ^ (-(3 / 4 : ℝ)) * (‖p n r - u r‖ * (‖p n r‖ + ‖u r‖)) := by ring
            _ ≤ C * (s - r) ^ (-(3 / 4 : ℝ)) * (2 * M' * (1 / 2) ^ n * (3 * M' + M')) := by
                gcongr
            _ = C * (s - r) ^ (-(3 / 4 : ℝ)) * (2 * M' * (1 / 2) ^ n * (4 * M')) := by ring
      rw [hdiff]
      refine (norm_integral_le_kernel hs.1 hbound).trans ?_
      have hA : 0 ≤ 4 * C * (2 * M' * (1 / 2) ^ n * (4 * M')) := by positivity
      calc 4 * C * (2 * M' * (1 / 2) ^ n * (4 * M')) * (s - a) ^ (1 / 4 : ℝ)
          ≤ 4 * C * (2 * M' * (1 / 2) ^ n * (4 * M')) * ε := mul_le_mul_of_nonneg_left (hroot s hs) hA
        _ = (32 * C * M' * ε) * (M' * (1 / 2) ^ n) := by ring
        _ ≤ 1 * (M' * (1 / 2) ^ n) := mul_le_mul_of_nonneg_right hεM (by positivity)
        _ = 2 * M' * (1 / 2) ^ (n + 1) := by ring
  intro t ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => key n t ht) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (2 * M')

end Breakdown.FarField

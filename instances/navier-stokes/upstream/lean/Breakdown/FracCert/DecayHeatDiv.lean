import Breakdown.FracCert.StDecay
import Breakdown.Uniqueness.CutoffBounds
import Breakdown.Frac.OpIntegrable

open MeasureTheory Set Real Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.DecayHeatDiv

open Breakdown.FracCert

theorem near_deriv {φ : Space → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) {G : Space → ℝ}
    {j : ℕ} (hG : ContDiff ℝ j G) :
    ContDiff ℝ j (fun x => ∫ z, φ z * G (x - z)) ∧
    iteratedFDeriv ℝ j (fun x => ∫ z, φ z * G (x - z)) =
      fun x => ∫ z, φ z • iteratedFDeriv ℝ j G (x - z) := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hs
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ z, φ z ≠ 0 → ‖z‖ ≤ S := by
    obtain ⟨S, hS⟩ := hs.isCompact.isBounded.subset_closedBall 0
    exact ⟨S, fun z hz => by simpa using hS (subset_tsupport _ hz)⟩
  have hGc : ∀ n : ℕ, n ≤ j → Continuous (iteratedFDeriv ℝ n G) := fun n hn =>
    hG.continuous_iteratedFDeriv (by exact_mod_cast hn)
  have hdom : ∀ n : ℕ, n ≤ j → ∀ x₀ : Space, ∃ M : ℝ, ∀ x ∈ closedBall x₀ 1, ∀ z,
      ‖φ z • iteratedFDeriv ℝ n G (x - z)‖ ≤ M * ‖φ z‖ := by
    intro n hn x₀
    obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (1 + S)).exists_bound_of_continuousOn
      (hGc n hn).continuousOn
    refine ⟨M, fun x hx z => ?_⟩
    by_cases hz : φ z = 0
    · simp [hz]
    · rw [norm_smul, mul_comm]
      refine mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _)
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      have := hS z hz
      calc ‖x - z - x₀‖ = ‖(x - x₀) - z‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 1 + S := by linarith
  have hmeas : ∀ n : ℕ, n ≤ j → ∀ x, AEStronglyMeasurable
      (fun z => φ z • iteratedFDeriv ℝ n G (x - z)) volume := by
    intro n hn x
    have : SecondCountableTopologyEither Space
        (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ) := ⟨Or.inl inferInstance⟩
    exact (hφ.smul ((hGc n hn).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hintj : ∀ n : ℕ, n ≤ j → ∀ x, Integrable (fun z => φ z • iteratedFDeriv ℝ n G (x - z)) := by
    intro n hn x
    obtain ⟨M, hM⟩ := hdom n hn x
    exact Integrable.mono' (hφi.norm.const_mul M) (hmeas n hn x)
      (Filter.Eventually.of_forall fun z => hM x (mem_closedBall_self zero_le_one) z)
  have hd : ∀ n : ℕ, n < j → ∀ x₀, HasFDerivAt
      (fun x => ∫ z, φ z • iteratedFDeriv ℝ n G (x - z))
      (∫ z, φ z • fderiv ℝ (iteratedFDeriv ℝ n G) (x₀ - z)) x₀ := by
    intro n hn x₀
    have : SecondCountableTopologyEither Space
        (Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ) := ⟨Or.inl inferInstance⟩
    have hc : Continuous (fderiv ℝ (iteratedFDeriv ℝ n G)) := by
      rw [fderiv_iteratedFDeriv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) ℝ).continuous.comp
        (hGc (n + 1) hn)
    obtain ⟨M, hM⟩ := hdom (n + 1) hn x₀
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
      (F' := fun x z => φ z • fderiv ℝ (iteratedFDeriv ℝ n G) (x - z))
      (bound := fun z => M * ‖φ z‖) (ball_mem_nhds x₀ one_pos)
      (Filter.Eventually.of_forall (fun x => hmeas n hn.le x)) (hintj n hn.le x₀) ?_ ?_
      (hφi.norm.const_mul M) ?_
    · exact (hφ.smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z x hx => ?_)
      have := hM x (ball_subset_closedBall hx) z
      rw [norm_smul] at this ⊢
      rw [norm_fderiv_iteratedFDeriv]
      exact this
    · refine Filter.Eventually.of_forall (fun z x _ => ?_)
      have hdk : HasFDerivAt (iteratedFDeriv ℝ n G) (fderiv ℝ (iteratedFDeriv ℝ n G) (x - z))
          (x - z) :=
        ((hG.differentiable_iteratedFDeriv (by exact_mod_cast hn)) _).hasFDerivAt
      have h2 := (hdk.comp x ((hasFDerivAt_id x).sub_const z)).const_smul (φ z)
      simp only [ContinuousLinearMap.comp_id] at h2
      exact h2
  have hform : ∀ n : ℕ, n ≤ j → iteratedFDeriv ℝ n (fun x => ∫ z, φ z * G (x - z)) =
      fun x => ∫ z, φ z • iteratedFDeriv ℝ n G (x - z) := by
    intro n
    induction n with
    | zero =>
      intro _
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      have : (fun z => φ z • iteratedFDeriv ℝ 0 G (x - z)) =
          fun z => (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (φ z * G (x - z)) := by
        funext z; ext m; simp
      rw [this, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ Space ℝ).symm.toContinuousLinearEquiv.integral_comp_comm
        _).symm
    | succ n ih =>
      intro hn
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih (by omega),
        (hd n (by omega) x).fderiv]
      refine (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space)
        ℝ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm).trans ?_
      congr 1
  refine ⟨contDiff_iff_continuous_differentiable.2 ⟨fun m hm => ?_, fun m hm => ?_⟩,
    hform j le_rfl⟩
  · have hm' : m ≤ j := by exact_mod_cast hm
    rw [hform m hm']
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨M, hM⟩ := hdom m hm' x₀
    refine continuousAt_of_dominated (bound := fun z => M * ‖φ z‖)
      (Filter.Eventually.of_forall fun x => hmeas m hm' x) ?_ (hφi.norm.const_mul M) ?_
    · filter_upwards [closedBall_mem_nhds x₀ one_pos] with x hx
      exact Filter.Eventually.of_forall (hM x hx)
    · refine Filter.Eventually.of_forall fun z => ?_
      refine Continuous.continuousAt (f := fun x => φ z • iteratedFDeriv ℝ m G (x - z)) ?_
      exact (continuous_const (y := φ z)).smul ((hGc m hm').comp (continuous_id.sub continuous_const))
  · have hm' : m < j := by exact_mod_cast hm
    rw [hform m hm'.le]
    exact fun x => (hd m hm' x).differentiableAt

theorem shift16 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 + b ≤ 2 * (1 + a)) :
    (1 + a) ^ (-4 : ℝ) ≤ 16 * (1 + b) ^ (-4 : ℝ) := by
  have h1 : (1 + b) ^ (4 : ℝ) ≤ 16 * (1 + a) ^ (4 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h (by norm_num)
  have hpa : 0 < (1 + a) ^ (4 : ℝ) := by positivity
  have hpb : 0 < (1 + b) ^ (4 : ℝ) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    inv_le_comm₀ hpa (by positivity), inv_div, div_le_iff₀ (by norm_num)]
  linarith

theorem far_deriv {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hκb : ∀ n : ℕ, ∃ E : ℝ, ∀ y, ‖iteratedFDeriv ℝ n κ y‖ ≤ E * (1 + ‖y‖) ^ (-4 : ℝ))
    {f : Space → ℝ} (hf : Continuous f) {B0 : ℝ} (hfb : ∀ y, ‖f y‖ ≤ B0) :
    ContDiff ℝ ∞ (fun x => ∫ w, κ (x - w) * f w) ∧ ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun x => ∫ w, κ (x - w) * f w) =
        fun x => ∫ w, f w • iteratedFDeriv ℝ n κ (x - w) := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  have hkc : ∀ n : ℕ, Continuous (iteratedFDeriv ℝ n κ) := fun n =>
    hκ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  choose E hEb using hκb
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    have := (norm_nonneg _).trans (hEb n 0)
    simpa using this
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hfb 0)
  have hintj : ∀ (n : ℕ) (x : Space), Integrable (fun w => f w • iteratedFDeriv ℝ n κ (x - w)) := by
    intro n x
    have : SecondCountableTopologyEither Space
        (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ) := ⟨Or.inl inferInstance⟩
    refine Integrable.mono' ((hw.comp_sub_left x).const_mul (B0 * E n))
      ((hf.smul ((hkc n).comp (continuous_const.sub continuous_id))).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_smul]
    calc ‖f w‖ * ‖iteratedFDeriv ℝ n κ (x - w)‖ ≤ B0 * (E n * (1 + ‖x - w‖) ^ (-4 : ℝ)) :=
          mul_le_mul (hfb w) (hEb n _) (norm_nonneg _) hB0
      _ = B0 * E n * (1 + ‖x - w‖) ^ (-(4 : ℝ)) := by ring_nf
  have hd : ∀ (n : ℕ) (x₀ : Space), HasFDerivAt (fun x => ∫ w, f w • iteratedFDeriv ℝ n κ (x - w))
      (∫ w, f w • fderiv ℝ (iteratedFDeriv ℝ n κ) (x₀ - w)) x₀ := by
    intro n x₀
    have : SecondCountableTopologyEither Space
        (Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ) := ⟨Or.inl inferInstance⟩
    have hc : Continuous (fderiv ℝ (iteratedFDeriv ℝ n κ)) := by
      rw [fderiv_iteratedFDeriv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) ℝ).continuous.comp
        (hkc (n + 1))
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
      (F' := fun x w => f w • fderiv ℝ (iteratedFDeriv ℝ n κ) (x - w))
      (bound := fun w => B0 * E (n + 1) * 16 * (1 + ‖x₀ - w‖) ^ (-(4 : ℝ)))
      (ball_mem_nhds x₀ one_pos)
      (Filter.Eventually.of_forall (fun x => (hintj n x).aestronglyMeasurable)) (hintj n x₀) ?_ ?_
      ((hw.comp_sub_left x₀).const_mul _) ?_
    · exact (hf.smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun w x hx => ?_)
      rw [norm_smul, norm_fderiv_iteratedFDeriv]
      have hx' : ‖x₀ - x‖ < 1 := by rw [← dist_eq_norm, dist_comm]; exact hx
      have hsh : (1 + ‖x - w‖) ^ (-4 : ℝ) ≤ 16 * (1 + ‖x₀ - w‖) ^ (-4 : ℝ) := by
        refine shift16 (norm_nonneg _) (norm_nonneg _) ?_
        have := norm_sub_le_norm_sub_add_norm_sub x₀ x w
        have := norm_nonneg (x - w)
        linarith
      calc ‖f w‖ * ‖iteratedFDeriv ℝ (n + 1) κ (x - w)‖
          ≤ B0 * (E (n + 1) * (16 * (1 + ‖x₀ - w‖) ^ (-4 : ℝ))) :=
            mul_le_mul (hfb w) ((hEb _ _).trans (mul_le_mul_of_nonneg_left hsh (hE0 _)))
              (norm_nonneg _) hB0
        _ = B0 * E (n + 1) * 16 * (1 + ‖x₀ - w‖) ^ (-(4 : ℝ)) := by ring_nf
    · refine Filter.Eventually.of_forall (fun w x _ => ?_)
      have hdk : HasFDerivAt (iteratedFDeriv ℝ n κ) (fderiv ℝ (iteratedFDeriv ℝ n κ) (x - w))
          (x - w) :=
        ((hκ.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) _).hasFDerivAt
      have h2 := (hdk.comp x ((hasFDerivAt_id x).sub_const w)).const_smul (f w)
      simp only [ContinuousLinearMap.comp_id] at h2
      exact h2
  have hform : ∀ n : ℕ, iteratedFDeriv ℝ n (fun x => ∫ w, κ (x - w) * f w) =
      fun x => ∫ w, f w • iteratedFDeriv ℝ n κ (x - w) := by
    intro n
    induction n with
    | zero =>
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      have : (fun w => f w • iteratedFDeriv ℝ 0 κ (x - w)) =
          fun w => (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (κ (x - w) * f w) := by
        funext w; ext m; simp [mul_comm]
      rw [this, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ Space ℝ).symm.toContinuousLinearEquiv.integral_comp_comm
        _).symm
    | succ n ih =>
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd n x).fderiv]
      refine (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space)
        ℝ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm).trans ?_
      congr 1
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun m _ => ?_), hform⟩
  rw [hform m]
  exact fun x => (hd m x).differentiableAt

theorem cutoff_scale {R : ℝ} (hR : 0 < R) :
    (fun y => 1 - radialCutoff R y) =
      (fun y => 1 - radialCutoff 1 y) ∘ (R⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  funext y
  simp only [radialCutoff, Function.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_one]
  rw [div_eq_inv_mul]

theorem cutoff_deriv (i : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 < R → ∀ y : Space,
    ‖iteratedFDeriv ℝ i (fun y => 1 - radialCutoff R y) y‖ ≤ c * R ^ (-(i : ℝ)) := by
  have hχ : ContDiff ℝ ∞ (radialCutoff 1) := contDiff_radialCutoff one_pos
  have hψ : ContDiff ℝ ∞ (fun y : Space => 1 - radialCutoff 1 y) := contDiff_const.sub hχ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ u,
      ‖iteratedFDeriv ℝ i (fun y : Space => 1 - radialCutoff 1 y) u‖ ≤ c := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨1, fun u => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [radialCutoff_nonneg 1 u, radialCutoff_le_one 1 u]
    · obtain ⟨c, hc⟩ := ((hasCompactSupport_radialCutoff one_pos).iteratedFDeriv i).exists_bound_of_continuous
        (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
      refine ⟨c, fun u => ?_⟩
      rw [fun_iteratedFDeriv_sub_apply contDiffAt_const
        (hχ.contDiffAt.of_le (by exact_mod_cast le_top)),
        iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hi)]
      simpa using hc u
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  refine ⟨c, hc0, fun R hR y => ?_⟩
  rw [cutoff_scale hR, ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ _
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hn : ‖R⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ R⁻¹ := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  have e : R ^ (-(i : ℝ)) = R⁻¹ ^ i := by rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
  rw [e]
  exact mul_le_mul (hc _) (pow_le_pow_left₀ (norm_nonneg _) hn i) (by positivity) hc0

theorem far_kernel (j : ℕ) : ∃ a : ℝ, 0 ≤ a ∧ ∀ (k : Space → ℝ) (D : ℝ), ContDiff ℝ ∞ k →
    (∀ n ≤ j, ∀ y : Space, y ≠ 0 → ‖iteratedFDeriv ℝ n k y‖ ≤ D * ‖y‖ ^ (-(4 + n : ℝ))) →
    ∀ R : ℝ, 0 < R → ∀ y : Space,
      (‖y‖ < R → iteratedFDeriv ℝ j (fun z => (1 - radialCutoff R z) * k z) y = 0) ∧
      (R ≤ ‖y‖ → ‖iteratedFDeriv ℝ j (fun z => (1 - radialCutoff R z) * k z) y‖ ≤
        a * D * ∑ m ∈ Finset.range (j + 1), R ^ (-(m : ℝ)) * ‖y‖ ^ (-((4 : ℝ) + j - m))) := by
  choose c hc0 hc using cutoff_deriv
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c i,
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hc0 i), ?_⟩
  intro k D hk hD R hR y
  have hψ : ContDiff ℝ ∞ (fun y : Space => 1 - radialCutoff R y) :=
    contDiff_const.sub (contDiff_radialCutoff hR)
  constructor
  · intro hy
    have he : (fun z => (1 - radialCutoff R z) * k z) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with v hv
      rw [radialCutoff_eq_one hR (le_of_lt (mem_ball_zero_iff.1 hv)), sub_self, zero_mul]
    rw [(he.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    simp
  · intro hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, norm_zero] at hy
      linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hD0 : 0 ≤ D := by
      have h := (norm_nonneg _).trans (hD 0 (Nat.zero_le _) y hy0)
      exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hypos _)).1 h
    refine (norm_iteratedFDeriv_mul_le hψ hk y (n := j) (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => 1 - radialCutoff R y) y‖ *
          ‖iteratedFDeriv ℝ (j - i) k y‖
        ≤ ∑ i ∈ Finset.range (j + 1), (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c i) * D *
          (R ^ (-(i : ℝ)) * ‖y‖ ^ (-((4 : ℝ) + j - i))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have hk1 := hD (j - i) (Nat.sub_le j i) y hy0
          have hcast : (-(4 + ((j - i : ℕ) : ℝ))) = -((4 : ℝ) + j - i) := by
            rw [Nat.cast_sub hij]; ring
          rw [hcast] at hk1
          have ha : (j.choose i : ℝ) * c i ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c i :=
            Finset.single_le_sum (f := fun i => (j.choose i : ℝ) * c i)
              (fun i _ => mul_nonneg (by positivity) (hc0 i)) hi
          have hp1 : 0 ≤ R ^ (-(i : ℝ)) := by positivity
          have hp2 : 0 ≤ ‖y‖ ^ (-((4 : ℝ) + j - i)) := by positivity
          calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => 1 - radialCutoff R y) y‖ *
                ‖iteratedFDeriv ℝ (j - i) k y‖
              ≤ (j.choose i : ℝ) * (c i * R ^ (-(i : ℝ))) * (D * ‖y‖ ^ (-((4 : ℝ) + j - i))) :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hc i R hR y) (by positivity)) hk1
                  (norm_nonneg _) (by have := hc0 i; positivity)
            _ = ((j.choose i : ℝ) * c i) * D * (R ^ (-(i : ℝ)) * ‖y‖ ^ (-((4 : ℝ) + j - i))) := by
                ring
            _ ≤ _ := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hD0) ?_
                positivity
      _ = _ := by rw [← Finset.mul_sum]

theorem far_kernel_qual {k : Space → ℝ} (hk : ContDiff ℝ ∞ k)
    (hE : ∀ n : ℕ, ∃ E : ℝ, ∀ y : Space, y ≠ 0 →
      ‖iteratedFDeriv ℝ n k y‖ ≤ E * ‖y‖ ^ (-(4 + n : ℝ)))
    {R : ℝ} (hR : 0 < R) (n : ℕ) : ∃ E : ℝ, ∀ y,
      ‖iteratedFDeriv ℝ n (fun z => (1 - radialCutoff R z) * k z) y‖ ≤ E * (1 + ‖y‖) ^ (-4 : ℝ) := by
  choose E hEb using hE
  obtain ⟨a, ha0, ha⟩ := far_kernel n
  set D : ℝ := ∑ m ∈ Finset.range (n + 1), |E m| with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : ∀ m ≤ n, ∀ y : Space, y ≠ 0 →
      ‖iteratedFDeriv ℝ m k y‖ ≤ D * ‖y‖ ^ (-(4 + m : ℝ)) := by
    intro m hm y hy
    refine (hEb m y hy).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun m => |E m|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega)))) (by positivity))
  set T : ℕ → ℝ := fun m => R ^ (-(m : ℝ)) * (R ^ (-((n : ℝ) - m)) * (1 + R⁻¹) ^ (4 : ℝ))
    with hT
  have hT0 : ∀ m, 0 ≤ T m := fun m => by positivity
  refine ⟨a * D * ∑ m ∈ Finset.range (n + 1), T m, fun y => ?_⟩
  obtain ⟨h0, h1⟩ := ha k D hk hD R hR y
  by_cases hy : R ≤ ‖y‖
  · refine (h1 hy).trans ?_
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hy
    have key : ∀ m ∈ Finset.range (n + 1), R ^ (-(m : ℝ)) * ‖y‖ ^ (-((4 : ℝ) + n - m)) ≤
        T m * (1 + ‖y‖) ^ (-4 : ℝ) := by
      intro m hm
      have hm' : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      have e1 : ‖y‖ ^ (-((4 : ℝ) + n - m)) = ‖y‖ ^ (-((n : ℝ) - m)) * ‖y‖ ^ (-4 : ℝ) := by
        rw [← Real.rpow_add hy0]; ring_nf
      have e2 : ‖y‖ ^ (-((n : ℝ) - m)) ≤ R ^ (-((n : ℝ) - m)) :=
        Real.rpow_le_rpow_of_nonpos hR hy (by linarith)
      have e3 : ‖y‖ ^ (-4 : ℝ) ≤ (1 + R⁻¹) ^ (4 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by
        have h3 : 1 + ‖y‖ ≤ (1 + R⁻¹) * ‖y‖ := by
          have : 1 ≤ R⁻¹ * ‖y‖ := by rw [inv_mul_eq_div, le_div_iff₀ hR]; linarith
          nlinarith
        have h4 : ((1 + R⁻¹) * ‖y‖) ^ (-4 : ℝ) ≤ (1 + ‖y‖) ^ (-4 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by norm_num)
        rw [Real.mul_rpow (by positivity) hy0.le, Real.rpow_neg (x := 1 + R⁻¹) (by positivity)]
          at h4
        have hp : 0 < (1 + R⁻¹) ^ (4 : ℝ) := by positivity
        rw [← div_eq_inv_mul, div_le_iff₀ hp] at h4
        linarith
      rw [e1]
      calc R ^ (-(m : ℝ)) * (‖y‖ ^ (-((n : ℝ) - m)) * ‖y‖ ^ (-4 : ℝ))
          ≤ R ^ (-(m : ℝ)) * (R ^ (-((n : ℝ) - m)) * ((1 + R⁻¹) ^ (4 : ℝ) *
            (1 + ‖y‖) ^ (-4 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul e2 e3 (by positivity) (by positivity))
              (by positivity)
        _ = T m * (1 + ‖y‖) ^ (-4 : ℝ) := by rw [hT]; ring
    calc a * D * ∑ m ∈ Finset.range (n + 1), R ^ (-(m : ℝ)) * ‖y‖ ^ (-((4 : ℝ) + n - m))
        ≤ a * D * ∑ m ∈ Finset.range (n + 1), T m * (1 + ‖y‖) ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum key) (mul_nonneg ha0 hD0)
      _ = a * D * (∑ m ∈ Finset.range (n + 1), T m) * (1 + ‖y‖) ^ (-4 : ℝ) := by
          rw [← Finset.sum_mul]; ring
  · rw [h0 (not_le.1 hy), norm_zero]
    have : 0 ≤ ∑ m ∈ Finset.range (n + 1), T m := Finset.sum_nonneg fun m _ => hT0 m
    positivity

theorem scale_pow {s p r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    s ^ (-p) * (s⁻¹ * r) ^ (-p) = r ^ (-p) := by
  rw [Real.mul_rpow (inv_nonneg.2 hs.le) hr, Real.inv_rpow hs.le, ← mul_assoc,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne', one_mul]

theorem div_pow_neg {s a p : ℝ} (hs : 0 < s) (ha : 0 < a) : (s / a) ^ (-p) = a ^ p * s ^ (-p) := by
  rw [div_eq_mul_inv, Real.mul_rpow hs.le (inv_nonneg.2 ha.le), Real.inv_rpow ha.le,
    Real.rpow_neg ha.le, inv_inv, mul_comm]

theorem scale_int (F : Space → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ w, F (s⁻¹ • w) = s ^ 3 * ∫ w, F w := by
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin, inv_pow, inv_inv,
    abs_of_pos (by positivity), smul_eq_mul]

theorem norm_inv_smul {s : ℝ} (hs : 0 < s) (y : Space) : ‖s⁻¹ • y‖ = s⁻¹ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]

theorem far_integral {β : ℝ} (hβ0 : 0 ≤ β) (hβ3 : β < 3) {q : ℝ} (hq : 3 < q) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x : Space,
      Integrable (fun w : Space => (if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) *
        (1 + ‖w‖) ^ (-β)) ∧
      ∫ w, (if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) * (1 + ‖w‖) ^ (-β) ≤
        Q * (1 + ‖x‖) ^ (3 - q - β) := by
  set g1 : Space → ℝ := fun u => if 1 / 4 ≤ ‖u‖ then ‖u‖ ^ (-q) else 0 with hg1d
  set g2 : Space → ℝ := fun u => if ‖u‖ < 1 then ‖u‖ ^ (-β) else 0 with hg2d
  set u0 : Space → ℝ := fun u => (1 + ‖u‖) ^ (-(4 : ℝ)) with hu0d
  have hint4 : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hu0 : Integrable u0 := integrable_one_add_norm hint4
  have hintq : q > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; push_cast; linarith
  have hg1m : Measurable g1 :=
    Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (measurable_norm.pow_const _) measurable_const
  have hg1 : Integrable g1 := by
    refine ((integrable_one_add_norm hintq).const_mul ((5 : ℝ) ^ q)).mono'
      hg1m.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [hg1d]
    dsimp only
    split_ifs with hu
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have h1 : (1 + ‖u‖) / 5 ≤ ‖u‖ := by linarith
      have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖u‖) / 5) h1
        (by linarith : -q ≤ 0)
      rw [div_pow_neg (by positivity) (by norm_num)] at h2
      exact h2
    · simp only [norm_zero]
      positivity
  have hg2 : Integrable g2 := by
    have e : g2 = (ball (0 : Space) 1).indicator (fun u => ‖u‖ ^ (-β)) := by
      funext u
      by_cases hu : ‖u‖ < 1
      · rw [Set.indicator_of_mem (mem_ball_zero_iff.2 hu)]
        simp only [hg2d, if_pos hu]
      · rw [Set.indicator_of_notMem (fun h => hu (mem_ball_zero_iff.1 h))]
        simp only [hg2d, if_neg hu]
    rw [e]
    exact (integrableOn_ball_norm_rpow (by linarith)).integrable_indicator measurableSet_ball
  have hg1n : ∀ u, 0 ≤ g1 u := fun u => by
    rw [hg1d]; dsimp only; split_ifs <;> positivity
  have hg2n : ∀ u, 0 ≤ g2 u := fun u => by
    rw [hg2d]; dsimp only; split_ifs <;> positivity
  have hI1 : 0 ≤ ∫ u, g1 u := integral_nonneg hg1n
  have hI2 : 0 ≤ ∫ u, g2 u := integral_nonneg hg2n
  have hI0 : 0 ≤ ∫ u, u0 u := integral_nonneg fun u => by positivity
  refine ⟨8 ^ β * (∫ u, g1 u) + 4 ^ q * ((∫ u, g2 u) + ∫ u, u0 u), by positivity, fun x => ?_⟩
  set s : ℝ := 1 + ‖x‖ with hs
  have hs1 : 1 ≤ s := by linarith [norm_nonneg x]
  have hs0 : 0 < s := by linarith
  set c1 : ℝ := 8 ^ β * s ^ (-β) * s ^ (-q) with hc1
  set c2 : ℝ := 4 ^ q * s ^ (-q) * s ^ (-β) with hc2
  set c3 : ℝ := 4 ^ q * s ^ (-q) with hc3
  have hA : Integrable (fun w => g1 (s⁻¹ • (x - w))) :=
    (hg1.comp_smul (inv_ne_zero hs0.ne')).comp_sub_left x
  have hB : Integrable (fun w => g2 (s⁻¹ • w)) := hg2.comp_smul (inv_ne_zero hs0.ne')
  have hH : Integrable (fun w => c1 * g1 (s⁻¹ • (x - w)) + c2 * g2 (s⁻¹ • w) + c3 * u0 w) :=
    ((hA.const_mul c1).add (hB.const_mul c2)).add (hu0.const_mul c3)
  have hmeas : AEStronglyMeasurable (fun w : Space =>
      (if s / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) * (1 + ‖w‖) ^ (-β)) volume := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
        ((by fun_prop : Measurable fun w : Space => ‖x - w‖).pow_const _) measurable_const
    · exact ((by fun_prop : Measurable fun w : Space => 1 + ‖w‖)).pow_const _
  have hpt : ∀ w : Space, 0 ≤ (if s / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) *
        (1 + ‖w‖) ^ (-β) ∧
      (if s / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) * (1 + ‖w‖) ^ (-β) ≤
        c1 * g1 (s⁻¹ • (x - w)) + c2 * g2 (s⁻¹ • w) + c3 * u0 w := by
    intro w
    have hH0 : 0 ≤ c1 * g1 (s⁻¹ • (x - w)) + c2 * g2 (s⁻¹ • w) + c3 * u0 w := by
      have := hg1n (s⁻¹ • (x - w)); have := hg2n (s⁻¹ • w)
      have : 0 ≤ u0 w := by positivity
      positivity
    split_ifs with hw
    · have hxw : 0 < ‖x - w‖ := lt_of_lt_of_le (by positivity) hw
      refine ⟨by positivity, ?_⟩
      by_cases hA' : s / 8 ≤ 1 + ‖w‖
      · have e1 : ‖x - w‖ ^ (-q) = s ^ (-q) * g1 (s⁻¹ • (x - w)) := by
          have : 1 / 4 ≤ ‖s⁻¹ • (x - w)‖ := by
            rw [norm_inv_smul hs0, inv_mul_eq_div, le_div_iff₀ hs0]; linarith
          rw [hg1d]; dsimp only
          rw [if_pos this, norm_inv_smul hs0, scale_pow hs0 (norm_nonneg _)]
        have e2 : (1 + ‖w‖) ^ (-β) ≤ 8 ^ β * s ^ (-β) := by
          rw [← div_pow_neg hs0 (by norm_num)]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hA' (by linarith)
        have hg := hg1n (s⁻¹ • (x - w))
        have h2 := hg2n (s⁻¹ • w)
        have : 0 ≤ u0 w := by positivity
        calc ‖x - w‖ ^ (-q) * (1 + ‖w‖) ^ (-β) ≤ ‖x - w‖ ^ (-q) * (8 ^ β * s ^ (-β)) :=
              mul_le_mul_of_nonneg_left e2 (by positivity)
          _ = c1 * g1 (s⁻¹ • (x - w)) := by rw [e1, hc1]; ring
          _ ≤ _ := by
              have : 0 ≤ c2 * g2 (s⁻¹ • w) + c3 * u0 w := by positivity
              linarith
      · have hw1 : ‖w‖ < s := by linarith [not_le.1 hA']
        have e1 : ‖x - w‖ ^ (-q) ≤ 4 ^ q * s ^ (-q) := by
          rw [← div_pow_neg hs0 (by norm_num)]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hw (by linarith)
        have e2 : (1 + ‖w‖) ^ (-β) ≤ s ^ (-β) * g2 (s⁻¹ • w) + u0 w := by
          by_cases hw0 : w = 0
          · subst hw0
            have : 0 ≤ s ^ (-β) * g2 (s⁻¹ • (0 : Space)) := by
              have := hg2n (s⁻¹ • (0 : Space)); positivity
            simp only [norm_zero, add_zero, Real.one_rpow, hu0d] at this ⊢
            linarith
          · have hwp : 0 < ‖w‖ := norm_pos_iff.2 hw0
            have hlt : ‖s⁻¹ • w‖ < 1 := by
              rw [norm_inv_smul hs0, inv_mul_eq_div, div_lt_one hs0]; exact hw1
            have e3 : s ^ (-β) * g2 (s⁻¹ • w) = ‖w‖ ^ (-β) := by
              rw [hg2d]; dsimp only
              rw [if_pos hlt, norm_inv_smul hs0, scale_pow hs0 (norm_nonneg _)]
            have e4 : (1 + ‖w‖) ^ (-β) ≤ ‖w‖ ^ (-β) :=
              Real.rpow_le_rpow_of_nonpos hwp (by linarith) (by linarith)
            have : 0 ≤ u0 w := by positivity
            linarith
        have hg := hg1n (s⁻¹ • (x - w))
        calc ‖x - w‖ ^ (-q) * (1 + ‖w‖) ^ (-β)
            ≤ (4 ^ q * s ^ (-q)) * (s ^ (-β) * g2 (s⁻¹ • w) + u0 w) :=
              mul_le_mul e1 e2 (by positivity) (by positivity)
          _ = c2 * g2 (s⁻¹ • w) + c3 * u0 w := by rw [hc2, hc3]; ring
          _ ≤ _ := by
              have : 0 ≤ c1 * g1 (s⁻¹ • (x - w)) := by positivity
              linarith
    · simp only [zero_mul, le_refl, true_and]
      exact hH0
  have hInt : Integrable (fun w : Space =>
      (if s / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-q) else 0) * (1 + ‖w‖) ^ (-β)) :=
    hH.mono' hmeas (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpt w).1]; exact (hpt w).2)
  refine ⟨hInt, ?_⟩
  refine (integral_mono hInt hH fun w => (hpt w).2).trans ?_
  have hAB : Integrable (fun w => c1 * g1 (s⁻¹ • (x - w)) + c2 * g2 (s⁻¹ • w)) :=
    (hA.const_mul c1).add (hB.const_mul c2)
  have hC3 : Integrable (fun w => c3 * u0 w) := hu0.const_mul c3
  have hA1 : Integrable (fun w => c1 * g1 (s⁻¹ • (x - w))) := hA.const_mul c1
  have hB1 : Integrable (fun w => c2 * g2 (s⁻¹ • w)) := hB.const_mul c2
  rw [integral_add hAB hC3, integral_add hA1 hB1, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have eA : ∫ w, g1 (s⁻¹ • (x - w)) = s ^ 3 * ∫ u, g1 u := by
    rw [integral_sub_left_eq_self (fun w => g1 (s⁻¹ • w)) volume x]
    exact scale_int g1 hs0
  have eB : ∫ w, g2 (s⁻¹ • w) = s ^ 3 * ∫ u, g2 u := scale_int g2 hs0
  rw [eA, eB]
  have e3 : s ^ (3 : ℕ) = s ^ (3 : ℝ) := by exact_mod_cast (Real.rpow_natCast s 3).symm
  have ek : ∀ p r : ℝ, s ^ (-p) * s ^ (-r) * s ^ (3 : ℕ) = s ^ (3 - r - p) := by
    intro p r
    rw [e3, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
    congr 1; ring
  have hq3 : s ^ (-q) ≤ s ^ (3 - q - β) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hk1 : c1 * (s ^ 3 * ∫ u, g1 u) = 8 ^ β * (∫ u, g1 u) * s ^ (3 - q - β) := by
    rw [hc1, ← ek β q]; ring
  have hk2 : c2 * (s ^ 3 * ∫ u, g2 u) = 4 ^ q * (∫ u, g2 u) * s ^ (3 - q - β) := by
    rw [hc2, ← ek β q]; ring
  rw [hk1, hk2, hc3]
  have h4 : (0 : ℝ) ≤ 4 ^ q := by positivity
  have : 4 ^ q * s ^ (-q) * ∫ u, u0 u ≤ 4 ^ q * (∫ u, u0 u) * s ^ (3 - q - β) := by
    have := mul_le_mul_of_nonneg_left hq3 (mul_nonneg h4 hI0)
    linarith
  nlinarith [this]

theorem split_eq {k f : Space → ℝ} (hk : Continuous k) (hki : Integrable k) (hf : Continuous f)
    {B0 : ℝ} (hfb : ∀ y, ‖f y‖ ≤ B0) {R : ℝ} (hR : 0 < R) :
    (fun x => ∫ z, k (x - z) * f z) =
      (fun x => ∫ z, (fun y => radialCutoff R y * k y) z * f (x - z)) +
      (fun x => ∫ w, (fun y => (1 - radialCutoff R y) * k y) (x - w) * f w) := by
  have hχc : Continuous (radialCutoff R) := (contDiff_radialCutoff hR).continuous
  have hmul : ∀ (u : Space → ℝ), Continuous u → Integrable u → ∀ x : Space,
      Integrable (fun z => u (x - z) * f z) := by
    intro u hu hui x
    refine Integrable.mono' ((hui.comp_sub_left x).norm.mul_const B0)
      ((hu.comp (continuous_const.sub continuous_id)).mul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hfb z) (norm_nonneg _)
  have hφc : Continuous (fun y => radialCutoff R y * k y) := hχc.mul hk
  have hκc : Continuous (fun y => (1 - radialCutoff R y) * k y) := (continuous_const.sub hχc).mul hk
  have hφi : Integrable (fun y => radialCutoff R y * k y) := by
    refine hki.norm.mono' hφc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs (radialCutoff R y), abs_of_nonneg (radialCutoff_nonneg R y)]
    exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_le_one R y)
  have hκi : Integrable (fun y => (1 - radialCutoff R y) * k y) := by
    refine hki.norm.mono' hκc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have h0 := radialCutoff_nonneg R y
    have h1 := radialCutoff_le_one R y
    rw [norm_mul, Real.norm_eq_abs (1 - radialCutoff R y), abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  funext x
  rw [Pi.add_apply]
  have e1 : ∫ z, (fun y => radialCutoff R y * k y) z * f (x - z) =
      ∫ z, (fun y => radialCutoff R y * k y) (x - z) * f z := by
    rw [← integral_sub_left_eq_self (fun z => (fun y => radialCutoff R y * k y) z * f (x - z))
      volume x]
    simp only [sub_sub_cancel]
  rw [e1, ← integral_add (hmul _ hφc hφi x) (hmul _ hκc hκi x)]
  congr 1
  funext z
  beta_reduce
  ring

theorem weight_alg {s b β : ℝ} {j m : ℕ} (hs : 1 ≤ s) (hb : b ≤ β + 1 + j) :
    s ^ b * ((s / 4) ^ (-(m : ℝ)) * s ^ (3 - ((4 : ℝ) + j - m) - β)) ≤ 4 ^ (m : ℝ) := by
  have hs0 : 0 < s := by linarith
  rw [Real.div_rpow hs0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), div_inv_eq_mul]
  have e : s ^ b * (s ^ (-(m : ℝ)) * 4 ^ (m : ℝ) * s ^ (3 - ((4 : ℝ) + j - m) - β)) =
      4 ^ (m : ℝ) * s ^ (b + -(m : ℝ) + (3 - ((4 : ℝ) + j - m) - β)) := by
    rw [Real.rpow_add hs0, Real.rpow_add hs0]
    ring
  rw [e]
  have h1 : s ^ (b + -(m : ℝ) + (3 - ((4 : ℝ) + j - m) - β)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have h4 : (0 : ℝ) ≤ 4 ^ (m : ℝ) := by positivity
  calc 4 ^ (m : ℝ) * s ^ (b + -(m : ℝ) + (3 - ((4 : ℝ) + j - m) - β)) ≤ 4 ^ (m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = 4 ^ (m : ℝ) := mul_one _

theorem conv_core {β b : ℝ} (j : ℕ) (hβ0 : 0 ≤ β) (hβ3 : β < 3) (hb0 : 0 ≤ b)
    (hb : b ≤ β + 1 + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Space → ℝ) (D L : ℝ), ContDiff ℝ ∞ k → Integrable k →
      (∫ y, ‖k y‖) ≤ L →
      (∀ n ≤ j, ∀ y : Space, y ≠ 0 → ‖iteratedFDeriv ℝ n k y‖ ≤ D * ‖y‖ ^ (-(4 + n : ℝ))) →
      (∀ n : ℕ, ∃ E : ℝ, ∀ y : Space, y ≠ 0 →
        ‖iteratedFDeriv ℝ n k y‖ ≤ E * ‖y‖ ^ (-(4 + n : ℝ))) →
      ∀ (f : Space → ℝ) (A B : ℝ), ContDiff ℝ j f →
        (∀ y, (1 + ‖y‖) ^ b * ‖iteratedFDeriv ℝ j f y‖ ≤ A) →
        (∀ y, (1 + ‖y‖) ^ β * ‖f y‖ ≤ B) →
        ContDiff ℝ j (fun x => ∫ z, k (x - z) * f z) ∧
        ∀ x, (1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (fun x => ∫ z, k (x - z) * f z) x‖ ≤
          C * (L * A + D * B) := by
  obtain ⟨a, ha0, ha⟩ := far_kernel j
  have hQex : ∀ m : ℕ, ∃ Q : ℝ, 0 ≤ Q ∧ (m ≤ j → ∀ x : Space,
      Integrable (fun w : Space =>
        (if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-((4 : ℝ) + j - m)) else 0) *
          (1 + ‖w‖) ^ (-β)) ∧
      ∫ w, (if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-((4 : ℝ) + j - m)) else 0) *
          (1 + ‖w‖) ^ (-β) ≤ Q * (1 + ‖x‖) ^ (3 - ((4 : ℝ) + j - m) - β)) := by
    intro m
    by_cases hm : m ≤ j
    · have hq : (3 : ℝ) < (4 : ℝ) + j - m := by
        have : (m : ℝ) ≤ j := by exact_mod_cast hm
        linarith
      obtain ⟨Q, hQ0, hQ⟩ := far_integral hβ0 hβ3 hq
      exact ⟨Q, hQ0, fun _ => hQ⟩
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose Q hQ0 hQ using hQex
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m :=
    Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (hQ0 m)
  refine ⟨2 ^ b + a * ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m, by positivity, ?_⟩
  intro k D L hk hki hkL hD hE f A B hf hA hB
  have hkc : Continuous k := hk.continuous
  have hfc : Continuous f := hf.continuous
  have hA0 : 0 ≤ A := le_trans (by positivity) (hA 0)
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  have hL0 : 0 ≤ L := le_trans (integral_nonneg fun y => norm_nonneg _) hkL
  have hD0 : 0 ≤ D := by
    set e : Space := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
    have he : e ≠ 0 := by
      intro h
      have := congrArg (fun v : Space => v 0) h
      simp [e] at this
    have h := (norm_nonneg _).trans (hD 0 (Nat.zero_le _) e he)
    have hp : 0 < ‖e‖ ^ (-(4 + ((0 : ℕ) : ℝ))) := Real.rpow_pos_of_pos (norm_pos_iff.2 he) _
    exact (mul_nonneg_iff_of_pos_right hp).1 h
  have hfB : ∀ w, ‖f w‖ ≤ B * (1 + ‖w‖) ^ (-β) := by
    intro w
    have hp : 0 < (1 + ‖w‖) ^ β := by positivity
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
    exact hB w
  have hfB' : ∀ w, ‖f w‖ ≤ B := fun w =>
    (hfB w).trans (mul_le_of_le_one_right hB0
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg w]) (by linarith)))
  have hnear : ∀ R : ℝ, 0 < R → ContDiff ℝ j
      (fun x => ∫ z, (fun y => radialCutoff R y * k y) z * f (x - z)) ∧
      iteratedFDeriv ℝ j (fun x => ∫ z, (fun y => radialCutoff R y * k y) z * f (x - z)) =
        fun x => ∫ z, (fun y => radialCutoff R y * k y) z • iteratedFDeriv ℝ j f (x - z) :=
    fun R hR => near_deriv ((contDiff_radialCutoff hR).continuous.mul hkc)
      ((hasCompactSupport_radialCutoff hR).mul_right) hf
  have hfar : ∀ R : ℝ, 0 < R → ContDiff ℝ ∞
      (fun x => ∫ w, (fun y => (1 - radialCutoff R y) * k y) (x - w) * f w) ∧ ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun x => ∫ w, (fun y => (1 - radialCutoff R y) * k y) (x - w) * f w) =
        fun x => ∫ w, f w • iteratedFDeriv ℝ n (fun y => (1 - radialCutoff R y) * k y) (x - w) :=
    fun R hR => far_deriv ((contDiff_const.sub (contDiff_radialCutoff hR)).mul hk)
      (far_kernel_qual hk hE hR) hfc hfB'
  refine ⟨?_, fun x => ?_⟩
  · rw [split_eq hkc hki hfc hfB' one_pos]
    exact (hnear 1 one_pos).1.add ((hfar 1 one_pos).1.of_le (by exact_mod_cast le_top))
  set s : ℝ := 1 + ‖x‖ with hs
  have hs1 : 1 ≤ s := by linarith [norm_nonneg x]
  have hR : 0 < (1 + ‖x‖) / 4 := by positivity
  rw [split_eq hkc hki hfc hfB' hR]
  rw [iteratedFDeriv_add_apply (hnear _ hR).1.contDiffAt
    ((hfar _ hR).1.of_le (by exact_mod_cast le_top)).contDiffAt, (hnear _ hR).2, (hfar _ hR).2 j]
  have hsb : 0 < s ^ b := by positivity
  have hN : ‖∫ z, (fun y => radialCutoff ((1 + ‖x‖) / 4) y * k y) z • iteratedFDeriv ℝ j f (x - z)‖ ≤
      L * (2 ^ b * A * (s ^ b)⁻¹) := by
    refine (norm_integral_le_of_norm_le (hki.norm.mul_const (2 ^ b * A * (s ^ b)⁻¹))
      (Filter.Eventually.of_forall fun z => ?_)).trans ?_
    · rw [norm_smul]
      have hc0 := radialCutoff_nonneg ((1 + ‖x‖) / 4) z
      have hc1 := radialCutoff_le_one ((1 + ‖x‖) / 4) z
      by_cases hz : radialCutoff ((1 + ‖x‖) / 4) z = 0
      · simp only [hz, zero_mul, norm_zero]
        positivity
      · have hzn : ‖z‖ < 2 * ((1 + ‖x‖) / 4) := by
          by_contra hcon
          exact hz (radialCutoff_eq_zero hR (not_lt.1 hcon))
        have hk1 : ‖radialCutoff ((1 + ‖x‖) / 4) z * k z‖ ≤ ‖k z‖ := by
          rw [norm_mul, Real.norm_eq_abs (radialCutoff _ z), abs_of_nonneg hc0]
          exact mul_le_of_le_one_left (norm_nonneg _) hc1
        have hxz : s ≤ 2 * (1 + ‖x - z‖) := by
          have := norm_sub_norm_le x z
          linarith
        have hsb2 : s ^ b ≤ 2 ^ b * (1 + ‖x - z‖) ^ b := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) hxz hb0
        have hG : ‖iteratedFDeriv ℝ j f (x - z)‖ ≤ 2 ^ b * A * (s ^ b)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hsb]
          calc ‖iteratedFDeriv ℝ j f (x - z)‖ * s ^ b ≤
              ‖iteratedFDeriv ℝ j f (x - z)‖ * (2 ^ b * (1 + ‖x - z‖) ^ b) :=
                mul_le_mul_of_nonneg_left hsb2 (norm_nonneg _)
            _ = 2 ^ b * ((1 + ‖x - z‖) ^ b * ‖iteratedFDeriv ℝ j f (x - z)‖) := by ring
            _ ≤ 2 ^ b * A := mul_le_mul_of_nonneg_left (hA _) (by positivity)
        exact mul_le_mul hk1 hG (norm_nonneg _) (norm_nonneg _)
    · rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right hkL (by positivity)
  have hFar : ‖∫ w, f w • iteratedFDeriv ℝ j
      (fun y => (1 - radialCutoff ((1 + ‖x‖) / 4) y) * k y) (x - w)‖ ≤
      a * D * B * ∑ m ∈ Finset.range (j + 1), ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
        (Q m * (1 + ‖x‖) ^ (3 - ((4 : ℝ) + j - m) - β)) := by
    have hint : ∀ m ∈ Finset.range (j + 1), Integrable (fun w : Space =>
        ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
        ((if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-((4 : ℝ) + j - m)) else 0) *
          (1 + ‖w‖) ^ (-β))) := fun m hm =>
      ((hQ m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) x).1.const_mul _)
    refine (norm_integral_le_of_norm_le ((integrable_finsetSum _ hint).const_mul (a * D * B))
      (Filter.Eventually.of_forall fun w => ?_)).trans ?_
    · rw [norm_smul]
      obtain ⟨h0, h1⟩ := ha k D hk hD ((1 + ‖x‖) / 4) hR (x - w)
      by_cases hw : (1 + ‖x‖) / 4 ≤ ‖x - w‖
      · have hsum : ∑ m ∈ Finset.range (j + 1), ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
            ((if (1 + ‖x‖) / 4 ≤ ‖x - w‖ then ‖x - w‖ ^ (-((4 : ℝ) + j - m)) else 0) *
              (1 + ‖w‖) ^ (-β)) =
            (∑ m ∈ Finset.range (j + 1), ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
              ‖x - w‖ ^ (-((4 : ℝ) + j - m))) * (1 + ‖w‖) ^ (-β) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [if_pos hw]
          ring
        rw [hsum]
        have hk2 := h1 hw
        have hp : 0 ≤ (1 + ‖w‖) ^ (-β) := by positivity
        calc ‖f w‖ * ‖iteratedFDeriv ℝ j (fun y => (1 - radialCutoff ((1 + ‖x‖) / 4) y) * k y)
              (x - w)‖ ≤ (B * (1 + ‖w‖) ^ (-β)) * (a * D * ∑ m ∈ Finset.range (j + 1),
                ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) * ‖x - w‖ ^ (-((4 : ℝ) + j - m))) :=
              mul_le_mul (hfB w) hk2 (norm_nonneg _) (by positivity)
          _ = a * D * B * ((∑ m ∈ Finset.range (j + 1), ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
              ‖x - w‖ ^ (-((4 : ℝ) + j - m))) * (1 + ‖w‖) ^ (-β)) := by ring
      · rw [h0 (not_le.1 hw), norm_zero, mul_zero]
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
        rw [if_neg hw, zero_mul, mul_zero]
    · rw [integral_const_mul, integral_finsetSum _ hint]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) (by positivity)
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hQ m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) x).2
        (by positivity)
  have hFar2 : s ^ b * (a * D * B * ∑ m ∈ Finset.range (j + 1), ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) *
        (Q m * (1 + ‖x‖) ^ (3 - ((4 : ℝ) + j - m) - β))) ≤
      a * D * B * ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m := by
    rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
    have := weight_alg (j := j) (m := m) (β := β) hs1 hb
    calc s ^ b * (((1 + ‖x‖) / 4) ^ (-(m : ℝ)) * (Q m * (1 + ‖x‖) ^ (3 - ((4 : ℝ) + j - m) - β)))
        = Q m * (s ^ b * ((s / 4) ^ (-(m : ℝ)) * s ^ (3 - ((4 : ℝ) + j - m) - β))) := by
          rw [hs]; ring
      _ ≤ Q m * 4 ^ (m : ℝ) := mul_le_mul_of_nonneg_left this (hQ0 m)
      _ = 4 ^ (m : ℝ) * Q m := by ring
  calc s ^ b * ‖(∫ z, (fun y => radialCutoff ((1 + ‖x‖) / 4) y * k y) z •
        iteratedFDeriv ℝ j f (x - z)) + ∫ w, f w • iteratedFDeriv ℝ j
        (fun y => (1 - radialCutoff ((1 + ‖x‖) / 4) y) * k y) (x - w)‖
      ≤ s ^ b * (L * (2 ^ b * A * (s ^ b)⁻¹)) + s ^ b * (a * D * B * ∑ m ∈ Finset.range (j + 1),
        ((1 + ‖x‖) / 4) ^ (-(m : ℝ)) * (Q m * (1 + ‖x‖) ^ (3 - ((4 : ℝ) + j - m) - β))) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hN hFar)) hsb.le
    _ ≤ 2 ^ b * (L * A) + a * D * B * ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m := by
        refine add_le_add (le_of_eq ?_) hFar2
        field_simp
    _ ≤ (2 ^ b + a * ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m) * (L * A + D * B) := by
        have h2b : (0 : ℝ) ≤ 2 ^ b := by positivity
        have hLA : 0 ≤ L * A := mul_nonneg hL0 hA0
        have hDB : 0 ≤ D * B := mul_nonneg hD0 hB0
        have haS : 0 ≤ a * ∑ m ∈ Finset.range (j + 1), (4 : ℝ) ^ (m : ℝ) * Q m := mul_nonneg ha0 hS0
        nlinarith [mul_nonneg h2b hDB, mul_nonneg haS hLA]

def unitMap (i : Fin 3) : ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))

def comp (α t : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (c : Fin 3 × Fin 3 × Fin 3) (x : Space) : ℝ :=
  ∫ z, (projDivKernel α t c.1 c.2.1 c.2.2 (x - z)).re * F z c.2.1 c.2.2

theorem heatDivConv_eq (α t : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) :
    heatDivConv α t F = fun x => ∑ c : Fin 3 × Fin 3 × Fin 3, unitMap c.1 (comp α t F c x) := by
  funext x
  ext m
  simp [heatDivConv, comp, unitMap, Fintype.sum_prod_type, Pi.single_apply]

end Breakdown.FracInternal.DecayHeatDiv

namespace Breakdown.FracCert

open Breakdown.FracInternal.DecayHeatDiv

theorem heatDivBound_of (h1 : KernelDecayStatement) (h2 : KernelScalingStatement) :
    HeatDivBoundStatement := by
  intro α hα1 hα2 β b j hβ0 hβ3 hb0 hb
  have hα0 : 0 < α := by linarith
  obtain ⟨C0, hC00, hC0⟩ := conv_core j hβ0 hβ3 hb0 hb
  choose Cd hCd using fun c : Fin 3 × Fin 3 × Fin 3 => (h1 α hα0 c.1 c.2.1 c.2.2).2
  set Dk : ℝ := ∑ c : Fin 3 × Fin 3 × Fin 3, ∑ n ∈ Finset.range (j + 1), |Cd c n| with hDk
  set Lk : ℝ := ∑ c : Fin 3 × Fin 3 × Fin 3, ∫ x, ‖projDivKernel α 1 c.1 c.2.1 c.2.2 x‖ with hLk
  set M : ℝ := ∑ i : Fin 3, ‖unitMap i‖ with hM
  have hDk0 : 0 ≤ Dk := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun n _ => abs_nonneg _
  have hLk0 : 0 ≤ Lk := Finset.sum_nonneg fun c _ => integral_nonneg fun x => norm_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨27 * M * (C0 * (Lk + Dk)), ?_⟩
  intro t ht0 ht1 F A B hF hA hB x
  set g : ℝ := t ^ (-(1 / (2 * α))) with hg
  have hpos : 0 < 1 / (2 * α) := by positivity
  have hg1 : 1 ≤ g := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hA0 : 0 ≤ A := le_trans (by positivity) (hA 0)
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  have hcomp : ∀ c : Fin 3 × Fin 3 × Fin 3, ContDiff ℝ j (comp α t F c) ∧
      (1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (comp α t F c) x‖ ≤ C0 * (Lk + Dk) * g * (A + B) := by
    intro c
    obtain ⟨i, p, q⟩ := c
    have hsc := h2 α hα0 i p q t ht0
    have hKs : ContDiff ℝ ∞ (projDivKernel α t i p q) := (h1 α hα0 i p q).1 t ht0
    have hks : ContDiff ℝ ∞ (fun y => (projDivKernel α t i p q y).re) :=
      Complex.reCLM.contDiff.comp hKs
    have hki : Integrable (fun y => (projDivKernel α t i p q y).re) := hsc.2.2.1.re
    have hLc : (∫ y, ‖projDivKernel α 1 i p q y‖) ≤ Lk := by
      have := Finset.single_le_sum (f := fun c : Fin 3 × Fin 3 × Fin 3 =>
        ∫ x, ‖projDivKernel α 1 c.1 c.2.1 c.2.2 x‖)
        (fun c _ => integral_nonneg fun x => norm_nonneg _) (Finset.mem_univ (i, p, q))
      exact this
    have hkL : (∫ y, ‖(projDivKernel α t i p q y).re‖) ≤ g * Lk := by
      calc (∫ y, ‖(projDivKernel α t i p q y).re‖) ≤ ∫ y, ‖projDivKernel α t i p q y‖ :=
            integral_mono hki.norm hsc.2.2.1.norm
              (fun y => by simpa using Complex.abs_re_le_norm (projDivKernel α t i p q y))
        _ = g * ∫ y, ‖projDivKernel α 1 i p q y‖ := hsc.2.2.2.1
        _ ≤ g * Lk := mul_le_mul_of_nonneg_left hLc (by linarith)
    have hkAll : ∀ n : ℕ, ∀ y : Space, y ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun y => (projDivKernel α t i p q y).re) y‖ ≤
          |Cd (i, p, q) n| * ‖y‖ ^ (-(4 + n : ℝ)) := by
      intro n y hy
      have e1 : ‖iteratedFDeriv ℝ n (fun y => (projDivKernel α t i p q y).re) y‖ ≤
          ‖iteratedFDeriv ℝ n (projDivKernel α t i p q) y‖ := by
        have := Complex.reCLM.norm_iteratedFDeriv_comp_left (f := projDivKernel α t i p q)
          (x := y) (N := ∞) (n := n) hKs.contDiffAt (by exact_mod_cast le_top)
        rw [Complex.reCLM_norm, one_mul] at this
        exact this
      have e2 := hCd (i, p, q) n t ht0 y
      have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
      have e3 : (t ^ (1 / (2 * α)) + ‖y‖) ^ (-(4 + n : ℝ)) ≤ ‖y‖ ^ (-(4 + n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hy0
          (by have : 0 < t ^ (1 / (2 * α)) := by positivity
              linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                            linarith)
      have e4 : 0 ≤ (t ^ (1 / (2 * α)) + ‖y‖) ^ (-(4 + n : ℝ)) := by positivity
      calc _ ≤ ‖iteratedFDeriv ℝ n (projDivKernel α t i p q) y‖ := e1
        _ ≤ Cd (i, p, q) n * (t ^ (1 / (2 * α)) + ‖y‖) ^ (-(4 + n : ℝ)) := e2
        _ ≤ |Cd (i, p, q) n| * (t ^ (1 / (2 * α)) + ‖y‖) ^ (-(4 + n : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) e4
        _ ≤ |Cd (i, p, q) n| * ‖y‖ ^ (-(4 + n : ℝ)) :=
            mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
    have hkD : ∀ n ≤ j, ∀ y : Space, y ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun y => (projDivKernel α t i p q y).re) y‖ ≤
          Dk * ‖y‖ ^ (-(4 + n : ℝ)) := by
      intro n hn y hy
      have h5 : |Cd (i, p, q) n| ≤ Dk := by
        have a1 : |Cd (i, p, q) n| ≤ ∑ m ∈ Finset.range (j + 1), |Cd (i, p, q) m| :=
          Finset.single_le_sum (f := fun m => |Cd (i, p, q) m|) (fun m _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
        have a2 := Finset.single_le_sum (f := fun c : Fin 3 × Fin 3 × Fin 3 =>
          ∑ m ∈ Finset.range (j + 1), |Cd c m|)
          (fun c _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ (i, p, q))
        exact a1.trans a2
      exact (hkAll n y hy).trans (mul_le_mul_of_nonneg_right h5 (by positivity))
    have hf : ContDiff ℝ j (fun z => F z p q) := contDiff_pi.1 (contDiff_pi.1 hF p) q
    set P : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) q).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) p) with hP
    have hPn : ‖P‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      exact (norm_le_pi_norm (v p) q).trans (norm_le_pi_norm v p)
    have hfA : ∀ y, (1 + ‖y‖) ^ b * ‖iteratedFDeriv ℝ j (fun z => F z p q) y‖ ≤ A := by
      intro y
      have e : ‖iteratedFDeriv ℝ j (P ∘ F) y‖ ≤ ‖P‖ * ‖iteratedFDeriv ℝ j F y‖ :=
        P.norm_iteratedFDeriv_comp_left (N := j) hF.contDiffAt le_rfl
      have e' : ‖iteratedFDeriv ℝ j (fun z => F z p q) y‖ ≤ ‖iteratedFDeriv ℝ j F y‖ := by
        refine le_trans (le_of_eq ?_) (e.trans (mul_le_of_le_one_left (norm_nonneg _) hPn))
        rfl
      exact (mul_le_mul_of_nonneg_left e' (by positivity)).trans (hA y)
    have hfB : ∀ y, (1 + ‖y‖) ^ β * ‖F y p q‖ ≤ B := by
      intro y
      have e : ‖F y p q‖ ≤ ‖F y‖ := (norm_le_pi_norm (F y p) q).trans (norm_le_pi_norm (F y) p)
      exact (mul_le_mul_of_nonneg_left e (by positivity)).trans (hB y)
    obtain ⟨hcd, hbd⟩ := hC0 (fun y => (projDivKernel α t i p q y).re) Dk (g * Lk) hks hki hkL hkD
      (fun n => ⟨|Cd (i, p, q) n|, hkAll n⟩) (fun z => F z p q) A B hf hfA hfB
    refine ⟨hcd, (hbd x).trans ?_⟩
    have : g * Lk * A + Dk * B ≤ (Lk + Dk) * g * (A + B) := by
      have h6 : Dk * B ≤ g * Dk * B := by
        have := mul_le_mul_of_nonneg_right hg1 (mul_nonneg hDk0 hB0)
        linarith
      nlinarith [mul_nonneg (mul_nonneg hLk0 (by linarith : (0:ℝ) ≤ g)) hB0,
        mul_nonneg (mul_nonneg hDk0 (by linarith : (0:ℝ) ≤ g)) hA0]
    calc C0 * (g * Lk * A + Dk * B) ≤ C0 * ((Lk + Dk) * g * (A + B)) :=
          mul_le_mul_of_nonneg_left this hC00
      _ = C0 * (Lk + Dk) * g * (A + B) := by ring
  rw [heatDivConv_eq]
  have hcd : ∀ c ∈ (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3)),
      ContDiffAt ℝ j (fun x => unitMap c.1 (comp α t F c x)) x :=
    fun c _ => ((unitMap c.1).contDiff.comp (hcomp c).1).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hcd]
  have hterm : ∀ c : Fin 3 × Fin 3 × Fin 3,
      (1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (fun x => unitMap c.1 (comp α t F c x)) x‖ ≤
        M * (C0 * (Lk + Dk) * g * (A + B)) := by
    intro c
    have e : ‖iteratedFDeriv ℝ j (unitMap c.1 ∘ comp α t F c) x‖ ≤
        ‖unitMap c.1‖ * ‖iteratedFDeriv ℝ j (comp α t F c) x‖ :=
      (unitMap c.1).norm_iteratedFDeriv_comp_left (N := j) (hcomp c).1.contDiffAt le_rfl
    have hMc : ‖unitMap c.1‖ ≤ M :=
      Finset.single_le_sum (f := fun i => ‖unitMap i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ c.1)
    have hT0 : 0 ≤ C0 * (Lk + Dk) * g * (A + B) := by
      have : (0 : ℝ) ≤ g := by linarith
      positivity
    calc (1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (fun x => unitMap c.1 (comp α t F c x)) x‖
        ≤ (1 + ‖x‖) ^ b * (‖unitMap c.1‖ * ‖iteratedFDeriv ℝ j (comp α t F c) x‖) :=
          mul_le_mul_of_nonneg_left e (by positivity)
      _ = ‖unitMap c.1‖ * ((1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (comp α t F c) x‖) := by ring
      _ ≤ M * (C0 * (Lk + Dk) * g * (A + B)) :=
          mul_le_mul hMc (hcomp c).2 (by positivity) hM0
  calc (1 + ‖x‖) ^ b * ‖∑ c : Fin 3 × Fin 3 × Fin 3,
        iteratedFDeriv ℝ j (fun x => unitMap c.1 (comp α t F c x)) x‖
      ≤ (1 + ‖x‖) ^ b * ∑ c : Fin 3 × Fin 3 × Fin 3,
        ‖iteratedFDeriv ℝ j (fun x => unitMap c.1 (comp α t F c x)) x‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ c : Fin 3 × Fin 3 × Fin 3, (1 + ‖x‖) ^ b *
        ‖iteratedFDeriv ℝ j (fun x => unitMap c.1 (comp α t F c x)) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _c : Fin 3 × Fin 3 × Fin 3, M * (C0 * (Lk + Dk) * g * (A + B)) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = 27 * M * (C0 * (Lk + Dk)) * g * (A + B) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end Breakdown.FracCert

import Breakdown.FracCert.StKernel
import Breakdown.Frac.OpIntegrable

open scoped ContDiff
open MeasureTheory Real Metric

noncomputable section

namespace Breakdown.FracInternal.KernelDyadicPieceFar

open Breakdown.FracCert


theorem weight_shift {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 + b ≤ 2 * (1 + a)) :
    (1 + a) ^ (-4 : ℝ) ≤ 16 * (1 + b) ^ (-4 : ℝ) := by
  have h1 : (1 + b) ^ (4 : ℝ) ≤ 16 * (1 + a) ^ (4 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h (by norm_num)
  have hpa : 0 < (1 + a) ^ (4 : ℝ) := by positivity
  have hpb : 0 < (1 + b) ^ (4 : ℝ) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  rw [← div_eq_mul_inv, inv_le_comm₀ hpa (by positivity), inv_div]
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem conv_iteratedFDeriv {k f : Space → ℂ} (hk : ContDiff ℝ ∞ k)
    (hkb : ∀ j : ℕ, ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j k y‖ ≤ A * (1 + ‖y‖) ^ (-4 : ℝ))
    (hfc : Continuous f) {Cf : ℝ} (hfb : ∀ y, ‖f y‖ ≤ Cf) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => ∫ w, f w • k (x - w)) =
      fun x => ∫ w, f w • iteratedFDeriv ℝ n k (x - w) := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  have hmeas : ∀ (j : ℕ) (x : Space), AEStronglyMeasurable
      (fun w => f w • iteratedFDeriv ℝ j k (x - w)) volume := fun j x =>
    (hfc.smul ((hk.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hintj : ∀ (j : ℕ) (x : Space), Integrable (fun w => f w • iteratedFDeriv ℝ j k (x - w)) := by
    intro j x
    obtain ⟨A, hA⟩ := hkb j
    refine Integrable.mono' ((hw.comp_sub_left x).const_mul (Cf * A)) (hmeas j x) ?_
    refine Filter.Eventually.of_forall (fun w => ?_)
    refine (norm_smul_le _ _).trans ?_
    have h0 : 0 ≤ ‖f w‖ := norm_nonneg _
    have hA0 : 0 ≤ A * (1 + ‖x - w‖) ^ (-4 : ℝ) := (norm_nonneg _).trans (hA _)
    calc ‖f w‖ * ‖iteratedFDeriv ℝ j k (x - w)‖ ≤ Cf * (A * (1 + ‖x - w‖) ^ (-4 : ℝ)) :=
          mul_le_mul (hfb w) (hA _) (norm_nonneg _) (h0.trans (hfb w))
      _ = Cf * A * (1 + ‖x - w‖) ^ (-(4 : ℝ)) := by ring_nf
  induction n with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    have : (fun w => f w • iteratedFDeriv ℝ 0 k (x - w)) =
        fun w => (continuousMultilinearCurryFin0 ℝ Space ℂ).symm (f w • k (x - w)) := by
      funext w; ext m; simp
    rw [this, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ Space ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n ih =>
    obtain ⟨A, hA⟩ := hkb (n + 1)
    have hd : ∀ x, HasFDerivAt (fun x => ∫ w, f w • iteratedFDeriv ℝ n k (x - w))
        (∫ w, f w • fderiv ℝ (iteratedFDeriv ℝ n k) (x - w)) x := by
      intro x₀
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
        (F' := fun x w => f w • fderiv ℝ (iteratedFDeriv ℝ n k) (x - w))
        (bound := fun w => Cf * A * 16 * (1 + ‖x₀ - w‖) ^ (-(4 : ℝ))) (ball_mem_nhds x₀ one_pos)
        (Filter.Eventually.of_forall (fun x => hmeas n x)) (hintj n x₀) ?_ ?_
        ((hw.comp_sub_left x₀).const_mul _) ?_
      · have hc : Continuous (fderiv ℝ (iteratedFDeriv ℝ n k)) := by
          rw [fderiv_iteratedFDeriv]
          exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) ℂ).continuous.comp
            (hk.continuous_iteratedFDeriv (by exact_mod_cast le_top))
        have : SecondCountableTopologyEither Space (Space →L[ℝ] Space [×n]→L[ℝ] ℂ) :=
          ⟨Or.inl inferInstance⟩
        exact (hfc.smul (hc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun w x hx => ?_)
        refine (norm_smul_le _ _).trans ?_
        rw [norm_fderiv_iteratedFDeriv]
        have hx' : ‖x₀ - x‖ < 1 := by rw [← dist_eq_norm, dist_comm]; exact hx
        have hsh : (1 + ‖x - w‖) ^ (-4 : ℝ) ≤ 16 * (1 + ‖x₀ - w‖) ^ (-4 : ℝ) := by
          refine weight_shift (norm_nonneg _) (norm_nonneg _) ?_
          have := norm_sub_le_norm_sub_add_norm_sub x₀ x w
          have := norm_nonneg (x - w)
          linarith
        have h0 : 0 ≤ ‖f w‖ := norm_nonneg _
        have hA0 : 0 ≤ A := by
          have := (norm_nonneg _).trans (hA 0)
          simpa using this
        calc ‖f w‖ * ‖iteratedFDeriv ℝ (n + 1) k (x - w)‖
            ≤ Cf * (A * (16 * (1 + ‖x₀ - w‖) ^ (-4 : ℝ))) :=
              mul_le_mul (hfb w) ((hA _).trans (mul_le_mul_of_nonneg_left hsh hA0))
                (norm_nonneg _) (h0.trans (hfb w))
          _ = Cf * A * 16 * (1 + ‖x₀ - w‖) ^ (-(4 : ℝ)) := by ring_nf
      · refine Filter.Eventually.of_forall (fun w x _ => ?_)
        have hdk : HasFDerivAt (iteratedFDeriv ℝ n k) (fderiv ℝ (iteratedFDeriv ℝ n k) (x - w)) (x - w) :=
          ((hk.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) _).hasFDerivAt
        have h2 := (hdk.comp x ((hasFDerivAt_id x).sub_const w)).const_smul (f w)
        simp only [ContinuousLinearMap.comp_id] at h2
        exact h2
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd x).fderiv]
    refine (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm).trans ?_
    congr 1


theorem rpow_neg_four_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : b ≤ c * a) :
    a ^ (-4 : ℝ) ≤ c ^ (4 : ℝ) * b ^ (-4 : ℝ) := by
  have h1 : b ^ (4 : ℝ) ≤ c ^ (4 : ℝ) * a ^ (4 : ℝ) := by
    rw [← Real.mul_rpow hc.le ha.le]
    exact Real.rpow_le_rpow hb.le h (by norm_num)
  have hpa : 0 < a ^ (4 : ℝ) := by positivity
  have hpb : 0 < b ^ (4 : ℝ) := by positivity
  have hpc : 0 < c ^ (4 : ℝ) := by positivity
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, ← div_eq_mul_inv, inv_le_comm₀ hpa (by positivity),
    inv_div, div_le_iff₀ hpc]
  linarith

theorem ring_zero_small {θ : Space → ℝ} (hθ : IsRingCutoff θ) {ξ : Space} (h : ‖ξ‖ ≤ 1 / 2) :
    θ ξ = 0 := by
  by_contra hne
  have := (hθ.2.2.1 ξ hne).1
  linarith

theorem ring_zero_large {θ : Space → ℝ} (hθ : IsRingCutoff θ) {ξ : Space} (h : 2 ≤ ‖ξ‖) :
    θ ξ = 0 := by
  by_contra hne
  have := (hθ.2.2.1 ξ hne).2
  linarith

theorem ring_symbol_contDiff {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) :
    ContDiff ℝ ∞ (fun ξ : Space => (θ ξ : ℂ) * σ ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : Space) (by norm_num : (0 : ℝ) < 1 / 2)] with η hη
    rw [mem_ball_zero_iff] at hη
    simp [ring_zero_small hθ hη.le]
  · exact ((Complex.ofRealCLM.contDiff.comp hθ.1).contDiffAt).mul
      (hσ.1.contDiffAt (isOpen_ne.mem_nhds h0))

theorem ring_symbol_hasCompactSupport {σ : Space → ℂ} {θ : Space → ℝ} (hθ : IsRingCutoff θ) :
    HasCompactSupport (fun ξ : Space => (θ ξ : ℂ) * σ ξ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) (fun ξ hξ => by
    rw [mem_closedBall_zero_iff, not_le] at hξ
    simp [ring_zero_large hθ hξ.le])

theorem ring_symbol_bound {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) (K : ℕ) :
    ∃ B : ℝ, ∀ i ≤ K, ∀ ξ, ‖iteratedFDeriv ℝ i (fun ξ : Space => (θ ξ : ℂ) * σ ξ) ξ‖ ≤ B := by
  have hb : ∀ i : ℕ, ∃ B : ℝ, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun ξ : Space => (θ ξ : ℂ) * σ ξ) ξ‖ ≤ B := fun i =>
    ((ring_symbol_hasCompactSupport hθ).iteratedFDeriv i).exists_bound_of_continuous
      ((ring_symbol_contDiff hσ hθ).continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose B hB using hb
  refine ⟨∑ i ∈ Finset.range (K + 1), |B i|, fun i hi ξ => ?_⟩
  refine ((hB i ξ).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem ring_kernel_props (h1 : PieceKernelStatement) {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ}
    (hσ : IsHomogeneousSymbol σ d) (hθ : IsRingCutoff θ) :
    ContDiff ℝ ∞ (FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ)) ∧
    ∀ j : ℕ, ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j
      (FourierTransform.fourierInv (fun ξ : Space => (θ ξ : ℂ) * σ ξ)) y‖ ≤
        A * (1 + ‖y‖) ^ (-4 : ℝ) := by
  have hsupp : ∀ ξ, (θ ξ : ℂ) * σ ξ ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 := by
    intro ξ h
    have hθ0 : θ ξ ≠ 0 := by
      intro h0
      apply h
      simp [h0]
    have := hθ.2.2.1 ξ hθ0
    constructor <;> linarith [this.1, this.2]
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨C, hC⟩ := h1 0 0
    obtain ⟨B, hB⟩ := ring_symbol_bound hσ hθ (0 + 0 + 4)
    exact (hC _ B (ring_symbol_contDiff hσ hθ) hsupp hB).1
  · obtain ⟨C, hC⟩ := h1 4 j
    obtain ⟨B, hB⟩ := ring_symbol_bound hσ hθ (4 + j + 4)
    refine ⟨C * B, fun y => ?_⟩
    have h := (hC _ B (ring_symbol_contDiff hσ hθ) hsupp hB).2 y
    have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
    have he : (1 + ‖y‖) ^ (-4 : ℝ) = ((1 + ‖y‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [he, ← div_eq_mul_inv, le_div_iff₀ hp]
    linarith [h]

theorem scaled_deriv_le {K : Space → ℂ} (hK : ContDiff ℝ ∞ K) (c : ℝ) {s : ℝ} (hs : 0 < s)
    (j : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ j (fun z => (c : ℂ) * K (s • z)) y‖ ≤
      |c| * s ^ j * ‖iteratedFDeriv ℝ j K (s • y)‖ := by
  have he : (fun z => (c : ℂ) * K (s • z)) =
      (c : ℂ) • (K ∘ (s • ContinuousLinearMap.id ℝ Space)) := by
    funext z
    simp
  have hg : ContDiff ℝ ∞ (K ∘ (s • ContinuousLinearMap.id ℝ Space)) :=
    hK.comp (ContinuousLinearMap.contDiff _)
  rw [he, iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, ContinuousLinearMap.iteratedFDeriv_comp_right _ hK _ (by exact_mod_cast le_top)]
  have hn : ‖s • ContinuousLinearMap.id ℝ Space‖ ≤ s := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg hs.le]
    exact mul_le_of_le_one_right hs.le ContinuousLinearMap.norm_id_le
  have hy : (s • ContinuousLinearMap.id ℝ Space) y = s • y := by simp
  rw [hy, Complex.norm_real, Real.norm_eq_abs]
  calc |c| * ‖(iteratedFDeriv ℝ j K (s • y)).compContinuousLinearMap
        fun _ => s • ContinuousLinearMap.id ℝ Space‖
      ≤ |c| * (‖iteratedFDeriv ℝ j K (s • y)‖ * ∏ _i : Fin j, s) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hn)) (norm_nonneg _)
    _ = |c| * s ^ j * ‖iteratedFDeriv ℝ j K (s • y)‖ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

theorem near_integral {β : ℝ} (hβ : 0 < β) (hβ3 : β < 3) : ∃ Q : ℝ, 0 ≤ Q ∧
    ∀ (s : ℝ), 0 < s → ∀ x : Space,
    Integrable (fun w : Space => (1 + ‖w‖) ^ (-β) * (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ))) ∧
    ∫ w, (1 + ‖w‖) ^ (-β) * (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ)) ≤ s ^ (β - 3) * Q := by
  have hint : (4 : ℝ) > (Module.finrank ℝ Space : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hw : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := integrable_one_add_norm hint
  have hball : IntegrableOn (fun u : Space => ‖u‖ ^ (-β)) (ball (0 : Space) 1) :=
    integrableOn_ball_norm_rpow (by linarith)
  set Q := (∫ u in ball (0 : Space) 1, ‖u‖ ^ (-β)) + ∫ v : Space, (1 + ‖v‖) ^ (-(4 : ℝ)) with hQ
  have hQ0 : 0 ≤ Q := by
    refine add_nonneg (setIntegral_nonneg measurableSet_ball (fun u _ => by positivity))
      (integral_nonneg (fun v => by positivity))
  refine ⟨Q, hQ0, fun s hs x => ?_⟩
  set g : Space → ℝ := fun w => (1 + ‖w‖) ^ (-β) * (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ)) with hg
  have hle1 : ∀ t : ℝ, 0 ≤ t → ∀ p : ℝ, p ≤ 0 → (1 + t) ^ p ≤ 1 := fun t ht p hp =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hp
  have hgm : ∀ w, g w ≤ (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ)) := by
    intro w
    have := hle1 ‖w‖ (norm_nonneg _) (-β) (by linarith)
    have h0 : 0 ≤ (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ)) := by positivity
    calc g w ≤ 1 * (1 + ‖s • (x - w)‖) ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_right this h0
      _ = _ := one_mul _
  have hgi : Integrable g := by
    refine Integrable.mono' ((hw.comp_smul hs.ne').comp_sub_left x)
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall (fun w => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hgm w
  refine ⟨hgi, ?_⟩
  have hI : ∫ u, g (s⁻¹ • u) = s ^ 3 * ∫ w, g w := by
    rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin, smul_eq_mul, inv_pow, inv_inv,
      abs_of_pos (by positivity)]
  have hgs : ∀ u, g (s⁻¹ • u) = (1 + ‖s⁻¹ • u‖) ^ (-β) * (1 + ‖s • x - u‖) ^ (-(4 : ℝ)) := by
    intro u
    simp only [hg, smul_sub, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  set h : Space → ℝ := fun u => s ^ β * ((ball (0 : Space) 1).indicator (fun u => ‖u‖ ^ (-β)) u +
    (1 + ‖s • x - u‖) ^ (-(4 : ℝ))) with hh
  have hhi : Integrable h :=
    ((hball.integrable_indicator measurableSet_ball).add (hw.comp_sub_left (s • x))).const_mul _
  have hae : ∀ᵐ u ∂(volume : Measure Space), u ≠ 0 := by
    rw [ae_iff]
    simp
  have hpt : ∀ᵐ u ∂(volume : Measure Space), g (s⁻¹ • u) ≤ h u := by
    filter_upwards [hae] with u hu
    rw [hgs u]
    have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hA : (1 + ‖s⁻¹ • u‖) ^ (-β) ≤ s ^ β * ‖u‖ ^ (-β) := by
      have hsu : ‖s⁻¹ • u‖ = s⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have hpos : 0 < ‖s⁻¹ • u‖ := by rw [hsu]; positivity
      calc (1 + ‖s⁻¹ • u‖) ^ (-β) ≤ ‖s⁻¹ • u‖ ^ (-β) :=
            Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
        _ = s ^ β * ‖u‖ ^ (-β) := by
            rw [hsu, Real.mul_rpow (by positivity) hu0.le, Real.inv_rpow hs.le, Real.rpow_neg hs.le,
              inv_inv]
    have hB0 : 0 ≤ (1 + ‖s • x - u‖) ^ (-(4 : ℝ)) := by positivity
    have hB1 : (1 + ‖s • x - u‖) ^ (-(4 : ℝ)) ≤ 1 := hle1 _ (norm_nonneg _) _ (by norm_num)
    have hsβ : 0 < s ^ β := by positivity
    simp only [hh]
    by_cases hub : u ∈ ball (0 : Space) 1
    · rw [Set.indicator_of_mem hub]
      have hr0 : 0 ≤ ‖u‖ ^ (-β) := by positivity
      calc (1 + ‖s⁻¹ • u‖) ^ (-β) * (1 + ‖s • x - u‖) ^ (-(4 : ℝ))
          ≤ (s ^ β * ‖u‖ ^ (-β)) * 1 := mul_le_mul hA hB1 hB0 (by positivity)
        _ ≤ s ^ β * (‖u‖ ^ (-β) + (1 + ‖s • x - u‖) ^ (-(4 : ℝ))) := by nlinarith
    · rw [Set.indicator_of_notMem hub]
      rw [mem_ball_zero_iff, not_lt] at hub
      have hr1 : ‖u‖ ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hub (by linarith)
      calc (1 + ‖s⁻¹ • u‖) ^ (-β) * (1 + ‖s • x - u‖) ^ (-(4 : ℝ))
          ≤ (s ^ β * 1) * (1 + ‖s • x - u‖) ^ (-(4 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hA.trans (mul_le_mul_of_nonneg_left hr1 hsβ.le)) hB0
        _ = s ^ β * (0 + (1 + ‖s • x - u‖) ^ (-(4 : ℝ))) := by ring
  have hgsi : Integrable (fun u => g (s⁻¹ • u)) := hgi.comp_smul (inv_ne_zero hs.ne')
  have hmono := integral_mono_ae hgsi hhi hpt
  have hhint : ∫ u, h u = s ^ β * Q := by
    simp only [hh]
    rw [integral_const_mul, integral_add (hball.integrable_indicator measurableSet_ball)
      (hw.comp_sub_left (s • x)), integral_indicator measurableSet_ball,
      integral_sub_left_eq_self (fun v : Space => (1 + ‖v‖) ^ (-(4 : ℝ))) volume (s • x)]
  rw [hI, hhint] at hmono
  have hs3 : 0 < s ^ 3 := by positivity
  have hpow : s ^ (β - 3) = s ^ β / s ^ 3 := by
    rw [Real.rpow_sub hs]
    norm_cast
  rw [hpow, div_mul_eq_mul_div, le_div_iff₀ hs3]
  linarith

end Breakdown.FracInternal.KernelDyadicPieceFar

namespace Breakdown.FracCert

def FarPieceBoundStatement : Prop :=
  ∀ (σ : Space → ℂ) (d β : ℝ) (θ : Space → ℝ), 0 ≤ d → 0 < β → β < 3 →
    IsHomogeneousSymbol σ d → IsRingCutoff θ →
    ∀ f : Space → ℂ, IsWeightedSmooth f β → ∀ n : ℕ, ∃ C : ℝ, ∀ (l : ℤ) (x : Space), 2 ≤ ‖x‖ →
      1 < (2 : ℝ) ^ (l : ℝ) * ‖x‖ →
      ‖iteratedFDeriv ℝ n (kernelConv (dyadicKernel σ θ d l) f) x‖ ≤
        C * ((2 : ℝ) ^ ((d - 1 - ⌈d⌉₊) * l) * ‖x‖ ^ (-(1 + β + ⌈d⌉₊ + n)))

end Breakdown.FracCert

import Breakdown.Frac.StTorusApprox
import Breakdown.Torus.Cutoff
import Breakdown.Torus.ApproxField

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracOuterBoundInternal

open Breakdown.Periodic.Cutoff.Internal

theorem nat_le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem integral_singular_le {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (f : ℝ → G)
    {K e : ℝ} (he : -1 < e) (hK : ∀ s ∈ Ioc (0 : ℝ) 1, ‖f s‖ ≤ K * s ^ e) :
    ‖∫ s in (0 : ℝ)..1, f s‖ ≤ K / (e + 1) := by
  have hint : IntervalIntegrable (fun s : ℝ => K * s ^ e) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' he).const_mul K
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one (ae_of_all _ hK) hint).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl he), Real.one_rpow,
    Real.zero_rpow (by linarith)]
  ring

theorem integral_iter_le (k : ℕ) : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × Space → G), ContDiff ℝ ∞ F → ∀ (y : Space) {K e : ℝ}, -1 < e →
    (∀ s ∈ Ioc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k (fun w => F (s, w)) y‖ ≤ K * s ^ e) →
    ‖iteratedFDeriv ℝ k (fun w => ∫ s in (0 : ℝ)..1, F (s, w)) y‖ ≤ K / (e + 1) := by
  induction k with
  | zero =>
    intro G _ _ _ F hF y K e he hK
    rw [norm_iteratedFDeriv_zero]
    exact integral_singular_le _ he (fun s hs => by simpa [norm_iteratedFDeriv_zero] using hK s hs)
  | succ k ih =>
    intro G _ _ _ F hF y K e he hK
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    have hfd : fderiv ℝ (fun w => ∫ s in (0 : ℝ)..1, F (s, w)) =
        fun w => ∫ s in (0 : ℝ)..1, partialSecond F s w :=
      funext fun w => (hasFDerivAt_integral_unit F h1 w).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    refine ih (fun z => partialSecond F z.1 z.2)
      ((contDiff_infty_iff_fderiv.1 hF).2.clm_comp contDiff_const) y he (fun s hs => ?_)
    have hsl : (fun w => partialSecond F s w) = fderiv ℝ (fun w => F (s, w)) :=
      funext fun w => ((hasFDerivAt_partialSecond F h1 s w).fderiv).symm
    show ‖iteratedFDeriv ℝ k (fun w => partialSecond F s w) y‖ ≤ _
    rw [hsl, norm_iteratedFDeriv_fderiv]
    exact hK s hs

theorem binom_sum_le3 {a b : ℕ → ℝ} {Ma Mb : ℝ} (ha : ∀ i ≤ 3, 0 ≤ a i ∧ a i ≤ Ma)
    (hb : ∀ i ≤ 3, 0 ≤ b i ∧ b i ≤ Mb) {j : ℕ} (hj : j ≤ 3) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 8 * (Ma * Mb) := by
  have p : ∀ i ≤ 3, ∀ k ≤ 3, a i * b k ≤ Ma * Mb := fun i hi k hk =>
    mul_le_mul (ha i hi).2 (hb k hk).2 (hb k hk).1 ((ha i hi).1.trans (ha i hi).2)
  have n : ∀ i ≤ 3, ∀ k ≤ 3, 0 ≤ a i * b k := fun i hi k hk => mul_nonneg (ha i hi).1 (hb k hk).1
  have hM : 0 ≤ Ma * Mb :=
    (n 0 (by norm_num) 0 (by norm_num)).trans (p 0 (by norm_num) 0 (by norm_num))
  have p00 := p 0 (by norm_num) 0 (by norm_num)
  have p01 := p 0 (by norm_num) 1 (by norm_num)
  have p10 := p 1 (by norm_num) 0 (by norm_num)
  have p02 := p 0 (by norm_num) 2 (by norm_num)
  have p11 := p 1 (by norm_num) 1 (by norm_num)
  have p20 := p 2 (by norm_num) 0 (by norm_num)
  have p03 := p 0 (by norm_num) 3 (by norm_num)
  have p12 := p 1 (by norm_num) 2 (by norm_num)
  have p21 := p 2 (by norm_num) 1 (by norm_num)
  have p30 := p 3 (by norm_num) 0 (by norm_num)
  interval_cases j <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;>
    norm_num [Nat.choose] <;> linarith

theorem shift_norm_le {x c : Space} (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun y : Space => y - c) x‖ ≤ max ‖x - c‖ 1 := by
  have hfd : fderiv ℝ (fun y : Space => y - c) = fun _ => ContinuousLinearMap.id ℝ Space := by
    funext y
    rw [fderiv_sub_const, fderiv_fun_id]
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    exact le_max_left _ _
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hfd]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
  · rw [← norm_iteratedFDeriv_fderiv, hfd, iteratedFDeriv_const_of_ne (by norm_num), Pi.zero_apply,
      norm_zero]
    exact le_max_of_le_right zero_le_one
  · rw [← norm_iteratedFDeriv_fderiv, hfd, iteratedFDeriv_const_of_ne (by norm_num), Pi.zero_apply,
      norm_zero]
    exact le_max_of_le_right zero_le_one

theorem dilate_norm_le {g : Space → Space} (hg : ContDiff ℝ ∞ g) {s : ℝ} (hs : 0 ≤ s)
    (c x : Space) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => g (c + s • (y - c))) x‖ ≤
      ‖iteratedFDeriv ℝ k g (c + s • (x - c))‖ * s ^ k := by
  obtain ⟨L, hL⟩ : ∃ L : Space →L[ℝ] Space, L = s • ContinuousLinearMap.id ℝ Space := ⟨_, rfl⟩
  have hh : ContDiff ℝ ∞ (fun z => g (z + c)) := hg.comp (contDiff_id.add contDiff_const)
  have hfun : (fun y => g (c + s • (y - c))) = fun y => ((fun z => g (z + c)) ∘ L) (y - c) := by
    funext y
    rw [hL]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      add_comm]
  have hLn : ‖L‖ ≤ s := by
    rw [hL]
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
  rw [hfun, iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hh _ (nat_le_infty k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDeriv_comp_add_right]
  have e : L (x - c) + c = c + s • (x - c) := by
    rw [hL, smul_apply, ContinuousLinearMap.id_apply, add_comm]
  rw [e]
  gcongr

theorem selfSimilar_contDiff {α a : ℝ} {U : Space → Space} (hU : ContDiff ℝ ∞ U) (T t : ℝ) :
    ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := by
  unfold fracSelfSimilar rotatingSlice pushForward
  have hR : ∀ R : Space ≃ₗᵢ[ℝ] Space, ContDiff ℝ ∞ (fun y => R (U (R.symm y))) := fun R =>
    R.contDiff.comp (hU.comp R.symm.contDiff)
  exact ((hR _).comp ((contDiff_id.sub contDiff_const).const_smul _)).const_smul _

theorem bounded_upto3 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 3, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := by
  have hb : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := fun j => by
    obtain ⟨K, hK⟩ := (hf.continuous_iteratedFDeriv (nat_le_infty j)).bounded_above_of_compact_support
      (hs.iteratedFDeriv j)
    exact ⟨max K 0, le_max_right _ _, fun x => (hK x).trans (le_max_left _ _)⟩
  obtain ⟨K0, h0, k0⟩ := hb 0
  obtain ⟨K1, h1, k1⟩ := hb 1
  obtain ⟨K2, h2, k2⟩ := hb 2
  obtain ⟨K3, h3, k3⟩ := hb 3
  refine ⟨K0 + K1 + K2 + K3, by positivity, fun j hj x => ?_⟩
  interval_cases j
  · linarith [k0 x]
  · linarith [k1 x]
  · linarith [k2 x]
  · linarith [k3 x]

theorem gradient_support : HasCompactSupport (gradientAt centralCut) := by
  refine HasCompactSupport.intro (isCompact_closedBall center (centralRadius / 2)) fun x hx => ?_
  have hx' : centralRadius / 2 ≤ dist x center := by
    simp only [Metric.mem_closedBall, not_le] at hx
    exact hx.le
  exact ApproxField.Internal.gradient_eq_zero_of_fderiv (ApproxField.Internal.fderiv_centralCut_outer hx')

theorem rpow_combine {s ρ α : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (i : ℕ) :
    s ^ (i + 1) * (s * ρ) ^ (-(2 * α - 1 + i)) = s ^ (2 - 2 * α) * ρ ^ (-(2 * α - 1 + i)) := by
  rw [Real.mul_rpow hs.le hρ.le, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hs]
  rw [show ((↑(i + 1) : ℝ) + -(2 * α - 1 + ↑i)) = 2 - 2 * α by push_cast; ring]

theorem far_le {σ μ ρ e : ℝ} (hσ : 0 < σ) (hμ : 0 ≤ μ) (hρ : σ ≤ ρ) (he : 0 ≤ e) :
    (μ + ρ) ^ (-e) ≤ σ ^ (-e) :=
  Real.rpow_le_rpow_of_nonpos hσ (by linarith) (by linarith)

theorem const_le {ρ e : ℝ} (hρ : 1 / 16 ≤ ρ) (he0 : 0 ≤ e) (he : e ≤ 5) :
    ρ ^ (-e) ≤ (1 / 16 : ℝ) ^ (-(5 : ℝ)) :=
  (Real.rpow_le_rpow_of_nonpos (by norm_num) hρ (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith))

theorem potential_bound (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hD : FracSelfSimilarDecay α)
    (a : ℝ) (U : Space → Space) (P : Space → ℝ) (hU : IsRotatingProfile α a 1 U P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ y : Space,
      1 / 16 ≤ dist y center → dist y center ≤ 1 / 8 → ∀ k ≤ 3,
        ‖iteratedFDeriv ℝ k (homotopyPotential center (fracSelfSimilar α a U T t)) y‖ ≤ K := by
  obtain ⟨C, hC⟩ := hD a U P hU
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; exact le_max_right _ _
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (1 / 16 : ℝ) ^ (-(5 : ℝ)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Real.rpow_nonneg (by norm_num) _
  have he : -1 < 2 - 2 * α := by linarith
  refine ⟨‖crossBilinear‖ * (8 * (C' * N * 1)) / (2 - 2 * α + 1), ?_, ?_⟩
  · exact div_nonneg (by positivity) (by linarith)
  intro T t hT hT1 ht0 htT y hy1 hy2 k hk
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := selfSimilar_contDiff hU.smooth T t
  have hμg : 0 ≤ (T - t) ^ (1 / (2 * α)) := Real.rpow_nonneg (by linarith) _
  have hρ : 0 < dist y center := by linarith
  have hyc : ‖y - center‖ = dist y center := (dist_eq_norm y center).symm
  rw [homotopyPotential_eq]
  refine integral_iter_le k (potentialIntegrand center (fracSelfSimilar α a U T t))
    (contDiff_potentialIntegrand hg) y he (fun s hs => ?_)
  have hs0 : 0 < s := hs.1
  have hv : ∀ i ≤ 3, 0 ≤ ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖ ∧
      ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖ ≤ 1 := fun i hi =>
    ⟨norm_nonneg _, (shift_norm_le i hi).trans (max_le (by rw [hyc]; linarith) le_rfl)⟩
  have hu : ∀ i ≤ 3, 0 ≤ s * ‖iteratedFDeriv ℝ i
      (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖ ∧
      s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖
        ≤ C' * N * s ^ (2 - 2 * α) := by
    intro i hi
    refine ⟨mul_nonneg hs0.le (norm_nonneg _), ?_⟩
    have hd1 := dilate_norm_le hg hs0.le center y i
    have hw : ‖center + s • (y - center) - center‖ = s * dist y center := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hyc]
    have hb := ((hC T t hT hT1 ht0 htT (center + s • (y - center))).1 i hi)
    rw [hw] at hb
    have hei : 0 ≤ 2 * α - 1 + (i : ℝ) := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hfar := far_le (μ := (T - t) ^ (1 / (2 * α))) (mul_pos hs0 hρ) hμg le_rfl hei
    have hb2 : ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ ≤
        C' * (s * dist y center) ^ (-(2 * α - 1 + (i : ℝ))) := by
      refine hb.trans ?_
      have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + s * dist y center) ^ (-(2 * α - 1 + (i : ℝ))) :=
        Real.rpow_nonneg (by positivity) _
      calc C * ((T - t) ^ (1 / (2 * α)) + s * dist y center) ^ (-(2 * α - 1 + (i : ℝ)))
          ≤ C' * ((T - t) ^ (1 / (2 * α)) + s * dist y center) ^ (-(2 * α - 1 + (i : ℝ))) :=
            mul_le_mul_of_nonneg_right (by rw [hC']; exact le_max_left _ _) hX
        _ ≤ C' * (s * dist y center) ^ (-(2 * α - 1 + (i : ℝ))) :=
            mul_le_mul_of_nonneg_left hfar hC'0
    have hcst := const_le (ρ := dist y center) (e := 2 * α - 1 + (i : ℝ)) hy1 hei
      (by have : (i : ℝ) ≤ 3 := by exact_mod_cast hi
          linarith)
    have hcomb := rpow_combine (α := α) hs0 hρ i
    have hsi : 0 ≤ s ^ (2 - 2 * α) := Real.rpow_nonneg hs0.le _
    calc s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖
        ≤ s * (‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ * s ^ i) :=
          mul_le_mul_of_nonneg_left hd1 hs0.le
      _ = s ^ (i + 1) * ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ := by
          ring
      _ ≤ s ^ (i + 1) * (C' * (s * dist y center) ^ (-(2 * α - 1 + (i : ℝ)))) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = C' * (s ^ (i + 1) * (s * dist y center) ^ (-(2 * α - 1 + (i : ℝ)))) := by ring
      _ = C' * (s ^ (2 - 2 * α) * dist y center ^ (-(2 * α - 1 + (i : ℝ)))) := by rw [hcomb]
      _ ≤ C' * (s ^ (2 - 2 * α) * N) := by
          rw [hN]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcst hsi) hC'0
      _ = C' * N * s ^ (2 - 2 * α) := by ring
  have hu' : ContDiff ℝ ∞ (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) :=
    hg.comp (contDiff_const.add (ContDiff.const_smul s (contDiff_id.sub contDiff_const)))
  have hv' : ContDiff ℝ ∞ (fun w : Space => w - center) := contDiff_id.sub contDiff_const
  have hB : ContDiff ℝ ∞ (fun w => crossBilinear
      (fracSelfSimilar α a U T t (center + s • (w - center))) (w - center)) :=
    contDiff_cross hu' hv'
  have hfun : (fun w => potentialIntegrand center (fracSelfSimilar α a U T t) (s, w)) =
      fun w => s • crossBilinear (fracSelfSimilar α a U T t (center + s • (w - center))) (w - center) :=
    rfl
  rw [hfun, iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (nat_le_infty k)), norm_smul,
    Real.norm_eq_abs, abs_of_pos hs0]
  have hbil := crossBilinear.norm_iteratedFDeriv_le_of_bilinear hu' hv' y (nat_le_infty k)
  have hsum := binom_sum_le3
    (a := fun i => s * ‖iteratedFDeriv ℝ i
      (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖)
    (b := fun i => ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖) hu hv hk
  have hre : s * (‖crossBilinear‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun w : Space => w - center) y‖) =
      ‖crossBilinear‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t
          (center + s • (w - center))) y‖) *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Space => w - center) y‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc s * ‖iteratedFDeriv ℝ k (fun w => crossBilinear
        (fracSelfSimilar α a U T t (center + s • (w - center))) (w - center)) y‖
      ≤ s * (‖crossBilinear‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Space => w - center) y‖) :=
        mul_le_mul_of_nonneg_left hbil hs0.le
    _ = _ := hre
    _ ≤ ‖crossBilinear‖ * (8 * (C' * N * s ^ (2 - 2 * α) * 1)) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖crossBilinear‖ * (8 * (C' * N * 1)) * s ^ (2 - 2 * α) := by ring

theorem iteratedFDeriv_eq_zero_outer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ y, centralRadius / 2 ≤ dist y center → f y = 0) (n : ℕ) {x : Space}
    (hx : centralRadius / 2 ≤ dist x center) : iteratedFDeriv ℝ n f x = 0 := by
  have hρ : centralRadius / 2 ≠ 0 := by norm_num [centralRadius]
  have hcl : IsClosed {y : Space | iteratedFDeriv ℝ n f y = 0} :=
    isClosed_eq (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)) continuous_const
  have hsub : (Metric.closedBall center (centralRadius / 2))ᶜ ⊆
      {y : Space | iteratedFDeriv ℝ n f y = 0} := by
    intro y hy
    have hy' : centralRadius / 2 < dist y center := by
      simpa [Metric.mem_closedBall, not_le] using hy
    have hev : f =ᶠ[𝓝 y] fun _ => (0 : E) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
        hy'] with w hw
      exact h0 w (le_of_lt hw)
    show iteratedFDeriv ℝ n f y = 0
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    rfl
  have hmem : x ∈ closure (Metric.closedBall center (centralRadius / 2))ᶜ := by
    rw [closure_compl, interior_closedBall center hρ]
    simpa [Metric.mem_ball, not_lt] using hx
  exact hcl.closure_subset_iff.2 hsub hmem

end FracOuterBoundInternal

open FracOuterBoundInternal Cutoff.Internal

theorem fracApproxField_bounds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hD : FracSelfSimilarDecay α)
    (hF : FracApproxFieldProperties α) (a : ℝ) (U : Space → Space) (P : Space → ℝ)
    (hU : IsRotatingProfile α a 1 U P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ y : Space,
      ‖fracApproxField α a U T t y‖ ≤ C * (T - t) ^ (-(1 - 1 / (2 * α))) ∧
      (centralRadius / 4 ≤ dist y center →
        ‖iteratedFDeriv ℝ 3 (fracApproxField α a U T t) y‖ ≤ C) := by
  obtain ⟨C, hC⟩ := hD a U P hU
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; exact le_max_right _ _
  have hCC : C ≤ C' := by rw [hC']; exact le_max_left _ _
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (1 / 16 : ℝ) ^ (-(5 : ℝ)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Real.rpow_nonneg (by norm_num) _
  obtain ⟨KA, hKA0, hKA⟩ := potential_bound α h1 h2 hD a U P hU
  obtain ⟨Kc, hKc0, hKc⟩ := bounded_upto3 ApproxField.Internal.contDiff_centralCut
    (centralBump.hasCompactSupport : HasCompactSupport centralCut)
  obtain ⟨Kd, hKd0, hKd⟩ := bounded_upto3 ApproxField.Internal.contDiff_gradient_centralCut
    gradient_support
  have hB0 : 0 ≤ ‖crossBilinear‖ := norm_nonneg _
  refine ⟨(C' + ‖crossBilinear‖ * Kd * KA) + (8 * (Kc * (C' * N)) + ‖crossBilinear‖ * (8 * (Kd * KA))),
    by positivity, ?_⟩
  intro T t hT hT1 ht0 htT y
  have hμ : 0 < T - t := by linarith
  have hμ1 : T - t ≤ 1 := by linarith
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) := selfSimilar_contDiff hU.smooth T t
  have hA : ContDiff ℝ ∞ (homotopyPotential center (fracSelfSimilar α a U T t)) := by
    rw [homotopyPotential_eq]
    exact contDiff_integral_unit_infty _ (contDiff_potentialIntegrand hg)
  have hform : fracApproxField α a U T t = fun w => centralCut w • fracSelfSimilar α a U T t w +
      crossBilinear (gradientAt centralCut w) (homotopyPotential center (fracSelfSimilar α a U T t) w) :=
    rfl
  have hμg : 0 < (T - t) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  have hgb : ∀ w : Space, 1 / 16 ≤ dist w center → ∀ j ≤ 3,
      ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) w‖ ≤ C' * N := by
    intro w hw j hj
    have hb := (hC T t hT hT1 ht0 htT w).1 j hj
    have hwc : ‖w - center‖ = dist w center := (dist_eq_norm w center).symm
    rw [hwc] at hb
    have hej : 0 ≤ 2 * α - 1 + (j : ℝ) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hfar := far_le (μ := (T - t) ^ (1 / (2 * α))) (σ := dist w center) (by linarith) hμg.le
      le_rfl hej
    have hcst := const_le (ρ := dist w center) (e := 2 * α - 1 + (j : ℝ)) hw hej
      (by have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
          linarith)
    have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    calc ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) w‖
        ≤ C * ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) := hb
      _ ≤ C' * ((T - t) ^ (1 / (2 * α)) + dist w center) ^ (-(2 * α - 1 + (j : ℝ))) :=
          mul_le_mul_of_nonneg_right hCC hX
      _ ≤ C' * N := by
          rw [hN]
          exact mul_le_mul_of_nonneg_left (hfar.trans hcst) hC'0
  have hE1 : 1 ≤ (T - t) ^ (-(1 - 1 / (2 * α))) := by
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hμ hμ1 ?_
    have : 1 / (2 * α) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hs1 : ContDiff ℝ ∞ (fun w => centralCut w • fracSelfSimilar α a U T t w) :=
    ApproxField.Internal.contDiff_centralCut.smul hg
  have hs2 : ContDiff ℝ ∞ (fun w => crossBilinear (gradientAt centralCut w)
      (homotopyPotential center (fracSelfSimilar α a U T t) w)) :=
    (crossBilinear.contDiff.comp ApproxField.Internal.contDiff_gradient_centralCut).clm_apply hA
  refine ⟨?_, fun hy => ?_⟩
  · rw [hform]
    show ‖centralCut y • fracSelfSimilar α a U T t y +
      crossBilinear (gradientAt centralCut y) (homotopyPotential center (fracSelfSimilar α a U T t) y)‖ ≤ _
    have hχ : ‖centralCut y‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      have h0 : 0 ≤ centralCut y := centralBump.nonneg' y
      have h1' : centralCut y ≤ 1 := centralBump.le_one
      constructor <;> linarith
    have hgy : ‖fracSelfSimilar α a U T t y‖ ≤ C' * (T - t) ^ (-(1 - 1 / (2 * α))) := by
      have hb := (hC T t hT hT1 ht0 htT y).1 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at hb
      have hle : ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) ≤
          ((T - t) ^ (1 / (2 * α))) ^ (-(2 * α - 1)) :=
        Real.rpow_le_rpow_of_nonpos hμg (le_add_of_nonneg_right (norm_nonneg _)) (by linarith)
      have heq : ((T - t) ^ (1 / (2 * α))) ^ (-(2 * α - 1)) = (T - t) ^ (-(1 - 1 / (2 * α))) := by
        rw [← Real.rpow_mul hμ.le]
        congr 1
        field_simp
      have hX : 0 ≤ ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) :=
        Real.rpow_nonneg (by positivity) _
      calc ‖fracSelfSimilar α a U T t y‖ ≤ C * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) := hb
        _ ≤ C' * ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) :=
            mul_le_mul_of_nonneg_right hCC hX
        _ ≤ C' * (T - t) ^ (-(1 - 1 / (2 * α))) := by
            rw [← heq]
            exact mul_le_mul_of_nonneg_left hle hC'0
    have hpart1 : ‖centralCut y • fracSelfSimilar α a U T t y‖ ≤ C' * (T - t) ^ (-(1 - 1 / (2 * α))) := by
      rw [norm_smul]
      calc ‖centralCut y‖ * ‖fracSelfSimilar α a U T t y‖ ≤ 1 * ‖fracSelfSimilar α a U T t y‖ :=
            mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
        _ ≤ C' * (T - t) ^ (-(1 - 1 / (2 * α))) := by rw [one_mul]; exact hgy
    have hpart2 : ‖crossBilinear (gradientAt centralCut y)
        (homotopyPotential center (fracSelfSimilar α a U T t) y)‖ ≤ ‖crossBilinear‖ * Kd * KA := by
      by_cases hsh : 1 / 16 ≤ dist y center ∧ dist y center ≤ 1 / 8
      · have hd : ‖gradientAt centralCut y‖ ≤ Kd := by
          have := hKd 0 (by norm_num) y
          rwa [norm_iteratedFDeriv_zero] at this
        have hp : ‖homotopyPotential center (fracSelfSimilar α a U T t) y‖ ≤ KA := by
          have := hKA T t hT hT1 ht0 htT y hsh.1 hsh.2 0 (by norm_num)
          rwa [norm_iteratedFDeriv_zero] at this
        refine (crossBilinear.le_opNorm₂ _ _).trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd hB0) hp (norm_nonneg _) (by positivity)
      · have hz : gradientAt centralCut y = 0 := by
          rcases not_and_or.1 hsh with h | h
          · exact ApproxField.Internal.gradient_eq_zero_of_fderiv
              (ApproxField.Internal.fderiv_centralCut_inner (by norm_num [centralRadius]; linarith))
          · exact ApproxField.Internal.gradient_eq_zero_of_fderiv
              (ApproxField.Internal.fderiv_centralCut_outer (by norm_num [centralRadius]; linarith))
        rw [hz, map_zero, zero_apply, norm_zero]
        positivity
    have hK1 : ‖crossBilinear‖ * Kd * KA ≤ ‖crossBilinear‖ * Kd * KA * (T - t) ^ (-(1 - 1 / (2 * α))) :=
      le_mul_of_one_le_right (by positivity) hE1
    have hK2 : 0 ≤ (8 * (Kc * (C' * N)) + ‖crossBilinear‖ * (8 * (Kd * KA))) *
        (T - t) ^ (-(1 - 1 / (2 * α))) := by positivity
    calc _ ≤ ‖centralCut y • fracSelfSimilar α a U T t y‖ + ‖crossBilinear (gradientAt centralCut y)
          (homotopyPotential center (fracSelfSimilar α a U T t) y)‖ := norm_add_le _ _
      _ ≤ C' * (T - t) ^ (-(1 - 1 / (2 * α))) + ‖crossBilinear‖ * Kd * KA := add_le_add hpart1 hpart2
      _ ≤ _ := by nlinarith
  · have hy1 : 1 / 16 ≤ dist y center := by norm_num [centralRadius] at hy; linarith
    rcases le_total (dist y center) (1 / 8) with hle | hge
    · rw [hform]
      show ‖iteratedFDeriv ℝ 3 ((fun w => centralCut w • fracSelfSimilar α a U T t w) +
        (fun w => crossBilinear (gradientAt centralCut w)
          (homotopyPotential center (fracSelfSimilar α a U T t) w))) y‖ ≤ _
      rw [iteratedFDeriv_add_apply (hs1.contDiffAt.of_le (nat_le_infty 3))
        (hs2.contDiffAt.of_le (nat_le_infty 3))]
      have hsm := norm_iteratedFDeriv_smul_le ApproxField.Internal.contDiff_centralCut hg y
        (nat_le_infty 3)
      have hsum1 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i centralCut y‖)
        (b := fun i => ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) y‖)
        (fun i hi => ⟨norm_nonneg _, hKc i hi y⟩) (fun i hi => ⟨norm_nonneg _, hgb y hy1 i hi⟩)
        (le_refl 3)
      have hbl := crossBilinear.norm_iteratedFDeriv_le_of_bilinear
        ApproxField.Internal.contDiff_gradient_centralCut hA y (nat_le_infty 3)
      have hsum2 := binom_sum_le3 (a := fun i => ‖iteratedFDeriv ℝ i (gradientAt centralCut) y‖)
        (b := fun i => ‖iteratedFDeriv ℝ i (homotopyPotential center (fracSelfSimilar α a U T t)) y‖)
        (fun i hi => ⟨norm_nonneg _, hKd i hi y⟩)
        (fun i hi => ⟨norm_nonneg _, hKA T t hT hT1 ht0 htT y hy1 hle i hi⟩) (le_refl 3)
      have hb2 := mul_le_mul_of_nonneg_left hsum2 hB0
      refine (norm_add_le _ _).trans ?_
      have : 0 ≤ C' + ‖crossBilinear‖ * Kd * KA := by positivity
      linarith
    · rw [iteratedFDeriv_eq_zero_outer (hform ▸ (hs1.add hs2)) (fun w hw => ((hF a U P hU T hT).2.2 t htT w).2.1 hw |>.1)
        3 (by norm_num [centralRadius]; linarith), norm_zero]
      positivity

end Breakdown.Periodic

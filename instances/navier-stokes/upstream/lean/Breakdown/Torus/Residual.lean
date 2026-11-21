import Breakdown.Torus.StatementsApprox
import Breakdown.Torus.Cutoff

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Residual.Internal

private theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem norm_four_le (a b c d : Space) : ‖a + b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have e1 := norm_add_le (a + b - c) d
  have e2 := norm_sub_le (a + b) c
  have e3 := norm_add_le a b
  linarith

private theorem norm_sumSecondPartialsAt_le (f : Space → Space) (x : Space) :
    ‖sumSecondPartialsAt f x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 f x‖ := by
  unfold sumSecondPartialsAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖iteratedFDeriv ℝ 2 f x ![unitVector i, unitVector i]‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
    intro i
    refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans (le_of_eq ?_)
    simp [Fin.prod_univ_two, norm_unitVector]
  calc ∑ i : Fin 3, ‖iteratedFDeriv ℝ 2 f x ![unitVector i, unitVector i]‖
      ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 2 f x‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖iteratedFDeriv ℝ 2 f x‖ := by simp

private theorem norm_gradientAt_le (p : Space → ℝ) (x : Space) :
    ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ p x‖ := by
    intro i
    rw [norm_smul, norm_unitVector, mul_one]
    exact ((fderiv ℝ p x).le_opNorm _).trans (le_of_eq (by rw [norm_unitVector, mul_one]))
  calc ∑ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖
      ≤ ∑ _i : Fin 3, ‖fderiv ℝ p x‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ p x‖ := by simp


private theorem nat_le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

private theorem profile_slice {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) (s : ℝ) : ContDiff ℝ ∞ (W s) :=
  hW.smooth.comp (contDiff_const.prodMk contDiff_id)

private theorem profile_const_nonneg {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) : 0 ≤ C := by
  have h := hW.decay 0 0 0 (by norm_num)
  rw [norm_zero, add_zero, one_pow, div_one] at h
  exact (norm_nonneg _).trans h

private theorem selfSimilar_iteratedFDeriv_sharp {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) (x : Space) {j : ℕ}
    (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖ ≤ ((T - t) ^ (-(1 / 2 : ℝ))) ^ (j + 1) *
      (C / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist x center) ^ (j + 1)) := by
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (T - t) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ rpow_pos_of_pos (by linarith) _
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = similarityTime T t := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Space →L[ℝ] Space, L = l • ContinuousLinearMap.id ℝ Space := ⟨_, rfl⟩
  have hWs := profile_slice hW s
  have hfun : selfSimilar W T t = fun y => l • (W s ∘ L) (y - center) := by
    funext y
    simp only [selfSimilar, hl, hs, hL, Function.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply]
  have hcomp : ContDiff ℝ ∞ (W s ∘ L) := hWs.comp L.contDiff
  have hdist : ‖L (x - center)‖ = l * dist x center := by
    rw [hL, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, dist_eq_norm]
  have hLn : ‖L‖ ≤ l := by
    rw [hL]
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos hl0]
    exact mul_le_of_le_one_right hl0.le ContinuousLinearMap.norm_id_le
  have hD := hW.decay s (L (x - center)) j hj
  rw [hdist] at hD
  have h1 : ‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖ ≤
      l * (‖iteratedFDeriv ℝ j (W s) (L (x - center))‖ * l ^ j) := by
    rw [hfun, iteratedFDeriv_const_smul_apply' (f := fun y => (W s ∘ L) (y - center))
      ((hcomp.comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le (nat_le_infty j)),
      norm_smul, Real.norm_eq_abs, abs_of_pos hl0, iteratedFDeriv_comp_sub,
      L.iteratedFDeriv_comp_right hWs _ (nat_le_infty j)]
    gcongr
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  rw [← hl]
  calc ‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖
      ≤ l * (‖iteratedFDeriv ℝ j (W s) (L (x - center))‖ * l ^ j) := h1
    _ ≤ l * (C / (1 + l * dist x center) ^ (j + 1) * l ^ j) := by gcongr
    _ = l ^ (j + 1) * (C / (1 + l * dist x center) ^ (j + 1)) := by ring

private theorem weighted_le {l ρ C D : ℝ} (hl : 0 < l) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (n : ℕ)
    (hD : D ≤ l ^ n * (C / (1 + l * ρ) ^ n)) (_hD0 : 0 ≤ D) : D * ρ ^ n ≤ C := by
  have hA : 0 < (1 + l * ρ) ^ n := by positivity
  have hle : (l * ρ) ^ n ≤ (1 + l * ρ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) _
  calc D * ρ ^ n ≤ l ^ n * (C / (1 + l * ρ) ^ n) * ρ ^ n := by gcongr
    _ = C * ((l * ρ) ^ n / (1 + l * ρ) ^ n) := by ring
    _ ≤ C * 1 := by gcongr; exact div_le_one_of_le₀ hle hA.le
    _ = C := mul_one C

private theorem selfSimilar_iteratedFDeriv_bound {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) (x : Space) {j : ℕ}
    (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖ * dist x center ^ (j + 1) ≤ C := by
  have h := selfSimilar_iteratedFDeriv_sharp hW htT x hj
  exact weighted_le (l := (T - t) ^ (-(1 / 2 : ℝ))) (rpow_pos_of_pos (by linarith) _) dist_nonneg (profile_const_nonneg hW) _ h
    (norm_nonneg _)

private theorem bounded_iteratedFDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := by
  obtain ⟨K, hK⟩ := (hf.continuous_iteratedFDeriv (nat_le_infty j)).bounded_above_of_compact_support
    (hs.iteratedFDeriv j)
  exact ⟨max K 0, le_max_right _ _, fun x => (hK x).trans (le_max_left _ _)⟩

private theorem centralCut_contDiff : ContDiff ℝ ∞ centralCut := centralBump.contDiff

private theorem centralCut_support : HasCompactSupport centralCut := centralBump.hasCompactSupport

private theorem gradient_contDiff {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (gradientAt χ) := by
  unfold gradientAt
  refine ContDiff.sum fun i _ => ?_
  exact ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).smul contDiff_const

private theorem gradient_support {χ : Space → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (gradientAt χ) := by
  refine (hs.fderiv (𝕜 := ℝ)).mono ?_
  intro x hx
  by_contra h
  apply hx
  simp only [Function.mem_support, not_not] at h
  simp [gradientAt, h]


private theorem slice_of_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Space → E} {T t : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Iio T ×ˢ univ)) (htT : t < T) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.1 ((hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => mk_mem_prod htT (mem_univ _))) : ContDiffOn ℝ ∞ (fun x : Space => f t x) univ)

private theorem selfSimilarPressure_fderiv_sharp {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) (x : Space) :
    ‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ ((T - t) ^ (-(1 / 2 : ℝ))) ^ 3 *
      (C / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist x center) ^ 3) := by
  have hT0 : 0 < T - t := by linarith
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (T - t) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ rpow_pos_of_pos hT0 _
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = similarityTime T t := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Space →L[ℝ] Space, L = l • ContinuousLinearMap.id ℝ Space := ⟨_, rfl⟩
  have hqs : ContDiff ℝ ∞ (q s) := hW.smooth_pressure.comp (contDiff_const.prodMk contDiff_id)
  have hl2 : l ^ 2 = (T - t)⁻¹ := by
    rw [hl, rpow_neg hT0.le, inv_pow, ← rpow_natCast, ← rpow_mul hT0.le]
    norm_num
  have hfun : selfSimilarPressure q T t = fun y => l ^ 2 * q s (L (y - center)) := by
    funext y
    rw [hl2, hL, hs]
    simp only [selfSimilarPressure, smul_apply, ContinuousLinearMap.id_apply, hl]
  have hinner : HasFDerivAt (fun y => L (y - center)) L x := by
    simpa only [map_sub] using L.hasFDerivAt.sub_const (L center)
  have hq : HasFDerivAt (q s) (fderiv ℝ (q s) (L (x - center))) (L (x - center)) :=
    ((hqs.differentiable (by simp)) (L (x - center))).hasFDerivAt
  have htot : fderiv ℝ (fun y => l ^ 2 * q s (L (y - center))) x =
      l ^ 2 • (fderiv ℝ (q s) (L (x - center))).comp L :=
    ((hq.comp x hinner).const_mul (l ^ 2)).fderiv
  have hdist : ‖L (x - center)‖ = l * dist x center := by
    rw [hL, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, dist_eq_norm]
  have hLn : ‖L‖ ≤ l := by
    rw [hL]
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos hl0]
    exact mul_le_of_le_one_right hl0.le ContinuousLinearMap.norm_id_le
  have hD := hW.decay_pressure s (L (x - center))
  rw [hdist] at hD
  have hA : ‖l ^ 2 • (fderiv ℝ (q s) (L (x - center))).comp L‖ ≤
      l ^ 2 * (‖fderiv ℝ (q s) (L (x - center))‖ * l) := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
  rw [hfun, htot, ← hl]
  calc ‖l ^ 2 • (fderiv ℝ (q s) (L (x - center))).comp L‖
      ≤ l ^ 2 * (‖fderiv ℝ (q s) (L (x - center))‖ * l) := hA
    _ ≤ l ^ 2 * (C / (1 + l * dist x center) ^ 3 * l) := by gcongr
    _ = l ^ 3 * (C / (1 + l * dist x center) ^ 3) := by ring

private theorem selfSimilarPressure_fderiv_bound {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) (x : Space) :
    ‖fderiv ℝ (selfSimilarPressure q T t) x‖ * dist x center ^ 3 ≤ C := by
  have h := selfSimilarPressure_fderiv_sharp hW htT x
  exact weighted_le (l := (T - t) ^ (-(1 / 2 : ℝ))) (rpow_pos_of_pos (by linarith) _) dist_nonneg (profile_const_nonneg hW) _ h
    (norm_nonneg _)

private theorem segment_far {a b : Space} (ha : 1 / 16 ≤ ‖a‖) (hb : 1 / 16 ≤ ‖b‖)
    (hab : 0 ≤ inner ℝ a b) {z : Space} (hz : z ∈ segment ℝ (center + a) (center + b)) :
    1 / 32 ≤ dist z center := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  rw [dist_eq_norm]
  have e : center + a + θ • (center + b - (center + a)) - center = (1 - θ) • a + θ • b := by
    rw [add_sub_add_left_eq_sub, smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  have hA : (1 / 256 : ℝ) ≤ ‖a‖ ^ 2 := by nlinarith
  have hB : (1 / 256 : ℝ) ≤ ‖b‖ ^ 2 := by nlinarith
  have hsq : (1 / 32 : ℝ) ^ 2 ≤ ‖(1 - θ) • a + θ • b‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ),
      abs_of_nonneg h0]
    have hc : 0 ≤ (1 - θ) * (θ * inner ℝ a b) := mul_nonneg (by linarith) (mul_nonneg h0 hab)
    nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg (1 - θ)),
      mul_le_mul_of_nonneg_left hB (sq_nonneg θ), sq_nonneg (2 * θ - 1)]
  nlinarith [norm_nonneg ((1 - θ) • a + θ • b)]

private theorem segment_difference {p : Space → ℝ} {K : ℝ} (hp : ContDiff ℝ ∞ p)
    (hD : ∀ z, ‖fderiv ℝ p z‖ * dist z center ^ 3 ≤ K) {a b : Space} (ha : 1 / 16 ≤ ‖a‖)
    (hb : 1 / 16 ≤ ‖b‖) (hab : 0 ≤ inner ℝ a b) :
    |p (center + b) - p (center + a)| ≤ 32768 * K * ‖b - a‖ := by
  have hbound : ∀ z ∈ segment ℝ (center + a) (center + b), ‖fderiv ℝ p z‖ ≤ 32768 * K := by
    intro z hz
    have hf := segment_far ha hb hab hz
    have h3 : (1 / 32 : ℝ) ^ 3 ≤ dist z center ^ 3 := pow_le_pow_left₀ (by norm_num) hf _
    nlinarith [hD z, norm_nonneg (fderiv ℝ p z)]
  have h := (convex_segment (center + a) (center + b)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hp.differentiable (by simp)) z) hbound (left_mem_segment ℝ _ _)
    (right_mem_segment ℝ _ _)
  rwa [Real.norm_eq_abs, add_sub_add_left_eq_sub] at h

private theorem pressure_difference_bound (hS : SelfSimilarSolves) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        |selfSimilarPressure q T t x - selfSimilarPressure q T t pressureAnchor| ≤ K := by
  have hC0 := profile_const_nonneg hW
  refine ⟨32768 * C, by positivity, ?_⟩
  intro T t hT htT x hx1 hx2
  have hp : ContDiff ℝ ∞ (selfSimilarPressure q T t) :=
    slice_of_contDiffOn (hS W q C T hW hT).2.1 htT
  have hD := selfSimilarPressure_fderiv_bound hW htT
  obtain ⟨a, ha⟩ : ∃ a : Space, a = x - center := ⟨_, rfl⟩
  have hxa : x = center + a := by rw [ha]; abel
  have hna : 1 / 16 ≤ ‖a‖ ∧ ‖a‖ ≤ 1 / 8 := by
    rw [ha, ← dist_eq_norm]
    norm_num [centralRadius] at hx1 hx2
    constructor <;> linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = if 0 ≤ a 1 then 1 / 8 else -(1 / 8) := ⟨_, rfl⟩
  have hσn : |σ| = 1 / 8 := by rw [hσ]; split_ifs <;> norm_num
  have hσa : 0 ≤ σ * a 1 := by rw [hσ]; split_ifs with h <;> nlinarith
  obtain ⟨n, hn⟩ : ∃ n : Space, n = EuclideanSpace.single 1 σ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Space, b = ((3 / 8 : ℝ) * centralRadius) • unitVector 0 := ⟨_, rfl⟩
  have hanch : pressureAnchor = center + b := by rw [hb]; rfl
  have hnn : ‖n‖ = 1 / 8 := by rw [hn, PiLp.norm_single, Real.norm_eq_abs, hσn]
  have hnb : ‖b‖ = 3 / 32 := by
    rw [hb, norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
    norm_num [centralRadius]
  have han : 0 ≤ inner ℝ a n := by
    rw [hn]
    simpa [EuclideanSpace.inner_single_right] using hσa
  have hnb' : 0 ≤ inner ℝ n b := by
    rw [hn, hb]
    simp [unitVector, inner_smul_right, EuclideanSpace.inner_single_left]
  have e1 := segment_difference hp hD hna.1 (by rw [hnn]; norm_num) han
  have e2 := segment_difference hp hD (by rw [hnn]; norm_num) (by rw [hnb]; norm_num) hnb'
  have d1 : ‖n - a‖ ≤ 1 / 4 := by linarith [norm_sub_le n a, hna.2]
  have d2 : ‖b - n‖ ≤ 1 / 4 := by linarith [norm_sub_le b n]
  rw [hxa, hanch]
  calc |selfSimilarPressure q T t (center + a) - selfSimilarPressure q T t (center + b)|
      ≤ |selfSimilarPressure q T t (center + a) - selfSimilarPressure q T t (center + n)|
        + |selfSimilarPressure q T t (center + n) - selfSimilarPressure q T t (center + b)| :=
        abs_sub_le _ _ _
    _ = |selfSimilarPressure q T t (center + n) - selfSimilarPressure q T t (center + a)|
        + |selfSimilarPressure q T t (center + b) - selfSimilarPressure q T t (center + n)| := by
        rw [abs_sub_comm (selfSimilarPressure q T t (center + n))
          (selfSimilarPressure q T t (center + a)),
          abs_sub_comm (selfSimilarPressure q T t (center + b))
          (selfSimilarPressure q T t (center + n))]
    _ ≤ 32768 * C * ‖n - a‖ + 32768 * C * ‖b - n‖ := add_le_add e1 e2
    _ ≤ 32768 * C := by nlinarith

private theorem bounded_low_derivs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := by
  obtain ⟨K0, h0, k0⟩ := bounded_iteratedFDeriv hf hs 0
  obtain ⟨K1, h1, k1⟩ := bounded_iteratedFDeriv hf hs 1
  obtain ⟨K2, h2, k2⟩ := bounded_iteratedFDeriv hf hs 2
  refine ⟨K0 + K1 + K2, by positivity, fun j hj x => ?_⟩
  interval_cases j
  · linarith [k0 x]
  · linarith [k1 x]
  · linarith [k2 x]

private theorem binom_sum_le {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ i ≤ 2, 0 ≤ a i ∧ a i ≤ M)
    (hb : ∀ i ≤ 2, 0 ≤ b i ∧ b i ≤ M) {j : ℕ} (hj : j ≤ 2) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 4 * (M * M) := by
  have p : ∀ i ≤ 2, ∀ k ≤ 2, a i * b k ≤ M * M := fun i hi k hk =>
    mul_le_mul (ha i hi).2 (hb k hk).2 (hb k hk).1 ((ha i hi).1.trans (ha i hi).2)
  have n : ∀ i ≤ 2, ∀ k ≤ 2, 0 ≤ a i * b k := fun i hi k hk => mul_nonneg (ha i hi).1 (hb k hk).1
  have hM : 0 ≤ M * M := (n 0 (by norm_num) 0 (by norm_num)).trans (p 0 (by norm_num) 0 (by norm_num))
  interval_cases j
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 1 (by norm_num), p 1 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 2 (by norm_num), p 1 (by norm_num) 1 (by norm_num),
      p 2 (by norm_num) 0 (by norm_num)]

private theorem selfSimilar_shell_bound {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) {x : Space}
    (hx1 : centralRadius / 4 ≤ dist x center) (hx2 : dist x center ≤ centralRadius / 2) {i : ℕ}
    (hi : i ≤ 2) : ‖iteratedFDeriv ℝ i (selfSimilar W T t) x‖ ≤ 4096 * C := by
  have hb := selfSimilar_iteratedFDeriv_bound hW htT x hi
  have hr : (1 / 16 : ℝ) ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hr' : dist x center ≤ 1 := by norm_num [centralRadius] at hx2; linarith
  have h3 : (1 / 16 : ℝ) ^ 3 ≤ dist x center ^ (i + 1) :=
    (pow_le_pow_left₀ (by norm_num) hr _).trans (pow_le_pow_of_le_one dist_nonneg hr' (by omega))
  nlinarith [norm_nonneg (iteratedFDeriv ℝ i (selfSimilar W T t) x)]

private theorem integral_value_le {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ℝ × Space → G) (x : Space) {M : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖F (s, x)‖ ≤ M) : ‖∫ s in (0 : ℝ)..1, F (s, x)‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M)
    (f := fun s => F (s, x)) (fun s hs => hM s (Ioc_subset_Icc_self
      (by rwa [uIoc_of_le zero_le_one] at hs)))
  simpa using h

private theorem integral_deriv_le {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × Space → G) (hF : ContDiff ℝ ∞ F) (x : Space) {M : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fun y => F (s, y)) x‖ ≤ M) :
    ‖fderiv ℝ (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) x‖ ≤ M := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by simp)
  rw [(Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_integral_unit F hF1 x).fderiv]
  refine integral_value_le (fun z : ℝ × Space =>
    Breakdown.Periodic.Cutoff.Internal.partialSecond F z.1 z.2) x (fun s hs => ?_)
  rw [← (Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_partialSecond F hF1 s x).fderiv]
  exact hM s hs

private theorem shift_norm_le {x c : Space} (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun y : Space => y - c) x‖ ≤ max ‖x - c‖ 1 := by
  have hfd : fderiv ℝ (fun y : Space => y - c) = fun _ => ContinuousLinearMap.id ℝ Space := by
    funext y
    rw [fderiv_sub_const, fderiv_fun_id]
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    exact le_max_left _ _
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hfd]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
  · rw [← norm_iteratedFDeriv_fderiv, hfd, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero,
      fderiv_const_apply, norm_zero]
    exact le_max_of_le_right zero_le_one

private theorem dilate_norm_le {g : Space → Space} (hg : ContDiff ℝ ∞ g) {s : ℝ} (hs : 0 ≤ s)
    (c x : Space) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => g (c + s • (y - c))) x‖ ≤
      ‖iteratedFDeriv ℝ k g (c + s • (x - c))‖ * s ^ k := by
  obtain ⟨L, hL⟩ : ∃ L : Space →L[ℝ] Space, L = s • ContinuousLinearMap.id ℝ Space := ⟨_, rfl⟩
  have hh : ContDiff ℝ ∞ (fun z => g (z + c)) := hg.comp (contDiff_id.add contDiff_const)
  have hfun : (fun y => g (c + s • (y - c))) = fun y => ((fun z => g (z + c)) ∘ L) (y - c) := by
    funext y
    rw [hL]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, add_comm]
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

private theorem potential_bound (hS : SelfSimilarSolves)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j (homotopyPotential center (selfSimilar W T t)) x‖ ≤ K := by
  have hC0 := profile_const_nonneg hW
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 4096 * C + 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  refine ⟨‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (4 * (M * M)), by positivity, ?_⟩
  intro T t hT htT x hx1 hx2 j hj
  have hg : ContDiff ℝ ∞ (selfSimilar W T t) := slice_of_contDiffOn (hS W q C T hW hT).1 htT
  have hr : (1 / 16 : ℝ) ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hr' : dist x center ≤ 1 / 8 := by norm_num [centralRadius] at hx2; linarith
  have hxc : ‖x - center‖ = dist x center := (dist_eq_norm x center).symm
  have hv : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (fun y : Space => y - center) x‖ ≤ M := fun k hk =>
    (shift_norm_le k hk).trans (max_le (by rw [hxc]; linarith) hM1)
  have hu : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i ≤ 2,
      s * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t (center + s • (y - center))) x‖ ≤ M := by
    intro s hs i hi
    have h1 := dilate_norm_le hg hs.1 center x i
    have h2 := selfSimilar_iteratedFDeriv_bound hW htT (center + s • (x - center)) hi
    have hd : dist (center + s • (x - center)) center = s * dist x center := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, hxc]
    rw [hd, mul_pow] at h2
    have h3 : (1 / 16 : ℝ) ^ 3 ≤ dist x center ^ (i + 1) :=
      (pow_le_pow_left₀ (by norm_num) hr _).trans
        (pow_le_pow_of_le_one dist_nonneg (by linarith) (by omega))
    have hsi : s * s ^ i = s ^ (i + 1) := by ring
    have hN := norm_nonneg (iteratedFDeriv ℝ i (selfSimilar W T t) (center + s • (x - center)))
    have hs0 : 0 ≤ s ^ (i + 1) := pow_nonneg hs.1 _
    have h4 : s ^ (i + 1) * ‖iteratedFDeriv ℝ i (selfSimilar W T t) (center + s • (x - center))‖
        ≤ 4096 * C := by
      nlinarith [mul_nonneg hs0 hN]
    calc s * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t (center + s • (y - center))) x‖
        ≤ s * (‖iteratedFDeriv ℝ i (selfSimilar W T t) (center + s • (x - center))‖ * s ^ i) :=
          mul_le_mul_of_nonneg_left h1 hs.1
      _ = s ^ (i + 1) * ‖iteratedFDeriv ℝ i (selfSimilar W T t) (center + s • (x - center))‖ := by
          ring
      _ ≤ M := by rw [hM]; linarith
  have hΦ := Breakdown.Periodic.Cutoff.Internal.contDiff_potentialIntegrand (x₀ := center) hg
  have hP : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (fun y =>
      Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t) (s, y)) x‖ ≤
      ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (4 * (M * M)) := by
    intro s hs k hk
    have hu' : ContDiff ℝ ∞ (fun y => selfSimilar W T t (center + s • (y - center))) :=
      hg.comp (contDiff_const.add (ContDiff.const_smul s (contDiff_id.sub contDiff_const)))
    have hv' : ContDiff ℝ ∞ (fun y : Space => y - center) := contDiff_id.sub contDiff_const
    have hB : ContDiff ℝ ∞ (fun y => Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (selfSimilar W T t (center + s • (y - center))) (y - center)) :=
      Breakdown.Periodic.Cutoff.Internal.contDiff_cross hu' hv'
    have hfun : (fun y => Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center
        (selfSimilar W T t) (s, y)) = fun y => s • Breakdown.Periodic.Cutoff.Internal.crossBilinear
          (selfSimilar W T t (center + s • (y - center))) (y - center) := rfl
    rw [hfun, iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (nat_le_infty k)), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    have hbil := Breakdown.Periodic.Cutoff.Internal.crossBilinear.norm_iteratedFDeriv_le_of_bilinear
      hu' hv' x (nat_le_infty k)
    have hsum := binom_sum_le
      (a := fun i => s * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t (center + s • (y - center))) x‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (fun y : Space => y - center) x‖)
      (fun i hi => ⟨mul_nonneg hs.1 (norm_nonneg _), hu s hs i hi⟩)
      (fun i hi => ⟨norm_nonneg _, hv i hi⟩) hk
    have hre : s * (‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t (center + s • (y - center))) x‖
          * ‖iteratedFDeriv ℝ (k - i) (fun y : Space => y - center) x‖) =
        ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (s * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t
          (center + s • (y - center))) x‖) * ‖iteratedFDeriv ℝ (k - i) (fun y : Space => y - center) x‖ := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    calc s * ‖iteratedFDeriv ℝ k (fun y => Breakdown.Periodic.Cutoff.Internal.crossBilinear
          (selfSimilar W T t (center + s • (y - center))) (y - center)) x‖
        ≤ s * (‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => selfSimilar W T t
            (center + s • (y - center))) x‖ * ‖iteratedFDeriv ℝ (k - i)
              (fun y : Space => y - center) x‖) := mul_le_mul_of_nonneg_left hbil hs.1
      _ = _ := hre
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  have hΨ := Breakdown.Periodic.Cutoff.Internal.homotopyPotential_eq (x₀ := center)
    (g := selfSimilar W T t)
  have hP1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fun y =>
      Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t) (s, y)) x‖ ≤
      ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (4 * (M * M)) := fun s hs => by
    have := hP s hs 1 (by norm_num)
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, hΨ]
    refine integral_value_le _ x (fun s hs => ?_)
    have := hP s hs 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hΨ]
    exact integral_deriv_le _ hΦ x hP1
  · have hF1 : ContDiff ℝ 1 (Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center
        (selfSimilar W T t)) := hΦ.of_le (by simp)
    have hfd : fderiv ℝ (homotopyPotential center (selfSimilar W T t)) = fun y =>
        ∫ s in (0 : ℝ)..1, Breakdown.Periodic.Cutoff.Internal.partialSecond
          (Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t)) s y := by
      funext y
      rw [hΨ]
      exact (Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_integral_unit _ hF1 y).fderiv
    have hF2 : ContDiff ℝ ∞ (fun z : ℝ × Space => Breakdown.Periodic.Cutoff.Internal.partialSecond
        (Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t)) z.1 z.2) :=
      (contDiff_infty_iff_fderiv.1 hΦ).2.clm_comp contDiff_const
    rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hfd]
    refine integral_deriv_le (fun z : ℝ × Space => Breakdown.Periodic.Cutoff.Internal.partialSecond
      (Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t)) z.1 z.2)
      hF2 x (fun s hs => ?_)
    have hsl : (fun y => Breakdown.Periodic.Cutoff.Internal.partialSecond
        (Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center (selfSimilar W T t)) s y) =
        fderiv ℝ (fun y => Breakdown.Periodic.Cutoff.Internal.potentialIntegrand center
          (selfSimilar W T t) (s, y)) := by
      funext y
      exact ((Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_partialSecond _ hF1 s y).fderiv).symm
    have := hP s hs 2 le_rfl
    rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero,
      ← hsl] at this
    exact this

private theorem centralCut_norm_le (x : Space) : ‖centralCut x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  have h0 : 0 ≤ centralCut x := centralBump.nonneg' x
  have h1 : centralCut x ≤ 1 := centralBump.le_one
  exact ⟨by linarith, h1⟩

private theorem selfSimilarPressure_shell_bound {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (htT : t < T) {x : Space}
    (hx1 : centralRadius / 4 ≤ dist x center) :
    ‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ 4096 * C := by
  have hr : (1 / 16 : ℝ) ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hP := selfSimilarPressure_fderiv_bound hW htT x
  have h3 : (1 / 16 : ℝ) ^ 3 ≤ dist x center ^ 3 := pow_le_pow_left₀ (by norm_num) hr _
  nlinarith [norm_nonneg (fderiv ℝ (selfSimilarPressure q T t) x)]

private theorem time_selfSimilar_bound (hS : SelfSimilarSolves) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (hT : 0 < T)
    (htT : t < T) {x : Space} (hx1 : centralRadius / 4 ≤ dist x center)
    (hx2 : dist x center ≤ centralRadius / 2) :
    ‖deriv (fun τ => selfSimilar W T τ x) t‖ ≤ 4096 * C * (4096 * C) + 6 * (4096 * C) := by
  have hC0 := profile_const_nonneg hW
  have hE := ((hS W q C T hW hT).2.2 t htT x).2
  have hg0 := selfSimilar_shell_bound hW htT hx1 hx2 (i := 0) (by norm_num)
  have hg1 := selfSimilar_shell_bound hW htT hx1 hx2 (i := 1) (by norm_num)
  have hg2 := selfSimilar_shell_bound hW htT hx1 hx2 (i := 2) (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hg0
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at hg1
  have hp := selfSimilarPressure_shell_bound hW htT hx1
  have ha : ‖advectionAt (selfSimilar W T t) x‖ ≤ 4096 * C * (4096 * C) := by
    unfold advectionAt
    exact ((fderiv ℝ (selfSimilar W T t) x).le_opNorm _).trans
      (mul_le_mul hg1 hg0 (norm_nonneg _) (by positivity))
  have hl := (norm_sumSecondPartialsAt_le (selfSimilar W T t) x).trans
    (mul_le_mul_of_nonneg_left hg2 (by norm_num : (0 : ℝ) ≤ 3))
  have hgr := (norm_gradientAt_le (selfSimilarPressure q T t) x).trans
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3))
  have heq : deriv (fun τ => selfSimilar W T τ x) t = sumSecondPartialsAt (selfSimilar W T t) x
      - advectionAt (selfSimilar W T t) x - gradientAt (selfSimilarPressure q T t) x := by
    rw [← sub_eq_zero, ← hE]
    abel
  rw [heq]
  have e1 := norm_sub_le (sumSecondPartialsAt (selfSimilar W T t) x - advectionAt (selfSimilar W T t) x)
    (gradientAt (selfSimilarPressure q T t) x)
  have e2 := norm_sub_le (sumSecondPartialsAt (selfSimilar W T t) x) (advectionAt (selfSimilar W T t) x)
  linarith


private theorem time_selfSimilar_sharp (hS : SelfSimilarSolves) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (hT : 0 < T)
    (htT : t < T) (z : Space) :
    ‖deriv (fun τ => selfSimilar W T τ z) t‖ ≤ (C * C + 6 * C) *
      (((T - t) ^ (-(1 / 2 : ℝ))) ^ 3 / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist z center) ^ 3) := by
  have hC0 := profile_const_nonneg hW
  have hE := ((hS W q C T hW hT).2.2 t htT z).2
  have hg0 := selfSimilar_iteratedFDeriv_sharp hW htT z (j := 0) (by norm_num)
  have hg1 := selfSimilar_iteratedFDeriv_sharp hW htT z (j := 1) (by norm_num)
  have hg2 := selfSimilar_iteratedFDeriv_sharp hW htT z (j := 2) (by norm_num)
  have hp := selfSimilarPressure_fderiv_sharp hW htT z
  rw [norm_iteratedFDeriv_zero] at hg0
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at hg1
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (T - t) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ rpow_pos_of_pos (by linarith) _
  rw [← hl] at hg0 hg1 hg2 hp ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + l * dist z center := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  rw [← hA] at hg0 hg1 hg2 hp ⊢
  have ha : ‖advectionAt (selfSimilar W T t) z‖ ≤ C * C * (l ^ 3 / A ^ 3) := by
    unfold advectionAt
    refine ((fderiv ℝ (selfSimilar W T t) z).le_opNorm _).trans ?_
    calc ‖fderiv ℝ (selfSimilar W T t) z‖ * ‖selfSimilar W T t z‖
        ≤ (l ^ (1 + 1) * (C / A ^ (1 + 1))) * (l ^ (0 + 1) * (C / A ^ (0 + 1))) :=
          mul_le_mul hg1 hg0 (norm_nonneg _) (by positivity)
      _ = C * C * (l ^ 3 / A ^ 3) := by ring
  have hl' := (norm_sumSecondPartialsAt_le (selfSimilar W T t) z).trans
    (mul_le_mul_of_nonneg_left hg2 (by norm_num : (0 : ℝ) ≤ 3))
  have hgr := (norm_gradientAt_le (selfSimilarPressure q T t) z).trans
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3))
  have e3 : 3 * (l ^ (2 + 1) * (C / A ^ (2 + 1))) = 3 * C * (l ^ 3 / A ^ 3) := by ring
  have e4 : 3 * (l ^ 3 * (C / A ^ 3)) = 3 * C * (l ^ 3 / A ^ 3) := by ring
  have heq : deriv (fun τ => selfSimilar W T τ z) t = sumSecondPartialsAt (selfSimilar W T t) z
      - advectionAt (selfSimilar W T t) z - gradientAt (selfSimilarPressure q T t) z := by
    rw [← sub_eq_zero, ← hE]
    abel
  rw [heq]
  have e1 := norm_sub_le (sumSecondPartialsAt (selfSimilar W T t) z - advectionAt (selfSimilar W T t) z)
    (gradientAt (selfSimilarPressure q T t) z)
  have e2 := norm_sub_le (sumSecondPartialsAt (selfSimilar W T t) z) (advectionAt (selfSimilar W T t) z)
  linarith

private theorem integral_kernel_bound {a : ℝ} (ha : 0 < a) :
    ∫ s in (0 : ℝ)..1, s / (1 + a * s) ^ 3 ≤ 1 / a ^ 2 := by
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + a * s := fun s hs => by nlinarith [hs.1]
  have hcont1 : ContinuousOn (fun s : ℝ => s / (1 + a * s) ^ 3) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_id.div (by fun_prop) (fun s hs => (pow_pos (hpos s hs) 3).ne')
  have hcont2 : ContinuousOn (fun s : ℝ => 1 / (a * (1 + a * s) ^ 2)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.div (by fun_prop)
      (fun s hs => (mul_pos ha (pow_pos (hpos s hs) 2)).ne')
  have hmono := intervalIntegral.integral_mono_on zero_le_one (hcont1.intervalIntegrable (μ := MeasureTheory.volume))
    (hcont2.intervalIntegrable (μ := MeasureTheory.volume)) (fun s hs => by
      have h1 := hpos s hs
      rw [div_le_div_iff₀ (pow_pos h1 3) (mul_pos ha (pow_pos h1 2))]
      nlinarith [sq_nonneg (1 + a * s)])
  have hF : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => -1 / (a ^ 2 * (1 + a * s)))
      (1 / (a * (1 + a * s) ^ 2)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := hpos s hs
    have hd : HasDerivAt (fun s => a ^ 2 * (1 + a * s)) (a ^ 2 * (a * 1)) s :=
      (((hasDerivAt_id' s).const_mul a).const_add 1).const_mul (a ^ 2)
    have hq := (hasDerivAt_const s (-1 : ℝ)).div hd (mul_pos (pow_pos ha 2) h1).ne'
    refine hq.congr_deriv ?_
    rw [div_eq_div_iff (pow_pos (mul_pos (pow_pos ha 2) h1) 2).ne' (mul_pos ha (pow_pos h1 2)).ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont2.intervalIntegrable (μ := MeasureTheory.volume))] at hmono
  simp only [mul_one, mul_zero, add_zero] at hmono
  have h2 : 0 ≤ 1 / (a ^ 2 * (1 + a)) := by positivity
  have e : -1 / (a ^ 2 * (1 + a)) - -1 / a ^ 2 = 1 / a ^ 2 - 1 / (a ^ 2 * (1 + a)) := by ring
  linarith

private theorem potential_time_deriv (hS : SelfSimilarSolves) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) {T t : ℝ} (hT : 0 < T)
    (htT : t < T) (x : Space) :
    HasDerivAt (fun τ => homotopyPotential center (selfSimilar W T τ) x)
      (∫ s in (0 : ℝ)..1, s • cross (deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t)
        (x - center)) t := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × Space → Space, G = fun z => selfSimilar W T z.1 z.2 := ⟨_, rfl⟩
  have hG : ContDiffOn ℝ ∞ G (Iio T ×ˢ univ) := hGdef ▸ (hS W q C T hW hT).1
  have hU : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ G) (Iio T ×ˢ univ) :=
    hG.continuousOn_fderiv_of_isOpen hU (by simp)
  have hGd : ∀ τ < T, ∀ z : Space,
      HasDerivAt (fun σ => selfSimilar W T σ z) (fderiv ℝ G (τ, z) (1, 0)) τ := by
    intro τ hτ z
    have hJ : HasFDerivAt G (fderiv ℝ G (τ, z)) (τ, z) :=
      ((hG.contDiffAt (prod_mem_nhds (Iio_mem_nhds hτ) univ_mem)).differentiableAt
        (by simp)).hasFDerivAt
    have h := hJ.comp_hasDerivAt τ ((hasDerivAt_id' τ).prodMk (hasDerivAt_const τ z))
    have e : (G ∘ fun σ : ℝ => (σ, z)) = fun σ => selfSimilar W T σ z := by
      rw [hGdef]
      rfl
    rw [e] at h
    exact h
  have hcr : Continuous (fun p : Space × Space => cross p.1 p.2) :=
    (Breakdown.Periodic.Cutoff.Internal.contDiff_cross (n := 0) contDiff_fst contDiff_snd).continuous
  obtain ⟨a, ha⟩ : ∃ a : Space, a = x - center := ⟨_, rfl⟩
  show HasDerivAt (fun τ => ∫ s in (0 : ℝ)..1,
    s • cross (selfSimilar W T τ (center + s • (x - center))) (x - center)) _ t
  rw [← ha]
  have hline : Continuous (fun s : ℝ => center + s • a) :=
    continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨F', hF'def⟩ : ∃ F' : ℝ → ℝ → Space,
      F' = fun τ s => s • Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (τ, center + s • a) (1, 0)) a := ⟨_, rfl⟩
  have hsub : Icc (t - (T - t) / 2) (t + (T - t) / 2) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hST : ∀ τ ∈ Icc (t - (T - t) / 2) (t + (T - t) / 2), τ < T :=
    fun τ hτ => by linarith [hτ.2]
  have hcontF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G (p.1, center + p.2 • a))
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      hfd.comp (continuous_fst.prodMk (hline.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hST p.1 hp.1, mem_univ _⟩)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G (p.1, center + p.2 • a) (1, 0))
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      h1.clm_apply continuousOn_const
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (p.1, center + p.2 • a) (1, 0)) a)
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      (Breakdown.Periodic.Cutoff.Internal.crossBilinear.continuous.comp_continuousOn h2).clm_apply
        continuousOn_const
    rw [hF'def]
    exact continuous_snd.continuousOn.smul h4
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcontF'
  have hF'cont : Continuous (F' t) := by
    have h1 : Continuous (fun s : ℝ => fderiv ℝ G (t, center + s • a)) :=
      hfd.comp_continuous (continuous_const.prodMk hline) (fun s => ⟨htT, mem_univ _⟩)
    have h3 : Continuous (fun s : ℝ => Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (t, center + s • a) (1, 0)) a) :=
      (Breakdown.Periodic.Cutoff.Internal.crossBilinear.continuous.comp
        (h1.clm_apply continuous_const)).clm_apply continuous_const
    rw [hF'def]
    exact continuous_id.smul h3
  have hFcont : ∀ τ < T, Continuous (fun s : ℝ => s • cross (selfSimilar W T τ (center + s • a)) a) := by
    intro τ hτ
    have h1 : Continuous (fun s : ℝ => selfSimilar W T τ (center + s • a)) :=
      (slice_of_contDiffOn (hS W q C T hW hT).1 hτ).continuous.comp hline
    have h2 : Continuous (fun s : ℝ => (selfSimilar W T τ (center + s • a), a)) :=
      h1.prodMk (continuous_const (y := a))
    have h3 : Continuous (fun s : ℝ => cross (selfSimilar W T τ (center + s • a)) a) := hcr.comp h2
    exact continuous_id.smul h3
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (bound := fun _ => K)
    (F := fun τ s => s • cross (selfSimilar W T τ (center + s • a)) a) (F' := F') hsub
    (by filter_upwards [Iio_mem_nhds htT] with τ hτ using (hFcont τ hτ).aestronglyMeasurable)
    ((hFcont t htT).intervalIntegrable _ _) hF'cont.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun s hs τ hτ => hK (τ, s) ⟨hτ, Ioc_subset_Icc_self
      (by rwa [uIoc_of_le zero_le_one] at hs)⟩)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun s _ τ hτ => by
      have h := (s • (Breakdown.Periodic.Cutoff.Internal.crossBilinear.flip a)).hasFDerivAt.comp_hasDerivAt
        τ (hGd τ (hST τ hτ) (center + s • a))
      rw [smul_apply, ContinuousLinearMap.flip_apply] at h
      rw [hF'def]
      exact h)
  have heq : (∫ s in (0 : ℝ)..1, s • cross (deriv (fun τ => selfSimilar W T τ (center + s • a)) t) a)
      = ∫ s in (0 : ℝ)..1, F' t s := by
    congr 1
    funext s
    rw [(hGd t htT (center + s • a)).deriv, hF'def]
    rfl
  rw [heq]
  exact hmain.2

private theorem potential_time_bound (hS : SelfSimilarSolves)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        DifferentiableAt ℝ (fun τ => homotopyPotential center (selfSimilar W T τ) x) t ∧
          ‖deriv (fun τ => homotopyPotential center (selfSimilar W T τ) x) t‖ ≤
            K * (T - t) ^ (-(1 / 2 : ℝ)) := by
  have hC0 := profile_const_nonneg hW
  refine ⟨16 * ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (C * C + 6 * C),
    by positivity, ?_⟩
  intro T t hT _ _ htT x hx1 hx2
  have hd := potential_time_deriv hS hW hT htT x
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (T - t) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ rpow_pos_of_pos (by linarith) _
  rw [← hl]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = dist x center := ⟨_, rfl⟩
  have hρ1 : 1 / 16 ≤ ρ := by rw [hρ]; norm_num [centralRadius] at hx1; linarith
  have hρ0 : 0 < ρ := by linarith
  have hxa : ‖x - center‖ = ρ := by rw [hρ, dist_eq_norm]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ norm_nonneg _
  rw [← hB]
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1, ‖s • cross (deriv (fun τ => selfSimilar W T τ
      (center + s • (x - center))) t) (x - center)‖ ≤
      (B * (C * C + 6 * C) * ρ * l ^ 3) * (s / (1 + (l * ρ) * s) ^ 3) := by
    intro s hs
    have hts := time_selfSimilar_sharp hS hW hT htT (center + s • (x - center))
    rw [← hl] at hts
    have hdist : dist (center + s • (x - center)) center = s * ρ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hxa]
    have e : l * (s * ρ) = (l * ρ) * s := by ring
    rw [hdist, e] at hts
    have hcr : ‖cross (deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t)
        (x - center)‖ ≤ B * ‖deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t‖
          * ρ := by
      have h := Breakdown.Periodic.Cutoff.Internal.crossBilinear.le_opNorm₂
        (deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t) (x - center)
      rw [hxa, ← hB] at h
      exact h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖cross (deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t)
          (x - center)‖
        ≤ s * (B * ((C * C + 6 * C) * (l ^ 3 / (1 + l * ρ * s) ^ 3)) * ρ) := by
          exact mul_le_mul_of_nonneg_left (hcr.trans (by gcongr)) hs.1.le
      _ = (B * (C * C + 6 * C) * ρ * l ^ 3) * (s / (1 + (l * ρ) * s) ^ 3) := by ring
  have hcont : ContinuousOn (fun s : ℝ => (B * (C * C + 6 * C) * ρ * l ^ 3) *
      (s / (1 + (l * ρ) * s) ^ 3)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine continuousOn_const.mul (continuousOn_id.div (by fun_prop) (fun s hs => ?_))
    have : 0 < 1 + l * ρ * s := by nlinarith [hs.1, mul_pos hl0 hρ0]
    exact (pow_pos this 3).ne'
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (MeasureTheory.ae_of_all _ fun s hs => hpt s hs) (hcont.intervalIntegrable (μ := MeasureTheory.volume))
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 := integral_kernel_bound (mul_pos hl0 hρ0)
  have hM : 0 ≤ B * (C * C + 6 * C) * ρ * l ^ 3 := by positivity
  have h3 : B * (C * C + 6 * C) * ρ * l ^ 3 * (1 / (l * ρ) ^ 2) =
      B * (C * C + 6 * C) * l * (1 / ρ) := by
    field_simp
  have h4 : 1 / ρ ≤ 16 := by rw [div_le_iff₀ hρ0]; linarith
  have hK : 0 ≤ B * (C * C + 6 * C) * l := by positivity
  calc _ ≤ _ := h1
    _ ≤ B * (C * C + 6 * C) * ρ * l ^ 3 * (1 / (l * ρ) ^ 2) := by gcongr
    _ = B * (C * C + 6 * C) * l * (1 / ρ) := h3
    _ ≤ B * (C * C + 6 * C) * l * 16 := by gcongr
    _ = 16 * B * (C * C + 6 * C) * l := by ring

private theorem residual_zero_outer (hA : ApproxFieldProperties) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C T t : ℝ} (hW : IsSimilarityProfile W q C) (hT : 0 < T) (htT : t < T)
    {x : Space} (hx : centralRadius / 2 < dist x center) : approxResidual W q T t x = 0 := by
  have hU : {y : Space | centralRadius / 2 < dist y center} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hx
  have hF : ∀ τ < T, ∀ y ∈ {y : Space | centralRadius / 2 < dist y center},
      approxField W T τ y = 0 ∧ approxPressure q T τ y = 0 :=
    fun τ hτ y hy => ((hA W q C T hW hT).2.2 τ hτ y).2.1 (le_of_lt hy)
  have h1 : (fun τ => approxField W T τ x) =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds htT] with τ hτ
    exact (hF τ hτ x hx).1
  have h2 : approxField W T t =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU] with y hy
    exact (hF t htT y hy).1
  have h3 : approxPressure q T t =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU] with y hy
    exact (hF t htT y hy).2
  unfold approxResidual advectionAt sumSecondPartialsAt gradientAt
  rw [h1.deriv_eq, h2.fderiv_eq, h3.fderiv_eq, (h2.iteratedFDeriv ℝ 2).eq_of_nhds]
  simp

private theorem residual_zero_inner (hS : SelfSimilarSolves) (hA : ApproxFieldProperties)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ} (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) (htT : t < T) {x : Space} (hx : dist x center < centralRadius / 4) :
    approxResidual W q T t x = 0 := by
  have hU : Metric.ball center (centralRadius / 4) ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
  have hF : ∀ τ < T, ∀ y ∈ Metric.ball center (centralRadius / 4),
      approxField W T τ y = selfSimilar W T τ y :=
    fun τ hτ y hy => ((hA W q C T hW hT).2.2 τ hτ y).2.2 (le_of_lt hy)
  have h1 : (fun τ => approxField W T τ x) =ᶠ[𝓝 t] fun τ => selfSimilar W T τ x := by
    filter_upwards [Iio_mem_nhds htT] with τ hτ
    exact hF τ hτ x hx
  have h2 : approxField W T t =ᶠ[𝓝 x] selfSimilar W T t := by
    filter_upwards [hU] with y hy
    exact hF t htT y hy
  have h3 : approxPressure q T t =ᶠ[𝓝 x]
      fun y => selfSimilarPressure q T t y - selfSimilarPressure q T t pressureAnchor := by
    filter_upwards [hU] with y hy
    have hy' : y ∈ Metric.closedBall center centralBump.rIn := Metric.ball_subset_closedBall hy
    simp only [approxPressure, centralCut]
    rw [centralBump.one_of_mem_closedBall hy', one_mul]
  have hE := ((hS W q C T hW hT).2.2 t htT x).2
  unfold approxResidual advectionAt sumSecondPartialsAt gradientAt
  unfold advectionAt sumSecondPartialsAt gradientAt at hE
  rw [h1.deriv_eq, h2.fderiv_eq, h2.eq_of_nhds, h3.fderiv_eq,
    (h2.iteratedFDeriv ℝ 2).eq_of_nhds, fderiv_sub_const]
  exact hE

private theorem residual_support (hS : SelfSimilarSolves) (hA : ApproxFieldProperties)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ} (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) (htT : t < T) (x : Space) (hR : approxResidual W q T t x ≠ 0) :
    centralRadius / 4 ≤ dist x center ∧ dist x center ≤ centralRadius / 2 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hR (residual_zero_inner hS hA hW hT htT (lt_of_not_ge h))
  · by_contra h
    exact hR (residual_zero_outer hA hW hT htT (lt_of_not_ge h))

private theorem time_term_bound (hS : SelfSimilarSolves)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖deriv (fun τ => approxField W T τ x) t‖ ≤ K * (T - t) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Kψ, hKψ, hψ⟩ := potential_time_bound hS hW
  obtain ⟨KG, hKG, hG⟩ := bounded_low_derivs (gradient_contDiff centralCut_contDiff)
    (gradient_support centralCut_support)
  have hC0 := profile_const_nonneg hW
  refine ⟨4096 * C * (4096 * C) + 6 * (4096 * C) +
    ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * KG * Kψ, by positivity, ?_⟩
  intro T t hT hT1 ht htT x hx1 hx2
  obtain ⟨hdiff, hbd⟩ := hψ T t hT hT1 ht htT x hx1 hx2
  have hP : 1 ≤ (T - t) ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hJ : DifferentiableAt ℝ (fun z : ℝ × Space => selfSimilar W T z.1 z.2) (t, x) :=
    ((hS W q C T hW hT).1.contDiffAt
      (prod_mem_nhds (Iio_mem_nhds htT) univ_mem)).differentiableAt (by simp)
  have hin : DifferentiableAt ℝ (fun τ : ℝ => (τ, x)) t :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  have hgt : DifferentiableAt ℝ ((fun z : ℝ × Space => selfSimilar W T z.1 z.2) ∘
      fun τ : ℝ => (τ, x)) t := hJ.comp t hin
  have hsplit : (fun τ => approxField W T τ x) = fun τ => centralCut x • selfSimilar W T τ x +
      Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut x)
        (homotopyPotential center (selfSimilar W T τ) x) := rfl
  have hd1 : HasDerivAt (fun τ => centralCut x • selfSimilar W T τ x)
      (centralCut x • deriv (fun τ => selfSimilar W T τ x) t) t := by
    have hgt' : DifferentiableAt ℝ (fun τ => selfSimilar W T τ x) t := hgt
    exact hgt'.hasDerivAt.const_smul (centralCut x)
  have hd2 : HasDerivAt (fun τ => Breakdown.Periodic.Cutoff.Internal.crossBilinear
      (gradientAt centralCut x) (homotopyPotential center (selfSimilar W T τ) x))
      (Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut x)
        (deriv (fun τ => homotopyPotential center (selfSimilar W T τ) x) t)) t :=
    (Breakdown.Periodic.Cutoff.Internal.crossBilinear
      (gradientAt centralCut x)).hasFDerivAt.comp_hasDerivAt t hdiff.hasDerivAt
  have hd : HasDerivAt (fun τ => centralCut x • selfSimilar W T τ x +
      Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut x)
        (homotopyPotential center (selfSimilar W T τ) x))
      (centralCut x • deriv (fun τ => selfSimilar W T τ x) t +
        Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut x)
          (deriv (fun τ => homotopyPotential center (selfSimilar W T τ) x) t)) t := hd1.add hd2
  rw [hsplit, hd.deriv]
  have hg := time_selfSimilar_bound hS hW hT htT hx1 hx2
  have hGx : ‖gradientAt centralCut x‖ ≤ KG := by
    have := hG 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero] at this
  have e1 : ‖centralCut x • deriv (fun τ => selfSimilar W T τ x) t‖ ≤
      1 * (4096 * C * (4096 * C) + 6 * (4096 * C)) := by
    rw [norm_smul]
    exact mul_le_mul (centralCut_norm_le x) hg (norm_nonneg _) zero_le_one
  have e2 : ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut x)
      (deriv (fun τ => homotopyPotential center (selfSimilar W T τ) x) t)‖ ≤
      ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * KG * (Kψ * (T - t) ^ (-(1 / 2 : ℝ))) := by
    refine (Breakdown.Periodic.Cutoff.Internal.crossBilinear.le_opNorm₂ _ _).trans ?_
    gcongr
  refine (norm_add_le _ _).trans ?_
  have hB : 0 ≤ ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * KG := by positivity
  have hA : 0 ≤ 4096 * C * (4096 * C) + 6 * (4096 * C) := by positivity
  nlinarith

private theorem field_bound (hS : SelfSimilarSolves) (hC : HomotopyCurl)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖approxField W T t x‖ ≤ K ∧ ‖fderiv ℝ (approxField W T t) x‖ ≤ K ∧
          ‖iteratedFDeriv ℝ 2 (approxField W T t) x‖ ≤ K := by
  obtain ⟨Kψ, hKψ, hψ⟩ := potential_bound hS hW
  obtain ⟨Kχ, hKχ, hχ⟩ := bounded_low_derivs centralCut_contDiff centralCut_support
  obtain ⟨KG, hKG, hG⟩ := bounded_low_derivs (gradient_contDiff centralCut_contDiff)
    (gradient_support centralCut_support)
  have hC0 := profile_const_nonneg hW
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Kχ + KG + 4096 * C + Kψ := ⟨_, rfl⟩
  have hGs := gradient_contDiff centralCut_contDiff
  have key : ∀ T t : ℝ, 0 < T → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j (approxField W T t) x‖ ≤ 4 * (M * M) + ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (4 * (M * M)) := by
    intro T t hT htT x hx1 hx2 j hj
    have hg : ContDiff ℝ ∞ (selfSimilar W T t) := slice_of_contDiffOn (hS W q C T hW hT).1 htT
    have hdiv : ∀ y, divergenceAt (selfSimilar W T t) y = 0 :=
      fun y => ((hS W q C T hW hT).2.2 t htT y).1
    have hψs : ContDiff ℝ ∞ (homotopyPotential center (selfSimilar W T t)) :=
      (hC center _ hg hdiv).1
    have hsplit : approxField W T t = (fun y => centralCut y • selfSimilar W T t y) +
        (fun y => Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut y)
          (homotopyPotential center (selfSimilar W T t) y)) := rfl
    have h1 : ContDiff ℝ ∞ (fun y => centralCut y • selfSimilar W T t y) := centralCut_contDiff.smul hg
    have h2 : ContDiff ℝ ∞ (fun y => Breakdown.Periodic.Cutoff.Internal.crossBilinear (gradientAt centralCut y)
        (homotopyPotential center (selfSimilar W T t) y)) := Breakdown.Periodic.Cutoff.Internal.contDiff_cross hGs hψs
    rw [hsplit, iteratedFDeriv_add_apply (h1.contDiffAt.of_le (nat_le_infty j))
      (h2.contDiffAt.of_le (nat_le_infty j))]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_iteratedFDeriv_smul_le centralCut_contDiff hg x (nat_le_infty j)).trans ?_
      exact binom_sum_le (a := fun i => ‖iteratedFDeriv ℝ i centralCut x‖)
        (b := fun i => ‖iteratedFDeriv ℝ i (selfSimilar W T t) x‖)
        (fun i hi => ⟨norm_nonneg _, by linarith [hχ i hi x]⟩)
        (fun i hi => ⟨norm_nonneg _, by linarith [selfSimilar_shell_bound hW htT hx1 hx2 hi]⟩) hj
    · refine (Breakdown.Periodic.Cutoff.Internal.crossBilinear.norm_iteratedFDeriv_le_of_bilinear hGs hψs x (nat_le_infty j)).trans ?_
      gcongr
      exact binom_sum_le (a := fun i => ‖iteratedFDeriv ℝ i (gradientAt centralCut) x‖)
        (b := fun i => ‖iteratedFDeriv ℝ i (homotopyPotential center (selfSimilar W T t)) x‖)
        (fun i hi => ⟨norm_nonneg _, by linarith [hG i hi x]⟩)
        (fun i hi => ⟨norm_nonneg _, by linarith [hψ T t hT htT x hx1 hx2 i hi]⟩) hj
  refine ⟨4 * (M * M) + ‖Breakdown.Periodic.Cutoff.Internal.crossBilinear‖ * (4 * (M * M)), add_nonneg (by nlinarith [mul_self_nonneg M])
    (mul_nonneg (norm_nonneg _) (by nlinarith [mul_self_nonneg M])), ?_⟩
  intro T t hT _ _ htT x hx1 hx2
  have k0 := key T t hT htT x hx1 hx2 0 (by norm_num)
  have k1 := key T t hT htT x hx1 hx2 1 (by norm_num)
  have k2 := key T t hT htT x hx1 hx2 2 (by norm_num)
  rw [norm_iteratedFDeriv_zero] at k0
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at k1
  exact ⟨k0, k1, k2⟩

private theorem pressure_bound (hS : SelfSimilarSolves)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ} (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖fderiv ℝ (approxPressure q T t) x‖ ≤ K := by
  obtain ⟨Kd, hKd, hd⟩ := pressure_difference_bound hS hW
  obtain ⟨Kc, hKc, hc⟩ := bounded_iteratedFDeriv centralCut_contDiff centralCut_support 1
  have hC0 := profile_const_nonneg hW
  refine ⟨4096 * C + Kd * Kc, by positivity, ?_⟩
  intro T t hT hT1 ht htT x hx1 hx2
  have hp : ContDiff ℝ ∞ (selfSimilarPressure q T t) :=
    slice_of_contDiffOn (hS W q C T hW hT).2.1 htT
  have hpd : DifferentiableAt ℝ (fun y => selfSimilarPressure q T t y
      - selfSimilarPressure q T t pressureAnchor) x :=
    ((hp.differentiable (by simp)) x).sub_const _
  have hcd : DifferentiableAt ℝ centralCut x := (centralCut_contDiff.differentiable (by simp)) x
  have hfun : approxPressure q T t = fun y => centralCut y * (selfSimilarPressure q T t y
      - selfSimilarPressure q T t pressureAnchor) := rfl
  have hfd : fderiv ℝ (fun y => centralCut y * (selfSimilarPressure q T t y
      - selfSimilarPressure q T t pressureAnchor)) x = centralCut x • fderiv ℝ (fun y =>
      selfSimilarPressure q T t y - selfSimilarPressure q T t pressureAnchor) x
      + (selfSimilarPressure q T t x - selfSimilarPressure q T t pressureAnchor) •
      fderiv ℝ centralCut x := (hcd.hasFDerivAt.mul hpd.hasFDerivAt).fderiv
  rw [hfun, hfd, fderiv_sub_const]
  have hχ : ‖centralCut x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    have h0 : 0 ≤ centralCut x := centralBump.nonneg' x
    have h1 : centralCut x ≤ 1 := centralBump.le_one
    exact ⟨by linarith, h1⟩
  have hχ' : ‖fderiv ℝ centralCut x‖ ≤ Kc := by
    have := hc x
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  have hr : (1 / 16 : ℝ) ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hP := selfSimilarPressure_fderiv_bound hW htT x
  have hP' : ‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ 4096 * C := by
    have h3 : (1 / 16 : ℝ) ^ 3 ≤ dist x center ^ 3 := pow_le_pow_left₀ (by norm_num) hr _
    nlinarith [norm_nonneg (fderiv ℝ (selfSimilarPressure q T t) x)]
  have hdx := hd T t hT htT x hx1 hx2
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs (_ - _)]
  have e1 : ‖centralCut x‖ * ‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ 1 * (4096 * C) :=
    mul_le_mul hχ hP' (norm_nonneg _) zero_le_one
  have e2 : |selfSimilarPressure q T t x - selfSimilarPressure q T t pressureAnchor|
      * ‖fderiv ℝ centralCut x‖ ≤ Kd * Kc := mul_le_mul hdx hχ' (norm_nonneg _) hKd
  linarith

private theorem shell_bound (hS : SelfSimilarSolves) (hC : HomotopyCurl) {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C : ℝ}
    (hW : IsSimilarityProfile W q C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖approxResidual W q T t x‖ ≤ K * (T - t) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K₁, hK₁, h₁⟩ := time_term_bound hS hW
  obtain ⟨K₂, hK₂, h₂⟩ := field_bound hS hC hW
  obtain ⟨K₃, hK₃, h₃⟩ := pressure_bound hS hW
  refine ⟨K₁ + K₂ * K₂ + 3 * K₂ + 3 * K₃, by positivity, ?_⟩
  intro T t hT hT1 ht htT x hx1 hx2
  have hP : 1 ≤ (T - t) ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
  obtain ⟨hv, hd, hdd⟩ := h₂ T t hT hT1 ht htT x hx1 hx2
  have ht' := h₁ T t hT hT1 ht htT x hx1 hx2
  have hp := h₃ T t hT hT1 ht htT x hx1 hx2
  have ha : ‖advectionAt (approxField W T t) x‖ ≤ K₂ * K₂ := by
    unfold advectionAt
    refine ((fderiv ℝ (approxField W T t) x).le_opNorm _).trans ?_
    exact mul_le_mul hd hv (norm_nonneg _) hK₂
  have hl := (norm_sumSecondPartialsAt_le (approxField W T t) x).trans
    (mul_le_mul_of_nonneg_left hdd (by norm_num : (0 : ℝ) ≤ 3))
  have hg := (norm_gradientAt_le (approxPressure q T t) x).trans
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3))
  unfold approxResidual
  have htri : ‖deriv (fun τ => approxField W T τ x) t + advectionAt (approxField W T t) x
      - sumSecondPartialsAt (approxField W T t) x + gradientAt (approxPressure q T t) x‖ ≤
      ‖deriv (fun τ => approxField W T τ x) t‖ + ‖advectionAt (approxField W T t) x‖
      + ‖sumSecondPartialsAt (approxField W T t) x‖ + ‖gradientAt (approxPressure q T t) x‖ := by
    exact norm_four_le _ _ _ _
  refine htri.trans ?_
  have hrest : 0 ≤ K₂ * K₂ + 3 * K₂ + 3 * K₃ := by positivity
  nlinarith

end Residual.Internal

open Residual.Internal in
theorem approxResidualBound (hS : SelfSimilarSolves) (hC : HomotopyCurl)
    (hA : ApproxFieldProperties) : ApproxResidualBound := by
  intro W q C hW
  obtain ⟨K, hK, hB⟩ := shell_bound hS hC hW
  refine ⟨K, fun T t hT hT1 ht htT x => ⟨?_, residual_support hS hA hW hT htT x⟩⟩
  by_cases hR : approxResidual W q T t x = 0
  · rw [hR, norm_zero]
    exact mul_nonneg hK (rpow_nonneg (by linarith) _)
  · obtain ⟨h1, h2⟩ := residual_support hS hA hW hT htT x hR
    exact hB T t hT hT1 ht htT x h1 h2

end Breakdown.Periodic

import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineSmooth

open scoped ContDiff NNReal Topology
open Set Metric

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline cellCount cellIndex atFirst weightPoly heightRatio)

namespace Internal

theorem scaled_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a a' : E) {s s' : ℝ}
    (hs : 0 ≤ s) (hs' : 0 < s') (ha : ‖a‖ ≤ s) :
    ‖s⁻¹ • a - s'⁻¹ • a'‖ * s' ≤ ‖a - a'‖ + |s - s'| := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have ha0 : a = 0 := norm_le_zero_iff.mp ha
    subst ha0
    have e : ‖(0 : ℝ)⁻¹ • (0 : E) - s'⁻¹ • a'‖ * s' = ‖a'‖ := by
      rw [smul_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs']
      field_simp
    rw [e, zero_sub, norm_neg]
    linarith [abs_nonneg (0 - s')]
  · have e : s⁻¹ • a - s'⁻¹ • a' = s'⁻¹ • (a - a') + (s⁻¹ - s'⁻¹) • a := by
      rw [smul_sub, sub_smul]
      abel
    have h1 : ‖s'⁻¹ • (a - a')‖ = s'⁻¹ * ‖a - a'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs']
    have h2 : ‖(s⁻¹ - s'⁻¹) • a‖ ≤ |s - s'| / s' := by
      rw [norm_smul, Real.norm_eq_abs]
      have e2 : s⁻¹ - s'⁻¹ = (s' - s) / (s * s') := by
        field_simp
      rw [e2, abs_div, abs_of_pos (mul_pos hpos hs'), abs_sub_comm]
      calc |s - s'| / (s * s') * ‖a‖ ≤ |s - s'| / (s * s') * s := by gcongr
        _ = |s - s'| / s' := by field_simp
    have h3 : ‖s⁻¹ • a - s'⁻¹ • a'‖ ≤ s'⁻¹ * ‖a - a'‖ + |s - s'| / s' := by
      rw [e]
      exact (norm_add_le _ _).trans (by rw [h1]; linarith [h2])
    calc ‖s⁻¹ • a - s'⁻¹ • a'‖ * s' ≤ (s'⁻¹ * ‖a - a'‖ + |s - s'| / s') * s' :=
          mul_le_mul_of_nonneg_right h3 hs'.le
      _ = ‖a - a'‖ + |s - s'| := by field_simp

def ScaleSlope (g : Space → ℂ) (s : Set Space) (C : ℝ) : Prop :=
  ∀ y ∈ s, ∀ y' ∈ s, y' ≠ 0 → ‖g y - g y'‖ * ‖y'‖ ≤ C * ‖y - y'‖

theorem scaleSlope_of_ne {g : Space → ℂ} {s : Set Space} {C M : ℝ} (hC : 0 ≤ C)
    (hM : ∀ y ∈ s, ‖g y‖ ≤ M)
    (h : ∀ y ∈ s, ∀ y' ∈ s, y ≠ 0 → y' ≠ 0 → ‖g y - g y'‖ * ‖y'‖ ≤ C * ‖y - y'‖) :
    ScaleSlope g s (C + 2 * M) := by
  intro y hy y' hy' hy'0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y hy)
  by_cases hy0 : y = 0
  · subst hy0
    have hd : ‖g 0 - g y'‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hM 0 hy, hM y' hy'])
    rw [zero_sub, norm_neg]
    calc ‖g 0 - g y'‖ * ‖y'‖ ≤ 2 * M * ‖y'‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ ≤ (C + 2 * M) * ‖y'‖ := by nlinarith [norm_nonneg y']
  · calc ‖g y - g y'‖ * ‖y'‖ ≤ C * ‖y - y'‖ := h y hy y' hy' hy0 hy'0
      _ ≤ (C + 2 * M) * ‖y - y'‖ := by nlinarith [norm_nonneg (y - y')]

theorem scaleSlope_mono {g : Space → ℂ} {s t : Set Space} {C : ℝ} (h : ScaleSlope g s C) (hts : t ⊆ s) :
    ScaleSlope g t C :=
  fun y hy y' hy' hy0 => h y (hts hy) y' (hts hy') hy0

theorem scaleSlope_mul {g₁ g₂ : Space → ℂ} {s : Set Space} {C₁ C₂ M₁ M₂ : ℝ}
    (h₁ : ScaleSlope g₁ s C₁) (h₂ : ScaleSlope g₂ s C₂) (hM₁ : ∀ y ∈ s, ‖g₁ y‖ ≤ M₁)
    (hM₂ : ∀ y ∈ s, ‖g₂ y‖ ≤ M₂) :
    ScaleSlope (fun y => g₁ y * g₂ y) s (C₁ * M₂ + M₁ * C₂) := by
  intro y hy y' hy' hy0
  have e : g₁ y * g₂ y - g₁ y' * g₂ y' = (g₁ y - g₁ y') * g₂ y + g₁ y' * (g₂ y - g₂ y') := by ring
  have n1 : ‖(g₁ y - g₁ y') * g₂ y‖ * ‖y'‖ ≤ C₁ * ‖y - y'‖ * M₂ := by
    rw [norm_mul]
    calc ‖g₁ y - g₁ y'‖ * ‖g₂ y‖ * ‖y'‖ = ‖g₁ y - g₁ y'‖ * ‖y'‖ * ‖g₂ y‖ := by ring
      _ ≤ C₁ * ‖y - y'‖ * M₂ :=
        mul_le_mul (h₁ y hy y' hy' hy0) (hM₂ y hy) (norm_nonneg _)
          ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (h₁ y hy y' hy' hy0))
  have n2 : ‖g₁ y' * (g₂ y - g₂ y')‖ * ‖y'‖ ≤ M₁ * (C₂ * ‖y - y'‖) := by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM₁ y' hy') (h₂ y hy y' hy' hy0)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans (hM₁ y' hy'))
  calc ‖g₁ y * g₂ y - g₁ y' * g₂ y'‖ * ‖y'‖
      ≤ (‖(g₁ y - g₁ y') * g₂ y‖ + ‖g₁ y' * (g₂ y - g₂ y')‖) * ‖y'‖ := by
        rw [e]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ ≤ C₁ * ‖y - y'‖ * M₂ + M₁ * (C₂ * ‖y - y'‖) := by rw [add_mul]; exact add_le_add n1 n2
    _ = (C₁ * M₂ + M₁ * C₂) * ‖y - y'‖ := by ring

theorem scaleSlope_of_slopeBound {g : Space → ℂ} {L : ℝ≥0} {r : ℝ}
    (h : LipschitzOnWith L g (closedBall 0 r)) : ScaleSlope g (closedBall 0 r) (L * |r|) := by
  intro y hy y' hy' _
  have hd : ‖g y - g y'‖ ≤ L * ‖y - y'‖ := by
    simpa [dist_eq_norm] using h.dist_le_mul y hy y' hy'
  have hr : ‖y'‖ ≤ |r| := (by simpa using hy' : ‖y'‖ ≤ r).trans (le_abs_self r)
  calc ‖g y - g y'‖ * ‖y'‖ ≤ (L * ‖y - y'‖) * |r| :=
        mul_le_mul hd hr (norm_nonneg _) (by positivity)
    _ = L * |r| * ‖y - y'‖ := by ring

theorem slopeBound_mul_of_vanish {h g : Space → ℂ} {s : Set Space} {Lh : ℝ≥0} {K M C : ℝ}
    (hh : LipschitzOnWith Lh h s) (hK : ∀ y ∈ s, ‖h y‖ ≤ K * ‖y‖) (hM : ∀ y ∈ s, ‖g y‖ ≤ M)
    (hg : ScaleSlope g s C) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun y => h y * g y) s := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := Lh * M + K * C) fun y hy y' hy' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have e : h y * g y - h y' * g y' = (h y - h y') * g y + h y' * (g y - g y') := by ring
  have n1 : ‖(h y - h y') * g y‖ ≤ Lh * ‖y - y'‖ * M := by
    rw [norm_mul]
    have hd : ‖h y - h y'‖ ≤ Lh * ‖y - y'‖ := by
      simpa [dist_eq_norm] using hh.dist_le_mul y hy y' hy'
    exact mul_le_mul hd (hM y hy) (norm_nonneg _) (by positivity)
  have n2 : ‖h y' * (g y - g y')‖ ≤ K * C * ‖y - y'‖ := by
    rw [norm_mul]
    by_cases hy0 : y' = 0
    · subst hy0
      have : ‖h 0‖ ≤ 0 := by simpa using hK 0 hy'
      have h0 : ‖h 0‖ = 0 := le_antisymm this (norm_nonneg _)
      rw [h0, zero_mul]
      positivity
    · calc ‖h y'‖ * ‖g y - g y'‖ ≤ K * ‖y'‖ * ‖g y - g y'‖ :=
            mul_le_mul_of_nonneg_right (hK y' hy') (norm_nonneg _)
        _ = K * (‖g y - g y'‖ * ‖y'‖) := by ring
        _ ≤ K * (C * ‖y - y'‖) := mul_le_mul_of_nonneg_left (hg y hy y' hy' hy0) hK0
        _ = K * C * ‖y - y'‖ := by ring
  calc ‖h y * g y - h y' * g y'‖ ≤ ‖(h y - h y') * g y‖ + ‖h y' * (g y - g y')‖ := by
        rw [e]; exact norm_add_le _ _
    _ ≤ Lh * ‖y - y'‖ * M + K * C * ‖y - y'‖ := add_le_add n1 n2
    _ = (Lh * M + K * C) * ‖y - y'‖ := by ring

theorem slopeBound_mul {f g : Space → ℂ} {s : Set Space} {Lf Lg : ℝ≥0} {Mf Mg : ℝ}
    (hf : LipschitzOnWith Lf f s) (hg : LipschitzOnWith Lg g s) (hMf : ∀ y ∈ s, ‖f y‖ ≤ Mf)
    (hMg : ∀ y ∈ s, ‖g y‖ ≤ Mg) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun y => f y * g y) s := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := Lf * Mg + Mf * Lg) fun y hy y' hy' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have e : f y * g y - f y' * g y' = (f y - f y') * g y + f y' * (g y - g y') := by ring
  have hd1 : ‖f y - f y'‖ ≤ Lf * ‖y - y'‖ := by
    simpa [dist_eq_norm] using hf.dist_le_mul y hy y' hy'
  have hd2 : ‖g y - g y'‖ ≤ Lg * ‖y - y'‖ := by
    simpa [dist_eq_norm] using hg.dist_le_mul y hy y' hy'
  have n1 : ‖(f y - f y') * g y‖ ≤ Lf * ‖y - y'‖ * Mg := by
    rw [norm_mul]; exact mul_le_mul hd1 (hMg y hy) (norm_nonneg _) (by positivity)
  have n2 : ‖f y' * (g y - g y')‖ ≤ Mf * (Lg * ‖y - y'‖) := by
    rw [norm_mul]
    exact mul_le_mul (hMf y' hy') hd2 (norm_nonneg _) ((norm_nonneg _).trans (hMf y' hy'))
  calc ‖f y * g y - f y' * g y'‖ ≤ ‖(f y - f y') * g y‖ + ‖f y' * (g y - g y')‖ := by
        rw [e]; exact norm_add_le _ _
    _ ≤ Lf * ‖y - y'‖ * Mg + Mf * (Lg * ‖y - y'‖) := add_le_add n1 n2
    _ = (Lf * Mg + Mf * Lg) * ‖y - y'‖ := by ring

theorem bound_of_slopeBound {f : Space → ℂ} {L : ℝ≥0} {r : ℝ} (hf : LipschitzOnWith L f (closedBall 0 r)) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ closedBall (0 : Space) r, ‖f y‖ ≤ M := by
  refine ⟨‖f 0‖ + L * |r|, by positivity, fun y hy => ?_⟩
  have hr : 0 ≤ r := le_trans (norm_nonneg y) (by simpa using hy)
  have h0 : (0 : Space) ∈ closedBall (0 : Space) r := by simpa using hr
  have hd : ‖f y - f 0‖ ≤ L * ‖y - 0‖ := by
    simpa [dist_eq_norm] using hf.dist_le_mul y hy 0 h0
  have hy' : ‖y - 0‖ ≤ |r| := by rw [sub_zero, abs_of_nonneg hr]; simpa using hy
  calc ‖f y‖ ≤ ‖f 0‖ + ‖f y - f 0‖ := by
        have := norm_add_le (f 0) (f y - f 0); rwa [add_sub_cancel] at this
    _ ≤ ‖f 0‖ + L * |r| := by
        gcongr
        exact hd.trans (mul_le_mul_of_nonneg_left hy' (by positivity))

theorem slopeBound_of_contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) {s : Set E}
    (hs : IsCompact s) (hc : Convex ℝ s) : ∃ L : ℝ≥0, LipschitzOnWith L f s := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn
    ((hf.continuous_fderiv one_ne_zero).norm.continuousOn)
  refine ⟨Real.toNNReal M, hc.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hf.differentiable one_ne_zero x) (fun x hx => ?_)⟩
  have h := hM x hx
  rw [norm_norm] at h
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact h.trans (Real.le_coe_toNNReal M)

theorem continuous_of_ball_slopes {f : Space → ℂ}
    (h : ∀ r : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 r)) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  obtain ⟨L, hL⟩ := h (‖y‖ + 1)
  refine hL.continuousOn.continuousAt (closedBall_mem_nhds_of_mem ?_)
  simp

theorem chartCoord_nonneg (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) : 0 ≤ chartCoord P y := by
  unfold chartCoord; positivity

theorem chartCoord_le_one (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) : chartCoord P y ≤ 1 := by
  unfold chartCoord
  rw [div_le_one (by positivity)]
  linarith

theorem chartCoord_le_norm (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    chartCoord P y ≤ ‖y‖ / P.chartLength := by
  unfold chartCoord
  exact div_le_div_of_nonneg_left (norm_nonneg _) hL (by linarith [norm_nonneg y])

theorem chartCoord_dist (P : ShapeParams) (hL : 0 < P.chartLength) (y y' : Space) :
    |chartCoord P y - chartCoord P y'| ≤ ‖y - y'‖ / P.chartLength := by
  unfold chartCoord
  set a := ‖y‖
  set b := ‖y'‖
  set L := P.chartLength
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hab : |a - b| ≤ ‖y - y'‖ := abs_norm_sub_norm_le y y'
  have e : a / (a + L) - b / (b + L) = L * (a - b) / ((a + L) * (b + L)) := by
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : 0 < (a + L) * (b + L)),
    div_le_div_iff₀ (by positivity) hL]
  have hLL : L * L ≤ (a + L) * (b + L) := by nlinarith
  calc L * |a - b| * L = |a - b| * (L * L) := by ring
    _ ≤ ‖y - y'‖ * ((a + L) * (b + L)) :=
        mul_le_mul hab hLL (by positivity) (norm_nonneg _)

theorem chartCoord_slopeBound (P : ShapeParams) (hL : 0 < P.chartLength) :
    LipschitzWith (Real.toNNReal (1 / P.chartLength)) (chartCoord P) :=
  LipschitzWith.of_dist_le' fun y y' => by
    rw [Real.dist_eq, dist_eq_norm]
    calc |chartCoord P y - chartCoord P y'| ≤ ‖y - y'‖ / P.chartLength := chartCoord_dist P hL y y'
      _ = 1 / P.chartLength * ‖y - y'‖ := by ring

theorem abs_coord_le (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le y i
  rwa [Real.norm_eq_abs] at h

theorem abs_heightRatio_le_one (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, abs_zero]; exact zero_le_one
  · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact abs_coord_le y 2

theorem heightRatio_slope (y y' : Space) (hy' : y' ≠ 0) :
    |heightRatio y - heightRatio y'| * ‖y'‖ ≤ 2 * ‖y - y'‖ := by
  have e : ∀ z : Space, heightRatio z = ‖z‖⁻¹ • (z 2) := fun z => by
    simp [heightRatio, smul_eq_mul, div_eq_inv_mul]
  have h := scaled_sub_le (E := ℝ) (y 2) (y' 2) (norm_nonneg y) (norm_pos_iff.mpr hy')
    (by rw [Real.norm_eq_abs]; exact abs_coord_le y 2)
  rw [← e, ← e, Real.norm_eq_abs] at h
  have h1 : ‖y 2 - y' 2‖ ≤ ‖y - y'‖ := by
    have := PiLp.norm_apply_le (y - y') 2
    simpa using this
  have h2 : |‖y‖ - ‖y'‖| ≤ ‖y - y'‖ := abs_norm_sub_norm_le y y'
  linarith

def planeVec (y : Space) : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I

theorem planeVec_sq (y : Space) : ‖planeVec y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [planeVec, Complex.sq_norm, Complex.normSq_add_mul_I]

theorem norm_sq_three (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem planeVec_le (y : Space) : ‖planeVec y‖ ≤ ‖y‖ := by
  have h : ‖planeVec y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [planeVec_sq, norm_sq_three]; nlinarith [sq_nonneg (y 2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem planeVec_sub (y y' : Space) : planeVec y - planeVec y' = planeVec (y - y') := by
  simp only [planeVec, PiLp.sub_apply, Complex.ofReal_sub]
  ring

def unitPlane (y : Space) : ℂ := ((‖y‖⁻¹ : ℝ) : ℂ) * planeVec y

theorem unitPlane_le (y : Space) : ‖unitPlane y‖ ≤ 1 := by
  unfold unitPlane
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_mul]; exact zero_le_one
  · rw [inv_mul_le_iff₀ hpos, mul_one]; exact planeVec_le y

theorem unitPlane_slope (y y' : Space) (hy' : y' ≠ 0) :
    ‖unitPlane y - unitPlane y'‖ * ‖y'‖ ≤ 2 * ‖y - y'‖ := by
  have e : ∀ z : Space, unitPlane z = ‖z‖⁻¹ • planeVec z := fun z => by
    simp [unitPlane, Complex.real_smul]
  have h := scaled_sub_le (E := ℂ) (planeVec y) (planeVec y') (norm_nonneg y) (norm_pos_iff.mpr hy')
    (planeVec_le y)
  rw [← e, ← e] at h
  have h1 : ‖planeVec y - planeVec y'‖ ≤ ‖y - y'‖ := by rw [planeVec_sub]; exact planeVec_le _
  have h2 : |‖y‖ - ‖y'‖| ≤ ‖y - y'‖ := abs_norm_sub_norm_le y y'
  linarith

theorem one_sub_heightRatio_sq (y : Space) (hy : y ≠ 0) :
    1 - heightRatio y ^ 2 = ‖unitPlane y‖ ^ 2 := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  unfold unitPlane heightRatio
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, mul_pow, planeVec_sq]
  have h3 := norm_sq_three y
  field_simp
  linarith

theorem pointAngle_eq_arg (y : Space) (hy : y ≠ 0) : pointAngle y = Complex.arg (unitPlane y) := by
  unfold unitPlane
  rw [Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr hy))]
  rfl

def angleAxis (M : ℤ) (a : ℕ) (y : Space) : ℂ :=
  Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) * (((1 - heightRatio y ^ 2) ^ a : ℝ) : ℂ)

def angleDisc (M : ℤ) (a : ℕ) (w : ℂ) : ℂ :=
  Complex.exp ((((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) * (((‖w‖ ^ 2) ^ a : ℝ) : ℂ)

theorem angleAxis_eq (M : ℤ) (a : ℕ) (y : Space) (hy : y ≠ 0) :
    angleAxis M a y = angleDisc M a (unitPlane y) := by
  rw [angleAxis, angleDisc, pointAngle_eq_arg y hy, one_sub_heightRatio_sq y hy]

theorem norm_pow_sub_pow_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ n : ℕ, ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖
  | 0 => by simp
  | n + 1 => by
    have ih := norm_pow_sub_pow_le a b ha hb n
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    have hn : ‖a ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    rw [e]
    calc ‖a ^ n * (a - b) + (a ^ n - b ^ n) * b‖ ≤ ‖a ^ n‖ * ‖a - b‖ + ‖a ^ n - b ^ n‖ * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖a - b‖ + (n * ‖a - b‖) * 1 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

theorem norm_zpow_sub_zpow_le (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (M : ℤ) :
    ‖a ^ M - b ^ M‖ ≤ |(M : ℝ)| * ‖a - b‖ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg M
  · rw [zpow_natCast, zpow_natCast, Int.cast_natCast, Nat.abs_cast]
    exact norm_pow_sub_pow_le a b ha.le hb.le n
  · have ha0 : a ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero))
    have hb0 : b ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hb]; exact one_ne_zero))
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv' ha0 hb0, norm_mul, norm_mul,
      norm_inv, norm_inv, norm_pow, norm_pow, ha, hb, one_pow, inv_one, one_mul, mul_one,
      Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, norm_sub_rev a b]
    exact norm_pow_sub_pow_le b a hb.le ha.le n

theorem exp_arg_eq (M : ℤ) (w : ℂ) (hw : w ≠ 0) :
    Complex.exp ((((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) = (w / (‖w‖ : ℂ)) ^ M := by
  have h1 : (((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I = (M : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_int_mul]
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw)
  have h2 : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w / (‖w‖ : ℂ) := by
    rw [eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I w
  rw [h2]

theorem unit_div_slope (w w' : ℂ) (hw' : w' ≠ 0) :
    ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ * ‖w'‖ ≤ 2 * ‖w - w'‖ := by
  have e : ∀ z : ℂ, z / (‖z‖ : ℂ) = ‖z‖⁻¹ • z := fun z => by
    rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]
  rw [e, e]
  have h := scaled_sub_le (E := ℂ) w w' (norm_nonneg w) (norm_pos_iff.mpr hw') le_rfl
  have h2 : |‖w‖ - ‖w'‖| ≤ ‖w - w'‖ := abs_norm_sub_norm_le w w'
  linarith

theorem norm_unit_div (w : ℂ) (hw : w ≠ 0) : ‖w / (‖w‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.mpr hw)

theorem angleDisc_slope (M : ℤ) (a : ℕ) (ha : 1 ≤ a) (w w' : ℂ) (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) :
    ‖angleDisc M a w - angleDisc M a w'‖ ≤ (2 * a + 2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by
  set e : ℂ → ℂ := fun z => Complex.exp ((((M : ℝ) * Complex.arg z : ℝ) : ℂ) * Complex.I) with he
  set p : ℂ → ℝ := fun z => (‖z‖ ^ 2) ^ a with hp
  have hne : ∀ z, ‖e z‖ = 1 := fun z => Complex.norm_exp_ofReal_mul_I _
  have hp0 : ∀ z, 0 ≤ p z := fun z => by positivity
  have hpsq : ∀ z : ℂ, ‖z‖ ≤ 1 → p z ≤ ‖z‖ := fun z hz => by
    have h1 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    calc p z ≤ ‖z‖ ^ 2 := pow_le_of_le_one (sq_nonneg _) h1 (by omega)
      _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have hA : |p w - p w'| ≤ 2 * a * ‖w - w'‖ := by
    have h := abs_pow_sub_pow_le (‖w‖ ^ 2) (‖w'‖ ^ 2) a
    have hmax : max |‖w‖ ^ 2| |‖w'‖ ^ 2| ^ (a - 1) ≤ 1 := by
      refine pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le ?_ ?_)
      · rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (norm_nonneg _) hw
      · rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (norm_nonneg _) hw'
    have hd : |‖w‖ ^ 2 - ‖w'‖ ^ 2| ≤ 2 * ‖w - w'‖ := by
      have e2 : ‖w‖ ^ 2 - ‖w'‖ ^ 2 = (‖w‖ - ‖w'‖) * (‖w‖ + ‖w'‖) := by ring
      rw [e2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖w‖ + ‖w'‖)]
      have := abs_norm_sub_norm_le w w'
      nlinarith [abs_nonneg (‖w‖ - ‖w'‖), norm_nonneg w, norm_nonneg w']
    calc |p w - p w'| ≤ |‖w‖ ^ 2 - ‖w'‖ ^ 2| * a * max |‖w‖ ^ 2| |‖w'‖ ^ 2| ^ (a - 1) := h
      _ ≤ (2 * ‖w - w'‖) * a * 1 := by gcongr
      _ = 2 * a * ‖w - w'‖ := by ring
  have hB : ‖e w - e w'‖ * p w' ≤ (2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by
    by_cases hw'0 : w' = 0
    · have : p w' = 0 := by
        simp only [hp, hw'0, norm_zero]
        rw [zero_pow two_ne_zero, zero_pow (by omega)]
      rw [this, mul_zero]; positivity
    by_cases hw0 : w = 0
    · have h2 : ‖e w - e w'‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hne, hne]; norm_num)
      calc ‖e w - e w'‖ * p w' ≤ 2 * ‖w'‖ :=
            mul_le_mul h2 (hpsq w' hw') (hp0 _) zero_le_two
        _ = 2 * ‖w - w'‖ := by rw [hw0, zero_sub, norm_neg]
        _ ≤ (2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by nlinarith [abs_nonneg (M : ℝ), norm_nonneg (w - w')]
    · have ew : e w = (w / (‖w‖ : ℂ)) ^ M := exp_arg_eq M w hw0
      have ew' : e w' = (w' / (‖w'‖ : ℂ)) ^ M := exp_arg_eq M w' hw'0
      have hz := norm_zpow_sub_zpow_le _ _ (norm_unit_div w hw0) (norm_unit_div w' hw'0) M
      have hu := unit_div_slope w w' hw'0
      rw [ew, ew']
      calc ‖(w / (‖w‖ : ℂ)) ^ M - (w' / (‖w'‖ : ℂ)) ^ M‖ * p w'
          ≤ (|(M : ℝ)| * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖) * ‖w'‖ :=
            mul_le_mul hz (hpsq w' hw') (hp0 _) (by positivity)
        _ = |(M : ℝ)| * (‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ * ‖w'‖) := by ring
        _ ≤ |(M : ℝ)| * (2 * ‖w - w'‖) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        _ ≤ (2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by nlinarith [abs_nonneg (M : ℝ), norm_nonneg (w - w')]
  have e1 : angleDisc M a w - angleDisc M a w' =
      e w * ((p w - p w' : ℝ) : ℂ) + (e w - e w') * ((p w' : ℝ) : ℂ) := by
    simp only [angleDisc, he, hp]
    push_cast
    ring
  rw [e1]
  calc ‖e w * ((p w - p w' : ℝ) : ℂ) + (e w - e w') * ((p w' : ℝ) : ℂ)‖
      ≤ ‖e w‖ * |p w - p w'| + ‖e w - e w'‖ * p w' := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (hp0 w')]
    _ ≤ 1 * (2 * a * ‖w - w'‖) + (2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by
        rw [hne]; gcongr
    _ = (2 * a + 2 * |(M : ℝ)| + 2) * ‖w - w'‖ := by ring

theorem angleAxis_bound (M : ℤ) (a : ℕ) (y : Space) : ‖angleAxis M a y‖ ≤ 1 := by
  rw [angleAxis, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : heightRatio y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (abs_heightRatio_le_one y)
  have h0 : 0 ≤ 1 - heightRatio y ^ 2 := by linarith
  rw [abs_of_nonneg (pow_nonneg h0 _)]
  exact pow_le_one₀ h0 (by nlinarith [sq_nonneg (heightRatio y)])

theorem angleAxis_slope (M : ℤ) (a : ℕ) (h : 1 ≤ a ∨ (M = 0 ∧ a = 0)) :
    ∃ C, 0 ≤ C ∧ ScaleSlope (angleAxis M a) univ C := by
  rcases h with ha | ⟨hM, ha⟩
  · set K : ℝ := 2 * a + 2 * |(M : ℝ)| + 2
    have hK : 0 ≤ K := by positivity
    refine ⟨2 * K + 2 * 1, by positivity, scaleSlope_of_ne (by positivity)
      (fun y _ => angleAxis_bound M a y) fun y _ y' _ hy hy' => ?_⟩
    rw [angleAxis_eq M a y hy, angleAxis_eq M a y' hy']
    have h1 := angleDisc_slope M a ha (unitPlane y) (unitPlane y') (unitPlane_le y) (unitPlane_le y')
    have h2 := unitPlane_slope y y' hy'
    calc ‖angleDisc M a (unitPlane y) - angleDisc M a (unitPlane y')‖ * ‖y'‖
        ≤ (K * ‖unitPlane y - unitPlane y'‖) * ‖y'‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = K * (‖unitPlane y - unitPlane y'‖ * ‖y'‖) := by ring
      _ ≤ K * (2 * ‖y - y'‖) := mul_le_mul_of_nonneg_left h2 hK
      _ = 2 * K * ‖y - y'‖ := by ring
  · refine ⟨0, le_rfl, fun y _ y' _ _ => ?_⟩
    subst hM; subst ha
    simp [angleAxis]

def timeFactor (n : ℤ) (σ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * (n : ℝ) * σ : ℝ) : ℂ) * Complex.I)

theorem timeFactor_norm (n : ℤ) (σ : ℝ) : ‖timeFactor n σ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem timeFactor_periodic (n : ℤ) (σ : ℝ) : timeFactor n (σ + 1) = timeFactor n σ := by
  unfold timeFactor
  have e : ((2 * Real.pi * (n : ℝ) * (σ + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * σ : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem timeFactor_continuous (n : ℤ) : Continuous (timeFactor n) := by
  unfold timeFactor
  fun_prop

def radFactor (φ : ℝ → ℝ) (j : ℤ) (y : Space) : ℂ :=
  Complex.exp ((((j : ℝ) * φ (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)

theorem radFactor_norm (φ : ℝ → ℝ) (j : ℤ) (y : Space) : ‖radFactor φ j y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem radFactor_contDiff (φ : ℝ → ℝ) (hφ : IsRadialPhase φ) (j : ℤ) : ContDiff ℝ 1 (radFactor φ j) := by
  obtain ⟨δ, hδ, hs⟩ := hφ.smooth
  have h1 : ContDiff ℝ 1 (fun y : Space => φ (‖y‖ ^ 2)) :=
    (hs.of_le (by norm_num)).comp_contDiff (contDiff_norm_sq ℝ)
      (fun y => by simp only [mem_Ioi]; linarith [sq_nonneg ‖y‖])
  have h2 : ContDiff ℝ 1 (fun y : Space => (j : ℝ) * φ (‖y‖ ^ 2)) := contDiff_const.mul h1
  unfold radFactor
  exact ContDiff.cexp ((Complex.ofRealCLM.contDiff.comp h2).mul contDiff_const)

theorem radFactor_slopeBound (φ : ℝ → ℝ) (hφ : IsRadialPhase φ) (j : ℤ) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (radFactor φ j) (closedBall 0 r) :=
  slopeBound_of_contDiff (radFactor_contDiff φ hφ j) (isCompact_closedBall 0 r) (convex_closedBall 0 r)

def weightAt (P : ShapeParams) (lo hi : ℕ) (y : Space) : ℂ := weightPoly lo hi (chartCoord P y)

theorem weightAt_slopeBound (P : ShapeParams) (hL : 0 < P.chartLength) (lo hi : ℕ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (weightAt P lo hi) univ := by
  have hp : ContDiff ℝ 1 (fun t : ℝ => t ^ lo * (1 - t) ^ hi) := by fun_prop
  obtain ⟨Lp, hLp⟩ := slopeBound_of_contDiff hp isCompact_Icc (convex_Icc (0 : ℝ) 1)
  have hmap : MapsTo (chartCoord P) univ (Icc 0 1) := fun y _ =>
    ⟨chartCoord_nonneg P hL y, chartCoord_le_one P hL y⟩
  exact ⟨_, Complex.isometry_ofReal.lipschitz.comp_lipschitzOnWith
    (hLp.comp ((chartCoord_slopeBound P hL).lipschitzOnWith (s := univ)) hmap)⟩

theorem weightAt_bound (P : ShapeParams) (hL : 0 < P.chartLength) (lo hi : ℕ) (y : Space) :
    ‖weightAt P lo hi y‖ ≤ 1 := by
  have h0 := chartCoord_nonneg P hL y
  have h1 := chartCoord_le_one P hL y
  rw [weightAt, weightPoly, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have : 0 ≤ 1 - chartCoord P y := by linarith
                      positivity)]
  exact mul_le_one₀ (pow_le_one₀ h0 h1) (by have : 0 ≤ 1 - chartCoord P y := by linarith
                                            positivity)
    (pow_le_one₀ (by linarith) (by linarith))

theorem weightAt_vanish (P : ShapeParams) (hL : 0 < P.chartLength) (lo hi : ℕ) (hlo : 1 ≤ lo) (y : Space) :
    ‖weightAt P lo hi y‖ ≤ 1 / P.chartLength * ‖y‖ := by
  have h0 := chartCoord_nonneg P hL y
  have h1 := chartCoord_le_one P hL y
  have hs : 0 ≤ 1 - chartCoord P y := by linarith
  rw [weightAt, weightPoly, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc chartCoord P y ^ lo * (1 - chartCoord P y) ^ hi ≤ chartCoord P y * 1 :=
        mul_le_mul (pow_le_of_le_one h0 h1 (by omega)) (pow_le_one₀ hs (by linarith)) (by positivity) h0
    _ ≤ ‖y‖ / P.chartLength := by rw [mul_one]; exact chartCoord_le_norm P hL y
    _ = 1 / P.chartLength * ‖y‖ := by ring

def splineAt (P : ShapeParams) (S : Spline) (y : Space) : ℂ := S.evalHalf (chartCoord P y) (heightRatio y)

theorem spline_continuous {S : Spline} (hS : IsJoinedSpline 0 0 S) :
    Continuous (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) :=
  (joinedSplineSmooth 0 0 S hS).continuous

theorem spline_box {S : Spline} (hS : IsJoinedSpline 0 0 S) :
    ∃ A, 0 ≤ A ∧ ∀ t x t' x' : ℝ, |t| ≤ 1 → |x| ≤ 1 → |t'| ≤ 1 → |x'| ≤ 1 →
      ‖S.evalHalf t x - S.evalHalf t' x'‖ ≤ A * (|t - t'| + |x - x'|) := by
  obtain ⟨A, hA, h⟩ := CertCell.GivenShape.Internal.pieceEval_box S.mesh.tBreaks S.mesh.xBreaks
    S.piece (spline_continuous hS) 1
  exact ⟨A, hA, fun t x t' x' ht hx ht' hx' => h (t, x) (t', x') ht hx ht' hx'⟩

theorem spline_bounded (S : Spline) :
    ∃ M, 0 ≤ M ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖S.evalHalf t x‖ ≤ M :=
  CertCell.GivenShape.Internal.pieceEval_bounded S.mesh.tBreaks S.mesh.xBreaks S.piece 1

theorem chartCoord_abs_le (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) : |chartCoord P y| ≤ 1 := by
  rw [abs_of_nonneg (chartCoord_nonneg P hL y)]; exact chartCoord_le_one P hL y

theorem splineAt_bound (P : ShapeParams) (hL : 0 < P.chartLength) (S : Spline) :
    ∃ M, 0 ≤ M ∧ ∀ y, ‖splineAt P S y‖ ≤ M := by
  obtain ⟨M, hM, h⟩ := spline_bounded S
  exact ⟨M, hM, fun y => h _ _ (chartCoord_abs_le P hL y) (abs_heightRatio_le_one y)⟩

theorem splineAt_slope (P : ShapeParams) (hL : 0 < P.chartLength) {S : Spline} (hS : IsJoinedSpline 0 0 S)
    (r : ℝ) : ∃ C, 0 ≤ C ∧ ScaleSlope (splineAt P S) (closedBall 0 r) C := by
  obtain ⟨A, hA, h⟩ := spline_box hS
  refine ⟨A * (|r| / P.chartLength + 2), by positivity, fun y hy y' hy' hy0 => ?_⟩
  have hb := h _ _ _ _ (chartCoord_abs_le P hL y) (abs_heightRatio_le_one y)
    (chartCoord_abs_le P hL y') (abs_heightRatio_le_one y')
  have ht := chartCoord_dist P hL y y'
  have hx := heightRatio_slope y y' hy0
  have hr : ‖y'‖ ≤ |r| := (by simpa using hy' : ‖y'‖ ≤ r).trans (le_abs_self r)
  have e1 : |chartCoord P y - chartCoord P y'| * ‖y'‖ ≤ ‖y - y'‖ / P.chartLength * |r| :=
    mul_le_mul ht hr (norm_nonneg _) (by positivity)
  unfold splineAt
  calc ‖S.evalHalf (chartCoord P y) (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y')‖ * ‖y'‖
      ≤ A * (|chartCoord P y - chartCoord P y'| + |heightRatio y - heightRatio y'|) * ‖y'‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A * (|chartCoord P y - chartCoord P y'| * ‖y'‖ + |heightRatio y - heightRatio y'| * ‖y'‖) := by ring
    _ ≤ A * (‖y - y'‖ / P.chartLength * |r| + 2 * ‖y - y'‖) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 hx) hA
    _ = A * (|r| / P.chartLength + 2) * ‖y - y'‖ := by ring

theorem inner_breaks_pos (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∀ b ∈ (l.drop 1).dropLast, 0 < b := by
  intro b hb
  have hb' : b ∈ l.drop 1 := List.mem_of_mem_dropLast hb
  cases l with
  | nil => simp at h0
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp only [List.drop_succ_cons, List.drop_zero] at hb'
    exact (List.pairwise_cons.mp hs).1 b hb'

theorem exists_pos_le_all (L : List ℝ) (h : ∀ b ∈ L, 0 < b) : ∃ δ > 0, ∀ b ∈ L, δ ≤ b := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a rest ih =>
    obtain ⟨δ, hδ, hδb⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨min a δ, lt_min (h a (by simp)) hδ, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hδb b hb)

theorem cellIndex_pos_bound (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∃ δ > 0, ∀ t, 1 ≤ cellIndex l t → δ ≤ t := by
  obtain ⟨δ, hδ, hb⟩ := exists_pos_le_all _ (inner_breaks_pos l hs h0)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  unfold cellIndex at ht
  obtain ⟨b, hbm⟩ := List.exists_mem_of_length_pos ht
  rw [List.mem_filter] at hbm
  exact (hb b hbm.1).trans (by simpa using hbm.2)

theorem cellIndex_at_zero (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    cellIndex l 0 = 0 := by
  obtain ⟨δ, hδ, hb⟩ := cellIndex_pos_bound l hs h0
  by_contra h
  exact absurd (hb 0 (Nat.one_le_iff_ne_zero.mpr h)) (not_le.mpr hδ)

theorem cellIndex_lt_cellCount (l : List ℝ) (h1 : l.head? = some (-1)) (h2 : l.getLast? = some 1) (x : ℝ) :
    cellIndex l x < cellCount l := by
  have hlen : 2 ≤ l.length := by
    match l, h1, h2 with
    | [], h1, _ => simp at h1
    | [a], h1, h2 =>
      simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
      linarith
    | a :: b :: rest, _, _ => simp
  have := CertCell.GivenShape.Internal.cellIndex_le l x
  simp only [List.length_dropLast, List.length_drop] at this
  unfold cellCount
  omega

theorem row_value (P : MvPolynomial (Fin 2) ℂ) (c : ℂ) (h : atFirst 0 P = MvPolynomial.C c) (s : ℝ) :
    MvPolynomial.eval ![((0 : ℝ) : ℂ), (s : ℂ)] P = c := by
  have h1 := CertCell.GivenShape.Internal.JoinedSpline.evP_atFirst 0 P (0, s)
  rw [Complex.ofReal_zero, h] at h1
  unfold CertCell.GivenShape.Internal.JoinedSpline.evP at h1
  simpa using h1.symm

theorem row_deriv_zero (P : MvPolynomial (Fin 2) ℂ) (c : ℂ) (h : atFirst 0 P = MvPolynomial.C c) (x : ℝ) :
    MvPolynomial.eval ![((0 : ℝ) : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 P) = 0 := by
  have hd := CertCell.GivenShape.Internal.polyEval_hasDerivAt_second P 0 x
  have hf : (fun s : ℝ => MvPolynomial.eval ![((0 : ℝ) : ℂ), (s : ℂ)] P) = fun _ => c :=
    funext (row_value P c h)
  rw [hf] at hd
  exact hd.unique (hasDerivAt_const x c)

theorem spline_row_value {S : Spline} (hS : IsJoinedSpline 0 0 S) {c : ℂ}
    (hrow : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = MvPolynomial.C c) (x : ℝ) :
    S.evalHalf 0 x = c := by
  have hj := cellIndex_lt_cellCount S.mesh.xBreaks hS.mesh.x_first hS.mesh.x_last x
  have hi := cellIndex_at_zero S.mesh.tBreaks hS.mesh.t_sorted hS.mesh.t_first
  have := row_value _ c (hrow _ hj) x
  unfold Spline.evalHalf
  rw [hi]
  exact this

theorem spline_xslope {S : Spline} (hS : IsJoinedSpline 0 0 S) {c : ℂ}
    (hrow : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = MvPolynomial.C c) :
    ∃ C, 0 ≤ C ∧ ∀ t x x' : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → |x'| ≤ 1 →
      ‖S.evalHalf t x - S.evalHalf t x'‖ ≤ C * t * |x - x'| := by
  obtain ⟨δ, hδ, hδt⟩ := cellIndex_pos_bound S.mesh.tBreaks hS.mesh.t_sorted hS.mesh.t_first
  obtain ⟨M1, hStrain, hb1⟩ := CertCell.GivenShape.Internal.pieceEval_bounded S.mesh.tBreaks S.mesh.xBreaks
    (fun _ j => MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (S.piece 0 j))) 1
  obtain ⟨M2, hM2, hb2⟩ := CertCell.GivenShape.Internal.pieceEval_bounded S.mesh.tBreaks S.mesh.xBreaks
    (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) 1
  have hderiv : ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks
        (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) t x‖ ≤ (M1 + M2 / δ) * t := by
    intro t x ht0 ht1 hx
    have ht : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
    by_cases hci : cellIndex S.mesh.tBreaks t = 0
    · have hj := cellIndex_lt_cellCount S.mesh.xBreaks hS.mesh.x_first hS.mesh.x_last x
      set F : ℕ → ℕ → MvPolynomial (Fin 2) ℂ := fun _ j => MvPolynomial.pderiv 1 (S.piece 0 j) with hF
      have e1 : CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks
          (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) t x =
          CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F t x := by
        simp only [CertCell.GivenShape.Internal.pieceEval, hF, hci]
      have hzero : CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F 0 x = 0 :=
        row_deriv_zero _ c (hrow _ hj) x
      have hc1 : Continuous fun s => CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F s x :=
        continuous_iff_continuousAt.mpr fun s =>
          (CertCell.GivenShape.Internal.polyEval_hasDerivAt_first
            (MvPolynomial.pderiv 1 (S.piece 0 (cellIndex S.mesh.xBreaks x))) x s).continuousAt
      have hmv := CertCell.GivenShape.Internal.slice_diff_le hc1
        (fun s => CertCell.GivenShape.Internal.pieceEval_right_first S.mesh.tBreaks S.mesh.xBreaks F x s)
        (fun s hs => hb1 s x hs hx) t 0 ht (by simp)
      rw [e1]
      calc ‖CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F t x‖
          = ‖CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F t x -
              CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks F 0 x‖ := by
            rw [hzero, sub_zero]
        _ ≤ M1 * |t - 0| := hmv
        _ = M1 * t := by rw [sub_zero, abs_of_nonneg ht0]
        _ ≤ (M1 + M2 / δ) * t :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (div_nonneg hM2 hδ.le)) ht0
    · have hδle : δ ≤ t := hδt t (Nat.one_le_iff_ne_zero.mpr hci)
      calc ‖CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks
            (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) t x‖ ≤ M2 := hb2 t x ht hx
        _ = M2 / δ * δ := by field_simp
        _ ≤ M2 / δ * t := mul_le_mul_of_nonneg_left hδle (div_nonneg hM2 hδ.le)
        _ ≤ (M1 + M2 / δ) * t := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hStrain) ht0
  refine ⟨M1 + M2 / δ, by positivity, fun t x x' ht0 ht1 hx hx' => ?_⟩
  have hc2 : Continuous fun s => CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks S.piece t s :=
    Continuous.comp (g := fun z : ℝ × ℝ => S.evalHalf z.1 z.2) (f := fun s : ℝ => (t, s)) (spline_continuous hS)
      ((continuous_const : Continuous fun _ : ℝ => t).prodMk continuous_id)
  have key := CertCell.GivenShape.Internal.slice_diff_le
    (g := fun s => CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks S.piece t s)
    (g' := fun s => CertCell.GivenShape.Internal.pieceEval S.mesh.tBreaks S.mesh.xBreaks
      (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) t s) (R := 1) (M := (M1 + M2 / δ) * t) hc2
    (fun s => CertCell.GivenShape.Internal.pieceEval_right_second S.mesh.tBreaks S.mesh.xBreaks S.piece t s)
    (fun s hs => hderiv t s ht0 ht1 hs) x x' hx hx'
  exact key

theorem splineAt_slopeBound_of_row (P : ShapeParams) (hL : 0 < P.chartLength) {S : Spline}
    (hS : IsJoinedSpline 0 0 S) {c : ℂ}
    (hrow : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = MvPolynomial.C c) :
    ∃ L : ℝ≥0, LipschitzOnWith L (splineAt P S) univ := by
  obtain ⟨A, hA, hbox⟩ := spline_box hS
  obtain ⟨C, hC, hxs⟩ := spline_xslope hS hrow
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := (A + 2 * C) / P.chartLength) fun y _ y' _ => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  unfold splineAt
  have ht0' := chartCoord_nonneg P hL y'
  have ht1' := chartCoord_le_one P hL y'
  have e1 : ‖S.evalHalf (chartCoord P y) (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y)‖ ≤
      A * (‖y - y'‖ / P.chartLength) := by
    have h := hbox _ _ _ _ (chartCoord_abs_le P hL y) (abs_heightRatio_le_one y)
      (chartCoord_abs_le P hL y') (abs_heightRatio_le_one y)
    rw [sub_self, abs_zero, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (chartCoord_dist P hL y y') hA)
  have e2 : ‖S.evalHalf (chartCoord P y') (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y')‖ ≤
      2 * C / P.chartLength * ‖y - y'‖ := by
    have h := hxs _ _ _ ht0' ht1' (abs_heightRatio_le_one y) (abs_heightRatio_le_one y')
    refine h.trans ?_
    by_cases hy0 : y' = 0
    · have : chartCoord P y' = 0 := by simp [chartCoord, hy0]
      rw [this, mul_zero, zero_mul]
      positivity
    · have hs := heightRatio_slope y y' hy0
      have ht' := chartCoord_le_norm P hL y'
      calc C * chartCoord P y' * |heightRatio y - heightRatio y'|
          ≤ C * (‖y'‖ / P.chartLength) * |heightRatio y - heightRatio y'| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' hC) (abs_nonneg _)
        _ = C / P.chartLength * (|heightRatio y - heightRatio y'| * ‖y'‖) := by ring
        _ ≤ C / P.chartLength * (2 * ‖y - y'‖) :=
            mul_le_mul_of_nonneg_left hs (div_nonneg hC hL.le)
        _ = 2 * C / P.chartLength * ‖y - y'‖ := by ring
  calc ‖S.evalHalf (chartCoord P y) (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y')‖
      ≤ ‖S.evalHalf (chartCoord P y) (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y)‖ +
        ‖S.evalHalf (chartCoord P y') (heightRatio y) - S.evalHalf (chartCoord P y') (heightRatio y')‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * (‖y - y'‖ / P.chartLength) + 2 * C / P.chartLength * ‖y - y'‖ := add_le_add e1 e2
    _ = (A + 2 * C) / P.chartLength * ‖y - y'‖ := by ring

theorem splineAt_vanish (P : ShapeParams) (hL : 0 < P.chartLength) {S : Spline}
    (hS : IsJoinedSpline 0 0 S) (hrow : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = 0) :
    ∃ K, 0 ≤ K ∧ ∀ y, ‖splineAt P S y‖ ≤ K * ‖y‖ := by
  obtain ⟨A, hA, hbox⟩ := spline_box hS
  have hrow' : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = MvPolynomial.C 0 := by
    intro j hj; rw [hrow j hj, map_zero]
  refine ⟨A / P.chartLength, by positivity, fun y => ?_⟩
  have h0 := spline_row_value hS hrow' (heightRatio y)
  have h := hbox (chartCoord P y) (heightRatio y) 0 (heightRatio y) (chartCoord_abs_le P hL y)
    (abs_heightRatio_le_one y) (by simp) (abs_heightRatio_le_one y)
  rw [h0, sub_zero, sub_self, abs_zero, add_zero, sub_zero, abs_of_nonneg (chartCoord_nonneg P hL y)] at h
  unfold splineAt
  calc ‖S.evalHalf (chartCoord P y) (heightRatio y)‖ ≤ A * chartCoord P y := h
    _ ≤ A * (‖y‖ / P.chartLength) := mul_le_mul_of_nonneg_left (chartCoord_le_norm P hL y) hA
    _ = A / P.chartLength * ‖y‖ := by ring

def spaceValue (P : ShapeParams) (κ : FieldKey) (A : PressureKeyAmp) (y : Space) : ℂ :=
  radFactor P.radialPhase κ.phaseIndex y *
    (angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y *
      (weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y))

theorem pressureKeyValue_split (P : ShapeParams) (κ : FieldKey) (A : PressureKeyAmp) (σ : ℝ) (y : Space) :
    pressureKeyValue P κ A σ y = timeFactor (labelTime κ.label) σ * spaceValue P κ A y := by
  simp only [pressureKeyValue, keyPhase, spaceValue, timeFactor, radFactor, angleAxis, weightAt, splineAt]
  rw [Complex.ofReal_add, Complex.ofReal_add, add_mul, add_mul, Complex.exp_add, Complex.exp_add]
  ring

theorem spaceValue_slopeBound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : PressureKeyAmp)
    (hJ : IsJoinedSpline 0 0 A.amp)
    (hB : 1 ≤ A.axisOrder ∨ (labelAzimuth P.azimuthOrder κ.label = 0 ∧ A.axisOrder = 0))
    (hO : 1 ≤ A.lowOrder ∨ (∀ j < cellCount A.amp.mesh.xBreaks, atFirst 0 (A.amp.piece 0 j) = 0) ∨
      ((labelAzimuth P.azimuthOrder κ.label = 0 ∧ A.axisOrder = 0) ∧
        ∃ c : ℂ, ∀ j < cellCount A.amp.mesh.xBreaks, atFirst 0 (A.amp.piece 0 j) = MvPolynomial.C c))
    (r : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L (spaceValue P κ A) (closedBall 0 r) := by
  have hL := hP.chartLength_pos
  obtain ⟨Lr, hLr⟩ := radFactor_slopeBound P.radialPhase hP.phase κ.phaseIndex r
  obtain ⟨Lw, hLw⟩ := weightAt_slopeBound P hL A.lowOrder A.highOrder
  have hLw' : LipschitzOnWith Lw (weightAt P A.lowOrder A.highOrder) (closedBall 0 r) :=
    hLw.mono (subset_univ _)
  obtain ⟨Ms, hMs0, hMs⟩ := splineAt_bound P hL A.amp
  obtain ⟨CB, hCB0, hCB⟩ := angleAxis_slope (labelAzimuth P.azimuthOrder κ.label) A.axisOrder hB
  have hCB' : ScaleSlope (angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder) (closedBall 0 r) CB :=
    scaleSlope_mono hCB (subset_univ _)
  obtain ⟨Cs, hCs0, hCs⟩ := splineAt_slope P hL hJ r
  have hG : ∃ L : ℝ≥0, LipschitzOnWith L (fun y => angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y *
      (weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y)) (closedBall 0 r) := by
    rcases hO with hlo | hrow | ⟨⟨hM0, ha0⟩, c, hrow⟩
    · have hslope := scaleSlope_mul hCB' hCs (M₁ := 1) (M₂ := Ms) (fun y _ => angleAxis_bound _ _ y)
        (fun y _ => hMs y)
      obtain ⟨L, hL'⟩ := slopeBound_mul_of_vanish hLw' (fun y _ => weightAt_vanish P hL _ _ hlo y)
        (M := 1 * Ms) (fun y _ => by
          rw [norm_mul]; exact mul_le_mul (angleAxis_bound _ _ y) (hMs y) (norm_nonneg _) zero_le_one)
        hslope (by positivity) (by positivity)
      refine ⟨L, ?_⟩
      have e : (fun y => angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y *
          (weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y)) =
          fun y => weightAt P A.lowOrder A.highOrder y *
            (angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y * splineAt P A.amp y) := by
        funext y; ring
      rw [e]; exact hL'
    · obtain ⟨Ls, hLs⟩ := splineAt_slopeBound_of_row P hL hJ (c := 0) (fun j hj => by rw [hrow j hj, map_zero])
      obtain ⟨K, hK0, hK⟩ := splineAt_vanish P hL hJ hrow
      have hWs := scaleSlope_of_slopeBound hLw'
      have hslope := scaleSlope_mul hCB' hWs (M₁ := 1) (M₂ := 1) (fun y _ => angleAxis_bound _ _ y)
        (fun y _ => weightAt_bound P hL _ _ y)
      obtain ⟨L, hL'⟩ := slopeBound_mul_of_vanish (hLs.mono (subset_univ _)) (fun y _ => hK y)
        (M := 1 * 1) (fun y _ => by
          rw [norm_mul]
          exact mul_le_mul (angleAxis_bound _ _ y) (weightAt_bound P hL _ _ y) (norm_nonneg _) zero_le_one)
        hslope hK0 (by positivity)
      refine ⟨L, ?_⟩
      have e : (fun y => angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y *
          (weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y)) =
          fun y => splineAt P A.amp y *
            (angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y * weightAt P A.lowOrder A.highOrder y) := by
        funext y; ring
      rw [e]; exact hL'
    · obtain ⟨Ls, hLs⟩ := splineAt_slopeBound_of_row P hL hJ hrow
      have hone : ∀ y, angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y = 1 := by
        intro y; rw [hM0, ha0]; simp [angleAxis]
      obtain ⟨L, hL'⟩ := slopeBound_mul hLw' (hLs.mono (subset_univ _)) (Mf := 1) (Mg := Ms)
        (fun y _ => weightAt_bound P hL _ _ y) (fun y _ => hMs y)
      refine ⟨L, ?_⟩
      have e : (fun y => angleAxis (labelAzimuth P.azimuthOrder κ.label) A.axisOrder y *
          (weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y)) =
          fun y => weightAt P A.lowOrder A.highOrder y * splineAt P A.amp y := by
        funext y; rw [hone, one_mul]
      rw [e]; exact hL'
  obtain ⟨LG, hLG⟩ := hG
  obtain ⟨MG, hMG0, hMG⟩ := bound_of_slopeBound hLG
  obtain ⟨L, hL'⟩ := slopeBound_mul hLr hLG (Mf := 1) (Mg := MG) (fun y _ => (radFactor_norm _ _ y).le) hMG
  exact ⟨L, hL'⟩

end Internal

theorem pressureFieldRegular_holds : PressureFieldRegularHolds := by
  intro P D hP hD
  have hkey : ∀ κ ∈ D.keys, ∀ r : ℝ, ∃ L : ℝ≥0,
      LipschitzOnWith L (Internal.spaceValue P κ (D.amp κ)) (closedBall 0 r) := by
    intro κ hκ r
    refine Internal.spaceValue_slopeBound P hP κ (D.amp κ) (hD.amp_class κ hκ) ?_ ?_ r
    · by_cases h1 : κ.label.1 = 0
      · right; exact ⟨by simp [labelAzimuth, h1], hD.typeTwo_axis κ hκ h1⟩
      · left; exact hD.typeOne_axis κ hκ h1
    · by_cases h1 : κ.label.1 = 0
      · by_cases hlo : (D.amp κ).lowOrder = 0
        · right; right
          exact ⟨⟨by simp [labelAzimuth, h1], hD.typeTwo_axis κ hκ h1⟩, hD.typeTwo_origin κ hκ h1 hlo⟩
        · left; omega
      · rcases hD.typeOne_origin κ hκ h1 with h | h
        · left; exact h
        · right; left; exact h
  have hsplit : ∀ σ y, shapePressure P D σ y = (∑ κ ∈ D.keys,
      Internal.timeFactor (labelTime κ.label) σ * Internal.spaceValue P κ (D.amp κ) y).re := by
    intro σ y
    unfold shapePressure
    simp only [Internal.pressureKeyValue_split]
  have hcont : ∀ κ ∈ D.keys, Continuous (Internal.spaceValue P κ (D.amp κ)) :=
    fun κ hκ => Internal.continuous_of_ball_slopes (hkey κ hκ)
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun z : ℝ × Space => shapePressure P D z.1 z.2) = fun z => (∑ κ ∈ D.keys,
        Internal.timeFactor (labelTime κ.label) z.1 * Internal.spaceValue P κ (D.amp κ) z.2).re :=
      funext fun z => hsplit z.1 z.2
    rw [e]
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun κ hκ =>
      ((Internal.timeFactor_continuous _).comp continuous_fst).mul ((hcont κ hκ).comp continuous_snd))
  · intro σ y
    rw [hsplit, hsplit]
    simp only [Internal.timeFactor_periodic]
  · intro r
    have hch : ∀ κ, ∃ L : ℝ≥0, κ ∈ D.keys →
        LipschitzOnWith L (Internal.spaceValue P κ (D.amp κ)) (closedBall 0 r) := by
      intro κ
      by_cases hκ : κ ∈ D.keys
      · obtain ⟨L, hL⟩ := hkey κ hκ r
        exact ⟨L, fun _ => hL⟩
      · exact ⟨0, fun h => absurd h hκ⟩
    choose Lk hLk using hch
    refine ⟨∑ κ ∈ D.keys, Lk κ, fun σ => LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_⟩
    rw [hsplit, hsplit, Real.dist_eq, ← Complex.sub_re, ← Finset.sum_sub_distrib]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    rw [NNReal.coe_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun κ hκ => ?_
    rw [← mul_sub, norm_mul, Internal.timeFactor_norm, one_mul, ← dist_eq_norm]
    exact (hLk κ hκ).dist_le_mul y hy y' hy'

end Instantiation

end CellReduction

end Breakdown

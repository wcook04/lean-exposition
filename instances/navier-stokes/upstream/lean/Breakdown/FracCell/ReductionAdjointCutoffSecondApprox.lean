import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCell.AdjointConvectionPairing

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace CutoffSecondApproxInternal

theorem entrySq_le_norm (A : Space →L[ℝ] Space) : entrySq A ≤ 3 * ‖A‖ ^ 2 := by
  unfold entrySq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
    have := A.le_opNorm (unitVector i)
    rw [FracInternal.ConvectionPairing.unit_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp

theorem fullSecondSq_le_norm (B : Space →L[ℝ] Space →L[ℝ] Space) :
    CellCert.fullSecondSq B ≤ 9 * ‖B‖ ^ 2 := by
  unfold CellCert.fullSecondSq
  have h : ∀ a b : Fin 3, ‖B (unitVector a) (unitVector b)‖ ^ 2 ≤ ‖B‖ ^ 2 := fun a b => by
    have h1 := (B (unitVector a)).le_opNorm (unitVector b)
    have h2 := B.le_opNorm (unitVector a)
    rw [FracInternal.ConvectionPairing.unit_norm, mul_one] at h1 h2
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  calc ∑ a : Fin 3, ∑ b : Fin 3, ‖B (unitVector a) (unitVector b)‖ ^ 2 ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, ‖B‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b
    _ = 9 * ‖B‖ ^ 2 := by norm_num; ring

theorem norm_sq_le_entrySq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ entrySq A := by
  have h0 : 0 ≤ entrySq A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have : ‖A‖ ≤ Real.sqrt (entrySq A) := ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => by
    rw [← Real.sqrt_sq (norm_nonneg (A x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul h0]
    exact Real.sqrt_le_sqrt (LinearStateClosedInternal.clm_sq_le A x)
  calc ‖A‖ ^ 2 ≤ Real.sqrt (entrySq A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = entrySq A := Real.sq_sqrt h0

theorem norm_sq_le_fullSecondSq (B : Space →L[ℝ] Space →L[ℝ] Space) : ‖B‖ ^ 2 ≤ CellCert.fullSecondSq B := by
  have h0 : 0 ≤ CellCert.fullSecondSq B :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have key : ∀ x, entrySq (B x) ≤ CellCert.fullSecondSq B * ‖x‖ ^ 2 := by
    intro x
    unfold entrySq CellCert.fullSecondSq
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    have := LinearStateClosedInternal.clm_sq_le (B.flip (unitVector b)) x
    simpa [entrySq, ContinuousLinearMap.flip_apply] using this
  have : ‖B‖ ≤ Real.sqrt (CellCert.fullSecondSq B) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => by
      rw [← Real.sqrt_sq (norm_nonneg (B x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul h0]
      exact Real.sqrt_le_sqrt ((norm_sq_le_entrySq (B x)).trans (key x))
  calc ‖B‖ ^ 2 ≤ Real.sqrt (CellCert.fullSecondSq B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = CellCert.fullSecondSq B := Real.sq_sqrt h0

theorem smooth_weak {w : Space → Space} (hw : ContDiff ℝ 1 w) : IsWeakGradientOf w (fun y => fderiv ℝ w y) := by
  intro φ hφ j
  obtain ⟨hφs, hφc⟩ := hφ
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hφ' : Continuous (fun y => fderiv ℝ φ y) := hφs.continuous_fderiv (by simp)
  have hw' : Continuous (fun y => fderiv ℝ w y) := hw.continuous_fderiv one_ne_zero
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • w y) :=
    ((hφ'.clm_apply continuous_const).smul hw.continuous).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have i2 : Integrable (fun y => φ y • fderiv ℝ w y (unitVector j)) :=
    (hφs.continuous.smul (hw'.clm_apply continuous_const)).integrable_of_hasCompactSupport hφc.smul_right
  have i3 : Integrable (fun y => φ y • w y) :=
    (hφs.continuous.smul hw.continuous).integrable_of_hasCompactSupport hφc.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3 (fun x _ => hφd x)
    (fun x _ => hwd x)
  rw [h, neg_neg]

theorem scale_eq {r : ℝ} (hr : 0 < r) :
    radialCutoff r = radialCutoff 1 ∘ (r⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  funext x
  simp only [radialCutoff, Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_one]
  rw [div_eq_inv_mul]

theorem iter_cutoff_le (i : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ r, 0 < r → ∀ x,
    ‖iteratedFDeriv ℝ i (radialCutoff r) x‖ ≤ c * r⁻¹ ^ i := by
  obtain ⟨C, hC⟩ := ((contDiff_radialCutoff one_pos).continuous_iteratedFDeriv (m := i) (by first | exact_mod_cast le_top | exact WithTop.coe_le_coe.2 le_top)).bounded_above_of_compact_support
    ((hasCompactSupport_radialCutoff one_pos).iteratedFDeriv (𝕜 := ℝ) i)
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun r hr x => ?_⟩
  have hn : ‖r⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ r⁻¹ := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    exact mul_le_of_le_one_right (inv_pos.2 hr).le ContinuousLinearMap.norm_id_le
  rw [scale_eq hr, ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_radialCutoff one_pos) x (by first | exact_mod_cast le_top | exact WithTop.coe_le_coe.2 le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) hn i) (by positivity) ((norm_nonneg _).trans (hC 0))

theorem iter_cutoff_far {r : ℝ} (hr : 0 < r) {x : Space} (hx : 2 * r < ‖x‖) (i : ℕ) :
    iteratedFDeriv ℝ i (radialCutoff r) x = 0 := by
  have h : radialCutoff r =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
    exact radialCutoff_eq_zero hr hz.le
  rw [(h.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds]
  simp

theorem cut_term {c : ℝ} (hc : 0 ≤ c) {R : ℝ} (hR : 1 ≤ R) {i : ℕ} (hi : 1 ≤ i)
    (hC : ∀ x, ‖iteratedFDeriv ℝ i (radialCutoff R) x‖ ≤ c * R⁻¹ ^ i) {y : Space} (hy : y ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) : ‖iteratedFDeriv ℝ i (radialCutoff R) y‖ * a ≤ 2 * c * (a / ‖y‖) := by
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  by_cases hfar : 2 * R < ‖y‖
  · rw [iter_cutoff_far hR0 hfar i, norm_zero, zero_mul]
    positivity
  · push_neg at hfar
    have h1 : R⁻¹ ^ i ≤ R⁻¹ := pow_le_of_le_one (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR) (by omega)
    have h2 : R⁻¹ ≤ 2 / ‖y‖ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hR0 hy0]
      linarith
    calc ‖iteratedFDeriv ℝ i (radialCutoff R) y‖ * a ≤ (c * (2 / ‖y‖)) * a := by
          gcongr
          exact (hC y).trans (mul_le_mul_of_nonneg_left (h1.trans h2) hc)
      _ = 2 * c * (a / ‖y‖) := by ring


theorem entrySq_cont : Continuous entrySq := by
  unfold entrySq
  exact continuous_finset_sum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm.pow 2)

theorem fullSecondSq_cont : Continuous CellCert.fullSecondSq := by
  unfold CellCert.fullSecondSq
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    (((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2)

theorem iter_two (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem first_bound {w : Space → Space} (hw : ContDiff ℝ ∞ w) {c1 : ℝ} (hc1 : 0 ≤ c1)
    (hC1 : ∀ r, 0 < r → ∀ x, ‖iteratedFDeriv ℝ 1 (radialCutoff r) x‖ ≤ c1 * r⁻¹ ^ 1)
    {R : ℝ} (hR : 1 ≤ R) {y : Space} (hy : y ≠ 0) :
    ‖fderiv ℝ (fun z => radialCutoff R z • w z) y‖ ≤ ‖fderiv ℝ w y‖ + 2 * c1 * (‖w y‖ / ‖y‖) := by
  have hR0 : 0 < R := by linarith
  have hL := norm_iteratedFDeriv_smul_le (contDiff_radialCutoff hR0) hw y (n := 1) (by first | exact_mod_cast le_top | exact WithTop.coe_le_coe.2 le_top)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, one_mul, Nat.sub_zero, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] at hL
  rw [show (1 : ℕ) - 1 = 0 from rfl, norm_iteratedFDeriv_zero] at hL
  have h0 : ‖radialCutoff R y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have ht := cut_term hc1 hR le_rfl (hC1 R hR0) hy ‖w y‖ (norm_nonneg _)
  rw [norm_iteratedFDeriv_one] at ht
  exact hL.trans (add_le_add (mul_le_of_le_one_left (norm_nonneg _) h0) ht)

theorem second_bound {w : Space → Space} (hw : ContDiff ℝ ∞ w) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hC1 : ∀ r, 0 < r → ∀ x, ‖iteratedFDeriv ℝ 1 (radialCutoff r) x‖ ≤ c1 * r⁻¹ ^ 1)
    (hC2 : ∀ r, 0 < r → ∀ x, ‖iteratedFDeriv ℝ 2 (radialCutoff r) x‖ ≤ c2 * r⁻¹ ^ 2)
    {R : ℝ} (hR : 1 ≤ R) {y : Space} (hy : y ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff R z • w z)) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ w) y‖ + 2 * c1 * ‖fderiv ℝ w y‖ + 2 * c2 * (‖w y‖ / ‖y‖) := by
  have hR0 : 0 < R := by linarith
  have hw2 : ContDiff ℝ 2 w := hw.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc2' : ContDiff ℝ 2 (radialCutoff R) := (contDiff_radialCutoff hR0).of_le (WithTop.coe_le_coe.mpr le_top)
  have hL := norm_iteratedFDeriv_smul_le hc2' hw2 y (n := 2) (by first | simp | norm_cast | exact le_rfl)
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] at hL
  rw [show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 2 = 0 from rfl, norm_iteratedFDeriv_one,
    norm_iteratedFDeriv_zero, ← Real.norm_eq_abs] at hL
  rw [iter_two, iter_two] at hL
  have h0 : ‖radialCutoff R y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have h1 : ‖fderiv ℝ (radialCutoff R) y‖ ≤ c1 := by
    have := hC1 R hR0 y
    rw [norm_iteratedFDeriv_one, pow_one] at this
    exact this.trans (mul_le_of_le_one_right hc1 (inv_le_one_of_one_le₀ hR))
  have ht := cut_term hc2 hR (by norm_num) (hC2 R hR0) hy ‖w y‖ (norm_nonneg _)
  have hm : 2 * ‖fderiv ℝ (radialCutoff R) y‖ * ‖fderiv ℝ w y‖ ≤ 2 * c1 * ‖fderiv ℝ w y‖ := by
    gcongr
  have hz : ‖radialCutoff R y‖ * ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ ‖fderiv ℝ (fderiv ℝ w) y‖ :=
    mul_le_of_le_one_left (norm_nonneg _) h0
  linarith

end CutoffSecondApproxInternal


def CutoffSecondApproxStatement : Prop :=
  ∀ w : Space → Space, ContDiff ℝ ∞ w → MemLp w 6 volume → Integrable (fun y => entrySq (fderiv ℝ w y)) →
    Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y)) → ∀ ε : ℝ, 0 < ε →
    ∃ u : Space → Space, IsTestVectorField u ∧
      Integrable (fun y => entrySq (fderiv ℝ u y - fderiv ℝ w y)) ∧
      ∫ y, entrySq (fderiv ℝ u y - fderiv ℝ w y) ≤ ε ∧
      Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ w) y)) ∧
      ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ w) y) ≤ ε

open CutoffSecondApproxInternal in
theorem cutoffSecondApprox : CutoffSecondApproxStatement := by
  intro w hw h6 hE hS ε hε
  obtain ⟨c1, hc1, hC1⟩ := iter_cutoff_le 1
  obtain ⟨c2, hc2, hC2⟩ := iter_cutoff_le 2
  have hq : Integrable (fun y => ‖w y‖ ^ 2 / ‖y‖ ^ 2) :=
    (inverseSquareBound w (fun y => fderiv ℝ w y) hw.continuous.aestronglyMeasurable h6 hE
      (smooth_weak (hw.of_le (by simp)))).1
  have hR0 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hR1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  set u : ℕ → Space → Space := fun k z => radialCutoff ((k : ℝ) + 1) z • w z with hu_def
  have hu : ∀ k, ContDiff ℝ ∞ (u k) := fun k => (contDiff_radialCutoff (hR0 k)).smul hw
  have hut : ∀ k, IsTestVectorField (u k) := fun k =>
    ⟨hu k, (hasCompactSupport_radialCutoff (hR0 k)).smul_right⟩
  have hev : ∀ y, ∀ᶠ k in atTop, fderiv ℝ (u k) y = fderiv ℝ w y ∧
      fderiv ℝ (fderiv ℝ (u k)) y = fderiv ℝ (fderiv ℝ w) y := by
    intro y
    filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with k hk
    have hy : ‖y‖ < (k : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : u k =ᶠ[𝓝 y] w := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
      simp only [hu_def, radialCutoff_eq_one (hR0 k) hz.le, one_smul]
    exact ⟨he.fderiv_eq, he.fderiv.fderiv_eq⟩
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have b1 : ∀ k y, y ≠ 0 → entrySq (fderiv ℝ (u k) y - fderiv ℝ w y) ≤
      24 * entrySq (fderiv ℝ w y) + 24 * c1 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2) := by
    intro k y hy
    have hb : ‖fderiv ℝ (u k) y‖ ≤ ‖fderiv ℝ w y‖ + 2 * c1 * (‖w y‖ / ‖y‖) :=
      first_bound hw hc1 hC1 (hR1 k) hy
    have hn := norm_sub_le (fderiv ℝ (u k) y) (fderiv ℝ w y)
    have hDw := norm_sq_le_entrySq (fderiv ℝ w y)
    have e1 := entrySq_le_norm (fderiv ℝ (u k) y - fderiv ℝ w y)
    have ht0 : 0 ≤ ‖w y‖ / ‖y‖ := by positivity
    have hd : ‖fderiv ℝ (u k) y - fderiv ℝ w y‖ ≤ 2 * ‖fderiv ℝ w y‖ + 2 * c1 * (‖w y‖ / ‖y‖) := by linarith
    rw [← div_pow]
    calc entrySq (fderiv ℝ (u k) y - fderiv ℝ w y) ≤ 3 * ‖fderiv ℝ (u k) y - fderiv ℝ w y‖ ^ 2 := e1
      _ ≤ 3 * (2 * ‖fderiv ℝ w y‖ + 2 * c1 * (‖w y‖ / ‖y‖)) ^ 2 := by gcongr
      _ ≤ 24 * ‖fderiv ℝ w y‖ ^ 2 + 24 * c1 ^ 2 * (‖w y‖ / ‖y‖) ^ 2 := by
          nlinarith [sq_nonneg (‖fderiv ℝ w y‖ - c1 * (‖w y‖ / ‖y‖))]
      _ ≤ 24 * entrySq (fderiv ℝ w y) + 24 * c1 ^ 2 * (‖w y‖ / ‖y‖) ^ 2 := by gcongr
  have b2 : ∀ k y, y ≠ 0 → CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y) ≤
      108 * CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y) + 108 * c1 ^ 2 * entrySq (fderiv ℝ w y) +
        108 * c2 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2) := by
    intro k y hy
    have hb : ‖fderiv ℝ (fderiv ℝ (u k)) y‖ ≤
        ‖fderiv ℝ (fderiv ℝ w) y‖ + 2 * c1 * ‖fderiv ℝ w y‖ + 2 * c2 * (‖w y‖ / ‖y‖) :=
      second_bound hw hc1 hc2 hC1 hC2 (hR1 k) hy
    have hn := norm_sub_le (fderiv ℝ (fderiv ℝ (u k)) y) (fderiv ℝ (fderiv ℝ w) y)
    have hDw := norm_sq_le_entrySq (fderiv ℝ w y)
    have hD2w := norm_sq_le_fullSecondSq (fderiv ℝ (fderiv ℝ w) y)
    have e1 := fullSecondSq_le_norm (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y)
    have ht0 : 0 ≤ ‖w y‖ / ‖y‖ := by positivity
    have hd : ‖fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y‖ ≤
        2 * ‖fderiv ℝ (fderiv ℝ w) y‖ + 2 * c1 * ‖fderiv ℝ w y‖ + 2 * c2 * (‖w y‖ / ‖y‖) := by
      nlinarith [norm_nonneg (fderiv ℝ w y)]
    rw [← div_pow]
    calc CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y)
        ≤ 9 * ‖fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y‖ ^ 2 := e1
      _ ≤ 9 * (2 * ‖fderiv ℝ (fderiv ℝ w) y‖ + 2 * c1 * ‖fderiv ℝ w y‖ + 2 * c2 * (‖w y‖ / ‖y‖)) ^ 2 := by
          gcongr
      _ ≤ 108 * ‖fderiv ℝ (fderiv ℝ w) y‖ ^ 2 + 108 * c1 ^ 2 * ‖fderiv ℝ w y‖ ^ 2 +
            108 * c2 ^ 2 * (‖w y‖ / ‖y‖) ^ 2 := by
          nlinarith [sq_nonneg (‖fderiv ℝ (fderiv ℝ w) y‖ - c1 * ‖fderiv ℝ w y‖),
            sq_nonneg (‖fderiv ℝ (fderiv ℝ w) y‖ - c2 * (‖w y‖ / ‖y‖)),
            sq_nonneg (c1 * ‖fderiv ℝ w y‖ - c2 * (‖w y‖ / ‖y‖))]
      _ ≤ _ := by gcongr
  have F1i : Integrable (fun y => 24 * entrySq (fderiv ℝ w y) + 24 * c1 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2)) :=
    (hE.const_mul 24).add (hq.const_mul _)
  have F2i : Integrable (fun y => 108 * CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y) +
      108 * c1 ^ 2 * entrySq (fderiv ℝ w y) + 108 * c2 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2)) :=
    ((hS.const_mul 108).add (hE.const_mul _)).add (hq.const_mul _)
  have hwd1 : Continuous (fun y => fderiv ℝ w y) := hw.continuous_fderiv (by simp)
  have hwd2 : Continuous (fun y => fderiv ℝ (fderiv ℝ w) y) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hw).2).2.continuous
  have m1 : ∀ k, AEStronglyMeasurable (fun y => entrySq (fderiv ℝ (u k) y - fderiv ℝ w y)) volume := fun k =>
    (entrySq_cont.comp (((hu k).continuous_fderiv (by simp)).sub hwd1)).aestronglyMeasurable
  have m2 : ∀ k, AEStronglyMeasurable
      (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y)) volume := fun k =>
    (fullSecondSq_cont.comp
      ((contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 (hu k)).2).2.continuous.sub hwd2)).aestronglyMeasurable
  have nn1 : ∀ k y, 0 ≤ entrySq (fderiv ℝ (u k) y - fderiv ℝ w y) := fun k y =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have nn2 : ∀ k y, 0 ≤ CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y) :=
    fun k y => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have d1 : ∀ k, ∀ᵐ y ∂volume, ‖entrySq (fderiv ℝ (u k) y - fderiv ℝ w y)‖ ≤
      24 * entrySq (fderiv ℝ w y) + 24 * c1 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2) := fun k =>
    hne.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (nn1 k y)]
      exact b1 k y hy
  have d2 : ∀ k, ∀ᵐ y ∂volume, ‖CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y)‖ ≤
      108 * CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y) + 108 * c1 ^ 2 * entrySq (fderiv ℝ w y) +
        108 * c2 ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2) := fun k =>
    hne.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (nn2 k y)]
      exact b2 k y hy
  have T1 : Tendsto (fun k => ∫ y, entrySq (fderiv ℝ (u k) y - fderiv ℝ w y)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) _ m1 F1i d1 (ae_of_all _ fun y =>
      tendsto_const_nhds.congr' ((hev y).mono fun k hk => by
        show (0 : ℝ) = entrySq (fderiv ℝ (u k) y - fderiv ℝ w y)
        rw [hk.1, sub_self]
        simp [entrySq]))
    simpa using h
  have T2 : Tendsto (fun k => ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y -
      fderiv ℝ (fderiv ℝ w) y)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) _ m2 F2i d2 (ae_of_all _ fun y =>
      tendsto_const_nhds.congr' ((hev y).mono fun k hk => by
        show (0 : ℝ) = CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ w) y)
        rw [hk.2, sub_self]
        simp [CellCert.fullSecondSq]))
    simpa using h
  obtain ⟨k, hk1, hk2⟩ := ((T1.eventually (gt_mem_nhds hε)).and (T2.eventually (gt_mem_nhds hε))).exists
  exact ⟨u k, hut k, F1i.mono' (m1 k) (d1 k), hk1.le, F2i.mono' (m2 k) (d2 k), hk2.le⟩

end Reduction

end CellCert

end Breakdown

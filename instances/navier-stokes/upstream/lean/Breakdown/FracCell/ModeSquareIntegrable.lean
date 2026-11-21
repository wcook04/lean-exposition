import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.FracCell.ModeGradSquare
import Mathlib

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.ModeSquareIntegrable.Internal

open SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

theorem combo_pt (κ : Fin 3 → Fin 3 → ℂ) (f : Fin 3 → Fin 3 → ℂ) :
    ‖∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b‖ ^ 2 ≤
      (∑ a : Fin 3, ∑ b : Fin 3, ‖κ a b‖ ^ 2) * ∑ a : Fin 3, ∑ b : Fin 3, ‖f a b‖ ^ 2 := by
  have h1 : ‖∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b‖ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖κ a b‖ * ‖f a b‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_)
    exact le_of_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _)
  have h2 : (∑ a : Fin 3, ∑ b : Fin 3, ‖κ a b‖ * ‖f a b‖) ^ 2 ≤
      (∑ a : Fin 3, ∑ b : Fin 3, ‖κ a b‖ ^ 2) * ∑ a : Fin 3, ∑ b : Fin 3, ‖f a b‖ ^ 2 := by
    rw [← Fintype.sum_prod_type' (fun a b => ‖κ a b‖ * ‖f a b‖),
      ← Fintype.sum_prod_type' (fun a b => ‖κ a b‖ ^ 2), ← Fintype.sum_prod_type' (fun a b => ‖f a b‖ ^ 2)]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem combo_sq (K : CellBox) (w : ℝ × ℝ → ℝ) (hwm : AEStronglyMeasurable w (volume.restrict K.rect))
    (hw0 : ∀ p ∈ K.rect, 0 ≤ w p) (f : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hm : ∀ a b, AEStronglyMeasurable (f a b) (volume.restrict K.rect))
    (hi : ∀ a b, IntegrableOn (fun p => w p * ‖f a b p‖ ^ 2) K.rect) (κ : Fin 3 → Fin 3 → ℂ) :
    AEStronglyMeasurable (fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b p) (volume.restrict K.rect) ∧
      IntegrableOn (fun p => w p * ‖∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b p‖ ^ 2) K.rect := by
  have hcm : AEStronglyMeasurable (fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b p)
      (volume.restrict K.rect) :=
    Finset.aestronglyMeasurable_fun_sum _ fun a _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun b _ => (hm a b).const_mul _
  refine ⟨hcm, ?_⟩
  set Kc : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, ‖κ a b‖ ^ 2 with hKc
  have hD : IntegrableOn (fun p => Kc * ∑ a : Fin 3, ∑ b : Fin 3, w p * ‖f a b p‖ ^ 2) K.rect :=
    (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b).const_mul _
  refine hD.mono' (hwm.mul (hcm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := hw0 p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (by positivity))]
  calc w p * ‖∑ a : Fin 3, ∑ b : Fin 3, κ a b * f a b p‖ ^ 2
      ≤ w p * (Kc * ∑ a : Fin 3, ∑ b : Fin 3, ‖f a b p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (combo_pt κ (fun a b => f a b p)) h0
    _ = Kc * ∑ a : Fin 3, ∑ b : Fin 3, w p * ‖f a b p‖ ^ 2 := by
        simp only [Finset.mul_sum]; ring_nf

theorem clm_apply_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) (x : Space) :
    L x = ∑ i : Fin 3, x i • L (unitVector i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp [unitVector, EuclideanSpace.basisFun_apply]

theorem clm_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  rw [clm_apply_sum L x]
  calc ‖∑ i : Fin 3, x i • L (unitVector i)‖ ≤ ∑ i : Fin 3, ‖x i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖L (unitVector i)‖ := by
        gcongr with i
        exact PiLp.norm_apply_le x i
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

theorem bil_norm_sq_le (T : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖T‖ ^ 2 ≤ 9 * ∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖ ^ 2 := by
  have h1 : ‖T‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖ :=
    (clm_norm_le T).trans (Finset.sum_le_sum fun i _ => clm_norm_le (T (unitVector i)))
  have h2 : (∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖) ^ 2 ≤
      9 * ∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖ ^ 2 := by
    rw [← Fintype.sum_prod_type' (fun i j => ‖T (unitVector i) (unitVector j)‖),
      ← Fintype.sum_prod_type' (fun i j => ‖T (unitVector i) (unitVector j)‖ ^ 2)]
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun x => ‖T (unitVector x.1) (unitVector x.2)‖)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
    norm_num at h
    exact h
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

def thirdKernel (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ T a b c : ℂ)

theorem frameThird_cont (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => frameThird q.1 q.2 a b c) := by
  unfold frameThird frameUnit
  exact ((continuous_snd.clm_apply ((unit_cont c).comp continuous_fst)).clm_apply
    ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)

theorem thirdKernel_cont (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdKernel m n a b c q.1 q.2) :=
  (phase_cont m n).mul (Complex.continuous_ofReal.comp (frameThird_cont a b c))

theorem frameThird_bound (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    |frameThird θ T a b c| ≤ ‖T‖ := by
  unfold frameThird frameUnit
  refine (inner_unit_bound θ _ a).trans ?_
  refine ((T _).le_opNorm _).trans ?_
  have hb := unit_norm θ b
  have hc := unit_norm θ c
  have h1 : ‖T (![radialUnit θ, angularUnit θ, axialUnit] c)‖ ≤ ‖T‖ := by
    refine (T.le_opNorm _).trans ?_
    simpa using mul_le_mul_of_nonneg_left hc (norm_nonneg T)
  calc ‖T (![radialUnit θ, angularUnit θ, axialUnit] c)‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] b‖
      ≤ ‖T‖ * 1 := mul_le_mul h1 hb (norm_nonneg _) (norm_nonneg _)
    _ = ‖T‖ := mul_one _

theorem thirdKernel_bound (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖thirdKernel m n a b c θ T‖ ≤ ‖T‖ := by
  rw [thirdKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact frameThird_bound θ T a b c

theorem frameThird_per (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird (θ + 2 * π) T a b c = frameThird θ T a b c := by
  simp only [frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem modeThird_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) :
    modeThird m n H a b c p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2)) := by
  unfold modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird_per]

theorem th_meas (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ)
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume) (a b c : Fin 3) :
    AEStronglyMeasurable (modeThird m n H a b c) (volume.restrict K.rect) := by
  have hF := meas_gen hH (thirdKernel m n a b c) (thirdKernel_cont m n a b c)
  have e : modeThird m n H a b c = fun p =>
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2)) :=
    funext fun p => modeThird_eq m n H a b c p
  rw [e]
  exact (hF.mono_measure (hle K hK)).const_mul _

theorem th_sq (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ)
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH1 : AEStronglyMeasurable H volume)
    (hH2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (a b c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n H a b c p‖ ^ 2) K.rect := by
  have h2 : MemLp H 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hH1).2 ((hH2.const_mul 9).mono'
      ((hH1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact bil_norm_sq_le (H y)
  refine ⟨(continuous_fst.aestronglyMeasurable).mul ((th_meas K hK m n hH1 a b c).norm.pow 2), ?_⟩
  set g : Space → ENNReal := fun y => ‖H y‖ₑ ^ 2 with hg_def
  set c0 : ENNReal := ‖(1 / (2 * π) : ℂ)‖ₑ ^ 2 * ENNReal.ofReal (2 * π) with hc0
  have hc0t : c0 ≠ ⊤ := by
    rw [hc0]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) ENNReal.ofReal_ne_top
  have hpt : ∀ p ∈ K.rect, ‖p.1 * ‖modeThird m n H a b c p‖ ^ 2‖ₑ ≤
      c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
    intro p hp
    have hw0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hw' : ‖p.1‖ₑ ≤ ENNReal.ofReal p.1 := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hw0]
    have hk : ∫⁻ θ in Ioo (-π) π, ‖thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2))‖ₑ ^ 2 ≤
        ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine lintegral_mono fun θ => pow_le_pow_left₀ (by positivity) ?_ 2
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (thirdKernel_bound m n a b c θ _)
    have hm : ‖modeThird m n H a b c p‖ₑ ^ 2 ≤ c0 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      rw [modeThird_eq, enorm_mul, mul_pow, hc0, mul_assoc]
      exact mul_le_mul' le_rfl ((int_sq_le _).trans (mul_le_mul' le_rfl hk))
    rw [enorm_mul, enorm_pow, enorm_norm]
    calc ‖p.1‖ₑ * ‖modeThird m n H a b c p‖ₑ ^ 2
        ≤ ENNReal.ofReal p.1 * (c0 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := mul_le_mul' hw' hm
      _ = c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by ring
  have hgm : AEMeasurable g volume := hH1.enorm.pow_const 2
  have hfin : ∫⁻ y, g y < ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hH1).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm, hg_def] using hi
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (b := c0 * ∫⁻ y, g y) ?_ (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc0t) hfin)
  calc ∫⁻ p in K.rect, ‖p.1 * ‖modeThird m n H a b c p‖ ^ 2‖ₑ
      ≤ ∫⁻ p in K.rect, c0 * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
        setLIntegral_mono' (rect_meas K) hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), c0 *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' (hle K hK) le_rfl
    _ = c0 * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ hc0t, hint]

end Breakdown.CellCert.CellAnalysis.ModeSquareIntegrable.Internal

namespace Breakdown.CellCert.CellAnalysis

open ModeSquareIntegrable.Internal ModeGradSquare.Internal LowEntry.Internal in
theorem modeSquareIntegrable : ModeSquareIntegrableStatement := by
  intro K hK m v G H hs n κ
  have hg := combo_sq K (fun p => K.lineWeight p.1)
    (((lineWeight_cont K).comp continuous_fst).aestronglyMeasurable)
    (fun p hp => by
      have h1 : K.r₁ ≤ p.1 := hp.1.1
      unfold CellBox.lineWeight
      split_ifs
      · linarith [hK.r_order.1]
      · exact zero_le_one)
    (gradMode m n G) (fun a b => gm_meas K hK m n hs.measurable_gradient a b)
    (fun a b => gm_sq K hK m n hs.measurable_gradient hs.gradient_two a b) κ
  refine ⟨hg.1, hg.2, fun c => ?_⟩
  exact combo_sq K (fun p => p.1) continuous_fst.aestronglyMeasurable
    (fun p hp => le_trans hK.r_order.1 hp.1.1)
    (fun a b => modeThird m n H a b c) (fun a b => th_meas K hK m n hs.measurable_second a b c)
    (fun a b => th_sq K hK m n hs.measurable_second hs.second_two a b c) κ

end Breakdown.CellCert.CellAnalysis

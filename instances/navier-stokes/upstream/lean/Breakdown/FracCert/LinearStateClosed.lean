import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.FreeExists

open scoped ContDiff ENNReal
open MeasureTheory Real Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

def DriftPowerSolenoidalStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space), IsSecondOrderField m v G H →
    IsWeakFractionalPower α v P → MemLp (driftField α a v G) 2 volume →
    IsSolenoidalL2 (fun y => driftField α a v G y + P y)

def GradientClosedStatement : Prop :=
  ∀ (Q : ℕ → Space → Space) (Q₀ : Space → Space), (∀ n, IsGradientField (Q n)) →
    (∀ n, MemLp (Q n) 2 volume) → MemLp Q₀ 2 volume →
    Tendsto (fun n => ∫ y, ‖Q n y - Q₀ y‖ ^ 2) atTop (𝓝 0) → IsGradientField Q₀

namespace LinearStateClosedInternal

open FreeExistsInternal

theorem ae_ne_zero' : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp only [not_not, Set.ofPred_eq_eq_singleton]
  exact measure_singleton 0

theorem app_meas {A : Space → (Space →L[ℝ] Space)} {x : Space → Space}
    (hA : AEStronglyMeasurable A volume) (hx : AEStronglyMeasurable x volume) :
    AEStronglyMeasurable (fun y => A y (x y)) volume :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Space) (F := Space)).continuous.comp_aestronglyMeasurable
    (hA.prodMk hx)

theorem clm_sq_le (K : Space →L[ℝ] Space) (x : Space) : ‖K x‖ ^ 2 ≤ entrySq K * ‖x‖ ^ 2 := by
  have h1 : ‖K x‖ ≤ ∑ j : Fin 3, |x j| * ‖K (unitVector j)‖ := by
    conv_lhs => rw [sum_unit x]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin 3 => |x j|)
    (fun j => ‖K (unitVector j)‖)
  have h3 : ‖x‖ ^ 2 = ∑ j : Fin 3, |x j| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs]
  have h4 : ‖K x‖ ^ 2 ≤ (∑ j : Fin 3, |x j| * ‖K (unitVector j)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [h3, entrySq, mul_comm]
  linarith

theorem entry_le (K : Space →L[ℝ] Space) (i : Fin 3) : ‖K (unitVector i)‖ ^ 2 ≤ entrySq K := by
  have := Finset.single_le_sum (f := fun j : Fin 3 => ‖K (unitVector j)‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [entrySq] using this

theorem col_memLp {K : Space → (Space →L[ℝ] Space)} (hK : AEStronglyMeasurable K volume)
    (hKi : Integrable (fun y => entrySq (K y))) (i : Fin 3) :
    MemLp (fun y => K y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => K y (unitVector i)) volume := hK.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hKi.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact entry_le _ _

theorem l2_pair_le {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ y, inner ℝ (f y) (g y) ≤ l2Norm f * l2Norm g := by
  have e : ∫ y, inner ℝ (f y) (g y) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
    rw [h1, h2]
  rw [e, l2Norm_eq hf, l2Norm_eq hg]
  exact real_inner_le_norm _ _

theorem sq_l2Norm {f : Space → Space} : l2Norm f ^ 2 = ∫ y, ‖f y‖ ^ 2 := by
  rw [l2Norm, Real.sq_sqrt (integral_nonneg fun _ => by positivity)]

theorem entrySq_nonneg (K : Space →L[ℝ] Space) : 0 ≤ entrySq K :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem half_sq (a b : ℝ) : ((1 / 2) * (a + b)) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem add_sq_le_two (a b : Space) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem l2_add {f g : ℕ → Space → Space} {f₀ g₀ : Space → Space} (hf : ∀ n, MemLp (f n) 2 volume)
    (hg : ∀ n, MemLp (g n) 2 volume) (hf₀ : MemLp f₀ 2 volume) (hg₀ : MemLp g₀ 2 volume)
    (h1 : Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ 2) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ y, ‖g n y - g₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ‖(f n y + g n y) - (f₀ y + g₀ y)‖ ^ 2) atTop (𝓝 0) := by
  have hb : ∀ n, ∫ y, ‖(f n y + g n y) - (f₀ y + g₀ y)‖ ^ 2 ≤
      2 * (∫ y, ‖f n y - f₀ y‖ ^ 2) + 2 * ∫ y, ‖g n y - g₀ y‖ ^ 2 := by
    intro n
    have i1 : Integrable (fun y => ‖f n y - f₀ y‖ ^ 2) volume :=
      ((hf n).sub hf₀).integrable_norm_pow (p := 2) two_ne_zero
    have i2 : Integrable (fun y => ‖g n y - g₀ y‖ ^ 2) volume :=
      ((hg n).sub hg₀).integrable_norm_pow (p := 2) two_ne_zero
    have i3 : Integrable (fun y => ‖(f n y + g n y) - (f₀ y + g₀ y)‖ ^ 2) volume :=
      (((hf n).add (hg n)).sub (hf₀.add hg₀)).integrable_norm_pow (p := 2) two_ne_zero
    calc ∫ y, ‖(f n y + g n y) - (f₀ y + g₀ y)‖ ^ 2
        ≤ ∫ y, (2 * ‖f n y - f₀ y‖ ^ 2 + 2 * ‖g n y - g₀ y‖ ^ 2) :=
          integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun y => by
            show ‖(f n y + g n y) - (f₀ y + g₀ y)‖ ^ 2 ≤ 2 * ‖f n y - f₀ y‖ ^ 2 + 2 * ‖g n y - g₀ y‖ ^ 2
            have e : (f n y + g n y) - (f₀ y + g₀ y) = (f n y - f₀ y) + (g n y - g₀ y) := by abel
            rw [e]
            exact add_sq_le_two (f n y - f₀ y) (g n y - g₀ y)
      _ = 2 * (∫ y, ‖f n y - f₀ y‖ ^ 2) + 2 * ∫ y, ‖g n y - g₀ y‖ ^ 2 := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
  refine squeeze_zero (fun n => integral_nonneg fun _ => by positivity) hb ?_
  simpa using (h1.const_mul 2).add (h2.const_mul 2)

theorem l2_smul {f : ℕ → Space → Space} {f₀ : Space → Space} (c : ℝ)
    (h1 : Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ‖c • f n y - c • f₀ y‖ ^ 2) atTop (𝓝 0) := by
  have e : ∀ n, ∫ y, ‖c • f n y - c • f₀ y‖ ^ 2 = c ^ 2 * ∫ y, ‖f n y - f₀ y‖ ^ 2 := by
    intro n
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [e]
  simpa using h1.const_mul (c ^ 2)

theorem l2_neg {f : ℕ → Space → Space} {f₀ : Space → Space}
    (h1 : Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ‖(-f n y) - (-f₀ y)‖ ^ 2) atTop (𝓝 0) := by
  refine h1.congr fun n => integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [← norm_neg (f n y - f₀ y)]
  congr 2
  abel

theorem l2_scal {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) {A : Space → Space} :
    Tendsto (fun n => ∫ y, ‖c n • A y - c₀ • A y‖ ^ 2) atTop (𝓝 0) := by
  have e : ∀ n, ∫ y, ‖c n • A y - c₀ • A y‖ ^ 2 = (c n - c₀) ^ 2 * ∫ y, ‖A y‖ ^ 2 := by
    intro n
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [e]
  have := ((hc.sub_const c₀).pow 2).mul_const (∫ y, ‖A y‖ ^ 2)
  simpa using this

theorem smul_memLp (c : ℝ) {A : Space → Space} (h : MemLp A 2 volume) :
    MemLp (fun y => c • A y) 2 volume :=
  h.const_smul c

theorem neg_memLp {A : Space → Space} (h : MemLp A 2 volume) : MemLp (fun y => -A y) 2 volume :=
  h.neg

theorem l2_sum {k : ℕ} {c : ℕ → Fin k → ℝ} {c₀ : Fin k → ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    {A : Fin k → Space → Space} (hA : ∀ i, MemLp (A i) 2 volume) (s : Finset (Fin k)) :
    Tendsto (fun n => ∫ y, ‖∑ i ∈ s, c n i • A i y - ∑ i ∈ s, c₀ i • A i y‖ ^ 2) atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    refine l2_add (f := fun n y => c n j • A j y) (g := fun n y => ∑ i ∈ s, c n i • A i y)
      (fun n => smul_memLp _ (hA j)) (fun n => memLp_finsetSum s (f := fun i y => c n i • A i y)
        fun i _ => smul_memLp _ (hA i))
      (smul_memLp _ (hA j)) (memLp_finsetSum s (f := fun i y => c₀ i • A i y) fun i _ => smul_memLp _ (hA i)) ?_ ih
    exact l2_scal ((continuous_apply j).tendsto c₀ |>.comp hc)

theorem l2_of_lp {f : ℕ → Space → Space} (hf : ∀ n, MemLp (f n) 2 volume) {L : Lp Space 2 volume}
    (h : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ y, ‖f n y - (L : Space → Space) y‖ ^ 2) atTop (𝓝 0) := by
  have e : ∀ n, ∫ y, ‖f n y - (L : Space → Space) y‖ ^ 2 = ‖(hf n).toLp (f n) - L‖ ^ 2 := by
    intro n
    rw [← sq_l2Norm, l2Norm_sub (hf n) (Lp.memLp L), Lp.toLp_coeFn]
  simp only [e]
  have := (tendsto_iff_norm_sub_tendsto_zero.1 h).pow 2
  simpa using this

theorem lp_of_l2 {f : ℕ → Space → Space} (hf : ∀ n, MemLp (f n) 2 volume) {f₀ : Space → Space}
    (hf₀ : MemLp f₀ 2 volume) (h : Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hf₀.toLp f₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(hf n).toLp (f n) - hf₀.toLp f₀‖ = Real.sqrt (∫ y, ‖f n y - f₀ y‖ ^ 2) := by
    intro n
    rw [← l2Norm_sub (hf n) hf₀, l2Norm]
  simp only [e]
  have := h.sqrt
  simpa using this

theorem sym_sub (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (v u : Space → Space)
    (G K : Space → (Space →L[ℝ] Space)) (y : Space) :
    symProduct W DW (fun y => v y - u y) (fun y => G y - K y) y =
      symProduct W DW v G y - symProduct W DW u K y := by
  simp only [symProduct, ContinuousLinearMap.sub_apply, map_sub]
  rw [← smul_sub]
  congr 1
  abel

theorem sym_bound (hInv : InverseSquareBoundStatement) (W : Space → Space)
    (DW : Space → (Space →L[ℝ] Space)) (hW : Continuous W) (hDW : Continuous DW) (C : ℝ)
    (hC : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖DW y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) (m : ℕ)
    {u : Space → Space} {K : Space → (Space →L[ℝ] Space)} {L : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hu : IsSecondOrderField m u K L) :
    MemLp (symProduct W DW u K) 2 volume ∧
      ∫ y, ‖symProduct W DW u K y‖ ^ 2 ≤ (5 / 2 * C ^ 2) * ∫ y, entrySq (K y) := by
  obtain ⟨hI, hIb⟩ := hInv u K hu.measurable_velocity hu.velocity_six hu.gradient_two hu.weak_gradient
  have hC0 : 0 ≤ C := by
    have := (hC 0).1
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hpt : ∀ y, y ≠ 0 → ‖symProduct W DW u K y‖ ^ 2 ≤
      C ^ 2 / 2 * (entrySq (K y) + ‖u y‖ ^ 2 / ‖y‖ ^ 2) := by
    intro y hy
    have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
    have h1r : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have hW1 : ‖W y‖ ≤ C := by
      have := (hC y).1
      have t1 : (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
      nlinarith [Real.rpow_nonneg h1r.le (-(1 : ℝ))]
    have hD1 : ‖DW y‖ * ‖y‖ ≤ C := by
      have h := (hC y).2
      have e : (1 + ‖y‖) ^ (-(2 : ℝ)) * (1 + ‖y‖) ^ 2 = 1 := by
        rw [Real.rpow_neg h1r.le, Real.rpow_two]
        exact inv_mul_cancel₀ (by positivity)
      have t : ‖y‖ ≤ (1 + ‖y‖) ^ 2 := by nlinarith
      have hp := Real.rpow_nonneg h1r.le (-(2 : ℝ))
      calc ‖DW y‖ * ‖y‖ ≤ (C * (1 + ‖y‖) ^ (-(2 : ℝ))) * (1 + ‖y‖) ^ 2 :=
            mul_le_mul h t hr.le (by positivity)
        _ = C := by rw [mul_assoc, e, mul_one]
    have a1 : ‖K y (W y)‖ ^ 2 ≤ entrySq (K y) * C ^ 2 := by
      have h1 := clm_sq_le (K y) (W y)
      have hes := entrySq_nonneg (K y)
      have h2 : ‖W y‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hW1 2
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hes)
    have a2 : ‖DW y (u y)‖ ^ 2 ≤ C ^ 2 * (‖u y‖ ^ 2 / ‖y‖ ^ 2) := by
      have b1 : ‖DW y (u y)‖ ≤ ‖DW y‖ * ‖u y‖ := (DW y).le_opNorm _
      have b2 : (‖DW y‖ * ‖y‖) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) hD1 2
      have b3 : ‖DW y (u y)‖ ^ 2 ≤ ‖DW y‖ ^ 2 * ‖u y‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) b1 2
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have c1 : ‖DW y‖ ^ 2 * ‖u y‖ ^ 2 * ‖y‖ ^ 2 ≤ C ^ 2 * ‖u y‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right b2 (sq_nonneg ‖u y‖)
        have e : ‖DW y‖ ^ 2 * ‖u y‖ ^ 2 * ‖y‖ ^ 2 = (‖DW y‖ * ‖y‖) ^ 2 * ‖u y‖ ^ 2 := by ring
        rw [e]; exact this
      have c2 := mul_le_mul_of_nonneg_right b3 (sq_nonneg ‖y‖)
      exact c2.trans c1
    have s : ‖symProduct W DW u K y‖ ≤ (1 / 2) * (‖K y (W y)‖ + ‖DW y (u y)‖) := by
      rw [symProduct, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    have s2 : ‖symProduct W DW u K y‖ ^ 2 ≤ ((1 / 2) * (‖K y (W y)‖ + ‖DW y (u y)‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) s 2
    have s3 := half_sq ‖K y (W y)‖ ‖DW y (u y)‖
    have e : C ^ 2 / 2 * (entrySq (K y) + ‖u y‖ ^ 2 / ‖y‖ ^ 2) =
        (entrySq (K y) * C ^ 2 + C ^ 2 * (‖u y‖ ^ 2 / ‖y‖ ^ 2)) / 2 := by ring
    rw [e]
    linarith
  have hm : AEStronglyMeasurable (symProduct W DW u K) volume := by
    have := ((app_meas hu.measurable_gradient hW.aestronglyMeasurable).add
      (app_meas hDW.aestronglyMeasurable hu.measurable_velocity)).const_smul (1 / 2 : ℝ)
    exact this
  have hg : Integrable (fun y => C ^ 2 / 2 * (entrySq (K y) + ‖u y‖ ^ 2 / ‖y‖ ^ 2)) volume :=
    (hu.gradient_two.add hI).const_mul _
  have hb : ∀ᵐ y ∂volume, ‖symProduct W DW u K y‖ ^ 2 ≤
      C ^ 2 / 2 * (entrySq (K y) + ‖u y‖ ^ 2 / ‖y‖ ^ 2) := by
    filter_upwards [ae_ne_zero'] with y hy
    exact hpt y hy
  have hL : MemLp (symProduct W DW u K) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine hg.mono' (hm.norm.pow 2) ?_
    filter_upwards [hb] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    exact hy
  refine ⟨hL, ?_⟩
  calc ∫ y, ‖symProduct W DW u K y‖ ^ 2
      ≤ ∫ y, C ^ 2 / 2 * (entrySq (K y) + ‖u y‖ ^ 2 / ‖y‖ ^ 2) :=
        integral_mono_ae (hL.integrable_norm_pow (p := 2) two_ne_zero) hg hb
    _ = C ^ 2 / 2 * ((∫ y, entrySq (K y)) + ∫ y, ‖u y‖ ^ 2 / ‖y‖ ^ 2) := by
        rw [integral_const_mul, integral_add hu.gradient_two hI]
    _ ≤ C ^ 2 / 2 * ((∫ y, entrySq (K y)) + 4 * ∫ y, entrySq (K y)) := by
        gcongr
    _ = (5 / 2 * C ^ 2) * ∫ y, entrySq (K y) := by ring

theorem entry_le_energy {w : Space → ℝ} {wmin wmax : ℝ} (hwmin : 0 < wmin) (hw : Measurable w)
    (hlow : ∀ y, wmin ≤ w y) (hup : ∀ y, w y ≤ wmax) {K : Space → (Space →L[ℝ] Space)}
    {L : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hK : Integrable (fun y => entrySq (K y))) :
    ∫ y, entrySq (K y) ≤ wmin⁻¹ * weightedEnergy w K L := by
  have hes : ∀ y, 0 ≤ entrySq (K y) := fun y => entrySq_nonneg _
  have hwi : Integrable (fun y => w y * entrySq (K y)) volume := by
    refine (hK.const_mul wmax).mono' (hw.aestronglyMeasurable.mul hK.aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    have h0 : 0 ≤ w y := hwmin.le.trans (hlow y)
    rw [Real.norm_of_nonneg (mul_nonneg h0 (hes y))]
    exact mul_le_mul_of_nonneg_right (hup y) (hes y)
  have h1 : wmin * ∫ y, entrySq (K y) ≤ ∫ y, w y * entrySq (K y) := by
    rw [← integral_const_mul]
    exact integral_mono (hK.const_mul _) hwi fun y => mul_le_mul_of_nonneg_right (hlow y) (hes y)
  have h2 : 0 ≤ ∫ y, ‖secondTrace (L y)‖ ^ 2 := integral_nonneg fun _ => by positivity
  rw [weightedEnergy, le_inv_mul_iff₀ hwmin]
  linarith

theorem energy_nonneg {w : Space → ℝ} {wmin : ℝ} (hwmin : 0 < wmin) (hlow : ∀ y, wmin ≤ w y)
    (K : Space → (Space →L[ℝ] Space)) (L : Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    0 ≤ weightedEnergy w K L := by
  refine add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun y => ?_)
  exact mul_nonneg (hwmin.le.trans (hlow y)) (entrySq_nonneg _)

theorem pin_tendsto {χ : Space → (Space →L[ℝ] Space)} (hχ : AEStronglyMeasurable χ volume)
    (hχi : Integrable (fun y => entrySq (χ y))) {G : ℕ → Space → (Space →L[ℝ] Space)}
    {G₀ : Space → (Space →L[ℝ] Space)} (hG : ∀ n, AEStronglyMeasurable (G n) volume)
    (hGi : ∀ n, Integrable (fun y => entrySq (G n y))) (hG₀ : AEStronglyMeasurable G₀ volume)
    (hG₀i : Integrable (fun y => entrySq (G₀ y)))
    (hGd : ∀ n, Integrable (fun y => entrySq (G n y - G₀ y)))
    (h : Tendsto (fun n => ∫ y, entrySq (G n y - G₀ y)) atTop (𝓝 0)) :
    Tendsto (fun n => pinValue χ (G n)) atTop (𝓝 (pinValue χ G₀)) := by
  have hc := fun i => col_memLp hχ hχi i
  have e : ∀ (K : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable K volume →
      Integrable (fun y => entrySq (K y)) →
      pinValue χ K = ∑ i : Fin 3, ∫ y, inner ℝ (K y (unitVector i)) (χ y (unitVector i)) := by
    intro K hK hKi
    rw [pinValue, ← integral_finsetSum]
    · rfl
    · exact fun i _ => inner_integrable (col_memLp hK hKi i) (hc i)
  rw [e G₀ hG₀ hG₀i]
  simp only [fun n => e (G n) (hG n) (hGi n)]
  refine tendsto_finsetSum _ fun i _ => ?_
  have hcol : ∀ n, MemLp (fun y => G n y (unitVector i)) 2 volume := fun n => col_memLp (hG n) (hGi n) i
  have hcol₀ : MemLp (fun y => G₀ y (unitVector i)) 2 volume := col_memLp hG₀ hG₀i i
  have hl2 : Tendsto (fun n => ∫ y, ‖G n y (unitVector i) - G₀ y (unitVector i)‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun _ => by positivity) (fun n => ?_) h
    refine integral_mono ((hcol n).sub hcol₀ |>.integrable_norm_pow (p := 2) two_ne_zero) ?_ fun y => ?_
    · exact hGd n
    · have := entry_le (G n y - G₀ y) i
      simpa [ContinuousLinearMap.sub_apply] using this
  have hT := (lp_of_l2 hcol hcol₀ hl2).inner (𝕜 := ℝ) (tendsto_const_nhds (x := (hc i).toLp _))
  have ee : ∀ (f : Space → Space) (hf : MemLp f 2 volume),
      inner ℝ (hf.toLp f) ((hc i).toLp _) = ∫ y, inner ℝ (f y) (χ y (unitVector i)) := by
    intro f hf
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, (hc i).coeFn_toLp] with y h1 h2
    rw [h1, h2]
  rw [ee _ hcol₀] at hT
  exact hT.congr fun n => ee _ (hcol n)


theorem full_eq {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (y : Space) :
    d.fullField α p v G H P κ y = (driftField α (d.rotationRate p) v G y + P y) +
      (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y + ∑ i, κ i • d.actuator i y := by
  simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField]
  abel

theorem l2_congr {f g : ℕ → Space → Space} {f₀ g₀ : Space → Space}
    (he : ∀ n y, f n y - f₀ y = g n y - g₀ y)
    (h : Tendsto (fun n => ∫ y, ‖f n y - f₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ‖g n y - g₀ y‖ ^ 2) atTop (𝓝 0) := by
  simpa only [he] using h

theorem sq_le_of {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b * a) : a ≤ b := by
  nlinarith

end LinearStateClosedInternal

open LinearStateClosedInternal FreeExistsInternal in
theorem linearStateClosed (h1 : FreeBoundsStatement) (h2 : SecondOrderCompleteStatement)
    (h3 : SecondOrderLinearStatement) (h4 : SolenoidalSplitStatement) (h5 : GradientOrthogonalStatement)
    (h6 : InverseSquareBoundStatement) (h7 : DriftPowerSolenoidalStatement)
    (h8 : GradientClosedStatement) : LinearStateClosedStatement := by
  intro α hα1 hα2 k N d hd p hp v G H P F κ F₀ hS hEq hF hF₀ hFt hC
  have hα32 : α < 3 / 2 := by linarith
  obtain ⟨C₀, hC₀⟩ := h1 α hα1 hα2
  obtain ⟨Cp, hCp⟩ := hd.profile_bounds
  have hW : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDW : Continuous (d.gradProfile p) := (hd.profile_smooth p hp).continuous_fderiv one_ne_zero
  have hsym : ∀ u K L, IsSecondOrderField d.order u K L →
      MemLp (symProduct (d.profile p) (d.gradProfile p) u K) 2 volume ∧
      ∫ y, ‖symProduct (d.profile p) (d.gradProfile p) u K y‖ ^ 2 ≤ (5 / 2 * Cp ^ 2) * ∫ y, entrySq (K y) :=
    fun u K L hu => sym_bound h6 (d.profile p) (d.gradProfile p) hW hDW Cp
      (fun y => ⟨(hCp p hp y).1, (hCp p hp y).2.1⟩) d.order hu
  have hv : ∀ n, IsSecondOrderField d.order (v n) (G n) (H n) := fun n => (hS n).second
  have hP : ∀ n, IsWeakFractionalPower α (v n) (P n) := fun n => (hS n).power
  have hD : ∀ n, MemLp (driftField α (d.rotationRate p) (v n) (G n)) 2 volume := fun n => (hS n).drift
  obtain ⟨sy, hsy⟩ : ∃ sy : ℕ → Space → Space, ∀ n,
      sy n = symProduct (d.profile p) (d.gradProfile p) (v n) (G n) := ⟨_, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Fin k → ℝ) → Space → Space, ∀ c, T c = fun y => ∑ i, c i • d.actuator i y :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Space → Space, ∀ n, R n = fun y => F n y - (2 : ℝ) • sy n y - T (κ n) y :=
    ⟨_, fun _ => rfl⟩
  have hTL : ∀ c, MemLp (T c) 2 volume := fun c => by
    rw [hT c]
    exact memLp_finsetSum _ (f := fun i y => c i • d.actuator i y) fun i _ => smul_memLp _ (hd.actuator_two i)
  have hsyL : ∀ n, MemLp (sy n) 2 volume := fun n => by rw [hsy n]; exact (hsym _ _ _ (hv n)).1
  have hRL : ∀ n, MemLp (R n) 2 volume := fun n => by
    rw [hR n]; exact ((hF n).sub (smul_memLp 2 (hsyL n))).sub (hTL _)
  choose Qw hQg hQe using hEq
  have hEn' : ∀ n, ∀ᵐ y ∂volume, driftField α (d.rotationRate p) (v n) (G n) y + P n y = R n y + Qw n y := by
    intro n
    filter_upwards [hQe n] with y hy
    rw [full_eq] at hy
    rw [hR n]
    have e2 : (∑ i, κ n i • d.actuator i y) = T (κ n) y := by rw [hT]
    rw [← hsy n, e2] at hy
    calc driftField α (d.rotationRate p) (v n) (G n) y + P n y
        = ((driftField α (d.rotationRate p) (v n) (G n) y + P n y) + (2 : ℝ) • sy n y + T (κ n) y)
          - (2 : ℝ) • sy n y - T (κ n) y := by abel
      _ = (F n y + Qw n y) - (2 : ℝ) • sy n y - T (κ n) y := by rw [hy]
      _ = (F n y - (2 : ℝ) • sy n y - T (κ n) y) + Qw n y := by abel
  have hQL : ∀ n, MemLp (Qw n) 2 volume := fun n =>
    (((hD n).add (hP n).1).sub (hRL n)).ae_eq (by
      filter_upwards [hEn' n] with y hy
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hy]; abel)
  have hkey : ∀ n m, l2Norm (fun y => P n y - P m y) ≤ l2Norm (fun y => R n y - R m y) ∧
      l2Norm (fun y => driftField α (d.rotationRate p) (v n) (G n) y -
        driftField α (d.rotationRate p) (v m) (G m) y) ≤ l2Norm (fun y => R n y - R m y) := by
    intro n m
    have hvd := sub_field h3 (hv n) (hv m)
    have hPd := sub_power hα1 hα32 (hv n).velocity_six (hv m).velocity_six (hP n) (hP m)
    have hDd : MemLp (driftField α (d.rotationRate p) (fun y => v n y - v m y) (fun y => G n y - G m y)) 2 volume :=
      ((hD n).sub (hD m)).ae_eq (Eventually.of_forall fun y => (drift_sub _ _ _ _ _ _ y).symm)
    have hsol := h7 α hα1 hα2 (d.rotationRate p) d.order _ _ _ _ hvd hPd hDd
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Space → Space, ζ = fun y => driftField α (d.rotationRate p)
        (fun y => v n y - v m y) (fun y => G n y - G m y) y + (P n y - P m y) := ⟨_, rfl⟩
    rw [← hζ] at hsol
    have hζL : MemLp ζ 2 volume := hsol.1
    have hFB := hC₀ (d.rotationRate p) d.order _ _ _ _ ζ hvd hPd hDd hζL (ae_of_all _ fun y => by rw [hζ])
    have hρL : MemLp (fun y => R n y - R m y) 2 volume := (hRL n).sub (hRL m)
    have hζe : ∀ᵐ y ∂volume, ζ y = ((R n y - R m y) + Qw n y) - Qw m y := by
      filter_upwards [hEn' n, hEn' m] with y e1 e2
      rw [hζ]
      simp only
      rw [drift_sub]
      have e3 : driftField α (d.rotationRate p) (v n) (G n) y - driftField α (d.rotationRate p) (v m) (G m) y
          + (P n y - P m y) = (driftField α (d.rotationRate p) (v n) (G n) y + P n y)
            - (driftField α (d.rotationRate p) (v m) (G m) y + P m y) := by abel
      rw [e3, e1, e2]; abel
    have o1 := h5 (Qw n) ζ (hQg n) (hQL n) hsol
    have o2 := h5 (Qw m) ζ (hQg m) (hQL m) hsol
    have hI : ∫ y, ‖ζ y‖ ^ 2 = ∫ y, inner ℝ (R n y - R m y) (ζ y) := by
      have e : ∫ y, ‖ζ y‖ ^ 2 = ∫ y, inner ℝ (((R n y - R m y) + Qw n y) - Qw m y) (ζ y) := by
        refine integral_congr_ae ?_
        filter_upwards [hζe] with y hy
        rw [← real_inner_self_eq_norm_sq]
        exact congrArg (fun z => inner ℝ z (ζ y)) hy
      rw [e]
      have e5 : ∀ y, inner ℝ (((R n y - R m y) + Qw n y) - Qw m y) (ζ y) =
          (inner ℝ (R n y - R m y) (ζ y) + inner ℝ (Qw n y) (ζ y)) - inner ℝ (Qw m y) (ζ y) := by
        intro y; rw [inner_sub_left, inner_add_left]
      simp only [e5]
      have i12 : Integrable (fun y => inner ℝ (R n y - R m y) (ζ y) + inner ℝ (Qw n y) (ζ y)) volume :=
        (inner_integrable hρL hζL).add (inner_integrable (hQL n) hζL)
      rw [integral_sub i12 (inner_integrable (hQL m) hζL), integral_add (inner_integrable hρL hζL) (inner_integrable (hQL n) hζL),
        o1, o2]
      simp
    have hle : l2Norm ζ ≤ l2Norm (fun y => R n y - R m y) := by
      refine sq_le_of (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_
      rw [sq_l2Norm, hI]
      exact l2_pair_le hρL hζL
    have e4 : l2Norm (driftField α (d.rotationRate p) (fun y => v n y - v m y) (fun y => G n y - G m y)) =
        l2Norm (fun y => driftField α (d.rotationRate p) (v n) (G n) y -
          driftField α (d.rotationRate p) (v m) (G m) y) := by
      congr 1; funext y; exact drift_sub _ _ _ _ _ _ y
    exact ⟨hFB.1.trans hle, e4 ▸ hFB.2.1.trans hle⟩

  have hwE : ∀ n n', 0 ≤ weightedEnergy d.weight (fun y => G n y - G n' y) (fun y => H n y - H n' y) :=
    fun n n' => energy_nonneg hd.weightMin_pos hd.weight_lower _ _
  have hsz : ∀ n n', d.size (fun y => G n y - G n' y) (fun y => H n y - H n' y) (fun i => κ n i - κ n' i) =
      Real.sqrt (weightedEnergy d.weight (fun y => G n y - G n' y) (fun y => H n y - H n' y) +
        d.multiplierScale ^ 2 * ∑ i, (κ n i - κ n' i) ^ 2) := fun n n' => rfl
  have hμ := hd.multiplierScale_pos
  have hEC : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n ≥ M, ∀ n' ≥ M,
      weightedEnergy d.weight (fun y => G n y - G n' y) (fun y => H n y - H n' y) < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hC (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨M, fun n hn n' hn' => ?_⟩
    have h := hM n hn n' hn'
    rw [hsz, Real.sqrt_lt_sqrt_iff (add_nonneg (hwE n n') (by positivity))] at h
    have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, (κ n i - κ n' i) ^ 2 := by positivity
    linarith
  have hκc : CauchySeq κ := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hC (d.multiplierScale * ε) (by positivity)
    refine ⟨M, fun n hn n' hn' => ?_⟩
    have h := hM n hn n' hn'
    rw [hsz, Real.sqrt_lt' (by positivity)] at h
    refine (dist_pi_lt_iff hε).2 fun i => ?_
    rw [Real.dist_eq]
    have hi : (κ n i - κ n' i) ^ 2 ≤ ∑ j, (κ n j - κ n' j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (κ n j - κ n' j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : d.multiplierScale ^ 2 * (κ n i - κ n' i) ^ 2 < d.multiplierScale ^ 2 * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_left hi (sq_nonneg d.multiplierScale)
      have := hwE n n'
      nlinarith
    have h3 : (κ n i - κ n' i) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h2 (sq_nonneg _)
    exact abs_lt.2 ⟨by nlinarith, by nlinarith⟩
  obtain ⟨κ₀, hκ⟩ := cauchySeq_tendsto_of_complete hκc
  obtain ⟨v₀, G₀, H₀, h0, hEn, hv6⟩ := h2 d.order d.weight d.weightMin hd.weightMin_pos hd.weight_measurable
    hd.weight_lower ⟨d.weightMax, hd.weight_upper⟩ v G H hv hEC
  have hGd : ∀ n, Integrable (fun y => entrySq (G n y - G₀ y)) volume := fun n =>
    (sub_field h3 (hv n) h0).gradient_two
  have hGn : Tendsto (fun n => ∫ y, entrySq (G n y - G₀ y)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun y => entrySq_nonneg _) (fun n =>
      entry_le_energy hd.weightMin_pos hd.weight_measurable hd.weight_lower hd.weight_upper
        (L := fun y => H n y - H₀ y) (hGd n)) ?_
    simpa using hEn.const_mul d.weightMin⁻¹
  obtain ⟨sy₀, hsy₀⟩ : ∃ s : Space → Space, s = symProduct (d.profile p) (d.gradProfile p) v₀ G₀ :=
    ⟨_, rfl⟩
  have hsy₀L : MemLp sy₀ 2 volume := by rw [hsy₀]; exact (hsym _ _ _ h0).1
  have hsyt : Tendsto (fun n => ∫ y, ‖sy n y - sy₀ y‖ ^ 2) atTop (𝓝 0) := by
    have hb : ∀ n, ∫ y, ‖sy n y - sy₀ y‖ ^ 2 ≤ (5 / 2 * Cp ^ 2) * ∫ y, entrySq (G n y - G₀ y) := by
      intro n
      have := (hsym _ _ _ (sub_field h3 (hv n) h0)).2
      rw [hsy n, hsy₀]
      simpa only [sym_sub] using this
    refine squeeze_zero (fun n => integral_nonneg fun _ => by positivity) hb ?_
    simpa using hGn.const_mul (5 / 2 * Cp ^ 2)
  have hTt : Tendsto (fun n => ∫ y, ‖T (κ n) y - T κ₀ y‖ ^ 2) atTop (𝓝 0) := by
    simp only [hT]
    exact l2_sum hκ hd.actuator_two Finset.univ
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Space → Space, R₀ = fun y => F₀ y - (2 : ℝ) • sy₀ y - T κ₀ y := ⟨_, rfl⟩
  have hR0L : MemLp R₀ 2 volume := by
    rw [hR₀]; exact (hF₀.sub (smul_memLp 2 hsy₀L)).sub (hTL _)
  have hRt : Tendsto (fun n => ∫ y, ‖R n y - R₀ y‖ ^ 2) atTop (𝓝 0) := by
    have hA := l2_add (f := F) (g := fun n y => -((2 : ℝ) • sy n y)) hF
      (fun n => neg_memLp (smul_memLp 2 (hsyL n))) hF₀ (neg_memLp (smul_memLp 2 hsy₀L)) hFt
      (l2_neg (l2_smul 2 hsyt))
    have hB := l2_add (f := fun n y => F n y + -((2 : ℝ) • sy n y)) (g := fun n y => -T (κ n) y)
      (fun n => (hF n).add (neg_memLp (smul_memLp 2 (hsyL n)))) (fun n => neg_memLp (hTL _))
      (hF₀.add (neg_memLp (smul_memLp 2 hsy₀L))) (neg_memLp (hTL _)) hA (l2_neg hTt)
    refine l2_congr ?_ hB
    intro n y
    rw [hR n, hR₀]
    simp only [Pi.add_apply, Pi.neg_apply]
    abel
  have hRc := (lp_of_l2 hRL hR0L hRt).cauchySeq
  have hPc : CauchySeq (fun n => (hP n).1.toLp (P n)) := by
    rw [Metric.cauchySeq_iff] at hRc ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hRc ε hε
    refine ⟨M, fun n hn m hm => ?_⟩
    have hd' := hM n hn m hm
    rw [dist_eq_norm] at hd' ⊢
    rw [← l2Norm_sub (hP n).1 (hP m).1]
    rw [← l2Norm_sub (hRL n) (hRL m)] at hd'
    exact lt_of_le_of_lt (hkey n m).1 hd'
  have hDc : CauchySeq (fun n => (hD n).toLp (driftField α (d.rotationRate p) (v n) (G n))) := by
    rw [Metric.cauchySeq_iff] at hRc ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hRc ε hε
    refine ⟨M, fun n hn m hm => ?_⟩
    have hd' := hM n hn m hm
    rw [dist_eq_norm] at hd' ⊢
    rw [← l2Norm_sub (hD n) (hD m)]
    rw [← l2Norm_sub (hRL n) (hRL m)] at hd'
    exact lt_of_le_of_lt (hkey n m).2 hd'
  obtain ⟨P0L, hP0⟩ := cauchySeq_tendsto_of_complete hPc
  obtain ⟨D0L, hD0⟩ := cauchySeq_tendsto_of_complete hDc
  have hPt := l2_of_lp (fun n => (hP n).1) hP0
  have hDt := l2_of_lp hD hD0
  have hPow0 : IsWeakFractionalPower α v₀ (P0L : Space → Space) := by
    refine ⟨Lp.memLp P0L, fun φ hφ => ?_⟩
    have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
    have e : ∀ (f : Lp Space 2 volume) (g : Space → Space), (f : Space → Space) =ᵐ[volume] g →
        inner ℝ f (hφ2.toLp φ) = ∫ y, inner ℝ (g y) (φ y) := by
      intro f g hfg
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hfg, hφ2.coeFn_toLp] with y e1 e2
      rw [e1, e2]
    have hl : Tendsto (fun n => ∫ y, inner ℝ (P n y) (φ y)) atTop
        (𝓝 (∫ y, inner ℝ ((P0L : Space → Space) y) (φ y))) := by
      have ht := hP0.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφ2.toLp φ))
      rw [e P0L P0L (ae_eq_refl _)] at ht
      exact ht.congr fun n => e _ _ (hP n).1.coeFn_toLp
    have hr : Tendsto (fun n => ∫ y, inner ℝ (v n y) (fractionalPowerAt α φ y)) atTop
        (𝓝 (∫ y, inner ℝ (v₀ y) (fractionalPowerAt α φ y))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => (∫ y, ‖v n y - v₀ y‖ ^ 6) ^ (1 / (6 : ℝ)) *
          (∫ y, ‖fractionalPowerAt α φ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ))) atTop (𝓝 0) := by
        have := (hv6.rpow_const (p := 1 / (6 : ℝ)) (Or.inr (by norm_num))).mul_const
          ((∫ y, ‖fractionalPowerAt α φ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)))
        rwa [Real.zero_rpow (by norm_num), zero_mul] at this
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have eq : (∫ y, inner ℝ (v n y) (fractionalPowerAt α φ y)) -
          ∫ y, inner ℝ (v₀ y) (fractionalPowerAt α φ y)
          = ∫ y, inner ℝ (v n y - v₀ y) (fractionalPowerAt α φ y) := by
        rw [← integral_sub (pair_integrable hα1 hα32 hφ (hv n).velocity_six)
          (pair_integrable hα1 hα32 hφ h0.velocity_six)]
        simp only [inner_sub_left]
      rw [Real.norm_eq_abs, eq]
      exact pair_bound hα1 hα32 hφ ((hv n).velocity_six.sub h0.velocity_six)
    exact tendsto_nhds_unique hl (hr.congr fun n => ((hP n).2 φ hφ).symm)
  have hlimit : ∀ᵐ y ∂volume, driftField α (d.rotationRate p) v₀ G₀ y = (D0L : Space → Space) y := by
    obtain ⟨hh, hhdef⟩ : ∃ hh : ℕ → Space → ℝ, ∀ n y, hh n y = ‖v n y - v₀ y‖ ^ 6 +
        entrySq (G n y - G₀ y) +
          ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖ ^ 2 :=
      ⟨_, fun _ _ => rfl⟩
    have ia : ∀ n, Integrable (fun y => ‖v n y - v₀ y‖ ^ 6) volume := fun n =>
      ((hv n).velocity_six.sub h0.velocity_six).integrable_norm_pow (p := 6) (by norm_num)
    have ic : ∀ n, Integrable (fun y =>
        ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖ ^ 2) volume :=
      fun n => ((hD n).sub (Lp.memLp D0L)).integrable_norm_pow (p := 2) two_ne_zero
    have hint : ∀ n, Integrable (hh n) volume := fun n => by
      have := ((ia n).add (hGd n)).add (ic n)
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [Pi.add_apply, hhdef]
    have hnn : ∀ n y, 0 ≤ hh n y := fun n y => by
      rw [hhdef]; have := entrySq_nonneg (G n y - G₀ y); positivity
    have hlimI : Tendsto (fun n => ∫ y, hh n y) atTop (𝓝 0) := by
      have e : ∀ n, ∫ y, hh n y = (∫ y, ‖v n y - v₀ y‖ ^ 6) + (∫ y, entrySq (G n y - G₀ y)) +
          ∫ y, ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖ ^ 2 := fun n => by
        have iab : Integrable (fun y => ‖v n y - v₀ y‖ ^ 6 + entrySq (G n y - G₀ y)) volume :=
          (ia n).add (hGd n)
        rw [← integral_add (ia n) (hGd n), ← integral_add iab (ic n)]
        exact integral_congr_ae (ae_of_all _ fun y => by simp only [hhdef])
      simp only [e]
      have := (hv6.add hGn).add hDt
      simpa using this
    have hmeas : TendstoInMeasure volume hh atTop (fun _ => 0) := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
        (fun n => (hint n).aestronglyMeasurable) aestronglyMeasurable_const ?_
      have e : ∀ n, eLpNorm (hh n - fun _ => (0 : ℝ)) 1 volume = ENNReal.ofReal (∫ y, hh n y) := fun n => by
        have h0' : hh n - (fun _ => (0 : ℝ)) = hh n := by ext y; simp
        rw [h0', eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
        congr 1
        exact integral_congr_ae (ae_of_all _ fun y => Real.norm_of_nonneg (hnn n y))
      simp only [e]
      have := ENNReal.tendsto_ofReal hlimI
      rwa [ENNReal.ofReal_zero] at this
    obtain ⟨ψ, -, hae⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hae] with y hy
    have part : ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) → (∀ n, f n ≤ hh n y) →
        Tendsto (fun i => f (ψ i)) atTop (𝓝 0) := fun f h0f hle =>
      squeeze_zero (fun i => h0f _) (fun i => hle _) hy
    have tv : Tendsto (fun i => v (ψ i) y) atTop (𝓝 (v₀ y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 6) (by norm_num) ?_
      exact part (fun n => ‖v n y - v₀ y‖ ^ 6) (fun n => by positivity) (fun n => by
        rw [hhdef]; have := entrySq_nonneg (G n y - G₀ y)
        nlinarith [sq_nonneg ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖])
    have tG : ∀ x, Tendsto (fun i => G (ψ i) y x) atTop (𝓝 (G₀ y x)) := by
      refine clm_tendsto (K := fun i => G (ψ i) y) fun j => ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 2) two_ne_zero ?_
      refine part (fun n => ‖G n y (unitVector j) - G₀ y (unitVector j)‖ ^ 2) (fun n => by positivity)
        (fun n => ?_)
      have hj : ‖G n y (unitVector j) - G₀ y (unitVector j)‖ ^ 2 ≤ entrySq (G n y - G₀ y) := by
        have := entry_le (G n y - G₀ y) j
        simpa using this
      rw [hhdef]
      nlinarith [sq_nonneg ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖,
        pow_nonneg (norm_nonneg (v n y - v₀ y)) 6]
    have tE : Tendsto (fun i => driftField α (d.rotationRate p) (v (ψ i)) (G (ψ i)) y) atTop
        (𝓝 ((D0L : Space → Space) y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 2) two_ne_zero ?_
      refine part (fun n => ‖driftField α (d.rotationRate p) (v n) (G n) y - (D0L : Space → Space) y‖ ^ 2)
        (fun n => by positivity) (fun n => ?_)
      rw [hhdef]
      have := entrySq_nonneg (G n y - G₀ y)
      nlinarith [pow_nonneg (norm_nonneg (v n y - v₀ y)) 6]
    have tD : Tendsto (fun i => driftField α (d.rotationRate p) (v (ψ i)) (G (ψ i)) y) atTop
        (𝓝 (driftField α (d.rotationRate p) v₀ G₀ y)) := by
      simp only [driftField]
      exact ((tv.const_smul _).add ((tG y).const_smul _)).add
        (((tG (axialTurn y)).sub ((axialTurn_continuous.tendsto _).comp tv)).const_smul _)
    exact tendsto_nhds_unique tD tE
  have hD0mem : MemLp (driftField α (d.rotationRate p) v₀ G₀) 2 volume :=
    (Lp.memLp D0L).ae_eq (hlimit.mono fun y h => h.symm)
  have hDt' : Tendsto (fun n => ∫ y, ‖driftField α (d.rotationRate p) (v n) (G n) y -
      driftField α (d.rotationRate p) v₀ G₀ y‖ ^ 2) atTop (𝓝 0) :=
    hDt.congr fun n => integral_congr_ae (hlimit.mono fun y h => by simp only [h])
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : Space → Space, Q₀ = fun y =>
      (driftField α (d.rotationRate p) v₀ G₀ y + (P0L : Space → Space) y) + (2 : ℝ) • sy₀ y + T κ₀ y - F₀ y :=
    ⟨_, rfl⟩
  have hQ0L : MemLp Q₀ 2 volume := by
    rw [hQ₀]
    exact (((hD0mem.add (Lp.memLp P0L)).add (smul_memLp 2 hsy₀L)).add (hTL κ₀)).sub hF₀
  have hA := l2_add (f := fun n y => driftField α (d.rotationRate p) (v n) (G n) y) (g := P) hD
    (fun n => (hP n).1) hD0mem (Lp.memLp P0L) hDt' hPt
  have hB := l2_add (f := fun n y => driftField α (d.rotationRate p) (v n) (G n) y + P n y)
    (g := fun n y => (2 : ℝ) • sy n y) (fun n => (hD n).add (hP n).1) (fun n => smul_memLp 2 (hsyL n))
    (hD0mem.add (Lp.memLp P0L)) (smul_memLp 2 hsy₀L) hA (l2_smul 2 hsyt)
  have hB' := l2_add (f := fun n y => (driftField α (d.rotationRate p) (v n) (G n) y + P n y) + (2 : ℝ) • sy n y)
    (g := fun n y => T (κ n) y) (fun n => ((hD n).add (hP n).1).add (smul_memLp 2 (hsyL n)))
    (fun n => hTL _) ((hD0mem.add (Lp.memLp P0L)).add (smul_memLp 2 hsy₀L)) (hTL _) hB hTt
  have hB'' := l2_add (f := fun n y => (driftField α (d.rotationRate p) (v n) (G n) y + P n y) +
      (2 : ℝ) • sy n y + T (κ n) y) (g := fun n y => -F n y)
    (fun n => (((hD n).add (hP n).1).add (smul_memLp 2 (hsyL n))).add (hTL _)) (fun n => neg_memLp (hF n))
    (((hD0mem.add (Lp.memLp P0L)).add (smul_memLp 2 hsy₀L)).add (hTL _)) (neg_memLp hF₀) hB' (l2_neg hFt)
  have hQf : Tendsto (fun n => ∫ y, ‖((driftField α (d.rotationRate p) (v n) (G n) y + P n y) +
      (2 : ℝ) • sy n y + T (κ n) y - F n y) - Q₀ y‖ ^ 2) atTop (𝓝 0) := by
    refine l2_congr ?_ hB''
    intro n y
    rw [hQ₀]
    simp only [Pi.add_apply, Pi.neg_apply]
    abel
  have hQt : Tendsto (fun n => ∫ y, ‖Qw n y - Q₀ y‖ ^ 2) atTop (𝓝 0) := by
    refine hQf.congr fun n => integral_congr_ae ?_
    filter_upwards [hQe n] with y hy
    rw [full_eq, ← hsy n] at hy
    have e2 : (∑ i, κ n i • d.actuator i y) = T (κ n) y := by rw [hT]
    rw [e2] at hy
    show ‖((driftField α (d.rotationRate p) (v n) (G n) y + P n y) + (2 : ℝ) • sy n y + T (κ n) y - F n y) - Q₀ y‖ ^ 2 = ‖Qw n y - Q₀ y‖ ^ 2
    rw [hy, add_sub_cancel_left]
  have hgrad : IsGradientField Q₀ := h8 Qw Q₀ hQg hQL hQ0L hQt
  have heq : ∀ y, d.fullField α p v₀ G₀ H₀ (P0L : Space → Space) κ₀ y = F₀ y + Q₀ y := by
    intro y
    rw [full_eq, hQ₀, hsy₀, hT]
    simp only
    abel
  have hsize : Tendsto (fun n => d.size (fun y => G n y - G₀ y) (fun y => H n y - H₀ y)
      (fun i => κ n i - κ₀ i)) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => ∑ i, (κ n i - κ₀ i) ^ 2) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin k)) fun i _ =>
        ((((continuous_apply i).tendsto κ₀).comp hκ).sub_const (κ₀ i)).pow 2
      simpa using this
    have := (hEn.add (hs.const_mul (d.multiplierScale ^ 2))).sqrt
    simpa [FracCertData.size, sizeNorm] using this
  have hpins : Tendsto (fun n => d.pins (G n)) atTop (𝓝 (d.pins G₀)) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    exact pin_tendsto (hd.pin_measurable i).1 (hd.pin_two i).1 (fun n => (hv n).measurable_gradient)
      (fun n => (hv n).gradient_two) h0.measurable_gradient h0.gradient_two hGd hGn
  exact ⟨v₀, G₀, H₀, (P0L : Space → Space), κ₀, ⟨h0, hPow0, hD0mem⟩, ⟨Q₀, hgrad, ae_of_all _ heq⟩,
    hsize, hv6, hpins⟩

end SteadyCert

end Breakdown

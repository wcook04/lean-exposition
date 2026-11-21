import Breakdown.FracCell.PuncturedWeakScalar
import Breakdown.FracCell.GivenAuxPressureOpen
import Breakdown.CellReduction.AdjointEntryDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace PressureWeak

namespace Internal

open CellCert.GivenFields.PressureOpen (shellSet)

def ShellSlope (f : Space → ℂ) (C : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ shellSet a b, ∀ y ∈ shellSet a b,
    ‖f x - f y‖ ≤ C * ((1 + b / a) ^ 2 / a) * ‖x - y‖

theorem shellWeight_nonneg {a : ℝ} (ha : 0 < a) (b : ℝ) : 0 ≤ (1 + b / a) ^ 2 / a := by positivity

theorem inv_le_shellWeight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 1 / a ≤ (1 + b / a) ^ 2 / a := by
  have h0 : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le
  exact div_le_div_of_nonneg_right (by nlinarith) ha.le

theorem ratio_le_shellWeight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b / a ^ 2 ≤ (1 + b / a) ^ 2 / a := by
  have h0 : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le
  rw [sq, ← div_div]
  exact div_le_div_of_nonneg_right (by nlinarith) ha.le

theorem mem_shell_iff {a b : ℝ} {x : Space} : x ∈ shellSet a b ↔ a ≤ ‖x‖ ∧ ‖x‖ ≤ b := Iff.rfl

theorem ShellSlope.mono {f : Space → ℂ} {C C' : ℝ} (h : ShellSlope f C) (hC : C ≤ C') : ShellSlope f C' := by
  intro a b ha hab x hx y hy
  refine (h a b ha hab x hx y hy).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (shellWeight_nonneg ha b)) (norm_nonneg _)

theorem ShellSlope.const (c : ℂ) : ShellSlope (fun _ => c) 0 := by
  intro a b ha hab x hx y hy
  simp

theorem ShellSlope.add {f g : Space → ℂ} {Cf Cg : ℝ} (hf : ShellSlope f Cf) (hg : ShellSlope g Cg) :
    ShellSlope (fun z => f z + g z) (Cf + Cg) := by
  intro a b ha hab x hx y hy
  show ‖(f x + g x) - (f y + g y)‖ ≤ _
  have e : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := hf a b ha hab x hx y hy
  have h2 := hg a b ha hab x hx y hy
  linarith

theorem ShellSlope.mul {f g : Space → ℂ} {Cf Cg Bf Bg : ℝ} (hf : ShellSlope f Cf) (hg : ShellSlope g Cg)
    (hfb : ∀ z, ‖f z‖ ≤ Bf) (hgb : ∀ z, ‖g z‖ ≤ Bg) :
    ShellSlope (fun z => f z * g z) (Bf * Cg + Bg * Cf) := by
  intro a b ha hab x hx y hy
  show ‖f x * g x - f y * g y‖ ≤ _
  have hBf : 0 ≤ Bf := (norm_nonneg _).trans (hfb 0)
  have hBg : 0 ≤ Bg := (norm_nonneg _).trans (hgb 0)
  have e1 := hf a b ha hab x hx y hy
  have e2 := hg a b ha hab x hx y hy
  calc ‖f x * g x - f y * g y‖ ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ :=
        CellCert.GivenFields.PressureOpen.PressureOpenInternal.mul_sub_le _ _ _ _
    _ ≤ Bf * (Cg * ((1 + b / a) ^ 2 / a) * ‖x - y‖) + Bg * (Cf * ((1 + b / a) ^ 2 / a) * ‖x - y‖) :=
        add_le_add (mul_le_mul (hfb x) e2 (norm_nonneg _) hBf) (mul_le_mul (hgb y) e1 (norm_nonneg _) hBg)
    _ = (Bf * Cg + Bg * Cf) * ((1 + b / a) ^ 2 / a) * ‖x - y‖ := by ring

theorem ShellSlope.sum {ι : Type*} (s : Finset ι) {f : ι → Space → ℂ} {C : ι → ℝ}
    (h : ∀ i ∈ s, ShellSlope (f i) (C i)) : ShellSlope (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a b ha hab x hx y hy
    simp
  | insert j s hj ih =>
    have h1 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h2 := (h j (Finset.mem_insert_self j s)).add h1
    intro a b ha hab x hx y hy
    have h3 := h2 a b ha hab x hx y hy
    simp only [Finset.sum_insert hj]
    exact h3

theorem ball_in_shell {z x : Space} (hx : x ∈ Metric.ball z (‖z‖ / 2)) :
    x ∈ shellSet (‖z‖ / 2) (3 * (‖z‖ / 2)) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 := norm_sub_norm_le z x
  have h2 := norm_le_insert' x z
  rw [norm_sub_rev] at h1
  rw [mem_shell_iff]
  constructor <;> linarith

theorem re_slope_ball {f : Space → ℂ} {C : ℝ} (hf : ShellSlope f C) {z : Space} (hz : z ≠ 0) :
    LipschitzOnWith (Real.toNNReal (32 * C / ‖z‖)) (fun y => (f y).re) (Metric.ball z (‖z‖ / 2)) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ha : 0 < ‖z‖ / 2 := by positivity
  have hab : ‖z‖ / 2 ≤ 3 * (‖z‖ / 2) := by linarith
  refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  show ‖(f x).re - (f y).re‖ ≤ _
  rw [Real.norm_eq_abs, ← Complex.sub_re]
  have h := hf _ _ ha hab x (ball_in_shell hx) y (ball_in_shell hy)
  have hw : (1 + 3 * (‖z‖ / 2) / (‖z‖ / 2)) ^ 2 / (‖z‖ / 2) = 32 / ‖z‖ := by
    field_simp
    ring
  rw [hw] at h
  calc |(f x - f y).re| ≤ ‖f x - f y‖ := Complex.abs_re_le_norm _
    _ ≤ C * (32 / ‖z‖) * ‖x - y‖ := h
    _ = 32 * C / ‖z‖ * ‖x - y‖ := by ring

theorem slope_ball {f : Space → ℂ} {C : ℝ} (hf : ShellSlope f C) {z : Space} (hz : z ≠ 0) :
    LipschitzOnWith (Real.toNNReal (32 * C / ‖z‖)) f (Metric.ball z (‖z‖ / 2)) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ha : 0 < ‖z‖ / 2 := by positivity
  have hab : ‖z‖ / 2 ≤ 3 * (‖z‖ / 2) := by linarith
  refine LipschitzOnWith.of_dist_le' fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h := hf _ _ ha hab x (ball_in_shell hx) y (ball_in_shell hy)
  have hw : (1 + 3 * (‖z‖ / 2) / (‖z‖ / 2)) ^ 2 / (‖z‖ / 2) = 32 / ‖z‖ := by
    field_simp
    ring
  rw [hw] at h
  calc ‖f x - f y‖ ≤ C * (32 / ‖z‖) * ‖x - y‖ := h
    _ = 32 * C / ‖z‖ * ‖x - y‖ := by ring

theorem ShellSlope.continuousOn {f : Space → ℂ} {C : ℝ} (hf : ShellSlope f C) : ContinuousOn f {0}ᶜ := by
  intro z hz
  have hz0 : z ≠ 0 := hz
  exact ((slope_ball hf hz0).continuousOn.continuousAt
    (Metric.ball_mem_nhds z (half_pos (norm_pos_iff.2 hz0)))).continuousWithinAt

theorem re_slope_annulus {f : Space → ℂ} {C : ℝ} (hf : ShellSlope f C) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun y => (f y).re) {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
  refine ⟨Real.toNNReal (C * ((1 + max ε R / ε) ^ 2 / ε)), LipschitzOnWith.of_dist_le' fun x hx y hy => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  show ‖(f x).re - (f y).re‖ ≤ _
  rw [Real.norm_eq_abs, ← Complex.sub_re]
  have hx' : x ∈ shellSet ε (max ε R) := mem_shell_iff.2 ⟨hx.1, hx.2.trans (le_max_right _ _)⟩
  have hy' : y ∈ shellSet ε (max ε R) := mem_shell_iff.2 ⟨hy.1, hy.2.trans (le_max_right _ _)⟩
  exact (Complex.abs_re_le_norm _).trans (hf ε (max ε R) hε (le_max_left _ _) x hx' y hy')

theorem norm_gradient_le (q : Space → ℝ) (y : Space) : ‖gradientAt q y‖ ≤ 3 * ‖fderiv ℝ q y‖ := by
  have hunit : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖fderiv ℝ q y (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ q y‖ := by
    intro i
    rw [norm_smul, hunit, mul_one]
    calc ‖fderiv ℝ q y (unitVector i)‖ ≤ ‖fderiv ℝ q y‖ * ‖unitVector i‖ := (fderiv ℝ q y).le_opNorm _
      _ = ‖fderiv ℝ q y‖ := by rw [hunit, mul_one]
  calc ∑ i : Fin 3, ‖fderiv ℝ q y (unitVector i) • unitVector i‖ ≤ ∑ _i : Fin 3, ‖fderiv ℝ q y‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ q y‖ := by simp

theorem gradient_component (q : Space → ℝ) (y : Space) (i : Fin 3) :
    gradientAt q y i = fderiv ℝ q y (unitVector i) := by
  rw [← CellCert.PuncturedWeakInternal.inner_gradient q y i, unitVector, EuclideanSpace.inner_single_right]
  simp

theorem weakScalarGradient_of_shellSlope {p : Space → ℝ} {f : Space → ℂ} {C B : ℝ}
    (hpf : ∀ z, p z = (f z).re) (hf : ShellSlope f C) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ B) :
    AdjointDefect.IsWeakScalarGradient p (gradientAt p) := by
  obtain rfl : p = fun y => (f y).re := funext hpf
  have hcont : ContinuousOn (fun y => (f y).re) {0}ᶜ := by
    intro z hz
    have hz0 : z ≠ 0 := hz
    exact ((re_slope_ball hf hz0).continuousOn.continuousAt
      (Metric.ball_mem_nhds z (half_pos (norm_pos_iff.2 hz0)))).continuousWithinAt
  have hm : AEStronglyMeasurable (fun y => (f y).re) volume := by
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure Space)) (measurableSet_singleton (0 : Space)).compl
    rwa [MeasureTheory.restrict_compl_singleton] at h
  have hg : ∀ᵐ y ∂(volume : Measure Space), ‖fderiv ℝ (fun y => (f y).re) y‖ ≤ (32 * C) * ‖y‖⁻¹ := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with y hy
    have hy0 : y ≠ 0 := hy
    have h := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y (half_pos (norm_pos_iff.2 hy0)))
      (re_slope_ball hf hy0)
    rw [Real.coe_toNNReal _ (div_nonneg (by linarith) (norm_nonneg _))] at h
    rw [← div_eq_mul_inv]
    exact h
  have hW := CellCert.PuncturedWeakInternal.weak_of_punctured (q := fun y => (f y).re) (M := B) (C := 32 * C) hm
    (fun y => (Complex.abs_re_le_norm _).trans (hb y)) (fun ε hε R => re_slope_annulus hf hε R) hg
  have hLq : LocallyIntegrable (fun y => (f y).re) volume := by
    intro x
    refine ⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), ?_⟩
    refine Measure.integrableOn_of_bounded (M := B) measure_ball_lt_top.ne hm ?_
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hb y)
  have hgm : AEStronglyMeasurable (gradientAt (fun y => (f y).re)) volume := by
    have h : Measurable (gradientAt (fun y => (f y).re)) := by
      show Measurable fun y => ∑ i : Fin 3, fderiv ℝ (fun y => (f y).re) y (unitVector i) • unitVector i
      exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ _ _).smul_const _
    exact h.aestronglyMeasurable
  have hLg : LocallyIntegrable (gradientAt (fun y => (f y).re)) volume := by
    intro x
    refine ⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), ?_⟩
    have hI : IntegrableOn (fun y : Space => (96 * C) * ‖y‖⁻¹) (Metric.ball 0 (‖x‖ + 1)) volume :=
      (CellCert.PuncturedWeakInternal.invNorm_ball (‖x‖ + 1)).const_mul _
    refine Integrable.mono' hI hgm.restrict (ae_restrict_of_ae ?_)
    filter_upwards [hg] with y hy
    have := norm_gradient_le (fun y => (f y).re) y
    linarith
  refine ⟨hLq, hLg, fun φ hφ i => ?_⟩
  have h := hW φ hφ i
  simp only [CellCert.PuncturedWeakInternal.inner_gradient] at h
  simp only [gradient_component]
  linarith [h]

end Internal

end PressureWeak

end PotentialShape

end Breakdown

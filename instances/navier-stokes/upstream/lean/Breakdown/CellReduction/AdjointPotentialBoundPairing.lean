import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.AdjointAssemblyMeasure
import Breakdown.CellReduction.AdjointAssemblyPairing
import Breakdown.CertCell.FormNegativeInverseSquare
import Breakdown.FracCell.ReductionAdjointMollifySecondApprox
import Breakdown.FracCell.AdjointConvectionPairingParts
import Breakdown.FracCell.ReductionAdjointCutoffSecondApprox

open scoped ContDiff ENNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

namespace PotentialBound

theorem inner_eq_sum (x y : Space) : inner ℝ x y = ∑ c, x c * y c := by
  simp [PiLp.inner_apply, mul_comm]

theorem abs_integral_le_of_le_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {h a b : X → ℝ}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (hh : ∀ᵐ x ∂μ, |h x| ≤ a x * b x) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ ≤ ENNReal.ofReal (A ^ 2))
    (hB : ∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2)) :
    |∫ x, h x ∂μ| ≤ A * B := by
  have h1 : |∫ x, h x ∂μ| ≤ (∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ).toReal := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_lintegral_norm h
  have h2 : ∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ ≤ ∫⁻ x, ((fun x => ENNReal.ofReal (a x)) * fun x => ENNReal.ofReal (b x)) x ∂μ := by
    refine lintegral_mono_ae (hh.mono fun x hx => ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (ha0 x), Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hx
  have h3 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two ha.ennreal_ofReal hb.ennreal_ofReal
  have e : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2) := fun t ht => by
    rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num)]
    norm_cast
  have hA' : (∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal A := by
    rw [lintegral_congr fun x => e _ (ha0 x)]
    calc (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (A ^ 2) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hA (by norm_num)
      _ = ENNReal.ofReal A := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq hA0]
  have hB' : (∫⁻ x, ENNReal.ofReal (b x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal B := by
    rw [lintegral_congr fun x => e _ (hb0 x)]
    calc (∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (B ^ 2) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hB (by norm_num)
      _ = ENNReal.ofReal B := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq hB0]
  have h4 : ∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ ≤ ENNReal.ofReal (A * B) := by
    rw [ENNReal.ofReal_mul hA0]
    exact h2.trans (h3.trans (mul_le_mul' hA' hB'))
  refine h1.trans ?_
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
  rwa [ENNReal.toReal_ofReal (mul_nonneg hA0 hB0)] at this

theorem cut_fderiv_zero {r : ℝ} (hr : 0 < r) {y : Space} (hy : ‖y‖ < r) :
    fderiv ℝ (radialCutoff r) y = 0 := by
  have h : radialCutoff r =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
    exact radialCutoff_eq_one hr (le_of_lt hz)
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

theorem cut_fderiv_zero_far {r : ℝ} (hr : 0 < r) {y : Space} (hy : 2 * r < ‖y‖) :
    fderiv ℝ (radialCutoff r) y = 0 := by
  have h : radialCutoff r =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact radialCutoff_eq_zero hr (le_of_lt hz)
  rw [h.fderiv_eq]
  exact fderiv_const_apply _

theorem cut_weight_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ r, 0 < r → ∀ y : Space,
    ‖y‖ * ‖fderiv ℝ (radialCutoff r) y‖ ≤ c := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hc0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  refine ⟨2 * c, by positivity, fun r hr y => ?_⟩
  rcases lt_or_ge ‖y‖ r with h | h
  · rw [cut_fderiv_zero hr h, norm_zero, mul_zero]; positivity
  rcases lt_or_ge (2 * r) ‖y‖ with h' | h'
  · rw [cut_fderiv_zero_far hr h', norm_zero, mul_zero]; positivity
  calc ‖y‖ * ‖fderiv ℝ (radialCutoff r) y‖ ≤ (2 * r) * (c / r) :=
        mul_le_mul h' (hc r hr y) (norm_nonneg _) (by positivity)
    _ = 2 * c := by field_simp

theorem cut_eventually_one (y : Space) : ∀ᶠ n : ℕ in atTop, radialCutoff ((n : ℝ) + 1) y = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  refine radialCutoff_eq_one (by positivity) ?_
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem cut_fderiv_eventually_zero (y : Space) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
  filter_upwards [eventually_ge_atTop N] with n hn
  refine cut_fderiv_zero (by positivity) ?_
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem cut_continuous_fderiv (r : ℝ) (hr : 0 < r) : Continuous (fderiv ℝ (radialCutoff r)) :=
  (contDiff_radialCutoff hr).continuous_fderiv (by simp)

theorem integrable_mul_apply_compact {f : Space → Space} {φ : Space → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) (c : Fin 3) :
    Integrable (fun y => φ y * f y c) := by
  have h := (EuclideanSpace.proj c : Space →L[ℝ] ℝ).integrable_comp
    (hf.integrable_smul_left_of_hasCompactSupport hφ hφs)
  refine h.congr (ae_of_all _ fun y => ?_)
  simp [smul_eq_mul]

theorem integrable_inner_compact {f g : Space → Space} (hf : LocallyIntegrable f volume)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun y => inner ℝ (g y) (f y)) := by
  have h : ∀ c : Fin 3, Integrable (fun y => g y c * f y c) := fun c =>
    integrable_mul_apply_compact hf ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp hg)
      (hgs.comp_left (g := fun x : Space => x c) (by simp)) c
  refine (integrable_finsetSum Finset.univ fun c _ => h c).congr (ae_of_all _ fun y => ?_)
  simp only [inner_eq_sum]

theorem hasFDerivAt_component {w : Space → Space} {y : Space} (hw : DifferentiableAt ℝ w y) (c : Fin 3) :
    HasFDerivAt (fun x => w x c) ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp (fderiv ℝ w y)) y :=
  (EuclideanSpace.proj c : Space →L[ℝ] ℝ).hasFDerivAt.comp y hw.hasFDerivAt

theorem fderiv_cut_mul {r : ℝ} (hr : 0 < r) {w : Space → Space} {y : Space} (hw : DifferentiableAt ℝ w y)
    (c i : Fin 3) :
    fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) =
      radialCutoff r y * fderiv ℝ w y (unitVector i) c + w y c * fderiv ℝ (radialCutoff r) y (unitVector i) := by
  have hχ : HasFDerivAt (radialCutoff r) (fderiv ℝ (radialCutoff r) y) y :=
    (((contDiff_radialCutoff hr).differentiable (by simp)) y).hasFDerivAt
  have h : HasFDerivAt (fun x => radialCutoff r x * w x c)
      (radialCutoff r y • (EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp (fderiv ℝ w y)
        + w y c • fderiv ℝ (radialCutoff r) y) y := hχ.mul (hasFDerivAt_component hw c)
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem summed_rel {w d : Space → Space} {m : Fin 3 → Space → Space} {r : ℝ} (hr : 0 < r)
    (hw : ContDiff ℝ 1 w) (hm : ∀ i, LocallyIntegrable (m i) volume) (hd : LocallyIntegrable d volume)
    (hrel : ∀ c : Fin 3, ∫ y, (radialCutoff r y * w y c) * d y c =
        -∫ y, ∑ i, fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) * m i y c) :
    ∫ y, radialCutoff r y * inner ℝ (w y) (d y) =
      -((∫ y, radialCutoff r y * ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y)) +
        ∫ y, ∑ i, fderiv ℝ (radialCutoff r) y (unitVector i) * inner ℝ (w y) (m i y)) := by
  have hχc : Continuous (radialCutoff r) := (contDiff_radialCutoff hr).continuous
  have hχs : HasCompactSupport (radialCutoff r) := hasCompactSupport_radialCutoff hr
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hwc : Continuous w := hw.continuous
  have hwD : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hχD : Continuous (fderiv ℝ (radialCutoff r)) := cut_continuous_fderiv r hr
  have hχDs : HasCompactSupport (fderiv ℝ (radialCutoff r)) := hχs.fderiv (𝕜 := ℝ)
  have hφc : ∀ c : Fin 3, Continuous (fun y => radialCutoff r y * w y c) := fun c =>
    hχc.mul ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp hwc)
  have hφs : ∀ c : Fin 3, HasCompactSupport (fun y => radialCutoff r y * w y c) := fun c =>
    hχs.mul_right
  have hpt : ∀ c i y, fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) * m i y c =
      radialCutoff r y * fderiv ℝ w y (unitVector i) c * m i y c
        + fderiv ℝ (radialCutoff r) y (unitVector i) * (w y c * m i y c) := by
    intro c i y
    rw [fderiv_cut_mul hr (hwd y) c i]
    ring
  have hA : ∀ c i : Fin 3, Continuous (fun y => radialCutoff r y * fderiv ℝ w y (unitVector i) c) := fun c i =>
    hχc.mul ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp (hwD.clm_apply continuous_const))
  have hAs : ∀ c i : Fin 3, HasCompactSupport (fun y => radialCutoff r y * fderiv ℝ w y (unitVector i) c) :=
    fun c i => hχs.mul_right
  have hBc : ∀ c i : Fin 3, Continuous (fun y => fderiv ℝ (radialCutoff r) y (unitVector i) * w y c) :=
    fun c i => (hχD.clm_apply continuous_const).mul ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).continuous.comp hwc)
  have hBs : ∀ c i : Fin 3, HasCompactSupport (fun y => fderiv ℝ (radialCutoff r) y (unitVector i) * w y c) :=
    fun c i => (hχDs.comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) (by simp)).mul_right
  have hterm : ∀ c i : Fin 3, Integrable (fun y =>
      fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) * m i y c) := by
    intro c i
    have h1 := integrable_mul_apply_compact (hm i) (hA c i) (hAs c i) c
    have h2 := integrable_mul_apply_compact (hm i) (hBc c i) (hBs c i) c
    refine (h1.add h2).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    rw [hpt]
    ring
  have hL : ∫ y, radialCutoff r y * inner ℝ (w y) (d y) = ∑ c, ∫ y, (radialCutoff r y * w y c) * d y c := by
    rw [← integral_finsetSum _ fun c _ => integrable_mul_apply_compact hd (hφc c) (hφs c) c]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [inner_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hsum : ∑ c, ∫ y, ∑ i, fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) * m i y c =
      ∫ y, ∑ c, ∑ i, fderiv ℝ (fun x => radialCutoff r x * w x c) y (unitVector i) * m i y c := by
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun i _ => hterm c i]
  have hF : Integrable (fun y => radialCutoff r y * ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y)) := by
    have h : ∀ i, Integrable (fun y => inner ℝ (radialCutoff r y • fderiv ℝ w y (unitVector i)) (m i y)) :=
      fun i => integrable_inner_compact (hm i) (hχc.smul (hwD.clm_apply continuous_const)) hχs.smul_right
    refine (integrable_finsetSum Finset.univ fun i _ => h i).congr (ae_of_all _ fun y => ?_)
    simp only [Finset.mul_sum, real_inner_smul_left]
  have hE : Integrable (fun y => ∑ i, fderiv ℝ (radialCutoff r) y (unitVector i) * inner ℝ (w y) (m i y)) := by
    have h : ∀ i, Integrable (fun y => inner ℝ (fderiv ℝ (radialCutoff r) y (unitVector i) • w y) (m i y)) :=
      fun i => integrable_inner_compact (hm i) ((hχD.clm_apply continuous_const).smul hwc)
        ((hχDs.comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) (by simp)).smul_right)
    refine (integrable_finsetSum Finset.univ fun i _ => h i).congr (ae_of_all _ fun y => ?_)
    simp only [real_inner_smul_left]
  rw [hL, Finset.sum_congr rfl fun c _ => hrel c, Finset.sum_neg_distrib, hsum, ← integral_add hF hE]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [hpt, Finset.sum_add_distrib, inner_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring
  · rw [Finset.sum_comm]

theorem cut_limit {f F : Space → ℝ} {E : ℕ → Space → ℝ} {D : Space → ℝ}
    (hrel : ∀ n : ℕ, ∫ y, radialCutoff ((n : ℝ) + 1) y * f y =
      -((∫ y, radialCutoff ((n : ℝ) + 1) y * F y) + ∫ y, E n y))
    (hf : Integrable f) (hF : Integrable F) (hD : Integrable D) (hEm : ∀ n, AEStronglyMeasurable (E n) volume)
    (hEb : ∀ n y, ‖E n y‖ ≤ D y) (hE0 : ∀ y, ∀ᶠ n in atTop, E n y = 0) :
    ∫ y, f y = -∫ y, F y := by
  have hχm : ∀ n : ℕ, AEStronglyMeasurable (radialCutoff ((n : ℝ) + 1)) volume := fun n =>
    (contDiff_radialCutoff (by positivity)).continuous.aestronglyMeasurable
  have hχb : ∀ (n : ℕ) (y : Space) (g : Space → ℝ), ‖radialCutoff ((n : ℝ) + 1) y * g y‖ ≤ ‖g y‖ := by
    intro n y g
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_le_one _ _)
  have t1 : Tendsto (fun n : ℕ => ∫ y, radialCutoff ((n : ℝ) + 1) y * f y) atTop (𝓝 (∫ y, f y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖f y‖) (fun n => (hχm n).mul hf.1) hf.norm
      (fun n => ae_of_all _ fun y => hχb n y f) (ae_of_all _ fun y => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cut_eventually_one y] with n hn
    rw [hn, one_mul]
  have t2 : Tendsto (fun n : ℕ => ∫ y, radialCutoff ((n : ℝ) + 1) y * F y) atTop (𝓝 (∫ y, F y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖F y‖) (fun n => (hχm n).mul hF.1) hF.norm
      (fun n => ae_of_all _ fun y => hχb n y F) (ae_of_all _ fun y => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cut_eventually_one y] with n hn
    rw [hn, one_mul]
  have t3 : Tendsto (fun n : ℕ => ∫ y, E n y) atTop (𝓝 (∫ _y : Space, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence D hEm hD (fun n => ae_of_all _ fun y => hEb n y)
      (ae_of_all _ fun y => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hE0 y] with n hn
    rw [hn]
  rw [integral_zero] at t3
  have t4 : Tendsto (fun n : ℕ => -((∫ y, radialCutoff ((n : ℝ) + 1) y * F y) + ∫ y, E n y)) atTop
      (𝓝 (-((∫ y, F y) + 0))) := (t2.add t3).neg
  rw [add_zero] at t4
  exact tendsto_nhds_unique (t1.congr fun n => hrel n) t4

def WeakColumnDivergence (m : Fin 3 → Space → Space) (d : Space → Space) : Prop :=
  ∀ φ : Space → ℝ, IsTestFunction φ → ∀ c : Fin 3,
    ∫ y, φ y * d y c = -∫ y, ∑ i, fderiv ℝ φ y (unitVector i) * m i y c

theorem ae_ne_zero : ∀ᵐ y : Space, y ≠ 0 := by
  rw [ae_iff]
  simp

theorem cut_pairing {w d : Space → Space} {m : Fin 3 → Space → Space}
    (hw1 : ContDiff ℝ 1 w) (hm : ∀ i, LocallyIntegrable (m i) volume) (hd : LocallyIntegrable d volume)
    (hrel : ∀ (n : ℕ) (c : Fin 3), ∫ y, (radialCutoff ((n : ℝ) + 1) y * w y c) * d y c =
      -∫ y, ∑ i, fderiv ℝ (fun x => radialCutoff ((n : ℝ) + 1) x * w x c) y (unitVector i) * m i y c)
    (h1 : Integrable (fun y => inner ℝ (w y) (d y)))
    (h2 : Integrable (fun y => ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y)))
    (hD : Integrable (fun y => ‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖)) :
    ∫ y, inner ℝ (w y) (d y) = -∫ y, ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y) := by
  obtain ⟨c, hc0, hc⟩ := cut_weight_bound
  have hwc : Continuous w := hw1.continuous
  refine cut_limit (E := fun n y => ∑ i, fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector i) *
      inner ℝ (w y) (m i y)) (D := fun y => c * (‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖)) (fun n => ?_) h1 h2
    (hD.const_mul c) (fun n => ?_) (fun n y => ?_) (fun y => ?_)
  · exact summed_rel (by positivity) hw1 hm hd (hrel n)
  · refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (((cut_continuous_fderiv _ (by positivity)).clm_apply continuous_const).aestronglyMeasurable).mul
      (hwc.aestronglyMeasurable.inner (hm i).aestronglyMeasurable)
  · have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : ∀ i, ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector i) * inner ℝ (w y) (m i y)‖ ≤
        ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y‖ * (‖w y‖ * ‖m i y‖) := by
      intro i
      rw [norm_mul]
      refine mul_le_mul ?_ (norm_inner_le_norm _ _) (norm_nonneg _) (norm_nonneg _)
      refine ((fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y).le_opNorm _).trans ?_
      rw [FracInternal.ConvectionPairing.unit_norm, mul_one]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hb i).trans ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    by_cases hy : y = 0
    · subst hy
      rw [cut_fderiv_zero hr (by simp; positivity), norm_zero, zero_mul]
      simp
    have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hχ : ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y‖ ≤ c / ‖y‖ := by
      rw [le_div_iff₀ hy0, mul_comm]
      exact hc _ hr y
    calc ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y‖ * (‖w y‖ * ∑ i, ‖m i y‖)
        ≤ c / ‖y‖ * (‖w y‖ * ∑ i, ‖m i y‖) :=
          mul_le_mul_of_nonneg_right hχ (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _))
      _ = c * (‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖) := by ring
  · filter_upwards [cut_fderiv_eventually_zero y] with n hn
    simp [hn]

theorem smooth_pairing {w d : Space → Space} {m : Fin 3 → Space → Space}
    (hw : ContDiff ℝ ∞ w) (hm : ∀ i, LocallyIntegrable (m i) volume) (hd : LocallyIntegrable d volume)
    (hrel : WeakColumnDivergence m d)
    (h1 : Integrable (fun y => inner ℝ (w y) (d y)))
    (h2 : Integrable (fun y => ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y)))
    (hD : Integrable (fun y => ‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖)) :
    ∫ y, inner ℝ (w y) (d y) = -∫ y, ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y) := by
  refine cut_pairing (hw.of_le (by simp)) hm hd (fun n c => ?_) h1 h2 hD
  have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht : IsTestFunction (fun y => radialCutoff ((n : ℝ) + 1) y * w y c) :=
    ⟨(contDiff_radialCutoff hr).mul ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hw),
      (hasCompactSupport_radialCutoff hr).mul_right⟩
  exact hrel _ ht c

theorem first_order_pairing {w d : Space → Space} {m : Fin 3 → Space → Space}
    (hw : ContDiff ℝ 1 w) (hm : ∀ i, LocallyIntegrable (m i) volume) (hd : LocallyIntegrable d volume)
    (hrel : ∀ φ : Space → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ c : Fin 3,
      ∫ y, φ y * d y c = -∫ y, ∑ i, fderiv ℝ φ y (unitVector i) * m i y c)
    (h1 : Integrable (fun y => inner ℝ (w y) (d y)))
    (h2 : Integrable (fun y => ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y)))
    (hD : Integrable (fun y => ‖w y‖ / ‖y‖ * ∑ i, ‖m i y‖)) :
    ∫ y, inner ℝ (w y) (d y) = -∫ y, ∑ i, inner ℝ (fderiv ℝ w y (unitVector i)) (m i y) := by
  refine cut_pairing hw hm hd (fun n c => ?_) h1 h2 hD
  have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact hrel _ ((contDiff_radialCutoff hr).of_le (by simp) |>.mul
    ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hw)) (hasCompactSupport_radialCutoff hr).mul_right c

def mollified (n : ℕ) (f : Space → Space) : Space → Space :=
  (CellCert.Reduction.MollifySecondApproxInternal.kernelBump n).normed volume
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem mollified_contDiff (n : ℕ) {f : Space → Space} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (mollified n f) :=
  (CellCert.Reduction.MollifySecondApproxInternal.kernelBump n).hasCompactSupport_normed.contDiff_convolution_left
    _ (CellCert.Reduction.MollifySecondApproxInternal.kernelBump n).contDiff_normed hf (n := ⊤)

theorem weakOf_of {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hg : IsWeakGradient v G) :
    SteadyCert.IsWeakGradientOf v G := fun φ hφ j => by
  rw [hg.2.2 φ hφ j, neg_neg]

theorem weak_smooth {w : Space → Space} (hw : ContDiff ℝ 1 w) : IsWeakGradient w (fun y => fderiv ℝ w y) := by
  refine ⟨hw.continuous.locallyIntegrable, (hw.continuous_fderiv one_ne_zero).locallyIntegrable, fun φ hφ i => ?_⟩
  rw [CellCert.Reduction.CutoffSecondApproxInternal.smooth_weak hw φ hφ i, neg_neg]

theorem mollified_fderiv (n : ℕ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hg : IsWeakGradient v G)
    (y : Space) (j : Fin 3) :
    fderiv ℝ (mollified n v) y (unitVector j) = mollified n (fun z => G z (unitVector j)) y :=
  CellCert.Reduction.MollifySecondApproxInternal.mollify_fderiv_apply' _ v G hg.1 (weakOf_of hg) y j

theorem column_locallyIntegrable {G : Space → (Space →L[ℝ] Space)} (hG : LocallyIntegrable G volume) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume := fun x => by
  obtain ⟨s, hs, hi⟩ := hG x
  exact ⟨s, hs, (ContinuousLinearMap.apply ℝ Space (unitVector j)).integrable_comp hi⟩

theorem mollified_sixth (n : ℕ) {f : Space → Space} (hf : LocallyIntegrable f volume)
    (h6 : Integrable (fun y => ‖f y‖ ^ 6)) : Integrable (fun y => ‖mollified n f y‖ ^ 6) := by
  have hc := (CellCert.Reduction.MollifySecondApproxInternal.kernelBump n).integrable_normed.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) h6 (μ := volume)
  refine hc.mono' (((mollified_contDiff n hf).continuous.norm.pow 6).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact CellCert.Reduction.MollifySecondApproxInternal.normPow_conv_le _ f 6 (by norm_num) h6 y

theorem sixth_sub_le (a b : Space) : ‖a - b‖ ^ 6 ≤ 64 * (‖a‖ ^ 6 + ‖b‖ ^ 6) := by
  have h1 : ‖a - b‖ ≤ 2 * max ‖a‖ ‖b‖ := by
    refine (norm_sub_le a b).trans ?_
    linarith [le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖]
  have h2 : ‖a - b‖ ^ 6 ≤ (2 * max ‖a‖ ‖b‖) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) h1 6
  have h3 : max ‖a‖ ‖b‖ ^ 6 ≤ ‖a‖ ^ 6 + ‖b‖ ^ 6 := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · rw [max_eq_right h]; have := pow_nonneg (norm_nonneg a) 6; linarith
    · rw [max_eq_left h]; have := pow_nonneg (norm_nonneg b) 6; linarith
  calc ‖a - b‖ ^ 6 ≤ (2 * max ‖a‖ ‖b‖) ^ 6 := h2
    _ = 64 * max ‖a‖ ‖b‖ ^ 6 := by ring
    _ ≤ 64 * (‖a‖ ^ 6 + ‖b‖ ^ 6) := by linarith

theorem weak_sub {f g : Space → Space} {F K : Space → (Space →L[ℝ] Space)} (h1 : IsWeakGradient f F)
    (h2 : IsWeakGradient g K) : IsWeakGradient (fun y => f y - g y) (fun y => F y - K y) := by
  refine ⟨h1.1.sub h2.1, h1.2.1.sub h2.2.1, fun φ hφ i => ?_⟩
  have hφc : Continuous φ := hφ.1.continuous
  have hDc : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)
  have iF := (column_locallyIntegrable h1.2.1 i).integrable_smul_left_of_hasCompactSupport hφc hφ.2
  have iK := (column_locallyIntegrable h2.2.1 i).integrable_smul_left_of_hasCompactSupport hφc hφ.2
  have if' := h1.1.integrable_smul_left_of_hasCompactSupport hDc hDs
  have ig := h2.1.integrable_smul_left_of_hasCompactSupport hDc hDs
  have e1 : ∫ y, φ y • (F y - K y) (unitVector i) = (∫ y, φ y • F y (unitVector i)) - ∫ y, φ y • K y (unitVector i) := by
    refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans (integral_sub iF iK)
    simp [smul_sub]
  have e2 : ∫ y, fderiv ℝ φ y (unitVector i) • (f y - g y) =
      (∫ y, fderiv ℝ φ y (unitVector i) • f y) - ∫ y, fderiv ℝ φ y (unitVector i) • g y := by
    refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans (integral_sub if' ig)
    simp [smul_sub]
  calc ∫ y, φ y • (F y - K y) (unitVector i) = (∫ y, φ y • F y (unitVector i)) - ∫ y, φ y • K y (unitVector i) := e1
    _ = (-∫ y, fderiv ℝ φ y (unitVector i) • f y) - (-∫ y, fderiv ℝ φ y (unitVector i) • g y) :=
        congrArg₂ (fun a b => a - b) (h1.2.2 φ hφ i) (h2.2.2 φ hφ i)
    _ = -((∫ y, fderiv ℝ φ y (unitVector i) • f y) - ∫ y, fderiv ℝ φ y (unitVector i) • g y) := by abel
    _ = -∫ y, fderiv ℝ φ y (unitVector i) • (f y - g y) := by rw [e2]

theorem integrable_of_lintegral_lt {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) (h0 : ∀ y, 0 ≤ f y)
    (h : ∫⁻ y, ENNReal.ofReal (f y) < ⊤) : Integrable f :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 h⟩

theorem inner_le_weighted (a b y : Space) (hy : y ≠ 0) :
    |inner ℝ a b| ≤ ‖a‖ / ‖y‖ * (‖y‖ * ‖b‖) := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [show ‖a‖ / ‖y‖ * (‖y‖ * ‖b‖) = ‖a‖ * ‖b‖ by field_simp]
  exact abs_real_inner_le_norm a b

theorem integrable_inner_weighted {f d : Space → Space} (hf : AEStronglyMeasurable f volume)
    (hd : AEStronglyMeasurable d volume) (hH : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / ‖y‖ ^ 2) < ⊤)
    (hd2 : Integrable (fun y => ‖y‖ ^ 2 * ‖d y‖ ^ 2)) : Integrable (fun y => inner ℝ (f y) (d y)) := by
  have hH' : Integrable (fun y => ‖f y‖ ^ 2 / ‖y‖ ^ 2) :=
    integrable_of_lintegral_lt (((hf.norm.pow 2).aemeasurable.div
      (continuous_norm.measurable.pow_const 2).aemeasurable).aestronglyMeasurable)
      (fun y => by positivity) hH
  refine ((hH'.add hd2).div_const 2).mono' (hf.inner hd) ?_
  filter_upwards [ae_ne_zero] with y hy
  rw [Real.norm_eq_abs]
  refine (inner_le_weighted _ _ y hy).trans ?_
  have e1 : ‖f y‖ ^ 2 / ‖y‖ ^ 2 = (‖f y‖ / ‖y‖) ^ 2 := by rw [div_pow]
  have e2 : ‖y‖ ^ 2 * ‖d y‖ ^ 2 = (‖y‖ * ‖d y‖) ^ 2 := by rw [mul_pow]
  simp only [Pi.add_apply]
  rw [e1, e2]
  nlinarith [sq_nonneg (‖f y‖ / ‖y‖ - ‖y‖ * ‖d y‖)]

theorem abs_integral_inner_weighted_le {f d : Space → Space} (hf : AEStronglyMeasurable f volume)
    (hd : AEStronglyMeasurable d volume) {A : ℝ} (hA0 : 0 ≤ A)
    (hH : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2 / ‖y‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (hd2 : Integrable (fun y => ‖y‖ ^ 2 * ‖d y‖ ^ 2)) :
    |∫ y, inner ℝ (f y) (d y)| ≤ A * Real.sqrt (∫ y, ‖y‖ ^ 2 * ‖d y‖ ^ 2) := by
  refine abs_integral_le_of_le_mul (a := fun y => ‖f y‖ / ‖y‖) (b := fun y => ‖y‖ * ‖d y‖)
    (hf.norm.aemeasurable.div continuous_norm.measurable.aemeasurable)
    (continuous_norm.aestronglyMeasurable.mul hd.norm).aemeasurable (fun y => by positivity)
    (fun y => by positivity) ?_ hA0 (Real.sqrt_nonneg _) ?_ ?_
  · filter_upwards [ae_ne_zero] with y hy
    exact inner_le_weighted _ _ y hy
  · simpa only [div_pow] using hH
  · have e : ∀ y : Space, (‖y‖ * ‖d y‖) ^ 2 = ‖y‖ ^ 2 * ‖d y‖ ^ 2 := fun y => by rw [mul_pow]
    simp only [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hd2 (ae_of_all _ fun y => by positivity),
      Real.sq_sqrt (integral_nonneg fun y => by positivity)]

theorem integrable_cols {X m : Fin 3 → Space → Space} (hX : ∀ i, AEStronglyMeasurable (X i) volume)
    (hm : ∀ i, AEStronglyMeasurable (m i) volume) (hX2 : ∀ i, Integrable (fun y => ‖X i y‖ ^ 2))
    (hm2 : ∀ i, Integrable (fun y => ‖m i y‖ ^ 2)) :
    Integrable (fun y => ∑ i, inner ℝ (X i y) (m i y)) := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  refine (((hX2 i).add (hm2 i)).div_const 2).mono' ((hX i).inner (hm i)) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖X i y‖ - ‖m i y‖)]

theorem abs_integral_cols_le {X m : Fin 3 → Space → Space} (hX : ∀ i, AEStronglyMeasurable (X i) volume)
    (hm : ∀ i, AEStronglyMeasurable (m i) volume) (hX2 : ∀ i, Integrable (fun y => ‖X i y‖ ^ 2))
    (hm2 : ∀ i, Integrable (fun y => ‖m i y‖ ^ 2)) :
    |∫ y, ∑ i, inner ℝ (X i y) (m i y)| ≤
      Real.sqrt (∫ y, ∑ i, ‖X i y‖ ^ 2) * Real.sqrt (∫ y, ∑ i, ‖m i y‖ ^ 2) := by
  have hXs : Integrable (fun y => ∑ i, ‖X i y‖ ^ 2) := integrable_finsetSum Finset.univ fun i _ => hX2 i
  have hms : Integrable (fun y => ∑ i, ‖m i y‖ ^ 2) := integrable_finsetSum Finset.univ fun i _ => hm2 i
  refine abs_integral_le_of_le_mul (a := fun y => Real.sqrt (∑ i, ‖X i y‖ ^ 2))
    (b := fun y => Real.sqrt (∑ i, ‖m i y‖ ^ 2)) hXs.1.aemeasurable.sqrt hms.1.aemeasurable.sqrt
    (fun y => Real.sqrt_nonneg _) (fun y => Real.sqrt_nonneg _) (ae_of_all _ fun y => ?_)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_ ?_
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm (X i y) (m i y)).trans ?_
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  · simp only [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hXs (ae_of_all _ fun y => by positivity),
      Real.sq_sqrt (integral_nonneg fun y => by positivity)]
  · simp only [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hms (ae_of_all _ fun y => by positivity),
      Real.sq_sqrt (integral_nonneg fun y => by positivity)]

theorem weak_pairing {v d : Space → Space} {G : Space → (Space →L[ℝ] Space)} {m : Fin 3 → Space → Space}
    (hvm : AEStronglyMeasurable v volume) (hGm : AEStronglyMeasurable G volume) (hg : IsWeakGradient v G)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6) < ⊤) (hG2 : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤)
    (hm : ∀ i, LocallyIntegrable (m i) volume) (hd : LocallyIntegrable d volume)
    (hrel : WeakColumnDivergence m d)
    (hm2 : ∀ i, Integrable (fun y => ‖m i y‖ ^ 2)) (hd2 : Integrable (fun y => ‖y‖ ^ 2 * ‖d y‖ ^ 2)) :
    Integrable (fun y => inner ℝ (v y) (d y)) ∧
      ∫ y, inner ℝ (v y) (d y) = -∫ y, ∑ i, inner ℝ (G y (unitVector i)) (m i y) := by
  set g : Fin 3 → Space → Space := fun j y => G y (unitVector j) with hgdef
  have hgm : ∀ j, AEStronglyMeasurable (g j) volume := fun j => hGm.apply_continuousLinearMap _
  have hgl : ∀ j, LocallyIntegrable (g j) volume := fun j => column_locallyIntegrable hg.2.1 j
  have hmm : ∀ i, AEStronglyMeasurable (m i) volume := fun i => (hm i).aestronglyMeasurable
  have hdm : AEStronglyMeasurable d volume := hd.aestronglyMeasurable
  have hGi : Integrable (fun y => matSq (G y)) :=
    integrable_of_lintegral_lt (continuous_entrySq.comp_aestronglyMeasurable hGm) (fun y => entrySq_nonneg _) hG2
  have hg2 : ∀ j, Integrable (fun y => ‖g j y‖ ^ 2) := fun j =>
    hGi.mono' ((hgm j).norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have h6i : Integrable (fun y => ‖v y‖ ^ 6) :=
    integrable_of_lintegral_lt (hvm.norm.pow 6) (fun y => by positivity) h6
  set w : ℕ → Space → Space := fun n => mollified n v with hwdef
  have hwC : ∀ n, ContDiff ℝ ∞ (w n) := fun n => mollified_contDiff n hg.1
  have hwD : ∀ n y j, fderiv ℝ (w n) y (unitVector j) = mollified n (g j) y := fun n y j =>
    mollified_fderiv n hg y j
  have hwg2 : ∀ n j, Integrable (fun y => ‖mollified n (g j) y‖ ^ 2) := fun n j =>
    (CellCert.Reduction.MollifySecondApproxInternal.conv_sq_integral_le _ (g j) (hgl j) (hg2 j)).1
  have hw6 : ∀ n, Integrable (fun y => ‖w n y‖ ^ 6) := fun n => mollified_sixth n hg.1 h6i
  have hwm : ∀ n, AEStronglyMeasurable (w n) volume := fun n => (hwC n).continuous.aestronglyMeasurable
  have hwDm : ∀ n, AEStronglyMeasurable (fun y => fderiv ℝ (w n) y) volume := fun n =>
    ((hwC n).continuous_fderiv (by simp)).aestronglyMeasurable
  set ε : ℕ → ℝ := fun n => ∑ j, ∫ y, (‖mollified n (g j) y - g j y‖ ^ 2) with hεdef
  have hdiff : ∀ n j, Integrable (fun y => ‖mollified n (g j) y - g j y‖ ^ 2) := fun n j =>
    CellCert.Reduction.MollifySecondApproxInternal.diff_sq_integrable _ (g j) (hgm j) (hg2 j)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => Finset.sum_nonneg fun j _ => integral_nonneg fun y => by positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin 3)) fun j _ =>
      CellCert.Reduction.MollifySecondApproxInternal.conv_sq_tendsto (g j) (hgm j) (hg2 j)
    rw [Finset.sum_const_zero] at h
    exact h
  have hHv : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 2 / ‖y‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt (CertCell.Internal.slice_inverseSquare_lintegral v G hvm hGm hg h6)
      (ENNReal.mul_lt_top (by norm_num) hG2)
  have hfw : ∀ n y, matSq (fderiv ℝ (w n) y) = ∑ j, ‖mollified n (g j) y‖ ^ 2 := fun n y => by
    simp only [matSq, hwD]
  have hfu : ∀ n y, matSq (fderiv ℝ (w n) y - G y) = ∑ j, ‖mollified n (g j) y - g j y‖ ^ 2 := fun n y => by
    simp only [matSq, ContinuousLinearMap.sub_apply, hwD, hgdef]
  have hHw : ∀ n, ∫⁻ y, ENNReal.ofReal (‖w n y‖ ^ 2 / ‖y‖ ^ 2) < ⊤ := by
    intro n
    refine lt_of_le_of_lt (CertCell.Internal.slice_inverseSquare_lintegral (w n) (fun y => fderiv ℝ (w n) y)
      (hwm n) (hwDm n) (weak_smooth ((hwC n).of_le (by simp))) ?_) (ENNReal.mul_lt_top (by norm_num) ?_)
    · exact (hw6 n).lintegral_lt_top
    · simp only [hfw]
      exact (integrable_finsetSum Finset.univ fun j _ => hwg2 n j).lintegral_lt_top
  have hHu : ∀ n, ∫⁻ y, ENNReal.ofReal (‖w n y - v y‖ ^ 2 / ‖y‖ ^ 2) ≤ ENNReal.ofReal ((2 * Real.sqrt (ε n)) ^ 2) := by
    intro n
    have h6u : ∫⁻ y, ENNReal.ofReal (‖w n y - v y‖ ^ 6) < ⊤ := by
      refine Integrable.lintegral_lt_top ((((hw6 n).add h6i).const_mul 64).mono' (((hwm n).sub hvm).norm.pow 6)
        (ae_of_all _ fun y => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sixth_sub_le _ _
    have hH := CertCell.Internal.slice_inverseSquare_lintegral (fun y => w n y - v y)
      (fun y => fderiv ℝ (w n) y - G y) ((hwm n).sub hvm) ((hwDm n).sub hGm) (weak_sub (weak_smooth ((hwC n).of_le (by simp))) hg) h6u
    refine hH.trans (le_of_eq ?_)
    simp only [hfu]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum Finset.univ fun j _ => hdiff n j)
      (ae_of_all _ fun y => by positivity), integral_finsetSum _ fun j _ => hdiff n j, mul_pow,
      Real.sq_sqrt (hε0 n), ENNReal.ofReal_mul (by norm_num)]
    norm_num
    rw [hεdef]
  have hsm : ∀ n, ∫ y, inner ℝ (w n y) (d y) = -∫ y, ∑ i, inner ℝ (mollified n (g i) y) (m i y) := by
    intro n
    have hH' : Integrable (fun y => ‖w n y‖ ^ 2 / ‖y‖ ^ 2) :=
      integrable_of_lintegral_lt (((hwm n).norm.pow 2).aemeasurable.div
        (continuous_norm.measurable.pow_const 2).aemeasurable).aestronglyMeasurable (fun y => by positivity) (hHw n)
    have hmsum : Integrable (fun y => ∑ i, ‖m i y‖ ^ 2) := integrable_finsetSum Finset.univ fun i _ => hm2 i
    have key := smooth_pairing (hwC n) hm hd hrel
      (integrable_inner_weighted (hwm n) hdm (hHw n) hd2)
      (by
        simp only [hwD]
        exact integrable_cols (fun i => (mollified_contDiff n (hgl i)).continuous.aestronglyMeasurable) hmm
          (hwg2 n) hm2)
      (by
        refine ((hH'.const_mul 3).add hmsum).mono' ?_ ?_
        · exact ((hwm n).norm.aemeasurable.div continuous_norm.measurable.aemeasurable).aestronglyMeasurable.mul
            (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hmm i).norm)
        · refine ae_of_all _ fun y => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have hs : (∑ i, ‖m i y‖) ^ 2 ≤ 3 * ∑ i, ‖m i y‖ ^ 2 := by
            simp only [Fin.sum_univ_three]
            nlinarith [sq_nonneg (‖m 0 y‖ - ‖m 1 y‖), sq_nonneg (‖m 1 y‖ - ‖m 2 y‖),
              sq_nonneg (‖m 0 y‖ - ‖m 2 y‖)]
          have e : ‖w n y‖ ^ 2 / ‖y‖ ^ 2 = (‖w n y‖ / ‖y‖) ^ 2 := by rw [div_pow]
          simp only [Pi.add_apply]
          rw [e]
          nlinarith [sq_nonneg (3 * (‖w n y‖ / ‖y‖) - ∑ i, ‖m i y‖),
            div_nonneg (norm_nonneg (w n y)) (norm_nonneg y), Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (m i y)])
    rw [key]
    simp only [hwD]
  set A : ℝ := ∫ y, inner ℝ (v y) (d y) with hA
  set Bv : ℝ := ∫ y, ∑ i, inner ℝ (g i y) (m i y) with hBv
  set Dd : ℝ := Real.sqrt (∫ y, ‖y‖ ^ 2 * ‖d y‖ ^ 2) with hDd
  set Mm : ℝ := Real.sqrt (∫ y, ∑ i, ‖m i y‖ ^ 2) with hMm
  have hvd : Integrable (fun y => inner ℝ (v y) (d y)) := integrable_inner_weighted hvm hdm hHv hd2
  have hbound : ∀ n, |A + Bv| ≤ (2 * Dd + Mm) * Real.sqrt (ε n) := by
    intro n
    have hwd : Integrable (fun y => inner ℝ (w n y) (d y)) := integrable_inner_weighted (hwm n) hdm (hHw n) hd2
    have e1 : (∫ y, inner ℝ (w n y) (d y)) - A = ∫ y, inner ℝ (w n y - v y) (d y) := by
      rw [hA, ← integral_sub hwd hvd]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [inner_sub_left]
    have b1 : |(∫ y, inner ℝ (w n y) (d y)) - A| ≤ 2 * Real.sqrt (ε n) * Dd := by
      rw [e1]
      exact abs_integral_inner_weighted_le ((hwm n).sub hvm) hdm (by positivity) (hHu n) hd2
    have hcn : Integrable (fun y => ∑ i, inner ℝ (mollified n (g i) y) (m i y)) :=
      integrable_cols (fun i => (mollified_contDiff n (hgl i)).continuous.aestronglyMeasurable) hmm (hwg2 n) hm2
    have hcv : Integrable (fun y => ∑ i, inner ℝ (g i y) (m i y)) := integrable_cols hgm hmm hg2 hm2
    have e2 : (∫ y, ∑ i, inner ℝ (mollified n (g i) y) (m i y)) - Bv =
        ∫ y, ∑ i, inner ℝ (mollified n (g i) y - g i y) (m i y) := by
      rw [hBv, ← integral_sub hcn hcv]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [inner_sub_left, Finset.sum_sub_distrib]
    have b2 : |(∫ y, ∑ i, inner ℝ (mollified n (g i) y) (m i y)) - Bv| ≤ Real.sqrt (ε n) * Mm := by
      rw [e2]
      have h := abs_integral_cols_le (X := fun i y => mollified n (g i) y - g i y) (m := m)
        (fun i => (mollified_contDiff n (hgl i)).continuous.aestronglyMeasurable.sub (hgm i)) hmm (hdiff n) hm2
      rwa [integral_finsetSum _ fun j _ => hdiff n j] at h
    have hsn := hsm n
    have : A + Bv = -((∫ y, inner ℝ (w n y) (d y)) - A) - ((∫ y, ∑ i, inner ℝ (mollified n (g i) y) (m i y)) - Bv) := by
      rw [hsn]; ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    nlinarith [b1, b2, Real.sqrt_nonneg (ε n)]
  have hlim : Tendsto (fun n => (2 * Dd + Mm) * Real.sqrt (ε n)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hε).const_mul (2 * Dd + Mm)
    simpa using this
  have h0 : |A + Bv| ≤ 0 := ge_of_tendsto' hlim hbound
  refine ⟨hvd, ?_⟩
  have : A + Bv = 0 := abs_nonpos_iff.1 h0
  linarith

end PotentialBound

end Internal

end AdjointDefect

end Breakdown

import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveSmoothPieceEpsSeries
import Breakdown.Cert.CoerciveSmoothEpsTailDeriv

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

def restAmp (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2) + ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
    + ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2) + ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)

def restSq (v : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  vortAmp (gradField v) κ σ y ^ 2 + vortGradAmp (secondDerivField v) κ σ y ^ 2 + gradAmp (gradField v) κ σ y ^ 2
    + (velAmp v κ σ y / (1 + ‖y‖)) ^ 2

theorem restSq_nonneg (v : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (y : Space) : 0 ≤ restSq v κ σ y := by
  unfold restSq
  positivity

theorem restAmp_eq (v : ℝ → Space → Space) (κ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    restAmp v κ σ y = ENNReal.ofReal (restSq v κ σ y) := by
  unfold restAmp restSq
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]

theorem norm_meanField_le (W : ℝ → Space → Space) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (y : Space) :
    ‖meanField W y‖ ≤ 9 * D := by
  have hv := Internal.SmoothPieceEps.velAmp_le W hD (0, 0) 0 y
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have h2 : D / (1 + ‖y‖) ≤ D := div_le_self hD0 hy1
  have hc : ∀ i, |(modeVel (0, 0) W 0 y i).re| ≤ velAmp W (0, 0) 0 y := fun i => by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := Real.abs_le_sqrt (x := ‖modeVel (0, 0) W 0 y i‖) (y := cnormSq (modeVel (0, 0) W 0 y))
      (Finset.single_le_sum (f := fun j => ‖modeVel (0, 0) W 0 y j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  unfold meanField
  calc ‖∑ i : Fin 3, (modeVel (0, 0) W 0 y i).re • unitVector i‖
      ≤ ∑ i : Fin 3, ‖(modeVel (0, 0) W 0 y i).re • unitVector i‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, |(modeVel (0, 0) W 0 y i).re| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Internal.SmoothPieceEps.norm_unit, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin 3, velAmp W (0, 0) 0 y := Finset.sum_le_sum fun i _ => hc i
    _ = 3 * velAmp W (0, 0) 0 y := by simp
    _ ≤ 9 * D := by linarith

theorem meanField_deriv_bounds {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ B ∧
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ B := by
  obtain ⟨D, hD⟩ := hS.flow_decay
  exact Internal.SmoothEpsTailDeriv.meanField_curl_bounds hS.flow_smooth hS.flow_periodic hD

theorem meanField_bounds {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖meanField W y‖ ≤ B ∧ ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ B ∧
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := meanField_deriv_bounds hS
  obtain ⟨D, hD⟩ := hS.flow_decay
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  refine ⟨B + 9 * D, by positivity, fun y => ⟨?_, ?_, ?_⟩⟩
  · linarith [norm_meanField_le W hD y]
  · linarith [(hB y).1]
  · linarith [(hB y).2]

theorem norm_axialGen_le (y : Space) : ‖-(y 1) • unitVector 0 + y 0 • unitVector 1‖ ≤ 2 * ‖y‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Internal.SmoothPieceEps.norm_unit, Internal.SmoothPieceEps.norm_unit, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  linarith [Internal.SmoothPieceEps.abs_coord_le y 0, Internal.SmoothPieceEps.abs_coord_le y 1]

theorem norm_relativeVelocity_le (W : ℝ → Space → Space) (a : Space → ℝ) (y : Space) :
    ‖relativeVelocity W a y‖ ≤ ‖meanField W y‖ + 1 / 2 * ‖y‖ + |a y| * (2 * ‖y‖) := by
  unfold relativeVelocity
  have h1 := norm_sub_le (meanField W y + (1 / 2 : ℝ) • y) (a y • (-(y 1) • unitVector 0 + y 0 • unitVector 1))
  have h2 := norm_add_le (meanField W y) ((1 / 2 : ℝ) • y)
  have h3 : ‖(1 / 2 : ℝ) • y‖ = 1 / 2 * ‖y‖ := by rw [norm_smul]; norm_num
  have h4 : ‖a y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)‖ ≤ |a y| * (2 * ‖y‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_axialGen_le y) (abs_nonneg _)
  linarith

theorem restCoeff_bounded {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ι y,
      m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y ≤ M ∧
      m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|) ≤ M ∧
      m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖) ≤ M ∧
      m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ M ∧
      ∀ σ, ∀ α ∈ m.waves, m.eps ι y * velAmp W α σ y ≤ M ∧ m.eps ι y * gradAmp (gradField W) α σ y ≤ M ∧
        m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖) ≤ M ∧
        m.eps ι y * vortAmp (gradField W) α σ y ≤ M := by
  obtain ⟨B, hB0, hB⟩ := meanField_bounds hS
  have ha := hS.admissible
  obtain ⟨Be, hBe⟩ := ha.epsW_decay
  obtain ⟨Br, hBr⟩ := ha.rate_bounded
  obtain ⟨D, hD⟩ := hS.flow_decay
  have hE : ∀ ι y, m.eps ι y ≤ epsSup := fun ι y => ha.epsW_le _ _
  have hE0 : ∀ ι y, 0 ≤ m.eps ι y := fun ι y => abs_nonneg _
  have hEs : 0 ≤ epsSup := (hE0 (0, 0) 0).trans (hE (0, 0) 0)
  have hEy : ∀ ι y, ‖y‖ * m.eps ι y ≤ Be := fun ι y => hBe _ _
  have hBe0 : 0 ≤ Be := (mul_nonneg (norm_nonneg (0 : Space)) (hE0 (0, 0) 0)).trans (hEy (0, 0) 0)
  have hBr0 : 0 ≤ Br := (abs_nonneg _).trans (hBr (m.classOf (0, 0)) 0)
  have hEg : ∀ ι y, m.epsGrad ι y ≤ epsGradSup := fun ι y => ha.epsW_grad_le _ _
  have hEg0 : 0 ≤ epsGradSup := (norm_nonneg _).trans (hEg (0, 0) 0)
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  set M := (epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup) + epsSup * (1 / 2 * B + Br)
    + B * (epsSup + Be) + epsSup * B + epsSup * (729 * D) with hM
  have q1 : 0 ≤ epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup := by positivity
  have q2 : 0 ≤ epsSup * (1 / 2 * B + Br) := by positivity
  have q3 : 0 ≤ B * (epsSup + Be) := by positivity
  have q4 : 0 ≤ epsSup * B := by positivity
  have q5 : 0 ≤ epsSup * (729 * D) := by positivity
  refine ⟨M, by positivity, fun ι y => ⟨?_, ?_, ?_, ?_, fun σ α _ => ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · have r1 := norm_relativeVelocity_le W (m.rate (m.classOf ι)) y
    have p1 : m.eps ι y * ‖meanField W y‖ ≤ epsSup * B := mul_le_mul (hE ι y) (hB y).1 (norm_nonneg _) hEs
    have p2 : |m.rate (m.classOf ι) y| * (‖y‖ * m.eps ι y) ≤ Br * Be :=
      mul_le_mul (hBr _ _) (hEy ι y) (mul_nonneg (norm_nonneg _) (hE0 ι y)) hBr0
    have p3 := hEy ι y
    calc m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y
        ≤ m.eps ι y * (‖meanField W y‖ + 1 / 2 * ‖y‖ + |m.rate (m.classOf ι) y| * (2 * ‖y‖)) + epsGradSup :=
          add_le_add (mul_le_mul_of_nonneg_left r1 (hE0 ι y)) (hEg ι y)
      _ = m.eps ι y * ‖meanField W y‖ + 1 / 2 * (‖y‖ * m.eps ι y)
          + 2 * (|m.rate (m.classOf ι) y| * (‖y‖ * m.eps ι y)) + epsGradSup := by ring
      _ ≤ epsSup * B + 1 / 2 * Be + 2 * (Br * Be) + epsGradSup := by linarith
      _ ≤ M := by linarith
  · have : m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|)
        ≤ epsSup * (1 / 2 * B + Br) :=
      mul_le_mul (hE ι y) (by linarith [(hB y).2.1, hBr (m.classOf ι) y]) (by positivity) hEs
    linarith
  · have : m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (1 + ‖y‖)
        = ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (m.eps ι y + ‖y‖ * m.eps ι y) := by ring
    rw [this]
    have : ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * (m.eps ι y + ‖y‖ * m.eps ι y)
        ≤ B * (epsSup + Be) :=
      mul_le_mul (hB y).2.2 (add_le_add (hE ι y) (hEy ι y))
        (add_nonneg (hE0 ι y) (mul_nonneg (norm_nonneg _) (hE0 ι y))) hB0
    linarith
  · have : m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ epsSup * B :=
      mul_le_mul (hE ι y) (hB y).2.1 (norm_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.velAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ≤ D := div_le_self hD0 hy1
    have : m.eps ι y * velAmp W α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.gradAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ hy1)
    have : m.eps ι y * gradAmp (gradField W) α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have hyp : 0 < 1 + ‖y‖ := by positivity
    have h1 := Internal.SmoothPieceEps.vortGradAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (le_self_pow₀ hy1 (by norm_num)) hD0
    have h3 : vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖) ≤ 729 * D := by
      have := mul_le_mul_of_nonneg_right h1 hyp.le
      nlinarith [this, h2]
    have : m.eps ι y * (vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)) ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) h3 (mul_nonneg (Real.sqrt_nonneg _) hyp.le) hEs
    calc m.eps ι y * vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)
        = m.eps ι y * (vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖)) := by ring
      _ ≤ M := by linarith
  · have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have h1 := Internal.SmoothPieceEps.vortAmp_le W hD α σ y
    have h2 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ hy1)
    have : m.eps ι y * vortAmp (gradField W) α σ y ≤ epsSup * (729 * D) :=
      mul_le_mul (hE ι y) (by linarith) (Real.sqrt_nonneg _) hEs
    linarith

theorem prod_le_sq {a M x z : ℝ} (hA : a ≤ M) (ha : 0 ≤ a) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    a * x * z ≤ M * (x ^ 2 + z ^ 2) := by
  have hM : 0 ≤ M := ha.trans hA
  have h1 : a * x * z ≤ M * x * z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hx) hz
  have h2 : x * z ≤ x ^ 2 + z ^ 2 := by nlinarith [sq_nonneg (x - z)]
  calc a * x * z ≤ M * x * z := h1
    _ = M * (x * z) := by ring
    _ ≤ M * (x ^ 2 + z ^ 2) := mul_le_mul_of_nonneg_left h2 hM

theorem regroup (p q s r : ℝ) (hr : r ≠ 0) : p * q * s = p * r * (q / r) * s := by
  have h : r * (q / r) = q := by field_simp
  rw [mul_assoc p r, h]

theorem negRest_le_restAmp {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ σ y ι,
      ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y)
        ≤ K * (restAmp v ι σ y + ∑ α ∈ m.waves, restAmp v (ι - α) σ y) := by
  obtain ⟨M, hM0, hM⟩ := restCoeff_bounded hS
  refine ⟨ENNReal.ofReal (M * (4 + 4 * m.waves.card)), ENNReal.ofReal_ne_top, fun σ y ι => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := hM ι y
  have e0 : 0 ≤ m.eps ι y := abs_nonneg _
  have hy : 0 < (1 + ‖y‖) := by positivity
  have hG : 0 ≤ vortAmp (gradField v) ι σ y := Real.sqrt_nonneg _
  have hH : 0 ≤ vortGradAmp (secondDerivField v) ι σ y := Real.sqrt_nonneg _
  have hGr : 0 ≤ gradAmp (gradField v) ι σ y := Real.sqrt_nonneg _
  have hVl : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
  have hR0def : restSq v ι σ y = vortAmp (gradField v) ι σ y ^ 2 + vortGradAmp (secondDerivField v) ι σ y ^ 2 + gradAmp (gradField v) ι σ y ^ 2 + (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := rfl
  have hRα : ∀ κ, 0 ≤ restSq v κ σ y := fun κ => restSq_nonneg v κ σ y
  have hR0 : 0 ≤ restSq v ι σ y := restSq_nonneg v ι σ y
  have hRel : 0 ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ := norm_nonneg _
  have hEg : 0 ≤ m.epsGrad ι y := norm_nonneg _
  have t1 : (m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y) * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y ≤ M * (vortGradAmp (secondDerivField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) :=
    prod_le_sq c1 (add_nonneg (mul_nonneg e0 hRel) hEg) hH hG
  have t2 : m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|) * vortAmp (gradField v) ι σ y ^ 2 ≤ M * vortAmp (gradField v) ι σ y ^ 2 :=
    mul_le_mul_of_nonneg_right c2 (sq_nonneg _)
  have t3 : m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * velAmp v ι σ y * vortAmp (gradField v) ι σ y ≤ M * ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2 + vortAmp (gradField v) ι σ y ^ 2) := by
    rw [regroup (m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖) (velAmp v ι σ y) (vortAmp (gradField v) ι σ y) (1 + ‖y‖) hy.ne']
    exact prod_le_sq c3 (mul_nonneg (mul_nonneg e0 (norm_nonneg _)) hy.le) (div_nonneg hVl hy.le) hG
  have t4 : m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ * gradAmp (gradField v) ι σ y * vortAmp (gradField v) ι σ y ≤ M * (gradAmp (gradField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) :=
    prod_le_sq c4 (mul_nonneg e0 (norm_nonneg _)) hGr hG
  have t5 : m.eps ι y * vortAmp (gradField v) ι σ y * ∑ α ∈ m.waves,
          (velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y
            + gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y
            + vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y
            + vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y)
      ≤ M * ∑ α ∈ m.waves, (4 * vortAmp (gradField v) ι σ y ^ 2 + restSq v (ι - α) σ y) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun α hα => ?_
    obtain ⟨d1, d2, d3, d4⟩ := c5 σ α hα
    have a1 : 0 ≤ velAmp W α σ y := Real.sqrt_nonneg _
    have a2 : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have a3 : 0 ≤ vortGradAmp (secondDerivField W) α σ y := Real.sqrt_nonneg _
    have a4 : 0 ≤ vortAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have b1 : 0 ≤ vortGradAmp (secondDerivField v) (ι - α) σ y := Real.sqrt_nonneg _
    have b2 : 0 ≤ vortAmp (gradField v) (ι - α) σ y := Real.sqrt_nonneg _
    have b3 : 0 ≤ velAmp v (ι - α) σ y := Real.sqrt_nonneg _
    have b4 : 0 ≤ gradAmp (gradField v) (ι - α) σ y := Real.sqrt_nonneg _
    have s1 := prod_le_sq d1 (mul_nonneg e0 a1) b1 hG
    have s2 := prod_le_sq d2 (mul_nonneg e0 a2) b2 hG
    have s3 := prod_le_sq d3 (mul_nonneg (mul_nonneg e0 a3) hy.le) (div_nonneg b3 hy.le) hG
    have s4 := prod_le_sq d4 (mul_nonneg e0 a4) b4 hG
    have e3 := regroup (m.eps ι y * vortGradAmp (secondDerivField W) α σ y) (velAmp v (ι - α) σ y) (vortAmp (gradField v) ι σ y) (1 + ‖y‖) hy.ne'
    have hsum : m.eps ι y * vortAmp (gradField v) ι σ y * (velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y
        + gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y
        + vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y
        + vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y)
        = m.eps ι y * velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y * vortAmp (gradField v) ι σ y
          + m.eps ι y * gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y * vortAmp (gradField v) ι σ y
          + m.eps ι y * vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y * vortAmp (gradField v) ι σ y
          + m.eps ι y * vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y * vortAmp (gradField v) ι σ y := by ring
    have hq : restSq v (ι - α) σ y = vortAmp (gradField v) (ι - α) σ y ^ 2 + vortGradAmp (secondDerivField v) (ι - α) σ y ^ 2 + gradAmp (gradField v) (ι - α) σ y ^ 2
        + (velAmp v (ι - α) σ y / (1 + ‖y‖)) ^ 2 := rfl
    rw [hsum, e3, hq]
    linarith [s1, s2, s3, s4]
  have hexp : -modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y =
      (m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y) * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y
      + m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|) * vortAmp (gradField v) ι σ y ^ 2
      + m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * velAmp v ι σ y * vortAmp (gradField v) ι σ y
      + m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ * gradAmp (gradField v) ι σ y * vortAmp (gradField v) ι σ y
      + m.eps ι y * vortAmp (gradField v) ι σ y * ∑ α ∈ m.waves,
          (velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y
            + gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y
            + vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y
            + vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y) := by
    unfold modeEpsRest
    ring
  have hS4 : ∑ α ∈ m.waves, (4 * vortAmp (gradField v) ι σ y ^ 2 + restSq v (ι - α) σ y)
      = 4 * m.waves.card * vortAmp (gradField v) ι σ y ^ 2 + ∑ α ∈ m.waves, restSq v (ι - α) σ y := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hSig : 0 ≤ ∑ α ∈ m.waves, restSq v (ι - α) σ y := Finset.sum_nonneg fun α _ => hRα _
  have hc : (0 : ℝ) ≤ m.waves.card := Nat.cast_nonneg _
  have hG2 : vortAmp (gradField v) ι σ y ^ 2 ≤ restSq v ι σ y := by
    rw [hR0def]; nlinarith [sq_nonneg (vortGradAmp (secondDerivField v) ι σ y), sq_nonneg (gradAmp (gradField v) ι σ y), sq_nonneg (velAmp v ι σ y / (1 + ‖y‖))]
  have hH2 : vortGradAmp (secondDerivField v) ι σ y ^ 2 + gradAmp (gradField v) ι σ y ^ 2 + (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 + vortAmp (gradField v) ι σ y ^ 2 = restSq v ι σ y := by
    rw [hR0def]; ring
  have key : (vortGradAmp (secondDerivField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + vortAmp (gradField v) ι σ y ^ 2 + ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + (gradAmp (gradField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2)
      + (4 * m.waves.card * vortAmp (gradField v) ι σ y ^ 2 + ∑ α ∈ m.waves, restSq v (ι - α) σ y)
      ≤ (4 + 4 * m.waves.card) * (restSq v ι σ y + ∑ α ∈ m.waves, restSq v (ι - α) σ y) := by
    linarith [mul_le_mul_of_nonneg_left hG2 hc, mul_nonneg hc hSig, mul_nonneg hc hR0, hSig, hR0, hG2, hH2]
  have hk := mul_le_mul_of_nonneg_left key hM0
  rw [hS4] at t5
  have hrest : -modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y ≤
      M * (4 + 4 * m.waves.card) * (restSq v ι σ y + ∑ α ∈ m.waves, restSq v (ι - α) σ y) := by
    rw [hexp]
    calc _ ≤ M * (vortGradAmp (secondDerivField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + M * vortAmp (gradField v) ι σ y ^ 2 + M * ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2 + vortAmp (gradField v) ι σ y ^ 2)
          + M * (gradAmp (gradField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + M * (4 * m.waves.card * vortAmp (gradField v) ι σ y ^ 2 + ∑ α ∈ m.waves, restSq v (ι - α) σ y) :=
          add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) t5
      _ = M * ((vortGradAmp (secondDerivField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + vortAmp (gradField v) ι σ y ^ 2 + ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2 + vortAmp (gradField v) ι σ y ^ 2) + (gradAmp (gradField v) ι σ y ^ 2 + vortAmp (gradField v) ι σ y ^ 2)
      + (4 * m.waves.card * vortAmp (gradField v) ι σ y ^ 2 + ∑ α ∈ m.waves, restSq v (ι - α) σ y)) := by ring
      _ ≤ M * ((4 + 4 * m.waves.card) * (restSq v ι σ y + ∑ α ∈ m.waves, restSq v (ι - α) σ y)) := hk
      _ = _ := by ring
  have hR : ENNReal.ofReal (restSq v ι σ y + ∑ α ∈ m.waves, restSq v (ι - α) σ y)
      = restAmp v ι σ y + ∑ α ∈ m.waves, restAmp v (ι - α) σ y := by
    rw [ENNReal.ofReal_add hR0 hSig, ENNReal.ofReal_sum_of_nonneg (fun α _ => hRα _), restAmp_eq]
    simp only [restAmp_eq]
  rw [← hR, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hrest

theorem tsum_restAmp_shift (s : Finset (ℤ × ℤ)) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ∑' ι, (restAmp v ι σ y + ∑ α ∈ s, restAmp v (ι - α) σ y)
      = ((1 : ℝ≥0∞) + s.card) * ∑' ι, restAmp v ι σ y := by
  have hsh : ∀ α : ℤ × ℤ, ∑' ι, restAmp v (ι - α) σ y = ∑' ι, restAmp v ι σ y := fun α =>
    (Equiv.subRight α).tsum_eq (fun ι => restAmp v ι σ y)
  have hsum : ∑' ι, ∑ α ∈ s, restAmp v (ι - α) σ y = ∑ α ∈ s, ∑' ι, restAmp v (ι - α) σ y := by
    exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
  rw [ENNReal.tsum_add, hsum, Finset.sum_congr rfl (fun α _ => hsh α), Finset.sum_const, nsmul_eq_mul, add_mul,
    one_mul]

theorem tsum_restAmp_eq (v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    ∑' ι, restAmp v ι σ y =
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) := by
  unfold restAmp
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]

theorem lintegral_negRest_lt_top (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι,
      ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y)) < ⊤ := by
  obtain ⟨K, hK, hle⟩ := negRest_le_restAmp hS
  have hA := Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hS.smooth
  set c : ℝ≥0∞ := K * ((1 : ℝ≥0∞) + m.waves.card)
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top hK (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.natCast_ne_top _⟩)
  have hpt : ∀ σ y, ∑' ι, ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y)
      ≤ c * ∑' ι, restAmp v ι σ y := fun σ y => by
    calc ∑' ι, ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y)
        ≤ ∑' ι, K * (restAmp v ι σ y + ∑ α ∈ m.waves, restAmp v (ι - α) σ y) :=
          ENNReal.tsum_le_tsum fun ι => hle σ y ι
      _ = c * ∑' ι, restAmp v ι σ y := by
          rw [ENNReal.tsum_mul_left, tsum_restAmp_shift, mul_assoc]
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι,
      ENNReal.ofReal (-modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, c * ∑' ι, restAmp v ι σ y :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, restAmp v ι σ y := by
        simp_rw [lintegral_const_mul' c _ hc]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) ?_
        simp_rw [tsum_restAmp_eq]
        exact hA

end SmoothEpsInternal

end Coercive

end Breakdown

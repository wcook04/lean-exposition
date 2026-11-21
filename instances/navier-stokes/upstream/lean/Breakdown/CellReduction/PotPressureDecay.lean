import Breakdown.CellReduction.PotPressureDecayProfile

open scoped ContDiff Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline cellIndex cellCount weightPoly heightRatio)

namespace Internal.PressureDecay

def planePoint (y : Space) : ℂ := ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I

theorem norm_planePoint_sq (v : Space) : ‖planePoint v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  unfold planePoint
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

theorem norm_sq_three (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem planePoint_sub (z w : Space) : planePoint z - planePoint w = planePoint (z - w) := by
  unfold planePoint
  simp only [PiLp.sub_apply]
  push_cast
  ring

theorem norm_planePoint_le (v : Space) : ‖planePoint v‖ ≤ ‖v‖ := by
  have h1 := norm_planePoint_sq v
  have h2 := norm_sq_three v
  have h3 : ‖planePoint v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h1, h2]
    nlinarith [sq_nonneg (v 2)]
  nlinarith [norm_nonneg (planePoint v), norm_nonneg v]

theorem planePoint_slopeBound (z w : Space) : ‖planePoint z - planePoint w‖ ≤ ‖z - w‖ := by
  rw [planePoint_sub]
  exact norm_planePoint_le _

theorem one_sub_height_sq {y : Space} (hy : y ≠ 0) : 1 - heightRatio y ^ 2 = ‖planePoint y‖ ^ 2 / ‖y‖ ^ 2 := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h3 := norm_sq_three y
  rw [norm_planePoint_sq, CellCert.GivenFields.heightRatio, div_pow, eq_div_iff (by positivity), sub_mul, one_mul,
    div_mul_cancel₀ _ (by positivity)]
  linarith

theorem angle_exp (M : ℤ) {w : ℂ} (hw : w ≠ 0) :
    Complex.exp ((((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) = ((‖w‖ : ℂ)⁻¹ * w) ^ M := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have h1 : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = (‖w‖ : ℂ)⁻¹ * w := by
    rw [eq_inv_mul_iff_mul_eq₀ hn, Complex.norm_mul_exp_arg_mul_I]
  rw [← h1, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem norm_unit {w : ℂ} (hw : w ≠ 0) : ‖(‖w‖ : ℂ)⁻¹ * w‖ = 1 := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw', inv_mul_cancel₀ hw'.ne']

theorem unit_sub_le {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    ‖(‖w‖ : ℂ)⁻¹ * w - (‖v‖ : ℂ)⁻¹ * v‖ ≤ 2 * ‖w - v‖ / ‖w‖ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e : (‖w‖ : ℂ)⁻¹ * w - (‖v‖ : ℂ)⁻¹ * v =
      (‖w‖ : ℂ)⁻¹ * (w - v) + (((‖v‖ - ‖w‖) / (‖w‖ * ‖v‖) : ℝ) : ℂ) * v := by
    have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw'.ne'
    have hm : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hv'.ne'
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hw', abs_div, abs_of_pos (mul_pos hw' hv')]
  have h1 : |‖v‖ - ‖w‖| ≤ ‖w - v‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le w v
  have e2 : |‖v‖ - ‖w‖| / (‖w‖ * ‖v‖) * ‖v‖ = |‖v‖ - ‖w‖| / ‖w‖ := by
    field_simp
  rw [e2, inv_mul_eq_div, ← add_div]
  apply div_le_div_of_nonneg_right _ hw'.le
  linarith

theorem pow_sub_le_of_norm_one {ζ ξ : ℂ} (hζ : ‖ζ‖ = 1) (hξ : ‖ξ‖ = 1) :
    ∀ n : ℕ, ‖ζ ^ n - ξ ^ n‖ ≤ n * ‖ζ - ξ‖
  | 0 => by simp
  | n + 1 => by
    have ih := pow_sub_le_of_norm_one hζ hξ n
    have e : ζ ^ (n + 1) - ξ ^ (n + 1) = ζ ^ n * (ζ - ξ) + (ζ ^ n - ξ ^ n) * ξ := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, hζ, hξ, one_pow, one_mul, mul_one]
    push_cast
    linarith

theorem zpow_sub_le_of_norm_one {ζ ξ : ℂ} (hζ : ‖ζ‖ = 1) (hξ : ‖ξ‖ = 1) (M : ℤ) :
    ‖ζ ^ M - ξ ^ M‖ ≤ |(M : ℝ)| * ‖ζ - ξ‖ := by
  rcases M with n | n
  · have := pow_sub_le_of_norm_one hζ hξ n
    simpa [zpow_natCast] using this
  · have h0 : ζ ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hζ]; norm_num))
    have h1 : ξ ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hξ]; norm_num))
    rw [zpow_negSucc, zpow_negSucc, inv_sub_inv' h0 h1, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow,
      norm_pow, hζ, hξ, one_pow, inv_one, one_mul, mul_one, norm_sub_rev, Int.cast_negSucc, abs_neg,
      Nat.abs_cast]
    exact pow_sub_le_of_norm_one hζ hξ (n + 1)

theorem exp_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have e : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  simpa [Real.norm_eq_abs] using this

theorem phase_slope {F : ℝ → ℝ} (hF : IsRadialPhase F) :
    ∃ B, 0 ≤ B ∧ ∀ c > 0, ∀ u v, c ≤ u → c ≤ v → |F u - F v| ≤ B / c * |u - v| := by
  obtain ⟨B, hB, hd⟩ := GivenShape.Internal.radialPhase_derivs hF
  refine ⟨B, hB, fun c hc u v hu hv => ?_⟩
  have hder : ∀ x ∈ Ici c, HasDerivWithinAt F (deriv F x) (Ici c) x :=
    fun x hx => ((hd x (hc.trans_le hx)).1).hasDerivWithinAt
  have hbd : ∀ x ∈ Ici c, ‖deriv F x‖ ≤ B / c := by
    intro x hx
    have hx0 : 0 < x := hc.trans_le hx
    have h1 := (hd x hx0).2.2.2.1
    rw [abs_mul, abs_of_pos hx0] at h1
    rw [Real.norm_eq_abs, le_div_iff₀ hc]
    calc |deriv F x| * c ≤ |deriv F x| * x := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = x * |deriv F x| := mul_comm _ _
      _ ≤ B := h1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Ici c) hv hu
  simpa [Real.norm_eq_abs] using this

theorem chart_bounds (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    0 ≤ chartCoord P y ∧ chartCoord P y ≤ 1 := by
  have h := GivenShape.Internal.one_sub_chartCoord P hL y
  have hd : 0 < ‖y‖ + P.chartLength := by positivity
  refine ⟨by unfold chartCoord; positivity, ?_⟩
  have : 0 ≤ P.chartLength / (‖y‖ + P.chartLength) := by positivity
  linarith

theorem chart_diff (P : ShapeParams) (hL : 0 < P.chartLength) (z w : Space) :
    |chartCoord P z - chartCoord P w| ≤
      (1 - chartCoord P z) * (1 - chartCoord P w) / P.chartLength * ‖z - w‖ := by
  have hz : 0 < ‖z‖ + P.chartLength := by positivity
  have hw : 0 < ‖w‖ + P.chartLength := by positivity
  rw [show chartCoord P z - chartCoord P w = (1 - chartCoord P w) - (1 - chartCoord P z) by ring,
    GivenShape.Internal.one_sub_chartCoord P hL z, GivenShape.Internal.one_sub_chartCoord P hL w]
  have e : P.chartLength / (‖w‖ + P.chartLength) - P.chartLength / (‖z‖ + P.chartLength) =
      P.chartLength / (‖z‖ + P.chartLength) * (P.chartLength / (‖w‖ + P.chartLength)) / P.chartLength *
        (‖z‖ - ‖w‖) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z w) (by positivity)

theorem chartGap_le (L r : ℝ) (hL : 0 < L) (hr : 0 ≤ r) : L / (r + L) ≤ max L 1 / (1 + r) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total L 1 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

theorem one_sub_chart_le_double (P : ShapeParams) (hL : 0 < P.chartLength) {r : ℝ} (hr : 0 ≤ r) {v : Space}
    (hv : r / 2 ≤ ‖v‖) : 1 - chartCoord P v ≤ 2 * (P.chartLength / (r + P.chartLength)) := by
  rw [GivenShape.Internal.one_sub_chartCoord P hL v, ← mul_div_assoc,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem half_ball_bounds {y v : Space} (hv : v ∈ Metric.ball y (‖planePoint y‖ / 2)) :
    ‖y‖ / 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 3 * ‖y‖ / 2 ∧ ‖planePoint y‖ / 2 ≤ ‖planePoint v‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hv
  have h1 := abs_le.1 (abs_norm_sub_norm_le v y)
  have h2 := abs_le.1 (abs_norm_sub_norm_le (planePoint v) (planePoint y))
  have h3 := planePoint_slopeBound v y
  have h4 := norm_planePoint_le y
  refine ⟨by linarith, by linarith, by linarith⟩

def phasedProfile (P : ShapeParams) (Φ : ℝ → ℝ → ℂ) (M j : ℤ) (a : ℝ) (y : Space) : ℂ :=
  Complex.exp (((a + (M : ℝ) * pointAngle y + (j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
    Φ (chartCoord P y) (heightRatio y)

theorem phasedProfile_split (P : ShapeParams) (Φ : ℝ → ℝ → ℂ) (M j : ℤ) (a : ℝ) (y : Space) :
    phasedProfile P Φ M j a y = Complex.exp ((a : ℂ) * Complex.I) *
      (Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) *
      Φ (chartCoord P y) (heightRatio y) := by
  unfold phasedProfile
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem phasedProfile_value (P : ShapeParams) (hL : 0 < P.chartLength) (Φ : ℝ → ℝ → ℂ) (k : ℕ) (Cv : ℝ)
    (hCv : 0 ≤ Cv) (hv : ∀ t x, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖Φ t x‖ ≤ Cv * (1 - t) ^ 2 * (1 - x ^ 2) ^ k)
    (M j : ℤ) (a : ℝ) (y : Space) :
    ‖phasedProfile P Φ M j a y‖ ≤ Cv * max P.chartLength 1 ^ 2 / (1 + ‖y‖) ^ 2 := by
  unfold phasedProfile
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  obtain ⟨ht0, ht1⟩ := chart_bounds P hL y
  have hx := GivenShape.Internal.abs_heightRatio_le y
  refine (hv _ _ ht0 ht1 hx).trans ?_
  have hA := axisPow_le_one k hx
  have hA0 := axisPow_nonneg k hx
  have hu := chartGap_le P.chartLength ‖y‖ hL (norm_nonneg y)
  rw [← GivenShape.Internal.one_sub_chartCoord P hL y] at hu
  have hu0 : 0 ≤ 1 - chartCoord P y := by linarith
  have hsq : (1 - chartCoord P y) ^ 2 ≤ (max P.chartLength 1 / (1 + ‖y‖)) ^ 2 := pow_le_pow_left₀ hu0 hu 2
  rw [div_pow] at hsq
  calc Cv * (1 - chartCoord P y) ^ 2 * (1 - heightRatio y ^ 2) ^ k ≤ Cv * (1 - chartCoord P y) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ Cv * (max P.chartLength 1 ^ 2 / (1 + ‖y‖) ^ 2) * 1 := by gcongr
    _ = Cv * max P.chartLength 1 ^ 2 / (1 + ‖y‖) ^ 2 := by ring

theorem decay_rate_combine {u r L cL A Ct : ℝ} (hu : 0 ≤ u) (hr : 0 < r) (hL : 0 < L) (hA : 0 ≤ A) (hCt : 0 ≤ Ct)
    (hucL : u ≤ cL / (1 + r)) :
    A * (u ^ 2 / r) + 8 * Ct * (u ^ 3 / L) ≤ (A * cL ^ 2 + 8 * Ct * cL ^ 3 / L) / (r * (1 + r) ^ 2) := by
  have h1r : 0 < 1 + r := by linarith
  have hcL : 0 ≤ cL := by
    have : 0 ≤ cL / (1 + r) := hu.trans hucL
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hu2 : u ^ 2 ≤ cL ^ 2 / (1 + r) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hu hucL 2
  have hu3 : u ^ 3 ≤ cL ^ 3 / (1 + r) ^ 3 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ hu hucL 3
  have e1 : u ^ 2 / r ≤ cL ^ 2 / (r * (1 + r) ^ 2) := by
    rw [div_le_div_iff₀ hr (by positivity)]
    have := mul_le_mul_of_nonneg_right hu2 (le_of_lt (by positivity : (0 : ℝ) < r * (1 + r) ^ 2))
    calc u ^ 2 * (r * (1 + r) ^ 2) ≤ cL ^ 2 / (1 + r) ^ 2 * (r * (1 + r) ^ 2) := this
      _ = cL ^ 2 * r := by field_simp
  have e2 : u ^ 3 / L ≤ cL ^ 3 / L / (r * (1 + r) ^ 2) := by
    rw [div_div, div_le_div_iff₀ hL (by positivity)]
    have h3 : cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) ≤ cL ^ 3 * L := by
      rw [show cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) = cL ^ 3 * L * (r / (1 + r)) by
        field_simp]
      have : r / (1 + r) ≤ 1 := (div_le_one h1r).2 (by linarith)
      have : 0 ≤ cL ^ 3 * L := by positivity
      nlinarith
    calc u ^ 3 * (L * (r * (1 + r) ^ 2)) ≤ cL ^ 3 / (1 + r) ^ 3 * (L * (r * (1 + r) ^ 2)) :=
          mul_le_mul_of_nonneg_right hu3 (by positivity)
      _ ≤ cL ^ 3 * L := h3
  have e3 : (A * cL ^ 2 + 8 * Ct * cL ^ 3 / L) / (r * (1 + r) ^ 2) =
      A * (cL ^ 2 / (r * (1 + r) ^ 2)) + 8 * Ct * (cL ^ 3 / L / (r * (1 + r) ^ 2)) := by ring
  rw [e3]
  have := mul_le_mul_of_nonneg_left e1 hA
  have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 8 * Ct)
  linarith

theorem angleTerm_bound (M : ℤ) (k : ℕ) (hMk : M ≠ 0 → 1 ≤ k) {Cv : ℝ} (hCv : 0 ≤ Cv) {z w : Space} (hplz : planePoint z ≠ 0)
    (hplw : planePoint w ≠ 0) {c : ℂ} {tz u r : ℝ} (hc : ‖c‖ ≤ Cv * (1 - tz) ^ 2 * (1 - heightRatio z ^ 2) ^ k)
    (huz2 : (1 - tz) ^ 2 ≤ 4 * u ^ 2) (hnz : r / 2 ≤ ‖z‖) (hr : 0 < r) :
    ‖Complex.exp ((((M : ℝ) * pointAngle z : ℝ) : ℂ) * Complex.I) -
        Complex.exp ((((M : ℝ) * pointAngle w : ℝ) : ℂ) * Complex.I)‖ * ‖c‖ ≤
      16 * |(M : ℝ)| * Cv * (u ^ 2 / r) * ‖z - w‖ := by
  have hpz : 0 < ‖planePoint z‖ := norm_pos_iff.2 hplz
  have hnz0 : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hnz0
  have hxz := GivenShape.Internal.abs_heightRatio_le z
  have hD0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have A1 : ‖Complex.exp ((((M : ℝ) * pointAngle z : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((((M : ℝ) * pointAngle w : ℝ) : ℂ) * Complex.I)‖ ≤ |(M : ℝ)| * (2 * ‖z - w‖ / ‖planePoint z‖) := by
    rw [show pointAngle z = Complex.arg (planePoint z) from rfl, show pointAngle w = Complex.arg (planePoint w) from rfl,
      angle_exp M hplz, angle_exp M hplw]
    refine (zpow_sub_le_of_norm_one (norm_unit hplz) (norm_unit hplw) M).trans ?_
    refine mul_le_mul_of_nonneg_left ((unit_sub_le hplz hplw).trans ?_) (abs_nonneg _)
    exact div_le_div_of_nonneg_right (by linarith [planePoint_slopeBound z w]) hpz.le
  have A2 : |(M : ℝ)| * ‖c‖ ≤ |(M : ℝ)| * (Cv * (1 - tz) ^ 2 * (‖planePoint z‖ ^ 2 / ‖z‖ ^ 2)) := by
    by_cases hM : M = 0
    · simp [hM]
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine hc.trans ?_
      have hk := hMk hM
      have h1 : (1 - heightRatio z ^ 2) ^ k ≤ 1 - heightRatio z ^ 2 := by
        calc (1 - heightRatio z ^ 2) ^ k ≤ (1 - heightRatio z ^ 2) ^ 1 :=
              pow_le_pow_of_le_one (base_nonneg hxz) (base_le_one _) hk
          _ = _ := pow_one _
      exact mul_le_mul_of_nonneg_left (h1.trans (le_of_eq (one_sub_height_sq hz0))) (by positivity)
  have A3 : 2 * ‖z - w‖ / ‖planePoint z‖ * (|(M : ℝ)| * (Cv * (1 - tz) ^ 2 * (‖planePoint z‖ ^ 2 / ‖z‖ ^ 2))) ≤
      2 * |(M : ℝ)| * Cv * ((1 - tz) ^ 2 / ‖z‖) * ‖z - w‖ := by
    have e : 2 * ‖z - w‖ / ‖planePoint z‖ * (|(M : ℝ)| * (Cv * (1 - tz) ^ 2 * (‖planePoint z‖ ^ 2 / ‖z‖ ^ 2))) =
        2 * |(M : ℝ)| * Cv * ((1 - tz) ^ 2 / ‖z‖) * ‖z - w‖ * (‖planePoint z‖ / ‖z‖) := by
      field_simp
    rw [e]
    have h1 : ‖planePoint z‖ / ‖z‖ ≤ 1 := (div_le_one hnz0).2 (norm_planePoint_le z)
    have h2 : 0 ≤ 2 * |(M : ℝ)| * Cv * ((1 - tz) ^ 2 / ‖z‖) * ‖z - w‖ := by positivity
    calc _ ≤ 2 * |(M : ℝ)| * Cv * ((1 - tz) ^ 2 / ‖z‖) * ‖z - w‖ * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := mul_one _
  have A4 : (1 - tz) ^ 2 / ‖z‖ ≤ 8 * (u ^ 2 / r) := by
    have hinv : 1 / ‖z‖ ≤ 2 / r := by
      rw [div_le_div_iff₀ hnz0 hr]
      linarith
    calc (1 - tz) ^ 2 / ‖z‖ = (1 - tz) ^ 2 * (1 / ‖z‖) := by ring
      _ ≤ (4 * u ^ 2) * (2 / r) := mul_le_mul huz2 hinv (by positivity) (by positivity)
      _ = 8 * (u ^ 2 / r) := by ring
  calc _ ≤ |(M : ℝ)| * (2 * ‖z - w‖ / ‖planePoint z‖) * ‖c‖ := mul_le_mul_of_nonneg_right A1 (norm_nonneg _)
    _ = 2 * ‖z - w‖ / ‖planePoint z‖ * (|(M : ℝ)| * ‖c‖) := by ring
    _ ≤ 2 * ‖z - w‖ / ‖planePoint z‖ * (|(M : ℝ)| * (Cv * (1 - tz) ^ 2 * (‖planePoint z‖ ^ 2 / ‖z‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left A2 (by positivity)
    _ ≤ 2 * |(M : ℝ)| * Cv * ((1 - tz) ^ 2 / ‖z‖) * ‖z - w‖ := A3
    _ ≤ 2 * |(M : ℝ)| * Cv * (8 * (u ^ 2 / r)) * ‖z - w‖ := by gcongr
    _ = 16 * |(M : ℝ)| * Cv * (u ^ 2 / r) * ‖z - w‖ := by ring

theorem radialPhaseTerm_bound (j : ℤ) (F : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hph : ∀ c > 0, ∀ u v, c ≤ u → c ≤ v → |F u - F v| ≤ B / c * |u - v|) {z w : Space} {c : ℂ}
    {Cv u r : ℝ} (hc : ‖c‖ ≤ 4 * Cv * u ^ 2) (hr : 0 < r) (hz1 : r / 2 ≤ ‖z‖)
    (hz2 : ‖z‖ ≤ 3 * r / 2) (hw1 : r / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 3 * r / 2) :
    ‖Complex.exp ((((j : ℝ) * F (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) -
        Complex.exp ((((j : ℝ) * F (‖w‖ ^ 2) : ℝ) : ℂ) * Complex.I)‖ * ‖c‖ ≤
      48 * |(j : ℝ)| * B * Cv * (u ^ 2 / r) * ‖z - w‖ := by
  have hD0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have B1 : ‖Complex.exp ((((j : ℝ) * F (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((((j : ℝ) * F (‖w‖ ^ 2) : ℝ) : ℂ) * Complex.I)‖ ≤ |(j : ℝ)| * |F (‖z‖ ^ 2) - F (‖w‖ ^ 2)| := by
    refine (exp_I_sub_le _ _).trans (le_of_eq ?_)
    rw [← mul_sub, abs_mul]
  have hc4 : 0 < r ^ 2 / 4 := by positivity
  have hcz : r ^ 2 / 4 ≤ ‖z‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) hz1 2
    linarith [show (r / 2) ^ 2 = r ^ 2 / 4 by ring]
  have hcw : r ^ 2 / 4 ≤ ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) hw1 2
    linarith [show (r / 2) ^ 2 = r ^ 2 / 4 by ring]
  have B2 := hph _ hc4 _ _ hcz hcw
  have B3 : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 3 * r * ‖z - w‖ := by
    rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring, abs_mul,
      abs_of_pos (by linarith : 0 < ‖z‖ + ‖w‖)]
    have h1 := abs_norm_sub_norm_le z w
    have h2 : ‖z‖ + ‖w‖ ≤ 3 * r := by linarith
    calc |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) ≤ ‖z - w‖ * (3 * r) := mul_le_mul h1 h2 (by positivity) hD0
      _ = 3 * r * ‖z - w‖ := by ring
  have B4 : |(j : ℝ)| * |F (‖z‖ ^ 2) - F (‖w‖ ^ 2)| ≤ 12 * |(j : ℝ)| * B / r * ‖z - w‖ := by
    have hr' : r ≠ 0 := hr.ne'
    calc |(j : ℝ)| * |F (‖z‖ ^ 2) - F (‖w‖ ^ 2)| ≤ |(j : ℝ)| * (B / (r ^ 2 / 4) * |‖z‖ ^ 2 - ‖w‖ ^ 2|) :=
          mul_le_mul_of_nonneg_left B2 (abs_nonneg _)
      _ ≤ |(j : ℝ)| * (B / (r ^ 2 / 4) * (3 * r * ‖z - w‖)) := by gcongr
      _ = 12 * |(j : ℝ)| * B / r * ‖z - w‖ := by
        field_simp
        ring
  calc _ ≤ (12 * |(j : ℝ)| * B / r * ‖z - w‖) * (4 * Cv * u ^ 2) :=
        mul_le_mul (B1.trans B4) hc (norm_nonneg _) (by positivity)
    _ = 48 * |(j : ℝ)| * B * Cv * (u ^ 2 / r) * ‖z - w‖ := by ring

theorem profileDiff_bound (P : ShapeParams) (hL : 0 < P.chartLength) (Φ : ℝ → ℝ → ℂ) {Ct Cx : ℝ} (hCt : 0 ≤ Ct)
    (hCx : 0 ≤ Cx)
    (ht : ∀ x, |x| ≤ 1 → ∀ t t', 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 →
      ‖Φ t x - Φ t' x‖ ≤ Ct * max (1 - t) (1 - t') * |t - t'|)
    (hx : ∀ t, 0 ≤ t → t ≤ 1 → ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
      ‖Φ t x - Φ t x'‖ ≤ Cx * (1 - t) ^ 2 * |x - x'|) {z w : Space} {u r : ℝ} (hu0 : 0 ≤ u) (hr : 0 < r)
    (huz : 1 - chartCoord P z ≤ 2 * u) (huw : 1 - chartCoord P w ≤ 2 * u) (hw1 : r / 2 ≤ ‖w‖) :
    ‖Φ (chartCoord P z) (heightRatio z) - Φ (chartCoord P w) (heightRatio w)‖ ≤
      8 * Ct * (u ^ 3 / P.chartLength) * ‖z - w‖ + 16 * Cx * (u ^ 2 / r) * ‖z - w‖ := by
  have hD0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  obtain ⟨htz0, htz1⟩ := chart_bounds P hL z
  obtain ⟨htw0, htw1⟩ := chart_bounds P hL w
  have hxz := GivenShape.Internal.abs_heightRatio_le z
  have hxw := GivenShape.Internal.abs_heightRatio_le w
  have C0 := norm_sub_le_norm_sub_add_norm_sub (Φ (chartCoord P z) (heightRatio z))
    (Φ (chartCoord P w) (heightRatio z)) (Φ (chartCoord P w) (heightRatio w))
  have C1 := ht (heightRatio z) hxz (chartCoord P z) (chartCoord P w) htz0 htz1 htw0 htw1
  have C2 := hx (chartCoord P w) htw0 htw1 (heightRatio z) (heightRatio w) hxz hxw
  have hmax : max (1 - chartCoord P z) (1 - chartCoord P w) ≤ 2 * u := max_le huz huw
  have hmax0 : 0 ≤ max (1 - chartCoord P z) (1 - chartCoord P w) := le_max_of_le_left (by linarith)
  have huw2 : (1 - chartCoord P w) ^ 2 ≤ 4 * u ^ 2 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - chartCoord P w) huw 2
    linarith [show (2 * u) ^ 2 = 4 * u ^ 2 by ring]
  have hdt' : |chartCoord P z - chartCoord P w| ≤ 4 * u ^ 2 / P.chartLength * ‖z - w‖ := by
    refine (chart_diff P hL z w).trans ?_
    have h1 : (1 - chartCoord P z) * (1 - chartCoord P w) ≤ (2 * u) * (2 * u) :=
      mul_le_mul huz huw (by linarith) (by positivity)
    calc (1 - chartCoord P z) * (1 - chartCoord P w) / P.chartLength * ‖z - w‖ ≤
          (2 * u) * (2 * u) / P.chartLength * ‖z - w‖ := by gcongr
      _ = 4 * u ^ 2 / P.chartLength * ‖z - w‖ := by ring
  have hdh : |heightRatio z - heightRatio w| ≤ 4 * ‖z - w‖ / r := by
    have h1 := CertCell.Instance.Internal.Slope.height_slope z w
    have h2 := mul_le_mul_of_nonneg_right hw1 (abs_nonneg (heightRatio z - heightRatio w))
    rw [le_div_iff₀ hr]
    linarith
  have C3 : Ct * max (1 - chartCoord P z) (1 - chartCoord P w) * |chartCoord P z - chartCoord P w| ≤
      8 * Ct * (u ^ 3 / P.chartLength) * ‖z - w‖ := by
    calc Ct * max (1 - chartCoord P z) (1 - chartCoord P w) * |chartCoord P z - chartCoord P w| ≤
          Ct * (2 * u) * (4 * u ^ 2 / P.chartLength * ‖z - w‖) := by gcongr
      _ = 8 * Ct * (u ^ 3 / P.chartLength) * ‖z - w‖ := by ring
  have C4 : Cx * (1 - chartCoord P w) ^ 2 * |heightRatio z - heightRatio w| ≤ 16 * Cx * (u ^ 2 / r) * ‖z - w‖ := by
    calc Cx * (1 - chartCoord P w) ^ 2 * |heightRatio z - heightRatio w| ≤
          Cx * (4 * u ^ 2) * (4 * ‖z - w‖ / r) := by gcongr
      _ = 16 * Cx * (u ^ 2 / r) * ‖z - w‖ := by ring
  linarith

theorem phase_product_diff_le {ea θz θw φz φw Φz Φw : ℂ} (hea : ‖ea‖ = 1) (hθw : ‖θw‖ = 1) (hφz : ‖φz‖ = 1)
    (hφw : ‖φw‖ = 1) :
    ‖ea * (θz * φz) * Φz - ea * (θw * φw) * Φw‖ ≤ ‖θz - θw‖ * ‖Φz‖ + ‖φz - φw‖ * ‖Φz‖ + ‖Φz - Φw‖ := by
  have e : ea * (θz * φz) * Φz - ea * (θw * φw) * Φw =
      ea * ((θz - θw) * (φz * Φz) + θw * ((φz - φw) * Φz) + θw * φw * (Φz - Φw)) := by ring
  rw [e, norm_mul, hea, one_mul]
  have n1 : ‖(θz - θw) * (φz * Φz)‖ = ‖θz - θw‖ * ‖Φz‖ := by rw [norm_mul, norm_mul, hφz, one_mul]
  have n2 : ‖θw * ((φz - φw) * Φz)‖ = ‖φz - φw‖ * ‖Φz‖ := by rw [norm_mul, norm_mul, hθw, one_mul]
  have n3 : ‖θw * φw * (Φz - Φw)‖ = ‖Φz - Φw‖ := by rw [norm_mul, norm_mul, hθw, hφw, one_mul, one_mul]
  rw [← n1, ← n2, ← n3]
  exact norm_add₃_le

theorem phasedProfile_slope (P : ShapeParams) (hP : IsShapeParams P) (Φ : ℝ → ℝ → ℂ) (k : ℕ) (M j : ℤ)
    (hMk : M ≠ 0 → 1 ≤ k) (Cv Ct Cx : ℝ) (hCv : 0 ≤ Cv) (hCt : 0 ≤ Ct) (hCx : 0 ≤ Cx)
    (hv : ∀ t x, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖Φ t x‖ ≤ Cv * (1 - t) ^ 2 * (1 - x ^ 2) ^ k)
    (ht : ∀ x, |x| ≤ 1 → ∀ t t', 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 →
      ‖Φ t x - Φ t' x‖ ≤ Ct * max (1 - t) (1 - t') * |t - t'|)
    (hx : ∀ t, 0 ≤ t → t ≤ 1 → ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
      ‖Φ t x - Φ t x'‖ ≤ Cx * (1 - t) ^ 2 * |x - x'|) :
    ∃ K, 0 ≤ K ∧ ∀ (a : ℝ) (y : Space), 0 < ‖planePoint y‖ → ∀ z ∈ Metric.ball y (‖planePoint y‖ / 2),
      ∀ w ∈ Metric.ball y (‖planePoint y‖ / 2),
        ‖phasedProfile P Φ M j a z - phasedProfile P Φ M j a w‖ ≤ K / (‖y‖ * (1 + ‖y‖) ^ 2) * ‖z - w‖ := by
  have hL := hP.chartLength_pos
  obtain ⟨B, hB, hph⟩ := phase_slope hP.phase
  refine ⟨(16 * |(M : ℝ)| * Cv + 48 * |(j : ℝ)| * B * Cv + 16 * Cx) * max P.chartLength 1 ^ 2 +
    8 * Ct * max P.chartLength 1 ^ 3 / P.chartLength, by positivity, ?_⟩
  intro a y hy z hz w hw
  obtain ⟨hz1, hz2, hz3⟩ := half_ball_bounds hz
  obtain ⟨hw1, hw2, hw3⟩ := half_ball_bounds hw
  have hρr := norm_planePoint_le y
  have hr : 0 < ‖y‖ := hy.trans_le hρr
  have hplz : planePoint z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hplw : planePoint w ≠ 0 := norm_pos_iff.1 (by linarith)
  have hD0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have huc := chartGap_le P.chartLength ‖y‖ hL hr.le
  have hu0 : 0 ≤ P.chartLength / (‖y‖ + P.chartLength) := by positivity
  obtain ⟨htz0, htz1⟩ := chart_bounds P hL z
  have huz := one_sub_chart_le_double P hL hr.le hz1
  have huw := one_sub_chart_le_double P hL hr.le hw1
  have hxz := GivenShape.Internal.abs_heightRatio_le z
  have huz2 : (1 - chartCoord P z) ^ 2 ≤ 4 * (P.chartLength / (‖y‖ + P.chartLength)) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - chartCoord P z) huz 2
    linarith [show (2 * (P.chartLength / (‖y‖ + P.chartLength))) ^ 2 =
      4 * (P.chartLength / (‖y‖ + P.chartLength)) ^ 2 by ring]
  have hΦz := hv _ _ htz0 htz1 hxz
  have hΦz4 : ‖Φ (chartCoord P z) (heightRatio z)‖ ≤ 4 * Cv * (P.chartLength / (‖y‖ + P.chartLength)) ^ 2 := by
    refine hΦz.trans ?_
    have h1 := axisPow_le_one k hxz
    have h2 := axisPow_nonneg k hxz
    calc Cv * (1 - chartCoord P z) ^ 2 * (1 - heightRatio z ^ 2) ^ k ≤
          Cv * (4 * (P.chartLength / (‖y‖ + P.chartLength)) ^ 2) * 1 := by gcongr
      _ = _ := by ring
  have TA := angleTerm_bound M k hMk hCv hplz hplw hΦz huz2 hz1 hr
  have TB := radialPhaseTerm_bound j P.radialPhase hB hph hΦz4 hr hz1 hz2 hw1 hw2
  have TC := profileDiff_bound P hL Φ hCt hCx ht hx hu0 hr huz huw hw1
  have fc := decay_rate_combine (A := 16 * |(M : ℝ)| * Cv + 48 * |(j : ℝ)| * B * Cv + 16 * Cx) hu0 hr hL
    (by positivity) hCt huc
  rw [phasedProfile_split, phasedProfile_split]
  refine (phase_product_diff_le (Complex.norm_exp_ofReal_mul_I a) (Complex.norm_exp_ofReal_mul_I _)
    (Complex.norm_exp_ofReal_mul_I _) (Complex.norm_exp_ofReal_mul_I _)).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right fc hD0)
  have e : ((16 * |(M : ℝ)| * Cv + 48 * |(j : ℝ)| * B * Cv + 16 * Cx) *
      ((P.chartLength / (‖y‖ + P.chartLength)) ^ 2 / ‖y‖) +
      8 * Ct * ((P.chartLength / (‖y‖ + P.chartLength)) ^ 3 / P.chartLength)) * ‖z - w‖ =
      16 * |(M : ℝ)| * Cv * ((P.chartLength / (‖y‖ + P.chartLength)) ^ 2 / ‖y‖) * ‖z - w‖ +
      48 * |(j : ℝ)| * B * Cv * ((P.chartLength / (‖y‖ + P.chartLength)) ^ 2 / ‖y‖) * ‖z - w‖ +
      (8 * Ct * ((P.chartLength / (‖y‖ + P.chartLength)) ^ 3 / P.chartLength) * ‖z - w‖ +
        16 * Cx * ((P.chartLength / (‖y‖ + P.chartLength)) ^ 2 / ‖y‖) * ‖z - w‖) := by ring
  rw [e]
  exact add_le_add (add_le_add TA TB) TC

theorem ae_first_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y 0 ≠ 0 := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L] at this
  have h0 := Measure.addHaar_submodule (volume : Measure Space) (LinearMap.ker L) hne
  rw [ae_iff]
  convert h0 using 2
  ext y
  simp [L]

theorem planePoint_pos_of_first {y : Space} (h : y 0 ≠ 0) : 0 < ‖planePoint y‖ := by
  refine norm_pos_iff.2 fun h0 => h ?_
  have := congrArg Complex.re h0
  simpa [planePoint] using this

theorem norm_gradientAt_le (p : Space → ℝ) (x : Space) : ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ p x‖ := by
    intro i
    have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
    rw [norm_smul, hu, mul_one]
    calc ‖fderiv ℝ p x (unitVector i)‖ ≤ ‖fderiv ℝ p x‖ * ‖unitVector i‖ := (fderiv ℝ p x).le_opNorm _
      _ = ‖fderiv ℝ p x‖ := by rw [hu, mul_one]
  calc ∑ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ ≤ ∑ _i : Fin 3, ‖fderiv ℝ p x‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ p x‖ := by simp

theorem scalarValue_eq (P : ShapeParams) (κ : FieldKey) (M : ℤ) (S : PotScalar) (σ : ℝ) (y : Space) :
    scalarValue P κ M false S σ y =
      phasedProfile P (axisProfile S) M κ.phaseIndex (2 * Real.pi * (labelTime κ.label : ℝ) * σ) y := by
  unfold scalarValue phasedProfile axisProfile weightedSpline
  simp only [Bool.false_eq_true, if_false, mul_one]
  push_cast
  ring

theorem pressureKey_bounds (P : ShapeParams) (hP : IsShapeParams P) (F : PotentialSeries) (hF : IsPotentialSeries F)
    (κ : FieldKey) (hκ : κ ∈ F.keys) :
    ∃ V K : ℝ, 0 ≤ V ∧ 0 ≤ K ∧
      (∀ σ y, ‖scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y‖ ≤
        V / (1 + ‖y‖) ^ 2) ∧
      ∀ σ (y : Space), 0 < ‖planePoint y‖ → ∀ z ∈ Metric.ball y (‖planePoint y‖ / 2), ∀ w ∈ Metric.ball y (‖planePoint y‖ / 2),
        ‖scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ z -
          scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ w‖ ≤
          K / (‖y‖ * (1 + ‖y‖) ^ 2) * ‖z - w‖ := by
  have hcl := hF.pressure_class κ hκ
  have hend : EndOrderBound (F.data κ).pressure := hF.pressure_end κ hκ
  obtain ⟨Cv, Ct, Cx, hCv, hCt, hCx, hv, ht, hx⟩ := axisProfile_bounds _ hcl hend
  have hMk : labelAzimuth P.azimuthOrder κ.label ≠ 0 → 1 ≤ (F.data κ).pressure.axisPower := by
    intro hM
    have hne : κ.label.1 ≠ 0 := by
      intro h0
      apply hM
      simp [labelAzimuth, h0]
    exact (hF.pressure_axis κ hκ hne).1
  obtain ⟨K, hK, hlip⟩ := phasedProfile_slope P hP (axisProfile (F.data κ).pressure) (F.data κ).pressure.axisPower
    (labelAzimuth P.azimuthOrder κ.label) κ.phaseIndex hMk Cv Ct Cx hCv hCt hCx hv ht hx
  refine ⟨Cv * max P.chartLength 1 ^ 2, K, by positivity, hK, fun σ y => ?_, fun σ y hy z hz w hw => ?_⟩
  · rw [scalarValue_eq]
    exact phasedProfile_value P hP.chartLength_pos _ _ Cv hCv hv _ _ _ y
  · rw [scalarValue_eq, scalarValue_eq]
    exact hlip _ y hy z hz w hw

end Internal.PressureDecay

open Internal.PressureDecay in
theorem pressureValue_decay_bounds : ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P →
    IsPotentialSeries F → ∃ C : ℝ, (∀ σ y, |pressureValue P F σ y| ≤ C / (1 + ‖y‖) ^ 2) ∧
      ∀ σ, ∀ᵐ y, ‖y‖ * ‖gradientAt (pressureValue P F σ) y‖ ≤ C ∧
        ‖y‖ ^ 3 * ‖gradientAt (pressureValue P F σ) y‖ ≤ C := by
  intro P F hP hF
  have hkey := pressureKey_bounds P hP F hF
  choose! V K hV hK hval hlip using hkey
  set SV := ∑ κ ∈ F.keys, V κ with hSV
  set SK := ∑ κ ∈ F.keys, K κ with hSK
  have hSV0 : 0 ≤ SV := Finset.sum_nonneg fun κ hκ => hV κ hκ
  have hSK0 : 0 ≤ SK := Finset.sum_nonneg fun κ hκ => hK κ hκ
  refine ⟨SV + 3 * SK, fun σ y => ?_, fun σ => ?_⟩
  · have h1 : |pressureValue P F σ y| ≤ SV / (1 + ‖y‖) ^ 2 := by
      unfold pressureValue
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      rw [hSV, Finset.sum_div]
      exact Finset.sum_le_sum fun κ hκ => hval κ hκ σ y
    have h2 : SV / (1 + ‖y‖) ^ 2 ≤ (SV + 3 * SK) / (1 + ‖y‖) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  · filter_upwards [ae_first_ne_zero] with y hy0
    have hy := planePoint_pos_of_first hy0
    have hr : 0 < ‖y‖ := hy.trans_le (norm_planePoint_le y)
    have hD : 0 < ‖y‖ * (1 + ‖y‖) ^ 2 := by positivity
    have hlipq : ∀ z ∈ Metric.ball y (‖planePoint y‖ / 2), ∀ w ∈ Metric.ball y (‖planePoint y‖ / 2),
        dist (pressureValue P F σ z) (pressureValue P F σ w) ≤ SK / (‖y‖ * (1 + ‖y‖) ^ 2) * dist z w := by
      intro z hz w hw
      rw [Real.dist_eq, dist_eq_norm]
      unfold pressureValue
      rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      rw [hSK, Finset.sum_div, Finset.sum_mul]
      exact Finset.sum_le_sum fun κ hκ => hlip κ hκ σ y hy z hz w hw
    have hL : LipschitzOnWith (SK / (‖y‖ * (1 + ‖y‖) ^ 2)).toNNReal (pressureValue P F σ)
        (Metric.ball y (‖planePoint y‖ / 2)) := by
      refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hlipq z hz w hw
    have hfd := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y (by positivity)) hL
    rw [Real.coe_toNNReal _ (by positivity)] at hfd
    have hg : ‖gradientAt (pressureValue P F σ) y‖ ≤ 3 * (SK / (‖y‖ * (1 + ‖y‖) ^ 2)) :=
      (norm_gradientAt_le _ y).trans (by linarith)
    have hg0 : 0 ≤ ‖gradientAt (pressureValue P F σ) y‖ := norm_nonneg _
    have e1 : ‖y‖ * (3 * (SK / (‖y‖ * (1 + ‖y‖) ^ 2))) = 3 * SK / (1 + ‖y‖) ^ 2 := by
      field_simp
    have e2 : ‖y‖ ^ 3 * (3 * (SK / (‖y‖ * (1 + ‖y‖) ^ 2))) = 3 * SK * (‖y‖ / (1 + ‖y‖)) ^ 2 := by
      field_simp
    have h1p : 1 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    have hq : (‖y‖ / (1 + ‖y‖)) ^ 2 ≤ 1 := by
      have : ‖y‖ / (1 + ‖y‖) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      have : 0 ≤ ‖y‖ / (1 + ‖y‖) := by positivity
      nlinarith
    constructor
    · calc ‖y‖ * ‖gradientAt (pressureValue P F σ) y‖ ≤ ‖y‖ * (3 * (SK / (‖y‖ * (1 + ‖y‖) ^ 2))) :=
            mul_le_mul_of_nonneg_left hg hr.le
        _ = 3 * SK / (1 + ‖y‖) ^ 2 := e1
        _ ≤ 3 * SK := div_le_self (by positivity) h1p
        _ ≤ SV + 3 * SK := by linarith
    · calc ‖y‖ ^ 3 * ‖gradientAt (pressureValue P F σ) y‖ ≤ ‖y‖ ^ 3 * (3 * (SK / (‖y‖ * (1 + ‖y‖) ^ 2))) :=
            mul_le_mul_of_nonneg_left hg (by positivity)
        _ = 3 * SK * (‖y‖ / (1 + ‖y‖)) ^ 2 := e2
        _ ≤ 3 * SK * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ SV + 3 * SK := by linarith


end PotentialShape

end Breakdown

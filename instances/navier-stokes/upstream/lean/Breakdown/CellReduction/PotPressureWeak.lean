import Breakdown.CellReduction.PotentialShape
import Breakdown.CellReduction.PotPressureWeakShell
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeJetJoin

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape

namespace PressureWeak

namespace Internal
open CellCert.GivenFields (weightPoly heightRatio qOf angleOf)
open CellCert.GivenFields.PressureOpen (shellSet)
open CellCert.GivenFields.PressureOpen.PressureOpenInternal (ratio_sub height_abs_le qOf_mem pow_sub_le
  planeField_sub expI_sub)

theorem chartCoord_mem (P : ShapeParams) (hP : 0 < P.chartLength) (y : Space) :
    0 ≤ chartCoord P y ∧ chartCoord P y ≤ 1 := by
  unfold chartCoord
  have hd : 0 < ‖y‖ + P.chartLength := add_pos_of_nonneg_of_pos (norm_nonneg _) hP
  exact ⟨div_nonneg (norm_nonneg _) hd.le, (div_le_one hd).2 (by linarith)⟩

theorem chartCoord_sub (P : ShapeParams) (hP : 0 < P.chartLength) {a : ℝ} (ha : 0 < a) {x y : Space}
    (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    |chartCoord P x - chartCoord P y| ≤ 1 / a * ‖x - y‖ := by
  unfold chartCoord
  set L := P.chartLength with hLdef
  have hx' : 0 < ‖x‖ + L := by linarith
  have hy' : 0 < ‖y‖ + L := by linarith
  have e : ‖x‖ / (‖x‖ + L) - ‖y‖ / (‖y‖ + L) = L * (‖x‖ - ‖y‖) / ((‖x‖ + L) * (‖y‖ + L)) := by
    rw [div_sub_div _ _ hx'.ne' hy'.ne']
    congr 1
    ring
  rw [e, abs_div, abs_mul, abs_of_pos hP, abs_of_pos (mul_pos hx' hy')]
  have h1 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h2 : a * L ≤ (‖x‖ + L) * (‖y‖ + L) := mul_le_mul (by linarith) (by linarith) hP.le (by linarith)
  rw [div_le_iff₀ (mul_pos hx' hy')]
  have hd : 0 ≤ 1 / a * ‖x - y‖ := mul_nonneg (div_nonneg zero_le_one ha.le) (norm_nonneg _)
  calc L * |‖x‖ - ‖y‖| ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_left h1 hP.le
    _ = 1 / a * ‖x - y‖ * (a * L) := by
        rw [show 1 / a * ‖x - y‖ * (a * L) = L * ‖x - y‖ * (a / a) by ring, div_self ha.ne', mul_one]
    _ ≤ 1 / a * ‖x - y‖ * ((‖x‖ + L) * (‖y‖ + L)) := mul_le_mul_of_nonneg_left h2 hd

theorem qOf_sub {a : ℝ} (ha : 0 < a) {x y : Space} (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    |qOf x - qOf y| ≤ 4 / a * ‖x - y‖ := by
  unfold qOf
  have h3 := ratio_sub ha hx hy
  have hxa := height_abs_le x
  have hya := height_abs_le y
  rw [show 1 - heightRatio x ^ 2 - (1 - heightRatio y ^ 2) =
    (heightRatio y + heightRatio x) * (heightRatio y - heightRatio x) by ring, abs_mul]
  have h3' : |heightRatio y - heightRatio x| ≤ 2 / a * ‖x - y‖ := by rw [abs_sub_comm]; exact h3
  have hs : |heightRatio y + heightRatio x| ≤ 2 := by
    have := abs_add_le (heightRatio y) (heightRatio x)
    linarith
  calc |heightRatio y + heightRatio x| * |heightRatio y - heightRatio x| ≤ 2 * (2 / a * ‖x - y‖) :=
        mul_le_mul hs h3' (abs_nonneg _) (by norm_num)
    _ = 4 / a * ‖x - y‖ := by ring

theorem pointAngle_eq (y : Space) : pointAngle y = angleOf y := by
  unfold pointAngle angleOf
  congr 1
  apply Complex.ext <;> simp

def radialPart (P : ShapeParams) (n j : ℤ) (σ : ℝ) (y : Space) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * σ + (j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)

def angularPart (M : ℤ) (k : ℕ) (y : Space) : ℂ :=
  Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) * (((1 - heightRatio y ^ 2) ^ k : ℝ) : ℂ)

theorem radialPart_norm (P : ShapeParams) (n j : ℤ) (σ : ℝ) (y : Space) : ‖radialPart P n j σ y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem angularPart_norm (M : ℤ) (k : ℕ) (y : Space) : ‖angularPart M k y‖ ≤ 1 := by
  unfold angularPart
  obtain ⟨q0, q1⟩ := qOf_mem y
  have q0' : 0 ≤ 1 - heightRatio y ^ 2 := q0
  have q1' : 1 - heightRatio y ^ 2 ≤ 1 := q1
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg q0' _)]
  exact pow_le_one₀ q0' q1'

theorem phase_sub {F : ℝ → ℝ} (hF : IsRadialPhase F) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ, 0 < a → ∀ x y : Space,
    a ≤ ‖x‖ → a ≤ ‖y‖ → |F (‖x‖ ^ 2) - F (‖y‖ ^ 2)| ≤ 2 * B / a * ‖x - y‖ := by
  obtain ⟨δ, hδ, hs⟩ := hF.smooth
  obtain ⟨B, hB⟩ := hF.scaled_bounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl).1
  refine ⟨B, hB0, fun a ha x y hx hy => ?_⟩
  have hd : ∀ u : ℝ, 0 ≤ u → HasDerivAt (fun v : ℝ => F (v ^ 2)) (deriv F (u ^ 2) * (2 * u)) u := by
    intro u hu
    have hmem : u ^ 2 ∈ Set.Ioi (-δ) := by
      simp only [Set.mem_Ioi]
      nlinarith [sq_nonneg u]
    have hdiff : DifferentiableAt ℝ F (u ^ 2) :=
      (hs.differentiableOn (by norm_num) _ hmem).differentiableAt (Ioi_mem_nhds hmem)
    have h2 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
    exact HasDerivAt.comp (h := fun v : ℝ => v ^ 2) u hdiff.hasDerivAt h2
  have hbound : ∀ u ∈ Set.Ici a, ‖deriv F (u ^ 2) * (2 * u)‖ ≤ 2 * B / a := by
    intro u hu
    have hau : a ≤ u := hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hau
    have h1 := (hB (u ^ 2) (sq_nonneg u)).1
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * u), le_div_iff₀ ha]
    have h3 : |deriv F (u ^ 2)| * (2 * u) * a ≤ |deriv F (u ^ 2)| * (2 * u) * u :=
      mul_le_mul_of_nonneg_left hau (mul_nonneg (abs_nonneg _) (by linarith))
    nlinarith
  have hmvt := (convex_Ici a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hd u (ha.le.trans hu)).hasDerivWithinAt) hbound (show ‖y‖ ∈ Set.Ici a from hy)
    (show ‖x‖ ∈ Set.Ici a from hx)
  beta_reduce at hmvt
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt.trans (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (div_nonneg (by linarith) ha.le))

theorem radialPart_shell (P : ShapeParams) (hP : IsShapeParams P) (n j : ℤ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ShellSlope (radialPart P n j σ) C := by
  obtain ⟨B, hB0, hB⟩ := phase_sub hP.phase
  refine ⟨2 * |(j : ℝ)| * B, mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hB0,
    fun a b ha hab x hx y hy => ?_⟩
  rw [mem_shell_iff] at hx hy
  unfold radialPart
  rw [mul_comm _ Complex.I, mul_comm _ Complex.I]
  refine (expI_sub _ _).trans ?_
  have e : 2 * Real.pi * (n : ℝ) * σ + (j : ℝ) * P.radialPhase (‖x‖ ^ 2) -
      (2 * Real.pi * (n : ℝ) * σ + (j : ℝ) * P.radialPhase (‖y‖ ^ 2)) =
      (j : ℝ) * (P.radialPhase (‖x‖ ^ 2) - P.radialPhase (‖y‖ ^ 2)) := by ring
  rw [e, abs_mul]
  have h := hB a ha x y hx.1 hy.1
  have hw := inv_le_shellWeight ha hab
  have hd := norm_nonneg (x - y)
  have hjB : 0 ≤ 2 * |(j : ℝ)| * B := mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hB0
  calc |(j : ℝ)| * |P.radialPhase (‖x‖ ^ 2) - P.radialPhase (‖y‖ ^ 2)| ≤ |(j : ℝ)| * (2 * B / a * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 2 * |(j : ℝ)| * B * (1 / a * ‖x - y‖) := by ring
    _ ≤ 2 * |(j : ℝ)| * B * ((1 + b / a) ^ 2 / a * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hd) hjB
    _ = 2 * |(j : ℝ)| * B * ((1 + b / a) ^ 2 / a) * ‖x - y‖ := by ring

theorem angularPart_shell (M : ℤ) (k : ℕ) (hk : M ≠ 0 → 1 ≤ k) :
    ShellSlope (angularPart M k) (2 * M.natAbs + 4 + 4 * k) := by
  intro a b ha hab x hx y hy
  rw [mem_shell_iff] at hx hy
  have hw1 := inv_le_shellWeight ha hab
  have hw2 := ratio_le_shellWeight ha hab
  have hd := norm_nonneg (x - y)
  have hw0 := shellWeight_nonneg ha b
  obtain ⟨qx0, qx1⟩ := qOf_mem x
  obtain ⟨qy0, qy1⟩ := qOf_mem y
  have hq := qOf_sub ha hx.1 hy.1
  have hqn : ∀ n : ℕ, |qOf x ^ n - qOf y ^ n| ≤ n * (4 / a * ‖x - y‖) := fun n =>
    (pow_sub_le n (by rw [abs_of_nonneg qx0]; exact qx1) (by rw [abs_of_nonneg qy0]; exact qy1)).trans
      (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg n))
  have h4 : 4 / a * ‖x - y‖ ≤ 4 * ((1 + b / a) ^ 2 / a * ‖x - y‖) := by
    rw [show 4 / a * ‖x - y‖ = 4 * (1 / a * ‖x - y‖) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw1 hd) (by norm_num)
  have hwd : 0 ≤ (1 + b / a) ^ 2 / a * ‖x - y‖ := mul_nonneg hw0 hd
  have hMn : (0 : ℝ) ≤ M.natAbs := Nat.cast_nonneg _
  by_cases hM : M = 0
  · subst hM
    have e : ∀ z, angularPart 0 k z = ((qOf z ^ k : ℝ) : ℂ) := by
      intro z
      unfold angularPart qOf
      simp
    rw [e, e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (hqn k).trans ?_
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h5 : (k : ℝ) * (4 / a * ‖x - y‖) ≤ (k : ℝ) * (4 * ((1 + b / a) ^ 2 / a * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left h4 hk0
    nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk hM; omega⟩
    have e : ∀ z, angularPart M (j + 1) z =
        (Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) * ((qOf z : ℝ) : ℂ)) * ((qOf z ^ j : ℝ) : ℂ) := by
      intro z
      unfold angularPart qOf
      have h1 : ((((M : ℝ) * pointAngle z : ℝ) : ℂ) * Complex.I) = Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ) := by
        rw [pointAngle_eq, mul_comm]
      rw [h1, pow_succ']
      push_cast
      ring
    rw [e, e]
    have hG := planeField_sub M ha hx hy
    have hGx : ‖Complex.exp (Complex.I * (((M : ℝ) * angleOf x : ℝ) : ℂ)) * ((qOf x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg qx0]
      exact qx1
    have hQy : ‖((qOf y ^ j : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg qy0 _)]
      exact pow_le_one₀ qy0 qy1
    have hQd : ‖((qOf x ^ j : ℝ) : ℂ) - ((qOf y ^ j : ℝ) : ℂ)‖ ≤ j * (4 / a * ‖x - y‖) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hqn j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h5 : (j : ℝ) * (4 / a * ‖x - y‖) ≤ (j : ℝ) * (4 * ((1 + b / a) ^ 2 / a * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left h4 hj0
    have h6 : (2 * M.natAbs + 4) * (b / a ^ 2) * ‖x - y‖ ≤ (2 * M.natAbs + 4) * ((1 + b / a) ^ 2 / a * ‖x - y‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw2 hd) (by positivity)
    refine (CellCert.GivenFields.PressureOpen.PressureOpenInternal.mul_sub_le _ _ _ _).trans ?_
    have h7 := mul_le_mul hGx hQd (norm_nonneg _) zero_le_one
    have h8 := mul_le_mul hQy hG (norm_nonneg _) zero_le_one
    have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hc]
    linarith

theorem weightPoly_norm (e0 e1 : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ‖weightPoly e0 e1 t‖ ≤ 1 := by
  unfold weightPoly
  have h2 : 0 ≤ 1 - t := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _))]
  exact mul_le_one₀ (pow_le_one₀ h0 h1) (pow_nonneg h2 _) (pow_le_one₀ h2 (by linarith))

theorem weightPoly_sub (e0 e1 : ℕ) {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖weightPoly e0 e1 t - weightPoly e0 e1 s‖ ≤ (e0 + e1) * |t - s| := by
  unfold weightPoly
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have A := pow_sub_le e0 (abs_le.2 ⟨by linarith, ht1⟩) (abs_le.2 ⟨by linarith, hs1⟩)
  have Bq := pow_sub_le e1 (u := 1 - t) (v := 1 - s) (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩)
  rw [show 1 - t - (1 - s) = -(t - s) by ring, abs_neg] at Bq
  have e : t ^ e0 * (1 - t) ^ e1 - s ^ e0 * (1 - s) ^ e1 =
      t ^ e0 * ((1 - t) ^ e1 - (1 - s) ^ e1) + (1 - s) ^ e1 * (t ^ e0 - s ^ e0) := by ring
  rw [e]
  have ht : |t ^ e0| ≤ 1 := by rw [abs_of_nonneg (pow_nonneg ht0 _)]; exact pow_le_one₀ ht0 ht1
  have hs : |(1 - s) ^ e1| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (by linarith) _)]; exact pow_le_one₀ (by linarith) (by linarith)
  calc |t ^ e0 * ((1 - t) ^ e1 - (1 - s) ^ e1) + (1 - s) ^ e1 * (t ^ e0 - s ^ e0)|
      ≤ |t ^ e0| * |(1 - t) ^ e1 - (1 - s) ^ e1| + |(1 - s) ^ e1| * |t ^ e0 - s ^ e0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * (e1 * |t - s|) + 1 * (e0 * |t - s|) :=
        add_le_add (mul_le_mul ht Bq (abs_nonneg _) zero_le_one) (mul_le_mul hs A (abs_nonneg _) zero_le_one)
    _ = (e0 + e1) * |t - s| := by ring

theorem weight_shell (P : ShapeParams) (hP : 0 < P.chartLength) (e0 e1 : ℕ) :
    ShellSlope (fun y => weightPoly e0 e1 (chartCoord P y)) (e0 + e1) := by
  intro a b ha hab x hx y hy
  rw [mem_shell_iff] at hx hy
  obtain ⟨tx0, tx1⟩ := chartCoord_mem P hP x
  obtain ⟨ty0, ty1⟩ := chartCoord_mem P hP y
  have h1 := weightPoly_sub e0 e1 tx0 tx1 ty0 ty1
  have h2 := chartCoord_sub P hP ha hx.1 hy.1
  have hw1 := inv_le_shellWeight ha hab
  have hd := norm_nonneg (x - y)
  have he : (0 : ℝ) ≤ e0 + e1 := by positivity
  calc ‖weightPoly e0 e1 (chartCoord P x) - weightPoly e0 e1 (chartCoord P y)‖
      ≤ (e0 + e1) * |chartCoord P x - chartCoord P y| := h1
    _ ≤ (e0 + e1) * (1 / a * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 he
    _ ≤ (e0 + e1) * ((1 + b / a) ^ 2 / a * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw1 hd) he
    _ = (e0 + e1) * ((1 + b / a) ^ 2 / a) * ‖x - y‖ := by ring

theorem spline_shell (P : ShapeParams) (hP : 0 < P.chartLength) (H : JetSpline) (hH : IsJetClass 0 0 H) :
    ∃ C B : ℝ, 0 ≤ C ∧ ShellSlope (fun y => H.toSpline.evalHalf (chartCoord P y) (heightRatio y)) C ∧
      ∀ y, ‖H.toSpline.evalHalf (chartCoord P y) (heightRatio y)‖ ≤ B := by
  have hJ := jetSplineJoined H hH.t_axis hH.x_axis
  have hc : Continuous fun z : ℝ × ℝ => CertCell.GivenShape.Internal.pieceEval H.toSpline.mesh.tBreaks H.toSpline.mesh.xBreaks
      H.toSpline.piece z.1 z.2 := (joinedSplineSmooth _ _ _ hJ).continuous
  obtain ⟨M, hM0, hM⟩ := CertCell.GivenShape.Internal.pieceEval_box _ _ _ hc 1
  obtain ⟨B, hB0, hB⟩ := CertCell.GivenShape.Internal.pieceEval_bounded H.toSpline.mesh.tBreaks H.toSpline.mesh.xBreaks
    H.toSpline.piece 1
  have ht : ∀ y : Space, |chartCoord P y| ≤ 1 := fun y => by
    obtain ⟨h0, h1⟩ := chartCoord_mem P hP y
    rw [abs_of_nonneg h0]; exact h1
  refine ⟨3 * M, B, by positivity, fun a b ha hab x hx y hy => ?_, fun y => hB _ _ (ht y) (height_abs_le y)⟩
  rw [mem_shell_iff] at hx hy
  have h1 := hM (chartCoord P x, heightRatio x) (chartCoord P y, heightRatio y) (ht x) (height_abs_le x)
    (ht y) (height_abs_le y)
  have h2 := chartCoord_sub P hP ha hx.1 hy.1
  have h3 := ratio_sub ha hx.1 hy.1
  have hw1 := inv_le_shellWeight ha hab
  have hd := norm_nonneg (x - y)
  show ‖CertCell.GivenShape.Internal.pieceEval _ _ _ (chartCoord P x) (heightRatio x) -
    CertCell.GivenShape.Internal.pieceEval _ _ _ (chartCoord P y) (heightRatio y)‖ ≤ _
  calc _ ≤ M * (|chartCoord P x - chartCoord P y| + |heightRatio x - heightRatio y|) := h1
    _ ≤ M * (1 / a * ‖x - y‖ + 2 / a * ‖x - y‖) := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hM0
    _ = 3 * M * (1 / a * ‖x - y‖) := by ring
    _ ≤ 3 * M * ((1 + b / a) ^ 2 / a * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw1 hd) (by positivity)
    _ = 3 * M * ((1 + b / a) ^ 2 / a) * ‖x - y‖ := by ring

theorem norm_mul_bound {f g : Space → ℂ} {Bf Bg : ℝ} (hf : ∀ z, ‖f z‖ ≤ Bf) (hg : ∀ z, ‖g z‖ ≤ Bg) :
    ∀ z, ‖f z * g z‖ ≤ Bf * Bg := fun z => by
  rw [norm_mul]
  exact mul_le_mul (hf z) (hg z) (norm_nonneg _) ((norm_nonneg _).trans (hf 0))

theorem scalarValue_eq (P : ShapeParams) (κ : FieldKey) (M : ℤ) (S : PotScalar) (σ : ℝ) (y : Space) :
    scalarValue P κ M false S σ y = radialPart P (labelTime κ.label) κ.phaseIndex σ y * angularPart M S.axisPower y *
      weightPoly S.lowOrder S.highOrder (chartCoord P y) * S.amp.toSpline.evalHalf (chartCoord P y) (heightRatio y) := by
  have key : ∀ A B C : ℝ, Complex.exp (((A + B + C : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((A + C : ℝ) : ℂ) * Complex.I) * Complex.exp (((B : ℝ) : ℂ) * Complex.I) := by
    intro A B C
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold scalarValue radialPart angularPart
  rw [key]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  ring

theorem radialPart_time (P : ShapeParams) (n j : ℤ) (σ : ℝ) (y : Space) :
    radialPart P n j σ y = Complex.exp (((2 * Real.pi * (n : ℝ) * σ : ℝ) : ℂ) * Complex.I) * radialPart P n j 0 y := by
  unfold radialPart
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem scalar_shell (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (S : PotScalar)
    (hcl : IsJetClass 0 0 S.amp) (hax : M ≠ 0 → 1 ≤ S.axisPower) (σ : ℝ) :
    ∃ C B : ℝ, ShellSlope (scalarValue P κ M false S σ) C ∧ ∀ y, ‖scalarValue P κ M false S σ y‖ ≤ B := by
  have hL := hP.chartLength_pos
  obtain ⟨C1, -, h1⟩ := radialPart_shell P hP (labelTime κ.label) κ.phaseIndex σ
  have h2 := angularPart_shell M S.axisPower hax
  have h3 := weight_shell P hL S.lowOrder S.highOrder
  obtain ⟨C4, B4, -, h4, hb4⟩ := spline_shell P hL S.amp hcl
  have b1 : ∀ y, ‖radialPart P (labelTime κ.label) κ.phaseIndex σ y‖ ≤ 1 := fun y =>
    (radialPart_norm _ _ _ _ _).le
  have b2 : ∀ y, ‖angularPart M S.axisPower y‖ ≤ 1 := angularPart_norm M S.axisPower
  have b3 : ∀ y, ‖weightPoly S.lowOrder S.highOrder (chartCoord P y)‖ ≤ 1 := fun y =>
    weightPoly_norm _ _ (chartCoord_mem P hL y).1 (chartCoord_mem P hL y).2
  have b12 := norm_mul_bound b1 b2
  have b123 := norm_mul_bound b12 b3
  have b1234 := norm_mul_bound b123 hb4
  have h1234 := ((h1.mul h2 b1 b2).mul h3 b12 b3).mul h4 b123 hb4
  have hfun : scalarValue P κ M false S σ = fun y => radialPart P (labelTime κ.label) κ.phaseIndex σ y *
      angularPart M S.axisPower y * weightPoly S.lowOrder S.highOrder (chartCoord P y) *
        S.amp.toSpline.evalHalf (chartCoord P y) (heightRatio y) := funext (scalarValue_eq P κ M S σ)
  rw [hfun]
  exact ⟨_, _, h1234, b1234⟩

theorem pressure_shell (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P) (hF : IsPotentialSeries F)
    (σ : ℝ) : ∃ C B : ℝ,
      ShellSlope (fun y => ∑ κ ∈ F.keys,
        scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y) C ∧
      ∀ y, ‖∑ κ ∈ F.keys, scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y‖ ≤ B := by
  have hk : ∀ κ ∈ F.keys, ∃ C B : ℝ,
      ShellSlope (scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ) C ∧
      ∀ y, ‖scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y‖ ≤ B := by
    intro κ hκ
    refine scalar_shell P hP κ _ _ (hF.pressure_class κ hκ) (fun hM => (hF.pressure_axis κ hκ fun h0 => hM ?_).1) σ
    simp [labelAzimuth, h0]
  choose! C B hC hB using hk
  refine ⟨∑ κ ∈ F.keys, C κ, ∑ κ ∈ F.keys, B κ,
    ShellSlope.sum F.keys (f := fun κ => scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false
      (F.data κ).pressure σ) (fun κ hκ => hC κ hκ), fun y => ?_⟩
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => hB κ hκ y)

theorem pressureValue_time (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) (y : Space) :
    pressureValue P F σ y = (∑ κ ∈ F.keys, Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) *
      Complex.I) * scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure 0 y).re := by
  unfold pressureValue
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [scalarValue_eq, scalarValue_eq, radialPart_time]
  ring

theorem pressure_jointly_measurable (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) :
    AEStronglyMeasurable (fun z : ℝ × Space => pressureValue P F z.1 z.2) volume := by
  have hk : ∀ κ ∈ F.keys,
      ContinuousOn (scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure 0) {0}ᶜ := by
    intro κ hκ
    obtain ⟨C, B, hC, -⟩ := scalar_shell P hP κ (labelAzimuth P.azimuthOrder κ.label) (F.data κ).pressure
      (hF.pressure_class κ hκ)
      (fun hM => (hF.pressure_axis κ hκ fun h0 => hM (by simp [labelAzimuth, h0])).1) 0
    exact hC.continuousOn
  have hfun : (fun z : ℝ × Space => pressureValue P F z.1 z.2) = fun z => (∑ κ ∈ F.keys,
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 : ℝ) : ℂ) * Complex.I) *
        scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure 0 z.2).re :=
    funext fun z => pressureValue_time P F z.1 z.2
  have hcont : ContinuousOn (fun z : ℝ × Space => pressureValue P F z.1 z.2) (Set.univ ×ˢ ({0}ᶜ : Set Space)) := by
    rw [hfun]
    refine Complex.continuous_re.comp_continuousOn (continuousOn_finsetSum _ fun κ hκ => ?_)
    refine ContinuousOn.mul ?_ ?_
    · exact Continuous.continuousOn (by fun_prop)
    · exact (hk κ hκ).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hnull : (volume : Measure (ℝ × Space)) (Set.univ ×ˢ ({0} : Set Space)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
  have hae : ∀ᵐ z ∂(volume : Measure (ℝ × Space)), z ∈ Set.univ ×ˢ ({0}ᶜ : Set Space) := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    have hz' : ¬ (z ∈ Set.univ ×ˢ ({0}ᶜ : Set Space)) := hz
    exact ⟨trivial, by_contra fun h => hz' ⟨trivial, h⟩⟩
  have h := hcont.aestronglyMeasurable (μ := (volume : Measure (ℝ × Space)))
    (MeasurableSet.univ.prod (measurableSet_singleton (0 : Space)).compl)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

end Internal

end PressureWeak

open PressureWeak.Internal in
theorem pressureValue_measurable_weak (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) :
    AEStronglyMeasurable (fun z : ℝ × Space => pressureValue P F z.1 z.2) volume ∧
      ∀ σ, AdjointDefect.IsWeakScalarGradient (pressureValue P F σ) (gradientAt (pressureValue P F σ)) := by
  refine ⟨pressure_jointly_measurable P F hP hF, fun σ => ?_⟩
  obtain ⟨C, B, hC, hB⟩ := pressure_shell P F hP hF σ
  exact weakScalarGradient_of_shellSlope
    (f := fun y => ∑ κ ∈ F.keys, scalarValue P κ (labelAzimuth P.azimuthOrder κ.label) false (F.data κ).pressure σ y)
    (fun z => rfl) (hC.mono (le_max_left C 0)) (le_max_right C 0) hB

end PotentialShape

end Breakdown

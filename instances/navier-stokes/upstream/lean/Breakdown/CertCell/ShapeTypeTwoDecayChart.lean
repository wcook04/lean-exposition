import Breakdown.CertCell.ShapeTypeTwoDecayRadial

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

open CellCert.GivenFields (heightRatio radialVec polarVecQ azimVecQ qOf)

theorem FarBound.pair {f g : Space → ℝ} (hf : FarBound f 0) (hg : FarBound g 0) :
    FarBound (fun z => (f z, g z)) 0 := by
  obtain ⟨M1, R1, hStrain, hR1, h1⟩ := hf
  obtain ⟨M2, R2, hM2, hR2, h2⟩ := hg
  refine ⟨M1 + M2, max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  refine ((h1 y (le_of_max_le_left hy)).pair (h2 y (le_of_max_le_right hy))).mono ?_ ?_ ?_ <;> rw [add_div]

theorem FarBound.mul {f g : Space → ℂ} {a b : ℕ} (hf : FarBound f a) (hg : FarBound g b) :
    FarBound (fun z => f z * g z) (a + b) := by
  have h := FarBound.bilin (ContinuousLinearMap.mul ℝ ℂ) (fun u v => (norm_mul u v).le) hf hg
  simpa only [ContinuousLinearMap.mul_apply'] using h

theorem FarBound.smul {f : Space → ℂ} {g : Space → Fin 3 → ℂ} {a b : ℕ} (hf : FarBound f a)
    (hg : FarBound g b) : FarBound (fun z => f z • g z) (a + b) := by
  have h := FarBound.bilin (ContinuousLinearMap.lsmul ℝ ℂ) (fun u v => (norm_smul u v).le) hf hg
  simpa only [ContinuousLinearMap.lsmul_apply] using h

theorem div_add_pow_le {c s L : ℝ} (hc : 0 ≤ c) (hs : 1 ≤ s) (hL : 0 ≤ L) {k m : ℕ} (hkm : m ≤ k) :
    c / (s + L) ^ k ≤ c / s ^ m :=
  div_le_div_of_nonneg_left hc (by positivity)
    ((pow_le_pow_right₀ hs hkm).trans (pow_le_pow_left₀ (by linarith) (by linarith) k))

theorem one_sub_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    1 - chartCoord P y = P.chartLength / (‖y‖ + P.chartLength) := by
  have : 0 < ‖y‖ + P.chartLength := by positivity
  rw [chartCoord]
  field_simp
  ring

theorem farBound_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) :
    FarBound (fun y => chartCoord P y) 0 := by
  set L := P.chartLength with hLdef
  have hpos : ∀ s : ℝ, 1 ≤ s → 0 < s + L := fun s hs => by linarith
  have h := farBound_radial (ρ := fun s : ℝ => s / (s + L)) (ρ1 := fun s => L / (s + L) ^ 2)
    (ρ2 := fun s => -(2 * L) / (s + L) ^ 3) (a := 0) (R0 := 1) (C := 1 + 2 * L) le_rfl (by positivity)
    (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
  · exact h
  · have hd := (hasDerivAt_id s).div ((hasDerivAt_id s).add_const L) (hpos s hs).ne'
    refine hd.congr_deriv ?_
    have := (hpos s hs).ne'
    simp only [id]
    field_simp
    try ring
  · have hd := (hasDerivAt_const s L).div (((hasDerivAt_id s).add_const L).pow 2) (pow_ne_zero 2 (hpos s hs).ne')
    refine hd.congr_deriv ?_
    have := (hpos s hs).ne'
    field_simp
    simp
    ring
  · have hs0 : 0 < s := by linarith
    have hsL := hpos s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_zero, div_one, div_le_iff₀ hsL]
      nlinarith
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine (div_add_pow_le hL.le hs hL.le (show 0 + 1 ≤ 2 by norm_num)).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * L),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s + L) ^ 3)]
      refine (div_add_pow_le (by positivity) hs hL.le (show 0 + 2 ≤ 3 by norm_num)).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem farBound_weight (P : ShapeParams) (hL : 0 < P.chartLength) :
    FarBound (fun y => ((1 - chartCoord P y : ℝ) : ℂ)) 1 := by
  set L := P.chartLength with hLdef
  have hpos : ∀ s : ℝ, 1 ≤ s → 0 < s + L := fun s hs => by linarith
  have h := farBound_radial (ρ := fun s : ℝ => ((L / (s + L) : ℝ) : ℂ))
    (ρ1 := fun s => ((-L / (s + L) ^ 2 : ℝ) : ℂ)) (ρ2 := fun s => ((2 * L / (s + L) ^ 3 : ℝ) : ℂ))
    (a := 1) (R0 := 1) (C := 2 * L) le_rfl (by positivity) (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
  · refine h.congr (R0 := 0) fun y _ => ?_
    rw [one_sub_chartCoord P hL y]
  · refine HasDerivAt.ofReal_comp ?_
    have hd := (hasDerivAt_const s L).div ((hasDerivAt_id s).add_const L) (hpos s hs).ne'
    refine hd.congr_deriv ?_
    have := (hpos s hs).ne'
    simp only [id]
    field_simp
    try ring
  · refine HasDerivAt.ofReal_comp ?_
    have hd := (hasDerivAt_const s (-L)).div (((hasDerivAt_id s).add_const L).pow 2)
      (pow_ne_zero 2 (hpos s hs).ne')
    refine hd.congr_deriv ?_
    have := (hpos s hs).ne'
    field_simp
    simp
    ring
  · have hsL := hpos s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine (div_add_pow_le hL.le hs hL.le (k := 1) (m := 1) le_rfl |>.trans_eq' (by simp)).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hL.le,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s + L) ^ 2)]
      refine (div_add_pow_le hL.le hs hL.le (show 1 + 1 ≤ 2 by norm_num)).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_add_pow_le (by positivity) hs hL.le (show 1 + 2 ≤ 3 by norm_num)

theorem heightRatio_smul (s : ℝ) (hs : 0 < s) (y : Space) : heightRatio (s • y) = heightRatio y := by
  simp only [heightRatio, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact mul_div_mul_left _ _ hs.ne'

theorem coord_div_smul (s : ℝ) (hs : 0 < s) (y : Space) (i : Fin 3) : (s • y) i / ‖s • y‖ = y i / ‖y‖ := by
  simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact mul_div_mul_left _ _ hs.ne'

theorem coord_div_contDiffAt (i : Fin 3) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 2 (fun z : Space => z i / ‖z‖) y :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt).div (contDiffAt_norm ℝ hy) (norm_ne_zero_iff.2 hy)

theorem heightRatio_contDiffAt {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 heightRatio y :=
  coord_div_contDiffAt 2 hy

theorem abs_heightRatio_le (y : Space) : |heightRatio y| ≤ 1 := by
  rw [heightRatio, abs_div, abs_norm]
  exact div_le_one_of_le₀ (by simpa using PiLp.norm_apply_le y 2) (norm_nonneg _)

theorem farBound_heightRatio : FarBound (fun y => heightRatio y) 0 :=
  farBound_homog heightRatio_smul fun _ hy => heightRatio_contDiffAt hy

theorem farBound_chart (P : ShapeParams) (hL : 0 < P.chartLength) {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hg2 : ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ g) (Metric.closedBall 0 1)) :
    FarBound (fun y => g (chartCoord P y, heightRatio y)) 0 := by
  refine FarBound.comp_unitBall ((farBound_chartCoord P hL).pair farBound_heightRatio) (fun z => ?_) hg hg2
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ (abs_heightRatio_le z)
  have : 0 < ‖z‖ + P.chartLength := by positivity
  rw [chartCoord, abs_of_nonneg (by positivity), div_le_one this]
  linarith

theorem farBound_chart_smooth (P : ShapeParams) (hL : 0 < P.chartLength) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) : FarBound (fun y => g (chartCoord P y, heightRatio y)) 0 :=
  farBound_chart P hL (unitBall_of_contDiff_two hg).1 (unitBall_of_contDiff_two hg).2

theorem farBound_radialFrame : FarBound (fun y (i : Fin 3) => ((radialVec y i : ℝ) : ℂ)) 0 := by
  refine farBound_homog (fun s hs y => ?_) fun y hy => ?_
  · funext i
    simp only [radialVec]
    rw [coord_div_smul s hs y i]
  · refine contDiffAt_pi.2 fun i => ?_
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp y (coord_div_contDiffAt i hy)

theorem polarVecQ_smul (s : ℝ) (hs : 0 < s) (y : Space) : polarVecQ (s • y) = polarVecQ y := by
  funext i
  have h2 := heightRatio_smul s hs y
  have hq : qOf (s • y) = qOf y := by simp only [qOf, h2]
  have e : ∀ k : Fin 3, heightRatio (s • y) * (s • y) k / ‖s • y‖ = heightRatio y * y k / ‖y‖ := by
    intro k
    rw [mul_div_assoc, mul_div_assoc, coord_div_smul s hs y k, h2]
  fin_cases i
  · exact e 0
  · exact e 1
  · simp only [polarVecQ, hq]
    rfl

theorem farBound_polarFrame : FarBound (fun y (i : Fin 3) => ((polarVecQ y i : ℝ) : ℂ)) 0 := by
  refine farBound_homog (fun s hs y => by rw [polarVecQ_smul s hs y]) fun y hy => ?_
  refine contDiffAt_pi.2 fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp y ?_
  have hx := heightRatio_contDiffAt hy
  have e : ∀ k : Fin 3, ContDiffAt ℝ 2 (fun z : Space => heightRatio z * z k / ‖z‖) y := fun k => by
    have := hx.mul (coord_div_contDiffAt k hy)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  fin_cases i
  · exact e 0
  · exact e 1
  · show ContDiffAt ℝ 2 (fun z : Space => -(1 - heightRatio z ^ 2)) y
    exact (contDiffAt_const.sub (hx.pow 2)).neg

theorem azimVecQ_smul (s : ℝ) (hs : 0 < s) (y : Space) : azimVecQ (s • y) = azimVecQ y := by
  funext i
  fin_cases i
  · show -((s • y) 1) / ‖s • y‖ = -(y 1) / ‖y‖
    rw [neg_div, neg_div, coord_div_smul s hs y 1]
  · exact coord_div_smul s hs y 0
  · rfl

theorem farBound_azimFrame : FarBound (fun y (i : Fin 3) => ((azimVecQ y i : ℝ) : ℂ)) 0 := by
  refine farBound_homog (fun s hs y => by rw [azimVecQ_smul s hs y]) fun y hy => ?_
  refine contDiffAt_pi.2 fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp y ?_
  fin_cases i
  · show ContDiffAt ℝ 2 (fun z : Space => -(z 1) / ‖z‖) y
    refine (coord_div_contDiffAt 1 hy).neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  · exact coord_div_contDiffAt 0 hy
  · exact contDiffAt_const

end Internal

end GivenShape

end CertCell

end Breakdown

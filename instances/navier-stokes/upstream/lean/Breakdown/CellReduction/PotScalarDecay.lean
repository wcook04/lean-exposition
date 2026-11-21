import Breakdown.CellReduction.PotScalarDecayFactor

open scoped ContDiff Topology
open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (heightRatio cellCount cellIndex weightPoly Spline)
open CertCell.GivenShape.Internal.KeyDecay

namespace Internal.ScalarDecay

theorem annulus_mem_nhds {y : Space} (hy : y ≠ 0) :
    {z : Space | ‖y‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖y‖} ∈ 𝓝 y := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  refine Metric.mem_nhds_iff.2 ⟨‖y‖ / 2, by positivity, fun z hz => ?_⟩
  have h1 : ‖z - y‖ < ‖y‖ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have h2 := norm_sub_norm_le y z
  have h3 := norm_sub_norm_le z y
  rw [norm_sub_rev] at h2
  exact ⟨by linarith, by linarith⟩

theorem angular_farDecay (hoff : ScalarSmoothAwayFromOrigin) (P : ShapeParams) (hP : IsShapeParams P)
    (M : ℤ) (w : Bool) (U : JetSpline) (κa : ℕ) (hU : IsJetClass 1 1 U)
    (hadm : AxisAdmissible M w ⟨U, 0, 0, κa⟩)
    (hUt : ∀ t t' x, U.toSpline.evalHalf t x = U.toSpline.evalHalf t' x) :
    FarDecay 0 (scalarValue P ⟨(0, 0), 0⟩ M w ⟨U, 0, 0, κa⟩ 0) := by
  obtain ⟨hA1, hA2⟩ := hoff P ⟨(0, 0), 0⟩ M w ⟨U, 0, 0, κa⟩ 0 hP hU hadm
  refine hom_farDecay (fun s hs y => ?_) (fun y hy => (hA1 y hy).differentiableAt one_ne_zero) ?_
  · simp only [scalarValue, pointAngle_smul hs, heightRatio_smul hs, polarSine]
    rw [hUt (chartCoord P (s • y)) (chartCoord P y)]
    simp [weightPoly]
  · intro y hy
    have hy' : y ≠ 0 := hy
    obtain ⟨K, hK⟩ := hA2 (‖y‖ / 2) (2 * ‖y‖) (by have := norm_pos_iff.2 hy'; positivity)
    exact ⟨K, _, mem_nhdsWithin_of_mem_nhds (annulus_mem_nhds hy'), hK⟩

theorem chart_ge_of_far (P : ShapeParams) (hL : 0 < P.chartLength) {tb : ℝ} (htb : tb < 1) {y : Space}
    (hy : P.chartLength / (1 - tb) < ‖y‖) : tb ≤ chartCoord P y := by
  have h1 := one_sub_chartCoord P hL y
  have hc : 0 < 1 - tb := by linarith
  have hpos : 0 < ‖y‖ + P.chartLength := by positivity
  have h2 : P.chartLength < (1 - tb) * ‖y‖ := by rwa [div_lt_iff₀ hc, mul_comm] at hy
  have h3 : P.chartLength * (‖y‖ + P.chartLength)⁻¹ < 1 - tb := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
    nlinarith
  linarith

theorem far_decay (hoff : ScalarSmoothAwayFromOrigin) (P : ShapeParams) (κ : FieldKey) (M : ℤ) (w : Bool)
    (S : PotScalar) (hP : IsShapeParams P) (hS : IsJetClass 1 1 S.amp) (hadm : AxisAdmissible M w S)
    {h z : ℕ} (hz : z ≤ S.amp.tAxis.depth) (hhz : h ≤ S.highOrder + z) (hv : EndVanishOrder S.amp z) :
    FarDecay h (scalarValue P κ M w S 0) := by
  have hL := hP.chartLength_pos
  obtain ⟨U, hUc, hUadm, hUt, hUg⟩ := exists_unit_spline hS hadm
  have hA := angular_farDecay hoff P hP M w U S.axisPower hUc hUadm hUt
  obtain ⟨tb, htb, D, hfac⟩ := lastCell_factor S.amp hS.t_axis hz hv
  obtain ⟨vv, hinj, hvv⟩ := interp_parts tb htb D
  have hJ : IsJoinedSpline 1 1 S.amp.toSpline :=
    CertCell.GivenShape.Internal.joinedSpline_of_jetClass jetSplineJoined hS
  have hsp := SlopeRegular.spline hJ le_rfl le_rfl
  set G : ℝ × ℝ → ℂ := fun p => ∑ k, (Lagrange.basis Finset.univ (fun k => (vv k : ℂ)) k).eval (p.1 : ℂ) *
    (S.amp.toSpline.evalHalf (vv k) p.2 * ((((vv k : ℝ) : ℂ) - 1) ^ z)⁻¹) with hG
  have hGreg : SlopeRegular G := slopeRegular_sum _ _ fun k _ =>
    (slopeRegular_poly _).mul ((slopeRegular_slice hsp (vv k)).mul (const_reg _))
  set Gc : ℝ × ℝ → ℂ := fun p => ((p.1 ^ S.lowOrder : ℝ) : ℂ) * ((-1 : ℂ) ^ z * G p) with hGc
  have hGcreg : SlopeRegular Gc :=
    (realC_reg (f := fun p : ℝ × ℝ => p.1 ^ S.lowOrder) (by fun_prop)).mul ((const_reg _).mul hGreg)
  have hcomp := FarDecay.comp (chartPair_farDecay P hL) (chartPair_mem P hL) hGcreg
  have hph := phaseC_farDecay hP.phase (κ.phaseIndex : ℝ)
  have htail := tailPow_farDecay hL (S.highOrder + z)
  have hprod := FarDecay.smul hA (FarDecay.smul hph (FarDecay.smul htail hcomp rfl) rfl) rfl
  refine farDecay_congr_far (farDecay_mono hprod (by omega)) (P.chartLength / (1 - tb)) fun y hy => ?_
  have hty := chart_ge_of_far P hL htb hy
  set t := chartCoord P y with ht
  set x := heightRatio y with hx
  have hgt := interp_eq hinj hvv hfac t x hty
  have h1t : (((P.chartLength * (‖y‖ + P.chartLength)⁻¹ : ℝ)) : ℂ) = 1 - (t : ℂ) := by
    rw [← one_sub_chartCoord P hL y]; push_cast; rfl
  have hsgn : ((t : ℂ) - 1) ^ z = (-1 : ℂ) ^ z * (1 - (t : ℂ)) ^ z := by
    rw [← mul_pow]; ring_nf
  have hGt : G (t, x) = ∑ k, (Lagrange.basis Finset.univ (fun k => (vv k : ℂ)) k).eval (t : ℂ) *
      (S.amp.toSpline.evalHalf (vv k) x / (((vv k : ℝ) : ℂ) - 1) ^ z) := by
    simp only [hG, div_eq_mul_inv]
  have hgU := hUg t x
  simp only [scalarValue, smul_eq_mul, hGc, weightPoly]
  rw [← hGt] at hgt
  rw [← ht, ← hx, h1t, ← hgU, hgt, hsgn, pow_add]
  have e1 : Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * 0 + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (((2 * Real.pi * (labelTime ((0 : ℤ), (0 : ℤ)) : ℝ) * 0 + (M : ℝ) * pointAngle y +
      ((0 : ℤ) : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((M : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [e1, e2]
  push_cast
  ring


theorem combine_bound {a Bn Cf Rf Y K : ℝ} {k m : ℕ} (hk : k ≤ m) (hRf : 1 ≤ Rf) (hY : 0 ≤ Y) (hCf : 0 ≤ Cf)
    (hK : |Bn| * (1 + Rf) ^ m + 2 ^ m * Cf ≤ K) (hn : Y ≤ Rf → a ≤ Bn) (hf : Rf ≤ Y → a ≤ Cf * Y⁻¹ ^ k) :
    a ≤ K / (1 + Y) ^ k := by
  rw [le_div_iff₀ (by positivity)]
  have hm0 : 0 ≤ 2 ^ m * Cf := by positivity
  have hn0 : 0 ≤ |Bn| * (1 + Rf) ^ m := by positivity
  rcases le_total Y Rf with h | h
  · have ha : a ≤ |Bn| := (hn h).trans (le_abs_self Bn)
    have p1 : (1 + Y) ^ k ≤ (1 + Rf) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have p2 : (1 + Rf) ^ k ≤ (1 + Rf) ^ m := pow_le_pow_right₀ (by linarith) hk
    have p0 : 0 ≤ (1 + Y) ^ k := by positivity
    calc a * (1 + Y) ^ k ≤ |Bn| * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
      _ ≤ |Bn| * (1 + Rf) ^ m := mul_le_mul_of_nonneg_left (p1.trans p2) (abs_nonneg _)
      _ ≤ K := by linarith
  · have hY1 : 1 ≤ Y := hRf.trans h
    have hYp : 0 < Y := by linarith
    have ha := hf h
    have p0 : 0 ≤ (1 + Y) ^ k := by positivity
    have e : Y⁻¹ ^ k * (1 + Y) ^ k = ((1 + Y) * Y⁻¹) ^ k := by rw [mul_pow]; ring
    have q : (1 + Y) * Y⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hYp]; linarith
    have q2 : ((1 + Y) * Y⁻¹) ^ k ≤ 2 ^ m :=
      (pow_le_pow_left₀ (by positivity) q k).trans (pow_le_pow_right₀ (by norm_num) hk)
    calc a * (1 + Y) ^ k ≤ Cf * Y⁻¹ ^ k * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
      _ = Cf * ((1 + Y) * Y⁻¹) ^ k := by rw [mul_assoc, e]
      _ ≤ Cf * 2 ^ m := mul_le_mul_of_nonneg_left q2 hCf
      _ ≤ K := by linarith

theorem second_bound_near {f : Space → ℂ} {δ Rf : ℝ} (hδ : 0 < δ) {Lδ La : NNReal}
    (hLδ : LipschitzOnWith Lδ (fderiv ℝ f) (Metric.closedBall 0 δ))
    (hLa : LipschitzOnWith La (fderiv ℝ f) {y : Space | δ / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ Rf + 1}) (y : Space)
    (hy : ‖y‖ ≤ Rf) : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ max (Lδ : ℝ) La := by
  by_cases hyδ : ‖y‖ < δ
  · have hs : Metric.closedBall (0 : Space) δ ∈ 𝓝 y :=
      Metric.closedBall_mem_nhds_of_mem (by rwa [Metric.mem_ball, dist_zero_right])
    exact (norm_fderiv_le_of_lipschitzOn ℝ hs hLδ).trans (le_max_left _ _)
  · push_neg at hyδ
    have hs : {y : Space | δ / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ Rf + 1} ∈ 𝓝 y := by
      refine Metric.mem_nhds_iff.2 ⟨min (δ / 2) 1, by positivity, fun z hz => ?_⟩
      have h1 : ‖z - y‖ < min (δ / 2) 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have h2 := norm_sub_norm_le y z
      have h3 := norm_sub_norm_le z y
      rw [norm_sub_rev] at h2
      have h4 := min_le_left (δ / 2) 1
      have h5 := min_le_right (δ / 2) 1
      exact ⟨by linarith, by linarith⟩
    exact (norm_fderiv_le_of_lipschitzOn ℝ hs hLa).trans (le_max_right _ _)

end Internal.ScalarDecay

open Internal.ScalarDecay in
theorem scalarDecayOrder_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) (h : ℕ) :
    ScalarDecayOrder h := by
  intro P κ M w S hP hS hadm
  obtain ⟨z, hz, hhz, hv⟩ := hS.end_order
  have hfar := far_decay hoff P κ M w S hP hS.smooth_class hadm hz hhz hv
  set f := scalarValue P κ M w S 0 with hfdef
  obtain ⟨Cf, Rf, hCf, hRf, hb⟩ := hfar.bounds
  obtain ⟨hO1, hO2⟩ := hoff P κ M w S 0 hP hS.smooth_class hadm
  obtain ⟨hN1, δ, hδ, Lδ, hLδ⟩ := hnear P κ M w S 0 hP hS.smooth_class hadm hS.start_order
  have hC1 : ContDiff ℝ 1 f := contDiff_iff_contDiffAt.2 fun y => by
    by_cases hy : y = 0
    · rw [hy]; exact hN1
    · exact hO1 y hy
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : Space) Rf).exists_bound_of_continuousOn
    hC1.continuous.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_closedBall (0 : Space) Rf).exists_bound_of_continuousOn
    (hC1.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨La, hLa⟩ := hO2 (δ / 2) (Rf + 1) (by positivity)
  set Bn : ℝ := |B0| + |B1| + max (Lδ : ℝ) La with hBn
  set K : ℝ := |Bn| * (1 + Rf) ^ (h + 2) + 2 ^ (h + 2) * Cf with hK
  have hmem : ∀ y : Space, ‖y‖ ≤ Rf → y ∈ Metric.closedBall (0 : Space) Rf := fun y hy => by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hmax0 : 0 ≤ max (Lδ : ℝ) La := le_max_of_le_left Lδ.2
  have n0 : ∀ y : Space, ‖y‖ ≤ Rf → ‖f y‖ ≤ Bn := fun y hy => by
    have := (hB0 y (hmem y hy)).trans (le_abs_self B0)
    have := abs_nonneg B1
    linarith
  have n1 : ∀ y : Space, ‖y‖ ≤ Rf → ‖fderiv ℝ f y‖ ≤ Bn := fun y hy => by
    have := (hB1 y (hmem y hy)).trans (le_abs_self B1)
    have := abs_nonneg B0
    linarith
  have n2 : ∀ y : Space, ‖y‖ ≤ Rf → ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ Bn := fun y hy => by
    have := second_bound_near hδ hLδ hLa y hy
    have := abs_nonneg B0
    have := abs_nonneg B1
    linarith
  have hKle : |Bn| * (1 + Rf) ^ (h + 2) + 2 ^ (h + 2) * Cf ≤ K := le_rfl
  refine ⟨K, fun σ y => ?_, fun σ => Filter.Eventually.of_forall fun y => ?_⟩
  all_goals
    set c : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hc
    have hc1 : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hfun : scalarValue P κ M w S σ = c • f := funext fun y => by
      rw [Pi.smul_apply, smul_eq_mul, hfdef, scalarValue_time]
    have hd1 : ∀ y, fderiv ℝ (scalarValue P κ M w S σ) y = c • fderiv ℝ f y := fun y => by
      rw [hfun, fderiv_const_smul_field]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [hfun, Pi.smul_apply, norm_smul, hc1, one_mul]
      exact combine_bound (by omega) hRf (norm_nonneg _) hCf hKle (n0 y) fun h' => (hb y h').1
    · rw [hd1, norm_smul, hc1, one_mul]
      exact combine_bound (by omega) hRf (norm_nonneg _) hCf hKle (n1 y) fun h' => (hb y h').2.1
  · have hd2 : (fun x => fderiv ℝ (scalarValue P κ M w S σ) x) = c • fun x => fderiv ℝ f x :=
      funext fun x => by rw [hd1, Pi.smul_apply]
    rw [hd2, fderiv_const_smul_field, Pi.smul_apply, norm_smul, hc1, one_mul]
    exact combine_bound le_rfl hRf (norm_nonneg _) hCf hKle (n2 y) fun h' => (hb y h').2.2

end PotentialShape

end Breakdown

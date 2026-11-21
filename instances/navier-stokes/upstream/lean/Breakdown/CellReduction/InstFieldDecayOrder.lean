import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline heightRatio radialVec polarVecQ azimVecQ weightPoly radialScale heightDeriv)

namespace Internal.DecayOrder

theorem near_far_bound {C0 M R r u : ℝ} {k K N : ℕ} (hkK : k ≤ K) (hkN : k ≤ N) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hr : 0 ≤ r) (hnear : r ≤ R → u ≤ C0) (hfar : R ≤ r → u ≤ M / r ^ K) :
    u ≤ (|C0| * (1 + R) ^ N + 2 ^ N * M) / (1 + r) ^ k := by
  have hpos : 0 < (1 + r) ^ k := by positivity
  have hA : 0 ≤ |C0| * (1 + R) ^ N := by
    have : 0 ≤ 1 + R := by linarith
    positivity
  have hB : 0 ≤ 2 ^ N * M := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_total r R with h | h
  · have h1 : (1 + r) ^ k ≤ (1 + R) ^ N :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hkN)
    have h2 : u ≤ |C0| := (hnear h).trans (le_abs_self C0)
    calc u * (1 + r) ^ k ≤ |C0| * (1 + r) ^ k := mul_le_mul_of_nonneg_right h2 hpos.le
      _ ≤ |C0| * (1 + R) ^ N := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |C0| * (1 + R) ^ N + 2 ^ N * M := le_add_of_nonneg_right hB
  · have hr1 : 1 ≤ r := hR.trans h
    have hr0 : 0 < r := by linarith
    have h2 : u ≤ M / r ^ k :=
      (hfar h).trans (div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ hr1 hkK))
    have h3 : (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have h4 : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hkN
    calc u * (1 + r) ^ k ≤ M / r ^ k * (1 + r) ^ k := mul_le_mul_of_nonneg_right h2 hpos.le
      _ ≤ M / r ^ k * (2 * r) ^ k := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ k * M := by
        rw [mul_pow]
        field_simp
      _ ≤ 2 ^ N * M := mul_le_mul_of_nonneg_right h4 hM
      _ ≤ |C0| * (1 + R) ^ N + 2 ^ N * M := le_add_of_nonneg_left hA

theorem key_bounds_of_far {f : Space → Fin 3 → ℂ} (hs : IsKeyFieldSmooth f) {h e : ℕ} (he : e ≤ h)
    (hfar : ∃ M R : ℝ, 0 ≤ M ∧ 1 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ → ‖f y‖ ≤ M / ‖y‖ ^ h ∧
      ‖fderiv ℝ f y‖ ≤ M / ‖y‖ ^ (h + 1) ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M / ‖y‖ ^ (h + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖) ^ e ∧ ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ (e + 1) ∧
      ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C / (1 + ‖y‖) ^ (e + 2) := by
  obtain ⟨M, R, hM, hR, hf⟩ := hfar
  obtain ⟨C0, hC0⟩ := hs.bounded_on_ball R
  have hA : 0 ≤ |C0| * (1 + R) ^ (e + 2) := by
    have : 0 ≤ 1 + R := by linarith
    positivity
  refine ⟨|C0| * (1 + R) ^ (e + 2) + 2 ^ (e + 2) * M, by positivity, fun y => ⟨?_, ?_, ?_⟩⟩
  · exact near_far_bound (K := h) he (by omega) hM hR (norm_nonneg y) (fun hy => (hC0 y hy).1)
      (fun hy => (hf y hy).1)
  · exact near_far_bound (K := h + 1) (by omega) (by omega) hM hR (norm_nonneg y) (fun hy => (hC0 y hy).2.1)
      (fun hy => (hf y hy).2.1)
  · exact near_far_bound (K := h + 2) (by omega) le_rfl hM hR (norm_nonneg y) (fun hy => (hC0 y hy).2.2)
      (fun hy => (hf y hy).2.2)

theorem farBound_bounds {f : Space → Fin 3 → ℂ} {a : ℕ} (hf : GivenShape.Internal.FarBound f a) :
    ∃ M R : ℝ, 0 ≤ M ∧ 1 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ → ‖f y‖ ≤ M / ‖y‖ ^ a ∧
      ‖fderiv ℝ f y‖ ≤ M / ‖y‖ ^ (a + 1) ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M / ‖y‖ ^ (a + 2) := by
  obtain ⟨M, R, hM, hR, h⟩ := hf
  refine ⟨M, R, hM, by linarith, fun y hy => ?_⟩
  have hb := h y hy
  have hy0 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨hb.val y hy0, hb.der y hy0, ?_⟩
  have hl : LipschitzOnWith (Real.toNNReal (M / ‖y‖ ^ (a + 2))) (fderiv ℝ f) (Metric.ball y 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (hb.slope z hz w hw).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  have hn := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hl
  rwa [Real.coe_toNNReal _ (by positivity)] at hn

theorem farBound_degree_eq {f : Space → Fin 3 → ℂ} {a b : ℕ} (hf : GivenShape.Internal.FarBound f a)
    (hab : a = b) : GivenShape.Internal.FarBound f b := hab ▸ hf

open GivenShape.Internal in
theorem farBound_weightPow (P : ShapeParams) (hL : 0 < P.chartLength) (n : ℕ) :
    FarBound (fun y => ((1 - chartCoord P y : ℝ) : ℂ) ^ n) n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact farBound_const (1 : ℂ)
  | succ n ih =>
    have h := ih.mul (farBound_weight P hL)
    simpa only [pow_succ] using h

open GivenShape.Internal in
theorem typeTwo_farBound_order (P : ShapeParams) (hP : IsShapeParams P) (D : TimeFieldData)
    (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (h0 : κ.label.1 = 0) (σ : ℝ) :
    FarBound (keyVector P κ (D.amp κ) σ) (D.amp κ).highOrder := by
  obtain ⟨n, hn⟩ : ∃ n, (D.amp κ).highOrder = n + 1 :=
    ⟨(D.amp κ).highOrder - 1, by have := hD.highOrder_pos κ hκ; omega⟩
  set A := D.amp κ with hA
  have hL := hP.chartLength_pos
  obtain ⟨Q, t0, ht00, ht01, hQ⟩ := origin_eq_poly_near_one P.origin hP.origin
  have hS := hD.stream_class κ hκ h0
  have hG := hD.swirl_class κ hκ h0
  have hSt := ((splineDerivatives_holds 2 2 A.stream hS).1 (by norm_num)).1
  have hSx := ((splineDerivatives_holds 2 2 A.stream hS).2 (by norm_num)).1
  set α := A.axisCoef
  have hQc : ContDiff ℝ 2 (fun t : ℝ => Q.eval t) := by
    simpa [Polynomial.coe_aeval_eq_eval] using Q.contDiff_aeval (𝕜 := ℝ) 2
  have hQd : ContDiff ℝ 2 (fun t : ℝ => Q.derivative.eval t) := by
    simpa [Polynomial.coe_aeval_eq_eval] using Q.derivative.contDiff_aeval (𝕜 := ℝ) 2
  have hw := farBound_weightPow P hL (n + 1)
  have hT : FarBound (fun y => ((chartCoord P y : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 : ℝ) : ℂ)) (contDiff_ofReal_two (by fun_prop))
  have hTd : FarBound (fun y => ((chartCoord P y * ((1 - chartCoord P y) - ((n : ℝ) + 1) * chartCoord P y) : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 * ((1 - u.1) - ((n : ℝ) + 1) * u.1) : ℝ) : ℂ))
      (contDiff_ofReal_two (by fun_prop))
  have hTp : FarBound (fun y => ((chartCoord P y * (chartCoord P y * (1 - chartCoord P y)) : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 * (u.1 * (1 - u.1)) : ℝ) : ℂ))
      (contDiff_ofReal_two (by fun_prop))
  have hm2 : FarBound (fun y => ((-(2 * heightRatio y) : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((-(2 * u.2) : ℝ) : ℂ)) (contDiff_ofReal_two (by fun_prop))
  have hQx : FarBound (fun y => ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((Q.eval u.1 * u.2 : ℝ) : ℂ))
      (contDiff_ofReal_two ((hQc.comp contDiff_fst).mul contDiff_snd))
  have hQ0 : FarBound (fun y => ((Q.eval (chartCoord P y) : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((Q.eval u.1 : ℝ) : ℂ)) (contDiff_ofReal_two (hQc.comp contDiff_fst))
  have hQ1x : FarBound (fun y => ((Q.derivative.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((Q.derivative.eval u.1 * u.2 : ℝ) : ℂ))
      (contDiff_ofReal_two ((hQd.comp contDiff_fst).mul contDiff_snd))
  have hq : FarBound (fun y => polarFactor (heightRatio y)) 0 :=
    farBound_chart_smooth P hL (g := fun u => polarFactor u.2) (contDiff_ofReal_two (by fun_prop))
  have hS0 := farBound_spline P hL A.stream hS (by norm_num) (by norm_num)
  have hSx0 := farBound_spline P hL (xDerivSpline A.stream) hSx (by norm_num) (by norm_num)
  have hSt0 := farBound_spline P hL (tDerivSpline A.stream) hSt (by norm_num) (by norm_num)
  have hG0 := farBound_spline P hL A.swirl hG (by norm_num) (by norm_num)
  have hΘ := farBound_phaseSlope P hP κ.phaseIndex
  have hph := farBound_keyPhase P hP κ h0 σ
  have hΨ : FarBound (fun y => α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
      A.stream.evalHalf (chartCoord P y) (heightRatio y)) 0 := ((farBound_const α).mul hQx).add hS0
  have hT0 : FarBound (fun y => -(((chartCoord P y : ℝ) : ℂ) *
      (((-(2 * heightRatio y) : ℝ) : ℂ) * (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
        A.stream.evalHalf (chartCoord P y) (heightRatio y)) +
      polarFactor (heightRatio y) * (α * ((Q.eval (chartCoord P y) : ℝ) : ℂ) +
        (xDerivSpline A.stream).evalHalf (chartCoord P y) (heightRatio y))))) 0 :=
    (hT.mul ((hm2.mul hΨ).add (hq.mul (((farBound_const α).mul hQ0).add hSx0)))).neg
  have hT1 : FarBound (fun y => -(((chartCoord P y * ((1 - chartCoord P y) - ((n : ℝ) + 1) * chartCoord P y) : ℝ) : ℂ) *
        (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
          A.stream.evalHalf (chartCoord P y) (heightRatio y)) +
      ((chartCoord P y * (chartCoord P y * (1 - chartCoord P y)) : ℝ) : ℂ) *
        (α * ((Q.derivative.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
          (tDerivSpline A.stream).evalHalf (chartCoord P y) (heightRatio y)) +
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P (chartCoord P y) : ℝ) : ℂ) *
        (((chartCoord P y : ℝ) : ℂ) * (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
            A.stream.evalHalf (chartCoord P y) (heightRatio y))) +
      2 * (((chartCoord P y : ℝ) : ℂ) * (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
            A.stream.evalHalf (chartCoord P y) (heightRatio y))))) 0 :=
    ((((hTd.mul hΨ).add (hTp.mul (((farBound_const α).mul hQ1x).add hSt0))).add
      (((farBound_const Complex.I).mul hΘ).mul (hT.mul hΨ))).add ((farBound_const 2).mul (hT.mul hΨ))).neg
  have hT2 : FarBound (fun y => ((chartCoord P y : ℝ) : ℂ) * A.swirl.evalHalf (chartCoord P y) (heightRatio y)) 0 :=
    hT.mul hG0
  have hV := hph.smul ((((hw.mul hT0).smul farBound_radialFrame).add ((hw.mul hT1).smul farBound_polarFrame)).add
    ((hw.mul hT2).smul farBound_azimFrame))
  rw [hn]
  refine (farBound_degree_eq hV (by omega)).congr (R0 := P.chartLength * t0 / (1 - t0)) fun y hy => ?_
  obtain ⟨htl, htu⟩ := chartCoord_gt P hL ht00 ht01 y hy
  have hsv : ∀ t', t0 < t' → t' < 1 → ∀ x', streamValue P A t' x' =
      α * ((Q.eval t' * x' : ℝ) : ℂ) + A.stream.evalHalf t' x' := by
    intro t' h1 h2 x'
    simp only [streamValue, hQ t' h1 h2]
    rfl
  set t := chartCoord P y with ht
  set x := heightRatio y with hx
  obtain ⟨hSxd, hStd⟩ := spline_partials A.stream hS (by norm_num) (by norm_num) t x
  have hHD : heightDeriv (fun t' x' => polarFactor x' * streamValue P A t' x') t x =
      ((-(2 * x) : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
        polarFactor x * (α * ((Q.eval t : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf t x) := by
    have hfun : (fun x' => polarFactor x' * streamValue P A t x') =
        fun x' => polarFactor x' * (α * ((Q.eval t * x' : ℝ) : ℂ) + A.stream.evalHalf t x') := by
      funext x'
      rw [hsv t htl htu x']
    show deriv (fun x' => polarFactor x' * streamValue P A t x') x = _
    rw [hfun]
    have hpf : HasDerivAt (fun x' => polarFactor x') (((-(2 * x)) : ℝ) : ℂ) x := by
      have h2 := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      refine h2.congr_deriv ?_
      push_cast
      ring
    have hlin : HasDerivAt (fun x' => α * ((Q.eval t * x' : ℝ) : ℂ)) (α * ((Q.eval t : ℝ) : ℂ)) x := by
      have h2 := (((hasDerivAt_id' x).const_mul (Q.eval t)).ofReal_comp).const_mul α
      refine h2.congr_deriv ?_
      simp
    exact (hpf.mul (hlin.add hSxd)).deriv
  have hRS : deriv (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) t =
      (((1 - t) ^ (n + 1) - ((n : ℝ) + 1) * t * (1 - t) ^ n : ℝ) : ℂ) *
        (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      weightPoly 1 A.highOrder t * (α * ((Q.derivative.eval t * x : ℝ) : ℂ) +
        (tDerivSpline A.stream).evalHalf t x) := by
    have hev : (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) =ᶠ[nhds t]
        (fun t' => weightPoly 1 A.highOrder t' * (α * ((Q.eval t' * x : ℝ) : ℂ) + A.stream.evalHalf t' x)) := by
      filter_upwards [Ioo_mem_nhds htl htu] with t' ht'
      rw [hsv t' ht'.1 ht'.2 x]
    rw [hev.deriv_eq]
    have hpw : HasDerivAt (fun t' => weightPoly 1 A.highOrder t')
        ((((1 - t) ^ (n + 1) - ((n : ℝ) + 1) * t * (1 - t) ^ n) : ℝ) : ℂ) t := by
      simp only [weightPoly, hn]
      have h2 := ((hasDerivAt_pow 1 t).mul (((hasDerivAt_id' t).const_sub 1).pow (n + 1))).ofReal_comp
      refine h2.congr_deriv ?_
      push_cast
      simp only [pow_zero, pow_one, Pi.pow_apply]
      push_cast
      ring
    have hlinT : HasDerivAt (fun t' => α * ((Q.eval t' * x : ℝ) : ℂ)) (α * ((Q.derivative.eval t * x : ℝ) : ℂ)) t :=
      ((Q.hasDerivAt t).mul_const x).ofReal_comp.const_mul α
    exact (hpw.mul (hlinT.add hStd)).deriv
  have hrc0 : reducedComps P κ A t x 0 = ((1 - t : ℝ) : ℂ) ^ (n + 1) * -(((t : ℝ) : ℂ) *
      (((-(2 * x) : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      polarFactor x * (α * ((Q.eval t : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf t x))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_zero]
    rw [hHD]
    simp only [weightPoly, hn]
    push_cast
    ring
  have hrc1 : reducedComps P κ A t x 1 = ((1 - t : ℝ) : ℂ) ^ (n + 1) * -(((t * ((1 - t) - ((n : ℝ) + 1) * t) : ℝ) : ℂ) *
        (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      ((t * (t * (1 - t)) : ℝ) : ℂ) *
        (α * ((Q.derivative.eval t * x : ℝ) : ℂ) + (tDerivSpline A.stream).evalHalf t x) +
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P t : ℝ) : ℂ) *
        (((t : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x)) +
      2 * (((t : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_one, Matrix.cons_val_zero, shiftedScale, radialScale]
    rw [hRS, hsv t htl htu x]
    simp only [weightPoly, hn]
    push_cast
    ring
  have hrc2 : reducedComps P κ A t x 2 = ((1 - t : ℝ) : ℂ) ^ (n + 1) * (((t : ℝ) : ℂ) *
      A.swirl.evalHalf t x) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [weightPoly, hn]
    push_cast
    ring
  funext i
  simp only [keyVector, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [hrc0, hrc1, hrc2]


def azimPartFull (A : KeyAmp) (e0 n : ℕ) (kc : ℂ) (z : ℝ × ℝ) : ℂ :=
  Complex.I / kc * (((z.1 * ((e0 : ℝ) * z.1 ^ (e0 - 1) * (1 - z.1) - ((n : ℝ) + 1) * z.1 ^ e0) : ℝ) : ℂ) *
      A.radial.evalHalf z.1 z.2 +
    ((z.1 * (z.1 ^ e0 * (1 - z.1)) : ℝ) : ℂ) * (tDerivSpline A.radial).evalHalf z.1 z.2 +
    2 * ((z.1 ^ e0 : ℝ) : ℂ) * A.radial.evalHalf z.1 z.2 +
    ((6 * z.2 : ℝ) : ℂ) * ((z.1 ^ e0 : ℝ) : ℂ) * A.polar.evalHalf z.1 z.2 +
    ((-(1 - z.2 ^ 2) : ℝ) : ℂ) * ((z.1 ^ e0 : ℝ) : ℂ) * (xDerivSpline A.polar).evalHalf z.1 z.2)

open GivenShape.Internal.KeyDecay in
theorem azimPartFull_regular (A : KeyAmp) (e0 n : ℕ) (kc : ℂ) (hR : IsJoinedSpline 2 1 A.radial)
    (hP : IsJoinedSpline 1 2 A.polar) : SlopeRegular (azimPartFull A e0 n kc) := by
  have sR := SlopeRegular.spline hR (by norm_num) (by norm_num)
  have sP := SlopeRegular.spline hP (by norm_num) (by norm_num)
  have sRt := SlopeRegular.spline ((splineDerivatives_holds 2 1 A.radial hR).1 (by norm_num)).1
    (by norm_num) (by norm_num)
  have sPx := SlopeRegular.spline ((splineDerivatives_holds 1 2 A.polar hP).2 (by norm_num)).1
    (by norm_num) (by norm_num)
  have v := realC_reg (f := fun z : ℝ × ℝ => z.1 ^ e0) (by fun_prop)
  have t1 := SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ =>
    z.1 * ((e0 : ℝ) * z.1 ^ (e0 - 1) * (1 - z.1) - ((n : ℝ) + 1) * z.1 ^ e0)) (by fun_prop)) sR
  have t2 := SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => z.1 * (z.1 ^ e0 * (1 - z.1))) (by fun_prop)) sRt
  have t3 := SlopeRegular.mul (SlopeRegular.mul (const_reg 2) v) sR
  have t4 := SlopeRegular.mul (SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => 6 * z.2) (by fun_prop)) v) sP
  have t5 := SlopeRegular.mul (SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => -(1 - z.2 ^ 2))
    (by fun_prop)) v) sPx
  exact SlopeRegular.mul (const_reg _) ((((t1.add t2).add t3).add t4).add t5)

open GivenShape.Internal.KeyDecay in
theorem tailPow_farDecay {L : ℝ} (hL : 0 < L) (n : ℕ) :
    FarDecay n (fun z : Space => (((L * (‖z‖ + L)⁻¹ : ℝ)) : ℂ) ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact FarDecay.const (1 : ℂ)
  | succ n ih =>
    have h := FarDecay.smul ih (tailC_farDecay hL) (c := n + 1) rfl
    simpa only [smul_eq_mul, pow_succ] using h

open GivenShape.Internal.KeyDecay in
theorem reduced_zero_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (t x : ℝ) :
    reducedComps P κ A t x 0 = axisFactor x * ((1 - t : ℝ) : ℂ) ^ (n + 1) * radialPart A A.lowOrder 0 (t, x) := by
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_zero, radialPart, weightLow, weightPoly, hn, axisFactor]
  push_cast
  ring

open GivenShape.Internal.KeyDecay in
theorem reduced_one_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (t x : ℝ) :
    reducedComps P κ A t x 1 = axisFactor x * ((1 - t : ℝ) : ℂ) ^ (n + 1) * polarPart A A.lowOrder 0 (t, x) := by
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_one, polarPart, weightLow, weightPoly, hn, axisFactor]
  push_cast
  ring

open GivenShape.Internal.KeyDecay in
theorem reduced_two_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (hR : IsJoinedSpline 2 1 A.radial) (hP : IsJoinedSpline 1 2 A.polar)
    (t x : ℝ) :
    reducedComps P κ A t x 2 = axisFactor x * ((1 - t : ℝ) : ℂ) ^ (n + 1) *
      (azimPartFull A A.lowOrder n (labelAzimuth P.azimuthOrder κ.label : ℂ) (t, x) +
        ((phaseSlope P t : ℝ) : ℂ) * azimSlopePart A A.lowOrder 0 (labelAzimuth P.azimuthOrder κ.label : ℂ)
          (κ.phaseIndex : ℂ) (t, x)) := by
  have hdt : HasDerivAt (fun t' => weightPoly A.lowOrder A.highOrder t' * axisFactor x * A.radial.evalHalf t' x)
      (((weightDeriv A.lowOrder A.highOrder t : ℝ) : ℂ) * axisFactor x * A.radial.evalHalf t x +
        weightPoly A.lowOrder A.highOrder t * axisFactor x * (tDerivSpline A.radial).evalHalf t x) t :=
    (((wR_hasDerivAt A.lowOrder A.highOrder t).ofReal_comp).mul_const (axisFactor x)).mul
      (spline_t_hasDerivAt hR (by norm_num) (by norm_num) t x)
  have hpf : HasDerivAt (fun x' : ℝ => polarFactor x') (((-(2 * x)) : ℝ) : ℂ) x :=
    ((sq_hasDerivAt x).const_sub 1).ofReal_comp
  have haf : HasDerivAt (fun x' : ℝ => axisFactor x') (((2 * (1 - x ^ 2) * (-(2 * x))) : ℝ) : ℂ) x :=
    ((((sq_hasDerivAt x).const_sub 1).pow 2).congr_deriv (by norm_num)).ofReal_comp
  have hdx : HasDerivAt (fun x' => polarFactor x' *
      (weightPoly A.lowOrder A.highOrder t * axisFactor x' * A.polar.evalHalf t x'))
      ((((-(2 * x)) : ℝ) : ℂ) * (weightPoly A.lowOrder A.highOrder t * axisFactor x * A.polar.evalHalf t x) +
        polarFactor x * (weightPoly A.lowOrder A.highOrder t * (((2 * (1 - x ^ 2) * (-(2 * x))) : ℝ) : ℂ) *
          A.polar.evalHalf t x + weightPoly A.lowOrder A.highOrder t * axisFactor x *
            (xDerivSpline A.polar).evalHalf t x)) x :=
    hpf.mul ((haf.const_mul _).mul (spline_x_hasDerivAt hP (by norm_num) (by norm_num) t x))
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, shiftedScale, radialScale, heightDeriv]
  rw [hdt.deriv, hdx.deriv]
  simp only [azimPartFull, azimSlopePart, weightLow, weightDeriv, weightPoly, hn, axisFactor, polarFactor,
    Nat.add_sub_cancel]
  push_cast
  ring

open GivenShape.Internal.KeyDecay in
theorem typeOne_farDecay_order (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (σ : ℝ)
    (h1 : κ.label.1 ≠ 0) (n : ℕ) (hn : A.highOrder = n + 1) (hR : IsJoinedSpline 2 1 A.radial)
    (hPo : IsJoinedSpline 1 2 A.polar) : FarDecay (n + 1) (keyVector P κ A σ) := by
  have hL := hP.chartLength_pos
  set k : ℤ := labelAzimuth P.azimuthOrder κ.label with hk
  set kc : ℂ := (labelAzimuth P.azimuthOrder κ.label : ℂ) with hkc
  set jc : ℂ := (κ.phaseIndex : ℂ) with hjc
  set e0 := A.lowOrder with he0
  set cσ : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hcσ
  obtain ⟨r0, r1, -, r3⟩ := parts_regular A e0 0 kc jc hR hPo
  have r2 := azimPartFull_regular A e0 n kc hR hPo
  have hφ := chartPair_farDecay P hL
  have hm := chartPair_mem P hL
  have g0 := FarDecay.comp hφ hm r0
  have g1 := FarDecay.comp hφ hm r1
  have g2 := FarDecay.comp hφ hm r2
  have g3 := FarDecay.comp hφ hm r3
  have hT1 := FarDecay.smul g0 radialC_farDecay rfl
  have hT2 := FarDecay.smul g1 polarC_farDecay rfl
  have hT3a := FarDecay.smul (slopeC_farDecay hP.phase) g3 rfl
  have hT3 := FarDecay.smul (FarDecay.add g2 hT3a) azimC_farDecay rfl
  have hS := FarDecay.add (FarDecay.add hT1 hT2) hT3
  have hTS := FarDecay.smul (tailPow_farDecay hL (n + 1)) hS (c := n + 1) rfl
  have hPh := FarDecay.smul (phaseC_farDecay hP.phase (κ.phaseIndex : ℝ)) hTS (c := n + 1) (by omega)
  have hAn := FarDecay.smul (angularC_farDecay k) hPh (c := n + 1) (by omega)
  have hAll := FarDecay.smul (FarDecay.const cσ) hAn (c := n + 1) (by omega)
  convert hAll using 1
  funext y
  funext i
  simp only [keyVector, Pi.smul_apply, Pi.add_apply, smul_eq_mul, radialC, polarC, azimC, angularC]
  rw [keyPhase_eq, reduced_zero_eq P κ A h1 n hn, reduced_one_eq P κ A h1 n hn,
    reduced_two_eq P κ A h1 n hn hR hPo, one_sub_chartCoord P hL, phaseSlope_chartCoord P hL]
  ring

theorem key_bounds_at_zero (P : ShapeParams) (D : TimeFieldData) (e : ℕ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (he : e ≤ (D.amp κ).highOrder) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖keyVector P κ (D.amp κ) 0 y‖ ≤ C / (1 + ‖y‖) ^ e ∧
      ‖fderiv ℝ (keyVector P κ (D.amp κ) 0) y‖ ≤ C / (1 + ‖y‖) ^ (e + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (keyVector P κ (D.amp κ) 0)) y‖ ≤ C / (1 + ‖y‖) ^ (e + 2) := by
  by_cases h0 : κ.label.1 = 0
  · exact key_bounds_of_far (typeTwoKeySmooth_closed P D κ 0 hP hD hκ h0) he
      (farBound_bounds (typeTwo_farBound_order P hP D hD κ hκ h0 0))
  · obtain ⟨n, hn⟩ : ∃ n, (D.amp κ).highOrder = n + 1 :=
      ⟨(D.amp κ).highOrder - 1, by have := hD.highOrder_pos κ hκ; omega⟩
    have hfd := typeOne_farDecay_order P hP κ (D.amp κ) 0 h0 n hn (hD.radial_class κ hκ h0)
      (hD.polar_class κ hκ h0)
    obtain ⟨C, R, hC, hR, hb⟩ := hfd.bounds
    refine key_bounds_of_far (h := n + 1) (typeOneKeySmooth_closed P D κ 0 hP hD hκ h0) (hn ▸ he)
      ⟨C, R, hC, hR, fun y hy => ?_⟩
    obtain ⟨b1, b2, b3⟩ := hb y hy
    simp only [inv_pow, ← div_eq_mul_inv] at b1 b2 b3
    exact ⟨b1, b2, b3⟩

theorem key_bounds_all (P : ShapeParams) (D : TimeFieldData) (e : ℕ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (he : e ≤ (D.amp κ).highOrder) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, ‖keyVector P κ (D.amp κ) σ y‖ ≤ C / (1 + ‖y‖) ^ e ∧
      ‖fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ C / (1 + ‖y‖) ^ (e + 1) ∧
      ‖keyHess P κ (D.amp κ) σ y‖ ≤ C / (1 + ‖y‖) ^ (e + 2) := by
  obtain ⟨C, hC0, hC⟩ := key_bounds_at_zero P D e hP hD κ hκ he
  refine ⟨C, hC0, fun σ y => ?_⟩
  set c : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hc
  have hcn : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hf : keyVector P κ (D.amp κ) σ = c • keyVector P κ (D.amp κ) 0 :=
    GivenShape.Internal.keyVector_time_eq_smul P κ (D.amp κ) σ
  have hd : fderiv ℝ (keyVector P κ (D.amp κ) σ) = c • fderiv ℝ (keyVector P κ (D.amp κ) 0) := by
    funext x
    rw [hf, fderiv_const_smul_field]
  have hdd : keyHess P κ (D.amp κ) σ y = c • fderiv ℝ (fderiv ℝ (keyVector P κ (D.amp κ) 0)) y := by
    show fderiv ℝ (fun x => fderiv ℝ (keyVector P κ (D.amp κ) σ) x) y = _
    rw [hd, fderiv_const_smul_field]
    rfl
  obtain ⟨h1, h2, h3⟩ := hC y
  refine ⟨?_, ?_, ?_⟩
  · rw [hf, Pi.smul_apply, norm_smul, hcn, one_mul]
    exact h1
  · rw [hd, Pi.smul_apply, norm_smul, hcn, one_mul]
    exact h2
  · rw [hdd, norm_smul, hcn, one_mul]
    exact h3

theorem scale_le {K K' X X' d : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (hX : 0 ≤ X) (hXX : X ≤ X') (hd : 0 < d) :
    K * (X / d) ≤ K' * X' / d := by
  rw [mul_div_assoc]
  exact mul_le_mul hKK (div_le_div_of_nonneg_right hXX hd.le) (by positivity) (hK.trans hKK)

theorem phase_hasDerivAt (a σ : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((a * s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((a * σ : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)) σ := by
  have h1 : HasDerivAt (fun s : ℝ => ((a * s : ℝ) : ℂ)) (a : ℂ) σ := by
    have h2 := ((hasDerivAt_id σ).const_mul a).ofReal_comp
    simpa using h2
  exact (h1.mul_const Complex.I).cexp

end Internal.DecayOrder

theorem fieldDecayOrder_holds : FieldDecayOrderHolds := by
  intro P D e hP hD he
  have hkey : ∀ κ, ∃ C : ℝ, κ ∈ D.keys → 0 ≤ C ∧ ∀ σ y, ‖keyVector P κ (D.amp κ) σ y‖ ≤ C / (1 + ‖y‖) ^ e ∧
      ‖fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ C / (1 + ‖y‖) ^ (e + 1) ∧
      ‖keyHess P κ (D.amp κ) σ y‖ ≤ C / (1 + ‖y‖) ^ (e + 2) := by
    intro κ
    by_cases hκ : κ ∈ D.keys
    · obtain ⟨C, hC0, hC⟩ := Internal.DecayOrder.key_bounds_all P D e hP hD κ hκ (he κ hκ)
      exact ⟨C, fun _ => ⟨hC0, hC⟩⟩
    · exact ⟨0, fun h => absurd h hκ⟩
  choose C hC using hkey
  set a : FieldKey → ℝ := fun κ => 2 * Real.pi * (labelTime κ.label : ℝ) with ha
  set S : ℝ := ∑ κ ∈ D.keys, C κ with hS
  set T : ℝ := ∑ κ ∈ D.keys, |a κ| * C κ with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun κ hκ => (hC κ hκ).1
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun κ hκ => mul_nonneg (abs_nonneg _) (hC κ hκ).1
  set K₁ : ℝ := ‖realPartVec‖ with hK₁
  set K₂ : ℝ := ‖ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec‖ with hK₂
  have hK₁0 : 0 ≤ K₁ := norm_nonneg _
  have hK₂0 : 0 ≤ K₂ := norm_nonneg _
  have hdiff : ∀ κ ∈ D.keys, ∀ σ, Differentiable ℝ (keyVector P κ (D.amp κ) σ) := fun κ hκ σ =>
    GivenShape.Internal.keyVector_differentiable typeOneKeySmooth_closed typeTwoKeySmooth_closed P D hP hD σ κ hκ
  refine ⟨(K₁ + K₂) * (S + T), fun σ y => ?_⟩
  have hpos : ∀ k : ℕ, 0 < (1 + ‖y‖) ^ k := fun k => by positivity
  have hsum : ∀ k : ℕ, ∑ κ ∈ D.keys, C κ / (1 + ‖y‖) ^ k = S / (1 + ‖y‖) ^ k := fun k => by
    rw [hS, Finset.sum_div]
  have hsumT : ∑ κ ∈ D.keys, |a κ| * (C κ / (1 + ‖y‖) ^ e) = T / (1 + ‖y‖) ^ e := by
    rw [hT, Finset.sum_div]
    exact Finset.sum_congr rfl fun κ _ => by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ‖shapeInfoField P D σ y‖ ≤ K₁ * ‖complexField P D σ y‖ := realPartVec.le_opNorm _
    have h2 : ‖complexField P D σ y‖ ≤ S / (1 + ‖y‖) ^ e := by
      rw [← hsum e]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ((hC κ hκ).2 σ y).1)
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hK₁0).trans
      (Internal.DecayOrder.scale_le hK₁0 (le_add_of_nonneg_right hK₂0) hS0 (le_add_of_nonneg_right hT0) (hpos e)))
  · have hfun : (fun s => shapeInfoField P D s y) = fun s => realPartVec (∑ κ ∈ D.keys,
        Complex.exp (((a κ * s : ℝ) : ℂ) * Complex.I) • keyVector P κ (D.amp κ) 0 y) := by
      funext s
      simp only [shapeInfoField, complexField]
      congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [GivenShape.Internal.keyVector_time_eq_smul P κ (D.amp κ) s]
      rfl
    have hsd : HasDerivAt (fun s => ∑ κ ∈ D.keys, Complex.exp (((a κ * s : ℝ) : ℂ) * Complex.I) •
        keyVector P κ (D.amp κ) 0 y)
        (∑ κ ∈ D.keys, (Complex.exp (((a κ * σ : ℝ) : ℂ) * Complex.I) * ((a κ : ℂ) * Complex.I)) •
          keyVector P κ (D.amp κ) 0 y) σ :=
      HasDerivAt.fun_sum fun κ _ => (Internal.DecayOrder.phase_hasDerivAt (a κ) σ).smul_const _
    have hF : HasDerivAt (fun s => realPartVec (∑ κ ∈ D.keys, Complex.exp (((a κ * s : ℝ) : ℂ) * Complex.I) •
        keyVector P κ (D.amp κ) 0 y))
        (realPartVec (∑ κ ∈ D.keys, (Complex.exp (((a κ * σ : ℝ) : ℂ) * Complex.I) * ((a κ : ℂ) * Complex.I)) •
          keyVector P κ (D.amp κ) 0 y)) σ :=
      realPartVec.hasFDerivAt.comp_hasDerivAt σ hsd
    rw [hfun, hF.deriv]
    have h1 := realPartVec.le_opNorm (∑ κ ∈ D.keys, (Complex.exp (((a κ * σ : ℝ) : ℂ) * Complex.I) *
      ((a κ : ℂ) * Complex.I)) • keyVector P κ (D.amp κ) 0 y)
    have h2 : ‖∑ κ ∈ D.keys, (Complex.exp (((a κ * σ : ℝ) : ℂ) * Complex.I) * ((a κ : ℂ) * Complex.I)) •
        keyVector P κ (D.amp κ) 0 y‖ ≤ T / (1 + ‖y‖) ^ e := by
      rw [← hsumT]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ?_)
      rw [norm_smul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, one_mul, mul_one]
      exact mul_le_mul_of_nonneg_left ((hC κ hκ).2 0 y).1 (abs_nonneg _)
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hK₁0).trans
      (Internal.DecayOrder.scale_le hK₁0 (le_add_of_nonneg_right hK₂0) hT0 (le_add_of_nonneg_left hS0) (hpos e)))
  · have hder : HasFDerivAt (complexField P D σ)
        (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) y := by
      have h := HasFDerivAt.fun_sum (u := D.keys) (A := fun κ => keyVector P κ (D.amp κ) σ)
        (A' := fun κ => fderiv ℝ (keyVector P κ (D.amp κ) σ) y) (x := y)
        (fun κ hκ => (hdiff κ hκ σ y).hasFDerivAt)
      exact h
    have hF : fderiv ℝ (shapeInfoField P D σ) y =
        realPartVec.comp (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) :=
      (realPartVec.hasFDerivAt.comp y hder).fderiv
    rw [hF]
    have h1 := realPartVec.opNorm_comp_le (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y)
    have h2 : ‖∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ S / (1 + ‖y‖) ^ (e + 1) := by
      rw [← hsum (e + 1)]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ((hC κ hκ).2 σ y).2.1)
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hK₁0).trans
      (Internal.DecayOrder.scale_le hK₁0 (le_add_of_nonneg_right hK₂0) hS0 (le_add_of_nonneg_right hT0)
        (hpos (e + 1))))
  · have h2 : ∑ κ ∈ D.keys, ‖(ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp
        (keyHess P κ (D.amp κ) σ y)‖ ≤ K₂ * (S / (1 + ‖y‖) ^ (e + 2)) := by
      rw [← hsum (e + 2), Finset.mul_sum]
      refine Finset.sum_le_sum fun κ hκ => ?_
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((hC κ hκ).2 σ y).2.2 hK₂0)
    exact (norm_sum_le _ _).trans (h2.trans
      (Internal.DecayOrder.scale_le hK₂0 (le_add_of_nonneg_left hK₁0) hS0 (le_add_of_nonneg_right hT0)
        (hpos (e + 2))))


end Instantiation

end CellReduction

end Breakdown

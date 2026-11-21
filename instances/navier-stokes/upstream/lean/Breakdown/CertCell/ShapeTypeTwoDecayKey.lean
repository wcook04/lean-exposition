import Breakdown.CertCell.ShapeTypeTwoDecayPhase
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineDeriv
import Breakdown.CertCell.ShapeDecayNear
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

open CellCert.GivenFields (Spline heightRatio radialVec polarVecQ azimVecQ weightPoly radialScale heightDeriv)

theorem farBound_spline (P : ShapeParams) (hL : 0 < P.chartLength) {a b : ℕ} (S : Spline)
    (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    FarBound (fun y => S.evalHalf (chartCoord P y) (heightRatio y)) 0 :=
  farBound_chart P hL (g := fun u : ℝ × ℝ => S.evalHalf u.1 u.2)
    ((joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb)))
    (joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth a b S hS ha hb 1)

theorem spline_partials {a b : ℕ} (S : Spline) (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun x' => S.evalHalf t x') ((xDerivSpline S).evalHalf t x) x ∧
      HasDerivAt (fun t' => S.evalHalf t' x) ((tDerivSpline S).evalHalf t x) t := by
  have hd : Differentiable ℝ (fun u : ℝ × ℝ => S.evalHalf u.1 u.2) :=
    ((joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))).differentiable one_ne_zero
  obtain ⟨ht, hx⟩ := splineDerivatives_holds a b S hS
  refine ⟨?_, ?_⟩
  · have hp : HasDerivAt (fun x' : ℝ => (t, x')) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x t).prodMk (hasDerivAt_id' x)
    have h2 := HasFDerivAt.comp_hasDerivAt (l := fun u : ℝ × ℝ => S.evalHalf u.1 u.2) x (hd (t, x)).hasFDerivAt hp
    have e2 : ((fun u : ℝ × ℝ => S.evalHalf u.1 u.2) ∘ fun x' : ℝ => (t, x')) = fun x' => S.evalHalf t x' := by
      funext x'
      simp only [Function.comp_apply]
    rw [e2] at h2
    have e := h2.deriv
    rw [(hx hb).2 t x] at e
    rw [e]
    exact h2
  · have hp : HasDerivAt (fun t' : ℝ => (t', x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
    have h2 := HasFDerivAt.comp_hasDerivAt (l := fun u : ℝ × ℝ => S.evalHalf u.1 u.2) t (hd (t, x)).hasFDerivAt hp
    have e2 : ((fun u : ℝ × ℝ => S.evalHalf u.1 u.2) ∘ fun t' : ℝ => (t', x)) = fun t' => S.evalHalf t' x := by
      funext t'
      simp only [Function.comp_apply]
    rw [e2] at h2
    have e := h2.deriv
    rw [(ht ha).2 t x] at e
    rw [e]
    exact h2

theorem origin_eq_poly_near_one (g : OriginProfile) (hg : IsOriginProfile g) :
    ∃ (Q : Polynomial ℝ) (t0 : ℝ), 0 ≤ t0 ∧ t0 < 1 ∧ ∀ t, t0 < t → t < 1 → g.eval t = Q.eval t := by
  by_cases h : g.edge < 1
  · refine ⟨Polynomial.C g.tail, g.edge, hg.edge_pos.le, h, fun t h1 _ => ?_⟩
    simp [OriginProfile.eval, not_le.2 h1]
  · refine ⟨g.poly, 0, le_rfl, zero_lt_one, fun t _ h2 => ?_⟩
    have : t ≤ g.edge := (le_of_lt h2).trans (not_lt.1 h)
    simp [OriginProfile.eval, this]

theorem chartCoord_gt (P : ShapeParams) (hL : 0 < P.chartLength) {t0 : ℝ} (ht0 : 0 ≤ t0) (h1 : t0 < 1)
    (y : Space) (hy : P.chartLength * t0 / (1 - t0) < ‖y‖) : t0 < chartCoord P y ∧ chartCoord P y < 1 := by
  have hp : 0 < ‖y‖ + P.chartLength := by positivity
  have h1' : 0 < 1 - t0 := by linarith
  rw [div_lt_iff₀ h1'] at hy
  rw [chartCoord, lt_div_iff₀ hp, div_lt_one hp]
  constructor <;> nlinarith

theorem contDiff_ofReal_two {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (fun u => (f u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem farBound_typeTwoKey (P : ShapeParams) (hP : IsShapeParams P) (D : TimeFieldData)
    (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (h0 : κ.label.1 = 0) (σ : ℝ) :
    FarBound (keyVector P κ (D.amp κ) σ) 1 := by
  set A := D.amp κ with hA
  have hL := hP.chartLength_pos
  obtain ⟨Q, t0, ht00, ht01, hQ⟩ := origin_eq_poly_near_one P.origin hP.origin
  have hho : 1 ≤ A.highOrder := hD.highOrder_pos κ hκ
  obtain ⟨e', he'⟩ : ∃ e', A.highOrder = e' + 1 := ⟨A.highOrder - 1, by omega⟩
  have hS := hD.stream_class κ hκ h0
  have hG := hD.swirl_class κ hκ h0
  have hSt := ((splineDerivatives_holds 2 2 A.stream hS).1 (by norm_num)).1
  have hSx := ((splineDerivatives_holds 2 2 A.stream hS).2 (by norm_num)).1
  set α := A.axisCoef
  have hQc : ContDiff ℝ 2 (fun t : ℝ => Q.eval t) := by
    simpa [Polynomial.coe_aeval_eq_eval] using Q.contDiff_aeval (𝕜 := ℝ) 2
  have hQd : ContDiff ℝ 2 (fun t : ℝ => Q.derivative.eval t) := by
    simpa [Polynomial.coe_aeval_eq_eval] using Q.derivative.contDiff_aeval (𝕜 := ℝ) 2
  have hw := farBound_weight P hL
  have hP1 : FarBound (fun y => ((chartCoord P y * (1 - chartCoord P y) ^ e' : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 * (1 - u.1) ^ e' : ℝ) : ℂ))
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
  have hTpd : FarBound (fun y => ((chartCoord P y * ((1 - chartCoord P y) ^ (e' + 1) -
      ((e' : ℝ) + 1) * chartCoord P y * (1 - chartCoord P y) ^ e') : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 * ((1 - u.1) ^ (e' + 1) - ((e' : ℝ) + 1) * u.1 * (1 - u.1) ^ e') : ℝ) : ℂ))
      (contDiff_ofReal_two (by fun_prop))
  have hTp : FarBound (fun y => ((chartCoord P y * (chartCoord P y * (1 - chartCoord P y) ^ (e' + 1)) : ℝ) : ℂ)) 0 :=
    farBound_chart_smooth P hL (g := fun u => ((u.1 * (u.1 * (1 - u.1) ^ (e' + 1)) : ℝ) : ℂ))
      (contDiff_ofReal_two (by fun_prop))
  have hS0 := farBound_spline P hL A.stream hS (by norm_num) (by norm_num)
  have hSx0 := farBound_spline P hL (xDerivSpline A.stream) hSx (by norm_num) (by norm_num)
  have hSt0 := farBound_spline P hL (tDerivSpline A.stream) hSt (by norm_num) (by norm_num)
  have hG0 := farBound_spline P hL A.swirl hG (by norm_num) (by norm_num)
  have hΘ := farBound_phaseSlope P hP κ.phaseIndex
  have hph := farBound_keyPhase P hP κ h0 σ
  have hΨ : FarBound (fun y => α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
      A.stream.evalHalf (chartCoord P y) (heightRatio y)) 0 := ((farBound_const α).mul hQx).add hS0
  have hT0 : FarBound (fun y => -(((chartCoord P y * (1 - chartCoord P y) ^ e' : ℝ) : ℂ) *
      (((-(2 * heightRatio y) : ℝ) : ℂ) * (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
        A.stream.evalHalf (chartCoord P y) (heightRatio y)) +
      polarFactor (heightRatio y) * (α * ((Q.eval (chartCoord P y) : ℝ) : ℂ) +
        (xDerivSpline A.stream).evalHalf (chartCoord P y) (heightRatio y))))) 0 :=
    (hP1.mul ((hm2.mul hΨ).add (hq.mul (((farBound_const α).mul hQ0).add hSx0)))).neg
  have hT1 : FarBound (fun y => -(((chartCoord P y * ((1 - chartCoord P y) ^ (e' + 1) -
      ((e' : ℝ) + 1) * chartCoord P y * (1 - chartCoord P y) ^ e') : ℝ) : ℂ) *
        (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
          A.stream.evalHalf (chartCoord P y) (heightRatio y)) +
      ((chartCoord P y * (chartCoord P y * (1 - chartCoord P y) ^ (e' + 1)) : ℝ) : ℂ) *
        (α * ((Q.derivative.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
          (tDerivSpline A.stream).evalHalf (chartCoord P y) (heightRatio y)) +
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P (chartCoord P y) : ℝ) : ℂ) *
        (((chartCoord P y * (1 - chartCoord P y) ^ e' : ℝ) : ℂ) *
          (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
            A.stream.evalHalf (chartCoord P y) (heightRatio y))) +
      2 * (((chartCoord P y * (1 - chartCoord P y) ^ e' : ℝ) : ℂ) *
          (α * ((Q.eval (chartCoord P y) * heightRatio y : ℝ) : ℂ) +
            A.stream.evalHalf (chartCoord P y) (heightRatio y))))) 0 :=
    ((((hTpd.mul hΨ).add (hTp.mul (((farBound_const α).mul hQ1x).add hSt0))).add
      (((farBound_const Complex.I).mul hΘ).mul (hP1.mul hΨ))).add ((farBound_const 2).mul (hP1.mul hΨ))).neg
  have hT2 : FarBound (fun y => ((chartCoord P y * (1 - chartCoord P y) ^ e' : ℝ) : ℂ) *
      A.swirl.evalHalf (chartCoord P y) (heightRatio y)) 0 := hP1.mul hG0
  have hV := hph.smul ((((hw.mul hT0).smul farBound_radialFrame).add ((hw.mul hT1).smul farBound_polarFrame)).add
    ((hw.mul hT2).smul farBound_azimFrame))
  refine hV.congr (R0 := P.chartLength * t0 / (1 - t0)) fun y hy => ?_
  obtain ⟨htl, htu⟩ := chartCoord_gt P hL ht00 ht01 y hy
  have hsv : ∀ t', t0 < t' → t' < 1 → ∀ x', streamValue P A t' x' =
      α * ((Q.eval t' * x' : ℝ) : ℂ) + A.stream.evalHalf t' x' := by
    intro t' h1 h2 x'
    simp only [streamValue, hQ t' h1 h2]
    rfl
  set t := chartCoord P y with ht
  set x := heightRatio y with hx
  obtain ⟨hSxd, -⟩ := spline_partials A.stream hS (by norm_num) (by norm_num) t x
  obtain ⟨-, hStd⟩ := spline_partials A.stream hS (by norm_num) (by norm_num) t x
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
      have := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      refine this.congr_deriv ?_
      push_cast
      ring
    have hlin : HasDerivAt (fun x' => α * ((Q.eval t * x' : ℝ) : ℂ)) (α * ((Q.eval t : ℝ) : ℂ)) x := by
      have := (((hasDerivAt_id' x).const_mul (Q.eval t)).ofReal_comp).const_mul α
      refine this.congr_deriv ?_
      simp
    exact (hpf.mul (hlin.add hSxd)).deriv
  have hRS : deriv (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) t =
      (((1 - t) ^ (e' + 1) - ((e' : ℝ) + 1) * t * (1 - t) ^ e' : ℝ) : ℂ) *
        (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      weightPoly 1 A.highOrder t * (α * ((Q.derivative.eval t * x : ℝ) : ℂ) +
        (tDerivSpline A.stream).evalHalf t x) := by
    have hev : (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) =ᶠ[nhds t]
        (fun t' => weightPoly 1 A.highOrder t' * (α * ((Q.eval t' * x : ℝ) : ℂ) + A.stream.evalHalf t' x)) := by
      filter_upwards [Ioo_mem_nhds htl htu] with t' ht'
      rw [hsv t' ht'.1 ht'.2 x]
    rw [hev.deriv_eq]
    have hpw : HasDerivAt (fun t' => weightPoly 1 A.highOrder t')
        ((((1 - t) ^ (e' + 1) - ((e' : ℝ) + 1) * t * (1 - t) ^ e') : ℝ) : ℂ) t := by
      simp only [weightPoly, he']
      have := ((hasDerivAt_pow 1 t).mul (((hasDerivAt_id' t).const_sub 1).pow (e' + 1))).ofReal_comp
      refine this.congr_deriv ?_
      push_cast
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one, Pi.pow_apply]
      push_cast
      ring
    have hlinT : HasDerivAt (fun t' => α * ((Q.eval t' * x : ℝ) : ℂ)) (α * ((Q.derivative.eval t * x : ℝ) : ℂ)) t :=
      ((Q.hasDerivAt t).mul_const x).ofReal_comp.const_mul α
    exact (hpw.mul (hlinT.add hStd)).deriv
  have hrc0 : reducedComps P κ A t x 0 = ((1 - t : ℝ) : ℂ) * -(((t * (1 - t) ^ e' : ℝ) : ℂ) *
      (((-(2 * x) : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      polarFactor x * (α * ((Q.eval t : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf t x))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_zero]
    rw [hHD]
    simp only [weightPoly, he']
    push_cast
    ring
  have hrc1 : reducedComps P κ A t x 1 = ((1 - t : ℝ) : ℂ) * -(((t * ((1 - t) ^ (e' + 1) -
      ((e' : ℝ) + 1) * t * (1 - t) ^ e') : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x) +
      ((t * (t * (1 - t) ^ (e' + 1)) : ℝ) : ℂ) *
        (α * ((Q.derivative.eval t * x : ℝ) : ℂ) + (tDerivSpline A.stream).evalHalf t x) +
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P t : ℝ) : ℂ) *
        (((t * (1 - t) ^ e' : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x)) +
      2 * (((t * (1 - t) ^ e' : ℝ) : ℂ) * (α * ((Q.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x))) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_one, Matrix.cons_val_zero, shiftedScale, radialScale]
    rw [hRS, hsv t htl htu x]
    simp only [weightPoly, he']
    push_cast
    ring
  have hrc2 : reducedComps P κ A t x 2 = ((1 - t : ℝ) : ℂ) * (((t * (1 - t) ^ e' : ℝ) : ℂ) *
      A.swirl.evalHalf t x) := by
    simp only [reducedComps, if_pos h0, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [weightPoly, he']
    push_cast
    ring
  funext i
  simp only [keyVector, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [hrc0, hrc1, hrc2]

end Internal

end GivenShape

end CertCell

end Breakdown

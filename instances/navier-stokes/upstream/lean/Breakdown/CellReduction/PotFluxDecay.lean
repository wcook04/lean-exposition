import Breakdown.CellReduction.PotFluxDecayAmp
import Breakdown.CellReduction.PotFluxDecayNull
import Breakdown.CellReduction.PotFluxDivergence

open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (weightPoly heightRatio radialVec polarVecQ heightDeriv)

namespace FluxDecay.Internal

theorem heightRatio_abs_lt {y : Space} (hy : y 0 ≠ 0) : |heightRatio y| < 1 := by
  have hy0 : y ≠ 0 := fun e => hy (by simp [e])
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hsq := SphericalDivInternal.coords_sq y
  have hq : 0 < y 0 ^ 2 := by positivity
  unfold heightRatio
  rw [abs_div, abs_norm, div_lt_one hr]
  have h2 : |y 2| ^ 2 < ‖y‖ ^ 2 := by rw [sq_abs]; nlinarith
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _) hr.le (by norm_num)).1 h2

theorem chartCoord_nonneg (P : ShapeParams) (hP : IsShapeParams P) (y : Space) : 0 ≤ chartCoord P y := by
  have := hP.chartLength_pos
  unfold chartCoord
  positivity

theorem chartCoord_le_one (P : ShapeParams) (hP : IsShapeParams P) (y : Space) : chartCoord P y ≤ 1 := by
  have := hP.chartLength_pos
  unfold chartCoord
  rw [div_le_one (by positivity)]
  linarith

theorem chart_decay (P : ShapeParams) (hP : IsShapeParams P) (y : Space) :
    (1 - chartCoord P y) ^ 2 ≤ (max P.chartLength 1) ^ 2 / (1 + ‖y‖) ^ 2 := by
  have hL := hP.chartLength_pos
  have hn := norm_nonneg y
  have h1 : 1 - chartCoord P y = P.chartLength / (‖y‖ + P.chartLength) := by
    unfold chartCoord
    field_simp
    ring
  have h2 : P.chartLength / (‖y‖ + P.chartLength) ≤ max P.chartLength 1 / (1 + ‖y‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [le_max_left P.chartLength 1, le_max_right P.chartLength 1]
  rw [h1, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) h2 2

theorem fluxVector_divergence_bound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (K : PotKeyData)
    (c : PotComponent) (hr : FluxScalarEnd (K.radialFlux c)) (hp : FluxScalarEnd (K.polarFlux c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, y 0 ≠ 0 →
      chartCoord P y ∉ ((K.radialFlux c).amp.tAxis.breaks.drop 1).dropLast →
      chartCoord P y ∉ ((K.polarFlux c).amp.tAxis.breaks.drop 1).dropLast →
      heightRatio y ∉ ((K.radialFlux c).amp.xAxis.breaks.drop 1).dropLast →
      heightRatio y ∉ ((K.polarFlux c).amp.xAxis.breaks.drop 1).dropLast →
      (∀ i : Fin 3, DifferentiableAt ℝ (fun x => fluxVector P κ K c σ x i) y) ∧
      ‖y‖ * ‖∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ K c σ x i) y (unitVector i)‖ ≤
        C * (1 - chartCoord P y) ^ 2 := by
  set M := labelAzimuth P.azimuthOrder κ.label + c.shift with hM
  have hP' := shiftedParams_valid hP M
  obtain ⟨C, hC0, hC⟩ := framedFormula_bound (shiftedParams P M) hP' K c κ.phaseIndex
    (labelAzimuth (shiftedParams P M).azimuthOrder (shiftedKey κ M).label) hr hp
  refine ⟨C, hC0, fun σ y hy h1 h2 h3 h4 => ?_⟩
  have hx1 := heightRatio_abs_lt hy
  have hy0 : y ≠ 0 := fun e => hy (by simp [e])
  have hr0 : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hU : ∀ c', DifferentiableAt ℝ (fun z : ℝ × ℝ => fluxAmps K c z.1 z.2 c')
      (chartCoord (shiftedParams P M) y, heightRatio y) := by
    intro c'
    fin_cases c'
    · exact scalarAmp_differentiableAt (K.radialFlux c) c.carriesSine h1 h3 hx1
    · exact scalarAmp_differentiableAt (K.polarFlux c) c.carriesSine h2 h4 hx1
    · simp only [fluxAmps]
      exact differentiableAt_const _
  have hd := framedField_differentiableAt (shiftedParams P M) hP' (shiftedKey κ M) (shiftedTime κ M σ)
    (fluxAmps K c) (Or.inl hy) hU
  rw [fluxVector_eq, ← hM]
  refine ⟨fun i => differentiableAt_pi.1 hd i, ?_⟩
  have hsum : ∑ i : Fin 3, fderiv ℝ (fun x => framedField (shiftedParams P M) (shiftedKey κ M)
      (shiftedTime κ M σ) (fluxAmps K c) x i) y (unitVector i) =
      complexDivergence (framedField (shiftedParams P M) (shiftedKey κ M) (shiftedTime κ M σ) (fluxAmps K c)) y := by
    unfold complexDivergence
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hasFDerivAt_pi'.1 hd.hasFDerivAt i).fderiv]
    rfl
  rw [hsum, complexDivergence_framedField_offAxis _ hP' _ _ _ (Or.inl hy) hU, norm_mul, norm_div,
    keyPhase_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← mul_assoc, mul_one_div_cancel hr0.ne',
    one_mul]
  exact hC _ _ (chartCoord_nonneg P hP y) (chartCoord_le_one P hP y) hx1 h1 h4

theorem fluxVector_value_bound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (K : PotKeyData)
    (c : PotComponent) (hr : FluxScalarEnd (K.radialFlux c)) (hp : FluxScalarEnd (K.polarFlux c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y (i : Fin 3), ‖fluxVector P κ K c σ y i‖ ≤ C * (1 - chartCoord P y) ^ 2 := by
  obtain ⟨Br, hBr0, hbr⟩ := scalarAmp_bound (K.radialFlux c) c.carriesSine hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  obtain ⟨Bp, hBp0, hbp⟩ := scalarAmp_bound (K.polarFlux c) c.carriesSine hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  refine ⟨Br + Bp, by positivity, fun σ y i => ?_⟩
  have ht0 := chartCoord_nonneg P hP y
  have ht1 := chartCoord_le_one P hP y
  have hx := CellCert.GivenFields.DualRestOpenInternal.height_le y
  have hA := (hbr _ _ ht0 ht1 hx).1
  have hB := (hbp _ _ ht0 ht1 hx).1
  have hrv := CellCert.GivenFields.DualRestOpenInternal.radial_le y i
  have hpv := CellCert.GivenFields.DualRestOpenInternal.polar_le y i
  simp only [fluxVector, componentValue, scalarValue_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, keyPhase_norm, one_mul, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : ‖scalarAmp (K.radialFlux c) c.carriesSine (chartCoord P y) (heightRatio y)‖ * |radialVec y i| ≤
      Br * (1 - chartCoord P y) ^ 2 :=
    (mul_le_of_le_one_right (norm_nonneg _) hrv).trans hA
  have h2 : ‖scalarAmp (K.polarFlux c) c.carriesSine (chartCoord P y) (heightRatio y)‖ * |polarVecQ y i| ≤
      Bp * (1 - chartCoord P y) ^ 2 :=
    (mul_le_of_le_one_right (norm_nonneg _) hpv).trans hB
  linarith

theorem coord_continuous (i : Fin 3) : Continuous (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

theorem coord_abs_le (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.abs_le_sqrt ?_
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem norm_le_sum_abs (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  calc Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) ≤ Real.sqrt ((|v 0| + |v 1| + |v 2|) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2), sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
          mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
          mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]
    _ = |v 0| + |v 1| + |v 2| := Real.sqrt_sq (by positivity)

theorem entryMap_norm_le (a i : Fin 3) : ‖Internal.entryMap a i‖ ≤ 1 := by
  unfold Internal.entryMap
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have h1 : ‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul, Real.norm_eq_abs]
      exact coord_abs_le v i
  have h2 : ‖unitVector a‖ = 1 := by simp [unitVector]
  rw [h2, mul_one]
  exact h1

theorem coords_norm_le (p n w : ℂ) (a : Fin 3) : ‖coordsOfComponents p n w a‖ ≤ ‖p‖ + ‖n‖ + ‖w‖ := by
  have hp := norm_nonneg p
  have hn := norm_nonneg n
  have hw := norm_nonneg w
  fin_cases a
  · show ‖(p + n) / 2‖ ≤ _
    rw [norm_div, Complex.norm_two]
    have := norm_add_le p n
    linarith
  · show ‖(p - n) / (2 * Complex.I)‖ ≤ _
    rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
    have := norm_sub_le p n
    linarith
  · show ‖w‖ ≤ _
    linarith

theorem pointAngle_measurable : Measurable pointAngle := by
  show Measurable (fun y : Space => Complex.arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I))
  have h : Continuous (fun y : Space => (y 0 : ℂ) + (y 1 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp (coord_continuous 0)).add
      ((Complex.continuous_ofReal.comp (coord_continuous 1)).mul continuous_const)
  exact Complex.measurable_arg.comp h.measurable

theorem heightRatio_measurable : Measurable heightRatio := by
  show Measurable (fun y : Space => y 2 / ‖y‖)
  exact (coord_continuous 2).measurable.div measurable_norm

theorem chartCoord_continuous (P : ShapeParams) (hP : IsShapeParams P) : Continuous (chartCoord P) := by
  have hL := hP.chartLength_pos
  show Continuous (fun y : Space => ‖y‖ / (‖y‖ + P.chartLength))
  exact continuous_norm.div (continuous_norm.add continuous_const) fun y => by positivity

theorem radialPhase_norm_continuous (P : ShapeParams) (hP : IsShapeParams P) :
    Continuous (fun y : Space => P.radialPhase (‖y‖ ^ 2)) := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  refine hf.continuousOn.comp_continuous (continuous_norm.pow 2) fun y => ?_
  show -δ < ‖y‖ ^ 2
  nlinarith [sq_nonneg ‖y‖]

theorem scalarValue_measurable (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (w : Bool)
    (S : PotScalar) : Measurable (fun z : ℝ × Space => scalarValue P κ M w S z.1 z.2) := by
  unfold scalarValue
  have hch : Measurable (fun z : ℝ × Space => chartCoord P z.2) :=
    (chartCoord_continuous P hP).measurable.comp measurable_snd
  have hh2 : Measurable (fun z : ℝ × Space => heightRatio z.2) := heightRatio_measurable.comp measurable_snd
  have harg : Measurable (fun z : ℝ × Space => 2 * Real.pi * (labelTime κ.label : ℝ) * z.1 +
      (M : ℝ) * pointAngle z.2 + (κ.phaseIndex : ℝ) * P.radialPhase (‖z.2‖ ^ 2)) := by
    have h1 : Measurable (fun z : ℝ × Space => z.1) := measurable_fst
    have h2 : Measurable (fun z : ℝ × Space => pointAngle z.2) := pointAngle_measurable.comp measurable_snd
    have h3 : Measurable (fun z : ℝ × Space => P.radialPhase (‖z.2‖ ^ 2)) :=
      (radialPhase_norm_continuous P hP).measurable.comp measurable_snd
    exact ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
  have hexp : Measurable (fun z : ℝ × Space => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 +
      (M : ℝ) * pointAngle z.2 + (κ.phaseIndex : ℝ) * P.radialPhase (‖z.2‖ ^ 2) : ℝ) : ℂ) * Complex.I)) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp harg).mul_const _)
  have hwc : Continuous (weightPoly S.lowOrder S.highOrder) := by
    unfold weightPoly
    exact Complex.continuous_ofReal.comp (by fun_prop)
  have hw : Measurable (fun z : ℝ × Space => weightPoly S.lowOrder S.highOrder (chartCoord P z.2)) :=
    hwc.measurable.comp hch
  have hq : Measurable (fun z : ℝ × Space =>
      (((1 - heightRatio z.2 ^ 2) ^ S.axisPower * (if w then polarSine z.2 else 1) : ℝ) : ℂ)) := by
    refine Complex.measurable_ofReal.comp ?_
    cases w with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact ((measurable_const.sub (hh2.pow_const 2)).pow_const _).mul measurable_const
    | true =>
      simp only [if_true]
      exact ((measurable_const.sub (hh2.pow_const 2)).pow_const _).mul
        (Real.continuous_sqrt.measurable.comp (measurable_const.sub (hh2.pow_const 2)))
  have he : Measurable (fun z : ℝ × Space => S.amp.toSpline.evalHalf (chartCoord P z.2) (heightRatio z.2)) := by
    have h := (CellCert.GivenFields.DualPartsInternal.evalHalf_measurable S.amp.toSpline).comp (hch.prodMk hh2)
    simp only [Function.comp_def, Function.uncurry_apply_pair] at h
    exact h
  exact ((hexp.mul hw).mul hq).mul he

theorem polarVecQ_measurable (i : Fin 3) : Measurable (fun y : Space => polarVecQ y i) := by
  fin_cases i
  · show Measurable (fun y : Space => heightRatio y * y 0 / ‖y‖)
    exact (heightRatio_measurable.mul (coord_continuous 0).measurable).div measurable_norm
  · show Measurable (fun y : Space => heightRatio y * y 1 / ‖y‖)
    exact (heightRatio_measurable.mul (coord_continuous 1).measurable).div measurable_norm
  · show Measurable (fun y : Space => -(1 - heightRatio y ^ 2))
    exact (measurable_const.sub (heightRatio_measurable.pow_const 2)).neg

theorem fluxVector_measurable (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (K : PotKeyData)
    (c : PotComponent) (i : Fin 3) : Measurable (fun z : ℝ × Space => fluxVector P κ K c z.1 z.2 i) := by
  have hr : Measurable (fun z : ℝ × Space => radialVec z.2 i) :=
    (((coord_continuous i).measurable).div measurable_norm).comp measurable_snd
  have hp : Measurable (fun z : ℝ × Space => polarVecQ z.2 i) := (polarVecQ_measurable i).comp measurable_snd
  exact ((scalarValue_measurable P hP κ _ _ _).mul (Complex.measurable_ofReal.comp hr)).add
    ((scalarValue_measurable P hP κ _ _ _).mul (Complex.measurable_ofReal.comp hp))

theorem fluxRow_re_measurable (P : ShapeParams) (hP : IsShapeParams P) (F : PotentialSeries) (a i : Fin 3) :
    Measurable (fun z : ℝ × Space => (Internal.fluxRow P F z.1 a z.2 i).re) := by
  refine Complex.measurable_re.comp ?_
  unfold Internal.fluxRow
  refine Finset.measurable_sum _ fun κ _ => ?_
  have hp := fluxVector_measurable P hP κ (F.data κ) .plus i
  have hn := fluxVector_measurable P hP κ (F.data κ) .minus i
  have hz := fluxVector_measurable P hP κ (F.data κ) .axial i
  fin_cases a
  · exact (hp.add hn).div_const _
  · exact (hp.sub hn).div_const _
  · exact hz

theorem fluxMap_eq_sum (P : ShapeParams) (F : PotentialSeries) (σ : ℝ) :
    fluxMap P F σ = fun y => ∑ a : Fin 3, ∑ i : Fin 3, (Internal.fluxRow P F σ a y i).re • Internal.entryMap a i :=
  Internal.eq_sum_entryMap _ _ (Internal.fluxMap_apply_eq P F σ)

theorem fluxMap_aestronglyMeasurable (P : ShapeParams) (hP : IsShapeParams P) (F : PotentialSeries) :
    AEStronglyMeasurable (fun z : ℝ × Space => fluxMap P F z.1 z.2) volume := by
  have e : (fun z : ℝ × Space => fluxMap P F z.1 z.2) =
      fun z => ∑ a : Fin 3, ∑ i : Fin 3, (Internal.fluxRow P F z.1 a z.2 i).re • Internal.entryMap a i := by
    funext z
    rw [fluxMap_eq_sum]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun a _ => Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (fluxRow_re_measurable P hP F a i).aestronglyMeasurable.smul aestronglyMeasurable_const

theorem flux_good_ae (P : ShapeParams) (hP : IsShapeParams P) (F : PotentialSeries) :
    ∀ᵐ y : Space, y 0 ≠ 0 ∧ ∀ κ ∈ F.keys, ∀ c : PotComponent,
      chartCoord P y ∉ (((F.data κ).radialFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      chartCoord P y ∉ (((F.data κ).polarFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).radialFlux c).amp.xAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).polarFlux c).amp.xAxis.breaks.drop 1).dropLast := by
  have hT : ∀ l : List ℝ, ∀ᵐ y : Space, chartCoord P y ∉ l := by
    intro l
    have h := (Filter.eventually_all_finset l.toFinset).2 (fun b _ => chartCoord_ne_ae P hP b)
    filter_upwards [h] with y hy hm
    exact hy _ (List.mem_toFinset.2 hm) rfl
  have hX : ∀ l : List ℝ, ∀ᵐ y : Space, heightRatio y ∉ l := by
    intro l
    have h := (Filter.eventually_all_finset l.toFinset).2 (fun b _ => heightRatio_ne_ae b)
    filter_upwards [h] with y hy hm
    exact hy _ (List.mem_toFinset.2 hm) rfl
  have hc : ∀ κ c, ∀ᵐ y : Space,
      chartCoord P y ∉ (((F.data κ).radialFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      chartCoord P y ∉ (((F.data κ).polarFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).radialFlux c).amp.xAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).polarFlux c).amp.xAxis.breaks.drop 1).dropLast := by
    intro κ c
    filter_upwards [hT _, hT _, hX _, hX _] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hk : ∀ κ, ∀ᵐ y : Space, ∀ c : PotComponent,
      chartCoord P y ∉ (((F.data κ).radialFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      chartCoord P y ∉ (((F.data κ).polarFlux c).amp.tAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).radialFlux c).amp.xAxis.breaks.drop 1).dropLast ∧
      heightRatio y ∉ (((F.data κ).polarFlux c).amp.xAxis.breaks.drop 1).dropLast := by
    intro κ
    filter_upwards [hc κ .plus, hc κ .minus, hc κ .axial] with y h1 h2 h3 c
    cases c
    · exact h1
    · exact h2
    · exact h3
  filter_upwards [firstCoord_ne_ae, (Filter.eventually_all_finset F.keys).2 (fun κ _ => hk κ)] with y h0 h1
  exact ⟨h0, h1⟩

end FluxDecay.Internal

open FluxDecay.Internal in
theorem fluxMap_measurable_decay (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) :
    ∃ C : ℝ, AEStronglyMeasurable (fun z : ℝ × Space => fluxMap P F z.1 z.2) volume ∧
      (∀ σ y, ‖fluxMap P F σ y‖ ≤ C / (1 + ‖y‖) ^ 2) ∧
      ∀ σ, ∀ᵐ y, ‖y‖ * ‖matrixDivergence (fluxMap P F σ) y‖ ≤ C / (1 + ‖y‖) ^ 2 := by
  have hend : ∀ κ ∈ F.keys, ∀ c, FluxScalarEnd ((F.data κ).radialFlux c) ∧
      FluxScalarEnd ((F.data κ).polarFlux c) := by
    intro κ hκ c
    obtain ⟨hr1, -⟩ := hF.radialFlux_mesh κ hκ c
    obtain ⟨hp1, -⟩ := hF.polarFlux_mesh κ hκ c
    obtain ⟨he1, he2⟩ := hF.flux_end κ hκ c
    exact ⟨⟨hr1.sorted, hr1.first, hr1.last, he1⟩, ⟨hp1.sorted, hp1.first, hp1.last, he2⟩⟩
  have hval : ∀ κ c, ∃ C : ℝ, 0 ≤ C ∧ (κ ∈ F.keys → ∀ σ y (i : Fin 3),
      ‖fluxVector P κ (F.data κ) c σ y i‖ ≤ C * (1 - chartCoord P y) ^ 2) := by
    intro κ c
    by_cases hκ : κ ∈ F.keys
    · obtain ⟨C, hC0, hC⟩ := fluxVector_value_bound P hP κ (F.data κ) c (hend κ hκ c).1 (hend κ hκ c).2
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hκ⟩
  have hdiv : ∀ κ c, ∃ C : ℝ, 0 ≤ C ∧ (κ ∈ F.keys → ∀ σ y, y 0 ≠ 0 →
      chartCoord P y ∉ (((F.data κ).radialFlux c).amp.tAxis.breaks.drop 1).dropLast →
      chartCoord P y ∉ (((F.data κ).polarFlux c).amp.tAxis.breaks.drop 1).dropLast →
      heightRatio y ∉ (((F.data κ).radialFlux c).amp.xAxis.breaks.drop 1).dropLast →
      heightRatio y ∉ (((F.data κ).polarFlux c).amp.xAxis.breaks.drop 1).dropLast →
      (∀ i : Fin 3, DifferentiableAt ℝ (fun x => fluxVector P κ (F.data κ) c σ x i) y) ∧
      ‖y‖ * ‖∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ (F.data κ) c σ x i) y (unitVector i)‖ ≤
        C * (1 - chartCoord P y) ^ 2) := by
    intro κ c
    by_cases hκ : κ ∈ F.keys
    · obtain ⟨C, hC0, hC⟩ := fluxVector_divergence_bound P hP κ (F.data κ) c (hend κ hκ c).1 (hend κ hκ c).2
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hκ⟩
  choose Cv hCv0 hCv using hval
  choose Cd hCd0 hCd using hdiv
  set S : ℝ := ∑ κ ∈ F.keys, (Cv κ .plus + Cv κ .minus + Cv κ .axial + (Cd κ .plus + Cd κ .minus + Cd κ .axial))
    with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun κ _ => by
    have := hCv0 κ .plus; have := hCv0 κ .minus; have := hCv0 κ .axial
    have := hCd0 κ .plus; have := hCd0 κ .minus; have := hCd0 κ .axial
    linarith
  set m : ℝ := max P.chartLength 1 with hm
  refine ⟨9 * S * m ^ 2, fluxMap_aestronglyMeasurable P hP F, fun σ y => ?_, fun σ => ?_⟩
  · have hdec := chart_decay P hP y
    have hu : 0 ≤ (1 - chartCoord P y) ^ 2 := sq_nonneg _
    have hrow : ∀ a i, ‖Internal.fluxRow P F σ a y i‖ ≤ S * (1 - chartCoord P y) ^ 2 := by
      intro a i
      unfold Internal.fluxRow
      refine (norm_sum_le _ _).trans ?_
      rw [hSdef, Finset.sum_mul]
      refine Finset.sum_le_sum fun κ hκ => ?_
      refine (coords_norm_le _ _ _ a).trans ?_
      have h1 := hCv κ .plus hκ σ y i
      have h2 := hCv κ .minus hκ σ y i
      have h3 := hCv κ .axial hκ σ y i
      have h4 := mul_nonneg (add_nonneg (add_nonneg (hCd0 κ .plus) (hCd0 κ .minus)) (hCd0 κ .axial)) hu
      nlinarith
    have hterm : ∀ a i, ‖(Internal.fluxRow P F σ a y i).re • Internal.entryMap a i‖ ≤ S * (1 - chartCoord P y) ^ 2 := by
      intro a i
      rw [norm_smul, Real.norm_eq_abs]
      calc |(Internal.fluxRow P F σ a y i).re| * ‖Internal.entryMap a i‖ ≤ ‖Internal.fluxRow P F σ a y i‖ * 1 := by
            gcongr
            · exact Complex.abs_re_le_norm _
            · exact entryMap_norm_le a i
        _ ≤ _ := by rw [mul_one]; exact hrow a i
    rw [fluxMap_eq_sum]
    calc ‖∑ a : Fin 3, ∑ i : Fin 3, (Internal.fluxRow P F σ a y i).re • Internal.entryMap a i‖
        ≤ ∑ a : Fin 3, ∑ i : Fin 3, ‖(Internal.fluxRow P F σ a y i).re • Internal.entryMap a i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin 3, ∑ i : Fin 3, S * (1 - chartCoord P y) ^ 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ => hterm a i
      _ = 9 * S * (1 - chartCoord P y) ^ 2 := by simp only [Fin.sum_univ_three]; ring
      _ ≤ 9 * S * (m ^ 2 / (1 + ‖y‖) ^ 2) := by gcongr
      _ = 9 * S * m ^ 2 / (1 + ‖y‖) ^ 2 := by ring
  · filter_upwards [flux_good_ae P hP F] with y hy
    obtain ⟨hy0, hgood⟩ := hy
    have hdec := chart_decay P hP y
    have hu : 0 ≤ (1 - chartCoord P y) ^ 2 := sq_nonneg _
    have hd : ∀ κ ∈ F.keys, ∀ c, (∀ i : Fin 3, DifferentiableAt ℝ (fun x => fluxVector P κ (F.data κ) c σ x i) y) ∧
        ‖y‖ * ‖∑ i : Fin 3, fderiv ℝ (fun x => fluxVector P κ (F.data κ) c σ x i) y (unitVector i)‖ ≤
          Cd κ c * (1 - chartCoord P y) ^ 2 := fun κ hκ c =>
      hCd κ c hκ σ y hy0 (hgood κ hκ c).1 (hgood κ hκ c).2.1 (hgood κ hκ c).2.2.1 (hgood κ hκ c).2.2.2
    have hmd := matrixDivergence_fluxMap_apply P F σ y (fun κ hκ c i => (hd κ hκ c).1 i)
    have hcomp : ∀ a, ‖y‖ * |matrixDivergence (fluxMap P F σ) y a| ≤ S * (1 - chartCoord P y) ^ 2 := by
      intro a
      rw [hmd a]
      refine (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg y)).trans ?_
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg y)).trans ?_
      rw [Finset.mul_sum, hSdef, Finset.sum_mul]
      refine Finset.sum_le_sum fun κ hκ => ?_
      refine (mul_le_mul_of_nonneg_left (coords_norm_le _ _ _ a) (norm_nonneg y)).trans ?_
      have h1 := (hd κ hκ .plus).2
      have h2 := (hd κ hκ .minus).2
      have h3 := (hd κ hκ .axial).2
      have h4 := mul_nonneg (add_nonneg (add_nonneg (hCv0 κ .plus) (hCv0 κ .minus)) (hCv0 κ .axial)) hu
      nlinarith
    have hn := norm_le_sum_abs (matrixDivergence (fluxMap P F σ) y)
    calc ‖y‖ * ‖matrixDivergence (fluxMap P F σ) y‖
        ≤ ‖y‖ * (|matrixDivergence (fluxMap P F σ) y 0| + |matrixDivergence (fluxMap P F σ) y 1| +
            |matrixDivergence (fluxMap P F σ) y 2|) := mul_le_mul_of_nonneg_left hn (norm_nonneg y)
      _ ≤ 3 * S * (1 - chartCoord P y) ^ 2 := by
          have := hcomp 0
          have := hcomp 1
          have := hcomp 2
          nlinarith
      _ ≤ 9 * S * (1 - chartCoord P y) ^ 2 := by nlinarith
      _ ≤ 9 * S * (m ^ 2 / (1 + ‖y‖) ^ 2) := by gcongr
      _ = 9 * S * m ^ 2 / (1 + ‖y‖) ^ 2 := by ring


end PotentialShape

end Breakdown

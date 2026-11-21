import Breakdown.CertCell.InstanceStatements
import Breakdown.FracCell.GivenAuxDualParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields (ChartParams IsChartParams chartT heightRatio Spline TensorMesh IsTensorMesh
  cellCount cellIndex atSecond xDeriv)

namespace BasicFactsInternal

theorem flipPoint_third (y : Space) : flipPoint y 2 = -y 2 := by
  simp [flipPoint, unitVector]

theorem flipPoint_norm_eq (y : Space) : ‖flipPoint y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, flipPoint, unitVector]

theorem axialRot_third (φ : ℝ) (y : Space) : axialRot φ y 2 = y 2 := by
  simp [axialRot, unitVector]

theorem axialRot_norm_eq (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp [axialRot, unitVector]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ

theorem chartT_axialRot (P : ChartParams) (φ : ℝ) (y : Space) : chartT P (axialRot φ y) = chartT P y := by
  unfold chartT
  rw [axialRot_norm_eq]

theorem heightRatio_axialRot (φ : ℝ) (y : Space) : heightRatio (axialRot φ y) = heightRatio y := by
  unfold heightRatio
  rw [axialRot_norm_eq, axialRot_third]

theorem chartT_flipPoint (P : ChartParams) (y : Space) : chartT P (flipPoint y) = chartT P y := by
  unfold chartT
  rw [flipPoint_norm_eq]

theorem heightRatio_flipPoint (y : Space) : heightRatio (flipPoint y) = -heightRatio y := by
  unfold heightRatio
  rw [flipPoint_norm_eq, flipPoint_third, neg_div]

theorem chartT_nonneg (P : ChartParams) (hP : IsChartParams P) (y : Space) : 0 ≤ chartT P y := by
  unfold chartT
  have := hP.L0_pos
  positivity

theorem chartT_lt_one (P : ChartParams) (hP : IsChartParams P) (y : Space) : chartT P y < 1 := by
  unfold chartT
  have h := hP.L0_pos
  rw [div_lt_one (by positivity)]
  linarith [norm_nonneg y]

theorem abs_third_le_norm (y : Space) : |y 2| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y 2
  simpa [Real.norm_eq_abs] using this

theorem heightRatio_nonneg_of (y : Space) (h : 0 ≤ y 2) : 0 ≤ heightRatio y := by
  unfold heightRatio
  exact div_nonneg h (norm_nonneg y)

theorem heightRatio_le_one (y : Space) : heightRatio y ≤ 1 := by
  unfold heightRatio
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · rw [div_le_one h]
    exact (le_abs_self _).trans (abs_third_le_norm y)

theorem neg_heightRatio_nonneg_of (y : Space) (h : y 2 < 0) : 0 ≤ -heightRatio y := by
  unfold heightRatio
  rw [← neg_div]
  exact div_nonneg (by linarith) (norm_nonneg y)

theorem neg_heightRatio_le_one (y : Space) : -heightRatio y ≤ 1 := by
  unfold heightRatio
  rw [← neg_div]
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · rw [div_le_one h]
    exact (neg_le_abs _).trans (abs_third_le_norm y)

theorem index_lt_count (l : List ℝ) (hf : l.head? = some 0) (hl : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  have hle : cellIndex l u ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
  rw [List.length_dropLast, List.length_drop] at hle
  unfold cellCount
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hf
  · simp at hf hl
    linarith
  · simp only [List.length_cons] at hle ⊢
    omega

theorem index_at_zero (l : List ℝ) (hs : l.Pairwise (· < ·)) (hf : l.head? = some 0) :
    cellIndex l 0 = 0 := by
  unfold cellIndex
  rcases l with _ | ⟨a, rest⟩
  · simp at hf
  · simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    rw [List.pairwise_cons] at hs
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have hc' : c ∈ rest := by
      simpa using List.dropLast_subset _ hc
    simpa using hs.1 c hc'

theorem eval_atSecond_zero (t : ℝ) (p : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![(t : ℂ), ((0 : ℝ) : ℂ)] (atSecond 0 p) = MvPolynomial.eval ![(t : ℂ), ((0 : ℝ) : ℂ)] p := by
  unfold atSecond
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) ![(t : ℂ), ((0 : ℝ) : ℂ)] _ =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) ![(t : ℂ), ((0 : ℝ) : ℂ)] _
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext k
  fin_cases k <;> simp

theorem halves_agree_on_plane (S : ChartScalar) (hS : IsJoinedScalar 0 S) (t : ℝ) :
    S.upper.evalHalf t 0 = S.lower.evalHalf t 0 := by
  unfold Spline.evalHalf
  rw [index_at_zero _ hS.upper.mesh.x_sorted hS.upper.mesh.x_first,
    index_at_zero _ hS.lower.mesh.x_sorted hS.lower.mesh.x_first, ← hS.same_t]
  have hi := index_lt_count _ hS.upper.mesh.t_first hS.upper.mesh.t_last t
  have hp := hS.plane_joins _ hi 0 le_rfl
  simp only [xDeriv, Function.iterate_zero, id, pow_zero, map_one, one_mul] at hp
  rw [← eval_atSecond_zero, hp, eval_atSecond_zero]

theorem chartT_measurable (P : ChartParams) : Measurable (fun y : Space => chartT P y) := by
  unfold chartT
  fun_prop

theorem heightRatio_measurable : Measurable (fun y : Space => heightRatio y) := by
  unfold heightRatio
  fun_prop

theorem half_measurable (P : ChartParams) (S : Spline) (sgn : ℝ) :
    Measurable (fun y : Space => (S.evalHalf (chartT P y) (sgn * heightRatio y)).re) := by
  have h := (CellCert.GivenFields.DualPartsInternal.evalHalf_measurable S).comp
    ((chartT_measurable P).prodMk (heightRatio_measurable.const_mul sgn))
  exact Complex.measurable_re.comp h

theorem values_measurable (P : ChartParams) (M : TensorMesh) (f : ℕ → ℕ → ℝ) (sgn : ℝ) :
    Measurable (fun y : Space =>
      f (cellIndex M.tBreaks (chartT P y)) (cellIndex M.xBreaks (sgn * heightRatio y))) := by
  have hf : Measurable (fun q : ℕ × ℕ => f q.1 q.2) := measurable_of_countable _
  exact hf.comp (((CellCert.GivenFields.DualPartsInternal.cellIndex_measurable _).comp (chartT_measurable P)).prodMk
    ((CellCert.GivenFields.DualPartsInternal.cellIndex_measurable _).comp
      (heightRatio_measurable.const_mul sgn)))

end BasicFactsInternal

open BasicFactsInternal

theorem scalarBasicFacts : ScalarBasicFacts := by
  intro P S hP
  refine ⟨?_, ?_, ?_⟩
  · have hu := half_measurable P S.upper 1
    have hl := half_measurable P S.lower (-1)
    simp only [one_mul, neg_one_mul] at hu hl
    have hz : MeasurableSet {y : Space | 0 ≤ y 2} :=
      measurableSet_le measurable_const (by fun_prop)
    have hd : Measurable (fun y : Space => (1 - chartT P y) ^ S.decay) :=
      (measurable_const.sub (chartT_measurable P)).pow_const _
    exact hd.mul (Measurable.ite hz hu hl)
  · intro φ y
    unfold ChartScalar.eval
    rw [chartT_axialRot, heightRatio_axialRot, axialRot_third]
  · intro hN y
    unfold ChartScalar.eval
    have h0 := chartT_nonneg P hP y
    have h1 := chartT_lt_one P hP y
    refine mul_nonneg (pow_nonneg (by linarith) _) ?_
    split_ifs with h
    · exact (hN _ _ h0 h1.le (heightRatio_nonneg_of y h) (heightRatio_le_one y)).1
    · exact (hN _ _ h0 h1.le (neg_heightRatio_nonneg_of y (not_le.mp h)) (neg_heightRatio_le_one y)).2

theorem stepBasicFacts : StepBasicFacts := by
  intro P S hP
  refine ⟨?_, ?_, ?_⟩
  · have hu := values_measurable P S.mesh S.upper 1
    have hl := values_measurable P S.mesh S.lower (-1)
    simp only [one_mul, neg_one_mul] at hu hl
    have hz : MeasurableSet {y : Space | 0 ≤ y 2} :=
      measurableSet_le measurable_const (by fun_prop)
    have hb : Measurable (fun y : Space => 1 - chartT P y) := measurable_const.sub (chartT_measurable P)
    have hd : Measurable (fun y : Space => (1 - chartT P y) ^ S.decay) := by
      generalize S.decay = d
      cases d with
      | ofNat n =>
        simp only [Int.ofNat_eq_natCast, zpow_natCast]
        exact hb.pow_const n
      | negSucc n =>
        simp only [zpow_negSucc]
        exact (hb.pow_const (n + 1)).inv
    exact hd.mul (Measurable.ite hz hu hl)
  · intro φ y
    unfold StepDatum.eval StepDatum.upperValue StepDatum.lowerValue
    rw [chartT_axialRot, heightRatio_axialRot, axialRot_third]
  · intro hS y
    unfold StepDatum.eval StepDatum.upperValue StepDatum.lowerValue
    have h1 := chartT_lt_one P hP y
    have ht := index_lt_count _ hS.1.t_first hS.1.t_last (chartT P y)
    refine mul_pos (zpow_pos (by linarith) _) ?_
    split_ifs
    · exact (hS.2 _ _ ht (index_lt_count _ hS.1.x_first hS.1.x_last _)).1
    · exact (hS.2 _ _ ht (index_lt_count _ hS.1.x_first hS.1.x_last _)).2

theorem mirrorEval : MirrorEval := by
  intro P _
  refine ⟨fun S hS y => ?_, fun S y hy => ?_⟩
  · unfold ChartScalar.eval ChartScalar.mirror
    simp only [chartT_flipPoint, heightRatio_flipPoint, flipPoint_third, neg_neg]
    congr 1
    rcases lt_trichotomy (y 2) 0 with h | h | h
    · have h' : 0 ≤ -y 2 := by linarith
      rw [if_pos h', if_neg (not_le.mpr h)]
    · have hr : heightRatio y = 0 := by
        unfold heightRatio
        rw [h, zero_div]
      rw [if_pos (by rw [h, neg_zero]), if_pos h.ge, hr, neg_zero, halves_agree_on_plane S hS]
    · have h' : ¬ (0 ≤ -y 2) := by linarith
      rw [if_neg h', if_pos h.le]
  · unfold StepDatum.eval StepDatum.mirror StepDatum.upperValue StepDatum.lowerValue
    simp only [chartT_flipPoint, heightRatio_flipPoint, flipPoint_third, neg_neg]
    congr 1
    rcases lt_or_gt_of_ne hy with h | h
    · have h' : 0 ≤ -y 2 := by linarith
      rw [if_pos h', if_neg (not_le.mpr h)]
    · have h' : ¬ (0 ≤ -y 2) := by linarith
      rw [if_neg h', if_pos h.le]

end Instance

end CertCell

end Breakdown

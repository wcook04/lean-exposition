import Breakdown.CellReduction.PotThetaScalar
import Mathlib.Analysis.Calculus.Rademacher

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

def componentCoordMap : PotComponent → (ℂ →L[ℝ] (Fin 3 → ℂ))
  | .plus => ContinuousLinearMap.pi ![ContinuousLinearMap.mul ℝ ℂ (1 / 2),
      ContinuousLinearMap.mul ℝ ℂ (1 / (2 * Complex.I)), 0]
  | .minus => ContinuousLinearMap.pi ![ContinuousLinearMap.mul ℝ ℂ (1 / 2),
      ContinuousLinearMap.mul ℝ ℂ (-(1 / (2 * Complex.I))), 0]
  | .axial => ContinuousLinearMap.pi ![0, 0, ContinuousLinearMap.id ℝ ℂ]

def componentMap (c : PotComponent) : ℂ →L[ℝ] Space := realPartVec.comp (componentCoordMap c)

def allComponents : Finset PotComponent := {PotComponent.plus, PotComponent.minus, PotComponent.axial}

theorem coordsOfComponents_eq_maps (gp gn gz : ℂ) :
    coordsOfComponents gp gn gz =
      componentCoordMap .plus gp + componentCoordMap .minus gn + componentCoordMap .axial gz := by
  funext a
  fin_cases a <;> simp [coordsOfComponents, componentCoordMap] <;> ring_nf <;> (try simp only [Complex.inv_I]) <;> ring

theorem vectorPotential_eq_sum (P : ShapeParams) (F : PotentialSeries)
    (pick : PotKeyData → PotComponent → PotScalar) (σ : ℝ) (y : Space) :
    vectorPotential P F pick σ y =
      ∑ p ∈ F.keys ×ˢ allComponents, componentMap p.2 (componentValue P p.1 (pick (F.data p.1)) p.2 σ y) := by
  rw [Finset.sum_product]
  unfold vectorPotential
  rw [map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [coordsOfComponents_eq_maps]
  simp [allComponents, componentMap, add_assoc]

theorem ae_differentiableAt_of_slopeOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {G : Space → F}
    (hG : ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K G (Metric.closedBall 0 R)) :
    ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ G y := by
  have h : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure Space), y ∈ Metric.ball (0 : Space) n → DifferentiableAt ℝ G y := by
    intro n
    obtain ⟨K, hK⟩ := hG n
    filter_upwards [(hK.mono Metric.ball_subset_closedBall).ae_differentiableWithinAt_of_mem (μ := volume)]
      with y hy hyb
    exact (hy hyb).differentiableAt (Metric.isOpen_ball.mem_nhds hyb)
  rw [← ae_all_iff] at h
  filter_upwards [h] with y hy
  obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
  exact hy n (by rwa [mem_ball_zero_iff])

namespace Internal

theorem norm_traceSecond_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  have hu : ∀ j : Fin 3, ‖unitVector j‖ = 1 := fun j => by simp [unitVector]
  have h1 : ‖secondDerivTrace H‖ ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ := by
    unfold secondDerivTrace
    exact norm_sum_le _ _
  refine h1.trans ?_
  calc ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖H‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ‖H (unitVector j) (unitVector j)‖ ≤ ‖H (unitVector j)‖ * ‖unitVector j‖ :=
              (H (unitVector j)).le_opNorm _
          _ ≤ ‖H‖ * ‖unitVector j‖ * ‖unitVector j‖ :=
              mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
          _ = ‖H‖ := by rw [hu, mul_one, mul_one]
    _ = 3 * ‖H‖ := by simp

variable {ι : Type*}

theorem norm_combo_le (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) (v : ι → ℂ) (C : ι → ℝ) {d : ℝ}
    (hv : ∀ i ∈ s, ‖v i‖ ≤ C i / d) : ‖∑ i ∈ s, L i (v i)‖ ≤ (∑ i ∈ s, ‖L i‖ * C i) / d := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [mul_div_assoc]
  exact ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hv i hi) (norm_nonneg _))

theorem norm_comboDeriv_le (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) (A : ι → Space →L[ℝ] ℂ) (C : ι → ℝ)
    {d : ℝ} (hA : ∀ i ∈ s, ‖A i‖ ≤ C i / d) :
    ‖∑ i ∈ s, ContinuousLinearMap.compL ℝ Space ℂ Space (L i) (A i)‖ ≤ (∑ i ∈ s, ‖L i‖ * C i) / d := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [mul_div_assoc, ContinuousLinearMap.compL_apply]
  exact ((L i).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hA i hi) (norm_nonneg _))

theorem norm_comboSecond_le (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) (B : ι → Space →L[ℝ] Space →L[ℝ] ℂ)
    (C : ι → ℝ) {d : ℝ} (hB : ∀ i ∈ s, ‖B i‖ ≤ C i / d) :
    ‖∑ i ∈ s, (ContinuousLinearMap.compL ℝ Space ℂ Space (L i)).comp (B i)‖ ≤
      (∑ i ∈ s, ‖L i‖ * C i) / d := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [mul_div_assoc]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  calc ‖((ContinuousLinearMap.compL ℝ Space ℂ Space (L i)).comp (B i)) v‖ = ‖(L i).comp (B i v)‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
    _ ≤ ‖L i‖ * ‖B i v‖ := (L i).opNorm_comp_le _
    _ ≤ ‖L i‖ * (‖B i‖ * ‖v‖) := mul_le_mul_of_nonneg_left ((B i).le_opNorm v) (norm_nonneg _)
    _ = ‖L i‖ * ‖B i‖ * ‖v‖ := by ring

theorem hasFDerivAt_combo (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) {f : ι → Space → ℂ} {y : Space}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) y) :
    HasFDerivAt (fun x => ∑ i ∈ s, L i (f i x))
      (∑ i ∈ s, ContinuousLinearMap.compL ℝ Space ℂ Space (L i) (fderiv ℝ (f i) y)) y := by
  have := HasFDerivAt.sum (u := s) (A := fun i x => L i (f i x)) fun i hi =>
    (L i).hasFDerivAt.comp y (hf i hi).hasFDerivAt
  simpa only [Finset.sum_fn, ContinuousLinearMap.compL_apply] using this

theorem fderiv_combo (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) {f : ι → Space → ℂ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) :
    fderiv ℝ (fun x => ∑ i ∈ s, L i (f i x)) =
      fun x => ∑ i ∈ s, ContinuousLinearMap.compL ℝ Space ℂ Space (L i) (fderiv ℝ (f i) x) := by
  funext x
  exact (hasFDerivAt_combo s L fun i hi => hf i hi x).fderiv

theorem hasFDerivAt_comboDeriv (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) {f : ι → Space → ℂ} {y : Space}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (fderiv ℝ (f i)) y) :
    HasFDerivAt (fun x => ∑ i ∈ s, ContinuousLinearMap.compL ℝ Space ℂ Space (L i) (fderiv ℝ (f i) x))
      (∑ i ∈ s, (ContinuousLinearMap.compL ℝ Space ℂ Space (L i)).comp (fderiv ℝ (fderiv ℝ (f i)) y)) y := by
  have := HasFDerivAt.sum (u := s)
    (A := fun i x => ContinuousLinearMap.compL ℝ Space ℂ Space (L i) (fderiv ℝ (f i) x)) fun i hi =>
    (ContinuousLinearMap.compL ℝ Space ℂ Space (L i)).hasFDerivAt.comp y (hf i hi).hasFDerivAt
  simpa only [Finset.sum_fn] using this

theorem comboDecay (s : Finset ι) (L : ι → ℂ →L[ℝ] Space) (f : ι → ℝ → Space → ℂ) (h : ℕ)
    (hd1 : ∀ i ∈ s, ∀ σ, Differentiable ℝ (f i σ))
    (hd2 : ∀ i ∈ s, ∀ σ, ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ (fderiv ℝ (f i σ)) y)
    (hb : ∀ i ∈ s, ∃ C : ℝ, (∀ σ y, ‖f i σ y‖ ≤ C / (1 + ‖y‖) ^ h ∧
      ‖fderiv ℝ (f i σ) y‖ ≤ C / (1 + ‖y‖) ^ (h + 1)) ∧
      ∀ σ, ∀ᵐ y ∂(volume : Measure Space),
        ‖fderiv ℝ (fun x => fderiv ℝ (f i σ) x) y‖ ≤ C / (1 + ‖y‖) ^ (h + 2)) :
    ∃ C : ℝ, (∀ σ y, ‖∑ i ∈ s, L i (f i σ y)‖ ≤ C / (1 + ‖y‖) ^ h ∧
      ‖fderiv ℝ (fun x => ∑ i ∈ s, L i (f i σ x)) y‖ ≤ C / (1 + ‖y‖) ^ (h + 1)) ∧
      ∀ σ, ∀ᵐ y ∂(volume : Measure Space),
        ‖secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ (fun x' => ∑ i ∈ s, L i (f i σ x')) x) y)‖ ≤
          C / (1 + ‖y‖) ^ (h + 2) := by
  classical
  choose! C hC using hb
  set S := ∑ i ∈ s, ‖L i‖ * |C i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have habs : ∀ i ∈ s, ∀ {a d : ℝ}, 0 < d → a ≤ C i / d → a ≤ |C i| / d := fun i _ a d hd ha =>
    ha.trans (by gcongr; exact le_abs_self _)
  refine ⟨3 * S, fun σ y => ⟨?_, ?_⟩, fun σ => ?_⟩
  · have hd : (0 : ℝ) < (1 + ‖y‖) ^ h := by positivity
    have := norm_combo_le s L (fun i => f i σ y) (fun i => |C i|) (d := (1 + ‖y‖) ^ h)
      fun i hi => habs i hi hd ((hC i hi).1 σ y).1
    refine this.trans ?_
    gcongr
    linarith
  · have hd : (0 : ℝ) < (1 + ‖y‖) ^ (h + 1) := by positivity
    rw [fderiv_combo s L fun i hi => hd1 i hi σ]
    have := norm_comboDeriv_le s L (fun i => fderiv ℝ (f i σ) y) (fun i => |C i|) (d := (1 + ‖y‖) ^ (h + 1))
      fun i hi => habs i hi hd ((hC i hi).1 σ y).2
    refine this.trans ?_
    gcongr
    linarith
  · filter_upwards [(Filter.eventually_all_finset s).2 fun i hi => hd2 i hi σ,
      (Filter.eventually_all_finset s).2 fun i hi => (hC i hi).2 σ] with y hy hy'
    have hd : (0 : ℝ) < (1 + ‖y‖) ^ (h + 2) := by positivity
    rw [fderiv_combo s L fun i hi => hd1 i hi σ]
    rw [(hasFDerivAt_comboDeriv s L hy).fderiv]
    refine (norm_traceSecond_le _).trans ?_
    have := norm_comboSecond_le s L (fun i => fderiv ℝ (fderiv ℝ (f i σ)) y) (fun i => |C i|)
      (d := (1 + ‖y‖) ^ (h + 2)) fun i hi => habs i hi hd (hy' i hi)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this (by norm_num)

end Internal

theorem potentialDecay_of_pick {h : ℕ} (hdec : ScalarDecayOrder h) {P : ShapeParams} {F : PotentialSeries}
    {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P) (hF : IsPotentialPick h F pick)
    (hd1 : ∀ κ ∈ F.keys, ∀ c σ, Differentiable ℝ (componentValue P κ (pick (F.data κ)) c σ))
    (hd2 : ∀ κ ∈ F.keys, ∀ c σ, ∀ᵐ y ∂(volume : Measure Space),
      DifferentiableAt ℝ (fderiv ℝ (componentValue P κ (pick (F.data κ)) c σ)) y) :
    ∃ C : ℝ, (∀ σ y, ‖vectorPotential P F pick σ y‖ ≤ C / (1 + ‖y‖) ^ h ∧
      ‖fderiv ℝ (vectorPotential P F pick σ) y‖ ≤ C / (1 + ‖y‖) ^ (h + 1)) ∧
      ∀ σ, ∀ᵐ y ∂(volume : Measure Space),
        ‖secondDerivTrace (secondDeriv (vectorPotential P F pick σ) y)‖ ≤ C / (1 + ‖y‖) ^ (h + 2) := by
  have e : ∀ σ, vectorPotential P F pick σ = fun y => ∑ p ∈ F.keys ×ˢ allComponents,
      componentMap p.2 (componentValue P p.1 (pick (F.data p.1)) p.2 σ y) :=
    fun σ => funext fun y => vectorPotential_eq_sum P F pick σ y
  obtain ⟨C, h1, h2⟩ := Internal.comboDecay (F.keys ×ˢ allComponents) (fun p => componentMap p.2)
    (fun p σ y => componentValue P p.1 (pick (F.data p.1)) p.2 σ y) h
    (fun p hp σ => hd1 p.1 (Finset.mem_product.1 hp).1 p.2 σ)
    (fun p hp σ => hd2 p.1 (Finset.mem_product.1 hp).1 p.2 σ)
    (fun p hp => hdec P p.1 _ _ _ hP (hF.scalar p.1 (Finset.mem_product.1 hp).1 p.2)
      (axisAdmissible_of_pick hF P.azimuthOrder (Finset.mem_product.1 hp).1 p.2))
  refine ⟨C, fun σ y => ?_, fun σ => ?_⟩
  · rw [e σ]
    exact h1 σ y
  · unfold secondDeriv
    rw [e σ]
    exact h2 σ

theorem ae_differentiableAt_of_annulusSlope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {G : Space → F}
    (hG : ∀ r R : ℝ, 0 < r → ∃ K : NNReal, LipschitzOnWith K G {y : Space | r ≤ ‖y‖ ∧ ‖y‖ ≤ R}) :
    ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ G y := by
  have h : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure Space),
      y ∈ {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} → DifferentiableAt ℝ G y := by
    intro n
    obtain ⟨K, hK⟩ := hG (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) (by positivity)
    filter_upwards [hK.ae_differentiableWithinAt_of_mem (μ := volume)] with y hy hyU
    have hU : IsOpen {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hsub : {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} ⊆
        {y : Space | 1 / ((n : ℝ) + 1) ≤ ‖y‖ ∧ ‖y‖ ≤ (n : ℝ) + 1} := fun z hz => ⟨hz.1.le, hz.2.le⟩
    exact (hy (hsub hyU)).differentiableAt (Filter.mem_of_superset (hU.mem_nhds hyU) hsub)
  rw [← ae_all_iff] at h
  have h0 : ∀ᵐ y ∂(volume : Measure Space), y ∈ ({0} : Set Space)ᶜ :=
    compl_mem_ae_iff.2 (measure_singleton (0 : Space))
  filter_upwards [h, h0] with y hy hy0
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 (by simpa using hy0)
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖y‖ (1 / ‖y‖))
  have h1 : ‖y‖ < (n : ℝ) + 1 := by linarith [le_max_left ‖y‖ (1 / ‖y‖)]
  have h2 : 1 / ‖y‖ < (n : ℝ) + 1 := by linarith [le_max_right ‖y‖ (1 / ‖y‖)]
  have h3 : 1 / ((n : ℝ) + 1) < ‖y‖ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at h2
    linarith
  exact hy n ⟨h3, h1⟩

theorem componentDifferentiable_of_smooth {h : ℕ} (hoff : ScalarSmoothAwayFromOrigin)
    (horig : ScalarSmoothNearOrigin) {P : ShapeParams} {F : PotentialSeries}
    {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P) (hF : IsPotentialPick h F pick)
    {κ : FieldKey} (hκ : κ ∈ F.keys) (c : PotComponent) (σ : ℝ) :
    Differentiable ℝ (componentValue P κ (pick (F.data κ)) c σ) := by
  intro y
  by_cases hy : y = 0
  · subst hy
    exact (horig P κ _ _ _ σ hP (hF.scalar κ hκ c).smooth_class (axisAdmissible_of_pick hF P.azimuthOrder hκ c)
      (hF.scalar κ hκ c).start_order).1.differentiableAt (by simp)
  · exact ((hoff P κ _ _ _ σ hP (hF.scalar κ hκ c).smooth_class
      (axisAdmissible_of_pick hF P.azimuthOrder hκ c)).1 y hy).differentiableAt (by simp)

theorem componentSecond_ae_of_smooth {h : ℕ} (hoff : ScalarSmoothAwayFromOrigin) {P : ShapeParams}
    {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P)
    (hF : IsPotentialPick h F pick) {κ : FieldKey} (hκ : κ ∈ F.keys) (c : PotComponent) (σ : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ (fderiv ℝ (componentValue P κ (pick (F.data κ)) c σ)) y :=
  ae_differentiableAt_of_annulusSlope fun r R hr =>
    (hoff P κ _ _ _ σ hP (hF.scalar κ hκ c).smooth_class (axisAdmissible_of_pick hF P.azimuthOrder hκ c)).2 r R hr

theorem potentialDecay_of_scalarParts {h : ℕ} (hoff : ScalarSmoothAwayFromOrigin)
    (horig : ScalarSmoothNearOrigin) (hdec : ScalarDecayOrder h) {P : ShapeParams} {F : PotentialSeries}
    {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P) (hF : IsPotentialPick h F pick) :
    ∃ C : ℝ, (∀ σ y, ‖vectorPotential P F pick σ y‖ ≤ C / (1 + ‖y‖) ^ h ∧
      ‖fderiv ℝ (vectorPotential P F pick σ) y‖ ≤ C / (1 + ‖y‖) ^ (h + 1)) ∧
      ∀ σ, ∀ᵐ y ∂(volume : Measure Space),
        ‖secondDerivTrace (secondDeriv (vectorPotential P F pick σ) y)‖ ≤ C / (1 + ‖y‖) ^ (h + 2) :=
  potentialDecay_of_pick hdec hP hF (fun _ hκ c σ => componentDifferentiable_of_smooth hoff horig hP hF hκ c σ)
    (fun _ hκ c σ => componentSecond_ae_of_smooth hoff hP hF hκ c σ)

end PotentialShape

end Breakdown
